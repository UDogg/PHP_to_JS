/* c_core/phc.c
 * PHC — PHP-to-C compiler.
 *
 * Supported PHP subset
 * --------------------
 *   Literals      : integers, floats, "double-quoted", 'single-quoted'
 *   Variables     : $var, $$var (variable variables)
 *   Operators     : + - * / % . (string concat)
 *                   == != === < > <= >=
 *                   ! (logical not)   unary -
 *   Assignment    : $var = expr
 *   Compound      : $var += expr   $var -= expr   $var .= expr
 *   Output        : echo expr [, expr]* ;
 *   Control flow  : if / else if / else
 *                   while (expr) { }
 *                   for ($i = x; cond; $i op= y) { }
 *   Comments      : // …   # …   block comments
 *   PHP tags      : <?php  ?>  (multiple blocks per file)
 *
 * Code-generation strategy
 * ------------------------
 * Every emitted C statement is enclosed in its own { } block so that the
 * phc_var temporaries it declares are block-scoped.  This means two sibling
 * statements can both use a temporary called "t0" with no collision — each
 * lives in its own anonymous block.
 *
 * Compound control statements (if/while/for) open their OWN brace structure
 * using emit_open_scope() / emit_close_scope() for the condition-evaluation
 * temporaries, and rely on parse_block() for the body braces.
 *
 * The key insight that makes if/else if/else work without stray declarations
 * between } and else:
 *   The condition for an else if is evaluated INSIDE the else block.
 *   We emit:   else { <cond-temps>; if (cond) { <body> } [else …] }
 *   The outer else { is opened before any temporaries are emitted, so
 *   nothing appears between the closing } of the previous branch and the
 *   else keyword.
 *
 * Ownership model for phc_var.value.str
 * --------------------------------------
 *   phc_set_var  TAKES ownership — do not free .str after calling it.
 *   phc_get_var  returns a SHALLOW copy — do not free its .str.
 *   Operator functions return a NEW heap string owned by the caller.
 *   All generated assignments call phc_var_dup() before phc_set_var.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include <stdarg.h>
#include <limits.h>

#include "phc_runtime.h"

/* ============================================================
 * Configuration
 * ========================================================== */
#define MAX_TOKEN_LEN     4096
#define EMIT_LINE_SIZE    4096
#define INITIAL_BUF_LINES 16384

/* ============================================================
 * Token types
 * ========================================================== */
typedef enum {
    TOK_EOF,
    TOK_OPEN_TAG,     /* <?php  */
    TOK_CLOSE_TAG,    /* ?>     */

    TOK_INTEGER,      /* 42     */
    TOK_FLOAT,        /* 3.14   */
    TOK_STRING,       /* "…"/'…'*/

    TOK_VARIABLE,     /* $foo  → value="foo" */
    TOK_DYNVAR,       /* $$foo → value="foo" */
    TOK_ECHO,
    TOK_IF,
    TOK_ELSE,
    TOK_WHILE,
    TOK_FOR,

    TOK_ASSIGN,       /* =   */
    TOK_PLUS_ASSIGN,  /* +=  */
    TOK_MINUS_ASSIGN, /* -=  */
    TOK_DOT_ASSIGN,   /* .=  */
    TOK_PLUS,         /* +   */
    TOK_MINUS,        /* -   */
    TOK_STAR,         /* *   */
    TOK_SLASH,        /* /   */
    TOK_PERCENT,      /* %   */
    TOK_DOT,          /* .   */
    TOK_EQ,           /* ==  */
    TOK_NEQ,          /* !=  */
    TOK_IDENTICAL,    /* === */
    TOK_LT,           /* <   */
    TOK_GT,           /* >   */
    TOK_LTE,          /* <=  */
    TOK_GTE,          /* >=  */
    TOK_BANG,         /* !   */

    TOK_SEMICOLON,    /* ;   */
    TOK_COMMA,        /* ,   */
    TOK_LBRACE,       /* {   */
    TOK_RBRACE,       /* }   */
    TOK_LPAREN,       /* (   */
    TOK_RPAREN        /* )   */
} TokenType;

typedef struct {
    TokenType type;
    char      value[MAX_TOKEN_LEN];
    int       line;
} Token;

/* ============================================================
 * Compiler state
 * ========================================================== */
static FILE  *infile   = NULL;
static FILE  *outfile  = NULL;
static int    line_num = 1;
static int    cur_char = 0;   /* int holds EOF = -1 safely */
static bool   at_eof   = false;
static Token  cur_tok;

static char  *code_buf = NULL;
static int    code_cnt = 0;
static int    code_cap = 0;

static int    tmp_ctr  = 0;   /* monotonically increasing unique-name counter */

/* ============================================================
 * Error reporting
 * ========================================================== */
static void compiler_error(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    fprintf(stderr, "Compile error at line %d: ", line_num);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
    exit(1);
}

/* ============================================================
 * Emit buffer
 * ========================================================== */
static void buf_init(void) {
    code_cap = INITIAL_BUF_LINES;
    code_buf = malloc((size_t)code_cap * EMIT_LINE_SIZE);
    if (!code_buf) { fputs("FATAL: malloc code_buf\n", stderr); exit(1); }
}

static void emit(const char *fmt, ...) {
    if (code_cnt >= code_cap) {
        code_cap *= 2;
        char *nb = realloc(code_buf, (size_t)code_cap * EMIT_LINE_SIZE);
        if (!nb) { fputs("FATAL: realloc code_buf\n", stderr); exit(1); }
        code_buf = nb;
    }
    char *slot = code_buf + (size_t)code_cnt * EMIT_LINE_SIZE;
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(slot, EMIT_LINE_SIZE, fmt, ap);
    va_end(ap);
    if (n < 0 || n >= EMIT_LINE_SIZE) {
        fprintf(stderr, "FATAL: emitted line too long (> %d bytes)\n",
                EMIT_LINE_SIZE);
        exit(1);
    }
    code_cnt++;
}

/* Write a unique C identifier into buf (needs >= 16 bytes) */
static void newtmp(char *buf) {
    snprintf(buf, 16, "t%d", tmp_ctr++);
}

/* ============================================================
 * C-string body escaper
 * Converts arbitrary bytes to a safe C string literal body
 * (no surrounding quotes). Prevents format-string injection.
 * ========================================================== */
static void escape_c_str(const char *src, char *out, size_t outsz) {
    size_t j = 0;
    for (const char *p = src; *p && j + 6 < outsz; p++) {
        unsigned char c = (unsigned char)*p;
        switch (c) {
            case '"':  out[j++] = '\\'; out[j++] = '"';  break;
            case '\\': out[j++] = '\\'; out[j++] = '\\'; break;
            case '\n': out[j++] = '\\'; out[j++] = 'n';  break;
            case '\r': out[j++] = '\\'; out[j++] = 'r';  break;
            case '\t': out[j++] = '\\'; out[j++] = 't';  break;
            default:
                if (c < 32 || c == 127)
                    j += (size_t)snprintf(out + j, 6, "\\x%02x", c);
                else
                    out[j++] = (char)c;
        }
    }
    out[j] = '\0';
}

/* ============================================================
 * Output writer
 * ========================================================== */
static void write_output(void) {
    fprintf(outfile,
        "#include <stdio.h>\n"
        "#include \"phc_runtime.h\"\n\n"
        "int main(void) {\n"
        "    phc_runtime_init();\n");
    for (int i = 0; i < code_cnt; i++)
        fprintf(outfile, "    %s\n",
                code_buf + (size_t)i * EMIT_LINE_SIZE);
    fprintf(outfile,
        "    phc_runtime_shutdown();\n"
        "    return 0;\n"
        "}\n");
}

/* ============================================================
 * Lexer
 * ========================================================== */
static void advance(void) {
    int ch = fgetc(infile);
    if (ch == EOF) { at_eof = true; cur_char = 0; }
    else           { cur_char = ch; if (ch == '\n') line_num++; }
}

static int lpeek(void) {
    int ch = fgetc(infile);
    if (ch != EOF) ungetc(ch, infile);
    return ch;
}

static void skip_ws(void) {
    while (!at_eof && isspace((unsigned char)cur_char)) advance();
}

static void skip_block_comment(void) {
    while (!at_eof) {
        if (cur_char == '*' && lpeek() == '/') { advance(); advance(); return; }
        advance();
    }
    compiler_error("unterminated block comment");
}

static void skip_line_comment(void) {
    while (!at_eof && cur_char != '\n') advance();
}

static void skip_gap(void) {
    for (;;) {
        skip_ws();
        if (at_eof) return;
        if (cur_char == '/' && lpeek() == '/') { advance(); advance(); skip_line_comment(); continue; }
        if (cur_char == '/' && lpeek() == '*') { advance(); advance(); skip_block_comment(); continue; }
        if (cur_char == '#')                   { skip_line_comment(); continue; }
        return;
    }
}

static void read_string(char *buf, int bufsz) {
    char q = (char)cur_char;
    advance();
    int i = 0;
    while (!at_eof && cur_char != q && i < bufsz - 1) {
        if (cur_char == '\\') {
            advance();
            if (at_eof) break;
            if (q == '\'') {
                if      (cur_char == '\'') { buf[i++] = '\''; }
                else if (cur_char == '\\') { buf[i++] = '\\'; }
                else { if (i < bufsz-2) { buf[i++]='\\'; buf[i++]=(char)cur_char; } }
            } else {
                switch (cur_char) {
                    case 'n':  buf[i++] = '\n'; break;
                    case 't':  buf[i++] = '\t'; break;
                    case 'r':  buf[i++] = '\r'; break;
                    case '"':  buf[i++] = '"';  break;
                    case '\\': buf[i++] = '\\'; break;
                    case '$':  buf[i++] = '$';  break;
                    default:
                        if (i < bufsz-2) { buf[i++]='\\'; buf[i++]=(char)cur_char; }
                        break;
                }
            }
        } else {
            buf[i++] = (char)cur_char;
        }
        advance();
    }
    buf[i] = '\0';
    if (!at_eof) advance();
}

static void read_number(char *buf, int bufsz) {
    int i = 0; bool has_dot = false, has_exp = false;
    while (!at_eof && i < bufsz - 1) {
        if (isdigit((unsigned char)cur_char)) {
            buf[i++] = (char)cur_char; advance();
        } else if (cur_char == '.' && !has_dot && !has_exp) {
            has_dot = true; buf[i++] = '.'; advance();
        } else if ((cur_char == 'e' || cur_char == 'E') && !has_exp) {
            has_exp = true; buf[i++] = (char)cur_char; advance();
            if (!at_eof && (cur_char == '+' || cur_char == '-')) {
                buf[i++] = (char)cur_char; advance();
            }
        } else break;
    }
    buf[i] = '\0';
}

static void read_ident(char *buf, int bufsz) {
    int i = 0;
    while (!at_eof &&
           (isalnum((unsigned char)cur_char) || cur_char == '_') &&
           i < bufsz - 1) {
        buf[i++] = (char)cur_char; advance();
    }
    buf[i] = '\0';
}

static void get_next_token(void) {
    skip_gap();
    cur_tok.line = line_num;

    if (at_eof) { cur_tok.type = TOK_EOF; cur_tok.value[0] = '\0'; return; }

    /* <?php */
    if (cur_char == '<' && lpeek() == '?') {
        advance(); advance();
        char kw[8] = {0}; int ki = 0;
        while (!at_eof && isalpha((unsigned char)cur_char) && ki < 7)
            kw[ki++] = (char)cur_char, advance();
        kw[ki] = '\0';
        if (strcmp(kw, "php") != 0) compiler_error("expected '<?php', got '<?%s'", kw);
        cur_tok.type = TOK_OPEN_TAG; strcpy(cur_tok.value, "<?php"); return;
    }

    /* ?> */
    if (cur_char == '?' && lpeek() == '>') {
        advance(); advance();
        cur_tok.type = TOK_CLOSE_TAG; strcpy(cur_tok.value, "?>"); return;
    }

    /* String */
    if (cur_char == '"' || cur_char == '\'') {
        cur_tok.type = TOK_STRING; read_string(cur_tok.value, MAX_TOKEN_LEN); return;
    }

    /* Number */
    if (isdigit((unsigned char)cur_char)) {
        read_number(cur_tok.value, MAX_TOKEN_LEN);
        cur_tok.type = (strchr(cur_tok.value, '.') ||
                        strchr(cur_tok.value, 'e') ||
                        strchr(cur_tok.value, 'E')) ? TOK_FLOAT : TOK_INTEGER;
        return;
    }

    /* $var / $$var */
    if (cur_char == '$') {
        advance();
        if (!at_eof && cur_char == '$') { advance(); cur_tok.type = TOK_DYNVAR; }
        else                            { cur_tok.type = TOK_VARIABLE; }
        read_ident(cur_tok.value, MAX_TOKEN_LEN);
        if (cur_tok.value[0] == '\0') compiler_error("expected identifier after '$'");
        return;
    }

    /* Keywords */
    if (isalpha((unsigned char)cur_char) || cur_char == '_') {
        read_ident(cur_tok.value, MAX_TOKEN_LEN);
        if      (!strcmp(cur_tok.value, "echo"))  cur_tok.type = TOK_ECHO;
        else if (!strcmp(cur_tok.value, "if"))    cur_tok.type = TOK_IF;
        else if (!strcmp(cur_tok.value, "else"))  cur_tok.type = TOK_ELSE;
        else if (!strcmp(cur_tok.value, "while")) cur_tok.type = TOK_WHILE;
        else if (!strcmp(cur_tok.value, "for"))   cur_tok.type = TOK_FOR;
        else compiler_error("unknown keyword '%s'", cur_tok.value);
        return;
    }

    /* Operators / punctuation */
    char c = (char)cur_char; advance();
    switch (c) {
        case '=':
            if (!at_eof && cur_char == '=') {
                advance();
                if (!at_eof && cur_char == '=') { advance(); cur_tok.type=TOK_IDENTICAL; strcpy(cur_tok.value,"==="); }
                else                            {            cur_tok.type=TOK_EQ;        strcpy(cur_tok.value,"=="); }
            } else { cur_tok.type=TOK_ASSIGN; strcpy(cur_tok.value,"="); }
            break;
        case '!': if (!at_eof && cur_char=='=') { advance(); cur_tok.type=TOK_NEQ;          strcpy(cur_tok.value,"!="); }
                  else                          {            cur_tok.type=TOK_BANG;          strcpy(cur_tok.value,"!"); } break;
        case '<': if (!at_eof && cur_char=='=') { advance(); cur_tok.type=TOK_LTE;           strcpy(cur_tok.value,"<="); }
                  else                          {            cur_tok.type=TOK_LT;            strcpy(cur_tok.value,"<"); } break;
        case '>': if (!at_eof && cur_char=='=') { advance(); cur_tok.type=TOK_GTE;           strcpy(cur_tok.value,">="); }
                  else                          {            cur_tok.type=TOK_GT;            strcpy(cur_tok.value,">"); } break;
        case '+': if (!at_eof && cur_char=='=') { advance(); cur_tok.type=TOK_PLUS_ASSIGN;   strcpy(cur_tok.value,"+="); }
                  else                          {            cur_tok.type=TOK_PLUS;          strcpy(cur_tok.value,"+"); } break;
        case '-': if (!at_eof && cur_char=='=') { advance(); cur_tok.type=TOK_MINUS_ASSIGN;  strcpy(cur_tok.value,"-="); }
                  else                          {            cur_tok.type=TOK_MINUS;         strcpy(cur_tok.value,"-"); } break;
        case '.': if (!at_eof && cur_char=='=') { advance(); cur_tok.type=TOK_DOT_ASSIGN;    strcpy(cur_tok.value,".="); }
                  else                          {            cur_tok.type=TOK_DOT;           strcpy(cur_tok.value,"."); } break;
        case '*': cur_tok.type=TOK_STAR;      strcpy(cur_tok.value,"*"); break;
        case '/': cur_tok.type=TOK_SLASH;     strcpy(cur_tok.value,"/"); break;
        case '%': cur_tok.type=TOK_PERCENT;   strcpy(cur_tok.value,"%"); break;
        case ';': cur_tok.type=TOK_SEMICOLON; strcpy(cur_tok.value,";"); break;
        case ',': cur_tok.type=TOK_COMMA;     strcpy(cur_tok.value,","); break;
        case '{': cur_tok.type=TOK_LBRACE;    strcpy(cur_tok.value,"{"); break;
        case '}': cur_tok.type=TOK_RBRACE;    strcpy(cur_tok.value,"}"); break;
        case '(': cur_tok.type=TOK_LPAREN;    strcpy(cur_tok.value,"("); break;
        case ')': cur_tok.type=TOK_RPAREN;    strcpy(cur_tok.value,")"); break;
        default:  compiler_error("unexpected character '%c' (0x%02x)", c, (unsigned char)c);
    }
}

/* ============================================================
 * Parser helpers
 * ========================================================== */
static void expect(TokenType t) {
    if (cur_tok.type != t)
        compiler_error("expected token %d, got %d (near '%s')",
                       t, cur_tok.type, cur_tok.value);
    get_next_token();
}

static void parse_expression(char *out_tmp);
static void parse_statement(void);
static void parse_block(void);
static void parse_else_chain(void);

/* ============================================================
 * Expression parser
 *
 * Precedence (low → high):
 *   comparison     == != === < > <= >=
 *   additive       + - .
 *   multiplicative * / %
 *   unary          ! unary-
 *   primary        literal | $var | $$var | (expr)
 *
 * Each function emits "phc_var NAME = ...;" declarations and
 * writes the result-temporary name into out_tmp (char[16]).
 * ========================================================== */
static void parse_primary(char *out_tmp) {
    newtmp(out_tmp);

    if (cur_tok.type == TOK_INTEGER) {
        emit("phc_var %s = {.type=PHC_LONG,   .value.lval=%sL};", out_tmp, cur_tok.value);
        get_next_token();

    } else if (cur_tok.type == TOK_FLOAT) {
        emit("phc_var %s = {.type=PHC_DOUBLE, .value.dval=%s};",  out_tmp, cur_tok.value);
        get_next_token();

    } else if (cur_tok.type == TOK_STRING) {
        char esc[MAX_TOKEN_LEN * 4];
        escape_c_str(cur_tok.value, esc, sizeof(esc));
        emit("phc_var %s = {.type=PHC_STRING, .value.str=phc_strdup_safe(\"%s\")};",
             out_tmp, esc);
        get_next_token();

    } else if (cur_tok.type == TOK_VARIABLE) {
        emit("phc_var %s = phc_get_var(\"%s\");", out_tmp, cur_tok.value);
        get_next_token();

    } else if (cur_tok.type == TOK_DYNVAR) {
        char inner[16], dname[16];
        newtmp(inner); newtmp(dname);
        emit("phc_var %s  = phc_get_var(\"%s\");", inner,   cur_tok.value);
        emit("char   *%s  = phc_to_string(%s);",   dname,   inner);
        emit("phc_var %s  = phc_get_var(%s);",     out_tmp, dname);
        emit("free(%s);",                           dname);
        get_next_token();

    } else if (cur_tok.type == TOK_LPAREN) {
        get_next_token();
        char sub[16]; parse_expression(sub);
        expect(TOK_RPAREN);
        emit("phc_var %s = %s;", out_tmp, sub);

    } else {
        compiler_error("unexpected token '%s' in expression", cur_tok.value);
    }
}

static void parse_unary(char *out_tmp) {
    if (cur_tok.type == TOK_BANG) {
        get_next_token();
        char sub[16]; parse_unary(sub);
        newtmp(out_tmp);
        emit("phc_var %s = phc_not(%s);", out_tmp, sub);
    } else if (cur_tok.type == TOK_MINUS) {
        get_next_token();
        char sub[16]; parse_unary(sub);
        newtmp(out_tmp);
        emit("phc_var %s = phc_negate(%s);", out_tmp, sub);
    } else {
        parse_primary(out_tmp);
    }
}

static void parse_multiplicative(char *out_tmp) {
    char lhs[16]; parse_unary(lhs); strcpy(out_tmp, lhs);
    while (cur_tok.type==TOK_STAR || cur_tok.type==TOK_SLASH || cur_tok.type==TOK_PERCENT) {
        TokenType op = cur_tok.type; get_next_token();
        char rhs[16]; parse_unary(rhs);
        char res[16]; newtmp(res);
        if      (op==TOK_STAR)    emit("phc_var %s = phc_mul(%s, %s);", res, out_tmp, rhs);
        else if (op==TOK_SLASH)   emit("phc_var %s = phc_div(%s, %s);", res, out_tmp, rhs);
        else                      emit("phc_var %s = phc_mod(%s, %s);", res, out_tmp, rhs);
        strcpy(out_tmp, res);
    }
}

static void parse_additive(char *out_tmp) {
    char lhs[16]; parse_multiplicative(lhs); strcpy(out_tmp, lhs);
    while (cur_tok.type==TOK_PLUS || cur_tok.type==TOK_MINUS || cur_tok.type==TOK_DOT) {
        TokenType op = cur_tok.type; get_next_token();
        char rhs[16]; parse_multiplicative(rhs);
        char res[16]; newtmp(res);
        if      (op==TOK_PLUS)  emit("phc_var %s = phc_add(%s, %s);",    res, out_tmp, rhs);
        else if (op==TOK_MINUS) emit("phc_var %s = phc_sub(%s, %s);",    res, out_tmp, rhs);
        else                    emit("phc_var %s = phc_concat(%s, %s);", res, out_tmp, rhs);
        strcpy(out_tmp, res);
    }
}

static void parse_expression(char *out_tmp) {
    char lhs[16]; parse_additive(lhs); strcpy(out_tmp, lhs);
    while (cur_tok.type==TOK_EQ || cur_tok.type==TOK_NEQ  || cur_tok.type==TOK_IDENTICAL ||
           cur_tok.type==TOK_LT || cur_tok.type==TOK_GT   ||
           cur_tok.type==TOK_LTE|| cur_tok.type==TOK_GTE) {
        TokenType op = cur_tok.type; get_next_token();
        char rhs[16]; parse_additive(rhs);
        char res[16]; newtmp(res);
        switch (op) {
            case TOK_EQ:        emit("phc_var %s = phc_equal(%s, %s);",      res, out_tmp, rhs); break;
            case TOK_NEQ:       emit("phc_var %s = phc_not_equal(%s, %s);",  res, out_tmp, rhs); break;
            case TOK_IDENTICAL: emit("phc_var %s = phc_identical(%s, %s);",  res, out_tmp, rhs); break;
            case TOK_LT:        emit("phc_var %s = phc_less(%s, %s);",       res, out_tmp, rhs); break;
            case TOK_GT:        emit("phc_var %s = phc_greater(%s, %s);",    res, out_tmp, rhs); break;
            case TOK_LTE:       emit("phc_var %s = phc_less_eq(%s, %s);",    res, out_tmp, rhs); break;
            case TOK_GTE:       emit("phc_var %s = phc_greater_eq(%s, %s);", res, out_tmp, rhs); break;
            default: break;
        }
        strcpy(out_tmp, res);
    }
}

/* ============================================================
 * Assignment helper — emits C code for $name <op>= rhs_tmp.
 * Never emits surrounding { }.
 * ========================================================== */
static void emit_assignment(const char *name, TokenType op, const char *rhs) {
    if (op == TOK_ASSIGN) {
        emit("phc_set_var(\"%s\", phc_var_dup(%s));", name, rhs);
    } else {
        char old[16], res[16]; newtmp(old); newtmp(res);
        emit("phc_var %s = phc_get_var(\"%s\");", old, name);
        if      (op == TOK_PLUS_ASSIGN)  emit("phc_var %s = phc_add(%s, %s);",    res, old, rhs);
        else if (op == TOK_MINUS_ASSIGN) emit("phc_var %s = phc_sub(%s, %s);",    res, old, rhs);
        else                             emit("phc_var %s = phc_concat(%s, %s);", res, old, rhs);
        emit("phc_set_var(\"%s\", phc_var_dup(%s));", name, res);
    }
}

/* ============================================================
 * Statement and block parsers
 *
 * SCOPING DESIGN
 * --------------
 * Simple statements (echo, assignment) wrap themselves in { } so their
 * temporaries are block-scoped and cannot clash with sibling statements.
 *
 * Compound statements (if/while/for) do NOT add an outer { } wrapper
 * because:
 *   { if (cond) { … } }  else { … }   ← C error: else without if
 *
 * Instead they manage their own braces, and their condition temporaries
 * are always emitted inside an open brace scope before the keyword that
 * needs them.  Concretely for else if:
 *
 *   else {                  ← opened immediately after consuming 'else'
 *       phc_var tN = …;     ← condition temporaries go INSIDE else scope
 *       if (phc_to_bool(tN)) {
 *           …body…
 *       }
 *   }                       ← closes the else scope
 *
 * Nothing appears between "}" and "else", satisfying C grammar.
 * ========================================================== */
static void parse_block(void) {
    expect(TOK_LBRACE);
    while (cur_tok.type != TOK_RBRACE && cur_tok.type != TOK_EOF)
        parse_statement();
    expect(TOK_RBRACE);
}

/* parse_else_chain — called after every if or else if body closes.
 *
 * If the next token is else, this function:
 *   1. Emits else {  immediately (nothing between } and else).
 *   2. If followed by if: evaluates the condition INSIDE the now-open
 *      else { block, emits if (cond) {, parses the body, emits },
 *      then recurses to handle any further else/else-if BEFORE closing
 *      the outer else {.  Only after the recursion returns does it
 *      emit the closing } for the else { it opened.
 *   3. If plain else: parses the body and closes.
 *
 * Why recursion instead of a loop?
 *   A loop would close the else { before the next else attaches, which
 *   produces } else { at the wrong nesting level.  Recursion keeps each
 *   else { open until its entire inner chain is done, then closes it —
 *   matching exactly what a human would write by hand.
 *
 * Generated C for  if / else if / else if / else:
 *
 *   if (phc_to_bool(t0)) { body0 }
 *   else {
 *     phc_var t1 = ...; int r1 = phc_to_bool(t1);
 *     if (r1) { body1 }
 *     else {
 *       phc_var t2 = ...; int r2 = phc_to_bool(t2);
 *       if (r2) { body2 }
 *       else { body3 }
 *     }
 *   }
 */
static void parse_else_chain(void) {
    if (cur_tok.type != TOK_ELSE) return;   
    /* no else clause — done */
    get_next_token();                        
    /* consume 'else' */

    emit("else {");   
    /* open BEFORE any condition temps — valid C */

    if (cur_tok.type == TOK_IF) {
        get_next_token();                    
        /* consume 'if' */
        expect(TOK_LPAREN);
        char econd[16]; parse_expression(econd);   
        /* temps go inside else { */
        expect(TOK_RPAREN);
        emit("if (phc_to_bool(%s)) {", econd);
        parse_block();
        emit("}");
        parse_else_chain();   
        /* recurse BEFORE closing the else { above */
    } else {
        /* plain else — parse body */
        parse_block();
    }

    emit("}");   /* close the else { we opened at the top */
}

static void parse_statement(void) {

    /* ---- echo expr [, expr]* ; ---- */
    if (cur_tok.type == TOK_ECHO) {
        emit("{");
        get_next_token();
        char tmp[16]; parse_expression(tmp);
        emit("phc_echo(%s);", tmp);
        while (cur_tok.type == TOK_COMMA) {
            get_next_token();
            parse_expression(tmp);
            emit("phc_echo(%s);", tmp);
        }
        expect(TOK_SEMICOLON);
        emit("}");
        return;
    }

    /* ---- $var op= expr ; ---- */
    if (cur_tok.type == TOK_VARIABLE) {
        emit("{");
        char name[MAX_TOKEN_LEN]; strcpy(name, cur_tok.value);
        get_next_token();
        TokenType op = cur_tok.type;
        if (op!=TOK_ASSIGN && op!=TOK_PLUS_ASSIGN &&
            op!=TOK_MINUS_ASSIGN && op!=TOK_DOT_ASSIGN)
            compiler_error("expected assignment operator after '$%s'", name);
        get_next_token();
        char rhs[16]; parse_expression(rhs);
        emit_assignment(name, op, rhs);
        expect(TOK_SEMICOLON);
        emit("}");
        return;
    }

    /* ---- $$var = expr ; ---- */
    if (cur_tok.type == TOK_DYNVAR) {
        emit("{");
        char iname[MAX_TOKEN_LEN]; strcpy(iname, cur_tok.value);
        get_next_token(); expect(TOK_ASSIGN);
        char rhs[16]; parse_expression(rhs);
        char inner[16], dname[16]; newtmp(inner); newtmp(dname);
        emit("phc_var %s = phc_get_var(\"%s\");", inner, iname);
        emit("char   *%s = phc_to_string(%s);",   dname, inner);
        emit("phc_set_var(%s, phc_var_dup(%s));",  dname, rhs);
        emit("free(%s);",                           dname);
        expect(TOK_SEMICOLON);
        emit("}");
        return;
    }

    /* ---- if / else if / else ----
     *
     * parse_else_chain() is called after every if or else if body closes.
     * It handles the optional trailing else/else-if by recursion, ensuring
     * that the next else keyword always appears immediately after the }
     * that closes the preceding body — with nothing in between.
     *
     * Structure of generated C for  if / else if / else:
     *
     *   {                                  <- outer scope: if-cond temps
     *     phc_var tN = ...;
     *     if (phc_to_bool(tN)) { body }
     *     else {                           <- opened by parse_else_chain
     *       phc_var tM = ...;              <- else-if cond temps inside here
     *       if (phc_to_bool(tM)) { body }
     *       else { body }                 <- nested by another parse_else_chain
     *     }
     *   }
     *
     * Key invariant: parse_else_chain() always emits else { BEFORE evaluating
     * any condition temporaries, so nothing ever appears between } and else.
     * The recursion then handles the *next* else/else-if inside the already-open
     * else { block, so it too attaches correctly to its nearest if.
     */
    if (cur_tok.type == TOK_IF) {
        get_next_token();
        expect(TOK_LPAREN);
        char cond[16]; parse_expression(cond);
        expect(TOK_RPAREN);
        emit("if (phc_to_bool(%s)) {", cond);
        parse_block();
        emit("}");
        parse_else_chain();
        return;
    }

    /* ---- while (cond) { body } ----
     *
     * Emitted as:
     *   while (1) {
     *       { <cond-temps>  if (!cond) break; }
     *       { <body> }
     *   }
     *
     * The condition re-evaluates every iteration inside its own { } scope,
     * keeping the condition temporaries out of the body's scope.
     */
    if (cur_tok.type == TOK_WHILE) {
        get_next_token();
        emit("while (1) {");
        emit("{");                               
        /* scope for cond temps    */
        expect(TOK_LPAREN);
        char cond[16]; parse_expression(cond);
        expect(TOK_RPAREN);
        emit("if (!phc_to_bool(%s)) break;", cond);
        emit("}");                               
        /* close cond scope        */
        parse_block();
        emit("}");                               
        /* close while(1)          */
        return;
    }

    /* ---- for (init; cond; post) { body } ----
     *
     * Emitted as:
     *   {                                <- scopes the init variable
     *     { <init-temps> }
     *     while (1) {
     *         { <cond-temps>  if (!cond) break; }
     *         { <body> }
     *         { <post-temps> }
     *     }
     *   }
     *
     * The post-expression lines are "deferred": we record code_cnt before
     * parsing the post expression, parse it into the buffer, then copy the
     * lines out, rewind code_cnt, parse the body, and re-append them.
     */
    if (cur_tok.type == TOK_FOR) {
        get_next_token();
        emit("{");                               
        /* outer for-init scope    */
        expect(TOK_LPAREN);

        /* init */
        if (cur_tok.type != TOK_SEMICOLON) {
            if (cur_tok.type != TOK_VARIABLE)
                compiler_error("for-loop init must be a variable assignment");
            char iname[MAX_TOKEN_LEN]; strcpy(iname, cur_tok.value);
            get_next_token();
            TokenType iop = cur_tok.type;
            if (iop!=TOK_ASSIGN && iop!=TOK_PLUS_ASSIGN &&
                iop!=TOK_MINUS_ASSIGN && iop!=TOK_DOT_ASSIGN)
                compiler_error("expected assignment operator in for-init");
            get_next_token();
            emit("{");
            char irhs[16]; parse_expression(irhs);
            emit_assignment(iname, iop, irhs);
            emit("}");
        }
        expect(TOK_SEMICOLON);

        emit("while (1) {");

        /* condition */
        emit("{");                               
        /* scope for cond temps    */
        if (cur_tok.type != TOK_SEMICOLON) {
            char cond[16]; parse_expression(cond);
            emit("if (!phc_to_bool(%s)) break;", cond);
        }
        emit("}");                               
        /* close cond scope        */
        expect(TOK_SEMICOLON);

        /* post — deferred emit */
        int   post_start = code_cnt;
        if (cur_tok.type != TOK_RPAREN) {
            if (cur_tok.type != TOK_VARIABLE)
                compiler_error("for-loop post must be a variable assignment");
            char pname[MAX_TOKEN_LEN]; strcpy(pname, cur_tok.value);
            get_next_token();
            TokenType pop = cur_tok.type;
            if (pop!=TOK_ASSIGN && pop!=TOK_PLUS_ASSIGN &&
                pop!=TOK_MINUS_ASSIGN && pop!=TOK_DOT_ASSIGN)
                compiler_error("expected assignment operator in for-post");
            get_next_token();
            emit("{");
            char prhs[16]; parse_expression(prhs);
            emit_assignment(pname, pop, prhs);
            emit("}");
        }
        int   post_n   = code_cnt - post_start;
        char *post_buf = NULL;
        if (post_n > 0) {
            post_buf = malloc((size_t)post_n * EMIT_LINE_SIZE);
            if (!post_buf) { fputs("FATAL: malloc post_buf\n", stderr); exit(1); }
            memcpy(post_buf,
                   code_buf + (size_t)post_start * EMIT_LINE_SIZE,
                   (size_t)post_n * EMIT_LINE_SIZE);
            code_cnt = post_start;               
            /* rewind — undo post lines */
        }
        expect(TOK_RPAREN);

        parse_block();

        for (int i = 0; i < post_n; i++)
            emit("%s", post_buf + (size_t)i * EMIT_LINE_SIZE);
        free(post_buf);

        emit("}");                               
        /* close while(1)          */
        emit("}");                               
        /* close outer for scope   */
        return;
    }

    /* End of PHP block */
    if (cur_tok.type == TOK_CLOSE_TAG || cur_tok.type == TOK_EOF) return;

    compiler_error("unexpected token '%s' at start of statement", cur_tok.value);
}

/* ============================================================
 * Program parser — handles multiple <?php … ?> blocks
 * ========================================================== */
static void parse_program(void) {
    while (!at_eof) {
        while (!at_eof && cur_tok.type != TOK_OPEN_TAG) get_next_token();
        if (cur_tok.type != TOK_OPEN_TAG) break;
        get_next_token();   /* consume <?php */
        while (cur_tok.type != TOK_EOF && cur_tok.type != TOK_CLOSE_TAG)
            parse_statement();
        if (cur_tok.type == TOK_CLOSE_TAG) get_next_token();   /* consume ?> */
    }
}

/* ============================================================
 * Entry point
 * ========================================================== */
int main(int argc, char *argv[]) {
    if (argc < 3) {
        fprintf(stderr, "Usage: %s <input.php> <output.c>\n", argv[0]);
        return 1;
    }

    infile = fopen(argv[1], "r");
    if (!infile) { fprintf(stderr, "Error: cannot open '%s': ", argv[1]); perror(NULL); return 1; }

    outfile = fopen(argv[2], "w");
    if (!outfile) {
        fprintf(stderr, "Error: cannot write '%s': ", argv[2]);
        perror(NULL); fclose(infile); return 1;
    }

    buf_init();
    advance();          /* prime character stream */
    get_next_token();   /* prime token stream     */

    parse_program();
    write_output();

    free(code_buf);
    fclose(infile);
    fclose(outfile);

    printf("Compiled: %s -> %s\n", argv[1], argv[2]);
    return 0;
}