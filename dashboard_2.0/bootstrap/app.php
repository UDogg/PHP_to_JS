<?php

use App\Http\Middleware\DecryptPayloadMiddleware;
use App\Http\Middleware\EncryptResponseMiddleware;
use App\Http\Middleware\ValidateTokenAU;
use App\Http\Middleware\ValidateTokenIPPB;
use Illuminate\Foundation\Application;
use Illuminate\Foundation\Configuration\Exceptions;
use Illuminate\Foundation\Configuration\Middleware;
use App\Http\Middleware\UpdateUserType;
use App\Http\Middleware\ValidateToken;
use App\Http\Middleware\ThirdPartyTokenGenerationMiddleware;
use App\Http\Middleware\SecureHeaders;
use App\Http\Middleware\BasicAuthMiddleware;
return Application::configure(basePath: dirname(__DIR__))
    ->withRouting(
        web: __DIR__.'/../routes/web.php',
        api: __DIR__.'/../routes/api.php',
        commands: __DIR__.'/../routes/console.php',
        health: '/up',
    )
    ->withMiddleware(function (Middleware $middleware) {
        $middleware->append([UpdateUserType::class,SecureHeaders::class]);

        $middleware->alias([
            'validate.token' => ValidateToken::class, // Add the ValidateToken middleware alias
            'validate.token.au' => ValidateTokenAU::class, // for AU
            'validate.token.ippb' => ValidateTokenIPPB::class, // for IPPB
            'decrypt.payload' => DecryptPayloadMiddleware::class,
            'encrypt.response' => EncryptResponseMiddleware::class,
            'auth' => \App\Http\Middleware\Authenticate::class,
            'basic.auth' => BasicAuthMiddleware::class,
        ]);
        $middleware->validateCsrfTokens(except: [
            'validate_token',
            'cron/posupload'
        ]);
    })
    ->withExceptions(function (Exceptions $exceptions) {
        //
    })->create();
