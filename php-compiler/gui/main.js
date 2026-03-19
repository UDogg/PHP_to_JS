/**
 * gui/main.js
 * Electron Main Process - Orchestrates compilation pipeline
 * 
 * Responsibilities:
 * 1. Create BrowserWindow
 * 2. Handle IPC from renderer (compile requests)
 * 3. Spawn child processes: phc (PHP→C) then gcc (C→binary)
 * 4. Stream progress updates to renderer
 * 5. Handle errors gracefully
 */

const { app, BrowserWindow, ipcMain } = require('electron');
const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');

// Global reference to prevent GC
let mainWindow = null;

// Compilation stage weights for progress bar
const STAGES = {
  INIT: { weight: 5, message: 'Initializing...' },
  PHC_START: { weight: 10, message: 'Starting PHP transpiler...' },
  PHC_RUNNING: { weight: 25, message: 'Parsing PHP...' },
  PHC_DONE: { weight: 5, message: 'PHP transpiled to C' },
  GCC_START: { weight: 5, message: 'Starting GCC...' },
  GCC_COMPILE: { weight: 35, message: 'Compiling C to object code...' },
  GCC_LINK: { weight: 10, message: 'Linking executable...' },
  GCC_DONE: { weight: 5, message: 'Compilation complete' }
};

/**
 * Calculate cumulative progress percentage for a given stage
 * @param {string} stageKey - Key from STAGES object
 * @returns {number} 0-100 percentage
 */
function calculateProgress(stageKey) {
  const stages = Object.keys(STAGES);
  const currentIndex = stages.indexOf(stageKey);
  if (currentIndex === -1) return 0;
  
  let cumulative = 0;
  for (let i = 0; i <= currentIndex; i++) {
    cumulative += STAGES[stages[i]].weight;
  }
  return Math.min(cumulative, 100);
}

/**
 * Send progress update to renderer
 * @param {BrowserWindow} win - Target window
 * @param {string} stage - Stage key
 * @param {string} [extraLog] - Optional log line for console
 */
function sendProgress(win, stage, extraLog = null) {
  const data = {
    percent: calculateProgress(stage),
    message: STAGES[stage].message
  };
  if (extraLog) data.log = extraLog;
  win.webContents.send('compile-progress', data);
}

/**
 * Send error to renderer
 * @param {BrowserWindow} win 
 * @param {string} error 
 * @param {string} [details]
 */
function sendError(win, error, details = null) {
  win.webContents.send('compile-error', {
    message: error,
    details: details
  });
}

/**
 * Send success to renderer
 * @param {BrowserWindow} win 
 * @param {string} outputPath 
 */
function sendSuccess(win, outputPath) {
  win.webContents.send('compile-success', {
    message: 'Compilation successful',
    outputPath: outputPath
  });
}

/**
 * Resolve project-relative path
 * @param {string} relativePath 
 * @returns {string} Absolute path
 */
function projectPath(relativePath) {
  // __dirname is gui/, so go up one level to project root
  return path.join(__dirname, '..', relativePath);
}

/**
 * Check if a command exists in PATH
 * @param {string} cmd 
 * @returns {Promise<boolean>}
 */
function commandExists(cmd) {
  return new Promise((resolve) => {
    const child = spawn(
      process.platform === 'win32' ? 'where' : 'which',
      [cmd],
      { stdio: 'ignore' }
    );
    child.on('exit', (code) => resolve(code === 0));
    child.on('error', () => resolve(false));
  });
}

/**
 * Run a child process with promise-based API
 * @param {string} cmd 
 * @param {string[]} args 
 * @param {object} options 
 * @returns {Promise<{stdout: string, stderr: string}>}
 */
function runProcess(cmd, args, options = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(cmd, args, {
      ...options,
      shell: process.platform === 'win32'  // Use shell on Windows for path resolution
    });
    
    let stdout = '';
    let stderr = '';
    
    child.stdout?.on('data', (data) => {
      stdout += data.toString();
      if (options.onStdout) options.onStdout(data.toString());
    });
    
    child.stderr?.on('data', (data) => {
      stderr += data.toString();
      if (options.onStderr) options.onStderr(data.toString());
    });
    
    child.on('error', (err) => reject(err));
    
    child.on('close', (code) => {
      if (code === 0) {
        resolve({ stdout, stderr });
      } else {
        reject(new Error(`${cmd} exited with code ${code}\n${stderr}`));
      }
    });
  });
}

/**
 * Main compilation pipeline
 * @param {BrowserWindow} win 
 * @param {object} config 
 */
async function runCompilation(win, config) {
  const { inputPhp, outputC, outputBin, cCorePath, buildMode } = config;
  
  try {
    // Validate input file exists
    if (!fs.existsSync(inputPhp)) {
      throw new Error(`Input file not found: ${inputPhp}`);
    }
    
    // Ensure temp directory exists
    const tempDir = path.dirname(outputC);
    if (!fs.existsSync(tempDir)) {
      fs.mkdirSync(tempDir, { recursive: true });
    }
    
    // ===== STAGE 1: PHP → C (using our phc compiler) =====
    sendProgress(win, 'PHC_START');
    
    const phcPath = projectPath('c_core/phc');
    
    // Check phc binary exists
    if (!fs.existsSync(phcPath)) {
      throw new Error(
        `Compiler binary not found: ${phcPath}\n` +
        `Please build the compiler first: ./build_compiler.sh`
      );
    }
    
    // Run phc
    await runProcess(phcPath, [inputPhp, outputC], {
      onStderr: (data) => {
        // Forward compiler warnings/errors to console
        win.webContents.send('compile-log', { level: 'warn', message: data.trim() });
      }
    });
    
    // Verify output.c was created
    if (!fs.existsSync(outputC)) {
      throw new Error('Transpilation failed: output.c was not created');
    }
    
    sendProgress(win, 'PHC_DONE');
    
    // ===== STAGE 2: C → Binary (using GCC) =====
    sendProgress(win, 'GCC_START');
    
    // Check GCC exists
    const gccCmd = process.platform === 'win32' ? 'gcc.exe' : 'gcc';
    if (!(await commandExists(gccCmd))) {
      throw new Error(
        `GCC not found in PATH.\n` +
        `Please install a C compiler:\n` +
        `• Linux: sudo apt install build-essential\n` +
        `• macOS: xcode-select --install\n` +
        `• Windows: Install MinGW-w64 or use WSL`
      );
    }
    
    // Build GCC arguments
    const gccArgs = [
      outputC,
      '-o', outputBin,
      '-I', cCorePath,  // Include path for phc_runtime.h
      '-std=c11'        // C11 standard for modern features
    ];
    
    // Add optimization flags based on build mode
    if (buildMode === 'release') {
      gccArgs.push('-O2', '-DNDEBUG');
      sendProgress(win, 'GCC_COMPILE', 'Mode: Release (optimized)');
    } else {
      gccArgs.push('-O0', '-g', '-DDEBUG');  // Debug: no opt, with symbols
      sendProgress(win, 'GCC_COMPILE', 'Mode: Debug (fast compile)');
    }
    
    // Track GCC progress by parsing verbose output
    let gccPhase = 'compile';
    
    await runProcess(gccCmd, gccArgs, {
      cwd: projectPath(''),  // Run from project root
      onStderr: (data) => {
        const line = data.trim();
        if (!line) return;
        
        // Detect linking phase from GCC verbose output
        if (line.includes('collect2') || line.includes('ld ') || line.includes('LINK')) {
          if (gccPhase !== 'link') {
            gccPhase = 'link';
            sendProgress(win, 'GCC_LINK');
          }
        }
        
        // Forward relevant logs (filter noise)
        if (line.includes('error:') || line.includes('warning:')) {
          win.webContents.send('compile-log', { 
            level: line.includes('error:') ? 'error' : 'warn',
            message: line 
          });
        }
      }
    });
    
    // Verify binary was created
    if (!fs.existsSync(outputBin)) {
      throw new Error('GCC linking failed: executable was not created');
    }
    
    // Make executable on Unix-like systems
    if (process.platform !== 'win32') {
      fs.chmodSync(outputBin, 0o755);
    }
    
    sendProgress(win, 'GCC_DONE');
    
    // Success!
    sendSuccess(win, outputBin);
    
  } catch (err) {
    console.error('Compilation failed:', err);
    sendError(win, err.message, err.stack);
  }
}

/**
 * Create the main application window
 */
function createWindow() {
  mainWindow = new BrowserWindow({
    width: 1000,
    height: 700,
    minWidth: 800,
    minHeight: 500,
    title: 'PHP Native Compiler',
    webPreferences: {
      nodeIntegration: false,      // Security: disable Node in renderer
      contextIsolation: true,      // Security: isolate contexts
      preload: path.join(__dirname, 'preload.js'),  // Secure IPC bridge
      sandbox: true,               // Additional renderer sandboxing
      devTools: process.env.NODE_ENV === 'development'  // DevTools in dev only
    },
    // Platform-specific tweaks
    ...(process.platform === 'darwin' ? {
      titleBarStyle: 'hiddenInset',
      trafficLightPosition: { x: 10, y: 10 }
    } : {})
  });
  
  // Load the GUI
  mainWindow.loadFile(path.join(__dirname, 'index.html'));
  
  // Handle window close
  mainWindow.on('closed', () => {
    mainWindow = null;
  });
  
  // Optional: Open DevTools in development
  if (process.env.NODE_ENV === 'development') {
    mainWindow.webContents.openDevTools({ mode: 'bottom' });
  }
}

/**
 * App initialization
 */
app.whenReady().then(() => {
  // Register IPC handler for compile requests
  ipcMain.handle('compile-request', async (event, config) => {
    // Validate config
    const required = ['inputPhp', 'outputC', 'outputBin', 'cCorePath'];
    for (const key of required) {
      if (!config[key]) {
        throw new Error(`Missing required config: ${key}`);
      }
    }
    
    // Run compilation (async, sends progress via events)
    await runCompilation(BrowserWindow.fromWebContents(event.sender), {
      ...config,
      buildMode: config.buildMode || 'debug'  // Default to debug
    });
    
    // Return final status (progress/success/error sent via events)
    return { status: 'completed' };
  });
  
  // Optional: Handle "open file" from OS
  app.on('open-file', (event, filePath) => {
    if (mainWindow) {
      mainWindow.webContents.send('file-opened', filePath);
    }
  });
  
  createWindow();
  
  // macOS: Re-create window when dock icon clicked
  app.on('activate', () => {
    if (BrowserWindow.getAllWindows().length === 0) {
      createWindow();
    }
  });
});

// Quit when all windows closed (except macOS)
app.on('window-all-closed', () => {
  if (process.platform !== 'darwin') {
    app.quit();
  }
});

// Graceful shutdown
app.on('before-quit', () => {
  // Cleanup: could kill any running child processes here
  // For now, rely on OS to clean up when parent exits
});

// Export for testing (if needed)
if (process.env.NODE_ENV === 'test') {
  module.exports = { runCompilation, calculateProgress, STAGES };
}
