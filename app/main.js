const { app, BrowserWindow, ipcMain, nativeTheme, dialog, Menu, shell } = require('electron');
const path = require('path');
const { SerialPort } = require('serialport');
const { usb: usbInstance } = require('usb');
const fs = require('fs');
const { flashFirmware, cancelFlash } = require('./flasher');
const { spawn, spawnSync } = require('child_process');
const { buildExtensionRuntime, readInstalledState } = require('./extensions/runtime');
const {
    DEFAULT_PLATFORMIO_HOME,
    DEFAULT_PLATFORMIO_VENV_PATH,
    getCompileCommandsPath,
    readPlatformioProjectConfig,
    resolveCompileCommandsState,
    resolvePlatformioActionArgs,
    selectPlatformioEnv,
} = require('./firmware/platformio');
const {
    getManagedClangdExecutable,
    getManagedClangdRoot,
    readManagedClangdState,
    writeManagedClangdState,
    getManagedPlatformioCoreDir,
    getManagedPlatformioExecutable,
    getManagedPlatformioPython,
    getManagedPlatformioRoot,
    readManagedPlatformioState,
    writeManagedPlatformioState,
} = require('./firmware/toolchain');
const { ClangdClient, toDocumentUri } = require('./firmware/clangd-client');
const {
    FIRMWARE_FOCUSED_FILES,
    getFirmwareWorkspaceStatePath,
    listAdvancedWorkspaceEntries,
    listFocusedWorkspaceEntries,
    pickDefaultActiveFile,
    readFirmwareWorkspaceState,
    readWorkspaceTextFile,
    resolveWorkspacePath,
    validateFirmwareWorkspaceRoot,
    writeFirmwareWorkspaceState,
    writeWorkspaceTextFile,
} = require('./firmware/workspace');

const argv = process.argv || [];
const noGpu = argv.includes('--no-gpu') || argv.includes('--disable-gpu');
if (noGpu) {
    // Must be called before app is ready
    app.disableHardwareAcceleration();
    app.commandLine.appendSwitch('disable-gpu');
}

if (process.env.MODULAR_USER_DATA_DIR) {
    try {
        app.setPath('userData', path.resolve(process.env.MODULAR_USER_DATA_DIR));
    } catch (err) {
        console.warn('Failed to override userData path:', err?.message || err);
    }
}

// Set ENABLE_THINGSET for preload.js detection; extension runtime handles actual enablement.
if (process.env.ENABLE_THINGSET === undefined) {
    process.env.ENABLE_THINGSET = app.isPackaged ? '0' : '1';
}

// Shared context passed to extension main entries. Properties populated below as they become available.
const extensionSharedContext = { ipcMain, app };

// Installed bundles live under userData so they survive app updates.
let installedRoot = null;
try {
    installedRoot = path.join(app.getPath('userData'), 'extensions');
} catch { /* userData unavailable before ready on some platforms — bundles discovered at boot only */ }

const extensionRuntime = buildExtensionRuntime({
    appRoot: __dirname,
    env: process.env,
    logger: console,
    extensionContext: extensionSharedContext,
    installedRoot,
});

function cloneExtensionInventory() {
    return extensionRuntime.inventory.map((entry) => ({
        ...entry,
        capabilities: Array.isArray(entry.capabilities) ? entry.capabilities.slice() : [],
    }));
}

function cloneExtensionBootstrap() {
    return {
        rendererScripts: extensionRuntime.bootstrap.rendererScripts.map((entry) => ({ ...entry })),
        flags: { ...extensionRuntime.bootstrap.flags },
        extensions: cloneExtensionInventory(),
        widgetDocsRoots: extensionRuntime.bootstrap.widgetDocsRoots.map((entry) => ({ ...entry })),
        exampleRoots: extensionRuntime.bootstrap.exampleRoots.map((entry) => ({ ...entry })),
        coursewareRoots: extensionRuntime.bootstrap.coursewareRoots.map((entry) => ({ ...entry })),
        tutorialRoots: extensionRuntime.bootstrap.tutorialRoots.map((entry) => ({ ...entry })),
        dashboardWelcomePaths: extensionRuntime.bootstrap.dashboardWelcomePaths.map((entry) => ({ ...entry })),
        dashboardRoots: extensionRuntime.bootstrap.dashboardRoots.map((entry) => ({ ...entry })),
        widgetDocs: extensionRuntime.bootstrap.widgetDocs.map((entry) => ({ ...entry })),
        courseware: extensionRuntime.bootstrap.courseware.map((entry) => ({ ...entry })),
        tutorials: extensionRuntime.bootstrap.tutorials.map((entry) => ({
            ...entry,
            menuSegments: Array.isArray(entry.menuSegments) ? entry.menuSegments.slice() : [],
            steps: Array.isArray(entry.steps) ? entry.steps.map((step) => ({ ...step })) : [],
        })),
        dashboardWelcomeEntries: extensionRuntime.bootstrap.dashboardWelcomeEntries.map((entry) => ({
            ...entry,
            actions: Array.isArray(entry.actions) ? entry.actions.map((action) => ({ ...action })) : [],
        })),
        datasources: extensionRuntime.bootstrap.datasources.map((entry) => ({ ...entry })),
    };
}

let mainWindow; // reference to the main BrowserWindow
let exampleWindow; // dedicated window for docs and lab actions
let firmwareWindow; // dedicated window for firmware editing sessions
let firmwareBuildJob = null; // currently running PlatformIO child process
let firmwareBuildSequence = 0;
let firmwarePlatformioCache = null;
let firmwareClangdCache = null;
let firmwareToolchainJob = null;
let firmwareLanguageClient = null;
let firmwareLanguageClientKey = null;
let exampleTabRequestTimer; // debounce docs tab requests
let pendingDocTabRequest = null; // last requested docs tab (for late renderer init)
// Track docs window docking previews/selection so popped tabs can be dragged back.
let exampleWindowActiveRef = null;
let exampleDockPreviewActive = false;
let exampleDockMoveTimer = null;
let exampleDockLastOverlap = false;
let exampleDockingInProgress = false;
let pendingWidgetDocType = null; // Track widget doc tab requests before renderer init.
let pendingTutorialRequest = null; // Track tutorial tab requests before renderer init.

function buildTimestampStamp(date = new Date()) {
    const pad = (value) => String(value).padStart(2, '0');
    return `${date.getFullYear()}-${pad(date.getMonth() + 1)}-${pad(date.getDate())}_${pad(date.getHours())}-${pad(date.getMinutes())}-${pad(date.getSeconds())}`;
}

function resolveTimestampedCsvPath(filePath, defaultDir) {
    const target = String(filePath || '').trim();
    if (!target) return target;
    const parsed = path.parse(target);
    const ext = parsed.ext || '.csv';
    const baseName = parsed.name || 'fast_frame';
    // Fall back to defaultDir (or acquireDir once declared) so relative names
    // never resolve against the process cwd (can be System32 on Windows).
    const dir = parsed.dir || defaultDir || '.';
    return path.join(dir, `${buildTimestampStamp()}-${baseName}${ext}`);
}

function isFirmwareWorkspaceEnabled() {
    return extensionRuntime.isEnabled('owntech-workspace');
}

function getFirmwareWorkspaceSessionPath() {
    return getFirmwareWorkspaceStatePath(app.getPath('userData'));
}

function readFirmwareSessionState() {
    return readFirmwareWorkspaceState(getFirmwareWorkspaceSessionPath());
}

function writeFirmwareSessionState(patch) {
    const currentState = readFirmwareSessionState();
    const nextState = {
        ...currentState,
        ...(patch && typeof patch === 'object' && !Array.isArray(patch) ? patch : {}),
    };
    return writeFirmwareWorkspaceState(getFirmwareWorkspaceSessionPath(), nextState);
}

function resolveFirmwareWorkspaceContext(inputState = null) {
    const persistedState = inputState || readFirmwareSessionState();
    if (!persistedState.workspaceRoot) {
        return {
            persistedState,
            workspaceRoot: null,
            invalidWorkspaceRoot: null,
            validationError: null,
            activeFile: null,
        };
    }

    try {
        const workspaceRoot = validateFirmwareWorkspaceRoot(persistedState.workspaceRoot);
        let activeFile = null;
        if (persistedState.activeFile) {
            try {
                const resolved = resolveWorkspacePath(workspaceRoot, persistedState.activeFile);
                if (fs.existsSync(resolved.absolutePath) && fs.statSync(resolved.absolutePath).isFile()) {
                    activeFile = resolved.relativePath;
                }
            } catch { /* fall back to a default file below */ }
        }
        if (!activeFile) {
            activeFile = pickDefaultActiveFile(workspaceRoot);
        }
        return {
            persistedState,
            workspaceRoot,
            invalidWorkspaceRoot: null,
            validationError: null,
            activeFile,
        };
    } catch (err) {
        return {
            persistedState,
            workspaceRoot: null,
            invalidWorkspaceRoot: persistedState.workspaceRoot,
            validationError: err?.message || String(err),
            activeFile: null,
        };
    }
}

function listFirmwareWorkspaceEntries(context) {
    if (!context || !context.workspaceRoot) return [];
    return context.persistedState.advancedMode
        ? listAdvancedWorkspaceEntries(context.workspaceRoot, { maxDepth: 4 })
        : listFocusedWorkspaceEntries(context.workspaceRoot);
}

function emitFirmwareToolchainStatus(nextState = null) {
    if (!firmwareWindow || firmwareWindow.isDestroyed() || !firmwareWindow.webContents) return;
    firmwareWindow.webContents.send('firmware-toolchain-status', nextState || getFirmwareToolchainStatus());
}

function emitFirmwareBuildOutput(payload) {
    if (!firmwareWindow || firmwareWindow.isDestroyed() || !firmwareWindow.webContents) return;
    firmwareWindow.webContents.send('firmware-build-output', payload);
}

function emitFirmwareBuildState(nextState = null) {
    if (!firmwareWindow || firmwareWindow.isDestroyed() || !firmwareWindow.webContents) return;
    firmwareWindow.webContents.send('firmware-build-state', nextState || getFirmwareBuildState());
}

function emitFirmwareLanguageDiagnostics(payload) {
    if (!firmwareWindow || firmwareWindow.isDestroyed() || !firmwareWindow.webContents) return;
    firmwareWindow.webContents.send('firmware-language-diagnostics', payload);
}

function emitFirmwareLanguageState(nextState = null) {
    if (!firmwareWindow || firmwareWindow.isDestroyed() || !firmwareWindow.webContents) return;
    firmwareWindow.webContents.send('firmware-language-state', nextState || getFirmwareLanguageState());
}

function getManagedPlatformioState() {
    return readManagedPlatformioState(app.getPath('userData'));
}

function getManagedClangdState() {
    return readManagedClangdState(app.getPath('userData'));
}

function writeManagedPlatformioRuntimeState(patch) {
    const current = getManagedPlatformioState();
    return writeManagedPlatformioState(app.getPath('userData'), {
        ...current,
        ...(patch && typeof patch === 'object' && !Array.isArray(patch) ? patch : {}),
    });
}

function writeManagedClangdRuntimeState(patch) {
    const current = getManagedClangdState();
    return writeManagedClangdState(app.getPath('userData'), {
        ...current,
        ...(patch && typeof patch === 'object' && !Array.isArray(patch) ? patch : {}),
    });
}

function emitFirmwareWorkspaceState(nextState = null) {
    if (!firmwareWindow || firmwareWindow.isDestroyed() || !firmwareWindow.webContents) return;
    const state = nextState || getFirmwareWorkspaceState();
    firmwareWindow.webContents.send('firmware-workspace-state', state);
}

function canWriteDirectory(targetPath) {
    try {
        fs.accessSync(targetPath, fs.constants.W_OK);
        return true;
    } catch {
        return false;
    }
}

function getFirmwarePlatformioCacheKey() {
    return JSON.stringify({
        envPath: process.env.MODULAR_FIRMWARE_PIO_PATH || '',
        disableLocal: process.env.MODULAR_FIRMWARE_DISABLE_LOCAL_PIO === '1',
        managedPath: getManagedPlatformioState().path || '',
        managedStatus: getManagedPlatformioState().status || '',
    });
}

function formatSpawnProbeError(probe, fallbackLabel) {
    const stderr = typeof probe?.stderr === 'string' ? probe.stderr.trim() : '';
    if (stderr) return stderr;
    const stdout = typeof probe?.stdout === 'string' ? probe.stdout.trim() : '';
    if (stdout) return stdout;
    if (probe?.error?.message) return probe.error.message;
    if (probe?.signal) return `${fallbackLabel} exited via ${probe.signal}`;
    if (probe && probe.status !== null && probe.status !== undefined) {
        return `${fallbackLabel} exited with code ${probe.status}`;
    }
    return `${fallbackLabel} could not be executed.`;
}

function probePlatformioExecutable(executablePath, source, extraEnv = {}) {
    if (!executablePath) {
        return {
            available: false,
            path: executablePath || null,
            source,
            version: null,
            error: 'Missing PlatformIO executable path.',
        };
    }

    try {
        const probe = spawnSync(executablePath, ['--version'], {
            env: {
                ...process.env,
                PLATFORMIO_SETTING_ENABLE_TELEMETRY: 'no',
                ...extraEnv,
            },
            encoding: 'utf8',
            timeout: 5000,
            windowsHide: true,
        });
        if (probe.status === 0) {
            return {
                available: true,
                path: executablePath,
                source,
                version: `${probe.stdout || ''}${probe.stderr || ''}`.trim().split(/\r?\n/)[0] || 'PlatformIO available',
                error: null,
            };
        }
        return {
            available: false,
            path: executablePath,
            source,
            version: null,
            error: formatSpawnProbeError(probe, 'PlatformIO'),
        };
    } catch (err) {
        return {
            available: false,
            path: executablePath,
            source,
            version: null,
            error: err?.message || String(err),
        };
    }
}

function getFirmwareClangdCacheKey() {
    return JSON.stringify({
        envPath: process.env.MODULAR_FIRMWARE_CLANGD_PATH || '',
        disableLocal: process.env.MODULAR_FIRMWARE_DISABLE_LOCAL_CLANGD === '1',
        managedPath: getManagedClangdState().path || '',
        managedStatus: getManagedClangdState().status || '',
    });
}

function probeClangdExecutable(executablePath, source) {
    if (!executablePath) {
        return {
            available: false,
            path: executablePath || null,
            source,
            version: null,
            error: 'Missing clangd executable path.',
        };
    }

    try {
        const probe = spawnSync(executablePath, ['--version'], {
            env: process.env,
            encoding: 'utf8',
            timeout: 5000,
            windowsHide: true,
        });
        if (probe.status === 0) {
            return {
                available: true,
                path: executablePath,
                source,
                version: `${probe.stdout || ''}${probe.stderr || ''}`.trim().split(/\r?\n/)[0] || 'clangd available',
                error: null,
            };
        }
        return {
            available: false,
            path: executablePath,
            source,
            version: null,
            error: formatSpawnProbeError(probe, 'clangd'),
        };
    } catch (err) {
        return {
            available: false,
            path: executablePath,
            source,
            version: null,
            error: err?.message || String(err),
        };
    }
}

function resolveManagedPlatformioStatus() {
    const state = getManagedPlatformioState();
    const managedRoot = getManagedPlatformioRoot(app.getPath('userData'));
    const coreDir = state.coreDir || getManagedPlatformioCoreDir(app.getPath('userData'));
    const executablePath = state.path || getManagedPlatformioExecutable(app.getPath('userData'));
    const status = firmwareToolchainJob ? 'installing' : state.status;
    const installError = firmwareToolchainJob ? null : state.lastError;

    if (status === 'installing') {
        return {
            available: false,
            managed: true,
            source: 'managed',
            status: 'installing',
            version: state.version,
            path: executablePath,
            coreDir,
            rootDir: managedRoot,
            error: null,
            installedAt: state.installedAt,
        };
    }

    const probe = probePlatformioExecutable(executablePath, 'managed', {
        PLATFORMIO_CORE_DIR: coreDir,
    });
    if (probe.available) {
        if (state.status !== 'installed' || state.version !== probe.version || state.path !== executablePath || state.coreDir !== coreDir) {
            writeManagedPlatformioRuntimeState({
                status: 'installed',
                version: probe.version,
                path: executablePath,
                coreDir,
                lastError: null,
                installedAt: state.installedAt || new Date().toISOString(),
            });
        }
        return {
            ...probe,
            managed: true,
            status: 'installed',
            coreDir,
            rootDir: managedRoot,
            installedAt: state.installedAt,
        };
    }

    return {
        available: false,
        managed: true,
        source: 'managed',
        status: state.status === 'installed' ? 'broken' : (state.status || 'not-installed'),
        version: state.version,
        path: executablePath,
        coreDir,
        rootDir: managedRoot,
        error: installError || probe.error,
        installedAt: state.installedAt,
    };
}

function resolveManagedClangdStatus() {
    const state = getManagedClangdState();
    const managedRoot = getManagedClangdRoot(app.getPath('userData'));
    const executablePath = state.path || getManagedClangdExecutable(app.getPath('userData'));
    const status = firmwareToolchainJob ? 'installing' : state.status;
    const installError = firmwareToolchainJob ? null : state.lastError;

    if (status === 'installing') {
        return {
            available: false,
            managed: true,
            source: 'managed',
            status: 'installing',
            version: state.version,
            path: executablePath,
            rootDir: managedRoot,
            error: null,
            installedAt: state.installedAt,
        };
    }

    const probe = probeClangdExecutable(executablePath, 'managed');
    if (probe.available) {
        if (state.status !== 'installed' || state.version !== probe.version || state.path !== executablePath) {
            writeManagedClangdRuntimeState({
                status: 'installed',
                version: probe.version,
                path: executablePath,
                lastError: null,
                installedAt: state.installedAt || new Date().toISOString(),
            });
        }
        return {
            ...probe,
            managed: true,
            status: 'installed',
            rootDir: managedRoot,
            installedAt: state.installedAt,
        };
    }

    return {
        available: false,
        managed: true,
        source: 'managed',
        status: state.status === 'installed' ? 'broken' : (state.status || 'not-installed'),
        version: state.version,
        path: executablePath,
        rootDir: managedRoot,
        error: installError || probe.error,
        installedAt: state.installedAt,
    };
}

function resolveFirmwarePlatformioStatus(options = {}) {
    const forceRefresh = !!options.forceRefresh;
    const cacheKey = getFirmwarePlatformioCacheKey();
    if (!forceRefresh && firmwarePlatformioCache && firmwarePlatformioCache.cacheKey === cacheKey) {
        return firmwarePlatformioCache.result;
    }

    const managed = resolveManagedPlatformioStatus();
    if (managed.available) {
        const result = {
            available: true,
            source: managed.source,
            path: managed.path,
            version: managed.version,
            managed: true,
            coreDir: managed.coreDir,
            errors: [],
            managedStatus: managed.status,
        };
        firmwarePlatformioCache = { cacheKey, result };
        return result;
    }

    const disableLocal = process.env.MODULAR_FIRMWARE_DISABLE_LOCAL_PIO === '1';
    const candidates = [];
    const pushCandidate = (candidatePath, source) => {
        if (!candidatePath) return;
        if (candidates.some((entry) => entry.path === candidatePath)) return;
        candidates.push({ path: candidatePath, source });
    };
    if (!disableLocal) {
        pushCandidate(process.env.MODULAR_FIRMWARE_PIO_PATH, 'env');
        pushCandidate(DEFAULT_PLATFORMIO_VENV_PATH, 'local-venv');
        pushCandidate('pio', 'path');
    }

    const errors = managed.error ? [{ path: managed.path, source: 'managed', error: managed.error }] : [];
    for (const candidate of candidates) {
        const probe = probePlatformioExecutable(candidate.path, candidate.source);
        if (probe.available) {
            const result = {
                available: true,
                source: candidate.source,
                path: candidate.path,
                version: probe.version,
                managed: false,
                coreDir: null,
                errors,
                managedStatus: managed.status,
            };
            firmwarePlatformioCache = { cacheKey, result };
            return result;
        }
        errors.push({
            path: candidate.path,
            source: candidate.source,
            error: probe.error,
        });
    }

    const result = {
        available: false,
        source: 'none',
        path: null,
        version: null,
        managed: false,
        coreDir: managed.coreDir || null,
        managedStatus: managed.status,
        errors,
    };
    firmwarePlatformioCache = { cacheKey, result };
    return result;
}

function resolveFirmwareClangdStatus(options = {}) {
    const forceRefresh = !!options.forceRefresh;
    const cacheKey = getFirmwareClangdCacheKey();
    if (!forceRefresh && firmwareClangdCache && firmwareClangdCache.cacheKey === cacheKey) {
        return firmwareClangdCache.result;
    }

    const managed = resolveManagedClangdStatus();
    if (managed.available) {
        const result = {
            available: true,
            source: managed.source,
            path: managed.path,
            version: managed.version,
            managed: true,
            errors: [],
            managedStatus: managed.status,
        };
        firmwareClangdCache = { cacheKey, result };
        return result;
    }

    const disableLocal = process.env.MODULAR_FIRMWARE_DISABLE_LOCAL_CLANGD === '1';
    const candidates = [];
    const pushCandidate = (candidatePath, source) => {
        if (!candidatePath) return;
        if (candidates.some((entry) => entry.path === candidatePath)) return;
        candidates.push({ path: candidatePath, source });
    };
    if (!disableLocal) {
        pushCandidate(process.env.MODULAR_FIRMWARE_CLANGD_PATH, 'env');
        pushCandidate('clangd', 'path');
    }

    const errors = managed.error ? [{ path: managed.path, source: 'managed', error: managed.error }] : [];
    for (const candidate of candidates) {
        const probe = probeClangdExecutable(candidate.path, candidate.source);
        if (probe.available) {
            const result = {
                available: true,
                source: candidate.source,
                path: candidate.path,
                version: probe.version,
                managed: false,
                errors,
                managedStatus: managed.status,
            };
            firmwareClangdCache = { cacheKey, result };
            return result;
        }
        errors.push({
            path: candidate.path,
            source: candidate.source,
            error: probe.error,
        });
    }

    const result = {
        available: false,
        source: 'none',
        path: null,
        version: null,
        managed: false,
        managedStatus: managed.status,
        errors,
    };
    firmwareClangdCache = { cacheKey, result };
    return result;
}

function getFirmwarePlatformioProcessEnv(runtime = null) {
    const nextEnv = {
        ...process.env,
        PLATFORMIO_SETTING_ENABLE_TELEMETRY: 'no',
    };
    if (runtime?.managed && runtime.coreDir) {
        fs.mkdirSync(runtime.coreDir, { recursive: true });
        nextEnv.PLATFORMIO_CORE_DIR = runtime.coreDir;
        return nextEnv;
    }
    if (process.env.MODULAR_FIRMWARE_PLATFORMIO_CORE_DIR) {
        nextEnv.PLATFORMIO_CORE_DIR = path.resolve(process.env.MODULAR_FIRMWARE_PLATFORMIO_CORE_DIR);
        return nextEnv;
    }

    if (canWriteDirectory(DEFAULT_PLATFORMIO_HOME)) {
        return nextEnv;
    }

    const localCoreDir = path.join(app.getPath('userData'), 'platformio-home');
    fs.mkdirSync(localCoreDir, { recursive: true });
    nextEnv.PLATFORMIO_CORE_DIR = localCoreDir;

    const cachedPackagesDir = path.join(DEFAULT_PLATFORMIO_HOME, 'packages');
    if (fs.existsSync(cachedPackagesDir)) {
        nextEnv.PLATFORMIO_PACKAGES_DIR = cachedPackagesDir;
    }

    const cachedPlatformsDir = path.join(DEFAULT_PLATFORMIO_HOME, 'platforms');
    if (fs.existsSync(cachedPlatformsDir)) {
        nextEnv.PLATFORMIO_PLATFORMS_DIR = cachedPlatformsDir;
    }

    return nextEnv;
}

function resolveFirmwareProjectState() {
    const context = resolveFirmwareWorkspaceContext();
    if (!context.workspaceRoot) {
        return {
            context,
            config: null,
            envs: [],
            defaultEnv: null,
            selectedEnv: null,
            configError: context.validationError || 'No attached firmware workspace.',
        };
    }

    try {
        const config = readPlatformioProjectConfig(context.workspaceRoot);
        const selectedEnv = selectPlatformioEnv(config, context.persistedState.selectedEnv || null);
        return {
            context,
            config,
            envs: config.envs.slice(),
            defaultEnv: config.selectedEnv,
            selectedEnv,
            configError: null,
        };
    } catch (err) {
        return {
            context,
            config: null,
            envs: [],
            defaultEnv: null,
            selectedEnv: null,
            configError: err?.message || String(err),
        };
    }
}

function finalizeFirmwareBuild(jobPatch = {}) {
    if (!firmwareBuildJob) return null;
    firmwareBuildJob = {
        ...firmwareBuildJob,
        ...jobPatch,
        process: null,
    };
    const finalized = firmwareBuildJob;
    firmwareBuildJob = null;
    emitFirmwareBuildState();
    return finalized;
}

function cancelRunningFirmwareBuild(reason = 'canceled') {
    if (!firmwareBuildJob || !firmwareBuildJob.process) return false;
    firmwareBuildJob.cancelRequested = true;
    firmwareBuildJob.cancelReason = reason;
    try {
        firmwareBuildJob.process.kill('SIGTERM');
        return true;
    } catch (err) {
        emitFirmwareBuildOutput({
            jobId: firmwareBuildJob.id,
            stream: 'stderr',
            text: `[session-7] Failed to cancel job ${firmwareBuildJob.id}: ${err?.message || err}`,
        });
        return false;
    }
}

function emitFirmwareRuntimeOutput(text, stream = 'stdout') {
    emitFirmwareBuildOutput({
        jobId: firmwareToolchainJob?.id || 'firmware-toolchain',
        action: 'install-toolchain',
        env: null,
        stream,
        text,
    });
}

function runToolchainCommand(command, args, options = {}) {
    const {
        env = process.env,
        cwd = process.cwd(),
        label = command,
    } = options;

    return new Promise((resolve, reject) => {
        const child = spawn(command, args, {
            cwd,
            env,
            stdio: ['ignore', 'pipe', 'pipe'],
            windowsHide: true,
        });

        child.stdout?.on('data', (chunk) => {
            emitFirmwareRuntimeOutput(Buffer.isBuffer(chunk) ? chunk.toString('utf8') : String(chunk || ''), 'stdout');
        });
        child.stderr?.on('data', (chunk) => {
            emitFirmwareRuntimeOutput(Buffer.isBuffer(chunk) ? chunk.toString('utf8') : String(chunk || ''), 'stderr');
        });
        child.on('error', (err) => {
            reject(new Error(`${label} failed to start: ${err?.message || err}`));
        });
        child.on('close', (code, signal) => {
            if (code === 0) {
                resolve();
                return;
            }
            reject(new Error(`${label} failed with exit ${code}${signal ? ` via ${signal}` : ''}`));
        });
    });
}

async function installManagedPlatformioRuntime() {
    const userDataDir = app.getPath('userData');
    const managedRoot = getManagedPlatformioRoot(userDataDir);
    const managedVenvDir = path.join(managedRoot, 'penv');
    const managedPythonPath = getManagedPlatformioPython(userDataDir);
    const managedPioPath = getManagedPlatformioExecutable(userDataDir);
    const managedCoreDir = getManagedPlatformioCoreDir(userDataDir);
    const seedPath = process.env.MODULAR_FIRMWARE_MANAGED_PIO_SEED_PATH;

    fs.mkdirSync(managedRoot, { recursive: true });
    fs.mkdirSync(managedCoreDir, { recursive: true });

    if (seedPath) {
        const sourcePath = path.resolve(seedPath);
        if (!fs.existsSync(sourcePath) || !fs.statSync(sourcePath).isFile()) {
            throw new Error(`Managed PlatformIO seed path does not exist: ${sourcePath}`);
        }
        fs.rmSync(managedVenvDir, { recursive: true, force: true });
        fs.mkdirSync(path.dirname(managedPioPath), { recursive: true });
        fs.copyFileSync(sourcePath, managedPioPath);
        fs.chmodSync(managedPioPath, 0o755);
        const probe = probePlatformioExecutable(managedPioPath, 'managed', {
            PLATFORMIO_CORE_DIR: managedCoreDir,
        });
        if (!probe.available) {
            throw new Error(probe.error || 'Seeded managed PlatformIO runtime failed verification.');
        }
        return {
            path: managedPioPath,
            version: probe.version,
            coreDir: managedCoreDir,
        };
    }

    const pythonPath = process.env.MODULAR_FIRMWARE_PYTHON_PATH || 'python3';
    emitFirmwareRuntimeOutput(`[session-7] Creating managed PlatformIO runtime in ${managedRoot}\n`);
    await runToolchainCommand(pythonPath, ['-m', 'venv', managedVenvDir], {
        cwd: managedRoot,
        label: 'python -m venv',
    });
    await runToolchainCommand(managedPythonPath, ['-m', 'pip', 'install', '--upgrade', 'pip'], {
        cwd: managedRoot,
        label: 'pip upgrade',
    });
    await runToolchainCommand(managedPythonPath, ['-m', 'pip', 'install', '--upgrade', 'platformio'], {
        cwd: managedRoot,
        label: 'pip install platformio',
    });

    const probe = probePlatformioExecutable(managedPioPath, 'managed', {
        PLATFORMIO_CORE_DIR: managedCoreDir,
    });
    if (!probe.available) {
        throw new Error(probe.error || 'Managed PlatformIO runtime failed verification.');
    }

    return {
        path: managedPioPath,
        version: probe.version,
        coreDir: managedCoreDir,
    };
}

async function installManagedClangdRuntime() {
    const userDataDir = app.getPath('userData');
    const managedRoot = getManagedClangdRoot(userDataDir);
    const managedClangdPath = getManagedClangdExecutable(userDataDir);
    const seedPath = process.env.MODULAR_FIRMWARE_MANAGED_CLANGD_SEED_PATH;

    fs.mkdirSync(path.dirname(managedClangdPath), { recursive: true });

    let sourcePath = null;
    if (seedPath) {
        sourcePath = path.resolve(seedPath);
    } else {
        const local = resolveFirmwareClangdStatus({ forceRefresh: true });
        if (local.available && !local.managed && local.path) {
            sourcePath = local.path;
        }
    }

    if (!sourcePath) {
        throw new Error('No clangd seed is available. Set MODULAR_FIRMWARE_MANAGED_CLANGD_SEED_PATH or install clangd locally first.');
    }
    if (!fs.existsSync(sourcePath) || !fs.statSync(sourcePath).isFile()) {
        throw new Error(`Managed clangd seed path does not exist: ${sourcePath}`);
    }

    emitFirmwareRuntimeOutput(`[session-7] Installing managed clangd in ${managedRoot}\n`);
    fs.copyFileSync(sourcePath, managedClangdPath);
    fs.chmodSync(managedClangdPath, 0o755);

    const probe = probeClangdExecutable(managedClangdPath, 'managed');
    if (!probe.available) {
        throw new Error(probe.error || 'Managed clangd runtime failed verification.');
    }

    return {
        path: managedClangdPath,
        version: probe.version,
    };
}

function disposeFirmwareLanguageClient(options = {}) {
    const { clearDiagnostics = true } = options;
    if (firmwareLanguageClient) {
        try {
            firmwareLanguageClient.dispose();
        } catch {}
    }
    firmwareLanguageClient = null;
    firmwareLanguageClientKey = null;
    if (clearDiagnostics) {
        emitFirmwareLanguageDiagnostics({
            workspaceRoot: resolveFirmwareWorkspaceContext().workspaceRoot || null,
            diagnostics: [],
        });
    }
}

function getFirmwareLanguageContext() {
    const projectState = resolveFirmwareProjectState();
    const clangd = resolveFirmwareClangdStatus();
    const activeEnv = projectState.selectedEnv;
    let compileCommands = null;
    if (projectState.context.workspaceRoot && activeEnv) {
        compileCommands = resolveCompileCommandsState(projectState.context.workspaceRoot, activeEnv);
    }

    let status = 'idle';
    let message = 'clangd is ready.';
    if (!projectState.context.workspaceRoot) {
        status = 'missing-workspace';
        message = 'Attach a firmware workspace to enable completion and hover.';
    } else if (projectState.configError) {
        status = 'config-error';
        message = projectState.configError;
    } else if (!activeEnv) {
        status = 'missing-env';
        message = 'Select a PlatformIO environment before starting clangd.';
    } else if (firmwareToolchainJob) {
        status = 'installing';
        message = 'Installing the managed toolchains.';
    } else if (!clangd.available) {
        status = 'missing-clangd';
        message = clangd.errors[0]?.error || 'clangd is not available. Install the managed toolchain.';
    } else if (!compileCommands?.exists) {
        status = 'missing-compiledb';
        message = `Run Reindex to generate ${getCompileCommandsPath(projectState.context.workspaceRoot, activeEnv)}.`;
    } else {
        status = 'ready';
        message = `clangd ready for ${activeEnv}`;
    }

    return {
        projectState,
        clangd,
        activeEnv,
        compileCommands,
        status,
        message,
    };
}

function getFirmwareLanguageState() {
    const context = getFirmwareLanguageContext();
    return {
        session: 7,
        status: context.status,
        message: context.message,
        activeEnv: context.activeEnv,
        workspaceAttached: !!context.projectState.context.workspaceRoot,
        workspaceRoot: context.projectState.context.workspaceRoot,
        compileCommandsPath: context.compileCommands?.path || null,
        compileCommandsReady: !!context.compileCommands?.exists,
        clientRunning: !!firmwareLanguageClient,
        clangd: {
            available: context.clangd.available,
            source: context.clangd.source,
            path: context.clangd.path,
            version: context.clangd.version,
            usingManagedRuntime: !!context.clangd.managed,
            managedStatus: context.clangd.managedStatus,
            error: context.clangd.available ? null : (context.clangd.errors[0]?.error || 'clangd is unavailable'),
        },
    };
}

async function ensureFirmwareLanguageClient() {
    const context = getFirmwareLanguageContext();
    if (context.status !== 'ready') {
        disposeFirmwareLanguageClient();
        return { ok: false, state: getFirmwareLanguageState(), context };
    }

    const clientKey = JSON.stringify({
        clangdPath: context.clangd.path,
        workspaceRoot: context.projectState.context.workspaceRoot,
        activeEnv: context.activeEnv,
        compileCommandsPath: context.compileCommands?.path || null,
    });
    if (firmwareLanguageClient && firmwareLanguageClientKey === clientKey) {
        return { ok: true, client: firmwareLanguageClient, state: getFirmwareLanguageState(), context };
    }

    disposeFirmwareLanguageClient({ clearDiagnostics: false });

    const workspaceRoot = context.projectState.context.workspaceRoot;
    const compileCommandsDir = context.compileCommands?.directory || path.dirname(context.compileCommands?.path || workspaceRoot);
    const client = new ClangdClient({
        command: context.clangd.path,
        args: [
            `--compile-commands-dir=${compileCommandsDir}`,
            '--clang-tidy=false',
            '--header-insertion=never',
        ],
        cwd: workspaceRoot,
        env: process.env,
        rootUri: toDocumentUri(workspaceRoot),
        workspaceName: path.basename(workspaceRoot),
        onDiagnostics: (payload = {}) => {
            const diagnostics = Array.isArray(payload.diagnostics) ? payload.diagnostics : [];
            let relativePath = null;
            if (payload.uri && payload.uri.startsWith('file://')) {
                try {
                    relativePath = path.relative(workspaceRoot, new URL(payload.uri).pathname);
                } catch {}
            }
            emitFirmwareLanguageDiagnostics({
                session: 7,
                uri: payload.uri,
                relativePath,
                version: payload.version,
                diagnostics,
            });
        },
        onOutput: (text, stream) => {
            emitFirmwareBuildOutput({
                jobId: 'firmware-clangd',
                action: 'clangd',
                env: context.activeEnv,
                stream,
                text,
            });
        },
        onExit: () => {
            firmwareLanguageClient = null;
            firmwareLanguageClientKey = null;
            emitFirmwareLanguageState();
        },
    });

    try {
        await client.start();
        firmwareLanguageClient = client;
        firmwareLanguageClientKey = clientKey;
        emitFirmwareLanguageState();
        return { ok: true, client, state: getFirmwareLanguageState(), context };
    } catch (err) {
        disposeFirmwareLanguageClient();
        return {
            ok: false,
            error: err?.message || String(err),
            state: getFirmwareLanguageState(),
            context,
        };
    }
}

async function syncFirmwareLanguageDocument(relativePath, content) {
    const context = resolveFirmwareWorkspaceContext();
    if (!context.workspaceRoot) {
        return { ok: false, error: 'No attached firmware workspace.', state: getFirmwareLanguageState() };
    }

    const clientState = await ensureFirmwareLanguageClient();
    if (!clientState.ok) {
        return clientState;
    }

    const resolved = resolveWorkspacePath(context.workspaceRoot, relativePath);
    await clientState.client.ensureDocument({
        filePath: resolved.absolutePath,
        text: content,
        languageId: 'cpp',
    });
    return {
        ok: true,
        state: getFirmwareLanguageState(),
    };
}

function getFirmwareWorkspaceState() {
    const context = resolveFirmwareWorkspaceContext();
    const fileEntries = listFirmwareWorkspaceEntries(context);
    const summary = context.workspaceRoot
        ? `Attached workspace: ${path.basename(context.workspaceRoot)}`
        : 'Attach an existing Core checkout to start editing in Monaco.';
    const placeholderMessage = context.workspaceRoot
        ? 'Session 7 adds managed clangd-backed completion and hover on top of the Monaco workspace shell and local build flow.'
        : 'Attach an existing firmware workspace to enable Monaco-backed editing.';

    return {
        session: 7,
        extensionId: 'owntech-workspace',
        enabled: isFirmwareWorkspaceEnabled(),
        windowOpen: !!(firmwareWindow && !firmwareWindow.isDestroyed()),
        summary,
        placeholderMessage,
        workspace: {
            mode: context.workspaceRoot ? 'attached' : 'detached',
            root: context.workspaceRoot,
            requestedRoot: context.invalidWorkspaceRoot,
            validationError: context.validationError,
            focusedFiles: FIRMWARE_FOCUSED_FILES.slice(),
            advancedMode: !!context.persistedState.advancedMode,
            activeFile: context.activeFile,
            fileCount: fileEntries.length,
        },
    };
}

function getFirmwareToolchainStatus() {
    const managedPlatformio = resolveManagedPlatformioStatus();
    const platformio = resolveFirmwarePlatformioStatus();
    const managedClangd = resolveManagedClangdStatus();
    const clangd = resolveFirmwareClangdStatus();
    const status = firmwareToolchainJob
        ? 'installing'
        : (
            managedPlatformio.available && managedClangd.available
                ? 'managed-ready'
                : ((platformio.available || clangd.available) ? 'partially-ready' : 'missing')
        );
    return {
        session: 7,
        managed: !!(managedPlatformio.available || managedClangd.available || firmwareToolchainJob),
        status,
        platformio: {
            status: firmwareToolchainJob
                ? 'installing'
                : (managedPlatformio.available ? 'installed' : (platformio.available ? 'available' : 'missing')),
            source: platformio.source,
            path: platformio.path,
            version: platformio.version,
            error: firmwareToolchainJob ? null : (platformio.available ? null : (managedPlatformio.error || platformio.errors[0]?.error || 'PlatformIO CLI not found')),
            managedPath: getManagedPlatformioExecutable(app.getPath('userData')),
            managedCoreDir: getManagedPlatformioCoreDir(app.getPath('userData')),
            managedStatus: managedPlatformio.status,
            managedInstalledAt: managedPlatformio.installedAt || null,
            installButtonEnabled: !firmwareToolchainJob && (!managedPlatformio.available || !managedClangd.available),
            usingManagedRuntime: !!platformio.managed,
        },
        clangd: {
            status: firmwareToolchainJob
                ? 'installing'
                : (managedClangd.available ? 'installed' : (clangd.available ? 'available' : 'missing')),
            source: clangd.source,
            path: clangd.path,
            version: clangd.version,
            error: firmwareToolchainJob ? null : (clangd.available ? null : (managedClangd.error || clangd.errors[0]?.error || 'clangd not found')),
            managedPath: getManagedClangdExecutable(app.getPath('userData')),
            managedStatus: managedClangd.status,
            managedInstalledAt: managedClangd.installedAt || null,
            usingManagedRuntime: !!clangd.managed,
        },
    };
}

function getFirmwareBuildState() {
    const projectState = resolveFirmwareProjectState();
    const managedPlatformio = resolveManagedPlatformioStatus();
    const managedClangd = resolveManagedClangdStatus();
    const platformio = resolveFirmwarePlatformioStatus();
    const activeJob = firmwareBuildJob;
    const supported = !!(projectState.context.workspaceRoot && projectState.envs.length && platformio.available);
    const status = activeJob
        ? (activeJob.cancelRequested ? 'canceling' : 'running')
        : (supported ? 'idle' : 'blocked');
    let placeholderMessage = '';
    if (!projectState.context.workspaceRoot) {
        placeholderMessage = 'Attach a firmware workspace to enable PlatformIO actions.';
    } else if (projectState.configError) {
        placeholderMessage = projectState.configError;
    } else if (!projectState.envs.length) {
        placeholderMessage = 'No [env:*] sections were found in platformio.ini.';
    } else if (firmwareToolchainJob) {
        placeholderMessage = 'Installing the managed PlatformIO runtime.';
    } else if (!platformio.available) {
        placeholderMessage = platformio.errors[0]?.error || 'No working PlatformIO runtime was detected. Install the managed toolchain or configure a local CLI.';
    } else {
        placeholderMessage = 'Ready to run PlatformIO build actions.';
    }

    return {
        session: 7,
        status,
        supported,
        selectedEnv: projectState.selectedEnv,
        defaultEnv: projectState.defaultEnv,
        envs: projectState.envs,
        workspaceAttached: !!projectState.context.workspaceRoot,
        activeJob: activeJob ? {
            id: activeJob.id,
            action: activeJob.action,
            env: activeJob.env,
            startedAt: activeJob.startedAt,
            cancelRequested: !!activeJob.cancelRequested,
        } : null,
        platformio: {
            available: platformio.available,
            path: platformio.path,
            source: platformio.source,
            version: platformio.version,
        },
        actions: {
            installToolchain: !firmwareToolchainJob && (!managedPlatformio.available || !managedClangd.available),
            build: supported && !activeJob,
            upload: supported && !activeJob,
            clean: supported && !activeJob,
            reindex: supported && !activeJob,
            cancel: !!activeJob,
        },
        placeholderMessage,
    };
}

function firmwareStubResponse(action) {
    return {
        ok: false,
        session: 7,
        error: `${action} is not implemented in Session 7.`,
    };
}

function openFirmwareWorkspaceWindow() {
    if (!isFirmwareWorkspaceEnabled()) {
        return null;
    }
    if (firmwareWindow && !firmwareWindow.isDestroyed()) {
        if (firmwareWindow.isMinimized()) firmwareWindow.restore();
        firmwareWindow.focus();
        return firmwareWindow;
    }

    firmwareWindow = new BrowserWindow({
        width: 1280,
        height: 860,
        minWidth: 920,
        minHeight: 640,
        title: 'Firmware Workspace',
        icon: path.join(__dirname, 'assets', 'icon.png'),
        backgroundColor: '#0c1320',
        webPreferences: {
            preload: path.join(__dirname, 'preload.js'),
            sandbox: false,
            nodeIntegration: false,
            contextIsolation: true,
        }
    });

    if (!app.isPackaged) {
        firmwareWindow.webContents.on('did-fail-load', (_event, code, desc, url) => {
            console.error('[firmware] did-fail-load', code, desc, url);
        });
    }

    firmwareWindow.loadFile(path.join(__dirname, 'firmware', 'index.html'));
    firmwareWindow.on('closed', () => {
        cancelRunningFirmwareBuild('window-closed');
        disposeFirmwareLanguageClient();
        firmwareWindow = null;
    });

    return firmwareWindow;
}

const dashboardsDir = path.join(app.getPath('userData'), 'dashboards');
fs.mkdirSync(dashboardsDir, { recursive: true });
const machinesDir = path.join(app.getPath('userData'), 'machines');
fs.mkdirSync(machinesDir, { recursive: true });
const headersDir = path.join(__dirname, 'headers');
fs.mkdirSync(headersDir, { recursive: true });
const acquireDir = path.join(__dirname, 'acquire');
fs.mkdirSync(acquireDir, { recursive: true });

// Menu-driven file open uses main-process dialog to satisfy user activation requirements.
ipcMain.handle('show-open-dashboard', async () => {
    if (!mainWindow) return null;
    const { canceled, filePaths } = await dialog.showOpenDialog(mainWindow, {
        defaultPath: path.join(dashboardsDir, 'dashboard.json'),
        properties: ['openFile'],
        filters: [{ name: 'Dashboard', extensions: ['json'] }]
    });
    if (canceled || !filePaths || filePaths.length === 0) return null;
    return filePaths[0];
});

ipcMain.handle('headers-save', async (_event, { labels } = {}) => {
    if (!mainWindow) return { saved: false };
    const { canceled, filePath } = await dialog.showSaveDialog(mainWindow, {
        title: 'Save Channel Headers',
        defaultPath: path.join(headersDir, 'headers.json'),
        filters: [{ name: 'JSON', extensions: ['json'] }]
    });
    if (canceled || !filePath) return { saved: false };
    fs.writeFileSync(filePath, JSON.stringify(labels, null, 2), 'utf8');
    return { saved: true };
});

ipcMain.handle('headers-load', async (_event) => {
    if (!mainWindow) return { loaded: false };
    const { canceled, filePaths } = await dialog.showOpenDialog(mainWindow, {
        title: 'Load Channel Headers',
        defaultPath: headersDir,
        filters: [{ name: 'JSON', extensions: ['json'] }],
        properties: ['openFile']
    });
    if (canceled || !filePaths || !filePaths.length) return { loaded: false };
    const content = fs.readFileSync(filePaths[0], 'utf8');
    return { loaded: true, labels: JSON.parse(content) };
});

ipcMain.handle('show-save-dashboard', async (_event, { content } = {}) => {
    if (!mainWindow) return false;
    const { canceled, filePath } = await dialog.showSaveDialog(mainWindow, {
        defaultPath: path.join(dashboardsDir, 'dashboard.json'),
        filters: [{ name: 'Dashboard', extensions: ['json'] }]
    });
    if (canceled || !filePath) return false;
    await fs.promises.writeFile(filePath, content, 'utf8');
    return true;
});

ipcMain.handle('show-save-machine', async (_event, { content } = {}) => {
    if (!mainWindow) return false;
    const { canceled, filePath } = await dialog.showSaveDialog(mainWindow, {
        defaultPath: path.join(machinesDir, 'machine.json'),
        filters: [{ name: 'State Machine', extensions: ['json'] }]
    });
    if (canceled || !filePath) return false;
    await fs.promises.writeFile(filePath, content, 'utf8');
    return true;
});

ipcMain.handle('show-open-machine', async () => {
    if (!mainWindow) return null;
    const { canceled, filePaths } = await dialog.showOpenDialog(mainWindow, {
        defaultPath: machinesDir,
        properties: ['openFile'],
        filters: [{ name: 'State Machine', extensions: ['json'] }]
    });
    if (canceled || !filePaths || filePaths.length === 0) return null;
    return fs.promises.readFile(filePaths[0], 'utf8');
});

ipcMain.handle('choose-csv-file', async () => {
    if (!mainWindow) return null;
    const { canceled, filePaths } = await dialog.showOpenDialog(mainWindow, {
        defaultPath: process.cwd(),
        properties: ['openFile'],
        filters: [{ name: 'CSV', extensions: ['csv'] }]
    });
    if (canceled || !filePaths || filePaths.length === 0) return null;
    return filePaths[0];
});

// Bridge renderer logs to the terminal for debugging.
ipcMain.on('renderer-log', (_event, { level = 'log', args = [] } = {}) => {
    const prefix = '[renderer]';
    const payload = Array.isArray(args) ? args : [args];
    if (level === 'error') {
        console.error(prefix, ...payload);
    } else if (level === 'warn') {
        console.warn(prefix, ...payload);
    } else {
        console.log(prefix, ...payload);
    }
});

ipcMain.on('set-theme', (_event, theme) => {
    nativeTheme.themeSource = theme === 'light' ? 'light' : 'dark';
});

// App menu is custom: Edit only hosts "Widget Categories" and View/Window are removed.
// ── Documentation menu helpers ────────────────────────────────────────────────

function collectReadmes(baseDir) {
    const readmes = [];
    if (!fs.existsSync(baseDir)) return readmes;
    const walk = (dir) => {
        const entries = fs.readdirSync(dir, { withFileTypes: true });
        for (const entry of entries) {
            const full = path.join(dir, entry.name);
            if (entry.isDirectory()) {
                walk(full);
            } else if (entry.isFile() && entry.name.toLowerCase() === 'readme.md') {
                readmes.push(full);
            }
        }
    };
    walk(baseDir);
    return readmes;
}

function collectReadmesFromRoots(rootEntries) {
    const readmes = [];
    for (const rootEntry of rootEntries || []) {
        if (!rootEntry || !rootEntry.path) continue;
        for (const docPath of collectReadmes(rootEntry.path)) {
            readmes.push({ root: rootEntry, docPath });
        }
    }
    return readmes;
}

function buildExamplesForExtension(extensionId) {
    try {
        const roots = (extensionRuntime.bootstrap.exampleRoots || []).filter(
            (r) => r.extensionId === extensionId
        );
        const readmes = collectReadmesFromRoots(roots);
        if (!readmes.length) return [];

        const root = { children: new Map(), exampleId: null };
        for (const entry of readmes) {
            const relDir = path.relative(entry.root.path, path.dirname(entry.docPath));
            const parts = relDir.split(path.sep).filter(Boolean);
            if (!parts.length) continue;
            let node = root;
            for (const part of parts) {
                if (!node.children.has(part)) node.children.set(part, { children: new Map(), exampleId: null });
                node = node.children.get(part);
            }
            node.exampleId = parts.join('/');
        }

        const buildMenuFromNode = (node) => {
            const items = [];
            const keys = Array.from(node.children.keys()).sort((a, b) => a.localeCompare(b));
            for (const key of keys) {
                const child = node.children.get(key);
                if (child.children.size > 0) {
                    items.push({ label: key, submenu: buildMenuFromNode(child) });
                } else if (child.exampleId) {
                    items.push({ label: key, click: () => openExampleTab(child.exampleId) });
                }
            }
            return items;
        };

        return buildMenuFromNode(root);
    } catch (err) {
        console.warn(`Failed to build Examples menu for ${extensionId}:`, err?.message || err);
        return [];
    }
}

function buildWidgetDocsForExtension(extensionId) {
    try {
        const entries = (extensionRuntime.bootstrap.widgetDocs || []).filter((entry) => {
            if (!entry || !entry.type || !entry.title) return false;
            if (entry.compatibilityOnly) return false;
            return entry.extensionId === extensionId;
        });
        if (!entries.length) return [];

        const grouped = new Map();
        for (const entry of entries) {
            const category = entry.category || 'Other';
            if (!grouped.has(category)) grouped.set(category, []);
            grouped.get(category).push(entry);
        }

        const categories = Array.from(grouped.keys()).sort((a, b) => a.localeCompare(b));
        return categories.map((category) => {
            const widgets = grouped.get(category).slice().sort((a, b) => a.title.localeCompare(b.title));
            return {
                label: category,
                submenu: widgets.map((widget) => ({
                    label: widget.title,
                    click: () => openWidgetDocTab(widget.type)
                }))
            };
        });
    } catch (err) {
        console.warn(`Failed to build Widgets menu for ${extensionId}:`, err?.message || err);
        return [];
    }
}

function isExtensionEnabled(extensionId) {
    return extensionRuntime.inventory.some((entry) => entry.id === extensionId && entry.enabled);
}

function buildWidgetExtensionsMenuItems() {
    const widgetSections = [
        { extensionId: 'core', label: 'Modular Core Widgets' },
        { extensionId: 'owntech', label: 'OwnTech Widgets' },
        { extensionId: 'thingset', label: 'Thingset Widgets' },
    ];
    const items = [];
    widgetSections.forEach(({ extensionId, label }) => {
        if (!isExtensionEnabled(extensionId)) return;
        const submenu = buildWidgetDocsForExtension(extensionId);
        if (!submenu.length) return;
        items.push({ label, submenu });
    });
    return items.length
        ? items
        : [{ label: 'No widget documentation found', enabled: false }];
}

function buildExamplesMenuItems(extensionId) {
    const items = buildExamplesForExtension(extensionId);
    return items.length
        ? items
        : [{ label: 'No examples found', enabled: false }];
}

function getExtensionDisplayName(extensionId) {
    const entry = extensionRuntime.inventory.find((item) => item.id === extensionId);
    return entry ? entry.displayName : extensionId;
}

function buildCoursewareTree(entries) {
    const root = { groups: new Map(), labs: [] };
    for (const entry of entries) {
        const segments = Array.isArray(entry.menuSegments) ? entry.menuSegments.filter(Boolean) : [];
        const parents = segments.length > 1 ? segments.slice(0, -1) : [];
        let node = root;
        for (const segment of parents) {
            if (!node.groups.has(segment)) node.groups.set(segment, { groups: new Map(), labs: [] });
            node = node.groups.get(segment);
        }
        node.labs.push(entry);
    }

    const toMenu = (node) => {
        const items = [];
        const groupLabels = Array.from(node.groups.keys()).sort((a, b) => a.localeCompare(b));
        for (const label of groupLabels) {
            items.push({
                label,
                submenu: toMenu(node.groups.get(label)),
            });
        }
        node.labs
            .slice()
            .sort((left, right) => {
                if (left.order !== right.order) return left.order - right.order;
                return left.title.localeCompare(right.title);
            })
            .forEach((entry) => {
                items.push({
                    label: entry.title,
                    click: () => openCoursewareTab(entry.id),
                });
            });
        return items;
    };

    return toMenu(root);
}

function buildCoursewareMenuItems() {
    try {
        const entries = Array.isArray(extensionRuntime.bootstrap.courseware)
            ? extensionRuntime.bootstrap.courseware.slice()
            : [];
        if (!entries.length) return [{ label: 'No courseware found', enabled: false }];

        const grouped = new Map();
        for (const entry of entries) {
            if (!entry || !entry.id || !entry.extensionId) continue;
            if (!grouped.has(entry.extensionId)) grouped.set(entry.extensionId, []);
            grouped.get(entry.extensionId).push(entry);
        }

        const extensionIds = Array.from(grouped.keys());
        if (extensionIds.length === 1) {
            return buildCoursewareTree(grouped.get(extensionIds[0]));
        }

        const sections = [];
        for (const extensionId of extensionIds) {
            if (sections.length) sections.push({ type: 'separator' });
            sections.push({ label: getExtensionDisplayName(extensionId), enabled: false });
            sections.push(...buildCoursewareTree(grouped.get(extensionId)));
        }
        return sections.length ? sections : [{ label: 'No courseware found', enabled: false }];
    } catch (err) {
        console.warn(`Failed to build Courseware menu:`, err?.message || err);
        return [{ label: 'No courseware found', enabled: false }];
    }
}

function buildTutorialTree(entries) {
    const root = { groups: new Map(), tutorials: [] };
    for (const entry of entries) {
        const segments = Array.isArray(entry.menuSegments) ? entry.menuSegments.filter(Boolean) : [];
        const parents = segments.length > 1 ? segments.slice(0, -1) : [];
        let node = root;
        for (const segment of parents) {
            if (!node.groups.has(segment)) node.groups.set(segment, { groups: new Map(), tutorials: [] });
            node = node.groups.get(segment);
        }
        node.tutorials.push(entry);
    }

    const toMenu = (node) => {
        const items = [];
        const groupLabels = Array.from(node.groups.keys()).sort((a, b) => a.localeCompare(b));
        for (const label of groupLabels) {
            items.push({
                label,
                submenu: toMenu(node.groups.get(label)),
            });
        }
        node.tutorials
            .slice()
            .sort((left, right) => {
                if (left.order !== right.order) return left.order - right.order;
                return left.title.localeCompare(right.title);
            })
            .forEach((entry) => {
                items.push({
                    label: entry.title,
                    click: () => openTutorial(entry.id),
                });
            });
        return items;
    };

    return toMenu(root);
}

function buildTutorialsMenuItems() {
    try {
        const entries = Array.isArray(extensionRuntime.bootstrap.tutorials)
            ? extensionRuntime.bootstrap.tutorials.slice()
            : [];
        if (!entries.length) return [{ label: 'No tutorials found', enabled: false }];

        const grouped = new Map();
        for (const entry of entries) {
            if (!entry || !entry.id || !entry.extensionId) continue;
            if (!grouped.has(entry.extensionId)) grouped.set(entry.extensionId, []);
            grouped.get(entry.extensionId).push(entry);
        }

        const extensionIds = Array.from(grouped.keys());
        if (extensionIds.length === 1) {
            return buildTutorialTree(grouped.get(extensionIds[0]));
        }

        const sections = [];
        for (const extensionId of extensionIds) {
            if (sections.length) sections.push({ type: 'separator' });
            sections.push({ label: getExtensionDisplayName(extensionId), enabled: false });
            sections.push(...buildTutorialTree(grouped.get(extensionId)));
        }
        return sections.length ? sections : [{ label: 'No tutorials found', enabled: false }];
    } catch (err) {
        console.warn(`Failed to build Tutorials menu:`, err?.message || err);
        return [{ label: 'No tutorials found', enabled: false }];
    }
}

// Renderer-facing docs helpers (used by tabs / example viewer).
ipcMain.handle('docs-list-readmes', async (_event, { baseDir } = {}) => {
    if (!baseDir) return [];
    try {
        return collectReadmes(baseDir);
    } catch (err) {
        console.warn('docs-list-readmes failed:', err?.message || err);
        return [];
    }
});

ipcMain.handle('docs-read-markdown', async (_event, { docPath } = {}) => {
    if (!docPath) return '';
    return fs.promises.readFile(docPath, 'utf8');
});

ipcMain.handle('files-read-text', async (_event, { filePath } = {}) => {
    if (!filePath) return '';
    return fs.promises.readFile(filePath, 'utf8');
});

ipcMain.handle('files-list-dir', async (_event, { dirPath } = {}) => {
    if (!dirPath) return [];
    try {
        return await fs.promises.readdir(dirPath);
    } catch (err) {
        console.warn('files-list-dir failed:', err?.message || err);
        return [];
    }
});

ipcMain.handle('files-write-text', async (_event, { filePath, content } = {}) => {
    if (!filePath) return { ok: false, error: 'Missing filePath' };
    try {
        await fs.promises.writeFile(filePath, content ?? '', 'utf8');
        return { ok: true };
    } catch (err) {
        console.warn('files-write-text failed:', err?.message || err);
        return { ok: false, error: err?.message || String(err) };
    }
});

ipcMain.handle('open-external-url', async (_event, { url } = {}) => {
    if (!url || !/^https?:\/\//i.test(String(url))) {
        return { ok: false, error: 'Invalid external URL' };
    }
    try {
        await shell.openExternal(String(url));
        return { ok: true };
    } catch (err) {
        return { ok: false, error: err?.message || String(err) };
    }
});

// IPC for widget documentation tabs.
function openWidgetDocTab(type) {
    if (!type) return;
    if (mainWindow && mainWindow.webContents) {
        mainWindow.webContents.send('open-widget-doc-tab', { type });
    } else {
        pendingWidgetDocType = type;
    }
}

ipcMain.on('open-widget-doc-tab', (_event, { type } = {}) => {
    openWidgetDocTab(type);
});

ipcMain.handle('get-pending-widget-doc', () => pendingWidgetDocType);

ipcMain.on('widget-docs-ready', () => {
    if (!pendingWidgetDocType) return;
    const pending = pendingWidgetDocType;
    pendingWidgetDocType = null;
    openWidgetDocTab(pending);
});

ipcMain.handle('extensions-list', () => cloneExtensionInventory());

ipcMain.handle('extensions-is-enabled', (_event, { id } = {}) => {
    if (!id) return false;
    return extensionRuntime.isEnabled(String(id));
});

ipcMain.handle('extensions-get-bootstrap', () => cloneExtensionBootstrap());
ipcMain.handle('firmware-workspace-open-window', () => {
    const win = openFirmwareWorkspaceWindow();
    if (!win) {
        return {
            ok: false,
            windowOpen: false,
            error: 'OwnTech Firmware Workspace is disabled.',
            state: getFirmwareWorkspaceState(),
        };
    }
    return {
        ok: !!win,
        windowOpen: !!win,
        state: getFirmwareWorkspaceState(),
    };
});
ipcMain.handle('firmware-workspace-get-state', () => getFirmwareWorkspaceState());
ipcMain.handle('firmware-workspace-use-managed', () => firmwareStubResponse('useManagedWorkspace'));
ipcMain.handle('firmware-workspace-attach-existing', async (_event, { workspacePath } = {}) => {
    let selectedPath = typeof workspacePath === 'string' && workspacePath.trim() ? workspacePath.trim() : '';
    if (!selectedPath) {
        const ownerWindow = (firmwareWindow && !firmwareWindow.isDestroyed()) ? firmwareWindow : mainWindow;
        const { canceled, filePaths } = await dialog.showOpenDialog(ownerWindow, {
            title: 'Attach Existing Firmware Workspace',
            defaultPath: process.cwd(),
            properties: ['openDirectory'],
        });
        if (canceled || !filePaths || filePaths.length === 0) {
            return { ok: false, canceled: true, state: getFirmwareWorkspaceState() };
        }
        [selectedPath] = filePaths;
    }

    try {
        const workspaceRoot = validateFirmwareWorkspaceRoot(selectedPath);
        const config = readPlatformioProjectConfig(workspaceRoot);
        const activeFile = pickDefaultActiveFile(workspaceRoot);
        const selectedEnv = selectPlatformioEnv(config, null);
        writeFirmwareSessionState({
            workspaceRoot,
            advancedMode: false,
            activeFile,
            selectedEnv,
        });
        const state = getFirmwareWorkspaceState();
        disposeFirmwareLanguageClient();
        emitFirmwareWorkspaceState(state);
        emitFirmwareBuildState();
        emitFirmwareToolchainStatus();
        emitFirmwareLanguageState();
        return { ok: true, state };
    } catch (err) {
        return {
            ok: false,
            error: err?.message || String(err),
            state: getFirmwareWorkspaceState(),
        };
    }
});
ipcMain.handle('firmware-workspace-list-files', () => {
    const context = resolveFirmwareWorkspaceContext();
    return {
        ok: true,
        session: 7,
        mode: context.persistedState.advancedMode ? 'advanced' : 'focused',
        files: listFirmwareWorkspaceEntries(context),
    };
});
ipcMain.handle('firmware-workspace-read-file', (_event, { relativePath } = {}) => {
    const context = resolveFirmwareWorkspaceContext();
    if (!context.workspaceRoot) {
        return { ok: false, error: context.validationError || 'No attached firmware workspace.' };
    }

    try {
        const targetPath = relativePath || context.activeFile || pickDefaultActiveFile(context.workspaceRoot);
        if (!targetPath) {
            return { ok: false, error: 'No readable file is available in the attached workspace.' };
        }
        const file = readWorkspaceTextFile(context.workspaceRoot, targetPath);
        writeFirmwareSessionState({ activeFile: file.relativePath });
        const state = getFirmwareWorkspaceState();
        emitFirmwareWorkspaceState(state);
        return {
            ok: true,
            session: 7,
            relativePath: file.relativePath,
            content: file.content,
            state,
        };
    } catch (err) {
        return { ok: false, error: err?.message || String(err) };
    }
});
ipcMain.handle('firmware-workspace-write-file', (_event, { relativePath, content } = {}) => {
    const context = resolveFirmwareWorkspaceContext();
    if (!context.workspaceRoot) {
        return { ok: false, error: context.validationError || 'No attached firmware workspace.' };
    }

    try {
        const targetPath = relativePath || context.activeFile;
        if (!targetPath) {
            return { ok: false, error: 'No active file selected.' };
        }
        const file = writeWorkspaceTextFile(context.workspaceRoot, targetPath, content ?? '');
        writeFirmwareSessionState({ activeFile: file.relativePath });
        const state = getFirmwareWorkspaceState();
        emitFirmwareWorkspaceState(state);
        return {
            ok: true,
            session: 7,
            relativePath: file.relativePath,
            state,
        };
    } catch (err) {
        return { ok: false, error: err?.message || String(err) };
    }
});
ipcMain.handle('firmware-workspace-set-advanced-mode', (_event, { enabled } = {}) => {
    writeFirmwareSessionState({ advancedMode: !!enabled });
    const state = getFirmwareWorkspaceState();
    emitFirmwareWorkspaceState(state);
    return { ok: true, state };
});
ipcMain.handle('firmware-toolchain-get-status', () => getFirmwareToolchainStatus());
ipcMain.handle('firmware-toolchain-install', async () => {
    if (firmwareToolchainJob) {
        return {
            ok: false,
            session: 7,
            error: 'Managed toolchain installation is already running.',
            state: getFirmwareToolchainStatus(),
        };
    }

    const existingManaged = resolveManagedPlatformioStatus();
    const existingManagedClangd = resolveManagedClangdStatus();
    if (existingManaged.available && existingManagedClangd.available) {
        return {
            ok: true,
            session: 7,
            installed: true,
            state: getFirmwareToolchainStatus(),
        };
    }

    firmwareToolchainJob = {
        id: `firmware-toolchain-${Date.now()}`,
        startedAt: new Date().toISOString(),
        components: [
            ...(!existingManaged.available ? ['platformio'] : []),
            ...(!existingManagedClangd.available ? ['clangd'] : []),
        ],
    };
    writeManagedPlatformioRuntimeState({
        status: existingManaged.available ? 'installed' : 'installing',
        lastError: existingManaged.available ? null : null,
    });
    writeManagedClangdRuntimeState({
        status: existingManagedClangd.available ? 'installed' : 'installing',
        lastError: existingManagedClangd.available ? null : null,
    });
    firmwarePlatformioCache = null;
    firmwareClangdCache = null;
    emitFirmwareToolchainStatus();
    emitFirmwareBuildState();
    emitFirmwareLanguageState();

    try {
        if (!existingManaged.available) {
            const result = await installManagedPlatformioRuntime();
            writeManagedPlatformioRuntimeState({
                status: 'installed',
                path: result.path,
                coreDir: result.coreDir,
                version: result.version,
                installedAt: new Date().toISOString(),
                lastError: null,
            });
            emitFirmwareRuntimeOutput(`[session-7] Managed PlatformIO runtime installed at ${result.path}\n`);
        }
        if (!existingManagedClangd.available) {
            const result = await installManagedClangdRuntime();
            writeManagedClangdRuntimeState({
                status: 'installed',
                path: result.path,
                version: result.version,
                installedAt: new Date().toISOString(),
                lastError: null,
            });
            emitFirmwareRuntimeOutput(`[session-7] Managed clangd runtime installed at ${result.path}\n`);
        }
        firmwareToolchainJob = null;
        firmwarePlatformioCache = null;
        firmwareClangdCache = null;
        emitFirmwareToolchainStatus();
        emitFirmwareBuildState();
        emitFirmwareLanguageState();
        return {
            ok: true,
            session: 7,
            installed: true,
            state: getFirmwareToolchainStatus(),
        };
    } catch (err) {
        if (!existingManaged.available) {
            writeManagedPlatformioRuntimeState({
                status: 'error',
                lastError: err?.message || String(err),
            });
        }
        if (!existingManagedClangd.available) {
            writeManagedClangdRuntimeState({
                status: 'error',
                lastError: err?.message || String(err),
            });
        }
        emitFirmwareRuntimeOutput(`[session-7] Managed toolchain install failed: ${err?.message || err}\n`, 'stderr');
        firmwareToolchainJob = null;
        firmwarePlatformioCache = null;
        firmwareClangdCache = null;
        emitFirmwareToolchainStatus();
        emitFirmwareBuildState();
        emitFirmwareLanguageState();
        return {
            ok: false,
            session: 7,
            error: err?.message || String(err),
            state: getFirmwareToolchainStatus(),
        };
    }
});
ipcMain.handle('firmware-build-get-state', () => getFirmwareBuildState());
ipcMain.handle('firmware-build-list-envs', () => {
    const buildState = getFirmwareBuildState();
    return {
        ok: true,
        session: 7,
        envs: buildState.envs,
        selectedEnv: buildState.selectedEnv,
        defaultEnv: buildState.defaultEnv,
    };
});
ipcMain.handle('firmware-build-select-env', (_event, { env } = {}) => {
    const projectState = resolveFirmwareProjectState();
    const nextEnv = selectPlatformioEnv(projectState, env || null);
    if (!nextEnv) {
        return { ok: false, error: 'No PlatformIO environments are available for this workspace.' };
    }
    if (env && !projectState.envs.includes(env)) {
        return { ok: false, error: `Unknown PlatformIO environment: ${env}` };
    }
    writeFirmwareSessionState({ selectedEnv: nextEnv });
    disposeFirmwareLanguageClient();
    const state = getFirmwareBuildState();
    emitFirmwareBuildState(state);
    emitFirmwareLanguageState();
    return { ok: true, session: 7, selectedEnv: nextEnv, state };
});
ipcMain.handle('firmware-build-run', (_event, { action } = {}) => {
    if (firmwareBuildJob) {
        return { ok: false, session: 7, error: 'A PlatformIO job is already running.', state: getFirmwareBuildState() };
    }

    const projectState = resolveFirmwareProjectState();
    if (!projectState.context.workspaceRoot) {
        return { ok: false, session: 7, error: projectState.configError || 'No attached firmware workspace.' };
    }
    if (projectState.configError) {
        return { ok: false, session: 7, error: projectState.configError };
    }

    const platformioRuntime = resolveFirmwarePlatformioStatus({ forceRefresh: true });
    if (!platformioRuntime.available) {
        const errorMessage = platformioRuntime.errors[0]?.error || 'No working PlatformIO runtime was detected.';
        emitFirmwareToolchainStatus();
        emitFirmwareBuildState();
        return { ok: false, session: 7, error: errorMessage, state: getFirmwareBuildState() };
    }

    let args;
    try {
        args = resolvePlatformioActionArgs(action, projectState.selectedEnv);
    } catch (err) {
        return { ok: false, session: 7, error: err?.message || String(err) };
    }

    const jobId = `firmware-build-${Date.now()}-${firmwareBuildSequence += 1}`;
    const child = spawn(platformioRuntime.path, args, {
        cwd: projectState.context.workspaceRoot,
        env: getFirmwarePlatformioProcessEnv(platformioRuntime),
        stdio: ['ignore', 'pipe', 'pipe'],
        windowsHide: true,
    });

    firmwareBuildJob = {
        id: jobId,
        action: String(action || 'build'),
        env: projectState.selectedEnv,
        startedAt: new Date().toISOString(),
        cancelRequested: false,
        cancelReason: null,
        process: child,
    };

    const emitChunk = (streamName, chunk) => {
        const text = Buffer.isBuffer(chunk) ? chunk.toString('utf8') : String(chunk || '');
        if (!text) return;
        emitFirmwareBuildOutput({
            jobId,
            action: firmwareBuildJob?.action || action,
            env: projectState.selectedEnv,
            stream: streamName,
            text,
        });
    };

    child.stdout?.on('data', (chunk) => emitChunk('stdout', chunk));
    child.stderr?.on('data', (chunk) => emitChunk('stderr', chunk));
    child.on('error', (err) => {
        emitChunk('stderr', `[session-7] Failed to start PlatformIO: ${err?.message || err}\n`);
        finalizeFirmwareBuild({
            completedAt: new Date().toISOString(),
            result: 'failed',
            exitCode: null,
            signal: null,
        });
        emitFirmwareLanguageState();
    });
    child.on('close', (code, signal) => {
        const canceled = !!(firmwareBuildJob && firmwareBuildJob.cancelRequested);
        const result = canceled ? 'canceled' : (code === 0 ? 'succeeded' : 'failed');
        emitChunk(
            code === 0 ? 'stdout' : 'stderr',
            `[session-7] ${String(action || 'build')} ${result} for ${projectState.selectedEnv}${code !== null ? ` (exit ${code})` : ''}${signal ? ` via ${signal}` : ''}\n`
        );
        finalizeFirmwareBuild({
            completedAt: new Date().toISOString(),
            result,
            exitCode: code,
            signal,
        });
        if (action === 'reindex' && result === 'succeeded') {
            disposeFirmwareLanguageClient();
        }
        emitFirmwareLanguageState();
    });

    emitFirmwareBuildOutput({
        jobId,
        action: firmwareBuildJob.action,
        env: projectState.selectedEnv,
        stream: 'stdout',
        text: `[session-7] Running ${platformioRuntime.path} ${args.join(' ')} in ${projectState.context.workspaceRoot}\n`,
    });
    emitFirmwareBuildState();
    emitFirmwareLanguageState();
    return { ok: true, session: 7, jobId, state: getFirmwareBuildState() };
});
ipcMain.handle('firmware-build-cancel', () => {
    if (!firmwareBuildJob) {
        return { ok: false, session: 7, error: 'No PlatformIO job is running.' };
    }
    const canceled = cancelRunningFirmwareBuild('user-request');
    emitFirmwareBuildState();
    return {
        ok: canceled,
        session: 7,
        canceled,
        jobId: firmwareBuildJob?.id || null,
        state: getFirmwareBuildState(),
        error: canceled ? null : 'Could not cancel the running PlatformIO job.',
    };
});
ipcMain.handle('firmware-language-get-state', () => getFirmwareLanguageState());
ipcMain.handle('firmware-language-sync-document', async (_event, { relativePath, content } = {}) => {
    if (!relativePath) {
        return { ok: false, session: 7, error: 'Missing relativePath.', state: getFirmwareLanguageState() };
    }
    try {
        const response = await syncFirmwareLanguageDocument(relativePath, content ?? '');
        emitFirmwareLanguageState();
        return {
            session: 7,
            ...response,
        };
    } catch (err) {
        return { ok: false, session: 7, error: err?.message || String(err), state: getFirmwareLanguageState() };
    }
});
ipcMain.handle('firmware-language-complete', async (_event, { relativePath, content, position } = {}) => {
    if (!relativePath || !position) {
        return { ok: false, session: 7, error: 'Missing language completion parameters.', state: getFirmwareLanguageState() };
    }
    const context = resolveFirmwareWorkspaceContext();
    if (!context.workspaceRoot) {
        return { ok: false, session: 7, error: 'No attached firmware workspace.', state: getFirmwareLanguageState() };
    }
    const clientState = await ensureFirmwareLanguageClient();
    if (!clientState.ok) {
        return { ok: false, session: 7, error: clientState.error || clientState.state.message, state: clientState.state };
    }
    try {
        const resolved = resolveWorkspacePath(context.workspaceRoot, relativePath);
        const result = await clientState.client.completion({
            filePath: resolved.absolutePath,
            text: content ?? '',
            position,
            languageId: 'cpp',
        });
        return { ok: true, session: 7, items: Array.isArray(result?.items) ? result.items : (Array.isArray(result) ? result : []), incomplete: !!result?.isIncomplete, state: getFirmwareLanguageState() };
    } catch (err) {
        return { ok: false, session: 7, error: err?.message || String(err), state: getFirmwareLanguageState() };
    }
});
ipcMain.handle('firmware-language-hover', async (_event, { relativePath, content, position } = {}) => {
    if (!relativePath || !position) {
        return { ok: false, session: 7, error: 'Missing hover parameters.', state: getFirmwareLanguageState() };
    }
    const context = resolveFirmwareWorkspaceContext();
    if (!context.workspaceRoot) {
        return { ok: false, session: 7, error: 'No attached firmware workspace.', state: getFirmwareLanguageState() };
    }
    const clientState = await ensureFirmwareLanguageClient();
    if (!clientState.ok) {
        return { ok: false, session: 7, error: clientState.error || clientState.state.message, state: clientState.state };
    }
    try {
        const resolved = resolveWorkspacePath(context.workspaceRoot, relativePath);
        const result = await clientState.client.hover({
            filePath: resolved.absolutePath,
            text: content ?? '',
            position,
            languageId: 'cpp',
        });
        return { ok: true, session: 7, hover: result, state: getFirmwareLanguageState() };
    } catch (err) {
        return { ok: false, session: 7, error: err?.message || String(err), state: getFirmwareLanguageState() };
    }
});
ipcMain.handle('firmware-language-definition', async (_event, { relativePath, content, position } = {}) => {
    if (!relativePath || !position) {
        return { ok: false, session: 7, error: 'Missing definition parameters.', state: getFirmwareLanguageState() };
    }
    const context = resolveFirmwareWorkspaceContext();
    if (!context.workspaceRoot) {
        return { ok: false, session: 7, error: 'No attached firmware workspace.', state: getFirmwareLanguageState() };
    }
    const clientState = await ensureFirmwareLanguageClient();
    if (!clientState.ok) {
        return { ok: false, session: 7, error: clientState.error || clientState.state.message, state: clientState.state };
    }
    try {
        const resolved = resolveWorkspacePath(context.workspaceRoot, relativePath);
        const result = await clientState.client.definition({
            filePath: resolved.absolutePath,
            text: content ?? '',
            position,
            languageId: 'cpp',
        });
        return { ok: true, session: 7, definition: result, state: getFirmwareLanguageState() };
    } catch (err) {
        return { ok: false, session: 7, error: err?.message || String(err), state: getFirmwareLanguageState() };
    }
});

// ── Extension Manager ──────────────────────────────────────────────────────

function getInstalledRoot() {
    return path.join(app.getPath('userData'), 'extensions');
}

function readManagerState() {
    return readInstalledState(getInstalledRoot());
}

function writeManagerState(state) {
    const dir = getInstalledRoot();
    fs.mkdirSync(dir, { recursive: true });
    fs.writeFileSync(path.join(dir, 'state.json'), JSON.stringify(state, null, 2), 'utf8');
}

function copyDirSync(src, dest) {
    fs.mkdirSync(dest, { recursive: true });
    for (const entry of fs.readdirSync(src, { withFileTypes: true })) {
        const srcPath = path.join(src, entry.name);
        const destPath = path.join(dest, entry.name);
        if (entry.isDirectory()) copyDirSync(srcPath, destPath);
        else fs.copyFileSync(srcPath, destPath);
    }
}

ipcMain.handle('extensions-manager-list', () => {
    return extensionRuntime.inventory.map((e) => ({
        ...e,
        source: e.isInstalled ? 'installed' : 'builtin',
    }));
});

ipcMain.handle('extensions-choose-bundle', async () => {
    if (!mainWindow) return null;
    const { canceled, filePaths } = await dialog.showOpenDialog(mainWindow, {
        title: 'Select Extension Bundle Directory',
        properties: ['openDirectory'],
    });
    if (canceled || !filePaths.length) return null;
    return filePaths[0];
});

ipcMain.handle('extensions-manager-install', async (_event, { bundlePath } = {}) => {
    if (!bundlePath) return { ok: false, error: 'Missing bundle path' };
    try {
        const manifestPath = path.join(bundlePath, 'manifest.json');
        if (!fs.existsSync(manifestPath)) return { ok: false, error: 'No manifest.json found in bundle directory' };
        const manifest = JSON.parse(fs.readFileSync(manifestPath, 'utf8'));
        const id = String(manifest.id || '').trim();
        const version = String(manifest.version || '0.0.0');
        if (!id) return { ok: false, error: 'Bundle manifest is missing an id field' };
        const destDir = path.join(getInstalledRoot(), id, version);
        if (fs.existsSync(destDir)) return { ok: false, error: `Extension ${id}@${version} is already installed` };
        copyDirSync(bundlePath, destDir);
        const state = readManagerState();
        state[id] = { enabled: !!manifest.enabledByDefault, version };
        writeManagerState(state);
        return { ok: true, id, version, requiresRestart: true };
    } catch (err) {
        return { ok: false, error: err?.message || String(err) };
    }
});

ipcMain.handle('extensions-manager-uninstall', (_event, { id } = {}) => {
    if (!id) return { ok: false, error: 'Missing id' };
    try {
        const state = readManagerState();
        const version = state[id]?.version;
        delete state[id];
        writeManagerState(state);
        if (version) {
            const bundleDir = path.join(getInstalledRoot(), id, version);
            if (fs.existsSync(bundleDir)) fs.rmSync(bundleDir, { recursive: true, force: true });
            const idDir = path.join(getInstalledRoot(), id);
            if (fs.existsSync(idDir) && !fs.readdirSync(idDir).length) fs.rmdirSync(idDir);
        }
        return { ok: true, requiresRestart: true };
    } catch (err) {
        return { ok: false, error: err?.message || String(err) };
    }
});

ipcMain.handle('extensions-manager-enable', (_event, { id } = {}) => {
    if (!id) return { ok: false, error: 'Missing id' };
    if (id === 'core') return { ok: false, error: 'The core extension cannot be disabled' };
    const state = readManagerState();
    if (!state[id]) state[id] = {};
    state[id].enabled = true;
    writeManagerState(state);
    return { ok: true, requiresRestart: true };
});

ipcMain.handle('extensions-manager-disable', (_event, { id } = {}) => {
    if (!id) return { ok: false, error: 'Missing id' };
    if (id === 'core') return { ok: false, error: 'The core extension cannot be disabled' };
    const state = readManagerState();
    if (!state[id]) state[id] = {};
    state[id].enabled = false;
    writeManagerState(state);
    return { ok: true, requiresRestart: true };
});

// ──────────────────────────────────────────────────────────────────────────────

function setAppMenu() {
    const widgetExtensionsMenu = buildWidgetExtensionsMenuItems();
    const owntechExamplesMenu = buildExamplesMenuItems('owntech-examples');
    const coursewareMenu = buildCoursewareMenuItems();
    const tutorialsMenu = buildTutorialsMenuItems();
    const template = [
        {
            label: 'File',
            submenu: [
                {
                    label: 'New Dashboard Tab',
                    accelerator: 'CmdOrCtrl+T',
                    click: () => {
                        if (mainWindow && mainWindow.webContents) {
                            mainWindow.webContents.send('menu-new-dashboard');
                        }
                    }
                },
                {
                    label: 'Open Dashboard',
                    accelerator: 'CmdOrCtrl+O',
                    click: () => {
                        if (mainWindow && mainWindow.webContents) {
                            mainWindow.webContents.send('menu-load-dashboard');
                        }
                    }
                },
                {
                    label: 'Firmware Workspace',
                    enabled: isExtensionEnabled('owntech-workspace'),
                    click: () => {
                        openFirmwareWorkspaceWindow();
                    }
                },
                { type: 'separator' },
                {
                    label: 'Save Dashboard',
                    accelerator: 'CmdOrCtrl+S',
                    click: () => {
                        if (mainWindow && mainWindow.webContents) {
                            mainWindow.webContents.send('menu-save-dashboard');
                        }
                    }
                },
                { type: 'separator' },
                { role: process.platform === 'darwin' ? 'close' : 'quit' }
            ]
        },
        {
            label: 'Edit',
            submenu: [
                {
                    label: 'Toggle Activity',
                    type: 'checkbox',
                    checked: activityEnabled,
                    click: (item) => {
                        activityEnabled = !!item.checked;
                        if (mainWindow && mainWindow.webContents) {
                            mainWindow.webContents.send('activity-toggle', { enabled: activityEnabled });
                        }
                    }
                },
                { type: 'separator' },
                {
                    label: 'Widget Categories',
                    click: () => {
                        if (mainWindow && mainWindow.webContents) {
                            mainWindow.webContents.send('show-widget-categories');
                        }
                    }
                },
                { type: 'separator' },
                {
                    label: 'Extension Manager',
                    click: () => {
                        if (mainWindow && mainWindow.webContents) {
                            mainWindow.webContents.send('open-extension-manager');
                        }
                    }
                }
            ]
        },
        {
            label: 'Widget Extensions',
            submenu: widgetExtensionsMenu
        }
    ];

    if (isExtensionEnabled('tutorials')) {
        template.push({
            label: 'Tutorials',
            submenu: tutorialsMenu
        });
    }
    if (isExtensionEnabled('owntech-examples')) {
        template.push({
            label: 'OwnTech Examples',
            submenu: owntechExamplesMenu
        });
    }
    if (isExtensionEnabled('courseware')) {
        template.push({
            label: 'Courseware',
            submenu: coursewareMenu
        });
    }

    Menu.setApplicationMenu(Menu.buildFromTemplate(template));
    // Sync activity toggle state to the renderer on menu build.
    if (mainWindow && mainWindow.webContents) {
        mainWindow.webContents.send('activity-toggle', { enabled: activityEnabled });
    }
}

// Activity toggle (default off to reduce UI noise).
let activityEnabled = false;

// Emit UI activity events to renderer (used for toasts/indicators)
function emitActivity(evt) {
    try {
        // Respect the activity toggle to avoid spamming the renderer.
        if (activityEnabled && mainWindow && mainWindow.webContents) {
            mainWindow.webContents.send('activity', { ts: Date.now(), scope: 'can', ...evt });
        }
    } catch {}
}
extensionSharedContext.emitActivity = emitActivity;

// Allow renderer to query the current activity toggle state.
ipcMain.handle('get-activity-enabled', () => ({ enabled: !!activityEnabled }));
ipcMain.handle('diagnostics-capture-snapshot', async () => captureDiagnosticsSnapshot());
ipcMain.handle('perf-log-snapshot', async () => {
    const mem = process.memoryUsage();
    const ipcSnapshot = Object.fromEntries(ipcCallCounts);
    const inProgressAcq = [];
    for (const [port, st] of fastStates) {
        if (st.state === FAST_RECORD) inProgressAcq.push({ port, lines: st.data.length });
    }
    let rendererMem = null;
    try {
        const rendererPid = mainWindow?.webContents?.getOSProcessId?.();
        if (rendererPid && typeof app.getAppMetrics === 'function') {
            const metric = app.getAppMetrics().find(m => m.pid === rendererPid);
            if (metric?.memory) {
                rendererMem = { workingSetMB: (metric.memory.workingSetSize / 1024).toFixed(1), pid: rendererPid };
            }
        }
    } catch (_) { /* ignore */ }
    let rendererV8 = null;
    try {
        if (mainWindow?.webContents && !mainWindow.webContents.isDestroyed()) {
            rendererV8 = await mainWindow.webContents.executeJavaScript(`
                (function() {
                    const m = performance.memory;
                    if (!m) return null;
                    return {
                        usedMB: (m.usedJSHeapSize / 1e6).toFixed(1),
                        totalMB: (m.totalJSHeapSize / 1e6).toFixed(1),
                        limitMB: (m.jsHeapSizeLimit / 1e6).toFixed(1),
                        domNodes: document.querySelectorAll('*').length
                    };
                })()
            `);
        }
    } catch (_) { /* ignore */ }
    const snap = {
        uptimeSec: Math.round(process.uptime()),
        mainProc: {
            heapUsedMB: (mem.heapUsed / 1e6).toFixed(1),
            heapTotalMB: (mem.heapTotal / 1e6).toFixed(1),
            rssMB: (mem.rss / 1e6).toFixed(1),
            externalMB: (mem.external / 1e6).toFixed(1),
        },
        renderer: { proc: rendererMem, v8: rendererV8 },
        ipcCallsSinceStart: ipcSnapshot,
        ports: {
            open: openPorts.size,
            serialBuffers: summarizeArrayMap(serialBuffers),
            terminalBuffers: summarizeArrayMap(terminalBuffers),
            rawBufferSizes: Object.fromEntries(rawBufferSizes),
            inProgressAcquisitions: inProgressAcq,
        },
    };
    console.log('[HEALTH/on-demand]', JSON.stringify(snap, null, 2));
    return snap;
});

function getBundledMcumgrCandidates() {
    if (process.platform === 'win32') {
        return ['mcumgr.exe'];
    }

    if (process.platform === 'darwin') {
        if (process.arch === 'arm64') {
            return ['mcumgr-mac-arm64'];
        }
        return ['mcumgr-mac-x64'];
    }

    if (process.platform === 'linux') {
        if (process.arch === 'arm64') {
            return ['mcumgr-linux-arm64', 'mcumgr'];
        }
        if (process.arch === 'arm') {
            return ['mcumgr-linux-armv7', 'mcumgr'];
        }
        if (process.arch === 'ia32') {
            return ['mcumgr-linux-x86', 'mcumgr'];
        }
        return ['mcumgr-linux-x64', 'mcumgr'];
    }

    return ['mcumgr'];
}

const mcumgrCandidates = getBundledMcumgrCandidates();
let activeFlashId = 0;
let activeFlashSender = null;
let activeFlashPort = null;
let activeFlashCanceled = false;

function resolveMcumgrPath(userPath) {
    if (userPath && typeof userPath === 'string') return userPath;
    if (process.env.MCUMGR_PATH) return process.env.MCUMGR_PATH;
    for (const mcumgrBinary of mcumgrCandidates) {
        const bundledPath = path.join(__dirname, 'tools', mcumgrBinary);
        if (fs.existsSync(bundledPath)) return bundledPath;
    }
    // Fallback to PATH on Linux when bundled binary is missing.
    return 'mcumgr';
}

const activeRecordings = new Map(); // Active CSV recordings mapped by port path
const openPorts = new Map(); // key: path, value: SerialPort instance
extensionSharedContext.openPorts = openPorts;
const safetyCommands = new Map(); // key: path, value: command string to send on shutdown
// Track ports that should not be opened (e.g., during flashing).
const serialLocks = new Map(); // key: path, value: { reason, until }
// Persist last-known serial settings per port so we can auto-reopen later.
const portSettings = new Map(); // key: path, value: { baudRate, separator, eol, type }
// Track pending auto-reopen timers and intent per port.
const pendingReopens = new Map(); // key: path, value: { timer: Timeout|null, settings }
const terminalBuffers = new Map(); // key: path, value: array of raw lines
const serialBuffers = new Map(); // key: path, value: array of parsed data arrays
const parserSettings = new Map(); // key: path, value: { separator, eol }
// header and color buffers keyed by "path||type" to support multiple
// datasources on the same serial port
const headerBuffers = new Map();
const colorBuffers = new Map();
const fastStates = new Map(); // key: path, value: state for fast frame parsing
const fastBuffers = new Map(); // key: path, value: last parsed fast dataset
const fastStatus = new Map(); // key: path, value: acquisition status metadata
const fastAcquisitionSeq = new Map(); // key: path, value: monotonically increasing acquisition id

// Instrumentation
const ipcCallCounts = new Map(); // channel → call count since last health log
const rawBufferSizes = new Map(); // port path → current rawBuffer byte length

const FAST_IDLE = 0;
const FAST_RECORD = 1;
const MAX_BUFFER_SIZE = 1000;
const MAX_TERMINAL_LINES = 200;

function dsKey(path, type = 'serialport_datasource') {
    return `${path}||${type}`;
}

function summarizeArrayMap(map) {
    let entries = 0;
    let totalItems = 0;
    let maxItems = 0;
    for (const value of map.values()) {
        entries += 1;
        const length = Array.isArray(value) ? value.length : 0;
        totalItems += length;
        if (length > maxItems) maxItems = length;
    }
    return { entries, totalItems, maxItems };
}

function summarizeFastBuffers(map) {
    let entries = 0;
    let totalPoints = 0;
    let maxPoints = 0;
    for (const value of map.values()) {
        entries += 1;
        const points = Array.isArray(value?.timestamps) ? value.timestamps.length : 0;
        totalPoints += points;
        if (points > maxPoints) maxPoints = points;
    }
    return { entries, totalPoints, maxPoints };
}

function summarizeMapEntries(map) {
    return { entries: map.size };
}

function trackIpcCall(channel) {
    ipcCallCounts.set(channel, (ipcCallCounts.get(channel) || 0) + 1);
}

async function captureDiagnosticsSnapshot() {
    const memory = process.memoryUsage();
    const cpu = process.cpuUsage();
    const resource = typeof process.resourceUsage === 'function' ? process.resourceUsage() : null;
    const appMetrics = typeof app.getAppMetrics === 'function'
        ? app.getAppMetrics().map((metric) => ({
            pid: metric.pid,
            type: metric.type,
            serviceName: metric.serviceName,
            name: metric.name,
            creationTime: metric.creationTime,
            cpu: metric.cpu ? {
                percentCPUUsage: metric.cpu.percentCPUUsage,
                idleWakeupsPerSecond: metric.cpu.idleWakeupsPerSecond
            } : null,
            memory: metric.memory ? {
                workingSetSize: metric.memory.workingSetSize,
                peakWorkingSetSize: metric.memory.peakWorkingSetSize,
                privateBytes: metric.memory.privateBytes,
                sharedBytes: metric.memory.sharedBytes
            } : null
        }))
        : [];

    let rendererProcessMemory = null;
    try {
        if (mainWindow?.webContents?.getProcessMemoryInfo) {
            rendererProcessMemory = await mainWindow.webContents.getProcessMemoryInfo();
        }
    } catch (err) {
        rendererProcessMemory = { error: err?.message || String(err) };
    }

    return {
        timestamp: Date.now(),
        process: {
            pid: process.pid,
            uptimeSec: process.uptime(),
            platform: process.platform,
            versions: {
                electron: process.versions.electron,
                chrome: process.versions.chrome,
                node: process.versions.node
            },
            memory,
            cpu,
            resource
        },
        renderer: {
            webContentsId: mainWindow?.webContents?.id ?? null,
            url: mainWindow?.webContents?.getURL?.() ?? null,
            processMemory: rendererProcessMemory
        },
        windows: {
            main: mainWindow ? {
                visible: mainWindow.isVisible(),
                focused: mainWindow.isFocused(),
                bounds: mainWindow.getBounds()
            } : null,
            example: exampleWindow ? {
                visible: exampleWindow.isVisible(),
                focused: exampleWindow.isFocused(),
                bounds: exampleWindow.getBounds()
            } : null
        },
                state: {
                    openPorts: openPorts.size,
                    activeRecordings: activeRecordings.size,
                    serialLocks: serialLocks.size,
            portSettings: portSettings.size,
            pendingReopens: pendingReopens.size,
            serialBuffers: summarizeArrayMap(serialBuffers),
            terminalBuffers: summarizeArrayMap(terminalBuffers),
            headerBuffers: summarizeMapEntries(headerBuffers),
            colorBuffers: summarizeMapEntries(colorBuffers),
            fastStates: summarizeMapEntries(fastStates),
            fastBuffers: summarizeFastBuffers(fastBuffers),
            fastStatus: summarizeMapEntries(fastStatus)
                },
                appMetrics
            };
}

function startHealthMonitor(intervalMs = 60_000) {
    const { PerformanceObserver } = require('perf_hooks');
    const gcEvents = [];
    try {
        const obs = new PerformanceObserver((list) => {
            for (const entry of list.getEntries()) {
                gcEvents.push({ kind: entry.detail?.kind, durationMs: Math.round(entry.duration) });
                if (gcEvents.length > 30) gcEvents.shift();
            }
        });
        obs.observe({ entryTypes: ['gc'] });
    } catch (e) {
        console.warn('[HEALTH] GC observer unavailable:', e.message);
    }

    // Detect event-loop blockage: measure how far each 1-second tick drifts.
    let lagBaseline = Date.now();
    const lagChecker = setInterval(() => {
        const now = Date.now();
        const lag = now - lagBaseline - 1000;
        lagBaseline = now;
        if (lag > 150) console.warn(`[HEALTH] Event-loop lag: ${lag}ms`);
    }, 1000);
    lagChecker.unref();

    const healthTick = setInterval(async () => {
        const mem = process.memoryUsage();

        // Snapshot and reset IPC call counts
        const ipcSnapshot = {};
        for (const [ch, n] of ipcCallCounts) {
            ipcSnapshot[ch] = n;
            ipcCallCounts.set(ch, 0);
        }

        // In-progress fast acquisitions whose data[] array could grow unbounded
        const inProgressAcq = [];
        for (const [port, st] of fastStates) {
            if (st.state === FAST_RECORD) inProgressAcq.push({ port, lines: st.data.length });
        }

        // Renderer OS-level memory: find the renderer process in app.getAppMetrics() by PID.
        // workingSetSize (KB) is the reliable cross-platform field on Linux.
        let rendererMem = null;
        try {
            const rendererPid = mainWindow?.webContents?.getOSProcessId?.();
            if (rendererPid && typeof app.getAppMetrics === 'function') {
                const metric = app.getAppMetrics().find(m => m.pid === rendererPid);
                if (metric?.memory) {
                    rendererMem = {
                        workingSetMB: (metric.memory.workingSetSize / 1024).toFixed(1),
                        pid: rendererPid,
                    };
                }
            }
        } catch (_) { /* ignore */ }

        // Renderer V8 JS heap via executeJavaScript (gives usedJSHeapSize / totalJSHeapSize)
        let rendererV8 = null;
        try {
            if (mainWindow?.webContents && !mainWindow.webContents.isDestroyed()) {
                rendererV8 = await mainWindow.webContents.executeJavaScript(`
                    (function() {
                        const m = performance.memory;
                        if (!m) return null;
                        return {
                            usedMB: (m.usedJSHeapSize / 1e6).toFixed(1),
                            totalMB: (m.totalJSHeapSize / 1e6).toFixed(1),
                            limitMB: (m.jsHeapSizeLimit / 1e6).toFixed(1),
                            domNodes: document.querySelectorAll('*').length
                        };
                    })()
                `);
            }
        } catch (_) { /* ignore */ }

        console.log('[HEALTH]', JSON.stringify({
            uptimeSec: Math.round(process.uptime()),
            mainProc: {
                heapUsedMB: (mem.heapUsed / 1e6).toFixed(1),
                heapTotalMB: (mem.heapTotal / 1e6).toFixed(1),
                rssMB: (mem.rss / 1e6).toFixed(1),
                externalMB: (mem.external / 1e6).toFixed(1),
            },
            renderer: { proc: rendererMem, v8: rendererV8 },
            ipcCallsLastCycle: ipcSnapshot,
            ports: {
                open: openPorts.size,
                serialBuffers: summarizeArrayMap(serialBuffers),
                terminalBuffers: summarizeArrayMap(terminalBuffers),
                rawBufferSizes: Object.fromEntries(rawBufferSizes),
                inProgressAcquisitions: inProgressAcq,
            },
            gcRecentEvents: gcEvents.slice(-5),
        }));
    }, intervalMs);
    healthTick.unref();
}

function decodeEolToken(token) {
    if (!token || typeof token !== 'string') return '\n';
    let out = token;
    out = out.replace(/\\r/g, '\r');
    out = out.replace(/\\n/g, '\n');
    out = out.replace(/\\t/g, '\t');
    return out;
}

function lockSerialPort(path, reason = 'locked', ttlMs = 30000) {
    if (!path) return;
    const until = ttlMs ? Date.now() + ttlMs : null;
    serialLocks.set(path, { reason, until });
}

function unlockSerialPort(path) {
    if (!path) return;
    serialLocks.delete(path);
}

function isSerialLocked(path) {
    const lock = serialLocks.get(path);
    if (!lock) return false;
    if (lock.until && Date.now() > lock.until) {
        serialLocks.delete(path);
        return false;
    }
    return true;
}

function addToBuffer(portPath, parsedData) {
        if (!Array.isArray(parsedData)) return;
        let buf = serialBuffers.get(portPath);
        if (!buf) {
                buf = [];
                serialBuffers.set(portPath, buf);
        }
        buf.push(parsedData);
        if (buf.length > MAX_BUFFER_SIZE) {
                buf.shift();
        }
}

function parseLine(line, separator = ':') {
	const clean = line.trim();
	const rawItems = clean.split(separator).filter(s => s.trim() !== "");
	const values = rawItems.map(v => parseFloat(v)).filter(n => !isNaN(n));
	return values;
}

function parseLineCustom(line, sep) {
        const clean = line.trim();
        return clean.split(sep).map(s => s.trim()).filter(s => s !== "");
}

function setFastStatus(path, partial = {}) {
    const prev = fastStatus.get(path) || {
        state: 'idle',
        message: '',
        updatedAt: Date.now(),
        completedAt: null,
        datasetPoints: 0,
        acquisitionId: 0
    };
    const next = {
        ...prev,
        ...partial,
        updatedAt: Date.now()
    };
    fastStatus.set(path, next);
    return next;
}

function handleFastLine(portPath, line) {
    let st = fastStates.get(portPath);
    if (!st) {
        st = { state: FAST_IDLE, header: null, idx: null, data: [] };
        fastStates.set(portPath, st);
    }

    if (line.includes('begin record')) {
        st.state = FAST_RECORD;
        st.header = null;
        st.idx = null;
        st.data = [];
        setFastStatus(portPath, {
            state: 'recording',
            message: 'Receiving fast frame',
            completedAt: null,
            datasetPoints: 0
        });
        return;
    }

    if (line.includes('end record')) {
        st.state = FAST_IDLE;
        const dataset = buildFastDataset(st);
        if (dataset) {
            const acquisitionId = fastAcquisitionSeq.get(portPath) || 0;
            dataset.acquisitionId = acquisitionId;
            dataset.capturedAt = Date.now();
            fastBuffers.set(portPath, dataset);
            setFastStatus(portPath, {
                state: 'complete',
                message: 'Fast frame ready',
                completedAt: dataset.capturedAt,
                datasetPoints: Array.isArray(dataset.timestamps) ? dataset.timestamps.length : 0,
                acquisitionId
            });
        } else {
            setFastStatus(portPath, {
                state: 'error',
                message: 'Fast frame ended without valid dataset',
                completedAt: null,
                datasetPoints: 0
            });
        }
        st.header = null;
        st.idx = null;
        st.data = [];
        return;
    }

    if (st.state === FAST_RECORD) {
        if (line.startsWith('#')) {
            if (!st.header) {
                st.header = line.substring(1).trim();
                const hdrs = st.header.split(',').map(h => h.trim()).filter(Boolean);
                headerBuffers.set(dsKey(portPath, 'fast_frame_datasource'), hdrs);
            } else if (st.idx === null) {
                const num = parseInt(line.replace(/^#+\s*/, '').trim());
                st.idx = isNaN(num) ? null : num;
            }
        } else if (line.trim()) {
            st.data.push(line.trim());
        }
    }
}

function buildFastDataset(st) {
    if (!st.header || !st.data.length) return null;
    let names = st.header.split(',').map(n => n.trim());
    if (names[names.length - 1] === '') names.pop();

    const floats = [];
    for (const hex of st.data) {
        try {
            const buf = Buffer.from(hex, 'hex');
            if (buf.length >= 4) floats.push(buf.readFloatBE(0));
        } catch { /* ignore */ }
    }

    const chunk = names.length;
    const rows = [];
    for (let i = 0; i < floats.length; i += chunk) {
        rows.push(floats.slice(i, i + chunk));
    }
    if (!rows.length) return null;

    if (st.idx !== null && st.idx >= 0 && st.idx < rows.length) {
        const shift = (st.idx + 1) % rows.length;
        if (shift) {
            for (let i = 0; i < shift; i++) {
                rows.push(rows.shift());
            }
        }
    }

    const timestamps = rows.map((_, i) => i);
    const series = names.map((_, ci) => rows.map(r => r[ci]));

    return { timestamps, series };
}

function createWindow() {
        mainWindow = new BrowserWindow({
                width: 1280,
                height: 800,
                icon: path.join(__dirname, 'assets', 'icon.png'),
                webPreferences: {
                        preload: path.join(__dirname, 'preload.js'),
                        sandbox: false,
                        nodeIntegration: false,
                        contextIsolation: true
                }
        });
        // Only open DevTools in development.
        if (!app.isPackaged) {
            mainWindow.webContents.openDevTools({ mode: 'detach' });
            mainWindow.webContents.on('did-fail-load', (_e, code, desc, url) => {
                console.error('[main] did-fail-load', code, desc, url);
            });
        }
        setAppMenu();
        mainWindow.loadFile(path.join(__dirname, 'dashboard/index.html'));
        mainWindow.on('closed', () => {
                mainWindow = null;
        });
        startHealthMonitor(60_000);
}

function normalizeDocRequest(kindOrPayload, id) {
    let payload = kindOrPayload;
    if (typeof payload === 'string') {
        payload = { kind: kindOrPayload, id };
    }
    if (!payload || typeof payload !== 'object') return null;
    const kindValue = String(payload.kind || '').trim().toLowerCase();
    const idValue = String(payload.id || '').trim();
    if (!kindValue || !idValue) return null;
    if (!['example', 'courseware'].includes(kindValue)) return null;
    return { kind: kindValue, id: idValue };
}

function emitDocTabOpen(targetWindow, payload) {
    if (!targetWindow || !targetWindow.webContents || !payload) return;
    targetWindow.webContents.send('open-doc-tab', payload);
    if (payload.kind === 'example') {
        targetWindow.webContents.send('open-example-tab', { id: payload.id });
    }
}

function emitDocSelect(targetWindow, payload) {
    if (!targetWindow || !targetWindow.webContents || !payload) return;
    targetWindow.webContents.send('doc-select', payload);
    if (payload.kind === 'example') {
        targetWindow.webContents.send('example-select', { id: payload.id });
    }
}

function emitDockPreview(targetWindow, payload) {
    if (!targetWindow || !targetWindow.webContents) return;
    targetWindow.webContents.send('doc-dock-preview', payload);
    if (payload && payload.kind === 'example') {
        targetWindow.webContents.send('example-dock-preview', {
            id: payload.id,
            active: payload.active,
        });
    } else if (payload && payload.active === false) {
        targetWindow.webContents.send('example-dock-preview', { id: null, active: false });
    }
}

function openDocTab(kindOrPayload, id) {
    const payload = normalizeDocRequest(kindOrPayload, id);
    if (!payload) return;
    pendingDocTabRequest = payload;
    if (mainWindow && mainWindow.webContents) {
        try {
            clearTimeout(exampleTabRequestTimer);
            exampleTabRequestTimer = setTimeout(() => {
                emitDocTabOpen(mainWindow, payload);
            }, 0);
            return;
        } catch {
            // Fall back to a dedicated window if the tab IPC fails.
        }
    }
    openExampleWindow(payload);
}

function openExampleTab(exampleId) {
    openDocTab('example', exampleId);
}

function openCoursewareTab(coursewareId) {
    openDocTab('courseware', coursewareId);
}

function normalizeTutorialRequest(payload) {
    if (typeof payload === 'string') {
        payload = { id: payload };
    }
    if (!payload || typeof payload !== 'object') return null;
    const id = String(payload.id || '').trim();
    if (!id) return null;
    return { id };
}

function emitTutorialOpen(targetWindow, payload) {
    if (!targetWindow || !targetWindow.webContents || !payload) return;
    targetWindow.webContents.send('open-tutorial', payload);
}

function openTutorial(payloadOrId) {
    const payload = normalizeTutorialRequest(payloadOrId);
    if (!payload) return;
    pendingTutorialRequest = payload;
    if (mainWindow && mainWindow.webContents) {
        emitTutorialOpen(mainWindow, payload);
    }
}

ipcMain.on('open-doc-tab', (_event, payload) => {
    openDocTab(payload);
});

ipcMain.on('open-example-tab', (_event, { id } = {}) => {
    openExampleTab(id);
});

ipcMain.handle('get-pending-doc-tab', () => {
    const pending = pendingDocTabRequest ? { ...pendingDocTabRequest } : null;
    pendingDocTabRequest = null;
    return pending;
});

ipcMain.handle('get-pending-example-tab', () => {
    if (!pendingDocTabRequest || pendingDocTabRequest.kind !== 'example') return null;
    const id = pendingDocTabRequest.id;
    pendingDocTabRequest = null;
    return id;
});

ipcMain.on('open-tutorial', (_event, payload) => {
    openTutorial(payload);
});

ipcMain.handle('get-pending-tutorial', () => {
    const pending = pendingTutorialRequest ? { ...pendingTutorialRequest } : null;
    pendingTutorialRequest = null;
    return pending;
});

ipcMain.on('tutorials-ready', () => {
    if (!pendingTutorialRequest) return;
    const pending = pendingTutorialRequest;
    pendingTutorialRequest = null;
    emitTutorialOpen(mainWindow, pending);
});

// Standalone docs window for offline markdown docs and lab actions.
function openExampleWindow(kindOrPayload, maybeId) {
    const payload = normalizeDocRequest(kindOrPayload, maybeId);
    if (!payload) return;
    if (exampleWindow) {
        exampleWindow.focus();
        emitDocSelect(exampleWindow, payload);
        return;
    }
    exampleWindowActiveRef = payload;
    exampleWindow = new BrowserWindow({
        width: 1100,
        height: 800,
        title: 'Modular Docs',
        icon: path.join(__dirname, 'assets', 'icon.png'),
        webPreferences: {
            preload: path.join(__dirname, 'preload.js'),
            sandbox: false,
            nodeIntegration: false,
            contextIsolation: true
        }
    });
    exampleWindow.loadFile(path.join(__dirname, 'dashboard', 'examples', 'example_viewer.html'), {
        query: { kind: payload.kind, id: payload.id }
    });
    // Watch for window moves to show a dock preview and pop the tab back in on release.
    const updateDockPreview = () => {
        if (!exampleWindow || !mainWindow || !mainWindow.webContents) return;
        const eb = exampleWindow.getBounds();
        const mb = mainWindow.getBounds();
        const overlapX = Math.max(0, Math.min(eb.x + eb.width, mb.x + mb.width) - Math.max(eb.x, mb.x));
        const overlapY = Math.max(0, Math.min(eb.y + eb.height, mb.y + mb.height) - Math.max(eb.y, mb.y));
        const overlapArea = overlapX * overlapY;
        const exampleArea = eb.width * eb.height || 1;
        const overlapRatio = overlapArea / exampleArea;
        const shouldPreview = overlapRatio >= 0.2 && Boolean(exampleWindowActiveRef && exampleWindowActiveRef.id);
        if (shouldPreview !== exampleDockPreviewActive || exampleDockLastOverlap !== shouldPreview) {
            exampleDockPreviewActive = shouldPreview;
            exampleDockLastOverlap = shouldPreview;
            emitDockPreview(mainWindow, {
                kind: exampleWindowActiveRef ? exampleWindowActiveRef.kind : null,
                id: exampleWindowActiveRef ? exampleWindowActiveRef.id : null,
                active: shouldPreview
            });
        }
    };
    const tryDockOnRelease = () => {
        clearTimeout(exampleDockMoveTimer);
        exampleDockMoveTimer = setTimeout(() => {
            if (!exampleWindow || !mainWindow) return;
            if (!exampleDockLastOverlap || !exampleWindowActiveRef || !exampleWindowActiveRef.id) return;
            if (exampleDockingInProgress) return;
            exampleDockingInProgress = true;
            try {
                if (mainWindow && mainWindow.webContents) {
                    emitDockPreview(mainWindow, {
                        kind: exampleWindowActiveRef.kind,
                        id: exampleWindowActiveRef.id,
                        active: false
                    });
                    emitDocTabOpen(mainWindow, exampleWindowActiveRef);
                }
                if (exampleWindow) exampleWindow.close();
            } finally {
                exampleDockingInProgress = false;
            }
        }, 180);
    };
    exampleWindow.on('move', () => {
        updateDockPreview();
        tryDockOnRelease();
    });
    exampleWindow.on('closed', () => {
        exampleWindowActiveRef = null;
        exampleDockPreviewActive = false;
        exampleDockLastOverlap = false;
        clearTimeout(exampleDockMoveTimer);
        if (mainWindow && mainWindow.webContents) {
            emitDockPreview(mainWindow, { kind: null, id: null, active: false });
        }
        exampleWindow = null;
    });
}

// Allow renderer tabs to be popped out into a dedicated docs window.
ipcMain.on('undock-doc-tab', (_event, payload = {}) => {
    const request = normalizeDocRequest(payload.kind || 'example', payload.id);
    if (request) openExampleWindow(request);
});
// Keep main process updated with the docs window's active selection for docking.
ipcMain.on('doc-active-ref', (_event, payload) => {
    const request = normalizeDocRequest(payload);
    exampleWindowActiveRef = request;
    if (exampleDockPreviewActive && mainWindow && mainWindow.webContents) {
        emitDockPreview(mainWindow, {
            kind: request ? request.kind : null,
            id: request ? request.id : null,
            active: !!(request && request.id)
        });
    }
});

ipcMain.on('example-active-id', (_event, { id } = {}) => {
    if (!id) {
        exampleWindowActiveRef = null;
        return;
    }
    exampleWindowActiveRef = { kind: 'example', id: String(id) };
    if (exampleDockPreviewActive && mainWindow && mainWindow.webContents) {
        emitDockPreview(mainWindow, {
            kind: 'example',
            id: String(id),
            active: true
        });
    }
});

// Load a dashboard JSON from a path into the main window Freeboard instance.
ipcMain.handle('load-dashboard-from-path', async (_event, { dashboardPath } = {}) => {
    if (!mainWindow || !dashboardPath) return { ok: false, error: 'Missing dashboard path or main window.' };
    try {
        mainWindow.webContents.send('load-dashboard-from-path', { dashboardPath });
        return { ok: true };
    } catch (err) {
        return { ok: false, error: err?.message || String(err) };
    }
});

app.whenReady().then(createWindow);
// Send each port's registered shutdown command so boards are not left running
// unattended after the app closes.  Ports with no registered command are skipped.
async function sendIdleToAllPorts() {
    const writes = [];
    for (const [path, port] of openPorts) {
        if (!port || !port.isOpen) continue;
        const cmd = safetyCommands.get(path);
        if (!cmd) continue;
        const fullCmd = cmd + '\r\n';
        writes.push(new Promise(resolve => {
            port.write(fullCmd, err => {
                if (err) { resolve(); return; }
                port.drain(() => resolve());
            });
        }));
    }
    // Cap the wait at 1 second so a dead port never blocks the shutdown.
    await Promise.race([
        Promise.all(writes),
        new Promise(resolve => setTimeout(resolve, 1000))
    ]);
}

// Reset USB devices for all currently-open serial ports.
// Uses SerialPort.list() to resolve VID/PID, then calls the WebUSB reset()
// method (open → reset → close).  Caps at 2 s so a failed reset never
// blocks shutdown.  Works cross-platform via libusb (Linux, macOS, Windows).
async function resetUsbForOpenPorts() {
    if (openPorts.size === 0) return;
    let allPorts;
    try {
        allPorts = await SerialPort.list();
    } catch (e) {
        console.error('USB reset: could not list ports:', e);
        return;
    }
    const resets = [];
    for (const [portPath] of openPorts) {
        const info = allPorts.find(p => p.path === portPath);
        if (!info || !info.vendorId || !info.productId) continue;
        const vid = parseInt(info.vendorId, 16);
        const pid = parseInt(info.productId, 16);
        resets.push((async () => {
            try {
                const device = await usbInstance.findDeviceByIds(vid, pid);
                if (!device) return;
                await device.open();
                await device.reset();
                await device.close();
                console.log(`USB reset OK: ${portPath} (${info.vendorId}:${info.productId})`);
            } catch (e) {
                console.error(`USB reset failed for ${portPath}:`, e.message);
            }
        })());
    }
    await Promise.race([
        Promise.all(resets),
        new Promise(resolve => setTimeout(resolve, 2000))
    ]);
}

let _safetyShutdownDone = false;
app.on('before-quit', async (event) => {
    cancelRunningFirmwareBuild('app-quit');
    if (_safetyShutdownDone) return;
    event.preventDefault();
    _safetyShutdownDone = true;
    try {
        await sendIdleToAllPorts();
    } catch (e) {
        console.error('Safety shutdown failed:', e);
    }
    try {
        await resetUsbForOpenPorts();
    } catch (e) {
        console.error('USB reset failed:', e);
    }
    app.quit();
});

// 🔌 List serial ports
ipcMain.handle('get-serial-ports', async () => {
	const ports = await SerialPort.list();
	return ports.map(port => {
		const vid = String(port.vendorId || '').toLowerCase();
		const pid = String(port.productId || '').toLowerCase();
		return {
			name: port.path,
			value: port.path,
			path: port.path,
			vendorId: port.vendorId || null,
			productId: port.productId || null,
			manufacturer: port.manufacturer || null,
			serialNumber: port.serialNumber || null,
			isOwntech: vid === '2fe3' && pid === '0100',
		};
	});
});



// 🚪 Open serial port with tracking and buffer setup
async function openSerialPortInternal({ path, baudRate, separator, eol, type = 'serialport_datasource' }) {
        if (!path) {
                throw new Error('Serial port path is required');
        }
        emitActivity({ id: 'serial:open', title: path, state: 'start', label: 'Open serial port' });
        const decodedEol = decodeEolToken(eol);
        parserSettings.set(path, {
                separator: separator || ":",
                eol: decodedEol
        });
        if (isSerialLocked(path)) {
                const lock = serialLocks.get(path);
                const reason = lock && lock.reason ? lock.reason : 'locked';
                console.warn(`Port ${path} is locked (${reason}).`);
                emitActivity({ id: 'serial:open', title: path, state: 'error', label: 'Open serial port', detail: `locked (${reason})` });
                return;
        }
        if (openPorts.has(path)) {
                const existing = openPorts.get(path);
                if (existing && existing.isOpen) {
                        console.warn(`Port ${path} is already open.`);
                        // ensure buffers for this datasource type exist
                        const key = dsKey(path, type);
                        if (!headerBuffers.has(key)) headerBuffers.set(key, []);
                        if (!colorBuffers.has(key)) colorBuffers.set(key, []);
                        if (type === 'fast_frame_datasource' && !fastStatus.has(path)) {
                                setFastStatus(path, { state: 'idle', message: 'Fast frame port ready', completedAt: null, datasetPoints: 0 });
                        }
                        emitActivity({ id: 'serial:open', title: path, state: 'done', label: 'Serial already open' });
                        return;
                }
                // Stale entry: in the map but not open (failed open left it behind). Remove
                // and fall through so a fresh open is attempted.
                console.warn(`Port ${path} has a stale non-open entry — removing and retrying open.`);
                openPorts.delete(path);
        }

        // Persist settings so a later auto-reopen uses the same config.
        portSettings.set(path, {
            baudRate: parseInt(baudRate),
            separator: separator || ":",
            eol: decodedEol,
            type
        });

	const port = new SerialPort({
		path,
		baudRate: parseInt(baudRate),
		autoOpen: false
	});

        port.open(err => {
                if (err) {
                        console.error("Serial open error:", err.message);
                        // Remove the stale map entry — openPorts.set() runs synchronously
                        // below before this callback fires, so if open fails the map holds
                        // a non-open port object that blocks every future open attempt.
                        openPorts.delete(path);
                        emitActivity({ id: 'serial:open', title: path, state: 'error', label: 'Open serial port', detail: err.message });
                        return;
                }
                console.log("✅ Serial port opened:", path);
                emitActivity({ id: 'serial:open', title: path, state: 'done', label: 'Serial opened' });
        });

	let rawBuffer = "";

        terminalBuffers.set(path, []);
        serialBuffers.set(path, []);
        headerBuffers.set(dsKey(path, type), []);
        colorBuffers.set(dsKey(path, type), []);
        fastStates.set(path, { state: FAST_IDLE, header: null, idx: null, data: [] });
        fastBuffers.delete(path);
        if (type === 'fast_frame_datasource') {
                setFastStatus(path, { state: 'idle', message: 'Fast frame port ready', completedAt: null, datasetPoints: 0 });
        }

        port.on("data", chunk => {
                        const parser = parserSettings.get(path) || { separator: ':', eol: '\n' };
                        rawBuffer += chunk.toString();
                        const lines = rawBuffer.split(parser.eol);
                        rawBuffer = lines.pop(); // keep the last (possibly incomplete) line
                        rawBufferSizes.set(path, rawBuffer.length);
                        const termBuf = terminalBuffers.get(path) || [];
                        for (const line of lines) {
                                        const parsed = parseLine(line, parser.separator);
                                        if (parsed.length) addToBuffer(path, parsed);
                                        handleFastLine(path, line);
                                        termBuf.push(line);
                                        if (termBuf.length > MAX_TERMINAL_LINES) termBuf.shift();
                        }
                        terminalBuffers.set(path, termBuf);
        });

	port.on("error", err => {
		console.error("Serial port error:", err.message);
	});

        port.on("close", () => {
                        console.log(`🔌 Serial port ${path} closed.`);
                        openPorts.delete(path);
                        safetyCommands.delete(path);
                        terminalBuffers.delete(path);
                        serialBuffers.delete(path);
                        for (const key of [...headerBuffers.keys()]) {
                            if (key.startsWith(`${path}||`)) headerBuffers.delete(key);
                        }
                        for (const key of [...colorBuffers.keys()]) {
                            if (key.startsWith(`${path}||`)) colorBuffers.delete(key);
                        }
                        fastStates.delete(path);
                        fastBuffers.delete(path);
                        fastStatus.delete(path);
                        parserSettings.delete(path);
                        rawBufferSizes.delete(path);
                        emitActivity({ id: 'serial:close', title: path, state: 'done', label: 'Serial closed' });
        });

	openPorts.set(path, port);
}

ipcMain.handle("open-serial-port", async (_event, payload) => {
        return openSerialPortInternal(payload || {});
});

// 📥 Renderer pulls latest parsed data
ipcMain.handle("get-serial-buffer", (event, { path }) => {
        trackIpcCall('get-serial-buffer');
        const buf = serialBuffers.get(path) || [];
        return buf.length > 0 ? buf[buf.length - 1] : [];
});

ipcMain.handle('get-fast-dataset', (event, { path }) => {
    trackIpcCall('get-fast-dataset');
    return fastBuffers.get(path) || null;
});

// Allow a regular serialport_datasource port to participate in fast-frame capture.
// Initialises fastStatus so that write-serial-port tracks the next trigger and
// handleFastLine (which already runs on every port) can complete the cycle.
ipcMain.handle('enable-fast-capture', (_event, { path }) => {
    if (!fastStatus.has(path)) {
        setFastStatus(path, { state: 'idle', message: 'Scope capture ready', completedAt: null, datasetPoints: 0 });
    }
    return true;
});

ipcMain.handle('get-fast-frame-status', (_event, { path }) => {
    trackIpcCall('get-fast-frame-status');
    return fastStatus.get(path) || {
        state: 'idle',
        message: 'No acquisition yet',
        updatedAt: Date.now(),
        completedAt: null,
        datasetPoints: 0,
        acquisitionId: 0
    };
});

// 📄 Get terminal lines for a port
ipcMain.handle("get-terminal-buffer", (event, { path }) => {
        trackIpcCall('get-terminal-buffer');
        return terminalBuffers.get(path) || [];
});

// 🏷️ Get/set headers for a port
ipcMain.handle('get-serial-headers', (_event, { path, type = 'serialport_datasource' }) => {
    trackIpcCall('get-serial-headers');
    return headerBuffers.get(dsKey(path, type)) || [];
});

ipcMain.handle('set-serial-headers', (_event, { path, headers, type = 'serialport_datasource' }) => {
    if (!Array.isArray(headers)) headers = [];
    headerBuffers.set(dsKey(path, type), headers);
    return 'ok';
});

// 🛑 Register/clear the command sent to a board when the app quits.
ipcMain.handle('register-safety-command', (_event, { path, command }) => {
    if (path && command && command.trim()) safetyCommands.set(path, command.trim());
    else if (path) safetyCommands.delete(path);
    return 'ok';
});

// 🎨 Get/set colors for a port
ipcMain.handle('get-serial-colors', (_event, { path, type = 'serialport_datasource' }) => {
    trackIpcCall('get-serial-colors');
    return colorBuffers.get(dsKey(path, type)) || [];
});

ipcMain.handle('set-serial-colors', (_event, { path, colors, type = 'serialport_datasource' }) => {
    if (!Array.isArray(colors)) colors = [];
    colorBuffers.set(dsKey(path, type), colors);
    return 'ok';
});


// ❌ Close port
ipcMain.handle("close-serial-port", async (event, { path }) => {
	emitActivity({ id: 'serial:close', title: path, state: 'start', label: 'Close serial port' });
	const port = openPorts.get(path);
	if (port && port.isOpen) {
			return new Promise((resolve, reject) => {
					port.close(err => {
							if (err) return reject(err.message);
                                                        openPorts.delete(path);
                                                        terminalBuffers.delete(path);
                                                        serialBuffers.delete(path);
                                                        for (const key of [...headerBuffers.keys()]) {
                                                            if (key.startsWith(`${path}||`)) headerBuffers.delete(key);
                                                        }
                                                        for (const key of [...colorBuffers.keys()]) {
                                                            if (key.startsWith(`${path}||`)) colorBuffers.delete(key);
                                                        }
                                                        fastStates.delete(path);
                                                        fastBuffers.delete(path);
                                                        emitActivity({ id: 'serial:close', title: path, state: 'done', label: 'Serial closed' });
                                                        resolve("closed");
                                        });
                        });
	} else {
			emitActivity({ id: 'serial:close', title: path, state: 'done', label: 'Serial already closed' });
			return "not open";
	}
});

// 🔁 Release a serial port temporarily and optionally auto-reopen after a delay.
ipcMain.handle("release-serial-port", async (_event, { path, reopen = true, reopenDelayMs = 0 } = {}) => {
        if (!path) throw new Error("path required");
        const port = openPorts.get(path);
        if (!port || !port.isOpen) {
                return { released: false, reason: "not-open" };
        }
        const settings = portSettings.get(path) || null;
        // Close now to free the COM port for external flash tools.
        await new Promise((resolve) => port.close(() => resolve()));
        // Clear any prior pending reopen.
        const pending = pendingReopens.get(path);
        if (pending && pending.timer) {
                clearTimeout(pending.timer);
        }
        pendingReopens.delete(path);
        if (reopen && settings) {
                if (reopenDelayMs > 0) {
                        const timer = setTimeout(() => {
                                // Fire-and-forget reopen using the last-known settings.
                                openSerialPortInternal({
                                        path,
                                        baudRate: settings.baudRate,
                                        separator: settings.separator,
                                        eol: settings.eol,
                                        type: settings.type
                                });
                        }, reopenDelayMs);
                        pendingReopens.set(path, { timer, settings });
                } else {
                        await openSerialPortInternal({
                                path,
                                baudRate: settings.baudRate,
                                separator: settings.separator,
                                eol: settings.eol,
                                type: settings.type
                        });
                }
        }
        return { released: true, reopenScheduled: Boolean(reopen && settings && reopenDelayMs > 0) };
});

// 🔁 Explicitly reopen a port that was previously released.
ipcMain.handle("reopen-serial-port", async (_event, { path } = {}) => {
        if (!path) throw new Error("path required");
        const settings = portSettings.get(path);
        if (!settings) return { reopened: false, reason: "no-settings" };
        const pending = pendingReopens.get(path);
        if (pending && pending.timer) clearTimeout(pending.timer);
        pendingReopens.delete(path);
        await openSerialPortInternal({
                path,
                baudRate: settings.baudRate,
                separator: settings.separator,
                eol: settings.eol,
                type: settings.type
        });
        return { reopened: true };
});

// ➡️ Write data to an open serial port
ipcMain.handle("write-serial-port", async (event, { path, data }) => {
        // Pick specified port or default to the first one
        const targetPort = path ? openPorts.get(path) : openPorts.values().next().value;
        if (targetPort && targetPort.isOpen) {
                if (path && fastStatus.has(path)) {
                        const nextAcquisitionId = (fastAcquisitionSeq.get(path) || 0) + 1;
                        fastAcquisitionSeq.set(path, nextAcquisitionId);
                        setFastStatus(path, {
                                state: 'awaiting_record',
                                message: 'Trigger sent, waiting for fast frame',
                                completedAt: null,
                                datasetPoints: 0,
                                acquisitionId: nextAcquisitionId
                        });
                }
                return new Promise((resolve, reject) => {
                        targetPort.write(data, err => {
                                if (err) return reject(err.message);
                                targetPort.drain(drainErr => {
                                        if (drainErr) return reject(drainErr.message);
                                        resolve("written");
                                });
                        });
                });
        } else {
                console.error(`write-serial-port: cannot write — path=${path}, found=${!!targetPort}, isOpen=${targetPort ? targetPort.isOpen : 'N/A'}, openPorts=[${[...openPorts.keys()].join(', ')}]`);
                throw new Error("No open serial port");
        }
});

// 📂 Start CSV recording for a given port
ipcMain.handle('start-csv-record', async (event, { path, filePath, separator, eol, order = 'old', addHeader = true, timestampMode = 'none', type = 'serialport_datasource' }) => {
        emitActivity({ id: 'csv:record', title: path, state: 'start', label: 'Start CSV recording', detail: filePath });
        const port = openPorts.get(path);
        if (!port) {
                const err = 'port not open';
                emitActivity({ id: 'csv:record', title: path, state: 'error', label: 'Start CSV recording', detail: err });
                throw new Error(err);
        }
        if (activeRecordings.has(path)) {
                emitActivity({ id: 'csv:record', title: path, state: 'done', label: 'Already recording' });
                return 'already recording';
        }
        const sep = separator || ',';
        const eolStr = decodeEolToken(eol);
        const headers = headerBuffers.get(dsKey(path, type)) || [];
        const recording = {
                order,
                addHeader,
                timestampMode,
                lines: [],
                headerLine: null,
                stream: null,
                listener: null,
                startTime: Date.now(),
                headerWritten: false,
                filePath,
                sep,
                eolStr,
                headers
        };

        if (order === 'old') {
                recording.stream = fs.createWriteStream(filePath, { flags: 'a' });
        }

        let buffer = '';
        const listener = chunk => {
                buffer += chunk.toString();
                const lines = buffer.split(eolStr);
                buffer = lines.pop();
                for (const line of lines) {
                        const values = parseLineCustom(line, sep);
                        if (!values.length) continue;

                        if (addHeader && !recording.headerWritten) {
                                const header = [];
                                if (timestampMode !== 'none') {
                                        header.push(timestampMode === 'relative' ? 'time_ms' : 'timestamp');
                                }
                                for (let i = 0; i < values.length; i++) {
                                        const label = recording.headers[i] || `ch${i + 1}`;
                                        header.push(label);
                                }
                                const headerLine = header.join(',');
                                if (order === 'old') {
                                        recording.stream.write(headerLine + '\n');
                                } else {
                                        recording.headerLine = headerLine;
                                }
                                recording.headerWritten = true;
                        }

                        const row = [];
                        if (timestampMode === 'relative') {
                                row.push(String(Date.now() - recording.startTime));
                        } else if (timestampMode === 'absolute') {
                                row.push(new Date().toISOString());
                        }
                        row.push(...values);

                        const lineStr = row.join(',');
                        if (order === 'old') {
                                recording.stream.write(lineStr + '\n');
                        } else {
                                recording.lines.unshift(lineStr);
						}
                }
        };
		recording.listener = listener;
        port.on('data', listener);
        activeRecordings.set(path, recording);
        emitActivity({ id: 'csv:record', title: path, state: 'done', label: 'CSV recording started' });
        return 'started';
});

// 🛑 Stop CSV recording for a port
ipcMain.handle('stop-csv-record', async (event, { path }) => {
        emitActivity({ id: 'csv:record', title: path, state: 'start', label: 'Stop CSV recording' });
        const rec = activeRecordings.get(path);
        if (!rec) {
                emitActivity({ id: 'csv:record', title: path, state: 'done', label: 'Not recording' });
                return 'not recording';
        }
        const port = openPorts.get(path);
        if (port) port.off('data', rec.listener);

        if (rec.order === 'old') {
                await new Promise(res => rec.stream.end(res));
        } else {
                const outLines = [];
                if (rec.headerLine) outLines.push(rec.headerLine);
                outLines.push(...rec.lines);
                const content = outLines.join('\n') + '\n';
                await fs.promises.writeFile(rec.filePath, content);
        }
        activeRecordings.delete(path);
        emitActivity({ id: 'csv:record', title: path, state: 'done', label: 'CSV recording stopped' });
        return 'stopped';
});

// 💾 Save the latest fast frame dataset to CSV
ipcMain.handle('save-fast-csv', async (event, { path, filePath, separator, eol, addHeader = true, timestampMode = 'none', useTimestampedFileName = false }) => {
        emitActivity({ id: 'csv:save-fast', title: path, state: 'start', label: 'Save fast dataset', detail: filePath });
        const dataset = fastBuffers.get(path);
        if (!dataset || !Array.isArray(dataset.series)) {
                const err = 'no dataset';
                emitActivity({ id: 'csv:save-fast', title: path, state: 'error', label: 'Save fast dataset', detail: err });
                throw new Error(err);
        }
        const resolvedFilePath = useTimestampedFileName
            ? resolveTimestampedCsvPath(filePath, acquireDir)
            : (path.isAbsolute(filePath) ? filePath : path.join(acquireDir, filePath));
        const headers = headerBuffers.get(dsKey(path, 'fast_frame_datasource')) || [];
        const sep = separator || ',';
        const eolStr = decodeEolToken(eol);
        const out = [];
        if (addHeader) {
                const h = [];
                if (timestampMode !== 'none') {
                        h.push(timestampMode === 'relative' ? 'time_ms' : 'timestamp');
                }
                for (let i = 0; i < dataset.series.length; i++) {
                        h.push(headers[i] || `ch${i + 1}`);
                }
                out.push(h.join(sep));
        }
        for (let i = 0; i < dataset.timestamps.length; i++) {
                const row = [];
                if (timestampMode === 'relative') {
                        row.push(String(dataset.timestamps[i]));
                } else if (timestampMode === 'absolute') {
                        row.push(new Date().toISOString());
                }
                for (let j = 0; j < dataset.series.length; j++) {
                        row.push(String(dataset.series[j][i]));
                }
                out.push(row.join(sep));
        }
        const content = out.join(eolStr) + eolStr;
        await fs.promises.writeFile(resolvedFilePath, content);
        setFastStatus(path, {
                state: 'saved',
                message: 'Fast frame saved to CSV',
                datasetPoints: Array.isArray(dataset.timestamps) ? dataset.timestamps.length : 0,
                filePath: resolvedFilePath
        });
        emitActivity({ id: 'csv:save-fast', title: path, state: 'done', label: 'Saved fast dataset', detail: resolvedFilePath });
        return { status: 'saved', filePath: resolvedFilePath };
});

// 📂 Open a dialog to choose a firmware binary file
ipcMain.handle('choose-firmware-file', async () => {
    const defaultFirmwareDir = path.join(__dirname, 'dashboard', 'binaries');
    const { canceled, filePaths } = await dialog.showOpenDialog(mainWindow, {
        defaultPath: defaultFirmwareDir,
        properties: ['openFile'],
        filters: [{ name: 'Firmware', extensions: ['bin'] }]
    });
    if (canceled || filePaths.length === 0) {
        return null;
    }
    return filePaths[0];
});

// 🔥 Flash firmware to a board over serial
ipcMain.handle('start-flash', async (event, { comPort, firmwarePath, mcumgrPath: userPath }) => {
    const flashId = ++activeFlashId;
    emitActivity({ id: 'dfu:serial', title: comPort, state: 'start', label: 'Serial DFU', detail: firmwarePath });
    // Prevent background serial datasources from reopening the port during flashing.
    lockSerialPort(comPort, 'flash', 60000);
    activeFlashSender = event.sender;
    activeFlashPort = comPort;
    activeFlashCanceled = false;
    const resolvedMcumgr = resolveMcumgrPath(userPath);
    if (resolvedMcumgr !== 'mcumgr' && !fs.existsSync(resolvedMcumgr)) {
        const msg = `Error: mcumgr not found at ${resolvedMcumgr}`;
        event.sender.send('flash-progress', msg);
        emitActivity({ id: 'dfu:serial', title: comPort, state: 'error', label: 'Serial DFU', detail: msg });
        unlockSerialPort(comPort);
        if (activeFlashId === flashId) {
            activeFlashSender = null;
            activeFlashPort = null;
            activeFlashCanceled = false;
        }
        event.sender.send('flash-complete');
        return 'error';
    }
    const existing = openPorts.get(comPort);
    if (existing && existing.isOpen) {
        await new Promise(res => existing.close(err => {
            if (err) {
                console.error('Error closing port before flash:', err.message);
            }
            res();
        }));
    }

    return new Promise(resolve => {
        flashFirmware(
            { comPort, firmwarePath, mcumgrPath: resolvedMcumgr },
            msg => {
                const m = String(msg);
                event.sender.send('flash-progress', m);
                if (m.toLowerCase().includes('error')) {
                    emitActivity({ id: 'dfu:serial', title: comPort, state: 'error', label: 'Serial DFU', detail: m });
                }
            },
            () => {
                if (activeFlashId !== flashId) {
                    unlockSerialPort(comPort);
                    return;
                }
                if (activeFlashSender && !activeFlashSender.isDestroyed()) {
                    activeFlashSender.send('flash-complete');
                }
                if (activeFlashCanceled) {
                    emitActivity({ id: 'dfu:serial', title: comPort, state: 'done', label: 'Serial DFU canceled' });
                } else {
                    emitActivity({ id: 'dfu:serial', title: comPort, state: 'done', label: 'Serial DFU complete' });
                }
                unlockSerialPort(comPort);
                activeFlashSender = null;
                activeFlashPort = null;
                activeFlashCanceled = false;
            }
        );
        resolve();
    });
});

// ❌ Cancel flashing
ipcMain.on('cancel-flash', () => {
    activeFlashCanceled = true;
    cancelFlash();
    if (activeFlashSender && !activeFlashSender.isDestroyed()) {
        activeFlashSender.send('flash-complete');
    }
    if (activeFlashPort) {
        unlockSerialPort(activeFlashPort);
    }
    activeFlashSender = null;
    activeFlashPort = null;
});


// 🧹 Flush buffers for a serial port
ipcMain.handle('flush-serial-buffers', async (_event, { path }) => {
    terminalBuffers.set(path, []);
    serialBuffers.set(path, []);
    for (const key of [...headerBuffers.keys()]) {
        if (key.startsWith(`${path}||`)) headerBuffers.delete(key);
    }
    for (const key of [...colorBuffers.keys()]) {
        if (key.startsWith(`${path}||`)) colorBuffers.delete(key);
    }
    fastStates.delete(path);
    fastBuffers.delete(path);
    fastStatus.delete(path);
    fastAcquisitionSeq.delete(path);
    return 'flushed';
});

// ❓ Check if a serial port is open
ipcMain.handle('is-serial-port-open', async (_event, { path }) => {
    const port = openPorts.get(path);
    return port ? port.isOpen : false;
});
