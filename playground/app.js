const MONACO_VERSION = '0.45.0';
const MONACO_BASE = `https://cdnjs.cloudflare.com/ajax/libs/monaco-editor/${MONACO_VERSION}/min/vs`;
const DEFAULT_SNIPPET = `(* Edit the buffer and press the button to refresh > results. *)
let id = fun x -> x

id unit
> unit`;
const EXAMPLE_PATH = '../tests/mox/editor.mox';
const EXAMPLE_CACHE_BUSTER = Date.now().toString(36);
const EXAMPLE_URL = `${EXAMPLE_PATH}?cache=${EXAMPLE_CACHE_BUSTER}`;
const KEY_HINTS = {
  mac: '⌘ + Enter',
  default: 'Ctrl + Enter'
};

const statusEl = document.getElementById('status');
const runButton = document.getElementById('process');
const editorContainer = document.getElementById('editor');
const shortcutHintEl = document.getElementById('shortcut-hint');
let statusFadeHandle = null;
let processingFlashHandle = null;
let shortcutHoldActive = false;

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

function clearStatusFade() {
  if (statusFadeHandle !== null) {
    window.clearTimeout(statusFadeHandle);
    statusFadeHandle = null;
  }
}

function scheduleStatusFade(delay = 2500) {
  clearStatusFade();
  statusFadeHandle = window.setTimeout(() => {
    statusEl.classList.add('dimmed');
  }, delay);
}

function detectPlatformHint() {
  const platform = navigator?.platform || navigator?.userAgent || '';
  const isMac = /mac/i.test(platform);
  return isMac ? KEY_HINTS.mac : KEY_HINTS.default;
}

function setStatus(message, tone = 'info', { autoFade = false } = {}) {
  statusEl.textContent = message;
  statusEl.classList.remove('ready', 'error', 'busy', 'dimmed');
  if (tone === 'ready' || tone === 'error' || tone === 'busy') {
    statusEl.classList.add(tone);
  }
  if (autoFade) {
    scheduleStatusFade();
  } else {
    clearStatusFade();
  }
}

function loadMonaco() {
  return new Promise((resolve, reject) => {
    if (typeof require === 'undefined') {
      reject(new Error('Monaco loader is not available.'));
      return;
    }

    require.config({ paths: { vs: MONACO_BASE } });
    require(['vs/editor/editor.main'], () => {
      resolve(window.monaco);
    });
  });
}

async function waitForPlayground(timeoutMs = 20000) {
  if (window.MoxPlayground?.process) {
    return window.MoxPlayground;
  }

  const started = performance.now();
  while (performance.now() - started < timeoutMs) {
    if (window.MoxPlayground?.process) {
      return window.MoxPlayground;
    }
    await sleep(50);
  }
  throw new Error('Timed out waiting for the WebAssembly bundle to load.');
}

function injectScriptOnce(src) {
  return new Promise((resolve, reject) => {
    const targetHref = new URL(src, document.baseURI).href;
    const existing = Array.from(document.getElementsByTagName('script')).find((el) => {
      try {
        return el.src === targetHref;
      } catch (_err) {
        return false;
      }
    });
    if (existing) {
      if (window.MoxPlayground?.process) {
        resolve(src);
        return;
      }
    }
    const script = document.createElement('script');
    script.defer = true;
    script.src = src;
    script.onload = () => resolve(src);
    script.onerror = () => reject(new Error(`Failed to load ${src}`));
    document.head.appendChild(script);
  });
}

async function ensurePlaygroundLoader() {
  if (window.MoxPlayground?.process) {
    return;
  }
  const pathname = window.location?.pathname || '';
  const isNestedPlayground = pathname.includes('/playground');
  const relRoot = isNestedPlayground ? '..' : '.';
  const candidates = [
    `${relRoot}/_build/default/playground/mox_playground.bc.wasm.js`,
    '/_build/default/playground/mox_playground.bc.wasm.js',
    './mox_playground.bc.wasm.js',
    `${relRoot}/playground/mox_playground.bc.wasm.js`
  ];
  let lastError = null;
  for (const src of candidates) {
    try {
      await injectScriptOnce(src);
      if (window.MoxPlayground?.process) {
        return;
      }
    } catch (err) {
      lastError = err;
    }
  }
  const message = lastError?.message || 'Unable to load WebAssembly bundle.';
  throw new Error(message);
}

function registerLanguage(monaco) {
  monaco.languages.register({ id: 'mox' });

  const MODE_WORDS = [
    'unique',
    'aliased',
    'contended',
    'shared',
    'uncontended',
    'local',
    'regional',
    'global',
    'portable',
    'nonportable',
    'once',
    'many',
    'never'
  ];

  monaco.languages.setMonarchTokensProvider('mox', {
    defaultToken: 'identifier',
    tokenPostfix: '.mox',
    keywords: [
      'let',
      'let!',
      'in',
      'borrow',
      'for',
      'fun',
      'match',
      'match!',
      'with',
      'ref',
      'fork',
      'left',
      'right',
      'absurd',
      'region',
      'unit'
    ],
    builtins: ['empty', 'true', 'false'],
    modeWords: MODE_WORDS,
    brackets: [
      { open: '(', close: ')', token: 'delimiter.parenthesis' },
      { open: '[', close: ']', token: 'delimiter.bracket' },
      { open: '{', close: '}', token: 'delimiter.brace' }
    ],
    tokenizer: {
      root: [
        [/^\s*>.*$/, 'annotation'],
        [/\blet!|\bmatch!/, 'keyword'],
        [/(\(\*).*(\*\))/, ['comment', 'comment']],
        [/\(\*/, 'comment', '@comment'],
        [/"([^"\\]|\\.)*"/, 'string'],
        [/\b\d+\b/, 'number'],
        [/\[(?=[^\]]*(?:u=|a=|p=|l=|c=))/, { token: 'annotation', next: '@modeAnn' }],
        [/[a-zA-Z_][\w']*/, {
          cases: {
            '@keywords': 'keyword',
            '@builtins': 'constant',
            '@modeWords': 'type',
            '@default': 'identifier'
          }
        }],
        [/[{}()\[\]]/, '@brackets'],
        [/(?:->|=>|\||\+|\-|\*|=|:|,|!|\$)/, 'operator'],
        [/[,]/, 'delimiter'],
        [/\s+/, 'white']
      ],
      comment: [
        [/[^*(]+/, 'comment'],
        [/\*\)/, 'comment', '@pop'],
        [/\(\*/, 'comment', '@push'],
        [/[*()]/, 'comment']
      ],
      modeAnn: [
        [/\]/, { token: 'annotation', next: '@pop' }],
        [/\b(?:unique|aliased|contended|shared|uncontended|local|regional|global|portable|nonportable|once|many|never)\b/, 'type'],
        [/[=,]/, 'operator'],
        [/[^\]\s]+/, 'annotation'],
        [/\s+/, 'white']
      ]
    }
  });

  monaco.editor.defineTheme('mox-dark', {
    base: 'vs-dark',
    inherit: true,
    rules: [
      { token: 'annotation', foreground: 'a6accd', fontStyle: 'italic' },
      { token: 'comment', foreground: '5c6370' },
      { token: 'keyword', foreground: 'c792ea' },
      { token: 'operator', foreground: '89ddff' },
      { token: 'number', foreground: 'f78c6c' },
      { token: 'string', foreground: 'c3e88d' }
    ],
    colors: {
      'editor.background': '#0f111a'
    }
  });
}

function createEditor(monaco, initialValue) {
  registerLanguage(monaco);
  const editor = monaco.editor.create(document.getElementById('editor'), {
    value: initialValue,
    language: 'mox',
    automaticLayout: true,
    minimap: { enabled: false },
    theme: 'mox-dark',
    fontFamily: 'JetBrains Mono, Fira Code, SFMono-Regular, Menlo, monospace',
    fontSize: 15,
    scrollBeyondLastLine: false,
    smoothScrolling: true
  });
  return editor;
}

function setEditorProcessingState(active) {
  if (!editorContainer) {
    return;
  }
  editorContainer.classList.toggle('processing', active);
}

function pulseEditorSurface() {
  setEditorProcessingState(true);
  if (processingFlashHandle) {
    window.clearTimeout(processingFlashHandle);
  }
  processingFlashHandle = window.setTimeout(() => {
    processingFlashHandle = null;
    if (!shortcutHoldActive) {
      setEditorProcessingState(false);
    }
  }, 120);
}

function processBuffer(editor, playground) {
  setStatus('Checking buffer…', 'busy');
  pulseEditorSurface();
  runButton.disabled = true;
  requestAnimationFrame(() => {
    try {
      const currentValue = editor.getValue();
      const viewState = editor.saveViewState();
      const result = playground.process(currentValue);
      if (result?.ok && result.output) {
        if (currentValue !== result.output) {
          editor.pushUndoStop();
          editor.setValue(result.output);
          if (viewState) {
            editor.restoreViewState(viewState);
          }
          editor.focus();
        }
        setStatus('Results refreshed.', 'ready', { autoFade: true });
      } else {
        const message = result?.error || 'Unknown error';
        setStatus(`Typechecker error: ${message}`, 'error');
      }
    } catch (err) {
      setStatus(`Runtime failure: ${err.message}`, 'error');
    } finally {
      runButton.disabled = false;
    }
  });
}

function wireShortcuts(editor, monaco, playground) {
  runButton.addEventListener('click', () => processBuffer(editor, playground));
  editor.addCommand(monaco.KeyMod.CtrlCmd | monaco.KeyCode.Enter, () => {
    processBuffer(editor, playground);
  });
  window.addEventListener('keydown', (event) => {
    if ((event.metaKey || event.ctrlKey) && event.key === 'Enter') {
      shortcutHoldActive = true;
      setEditorProcessingState(true);
    }
  });
  window.addEventListener('keyup', (event) => {
    if (event.key === 'Enter') {
      shortcutHoldActive = false;
      if (!processingFlashHandle) {
        setEditorProcessingState(false);
      }
    }
  });
}

async function loadEditorExamples() {
  if (!window.fetch) {
    return { text: DEFAULT_SNIPPET, source: 'default snippet' };
  }
  try {
    const response = await fetch(EXAMPLE_URL, { cache: 'no-store' });
    if (!response.ok) {
      throw new Error(`HTTP ${response.status}`);
    }
    const text = await response.text();
    const finalText = text.trim().length > 0 ? text : DEFAULT_SNIPPET;
    const source = finalText === text ? EXAMPLE_PATH : 'default snippet';
    return { text: finalText, source };
  } catch (err) {
    console.warn('Falling back to default snippet:', err);
    return { text: DEFAULT_SNIPPET, source: 'default snippet' };
  }
}

async function boot() {
  try {
    const monacoReady = loadMonaco();
    await ensurePlaygroundLoader();
    const [monaco, playground, exampleBundle] = await Promise.all([
      monacoReady,
      waitForPlayground(),
      loadEditorExamples()
    ]);
    const editor = createEditor(monaco, exampleBundle.text);
    wireShortcuts(editor, monaco, playground);
    const platformHint = detectPlatformHint();
    if (shortcutHintEl) {
      shortcutHintEl.textContent = `Process buffer (${platformHint})`;
    }
    setStatus(`Ready. Press ${platformHint} to sync > results.`, 'ready');
  } catch (err) {
    setStatus(err.message || 'Failed to initialise playground.', 'error');
  }
}

boot();
