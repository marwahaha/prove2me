import {
  EditorView,
  keymap,
  showTooltip,
  StateField,
  StateEffect,
  Prec,
} from '@uiw/react-codemirror';
import type { Tooltip } from '@codemirror/view';
import { leanAbbreviations } from './leanAbbreviations';

// State for tracking active abbreviation input
interface AbbrevState {
  active: boolean;
  from: number; // position of the backslash
  prefix: string; // characters typed after backslash
}

const defaultState: AbbrevState = { active: false, from: 0, prefix: '' };

const activateAbbrev = StateEffect.define<{ from: number }>();
const updatePrefix = StateEffect.define<string>();
const deactivateAbbrev = StateEffect.define<void>();

function getMatches(prefix: string): [string, string][] {
  if (!prefix) return [];
  const results: [string, string][] = [];
  for (const [key, value] of Object.entries(leanAbbreviations)) {
    if (key.startsWith(prefix)) {
      results.push([key, value]);
    }
  }
  // Sort: exact match first, then by length, then alphabetically
  results.sort((a, b) => {
    if (a[0] === prefix) return -1;
    if (b[0] === prefix) return 1;
    return a[0].length - b[0].length || a[0].localeCompare(b[0]);
  });
  return results;
}

const abbrevField = StateField.define<AbbrevState>({
  create() {
    return defaultState;
  },
  update(state, tr) {
    for (const effect of tr.effects) {
      if (effect.is(activateAbbrev)) {
        return { active: true, from: effect.value.from, prefix: '' };
      }
      if (effect.is(updatePrefix)) {
        return { ...state, prefix: effect.value };
      }
      if (effect.is(deactivateAbbrev)) {
        return defaultState;
      }
    }
    // If the document changed but no effects from us, adjust `from` for position mapping
    if (state.active && tr.docChanged) {
      const newFrom = tr.changes.mapPos(state.from, -1);
      if (newFrom !== state.from) {
        return { ...state, from: newFrom };
      }
    }
    return state;
  },
});

// Tooltip that shows matching abbreviations
const abbrevTooltipField = StateField.define<readonly Tooltip[]>({
  create() {
    return [];
  },
  update(_, tr) {
    const abbrev = tr.state.field(abbrevField);
    if (!abbrev.active || !abbrev.prefix) return [];
    const matches = getMatches(abbrev.prefix);
    if (matches.length === 0) return [];
    return [
      {
        pos: abbrev.from,
        above: false,
        create() {
          const dom = document.createElement('div');
          dom.className = 'lean-abbrev-tooltip';
          const list = matches.slice(0, 8);
          for (const [key, value] of list) {
            const row = document.createElement('div');
            row.className = 'lean-abbrev-row';
            row.textContent = `\\${key} → ${value}`;
            dom.appendChild(row);
          }
          if (matches.length > 8) {
            const more = document.createElement('div');
            more.className = 'lean-abbrev-row lean-abbrev-more';
            more.textContent = `… ${matches.length - 8} more`;
            dom.appendChild(more);
          }
          return { dom };
        },
      },
    ];
  },
  provide(f) {
    return showTooltip.computeN([f], (state) => state.field(f));
  },
});

// Apply the top match: replace \prefix with the unicode character
function applyMatch(view: EditorView, suffix = ''): boolean {
  const abbrev = view.state.field(abbrevField);
  if (!abbrev.active || !abbrev.prefix) return false;
  const matches = getMatches(abbrev.prefix);
  if (matches.length === 0) return false;
  const [, replacement] = matches[0];
  const from = abbrev.from;
  const to = from + 1 + abbrev.prefix.length;
  view.dispatch({
    changes: { from, to, insert: replacement + suffix },
    effects: deactivateAbbrev.of(undefined),
  });
  return true;
}

const abbrevKeymap = Prec.high(
  keymap.of([
    {
      key: 'Tab',
      run(view) {
        return applyMatch(view);
      },
    },
    {
      key: 'Enter',
      run(view) {
        return applyMatch(view);
      },
    },
    {
      key: ' ',
      run(view) {
        return applyMatch(view, ' ');
      },
    },
    {
      key: 'Escape',
      run(view) {
        const abbrev = view.state.field(abbrevField);
        if (!abbrev.active) return false;
        view.dispatch({ effects: deactivateAbbrev.of(undefined) });
        return true;
      },
    },
  ]),
);

// Update listener runs AFTER the view update, so dispatch is safe here
const abbrevListener = EditorView.updateListener.of((update) => {
  if (!update.docChanged) return;

  // Skip updates that were triggered by our own effects (to avoid loops)
  for (const tr of update.transactions) {
    for (const effect of tr.effects) {
      if (
        effect.is(activateAbbrev) ||
        effect.is(deactivateAbbrev) ||
        effect.is(updatePrefix)
      ) {
        return;
      }
    }
  }

  const state = update.state.field(abbrevField);

  if (!state.active) {
    // Check if a backslash was just typed
    let backslashPos = -1;
    update.changes.iterChanges((_fromA, _toA, fromB, _toB, inserted) => {
      const text = inserted.toString();
      if (text === '\\') {
        backslashPos = fromB;
      }
    });
    if (backslashPos >= 0) {
      update.view.dispatch({
        effects: activateAbbrev.of({ from: backslashPos }),
      });
    }
    return;
  }

  // Active: re-read the text from backslash to cursor to get current prefix
  const doc = update.state.doc;
  const cursor = update.state.selection.main.head;
  const from = state.from;

  // Validate backslash is still there
  if (from >= doc.length || doc.sliceString(from, from + 1) !== '\\') {
    update.view.dispatch({ effects: deactivateAbbrev.of(undefined) });
    return;
  }

  const prefix = doc.sliceString(from + 1, cursor);

  // Deactivate on space, empty prefix after deletion, or non-abbreviation chars
  if (!prefix || /\s/.test(prefix) || /[^a-zA-Z0-9_']/.test(prefix)) {
    update.view.dispatch({ effects: deactivateAbbrev.of(undefined) });
    return;
  }

  const matches = getMatches(prefix);

  if (matches.length === 0) {
    update.view.dispatch({ effects: deactivateAbbrev.of(undefined) });
    return;
  }

  // Check for unique exact match (prefix matches exactly one entry and nothing else extends it)
  if (matches.length === 1 && matches[0][0] === prefix) {
    const [, replacement] = matches[0];
    const to = from + 1 + prefix.length;
    update.view.dispatch({
      changes: { from, to, insert: replacement },
      effects: deactivateAbbrev.of(undefined),
    });
    return;
  }

  update.view.dispatch({ effects: updatePrefix.of(prefix) });
});

// CSS for the tooltip
const abbrevTheme = EditorView.baseTheme({
  '.lean-abbrev-tooltip': {
    backgroundColor: '#fff',
    border: '1px solid #ddd',
    borderRadius: '4px',
    padding: '4px 0',
    fontSize: '13px',
    fontFamily: 'monospace',
    boxShadow: '0 2px 8px rgba(0,0,0,0.15)',
    maxHeight: '200px',
    overflowY: 'auto',
    zIndex: '100',
  },
  '.lean-abbrev-row': {
    padding: '2px 8px',
    whiteSpace: 'nowrap',
  },
  '.lean-abbrev-more': {
    color: '#888',
    fontStyle: 'italic',
  },
});

export function leanUnicodeInput() {
  return [
    abbrevField,
    abbrevTooltipField,
    abbrevKeymap,
    abbrevListener,
    abbrevTheme,
  ];
}
