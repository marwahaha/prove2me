import { useMemo } from 'react';
import CodeMirror from '@uiw/react-codemirror';
import { markdown } from '@codemirror/lang-markdown';
import { githubLight } from '@uiw/codemirror-theme-github';
import { leanUnicodeInput } from '../lib/leanUnicodeInput';

interface CodeEditorProps {
  value: string;
  onChange: (value: string) => void;
  placeholder?: string;
  readOnly?: boolean;
  height?: string;
}

export default function CodeEditor({
  value,
  onChange,
  placeholder,
  readOnly = false,
  height = '300px',
}: CodeEditorProps) {
  const extensions = useMemo(
    () => (readOnly ? [markdown()] : [markdown(), leanUnicodeInput()]),
    [readOnly],
  );
  return (
    <div className="code-editor">
      <CodeMirror
        value={value}
        height={height}
        theme={githubLight}
        extensions={extensions}
        onChange={onChange}
        placeholder={placeholder}
        readOnly={readOnly}
        basicSetup={{
          lineNumbers: true,
          highlightActiveLineGutter: true,
          highlightActiveLine: true,
          foldGutter: true,
        }}
      />
    </div>
  );
}
