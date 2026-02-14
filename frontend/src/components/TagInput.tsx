import { useState, useEffect, useRef } from 'react';
import { tagsApi } from '../api/client';

interface TagInputProps {
  onSubmit: (tagName: string) => void;
  onCancel: () => void;
}

export default function TagInput({ onSubmit, onCancel }: TagInputProps) {
  const [value, setValue] = useState('');
  const [suggestions, setSuggestions] = useState<string[]>([]);
  const [showSuggestions, setShowSuggestions] = useState(false);
  const inputRef = useRef<HTMLInputElement>(null);
  const debounceRef = useRef<ReturnType<typeof setTimeout>>();

  useEffect(() => {
    inputRef.current?.focus();
  }, []);

  useEffect(() => {
    if (debounceRef.current) clearTimeout(debounceRef.current);

    if (value.trim().length === 0) {
      setSuggestions([]);
      setShowSuggestions(false);
      return;
    }

    debounceRef.current = setTimeout(async () => {
      try {
        const results = await tagsApi.autocomplete(value.trim());
        setSuggestions(results);
        setShowSuggestions(results.length > 0);
      } catch {
        setSuggestions([]);
      }
    }, 300);

    return () => {
      if (debounceRef.current) clearTimeout(debounceRef.current);
    };
  }, [value]);

  const handleSubmit = () => {
    const trimmed = value.trim();
    if (trimmed) {
      onSubmit(trimmed);
    }
  };

  const handleKeyDown = (e: React.KeyboardEvent) => {
    if (e.key === 'Enter') {
      e.preventDefault();
      handleSubmit();
    } else if (e.key === 'Escape') {
      onCancel();
    }
  };

  const handleSelectSuggestion = (suggestion: string) => {
    onSubmit(suggestion);
  };

  return (
    <div className="tag-input-wrapper" onClick={(e) => e.stopPropagation()}>
      <input
        ref={inputRef}
        type="text"
        className="tag-input"
        value={value}
        onChange={(e) => setValue(e.target.value)}
        onKeyDown={handleKeyDown}
        onBlur={() => {
          // Delay to allow click on suggestion
          setTimeout(() => {
            setShowSuggestions(false);
            if (!value.trim()) onCancel();
          }, 200);
        }}
        placeholder="Tag name..."
        maxLength={30}
      />
      {showSuggestions && (
        <div className="tag-autocomplete">
          {suggestions.map((s) => (
            <div
              key={s}
              className="tag-autocomplete-item"
              onMouseDown={(e) => {
                e.preventDefault();
                handleSelectSuggestion(s);
              }}
            >
              {s}
            </div>
          ))}
        </div>
      )}
    </div>
  );
}
