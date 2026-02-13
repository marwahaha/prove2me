import { useState } from 'react';
import { useNavigate } from 'react-router-dom';
import { statementsApi } from '../api/client';
import CodeEditor from '../components/CodeEditor';
import toast from 'react-hot-toast';

export default function SubmitStatement() {
  const [title, setTitle] = useState('');
  const [definitions, setDefinitions] = useState('');
  const [leanCode, setLeanCode] = useState('');
  const [loading, setLoading] = useState(false);
  const [compiling, setCompiling] = useState(false);
  const [compileError, setCompileError] = useState<string | null>(null);
  const navigate = useNavigate();

  const handleCompileTest = async () => {
    if (!leanCode.trim()) {
      toast.error('Please enter a proposition');
      return;
    }

    setCompiling(true);
    setCompileError(null);

    try {
      const result = await statementsApi.compile(title, leanCode, definitions || undefined);
      if (result.success) {
        toast.success('Code compiles successfully!');
      } else {
        setCompileError(result.error || 'Compilation failed');
        toast.error('Compilation failed');
      }
    } catch (error: any) {
      toast.error(error.message || 'Failed to compile');
    } finally {
      setCompiling(false);
    }
  };

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault();

    if (!title.trim() || !leanCode.trim()) {
      toast.error('Please fill in title and proposition');
      return;
    }

    setLoading(true);

    try {
      const statement = await statementsApi.create(title, leanCode, definitions || undefined);
      toast.success('Statement submitted successfully!');
      navigate(`/statement/${statement.id}`);
    } catch (error: any) {
      toast.error(error.message || 'Failed to submit statement');
    } finally {
      setLoading(false);
    }
  };

  return (
    <div className="container main-content">
      <div className="page-header">
        <h1 className="page-title">Submit Lean Statement</h1>
      </div>

      <div className="card">
        <form onSubmit={handleSubmit}>
          <div className="form-group">
            <label htmlFor="title">Title</label>
            <input
              type="text"
              id="title"
              value={title}
              onChange={(e) => setTitle(e.target.value)}
              placeholder="e.g., Prove that sqrt(2) is irrational"
              required
            />
          </div>

          <div className="form-group">
            <label>Definitions (optional)</label>
            <CodeEditor
              value={definitions}
              onChange={setDefinitions}
              placeholder="-- Optional: Add helper definitions, structures, or lemmas here
-- These will be available when compiling the proposition and proof
-- Example:
-- def MyPredicate (n : Nat) : Prop := n > 0 ∧ n < 100"
              height="150px"
            />
          </div>

          <div className="form-group">
            <label>Proposition (Lean term of type Prop)</label>
            <CodeEditor
              value={leanCode}
              onChange={setLeanCode}
              placeholder="-- Enter a Lean proposition (must have type Prop)
-- Examples:
-- ∀ n : Nat, n + 0 = n
-- ∀ x y : Nat, x + y = y + x
-- Irrational (Real.sqrt 2)"
            />
          </div>

          {compileError && (
            <div className="error-message">
              <strong>Compilation Error:</strong>
              <pre style={{ marginTop: '10px', whiteSpace: 'pre-wrap' }}>{compileError}</pre>
            </div>
          )}

          <div style={{ display: 'flex', gap: '10px' }}>
            <button
              type="button"
              className="btn btn-secondary"
              onClick={handleCompileTest}
              disabled={compiling || loading}
            >
              {compiling ? 'Compiling...' : 'Test Compile'}
            </button>
            <button
              type="submit"
              className="btn btn-primary"
              disabled={loading || compiling}
            >
              {loading ? 'Submitting...' : 'Submit Statement'}
            </button>
          </div>
        </form>
      </div>

      <div className="card" style={{ marginTop: '20px' }}>
        <h3 style={{ marginBottom: '15px' }}>Guidelines</h3>
        <ul style={{ paddingLeft: '20px' }}>
          <li>Use <strong>Definitions</strong> for helper types, predicates, or lemmas needed by your proposition</li>
          <li>The <strong>Proposition</strong> must have type <code>Prop</code></li>
          <li>Do not include <code>theorem</code> or <code>:= by sorry</code> — just the proposition itself</li>
          <li>Mathlib is available — you can use any Mathlib types and definitions</li>
          <li>The prize increases over time until someone solves it</li>
          <li>You'll earn 20% of the prize when someone proves your statement</li>
          <li><strong>Limit:</strong> You can submit a limited number of statements per 24 hours</li>
        </ul>
      </div>
    </div>
  );
}
