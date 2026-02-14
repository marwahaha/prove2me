import { useState, useEffect } from 'react';
import { useParams, useNavigate } from 'react-router-dom';
import { statementsApi, proofsApi, adminApi, Statement } from '../api/client';
import { useAuth } from '../contexts/AuthContext';
import CodeEditor from '../components/CodeEditor';
import toast from 'react-hot-toast';

export default function StatementDetail() {
  const { id } = useParams<{ id: string }>();
  const navigate = useNavigate();
  const { user, refreshUser } = useAuth();
  const [statement, setStatement] = useState<Statement | null>(null);
  const [loading, setLoading] = useState(true);
  const [imports, setImports] = useState('');
  const [proofCode, setProofCode] = useState('');
  const [theoremName, setTheoremName] = useState('');
  const [submitting, setSubmitting] = useState(false);
  const [proofResult, setProofResult] = useState<{ success: boolean; message: string } | null>(null);
  const [editingTitle, setEditingTitle] = useState(false);
  const [titleDraft, setTitleDraft] = useState('');

  useEffect(() => {
    loadStatement();
  }, [id]);

  const loadStatement = async () => {
    if (!id) return;

    try {
      const data = await statementsApi.get(id);
      setStatement(data);
    } catch (error: any) {
      toast.error('Failed to load statement');
    } finally {
      setLoading(false);
    }
  };

  const handleSubmitProof = async (e: React.FormEvent) => {
    e.preventDefault();

    if (!id || !proofCode.trim()) {
      toast.error('Please enter your proof code');
      return;
    }

    if (!theoremName.trim()) {
      toast.error('Please enter the theorem name');
      return;
    }

    setSubmitting(true);
    setProofResult(null);

    try {
      const result = await proofsApi.submit(id, proofCode, theoremName.trim(), imports || undefined);
      setProofResult(result);

      if (result.success) {
        toast.success('Proof accepted!');
        await refreshUser();
        await loadStatement();
      } else {
        toast.error('Proof rejected');
      }
    } catch (error: any) {
      toast.error(error.message || 'Failed to submit proof');
    } finally {
      setSubmitting(false);
    }
  };

  if (loading) {
    return <div className="loading">Loading statement...</div>;
  }

  if (!statement) {
    return (
      <div className="container main-content">
        <div className="card">
          <p>Statement not found.</p>
        </div>
      </div>
    );
  }

  const handleArchive = async () => {
    if (!statement || !confirm('Are you sure you want to archive this statement? It will be hidden from public listings.')) return;
    try {
      await statementsApi.archive(statement.id);
      toast.success('Statement archived');
      navigate('/profile');
    } catch (error: any) {
      toast.error(error.message || 'Failed to archive statement');
    }
  };

  const handleSaveTitle = async () => {
    if (!titleDraft.trim() || !statement) return;
    try {
      await adminApi.updateStatementTitle(statement.id, titleDraft.trim());
      setStatement({ ...statement, title: titleDraft.trim() });
      setEditingTitle(false);
      toast.success('Title updated');
    } catch (error: any) {
      toast.error(error.message || 'Failed to update title');
    }
  };

  const isOwnStatement = user && statement.submitter.id === user.id;

  return (
    <div className="container main-content">
      <div className="card">
        <div className="card-header">
          {editingTitle ? (
            <div style={{ display: 'flex', alignItems: 'center', gap: '8px', flex: 1 }}>
              <input
                type="text"
                value={titleDraft}
                onChange={(e) => setTitleDraft(e.target.value)}
                style={{ flex: 1, fontSize: '1.2em' }}
                onKeyDown={(e) => {
                  if (e.key === 'Enter') handleSaveTitle();
                  if (e.key === 'Escape') setEditingTitle(false);
                }}
                autoFocus
              />
              <button className="btn btn-success btn-small" onClick={handleSaveTitle}>Save</button>
              <button className="btn btn-secondary btn-small" onClick={() => setEditingTitle(false)}>Cancel</button>
            </div>
          ) : (
            <h1 className="card-title">
              {statement.title}
              {user?.is_admin && (
                <button
                  className="btn btn-secondary btn-small"
                  style={{ marginLeft: '10px', fontSize: '12px' }}
                  onClick={() => { setTitleDraft(statement.title); setEditingTitle(true); }}
                >
                  Edit
                </button>
              )}
            </h1>
          )}
          <span className={`prize-badge ${statement.is_solved ? 'solved' : ''}`}>
            {statement.is_solved ? 'Solved' : `${statement.current_prize} pts`}
          </span>
        </div>

        <div className="statement-meta" style={{ marginBottom: '20px' }}>
          <span>Submitted by {statement.submitter.username}</span>
          <span>{new Date(statement.created_at).toLocaleDateString()}</span>
          {statement.is_solved && statement.solver && (
            <span>Solved by {statement.solver.username}</span>
          )}
        </div>

        {statement.definitions && (
          <>
            <h3 style={{ marginBottom: '10px' }}>Definitions</h3>
            <CodeEditor value={statement.definitions} onChange={() => {}} readOnly height="150px" />
            <div style={{ marginTop: '20px' }} />
          </>
        )}

        <h3 style={{ marginBottom: '10px' }}>Proposition</h3>
        <CodeEditor value={statement.lean_code} onChange={() => {}} readOnly height="200px" />

        {!statement.is_solved && (isOwnStatement || user?.is_admin) && (
          <button
            className="btn btn-danger btn-small"
            style={{ marginTop: '15px' }}
            onClick={handleArchive}
          >
            Archive Statement
          </button>
        )}
      </div>

      {statement.is_solved ? (
        <div className="card">
          <div className="success-message" style={{ marginBottom: '20px' }}>
            Solved by {statement.solver?.username} on {new Date(statement.solved_at!).toLocaleDateString()}
          </div>
          <h3 style={{ marginBottom: '10px' }}>Proof</h3>
          {statement.proof_theorem_name && (
            <p style={{ marginBottom: '10px', color: '#666' }}>
              Theorem: <code>{statement.proof_theorem_name}</code>
            </p>
          )}
          {statement.proof_imports && (
            <>
              <h4 style={{ marginBottom: '5px' }}>Imports</h4>
              <CodeEditor
                value={statement.proof_imports}
                onChange={() => {}}
                readOnly
                height="60px"
              />
              <div style={{ marginTop: '10px' }} />
            </>
          )}
          <CodeEditor
            value={statement.proof_code || ''}
            onChange={() => {}}
            readOnly
            height="300px"
          />
        </div>
      ) : isOwnStatement ? (
        <div className="card">
          <p>This is your own statement. You cannot submit a proof for it.</p>
        </div>
      ) : user ? (
        <div className="card">
          <h2 style={{ marginBottom: '20px' }}>Submit Your Proof</h2>

          {proofResult && (
            <div className={proofResult.success ? 'success-message' : 'error-message'}>
              {proofResult.message}
            </div>
          )}

          <form onSubmit={handleSubmitProof}>
            <div className="form-group">
              <label>Imports</label>
              <CodeEditor
                value={imports}
                onChange={setImports}
                placeholder="-- Optional: e.g., import Mathlib.Data.Nat.Basic"
                height="60px"
              />
            </div>

            <div className="form-group">
              <label>Lean Code</label>
              <CodeEditor
                value={proofCode}
                onChange={setProofCode}
                placeholder="-- Write your proof here
-- You can include helper lemmas, definitions, etc.
-- Example:
theorem my_proof : ∀ n : Nat, n + 0 = n := by
  intro n
  simp"
                height="300px"
              />
            </div>

            <div className="form-group">
              <label htmlFor="theoremName">Theorem Name</label>
              <input
                type="text"
                id="theoremName"
                value={theoremName}
                onChange={(e) => setTheoremName(e.target.value)}
                placeholder="e.g., my_proof"
                required
              />
              <small style={{ color: '#666', display: 'block', marginTop: '5px' }}>
                The name of the theorem in your code that proves the proposition
              </small>
            </div>

            <button
              type="submit"
              className="btn btn-success"
              disabled={submitting}
            >
              {submitting ? 'Verifying Proof...' : 'Submit Proof'}
            </button>
          </form>

          <div style={{ marginTop: '20px', color: '#666' }}>
            <strong>Note:</strong> Your Lean code must compile without errors and cannot contain <code>sorry</code>.
            The specified theorem must have a type that exactly matches the proposition above.
          </div>
        </div>
      ) : (
        <div className="card">
          <p>Please log in to submit a proof.</p>
        </div>
      )}
    </div>
  );
}
