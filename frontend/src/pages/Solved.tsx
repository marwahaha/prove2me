import { useState, useEffect } from 'react';
import { statementsApi, StatementListItem } from '../api/client';
import StatementCard from '../components/StatementCard';
import toast from 'react-hot-toast';

export default function Solved() {
  const [statements, setStatements] = useState<StatementListItem[]>([]);
  const [loading, setLoading] = useState(true);
  const [selectedTags, setSelectedTags] = useState<string[]>([]);
  const [hideGatekeeper, setHideGatekeeper] = useState(true);

  useEffect(() => {
    loadStatements();
  }, [selectedTags]);

  const loadStatements = async () => {
    try {
      const data = await statementsApi.listSolved(selectedTags.length > 0 ? selectedTags : undefined);
      setStatements(data);
    } catch (error: any) {
      toast.error('Failed to load solved statements');
    } finally {
      setLoading(false);
    }
  };

  const handleTagClick = (tagName: string) => {
    setSelectedTags((prev) =>
      prev.some((t) => t.toLowerCase() === tagName.toLowerCase())
        ? prev.filter((t) => t.toLowerCase() !== tagName.toLowerCase())
        : [...prev, tagName]
    );
  };

  const visibleStatements = hideGatekeeper
    ? statements.filter((s) => s.solver?.username !== 'gatekeeper')
    : statements;

  return (
    <div className="container main-content">
      <div className="page-header">
        <h1 className="page-title">Solved Statements</h1>
        <label className="hide-gatekeeper-toggle">
          <input
            type="checkbox"
            checked={hideGatekeeper}
            onChange={(e) => setHideGatekeeper(e.target.checked)}
          />
          Hide gatekeeper solutions
        </label>
      </div>

      {selectedTags.length > 0 && (
        <div className="tags-filter">
          <span className="tags-filter-label">Filtering by:</span>
          {selectedTags.map((tag) => (
            <span key={tag} className="tag-pill tag-filter-pill" onClick={() => handleTagClick(tag)}>
              {tag} <span className="tag-delete">&times;</span>
            </span>
          ))}
          <span className="tag-pill tag-add" onClick={() => setSelectedTags([])}>Clear all</span>
        </div>
      )}

      {loading ? (
        <div className="loading">Loading statements...</div>
      ) : visibleStatements.length === 0 ? (
        <div className="card">
          <p>No statements have been solved yet.</p>
        </div>
      ) : (
        <div className="statement-list">
          {visibleStatements.map((statement) => (
            <StatementCard
              key={statement.id}
              statement={statement}
              onTagClick={handleTagClick}
              onTagsChanged={loadStatements}
            />
          ))}
        </div>
      )}
    </div>
  );
}
