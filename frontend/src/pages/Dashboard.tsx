import { useState, useEffect } from 'react';
import { statementsApi, StatementListItem } from '../api/client';
import StatementCard from '../components/StatementCard';
import { Link } from 'react-router-dom';
import toast from 'react-hot-toast';

export default function Dashboard() {
  const [statements, setStatements] = useState<StatementListItem[]>([]);
  const [loading, setLoading] = useState(true);
  const [sortBy, setSortBy] = useState<'newest' | 'prize'>('newest');

  useEffect(() => {
    loadStatements();
  }, [sortBy]);

  const loadStatements = async () => {
    try {
      const data = await statementsApi.list(sortBy);
      setStatements(data);
    } catch (error: any) {
      toast.error('Failed to load statements');
    } finally {
      setLoading(false);
    }
  };

  return (
    <div className="container main-content">
      <div className="page-header">
        <h1 className="page-title">Open Statements</h1>
        <Link to="/submit" className="btn btn-primary">
          Submit Statement
        </Link>
      </div>

      <div className="sort-controls">
        <label>Sort by: </label>
        <select value={sortBy} onChange={(e) => setSortBy(e.target.value as 'newest' | 'prize')}>
          <option value="newest">Newest</option>
          <option value="prize">Highest Prize</option>
        </select>
      </div>

      {loading ? (
        <div className="loading">Loading statements...</div>
      ) : statements.length === 0 ? (
        <div className="card">
          <p>No open statements yet. Be the first to submit one!</p>
        </div>
      ) : (
        <div className="statement-list">
          {statements.map((statement) => (
            <StatementCard key={statement.id} statement={statement} />
          ))}
        </div>
      )}
    </div>
  );
}
