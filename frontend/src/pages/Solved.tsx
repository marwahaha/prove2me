import { useState, useEffect } from 'react';
import { statementsApi, StatementListItem } from '../api/client';
import StatementCard from '../components/StatementCard';
import toast from 'react-hot-toast';

export default function Solved() {
  const [statements, setStatements] = useState<StatementListItem[]>([]);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    loadStatements();
  }, []);

  const loadStatements = async () => {
    try {
      const data = await statementsApi.listSolved();
      setStatements(data);
    } catch (error: any) {
      toast.error('Failed to load solved statements');
    } finally {
      setLoading(false);
    }
  };

  return (
    <div className="container main-content">
      <div className="page-header">
        <h1 className="page-title">Solved Statements</h1>
      </div>

      {loading ? (
        <div className="loading">Loading statements...</div>
      ) : statements.length === 0 ? (
        <div className="card">
          <p>No statements have been solved yet.</p>
        </div>
      ) : (
        statements.map((statement) => (
          <StatementCard key={statement.id} statement={statement} />
        ))
      )}
    </div>
  );
}
