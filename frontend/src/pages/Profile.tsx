import { useState, useEffect } from 'react';
import { useAuth } from '../contexts/AuthContext';
import { statementsApi, StatementListItem } from '../api/client';
import StatementCard from '../components/StatementCard';
import toast from 'react-hot-toast';

export default function Profile() {
  const { user } = useAuth();
  const [myStatements, setMyStatements] = useState<StatementListItem[]>([]);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    loadMyStatements();
  }, []);

  const loadMyStatements = async () => {
    try {
      const data = await statementsApi.my();
      setMyStatements(data);
    } catch (error: any) {
      toast.error('Failed to load your statements');
    } finally {
      setLoading(false);
    }
  };

  if (!user) {
    return <div className="loading">Loading...</div>;
  }

  const solvedStatements = myStatements.filter((s) => s.is_solved);
  const openStatements = myStatements.filter((s) => !s.is_solved);

  return (
    <div className="container main-content">
      <div className="page-header">
        <h1 className="page-title">My Profile</h1>
      </div>

      <div className="card">
        <h2 style={{ marginBottom: '20px' }}>{user.username}</h2>
        <div style={{ display: 'grid', gridTemplateColumns: 'repeat(auto-fit, minmax(150px, 1fr))', gap: '20px' }}>
          <div>
            <div style={{ color: '#666', fontSize: '0.9rem' }}>Total Points</div>
            <div style={{ fontSize: '2rem', fontWeight: 700, color: '#4CAF50' }}>
              {user.points.toLocaleString()}
            </div>
          </div>
          <div>
            <div style={{ color: '#666', fontSize: '0.9rem' }}>Statements Submitted</div>
            <div style={{ fontSize: '2rem', fontWeight: 700 }}>
              {myStatements.length}
            </div>
          </div>
          <div>
            <div style={{ color: '#666', fontSize: '0.9rem' }}>Open Statements</div>
            <div style={{ fontSize: '2rem', fontWeight: 700, color: '#ff9800' }}>
              {openStatements.length}
            </div>
          </div>
          <div>
            <div style={{ color: '#666', fontSize: '0.9rem' }}>Solved Statements</div>
            <div style={{ fontSize: '2rem', fontWeight: 700, color: '#4CAF50' }}>
              {solvedStatements.length}
            </div>
          </div>
        </div>
      </div>

      <h2 style={{ marginTop: '40px', marginBottom: '20px' }}>My Statements</h2>

      {loading ? (
        <div className="loading">Loading statements...</div>
      ) : myStatements.length === 0 ? (
        <div className="card">
          <p>You haven't submitted any statements yet.</p>
        </div>
      ) : (
        <>
          {openStatements.length > 0 && (
            <>
              <h3 style={{ marginBottom: '15px', color: '#666' }}>Open</h3>
              {openStatements.map((statement) => (
                <StatementCard key={statement.id} statement={statement} />
              ))}
            </>
          )}

          {solvedStatements.length > 0 && (
            <>
              <h3 style={{ marginTop: '30px', marginBottom: '15px', color: '#666' }}>Solved</h3>
              {solvedStatements.map((statement) => (
                <StatementCard key={statement.id} statement={statement} />
              ))}
            </>
          )}
        </>
      )}
    </div>
  );
}
