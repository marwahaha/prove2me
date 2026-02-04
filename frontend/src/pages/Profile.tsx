import { useState, useEffect } from 'react';
import { useAuth } from '../contexts/AuthContext';
import { statementsApi, StatementListItem } from '../api/client';
import StatementCard from '../components/StatementCard';
import toast from 'react-hot-toast';

export default function Profile() {
  const { user } = useAuth();
  const [myStatements, setMyStatements] = useState<StatementListItem[]>([]);
  const [solvedByMe, setSolvedByMe] = useState<StatementListItem[]>([]);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    loadData();
  }, []);

  const loadData = async () => {
    try {
      const [submitted, solved] = await Promise.all([
        statementsApi.my(),
        statementsApi.solvedByMe(),
      ]);
      setMyStatements(submitted);
      setSolvedByMe(solved);
    } catch (error: any) {
      toast.error('Failed to load data');
    } finally {
      setLoading(false);
    }
  };

  if (!user) {
    return <div className="loading">Loading...</div>;
  }

  const myOpenStatements = myStatements.filter((s) => !s.is_solved);
  const myStatementsGotSolved = myStatements.filter((s) => s.is_solved);

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
            <div style={{ color: '#666', fontSize: '0.9rem' }}>Proofs Submitted</div>
            <div style={{ fontSize: '2rem', fontWeight: 700, color: '#4CAF50' }}>
              {solvedByMe.length}
            </div>
          </div>
        </div>
      </div>

      {loading ? (
        <div className="loading">Loading...</div>
      ) : (
        <>
          <h2 style={{ marginTop: '40px', marginBottom: '20px' }}>My Submitted Statements</h2>

          {myStatements.length === 0 ? (
            <div className="card">
              <p>You haven't submitted any statements yet.</p>
            </div>
          ) : (
            <>
              {myOpenStatements.length > 0 && (
                <>
                  <h3 style={{ marginBottom: '15px', color: '#666' }}>Open (awaiting proof)</h3>
                  {myOpenStatements.map((statement) => (
                    <StatementCard key={statement.id} statement={statement} />
                  ))}
                </>
              )}

              {myStatementsGotSolved.length > 0 && (
                <>
                  <h3 style={{ marginTop: '30px', marginBottom: '15px', color: '#666' }}>
                    Solved (by others)
                  </h3>
                  {myStatementsGotSolved.map((statement) => (
                    <StatementCard key={statement.id} statement={statement} />
                  ))}
                </>
              )}
            </>
          )}

          <h2 style={{ marginTop: '40px', marginBottom: '20px' }}>My Proofs</h2>

          {solvedByMe.length === 0 ? (
            <div className="card">
              <p>You haven't solved any statements yet.</p>
            </div>
          ) : (
            solvedByMe.map((statement) => (
              <StatementCard key={statement.id} statement={statement} />
            ))
          )}
        </>
      )}
    </div>
  );
}
