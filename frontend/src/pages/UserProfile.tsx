import { useState, useEffect } from 'react';
import { useParams } from 'react-router-dom';
import { usersApi, UserProfileResponse, StatementListItem } from '../api/client';
import { useAuth } from '../contexts/AuthContext';
import StatementCard from '../components/StatementCard';
import toast from 'react-hot-toast';

export default function UserProfile() {
  const { username } = useParams<{ username: string }>();
  const { user: currentUser } = useAuth();
  const [profile, setProfile] = useState<UserProfileResponse | null>(null);
  const [statements, setStatements] = useState<StatementListItem[]>([]);
  const [solved, setSolved] = useState<StatementListItem[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    if (username) loadData();
  }, [username]);

  const loadData = async () => {
    if (!username) return;
    setLoading(true);
    setError(null);

    try {
      const [profileData, statementsData, solvedData] = await Promise.all([
        usersApi.getProfile(username),
        usersApi.getStatements(username),
        usersApi.getSolved(username),
      ]);
      setProfile(profileData);
      setStatements(statementsData);
      setSolved(solvedData);
    } catch (err: any) {
      if (err.status === 404) {
        setError('User not found');
      } else {
        setError('Failed to load user profile');
        toast.error('Failed to load user profile');
      }
    } finally {
      setLoading(false);
    }
  };

  if (loading) {
    return <div className="loading">Loading profile...</div>;
  }

  if (error || !profile) {
    return (
      <div className="container main-content">
        <div className="card">
          <p>{error || 'User not found'}</p>
        </div>
      </div>
    );
  }

  const isOwnProfile = currentUser?.username === profile.username;
  const openStatements = statements.filter((s) => !s.is_solved);
  const solvedStatements = statements.filter((s) => s.is_solved);

  return (
    <div className="container main-content">
      <div className="page-header">
        <h1 className="page-title">{profile.username}</h1>
        {isOwnProfile && (
          <span style={{ color: '#666', fontSize: '0.9rem' }}>That's you!</span>
        )}
      </div>

      <div className="card">
        <div style={{ display: 'grid', gridTemplateColumns: 'repeat(auto-fit, minmax(150px, 1fr))', gap: '20px' }}>
          <div>
            <div style={{ color: '#666', fontSize: '0.9rem' }}>Total Points</div>
            <div style={{ fontSize: '2rem', fontWeight: 700, color: '#4CAF50' }}>
              {profile.points.toLocaleString()}
            </div>
          </div>
          <div>
            <div style={{ color: '#666', fontSize: '0.9rem' }}>Statements Submitted</div>
            <div style={{ fontSize: '2rem', fontWeight: 700 }}>
              {profile.submitted_count}
            </div>
          </div>
          <div>
            <div style={{ color: '#666', fontSize: '0.9rem' }}>Proofs Submitted</div>
            <div style={{ fontSize: '2rem', fontWeight: 700, color: '#4CAF50' }}>
              {profile.solved_count}
            </div>
          </div>
          <div>
            <div style={{ color: '#666', fontSize: '0.9rem' }}>Member Since</div>
            <div style={{ fontSize: '1.2rem', fontWeight: 700 }}>
              {new Date(profile.created_at).toLocaleDateString()}
            </div>
          </div>
        </div>
      </div>

      <h2 style={{ marginTop: '40px', marginBottom: '20px' }}>Submitted Statements</h2>

      {statements.length === 0 ? (
        <div className="card">
          <p>No statements submitted yet.</p>
        </div>
      ) : (
        <>
          {openStatements.length > 0 && (
            <>
              <h3 style={{ marginBottom: '15px', color: '#666' }}>Open (awaiting proof)</h3>
              <div className="statement-list">
                {openStatements.map((statement) => (
                  <StatementCard key={statement.id} statement={statement} />
                ))}
              </div>
            </>
          )}

          {solvedStatements.length > 0 && (
            <>
              <h3 style={{ marginTop: '30px', marginBottom: '15px', color: '#666' }}>
                Solved (by others)
              </h3>
              <div className="statement-list">
                {solvedStatements.map((statement) => (
                  <StatementCard key={statement.id} statement={statement} />
                ))}
              </div>
            </>
          )}
        </>
      )}

      <h2 style={{ marginTop: '40px', marginBottom: '20px' }}>Proofs</h2>

      {solved.length === 0 ? (
        <div className="card">
          <p>No proofs submitted yet.</p>
        </div>
      ) : (
        <div className="statement-list">
          {solved.map((statement) => (
            <StatementCard key={statement.id} statement={statement} />
          ))}
        </div>
      )}
    </div>
  );
}
