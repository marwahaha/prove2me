import { useState, useEffect } from 'react';
import { Link } from 'react-router-dom';
import { leaderboardApi, LeaderboardEntry } from '../api/client';
import toast from 'react-hot-toast';

export default function Leaderboard() {
  const [entries, setEntries] = useState<LeaderboardEntry[]>([]);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    loadLeaderboard();
  }, []);

  const loadLeaderboard = async () => {
    try {
      const data = await leaderboardApi.get();
      setEntries(data);
    } catch (error: any) {
      toast.error('Failed to load leaderboard');
    } finally {
      setLoading(false);
    }
  };

  const getRankClass = (rank: number) => {
    if (rank === 1) return 'rank rank-1';
    if (rank === 2) return 'rank rank-2';
    if (rank === 3) return 'rank rank-3';
    return 'rank';
  };

  return (
    <div className="container main-content">
      <div className="page-header">
        <h1 className="page-title">Leaderboard</h1>
      </div>

      {loading ? (
        <div className="loading">Loading leaderboard...</div>
      ) : entries.length === 0 ? (
        <div className="card">
          <p>No users on the leaderboard yet.</p>
        </div>
      ) : (
        <div className="card">
          <table className="table">
            <thead>
              <tr>
                <th style={{ width: '80px' }}>Rank</th>
                <th>Username</th>
                <th style={{ width: '120px', textAlign: 'right' }}>Points</th>
              </tr>
            </thead>
            <tbody>
              {entries.map((entry) => (
                <tr key={entry.username}>
                  <td>
                    <span className={getRankClass(entry.rank)}>
                      {entry.rank === 1 && '🥇 '}
                      {entry.rank === 2 && '🥈 '}
                      {entry.rank === 3 && '🥉 '}
                      #{entry.rank}
                    </span>
                  </td>
                  <td><Link to={`/user/${entry.username}`}>{entry.username}</Link></td>
                  <td style={{ textAlign: 'right', fontWeight: 600 }}>
                    {entry.points.toLocaleString()}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      )}
    </div>
  );
}
