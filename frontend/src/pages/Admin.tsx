import { useState, useEffect } from 'react';
import { adminApi, bannerApi, User, PrizeSettings, StatementListItem } from '../api/client';
import { useAuth } from '../contexts/AuthContext';
import toast from 'react-hot-toast';

export default function Admin() {
  const { user: currentUser } = useAuth();
  const [pendingUsers, setPendingUsers] = useState<User[]>([]);
  const [allUsers, setAllUsers] = useState<User[]>([]);
  const [settings, setSettings] = useState<PrizeSettings | null>(null);
  const [allStatements, setAllStatements] = useState<StatementListItem[]>([]);
  const [loading, setLoading] = useState(true);
  const [activeTab, setActiveTab] = useState<'users' | 'settings' | 'statements'>('users');

  // Banner state
  const [bannerMessage, setBannerMessage] = useState('');
  const [savingBanner, setSavingBanner] = useState(false);

  // Settings form state
  const [basePoints, setBasePoints] = useState('');
  const [growthRate, setGrowthRate] = useState('');
  const [submitterShare, setSubmitterShare] = useState('');
  const [maxStatementsPerDay, setMaxStatementsPerDay] = useState('');
  const [minProofsToSubmit, setMinProofsToSubmit] = useState('');
  const [savingSettings, setSavingSettings] = useState(false);

  useEffect(() => {
    loadData();
  }, []);

  const loadData = async () => {
    try {
      const [pending, settingsData, statements, users, banner] = await Promise.all([
        adminApi.getPendingUsers(),
        adminApi.getSettings(),
        adminApi.getAllStatements(),
        adminApi.getAllUsers(),
        bannerApi.get(),
      ]);

      setPendingUsers(pending);
      setSettings(settingsData);
      setBannerMessage(banner.message);
      setAllStatements(statements);
      setAllUsers(users);

      setBasePoints(settingsData.base_points.toString());
      setGrowthRate(settingsData.growth_rate.toString());
      setSubmitterShare((settingsData.submitter_share * 100).toString());
      setMaxStatementsPerDay(settingsData.max_statements_per_day.toString());
      setMinProofsToSubmit(settingsData.min_proofs_to_submit.toString());
    } catch (error: any) {
      toast.error('Failed to load admin data');
    } finally {
      setLoading(false);
    }
  };

  const handleApproveUser = async (userId: string) => {
    try {
      await adminApi.approveUser(userId);
      toast.success('User approved');
      setPendingUsers(pendingUsers.filter((u) => u.id !== userId));
      loadData();
    } catch (error: any) {
      toast.error(error.message || 'Failed to approve user');
    }
  };

  const handleRejectUser = async (userId: string) => {
    if (!confirm('Are you sure you want to reject this user?')) return;

    try {
      await adminApi.rejectUser(userId);
      toast.success('User rejected');
      setPendingUsers(pendingUsers.filter((u) => u.id !== userId));
    } catch (error: any) {
      toast.error(error.message || 'Failed to reject user');
    }
  };

  const handleResetPassword = async (userId: string, username: string) => {
    const newPassword = prompt(`Enter new password for ${username}:`);
    if (!newPassword) return;

    if (newPassword.length < 6) {
      toast.error('Password must be at least 6 characters');
      return;
    }

    try {
      await adminApi.resetPassword(userId, newPassword);
      toast.success(`Password reset for ${username}`);
    } catch (error: any) {
      toast.error(error.message || 'Failed to reset password');
    }
  };

  const handleToggleAdmin = async (userId: string, username: string, isCurrentlyAdmin: boolean) => {
    const message = isCurrentlyAdmin
      ? `Are you sure you want to remove admin powers from ${username}?`
      : `Are you sure you want to give admin powers to ${username}?`;
    if (!confirm(message)) return;

    try {
      await adminApi.toggleAdmin(userId);
      toast.success(isCurrentlyAdmin ? 'Admin status removed' : 'User is now an admin');
      loadData();
    } catch (error: any) {
      toast.error(error.message || 'Failed to toggle admin status');
    }
  };

  const handleSaveSettings = async (e: React.FormEvent) => {
    e.preventDefault();
    setSavingSettings(true);

    try {
      const updatedSettings = await adminApi.updateSettings({
        base_points: parseInt(basePoints),
        growth_rate: parseFloat(growthRate),
        submitter_share: parseFloat(submitterShare) / 100,
        max_statements_per_day: parseInt(maxStatementsPerDay),
        min_proofs_to_submit: parseInt(minProofsToSubmit),
      });
      setSettings(updatedSettings);
      toast.success('Settings saved');
    } catch (error: any) {
      toast.error(error.message || 'Failed to save settings');
    } finally {
      setSavingSettings(false);
    }
  };

  const handleSaveBanner = async (e: React.FormEvent) => {
    e.preventDefault();
    setSavingBanner(true);
    try {
      await adminApi.setBanner(bannerMessage);
      toast.success(bannerMessage ? 'Banner updated' : 'Banner cleared');
    } catch (error: any) {
      toast.error(error.message || 'Failed to save banner');
    } finally {
      setSavingBanner(false);
    }
  };

  if (loading) {
    return <div className="loading">Loading admin data...</div>;
  }

  return (
    <div className="container main-content">
      <div className="page-header">
        <h1 className="page-title">Admin Panel</h1>
      </div>

      <div style={{ display: 'flex', gap: '10px', marginBottom: '30px' }}>
        <button
          className={`btn ${activeTab === 'users' ? 'btn-primary' : 'btn-secondary'}`}
          onClick={() => setActiveTab('users')}
        >
          Users {pendingUsers.length > 0 && `(${pendingUsers.length} pending)`}
        </button>
        <button
          className={`btn ${activeTab === 'settings' ? 'btn-primary' : 'btn-secondary'}`}
          onClick={() => setActiveTab('settings')}
        >
          Prize Settings
        </button>
        <button
          className={`btn ${activeTab === 'statements' ? 'btn-primary' : 'btn-secondary'}`}
          onClick={() => setActiveTab('statements')}
        >
          All Statements
        </button>
      </div>

      {activeTab === 'users' && (
        <div className="admin-section">
          <h3>Pending Approvals</h3>
          {pendingUsers.length === 0 ? (
            <div className="card">
              <p>No pending users to approve.</p>
            </div>
          ) : (
            <div className="card">
              <table className="table">
                <thead>
                  <tr>
                    <th>Username</th>
                    <th>Email</th>
                    <th>Registered</th>
                    <th>Actions</th>
                  </tr>
                </thead>
                <tbody>
                  {pendingUsers.map((user) => (
                    <tr key={user.id}>
                      <td>{user.username}</td>
                      <td>{user.email}</td>
                      <td>{new Date(user.created_at).toLocaleDateString()}</td>
                      <td>
                        <button
                          className="btn btn-success btn-small"
                          onClick={() => handleApproveUser(user.id)}
                          style={{ marginRight: '10px' }}
                        >
                          Approve
                        </button>
                        <button
                          className="btn btn-danger btn-small"
                          onClick={() => handleRejectUser(user.id)}
                        >
                          Reject
                        </button>
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          )}

          <h3 style={{ marginTop: '40px' }}>All Users</h3>
          <div className="card">
            <table className="table">
              <thead>
                <tr>
                  <th>Username</th>
                  <th>Email</th>
                  <th>Points</th>
                  <th>Status</th>
                  <th>Registered</th>
                  <th>Actions</th>
                </tr>
              </thead>
              <tbody>
                {allUsers.map((user) => (
                  <tr key={user.id}>
                    <td>
                      {user.username}
                      {user.is_admin && <span style={{ marginLeft: '5px', color: '#0066cc' }}>(Admin)</span>}
                    </td>
                    <td>{user.email}</td>
                    <td>{user.points}</td>
                    <td>
                      <span style={{ color: user.is_approved ? '#4CAF50' : '#ff9800' }}>
                        {user.is_approved ? 'Approved' : 'Pending'}
                      </span>
                    </td>
                    <td>{new Date(user.created_at).toLocaleDateString()}</td>
                    <td>
                      <button
                        className="btn btn-secondary btn-small"
                        onClick={() => handleResetPassword(user.id, user.username)}
                      >
                        Reset Password
                      </button>
                      {currentUser && currentUser.id !== user.id && (
                        <button
                          className={`btn ${user.is_admin ? 'btn-danger' : 'btn-success'} btn-small`}
                          onClick={() => handleToggleAdmin(user.id, user.username, user.is_admin)}
                          style={{ marginLeft: '10px' }}
                        >
                          {user.is_admin ? 'Remove Admin' : 'Make Admin'}
                        </button>
                      )}
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </div>
      )}

      {activeTab === 'settings' && (
        <div className="admin-section">
          <h3>Site Banner</h3>
          <div className="card" style={{ marginBottom: '30px' }}>
            <form onSubmit={handleSaveBanner}>
              <div className="form-group">
                <label htmlFor="bannerMessage">Banner Message</label>
                <input
                  type="text"
                  id="bannerMessage"
                  value={bannerMessage}
                  onChange={(e) => setBannerMessage(e.target.value)}
                  placeholder="Enter a message to display site-wide (leave empty to hide)"
                />
                <small style={{ color: '#666' }}>Displayed at the top of every page. Submit empty to clear.</small>
              </div>
              <button
                type="submit"
                className="btn btn-primary"
                disabled={savingBanner}
                style={{ marginTop: '10px' }}
              >
                {savingBanner ? 'Saving...' : 'Save Banner'}
              </button>
            </form>
          </div>

          <h3>Prize Settings</h3>
          <div className="card">
            <form onSubmit={handleSaveSettings}>
              <div className="settings-form">
                <div className="form-group">
                  <label htmlFor="basePoints">Base Points</label>
                  <input
                    type="number"
                    id="basePoints"
                    value={basePoints}
                    onChange={(e) => setBasePoints(e.target.value)}
                    min="1"
                  />
                  <small style={{ color: '#666' }}>Starting prize for new statements</small>
                </div>

                <div className="form-group">
                  <label htmlFor="growthRate">Growth Rate</label>
                  <input
                    type="number"
                    id="growthRate"
                    value={growthRate}
                    onChange={(e) => setGrowthRate(e.target.value)}
                    min="1"
                    step="0.01"
                  />
                  <small style={{ color: '#666' }}>Multiplier per day (1.5 = 50% growth)</small>
                </div>

                <div className="form-group">
                  <label htmlFor="submitterShare">Submitter Share (%)</label>
                  <input
                    type="number"
                    id="submitterShare"
                    value={submitterShare}
                    onChange={(e) => setSubmitterShare(e.target.value)}
                    min="0"
                    max="100"
                  />
                  <small style={{ color: '#666' }}>Percentage of prize to statement submitter</small>
                </div>

                <div className="form-group">
                  <label htmlFor="maxStatementsPerDay">Max Statements Per Day</label>
                  <input
                    type="number"
                    id="maxStatementsPerDay"
                    value={maxStatementsPerDay}
                    onChange={(e) => setMaxStatementsPerDay(e.target.value)}
                    min="1"
                  />
                  <small style={{ color: '#666' }}>Maximum statements a user can submit per 24 hours</small>
                </div>

                <div className="form-group">
                  <label htmlFor="minProofsToSubmit">Min Proofs to Submit Statements</label>
                  <input
                    type="number"
                    id="minProofsToSubmit"
                    value={minProofsToSubmit}
                    onChange={(e) => setMinProofsToSubmit(e.target.value)}
                    min="0"
                  />
                  <small style={{ color: '#666' }}>Minimum proofs a user must solve before submitting statements (0 = no restriction)</small>
                </div>
              </div>

              <button
                type="submit"
                className="btn btn-primary"
                disabled={savingSettings}
                style={{ marginTop: '20px' }}
              >
                {savingSettings ? 'Saving...' : 'Save Settings'}
              </button>
            </form>

            {settings && (
              <div style={{ marginTop: '30px', padding: '15px', background: '#f5f5f5', borderRadius: '6px' }}>
                <strong>Current Settings:</strong>
                <ul style={{ marginTop: '10px', paddingLeft: '20px' }}>
                  <li>Base Points: {settings.base_points}</li>
                  <li>Growth Rate: {settings.growth_rate}x per day</li>
                  <li>Submitter Share: {(settings.submitter_share * 100).toFixed(0)}%</li>
                  <li>Prover Share: {((1 - settings.submitter_share) * 100).toFixed(0)}%</li>
                  <li>Max Statements Per Day: {settings.max_statements_per_day}</li>
                  <li>Min Proofs to Submit: {settings.min_proofs_to_submit}</li>
                </ul>
              </div>
            )}
          </div>
        </div>
      )}

      {activeTab === 'statements' && (
        <div className="admin-section">
          <h3>All Statements ({allStatements.length})</h3>
          <div className="card">
            <table className="table">
              <thead>
                <tr>
                  <th>Title</th>
                  <th>Submitter</th>
                  <th>Status</th>
                  <th>Prize/Points</th>
                  <th>Created</th>
                </tr>
              </thead>
              <tbody>
                {allStatements.map((statement) => (
                  <tr key={statement.id}>
                    <td>
                      <a href={`/statement/${statement.id}`}>{statement.title}</a>
                    </td>
                    <td>{statement.submitter.username}</td>
                    <td>
                      <span style={{ color: statement.is_solved ? '#4CAF50' : '#ff9800' }}>
                        {statement.is_solved ? 'Solved' : 'Open'}
                      </span>
                    </td>
                    <td>{statement.current_prize || '-'}</td>
                    <td>{new Date(statement.created_at).toLocaleDateString()}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </div>
      )}
    </div>
  );
}
