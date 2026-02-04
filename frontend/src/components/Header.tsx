import { Link, useNavigate } from 'react-router-dom';
import { useAuth } from '../contexts/AuthContext';
import toast from 'react-hot-toast';

export default function Header() {
  const { user, logout } = useAuth();
  const navigate = useNavigate();

  const handleLogout = async () => {
    try {
      await logout();
      toast.success('Logged out successfully');
      navigate('/login');
    } catch (error) {
      toast.error('Failed to logout');
    }
  };

  return (
    <header className="header">
      <div className="container">
        <h1>
          <Link to="/">Prove2Me</Link>
        </h1>
        <nav className="nav">
          {user ? (
            <>
              <Link to="/">Open</Link>
              <Link to="/solved">Solved</Link>
              <Link to="/submit">Submit</Link>
              <Link to="/leaderboard">Leaderboard</Link>
              <Link to="/profile">Profile</Link>
              {user.is_admin && <Link to="/admin">Admin</Link>}
              <div className="user-info">
                <span className="points-badge">{user.points} pts</span>
                <span>{user.username}</span>
                <button className="btn btn-secondary btn-small" onClick={handleLogout}>
                  Logout
                </button>
              </div>
            </>
          ) : (
            <>
              <Link to="/login">Login</Link>
              <Link to="/register">Register</Link>
            </>
          )}
        </nav>
      </div>
    </header>
  );
}
