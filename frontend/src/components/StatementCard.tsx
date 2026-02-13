import { useNavigate } from 'react-router-dom';
import { StatementListItem } from '../api/client';

interface StatementCardProps {
  statement: StatementListItem;
}

function formatTimeAgo(dateString: string): string {
  // Backend stores UTC but serializes without timezone suffix; ensure JS parses as UTC
  const date = new Date(dateString.endsWith('Z') ? dateString : dateString + 'Z');
  const now = new Date();
  const seconds = Math.floor((now.getTime() - date.getTime()) / 1000);

  if (seconds < 60) return 'just now';
  if (seconds < 3600) return `${Math.floor(seconds / 60)}m ago`;
  if (seconds < 86400) return `${Math.floor(seconds / 3600)}h ago`;
  return `${Math.floor(seconds / 86400)}d ago`;
}

export default function StatementCard({ statement }: StatementCardProps) {
  const navigate = useNavigate();

  return (
    <div
      className="card statement-card"
      onClick={() => navigate(`/statement/${statement.id}`)}
    >
      <div className="card-header">
        <h3 className="card-title">{statement.title}</h3>
        {statement.current_prize && (
          <span className={`prize-badge ${statement.is_solved ? 'solved' : ''}`}>
            {statement.is_solved ? 'Solved' : `${statement.current_prize} pts`}
          </span>
        )}
      </div>
      <div className="statement-meta">
        <span>submitted by {statement.submitter.username} {formatTimeAgo(statement.created_at)}</span>
        {statement.is_solved && statement.solver && statement.solved_at && (
          <span>solved by {statement.solver.username} {formatTimeAgo(statement.solved_at)}</span>
        )}
      </div>
    </div>
  );
}
