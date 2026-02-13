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
      className="statement-row"
      onClick={() => navigate(`/statement/${statement.id}`)}
    >
      <span className="statement-row-title">{statement.title}</span>
      <span className="statement-row-meta">
        {statement.submitter.username}
        <span className="statement-row-time">{formatTimeAgo(statement.created_at)}</span>
      </span>
      {statement.is_solved && statement.solver ? (
        <span className="prize-badge solved">Solved</span>
      ) : statement.current_prize ? (
        <span className="prize-badge">{statement.current_prize} pts</span>
      ) : null}
    </div>
  );
}
