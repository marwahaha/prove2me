import { useNavigate } from 'react-router-dom';
import { StatementListItem } from '../api/client';
import { formatTimeAgo } from '../utils/time';

interface StatementCardProps {
  statement: StatementListItem;
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
