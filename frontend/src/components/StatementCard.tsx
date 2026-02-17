import { useState } from 'react';
import { useNavigate, Link } from 'react-router-dom';
import { StatementListItem, tagsApi } from '../api/client';
import { formatTimeAgo } from '../utils/time';
import { useAuth } from '../contexts/AuthContext';
import TagInput from './TagInput';
import toast from 'react-hot-toast';

interface StatementCardProps {
  statement: StatementListItem;
  onTagClick?: (tagName: string) => void;
  onTagsChanged?: () => void;
}

export default function StatementCard({ statement, onTagClick, onTagsChanged }: StatementCardProps) {
  const navigate = useNavigate();
  const { user } = useAuth();
  const [showTagInput, setShowTagInput] = useState(false);

  const handleAddTag = async (tagName: string) => {
    try {
      await tagsApi.create(statement.id, tagName);
      setShowTagInput(false);
      onTagsChanged?.();
    } catch (error: any) {
      toast.error(error.message || 'Failed to add tag');
    }
  };

  const handleDeleteTag = async (e: React.MouseEvent, tagName: string) => {
    e.stopPropagation();
    try {
      await tagsApi.delete(statement.id, tagName);
      onTagsChanged?.();
    } catch (error: any) {
      toast.error(error.message || 'Failed to delete tag');
    }
  };

  return (
    <div
      className="statement-row"
      onClick={() => navigate(`/statement/${statement.id}`)}
    >
      <span className="statement-row-title">{statement.title}</span>
      <div className="statement-row-tags" onClick={(e) => e.stopPropagation()}>
        {statement.tags?.map((tag) => (
          <span
            key={tag}
            className="tag-pill"
            onClick={(e) => {
              e.stopPropagation();
              onTagClick?.(tag);
            }}
          >
            {tag}
            {user?.is_admin && (
              <span
                className="tag-delete"
                onClick={(e) => handleDeleteTag(e, tag)}
              >
                &times;
              </span>
            )}
          </span>
        ))}
        {user && !showTagInput && (
          <span
            className="tag-pill tag-add"
            onClick={(e) => {
              e.stopPropagation();
              setShowTagInput(true);
            }}
          >
            + Tag
          </span>
        )}
        {showTagInput && (
          <TagInput
            onSubmit={handleAddTag}
            onCancel={() => setShowTagInput(false)}
          />
        )}
      </div>
      <span className="statement-row-meta">
        <Link to={`/user/${statement.submitter.username}`} onClick={(e) => e.stopPropagation()} className="username-link">{statement.submitter.username}</Link>
        <span className="statement-row-time">{formatTimeAgo(statement.created_at)}</span>
      </span>
      {statement.is_solved && statement.solver ? (
        <span className={`prize-badge ${statement.is_disproved ? 'disproved' : 'solved'}`}>
          {statement.is_disproved ? 'Disproved' : 'Proved'}
        </span>
      ) : statement.current_prize ? (
        <span className="prize-badge">{statement.current_prize} pts</span>
      ) : null}
    </div>
  );
}
