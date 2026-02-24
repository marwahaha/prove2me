import { useState, useEffect } from 'react';
import { Link } from 'react-router-dom';
import ReactMarkdown from 'react-markdown';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import { commentsApi, RecentComment } from '../api/client';
import { formatTimeAgo, formatExactTime } from '../utils/time';

const PAGE_SIZE = 5;
const PREVIEW_LINES = 3;

function truncateComment(content: string): { text: string; truncated: boolean } {
  const lines = content.split('\n');
  if (lines.length <= PREVIEW_LINES) return { text: content, truncated: false };
  return { text: lines.slice(0, PREVIEW_LINES).join('\n'), truncated: true };
}

export default function RecentComments() {
  const [comments, setComments] = useState<RecentComment[]>([]);
  const [total, setTotal] = useState(0);
  const [offset, setOffset] = useState(0);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    loadComments();
  }, [offset]);

  const loadComments = async () => {
    setLoading(true);
    try {
      const data = await commentsApi.recent(offset, PAGE_SIZE);
      setComments(data.items);
      setTotal(data.total);
    } catch {
      // non-critical
    } finally {
      setLoading(false);
    }
  };

  if (!loading && total === 0) return null;

  const start = offset + 1;
  const end = Math.min(offset + PAGE_SIZE, total);
  const hasNewer = offset > 0;
  const hasOlder = offset + PAGE_SIZE < total;

  return (
    <div style={{ marginTop: '30px' }}>
      <h2 className="page-title" style={{ fontSize: '1.4rem', marginBottom: '15px' }}>
        Recent Discussion
      </h2>

      {loading ? (
        <div className="loading">Loading comments...</div>
      ) : (
        <div className="recent-comments">
          {comments.map((comment) => (
            <div key={comment.id} className="recent-comment-row">
              <div className="recent-comment-body">
                <ReactMarkdown remarkPlugins={[remarkMath]} rehypePlugins={[rehypeKatex]}>
                  {truncateComment(comment.content).text}
                </ReactMarkdown>
              </div>
              <div className="recent-comment-meta">
                <Link to={`/user/${comment.author.username}`} className="username-link">
                  {comment.author.username}
                </Link>
                {' on '}
                <Link to={`/statement/${comment.statement.id}`} className="recent-comment-statement">
                  {comment.statement.title}
                </Link>
                <span className="recent-comment-time" title={formatExactTime(comment.created_at)}>{formatTimeAgo(comment.created_at)}</span>
              </div>
            </div>
          ))}

          {total > PAGE_SIZE && (
            <div className="recent-comments-pagination">
              <button
                className="btn btn-secondary btn-small"
                disabled={!hasNewer}
                onClick={() => setOffset(Math.max(0, offset - PAGE_SIZE))}
              >
                Newer
              </button>
              <span className="recent-comments-range">
                {start}–{end} of {total}
              </span>
              <button
                className="btn btn-secondary btn-small"
                disabled={!hasOlder}
                onClick={() => setOffset(offset + PAGE_SIZE)}
              >
                Older
              </button>
            </div>
          )}
        </div>
      )}
    </div>
  );
}
