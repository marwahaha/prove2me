import { useState, useEffect } from 'react';
import ReactMarkdown from 'react-markdown';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import 'katex/dist/katex.min.css';
import { commentsApi, Comment } from '../api/client';
import { formatTimeAgo } from '../utils/time';
import { useAuth } from '../contexts/AuthContext';
import toast from 'react-hot-toast';

interface Props {
  statementId: string;
}

export default function CommentSection({ statementId }: Props) {
  const { user } = useAuth();
  const [comments, setComments] = useState<Comment[]>([]);
  const [loading, setLoading] = useState(true);
  const [content, setContent] = useState('');
  const [posting, setPosting] = useState(false);
  const [editingId, setEditingId] = useState<string | null>(null);
  const [editContent, setEditContent] = useState('');

  useEffect(() => {
    loadComments();
  }, [statementId]);

  const loadComments = async () => {
    try {
      const data = await commentsApi.list(statementId);
      setComments(data);
    } catch {
      // silently fail - comments are non-critical
    } finally {
      setLoading(false);
    }
  };

  const handlePost = async (e: React.FormEvent) => {
    e.preventDefault();
    if (!content.trim()) return;

    setPosting(true);
    try {
      const comment = await commentsApi.create(statementId, content);
      setComments([...comments, comment]);
      setContent('');
    } catch (error: any) {
      toast.error(error.message || 'Failed to post comment');
    } finally {
      setPosting(false);
    }
  };

  const handleDelete = async (commentId: string) => {
    if (!confirm('Delete this comment?')) return;
    try {
      await commentsApi.delete(commentId);
      setComments(comments.filter((c) => c.id !== commentId));
    } catch (error: any) {
      toast.error(error.message || 'Failed to delete comment');
    }
  };

  const handleEditSave = async () => {
    if (!editingId || !editContent.trim()) return;
    try {
      const updated = await commentsApi.update(editingId, editContent);
      setComments(comments.map((c) => (c.id === editingId ? updated : c)));
      setEditingId(null);
    } catch (error: any) {
      toast.error(error.message || 'Failed to update comment');
    }
  };

  return (
    <div className="card">
      <h2 style={{ marginBottom: '20px' }}>Discussion</h2>

      {loading ? (
        <p style={{ color: '#666' }}>Loading comments...</p>
      ) : comments.length === 0 ? (
        <p style={{ color: '#666', marginBottom: '20px' }}>No comments yet. Be the first to discuss this proposition.</p>
      ) : (
        <div style={{ marginBottom: '20px' }}>
          {comments.map((comment) => (
            <div
              key={comment.id}
              style={{
                padding: '12px 0',
                borderBottom: '1px solid #eee',
              }}
            >
              {editingId === comment.id ? (
                <div>
                  <textarea
                    value={editContent}
                    onChange={(e) => setEditContent(e.target.value)}
                    rows={3}
                    style={{ width: '100%', marginBottom: '8px' }}
                  />
                  <div style={{ display: 'flex', gap: '8px' }}>
                    <button className="btn btn-success btn-small" onClick={handleEditSave}>
                      Save
                    </button>
                    <button className="btn btn-secondary btn-small" onClick={() => setEditingId(null)}>
                      Cancel
                    </button>
                  </div>
                </div>
              ) : (
                <>
                  <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', marginBottom: '4px' }}>
                    <span style={{ fontSize: '0.85rem', color: '#666' }}>
                      <strong style={{ color: '#333' }}>{comment.author.username}</strong>
                      {' · '}
                      {formatTimeAgo(comment.created_at)}
                      {comment.updated_at && ' (edited)'}
                    </span>
                    <div style={{ display: 'flex', gap: '6px' }}>
                      {(user?.is_admin || user?.id === comment.author.id) && (
                        <button
                          className="btn btn-secondary btn-small"
                          style={{ fontSize: '11px', padding: '2px 8px' }}
                          onClick={() => {
                            setEditingId(comment.id);
                            setEditContent(comment.content);
                          }}
                        >
                          Edit
                        </button>
                      )}
                      {user?.is_admin && (
                        <button
                          className="btn btn-danger btn-small"
                          style={{ fontSize: '11px', padding: '2px 8px' }}
                          onClick={() => handleDelete(comment.id)}
                        >
                          Delete
                        </button>
                      )}
                    </div>
                  </div>
                  <div className="comment-content" style={{ fontSize: '0.95rem', lineHeight: '1.5' }}>
                    <ReactMarkdown
                      remarkPlugins={[remarkMath]}
                      rehypePlugins={[rehypeKatex]}
                    >
                      {comment.content}
                    </ReactMarkdown>
                  </div>
                </>
              )}
            </div>
          ))}
        </div>
      )}

      {user?.is_approved && (
        <form onSubmit={handlePost}>
          <textarea
            value={content}
            onChange={(e) => setContent(e.target.value)}
            placeholder="Write a comment... (supports Markdown, LaTeX with $...$, and ```lean code blocks)"
            rows={3}
            style={{ width: '100%', marginBottom: '8px' }}
          />
          <button type="submit" className="btn btn-success" disabled={posting || !content.trim()}>
            {posting ? 'Posting...' : 'Post Comment'}
          </button>
        </form>
      )}
    </div>
  );
}
