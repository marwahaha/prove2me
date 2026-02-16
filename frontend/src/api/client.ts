const API_BASE = '/api';

export interface User {
  id: string;
  username: string;
  email: string;
  points: number;
  is_admin: boolean;
  is_approved: boolean;
  created_at: string;
}

export interface UserPublic {
  id: string;
  username: string;
  points: number;
}

export interface Statement {
  id: string;
  title: string;
  definitions: string | null;
  lean_code: string;
  submitter: UserPublic;
  is_solved: boolean;
  solved_at: string | null;
  solver: UserPublic | null;
  proof_code: string | null;
  proof_imports: string | null;
  proof_theorem_name: string | null;
  created_at: string;
  updated_at: string | null;
  last_edited_by: UserPublic | null;
  current_prize: number | null;
  tags: string[];
}

export interface StatementListItem {
  id: string;
  title: string;
  submitter: UserPublic;
  is_solved: boolean;
  solver: UserPublic | null;
  created_at: string;
  solved_at: string | null;
  current_prize: number | null;
  tags: string[];
}

export interface LeaderboardEntry {
  rank: number;
  username: string;
  points: number;
}

export interface ProofResult {
  success: boolean;
  message: string;
  points_earned: number | null;
}

export interface CompileResult {
  success: boolean;
  error: string | null;
}

export interface Comment {
  id: string;
  content: string;
  author: UserPublic;
  created_at: string;
  updated_at: string | null;
}

export interface PrizeSettings {
  base_points: number;
  growth_rate: number;
  submitter_share: number;
  max_statements_per_day: number;
  min_proofs_to_submit: number;
}

class ApiError extends Error {
  constructor(public status: number, message: string) {
    super(message);
    this.name = 'ApiError';
  }
}

async function request<T>(
  endpoint: string,
  options: RequestInit = {}
): Promise<T> {
  const response = await fetch(`${API_BASE}${endpoint}`, {
    ...options,
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      ...options.headers,
    },
  });

  if (!response.ok) {
    const data = await response.json().catch(() => ({}));
    throw new ApiError(response.status, data.detail || 'An error occurred');
  }

  return response.json();
}

// Auth API
export const authApi = {
  register: (username: string, email: string, password: string) =>
    request<User>('/auth/register', {
      method: 'POST',
      body: JSON.stringify({ username, email, password }),
    }),

  login: (username: string, password: string) =>
    request<User>('/auth/login', {
      method: 'POST',
      body: JSON.stringify({ username, password }),
    }),

  logout: () =>
    request<{ message: string }>('/auth/logout', { method: 'POST' }),

  me: () => request<User>('/auth/me'),
};

// Statements API
export const statementsApi = {
  list: (sortBy: 'newest' | 'prize' = 'newest', tags?: string[]) => {
    const params = new URLSearchParams({ sort_by: sortBy });
    if (tags && tags.length > 0) params.set('tags', tags.join(','));
    return request<StatementListItem[]>(`/statements?${params.toString()}`);
  },

  listSolved: (tags?: string[]) => {
    const params = new URLSearchParams();
    if (tags && tags.length > 0) params.set('tags', tags.join(','));
    const qs = params.toString();
    return request<StatementListItem[]>(`/statements/all-solved${qs ? '?' + qs : ''}`);
  },

  get: (id: string) => request<Statement>(`/statements/${id}`),

  create: (title: string, lean_code: string, definitions?: string) =>
    request<Statement>('/statements', {
      method: 'POST',
      body: JSON.stringify({ title, lean_code, definitions }),
    }),

  my: () => request<StatementListItem[]>('/statements/my'),

  solvedByMe: () => request<StatementListItem[]>('/statements/solved'),

  archive: (id: string) =>
    request<{ message: string }>(`/statements/${id}/archive`, { method: 'POST' }),

  compile: (title: string, lean_code: string, definitions?: string) =>
    request<CompileResult>('/statements/compile', {
      method: 'POST',
      body: JSON.stringify({ title, lean_code, definitions }),
    }),
};

// Proofs API
export const proofsApi = {
  submit: (statementId: string, lean_code: string, theorem_name: string, imports?: string) =>
    request<ProofResult>(`/proofs/${statementId}`, {
      method: 'POST',
      body: JSON.stringify({ lean_code, theorem_name, imports }),
    }),
};

// Leaderboard API
export const leaderboardApi = {
  get: () => request<LeaderboardEntry[]>('/leaderboard'),
};

// Banner API (public)
export const bannerApi = {
  get: () => request<{ message: string }>('/admin/banner'),
};

// Admin API
export const adminApi = {
  getPendingUsers: () => request<User[]>('/admin/pending-users'),

  approveUser: (userId: string) =>
    request<User>(`/admin/approve-user/${userId}`, { method: 'POST' }),

  rejectUser: (userId: string) =>
    request<{ message: string }>(`/admin/reject-user/${userId}`, {
      method: 'DELETE',
    }),

  resetPassword: (userId: string, newPassword: string) =>
    request<User>(`/admin/reset-password/${userId}`, {
      method: 'POST',
      body: JSON.stringify({ new_password: newPassword }),
    }),

  getSettings: () => request<PrizeSettings>('/admin/settings'),

  updateSettings: (settings: Partial<PrizeSettings>) =>
    request<PrizeSettings>('/admin/settings', {
      method: 'PUT',
      body: JSON.stringify(settings),
    }),

  getAllStatements: () => request<StatementListItem[]>('/admin/all-statements'),

  getAllUsers: () => request<User[]>('/admin/users'),

  toggleAdmin: (userId: string) =>
    request<User>(`/admin/toggle-admin/${userId}`, { method: 'POST' }),

  setBanner: (message: string) =>
    request<{ message: string }>('/admin/banner', {
      method: 'PUT',
      body: JSON.stringify({ message }),
    }),

  updateStatementTitle: (statementId: string, title: string) =>
    request<{ message: string }>(`/admin/statements/${statementId}/title`, {
      method: 'PUT',
      body: JSON.stringify({ title }),
    }),

  updateStatementContent: (statementId: string, lean_code: string, definitions?: string | null) =>
    request<{ message: string }>(`/admin/statements/${statementId}/content`, {
      method: 'PUT',
      body: JSON.stringify({ lean_code, definitions }),
    }),
};

// Comments API
export const commentsApi = {
  list: (statementId: string) =>
    request<Comment[]>(`/statements/${statementId}/comments`),

  create: (statementId: string, content: string) =>
    request<Comment>(`/statements/${statementId}/comments`, {
      method: 'POST',
      body: JSON.stringify({ content }),
    }),

  update: (commentId: string, content: string) =>
    request<Comment>(`/comments/${commentId}`, {
      method: 'PUT',
      body: JSON.stringify({ content }),
    }),

  delete: (commentId: string) =>
    request<{ message: string }>(`/comments/${commentId}`, {
      method: 'DELETE',
    }),
};

// Tags API
export const tagsApi = {
  create: (statementId: string, tagName: string) =>
    request<{ tag_name: string }>(`/statements/${statementId}/tags`, {
      method: 'POST',
      body: JSON.stringify({ tag_name: tagName }),
    }),

  delete: (statementId: string, tagName: string) =>
    request<{ message: string }>(`/statements/${statementId}/tags/${encodeURIComponent(tagName)}`, {
      method: 'DELETE',
    }),

  autocomplete: (query: string) =>
    request<string[]>(`/tags/autocomplete?q=${encodeURIComponent(query)}`),
};

export { ApiError };
