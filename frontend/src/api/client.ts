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
  proof_theorem_name: string | null;
  created_at: string;
  current_prize: number | null;
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

export interface PrizeSettings {
  base_points: number;
  growth_rate: number;
  submitter_share: number;
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
  list: (sortBy: 'newest' | 'prize' = 'newest') =>
    request<StatementListItem[]>(`/statements?sort_by=${sortBy}`),

  listSolved: () => request<StatementListItem[]>('/statements/all-solved'),

  get: (id: string) => request<Statement>(`/statements/${id}`),

  create: (title: string, lean_code: string, definitions?: string) =>
    request<Statement>('/statements', {
      method: 'POST',
      body: JSON.stringify({ title, lean_code, definitions }),
    }),

  my: () => request<StatementListItem[]>('/statements/my'),

  solvedByMe: () => request<StatementListItem[]>('/statements/solved'),

  compile: (title: string, lean_code: string, definitions?: string) =>
    request<CompileResult>('/statements/compile', {
      method: 'POST',
      body: JSON.stringify({ title, lean_code, definitions }),
    }),
};

// Proofs API
export const proofsApi = {
  submit: (statementId: string, lean_code: string, theorem_name: string) =>
    request<ProofResult>(`/proofs/${statementId}`, {
      method: 'POST',
      body: JSON.stringify({ lean_code, theorem_name }),
    }),
};

// Leaderboard API
export const leaderboardApi = {
  get: () => request<LeaderboardEntry[]>('/leaderboard'),
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

  getSettings: () => request<PrizeSettings>('/admin/settings'),

  updateSettings: (settings: Partial<PrizeSettings>) =>
    request<PrizeSettings>('/admin/settings', {
      method: 'PUT',
      body: JSON.stringify(settings),
    }),

  getAllStatements: () => request<StatementListItem[]>('/admin/all-statements'),

  getAllUsers: () => request<User[]>('/admin/users'),
};

export { ApiError };
