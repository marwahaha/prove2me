function parseDate(dateString: string): Date {
  // Backend stores UTC but serializes without timezone suffix; ensure JS parses as UTC
  return new Date(dateString.endsWith('Z') ? dateString : dateString + 'Z');
}

export function formatTimeAgo(dateString: string): string {
  const date = parseDate(dateString);
  const now = new Date();
  const seconds = Math.floor((now.getTime() - date.getTime()) / 1000);

  if (seconds < 60) return 'just now';
  if (seconds < 3600) return `${Math.floor(seconds / 60)}m ago`;
  if (seconds < 86400) return `${Math.floor(seconds / 3600)}h ago`;
  return `${Math.floor(seconds / 86400)}d ago`;
}

export function formatTimeUntil(dateString: string): string {
  const date = parseDate(dateString);
  const now = new Date();
  const seconds = Math.floor((date.getTime() - now.getTime()) / 1000);

  if (seconds <= 0) return 'shortly';
  if (seconds < 3600) return `in ${Math.ceil(seconds / 60)} minute${Math.ceil(seconds / 60) === 1 ? '' : 's'}`;
  if (seconds < 86400) return `in ${Math.floor(seconds / 3600)} hour${Math.floor(seconds / 3600) === 1 ? '' : 's'}`;
  return `in ${Math.floor(seconds / 86400)} day${Math.floor(seconds / 86400) === 1 ? '' : 's'}`;
}

export function formatExactTime(dateString: string): string {
  return parseDate(dateString).toLocaleString();
}
