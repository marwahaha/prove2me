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

export function formatExactTime(dateString: string): string {
  return parseDate(dateString).toLocaleString();
}
