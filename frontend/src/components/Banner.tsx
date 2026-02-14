import { useState, useEffect } from 'react';
import { bannerApi } from '../api/client';

export default function Banner() {
  const [message, setMessage] = useState('');

  useEffect(() => {
    bannerApi.get().then((data) => setMessage(data.message)).catch(() => {});
  }, []);

  if (!message) return null;

  return (
    <div
      style={{
        background: '#e8f0fe',
        color: '#1a73e8',
        textAlign: 'center',
        padding: '8px 20px',
        fontSize: '13px',
      }}
    >
      {message}
    </div>
  );
}
