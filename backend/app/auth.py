from datetime import datetime, timedelta
from typing import Optional
from uuid import UUID
import bcrypt
from jose import JWTError, jwt
from fastapi import Depends, HTTPException, status, Request, Response
from fastapi.security import APIKeyCookie
from sqlalchemy.orm import Session
from .database import get_db
from .models import User
from .config import get_settings

settings = get_settings()

ALGORITHM = "HS256"
SESSION_EXPIRE_DAYS = 7
COOKIE_NAME = "session_token"

cookie_scheme = APIKeyCookie(name=COOKIE_NAME, auto_error=False)


def hash_password(password: str) -> str:
    return bcrypt.hashpw(password.encode(), bcrypt.gensalt()).decode()


def verify_password(password: str, password_hash: str) -> bool:
    return bcrypt.checkpw(password.encode(), password_hash.encode())


def create_session_token(user_id: UUID) -> str:
    expire = datetime.utcnow() + timedelta(days=SESSION_EXPIRE_DAYS)
    data = {"sub": str(user_id), "exp": expire}
    return jwt.encode(data, settings.secret_key, algorithm=ALGORITHM)


def decode_session_token(token: str) -> Optional[UUID]:
    try:
        payload = jwt.decode(token, settings.secret_key, algorithms=[ALGORITHM])
        user_id = payload.get("sub")
        if user_id is None:
            return None
        return UUID(user_id)
    except JWTError:
        return None


def set_session_cookie(response: Response, token: str):
    response.set_cookie(
        key=COOKIE_NAME,
        value=token,
        httponly=True,
        max_age=SESSION_EXPIRE_DAYS * 24 * 60 * 60,
        samesite="lax",
        secure=False,  # Set to True in production with HTTPS
    )


def clear_session_cookie(response: Response):
    response.delete_cookie(key=COOKIE_NAME)


async def get_current_user(
    token: Optional[str] = Depends(cookie_scheme),
    db: Session = Depends(get_db)
) -> User:
    if not token:
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Not authenticated"
        )

    user_id = decode_session_token(token)
    if user_id is None:
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Invalid session"
        )

    user = db.query(User).filter(User.id == user_id).first()
    if user is None:
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="User not found"
        )

    return user


async def get_current_approved_user(
    current_user: User = Depends(get_current_user)
) -> User:
    if not current_user.is_approved:
        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="Account not approved yet"
        )
    return current_user


async def get_current_admin(
    current_user: User = Depends(get_current_approved_user)
) -> User:
    if not current_user.is_admin:
        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="Admin access required"
        )
    return current_user


async def get_optional_user(
    token: Optional[str] = Depends(cookie_scheme),
    db: Session = Depends(get_db)
) -> Optional[User]:
    if not token:
        return None

    user_id = decode_session_token(token)
    if user_id is None:
        return None

    return db.query(User).filter(User.id == user_id).first()
