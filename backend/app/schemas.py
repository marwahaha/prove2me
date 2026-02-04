from pydantic import BaseModel, EmailStr
from datetime import datetime
from uuid import UUID
from typing import Optional


# Auth schemas
class UserCreate(BaseModel):
    username: str
    email: EmailStr
    password: str


class UserLogin(BaseModel):
    username: str
    password: str


class UserResponse(BaseModel):
    id: UUID
    username: str
    email: str
    points: int
    is_admin: bool
    is_approved: bool
    created_at: datetime

    class Config:
        from_attributes = True


class UserPublic(BaseModel):
    id: UUID
    username: str
    points: int

    class Config:
        from_attributes = True


# Statement schemas
class StatementCreate(BaseModel):
    title: str
    lean_code: str


class StatementResponse(BaseModel):
    id: UUID
    title: str
    lean_code: str
    submitter: UserPublic
    is_solved: bool
    solved_at: Optional[datetime]
    solver: Optional[UserPublic]
    created_at: datetime
    current_prize: Optional[int] = None

    class Config:
        from_attributes = True


class StatementListItem(BaseModel):
    id: UUID
    title: str
    submitter: UserPublic
    is_solved: bool
    created_at: datetime
    current_prize: Optional[int] = None

    class Config:
        from_attributes = True


# Proof schemas
class ProofSubmit(BaseModel):
    lean_code: str


class ProofResult(BaseModel):
    success: bool
    message: str
    points_earned: Optional[int] = None


# Leaderboard schemas
class LeaderboardEntry(BaseModel):
    rank: int
    username: str
    points: int


# Admin schemas
class SettingsResponse(BaseModel):
    base_points: int
    growth_rate: float
    submitter_share: float


class SettingsUpdate(BaseModel):
    base_points: Optional[int] = None
    growth_rate: Optional[float] = None
    submitter_share: Optional[float] = None


# Compile result
class CompileResult(BaseModel):
    success: bool
    error: Optional[str] = None
