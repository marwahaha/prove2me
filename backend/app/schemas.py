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


# Tag schemas
class TagCreate(BaseModel):
    tag_name: str


class TagResponse(BaseModel):
    id: UUID
    tag_name: str
    tagger: UserPublic
    created_at: datetime
    is_privileged: bool = False

    class Config:
        from_attributes = True


# Statement schemas
class StatementCreate(BaseModel):
    title: str
    definitions: Optional[str] = None
    lean_code: str


class StatementResponse(BaseModel):
    id: UUID
    title: str
    definitions: Optional[str] = None
    lean_code: str
    submitter: UserPublic
    is_solved: bool
    solved_at: Optional[datetime]
    solver: Optional[UserPublic]
    proof_code: Optional[str] = None
    proof_imports: Optional[str] = None
    proof_theorem_name: Optional[str] = None
    created_at: datetime
    current_prize: Optional[int] = None
    tags: list[str] = []

    class Config:
        from_attributes = True


class StatementListItem(BaseModel):
    id: UUID
    title: str
    submitter: UserPublic
    is_solved: bool
    solver: Optional[UserPublic] = None
    created_at: datetime
    solved_at: Optional[datetime] = None
    current_prize: Optional[int] = None
    tags: list[str] = []

    class Config:
        from_attributes = True


# Proof schemas
class ProofSubmit(BaseModel):
    lean_code: str
    theorem_name: str
    imports: Optional[str] = None


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
class PasswordReset(BaseModel):
    new_password: str


class SettingsResponse(BaseModel):
    base_points: int
    growth_rate: float
    submitter_share: float
    max_statements_per_day: int


class SettingsUpdate(BaseModel):
    base_points: Optional[int] = None
    growth_rate: Optional[float] = None
    submitter_share: Optional[float] = None
    max_statements_per_day: Optional[int] = None


class StatementTitleUpdate(BaseModel):
    title: str


class BannerResponse(BaseModel):
    message: str


class BannerUpdate(BaseModel):
    message: str


# Comment schemas
class CommentCreate(BaseModel):
    content: str


class CommentUpdate(BaseModel):
    content: str


class CommentResponse(BaseModel):
    id: UUID
    content: str
    author: UserPublic
    created_at: datetime
    updated_at: Optional[datetime] = None

    class Config:
        from_attributes = True


# Compile result
class CompileResult(BaseModel):
    success: bool
    error: Optional[str] = None
