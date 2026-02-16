from fastapi import APIRouter, Depends, HTTPException, status
from sqlalchemy.orm import Session, joinedload
from sqlalchemy import desc
from typing import List
from ..database import get_db
from ..models import User, Statement, Tag
from ..schemas import UserProfileResponse, StatementListItem
from .statements import add_current_prize_list_item

router = APIRouter(prefix="/api/users", tags=["users"])


@router.get("/{username}", response_model=UserProfileResponse)
def get_user_profile(username: str, db: Session = Depends(get_db)):
    """Get a user's public profile by username."""
    user = db.query(User).filter(
        User.username == username,
        User.is_approved == True,
    ).first()

    if not user:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="User not found"
        )

    submitted_count = db.query(Statement).filter(
        Statement.submitter_id == user.id,
        Statement.is_archived == False,
    ).count()

    solved_count = db.query(Statement).filter(
        Statement.solver_id == user.id,
    ).count()

    return {
        "username": user.username,
        "points": user.points,
        "created_at": user.created_at,
        "submitted_count": submitted_count,
        "solved_count": solved_count,
    }


@router.get("/{username}/statements", response_model=List[StatementListItem])
def get_user_statements(username: str, db: Session = Depends(get_db)):
    """Get statements submitted by a user."""
    user = db.query(User).filter(
        User.username == username,
        User.is_approved == True,
    ).first()

    if not user:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="User not found"
        )

    statements = db.query(Statement).options(
        joinedload(Statement.tags).joinedload(Tag.tagger)
    ).filter(
        Statement.submitter_id == user.id,
        Statement.is_archived == False,
    ).order_by(desc(Statement.created_at)).all()

    return [add_current_prize_list_item(s, db) for s in statements]


@router.get("/{username}/solved", response_model=List[StatementListItem])
def get_user_solved(username: str, db: Session = Depends(get_db)):
    """Get statements solved by a user."""
    user = db.query(User).filter(
        User.username == username,
        User.is_approved == True,
    ).first()

    if not user:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="User not found"
        )

    statements = db.query(Statement).options(
        joinedload(Statement.tags).joinedload(Tag.tagger)
    ).filter(
        Statement.solver_id == user.id,
    ).order_by(desc(Statement.solved_at)).all()

    return [add_current_prize_list_item(s, db) for s in statements]
