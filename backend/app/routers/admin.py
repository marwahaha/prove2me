from fastapi import APIRouter, Depends, HTTPException, status
from sqlalchemy.orm import Session
from sqlalchemy import desc
from typing import List
from uuid import UUID
from ..database import get_db
from ..models import User, Statement
from ..schemas import UserResponse, SettingsResponse, SettingsUpdate, StatementListItem
from ..auth import get_current_admin
from ..prize import get_prize_settings, set_prize_setting

router = APIRouter(prefix="/api/admin", tags=["admin"])


@router.get("/pending-users", response_model=List[UserResponse])
def get_pending_users(
    current_user: User = Depends(get_current_admin),
    db: Session = Depends(get_db)
):
    """Get list of users awaiting approval."""
    users = db.query(User).filter(
        User.is_approved == False
    ).order_by(desc(User.created_at)).all()

    return users


@router.post("/approve-user/{user_id}", response_model=UserResponse)
def approve_user(
    user_id: UUID,
    current_user: User = Depends(get_current_admin),
    db: Session = Depends(get_db)
):
    """Approve a pending user."""
    user = db.query(User).filter(User.id == user_id).first()

    if not user:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="User not found"
        )

    if user.is_approved:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail="User is already approved"
        )

    user.is_approved = True
    db.commit()
    db.refresh(user)

    return user


@router.delete("/reject-user/{user_id}")
def reject_user(
    user_id: UUID,
    current_user: User = Depends(get_current_admin),
    db: Session = Depends(get_db)
):
    """Reject and delete a pending user."""
    user = db.query(User).filter(User.id == user_id).first()

    if not user:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="User not found"
        )

    if user.is_approved:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail="Cannot reject an approved user"
        )

    db.delete(user)
    db.commit()

    return {"message": "User rejected and deleted"}


@router.get("/settings", response_model=SettingsResponse)
def get_settings(
    current_user: User = Depends(get_current_admin),
    db: Session = Depends(get_db)
):
    """Get prize settings."""
    settings = get_prize_settings(db)
    return SettingsResponse(**settings)


@router.put("/settings", response_model=SettingsResponse)
def update_settings(
    settings_data: SettingsUpdate,
    current_user: User = Depends(get_current_admin),
    db: Session = Depends(get_db)
):
    """Update prize settings."""
    if settings_data.base_points is not None:
        if settings_data.base_points < 1:
            raise HTTPException(
                status_code=status.HTTP_400_BAD_REQUEST,
                detail="base_points must be at least 1"
            )
        set_prize_setting(db, "base_points", settings_data.base_points)

    if settings_data.growth_rate is not None:
        if settings_data.growth_rate < 1.0:
            raise HTTPException(
                status_code=status.HTTP_400_BAD_REQUEST,
                detail="growth_rate must be at least 1.0"
            )
        set_prize_setting(db, "growth_rate", settings_data.growth_rate)

    if settings_data.submitter_share is not None:
        if not 0 <= settings_data.submitter_share <= 1:
            raise HTTPException(
                status_code=status.HTTP_400_BAD_REQUEST,
                detail="submitter_share must be between 0 and 1"
            )
        set_prize_setting(db, "submitter_share", settings_data.submitter_share)

    settings = get_prize_settings(db)
    return SettingsResponse(**settings)


@router.get("/all-statements", response_model=List[StatementListItem])
def get_all_statements(
    current_user: User = Depends(get_current_admin),
    db: Session = Depends(get_db)
):
    """Get all statements (solved and unsolved)."""
    from ..prize import calculate_prize

    statements = db.query(Statement).order_by(desc(Statement.created_at)).all()
    settings = get_prize_settings(db)

    result = []
    for s in statements:
        prize = calculate_prize(s.created_at, settings) if not s.is_solved else None
        result.append({
            "id": s.id,
            "title": s.title,
            "submitter": s.submitter,
            "is_solved": s.is_solved,
            "created_at": s.created_at,
            "current_prize": prize,
        })

    return result


@router.get("/users", response_model=List[UserResponse])
def get_all_users(
    current_user: User = Depends(get_current_admin),
    db: Session = Depends(get_db)
):
    """Get all users."""
    users = db.query(User).order_by(desc(User.created_at)).all()
    return users
