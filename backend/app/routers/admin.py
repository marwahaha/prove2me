from fastapi import APIRouter, Depends, HTTPException, status
from sqlalchemy.orm import Session
from sqlalchemy import desc
from typing import List
from uuid import UUID
from ..database import get_db
from ..models import User, Statement, Setting
from ..schemas import UserResponse, SettingsResponse, SettingsUpdate, StatementListItem, PasswordReset, BannerResponse, BannerUpdate, StatementTitleUpdate, StatementContentUpdate, StatementResponse
from ..auth import get_current_admin, hash_password
from ..prize import get_prize_settings, set_prize_setting
import json

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


@router.post("/reset-password/{user_id}", response_model=UserResponse)
def reset_password(
    user_id: UUID,
    password_data: PasswordReset,
    current_user: User = Depends(get_current_admin),
    db: Session = Depends(get_db)
):
    """Reset a user's password."""
    user = db.query(User).filter(User.id == user_id).first()

    if not user:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="User not found"
        )

    if len(password_data.new_password) < 6:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail="Password must be at least 6 characters"
        )

    user.password_hash = hash_password(password_data.new_password)
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

    if settings_data.max_statements_per_day is not None:
        if settings_data.max_statements_per_day < 1:
            raise HTTPException(
                status_code=status.HTTP_400_BAD_REQUEST,
                detail="max_statements_per_day must be at least 1"
            )
        set_prize_setting(db, "max_statements_per_day", settings_data.max_statements_per_day)

    if settings_data.min_proofs_to_submit is not None:
        if settings_data.min_proofs_to_submit < 0:
            raise HTTPException(
                status_code=status.HTTP_400_BAD_REQUEST,
                detail="min_proofs_to_submit must be at least 0"
            )
        set_prize_setting(db, "min_proofs_to_submit", settings_data.min_proofs_to_submit)

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


@router.post("/toggle-admin/{user_id}", response_model=UserResponse)
def toggle_admin(
    user_id: UUID,
    current_user: User = Depends(get_current_admin),
    db: Session = Depends(get_db)
):
    """Toggle admin status for a user."""
    if str(current_user.id) == str(user_id):
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail="Cannot change your own admin status"
        )

    user = db.query(User).filter(User.id == user_id).first()

    if not user:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="User not found"
        )

    user.is_admin = not user.is_admin
    db.commit()
    db.refresh(user)

    return user


@router.get("/banner", response_model=BannerResponse)
def get_banner(db: Session = Depends(get_db)):
    """Get the site-wide banner message. Public endpoint, no auth required."""
    setting = db.query(Setting).filter(Setting.key == "banner_message").first()
    message = json.loads(setting.value) if setting else ""
    return BannerResponse(message=message)


@router.put("/banner", response_model=BannerResponse)
def set_banner(
    banner: BannerUpdate,
    current_user: User = Depends(get_current_admin),
    db: Session = Depends(get_db),
):
    """Set the site-wide banner message. Admin only."""
    set_prize_setting(db, "banner_message", banner.message)
    return BannerResponse(message=banner.message)


@router.put("/statements/{statement_id}/title")
def update_statement_title(
    statement_id: UUID,
    data: StatementTitleUpdate,
    current_user: User = Depends(get_current_admin),
    db: Session = Depends(get_db),
):
    """Update a statement's title. Admin only."""
    statement = db.query(Statement).filter(Statement.id == statement_id).first()
    if not statement:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="Statement not found",
        )
    if not data.title.strip():
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail="Title cannot be empty",
        )
    from datetime import datetime

    statement.title = data.title.strip()
    statement.updated_at = datetime.utcnow()
    statement.last_edited_by_id = current_user.id
    db.commit()
    return {"message": "Title updated"}


@router.put("/statements/{statement_id}/content")
def update_statement_content(
    statement_id: UUID,
    data: StatementContentUpdate,
    current_user: User = Depends(get_current_admin),
    db: Session = Depends(get_db),
):
    """Update a statement's definitions and proposition. Admin only."""
    from ..lean_runner import compile_statement

    statement = db.query(Statement).filter(Statement.id == statement_id).first()
    if not statement:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="Statement not found",
        )
    if statement.is_solved:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail="Cannot edit a solved statement",
        )

    success, error = compile_statement(data.lean_code, data.definitions)
    if not success:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail=f"Lean compilation failed: {error}",
        )

    from datetime import datetime

    statement.definitions = data.definitions
    statement.lean_code = data.lean_code
    statement.updated_at = datetime.utcnow()
    statement.last_edited_by_id = current_user.id
    db.commit()
    return {"message": "Statement content updated"}
