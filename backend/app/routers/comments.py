from fastapi import APIRouter, Depends, HTTPException, Query, status
from sqlalchemy.orm import Session, joinedload
from typing import List
from uuid import UUID
from datetime import datetime
from ..database import get_db
from ..models import User, Statement, Comment
from ..schemas import CommentCreate, CommentUpdate, CommentResponse, PaginatedComments
from ..auth import get_current_user, get_current_approved_user
from ..prize import get_prize_settings

router = APIRouter(prefix="/api", tags=["comments"])


@router.get("/comments/recent", response_model=PaginatedComments)
def recent_comments(
    offset: int = Query(0, ge=0),
    limit: int = Query(20, ge=1, le=50),
    db: Session = Depends(get_db),
    current_user: User = Depends(get_current_user),
):
    settings = get_prize_settings(db)
    gatekeeper_username = settings.get("gatekeeper_username", "admin")
    gatekeeper_user = db.query(User).filter(User.username == gatekeeper_username).first()

    base_query = (
        db.query(Comment)
        .join(Statement, Comment.statement_id == Statement.id)
        .filter(Statement.is_archived == False)
    )
    if gatekeeper_user:
        base_query = base_query.filter(Comment.author_id != gatekeeper_user.id)

    total = base_query.count()

    items = (
        base_query
        .options(joinedload(Comment.author), joinedload(Comment.statement))
        .order_by(Comment.created_at.desc())
        .offset(offset)
        .limit(limit)
        .all()
    )

    return PaginatedComments(items=items, total=total, offset=offset, limit=limit)


@router.get("/statements/{statement_id}/comments", response_model=List[CommentResponse])
def list_comments(
    statement_id: UUID,
    db: Session = Depends(get_db),
    current_user: User = Depends(get_current_user),
):
    statement = db.query(Statement).filter(Statement.id == statement_id).first()
    if not statement:
        raise HTTPException(status_code=404, detail="Statement not found")

    comments = (
        db.query(Comment)
        .filter(Comment.statement_id == statement_id)
        .order_by(Comment.created_at.asc())
        .all()
    )
    return comments


@router.post("/statements/{statement_id}/comments", response_model=CommentResponse)
def create_comment(
    statement_id: UUID,
    data: CommentCreate,
    db: Session = Depends(get_db),
    current_user: User = Depends(get_current_approved_user),
):
    statement = db.query(Statement).filter(Statement.id == statement_id).first()
    if not statement:
        raise HTTPException(status_code=404, detail="Statement not found")

    if not data.content.strip():
        raise HTTPException(status_code=400, detail="Comment content cannot be empty")

    comment = Comment(
        content=data.content.strip(),
        statement_id=statement_id,
        author_id=current_user.id,
    )
    db.add(comment)
    db.commit()
    db.refresh(comment)
    return comment


@router.put("/comments/{comment_id}", response_model=CommentResponse)
def update_comment(
    comment_id: UUID,
    data: CommentUpdate,
    db: Session = Depends(get_db),
    current_user: User = Depends(get_current_approved_user),
):
    comment = db.query(Comment).filter(Comment.id == comment_id).first()
    if not comment:
        raise HTTPException(status_code=404, detail="Comment not found")

    if comment.author_id != current_user.id and not current_user.is_admin:
        raise HTTPException(status_code=403, detail="Not authorized to edit this comment")

    if not data.content.strip():
        raise HTTPException(status_code=400, detail="Comment content cannot be empty")

    comment.content = data.content.strip()
    comment.updated_at = datetime.utcnow()
    db.commit()
    db.refresh(comment)
    return comment


@router.delete("/comments/{comment_id}")
def delete_comment(
    comment_id: UUID,
    db: Session = Depends(get_db),
    current_user: User = Depends(get_current_approved_user),
):
    comment = db.query(Comment).filter(Comment.id == comment_id).first()
    if not comment:
        raise HTTPException(status_code=404, detail="Comment not found")

    if not current_user.is_admin:
        raise HTTPException(status_code=403, detail="Only admins can delete comments")

    db.delete(comment)
    db.commit()
    return {"message": "Comment deleted"}
