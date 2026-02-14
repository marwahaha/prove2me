from fastapi import APIRouter, Depends, HTTPException, status, Query
from sqlalchemy.orm import Session
from sqlalchemy import func
from uuid import UUID
from ..database import get_db
from ..models import User, Statement, Tag
from ..schemas import TagCreate
from ..auth import get_current_approved_user

router = APIRouter(tags=["tags"])


@router.post("/api/statements/{statement_id}/tags")
def create_tag(
    statement_id: UUID,
    tag_data: TagCreate,
    current_user: User = Depends(get_current_approved_user),
    db: Session = Depends(get_db),
):
    """Add a tag to a statement."""
    tag_name = tag_data.tag_name.strip()
    if not tag_name:
        raise HTTPException(status_code=status.HTTP_400_BAD_REQUEST, detail="Tag name cannot be empty")
    if len(tag_name) > 30:
        raise HTTPException(status_code=status.HTTP_400_BAD_REQUEST, detail="Tag name must be 30 characters or less")

    statement = db.query(Statement).filter(Statement.id == statement_id).first()
    if not statement:
        raise HTTPException(status_code=status.HTTP_404_NOT_FOUND, detail="Statement not found")

    existing = db.query(Tag).filter(
        Tag.statement_id == statement_id,
        func.lower(Tag.tag_name) == tag_name.lower(),
    ).first()
    if existing:
        raise HTTPException(status_code=status.HTTP_409_CONFLICT, detail="Tag already exists on this statement")

    tag = Tag(
        statement_id=statement_id,
        tag_name=tag_name,
        tagger_id=current_user.id,
    )
    db.add(tag)
    db.commit()

    return {"tag_name": tag.tag_name}


@router.delete("/api/statements/{statement_id}/tags/{tag_name}")
def delete_tag(
    statement_id: UUID,
    tag_name: str,
    current_user: User = Depends(get_current_approved_user),
    db: Session = Depends(get_db),
):
    """Delete a tag. Admin only."""
    if not current_user.is_admin:
        raise HTTPException(status_code=status.HTTP_403_FORBIDDEN, detail="Admin access required")

    tag = db.query(Tag).filter(
        Tag.statement_id == statement_id,
        func.lower(Tag.tag_name) == tag_name.lower(),
    ).first()
    if not tag:
        raise HTTPException(status_code=status.HTTP_404_NOT_FOUND, detail="Tag not found")

    db.delete(tag)
    db.commit()
    return {"message": "Tag deleted"}


@router.get("/api/tags/autocomplete")
def autocomplete_tags(
    q: str = Query("", min_length=0),
    db: Session = Depends(get_db),
):
    """Return distinct tag names matching prefix."""
    if not q.strip():
        return []
    results = (
        db.query(Tag.tag_name)
        .filter(func.lower(Tag.tag_name).startswith(q.lower()))
        .distinct()
        .limit(10)
        .all()
    )
    return sorted([r[0] for r in results], key=str.lower)
