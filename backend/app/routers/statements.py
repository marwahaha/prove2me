import asyncio
from fastapi import APIRouter, Depends, HTTPException, status, Query
from sqlalchemy.orm import Session, joinedload
from sqlalchemy import desc, func
from typing import List, Optional
from uuid import UUID
from datetime import datetime, timedelta
from ..database import get_db
from ..models import User, Statement, Tag
from ..schemas import StatementCreate, StatementResponse, StatementListItem, CompileResult
from ..auth import get_current_approved_user
from ..lean_runner import compile_statement
from ..prize import get_prize_settings, calculate_prize

router = APIRouter(prefix="/api/statements", tags=["statements"])


def _build_tags(statement: Statement) -> list[str]:
    """Return sorted list of tag names."""
    tags = [tag.tag_name for tag in getattr(statement, 'tags', []) or []]
    tags.sort(key=str.lower)
    return tags


def _compute_in_holding_period(statement: Statement) -> bool:
    """Return True if statement is currently in its holding period."""
    return (
        statement.holding_period_ends_at is not None
        and statement.holding_period_ends_at > datetime.utcnow()
    )


def add_current_prize(statement: Statement, db: Session) -> dict:
    """Convert statement to dict and add current prize."""
    settings = get_prize_settings(db)
    prize = calculate_prize(statement.created_at, settings) if not statement.is_solved else None

    return {
        "id": statement.id,
        "title": statement.title,
        "definitions": statement.definitions,
        "lean_code": statement.lean_code,
        "submitter": statement.submitter,
        "is_solved": statement.is_solved,
        "is_disproved": statement.is_disproved,
        "solved_at": statement.solved_at,
        "solver": statement.solver,
        "proof_code": statement.proof_code,
        "proof_imports": statement.proof_imports,
        "proof_theorem_name": statement.proof_theorem_name,
        "created_at": statement.created_at,
        "updated_at": statement.updated_at,
        "last_edited_by": statement.last_edited_by,
        "current_prize": prize,
        "tags": _build_tags(statement),
        "holding_period_ends_at": statement.holding_period_ends_at,
        "in_holding_period": _compute_in_holding_period(statement),
    }


def add_current_prize_list_item(statement: Statement, db: Session) -> dict:
    """Convert statement to list item dict with current prize."""
    settings = get_prize_settings(db)
    prize = calculate_prize(statement.created_at, settings) if not statement.is_solved else None

    return {
        "id": statement.id,
        "title": statement.title,
        "submitter": statement.submitter,
        "is_solved": statement.is_solved,
        "is_disproved": statement.is_disproved,
        "solver": statement.solver,
        "created_at": statement.created_at,
        "solved_at": statement.solved_at,
        "current_prize": prize,
        "tags": _build_tags(statement),
        "holding_period_ends_at": statement.holding_period_ends_at,
        "in_holding_period": _compute_in_holding_period(statement),
    }


@router.get("", response_model=List[StatementListItem])
def list_statements(
    sort_by: Optional[str] = Query("newest", regex="^(newest|prize)$"),
    tags: Optional[str] = Query(None),
    db: Session = Depends(get_db)
):
    """List all unsolved statements."""
    query = db.query(Statement).options(
        joinedload(Statement.tags).joinedload(Tag.tagger)
    ).filter(Statement.is_solved == False, Statement.is_archived == False)

    if tags:
        tag_list = [t.strip().lower() for t in tags.split(",") if t.strip()]
        if tag_list:
            query = query.filter(
                Statement.tags.any(func.lower(Tag.tag_name).in_(tag_list))
            )

    if sort_by == "newest":
        query = query.order_by(desc(Statement.created_at))

    statements = query.all()

    # Convert to response with prize
    result = [add_current_prize_list_item(s, db) for s in statements]

    # Sort by prize if requested
    if sort_by == "prize":
        result.sort(key=lambda x: x["current_prize"] or 0, reverse=True)

    return result


@router.get("/all-solved", response_model=List[StatementListItem])
def list_solved_statements(
    tags: Optional[str] = Query(None),
    db: Session = Depends(get_db)
):
    """List all solved statements."""
    query = db.query(Statement).options(
        joinedload(Statement.tags).joinedload(Tag.tagger)
    ).filter(
        Statement.is_solved == True, Statement.is_archived == False
    )

    if tags:
        tag_list = [t.strip().lower() for t in tags.split(",") if t.strip()]
        if tag_list:
            query = query.filter(
                Statement.tags.any(func.lower(Tag.tag_name).in_(tag_list))
            )

    statements = query.order_by(desc(Statement.solved_at)).all()

    return [add_current_prize_list_item(s, db) for s in statements]


@router.get("/my", response_model=List[StatementListItem])
def list_my_statements(
    current_user: User = Depends(get_current_approved_user),
    db: Session = Depends(get_db)
):
    """List current user's submitted statements."""
    statements = db.query(Statement).options(
        joinedload(Statement.tags).joinedload(Tag.tagger)
    ).filter(
        Statement.submitter_id == current_user.id,
        Statement.is_archived == False,
    ).order_by(desc(Statement.created_at)).all()

    return [add_current_prize_list_item(s, db) for s in statements]


@router.get("/solved", response_model=List[StatementListItem])
def list_solved_by_me(
    current_user: User = Depends(get_current_approved_user),
    db: Session = Depends(get_db)
):
    """List statements the current user has solved (submitted proofs for)."""
    statements = db.query(Statement).options(
        joinedload(Statement.tags).joinedload(Tag.tagger)
    ).filter(
        Statement.solver_id == current_user.id
    ).order_by(desc(Statement.solved_at)).all()

    return [add_current_prize_list_item(s, db) for s in statements]


@router.get("/{statement_id}", response_model=StatementResponse)
def get_statement(
    statement_id: UUID,
    db: Session = Depends(get_db)
):
    """Get a specific statement by ID."""
    statement = db.query(Statement).options(
        joinedload(Statement.tags).joinedload(Tag.tagger),
        joinedload(Statement.last_edited_by),
    ).filter(Statement.id == statement_id).first()

    if not statement or statement.is_archived:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="Statement not found"
        )

    return add_current_prize(statement, db)


@router.post("", response_model=StatementResponse)
async def create_statement(
    statement_data: StatementCreate,
    current_user: User = Depends(get_current_approved_user),
    db: Session = Depends(get_db)
):
    """Submit a new Lean statement."""
    # Rate limit for non-admin users
    if not current_user.is_admin:
        settings = get_prize_settings(db)
        max_per_day = settings["max_statements_per_day"]
        one_day_ago = datetime.utcnow() - timedelta(days=1)
        recent_count = db.query(Statement).filter(
            Statement.submitter_id == current_user.id,
            Statement.created_at >= one_day_ago,
            Statement.is_archived == False,
        ).count()

        if recent_count >= max_per_day:
            raise HTTPException(
                status_code=status.HTTP_429_TOO_MANY_REQUESTS,
                detail=f"You can only submit {max_per_day} statements per 24 hours"
            )

        min_proofs = settings["min_proofs_to_submit"]
        if min_proofs > 0:
            solved_count = db.query(Statement).filter(
                Statement.solver_id == current_user.id
            ).count()
            if solved_count < min_proofs:
                raise HTTPException(
                    status_code=status.HTTP_403_FORBIDDEN,
                    detail=f"You must prove at least {min_proofs} statement(s) before submitting your own. You have proven {solved_count}."
                )

    # Compile the statement with definitions
    success, error = compile_statement(statement_data.lean_code, statement_data.definitions)

    if not success:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail=f"Statement does not compile: {error}"
        )

    # Create statement
    statement = Statement(
        title=statement_data.title,
        definitions=statement_data.definitions,
        lean_code=statement_data.lean_code,
        submitter_id=current_user.id,
    )
    db.add(statement)
    db.commit()
    db.refresh(statement)

    # Optionally start gatekeeper holding period
    settings = get_prize_settings(db)
    harmonic_enabled = settings.get("harmonic_enabled", True)
    holding_period_minutes = settings.get("holding_period_minutes", 10)

    if harmonic_enabled and holding_period_minutes > 0:
        from ..gatekeeper import run_gatekeeper
        statement.holding_period_ends_at = statement.created_at + timedelta(minutes=holding_period_minutes)
        db.commit()
        db.refresh(statement)
        asyncio.create_task(run_gatekeeper(statement.id))

    return add_current_prize(statement, db)


@router.post("/compile", response_model=CompileResult)
def compile_code(
    statement_data: StatementCreate,
    current_user: User = Depends(get_current_approved_user),
):
    """Compile Lean code without saving (for testing)."""
    success, error = compile_statement(statement_data.lean_code, statement_data.definitions)

    return CompileResult(
        success=success,
        error=error if not success else None
    )


@router.post("/{statement_id}/archive")
def archive_statement(
    statement_id: UUID,
    current_user: User = Depends(get_current_approved_user),
    db: Session = Depends(get_db),
):
    """Archive an unsolved statement. Only the submitter can do this."""
    statement = db.query(Statement).filter(Statement.id == statement_id).first()
    if not statement:
        raise HTTPException(status_code=status.HTTP_404_NOT_FOUND, detail="Statement not found")
    if str(statement.submitter_id) != str(current_user.id) and not current_user.is_admin:
        raise HTTPException(status_code=status.HTTP_403_FORBIDDEN, detail="You can only archive your own statements")
    if statement.is_solved:
        raise HTTPException(status_code=status.HTTP_400_BAD_REQUEST, detail="Cannot archive a solved statement")
    if statement.is_archived:
        raise HTTPException(status_code=status.HTTP_400_BAD_REQUEST, detail="Statement is already archived")
    statement.is_archived = True
    db.commit()
    return {"message": "Statement archived"}
