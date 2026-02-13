from fastapi import APIRouter, Depends, HTTPException, status, Query
from sqlalchemy.orm import Session
from sqlalchemy import desc
from typing import List, Optional
from uuid import UUID
from datetime import datetime, timedelta
from ..database import get_db
from ..models import User, Statement
from ..schemas import StatementCreate, StatementResponse, StatementListItem, CompileResult
from ..auth import get_current_approved_user
from ..lean_runner import compile_statement
from ..prize import get_prize_settings, calculate_prize

MAX_STATEMENTS_PER_DAY = 3

router = APIRouter(prefix="/api/statements", tags=["statements"])


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
        "solved_at": statement.solved_at,
        "solver": statement.solver,
        "proof_code": statement.proof_code,
        "proof_theorem_name": statement.proof_theorem_name,
        "created_at": statement.created_at,
        "current_prize": prize,
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
        "solver": statement.solver,
        "created_at": statement.created_at,
        "solved_at": statement.solved_at,
        "current_prize": prize,
    }


@router.get("", response_model=List[StatementListItem])
def list_statements(
    sort_by: Optional[str] = Query("newest", regex="^(newest|prize)$"),
    db: Session = Depends(get_db)
):
    """List all unsolved statements."""
    query = db.query(Statement).filter(Statement.is_solved == False)

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
    db: Session = Depends(get_db)
):
    """List all solved statements."""
    statements = db.query(Statement).filter(
        Statement.is_solved == True
    ).order_by(desc(Statement.solved_at)).all()

    return [add_current_prize_list_item(s, db) for s in statements]


@router.get("/my", response_model=List[StatementListItem])
def list_my_statements(
    current_user: User = Depends(get_current_approved_user),
    db: Session = Depends(get_db)
):
    """List current user's submitted statements."""
    statements = db.query(Statement).filter(
        Statement.submitter_id == current_user.id
    ).order_by(desc(Statement.created_at)).all()

    return [add_current_prize_list_item(s, db) for s in statements]


@router.get("/solved", response_model=List[StatementListItem])
def list_solved_by_me(
    current_user: User = Depends(get_current_approved_user),
    db: Session = Depends(get_db)
):
    """List statements the current user has solved (submitted proofs for)."""
    statements = db.query(Statement).filter(
        Statement.solver_id == current_user.id
    ).order_by(desc(Statement.solved_at)).all()

    return [add_current_prize_list_item(s, db) for s in statements]


@router.get("/{statement_id}", response_model=StatementResponse)
def get_statement(
    statement_id: UUID,
    db: Session = Depends(get_db)
):
    """Get a specific statement by ID."""
    statement = db.query(Statement).filter(Statement.id == statement_id).first()

    if not statement:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="Statement not found"
        )

    return add_current_prize(statement, db)


@router.post("", response_model=StatementResponse)
def create_statement(
    statement_data: StatementCreate,
    current_user: User = Depends(get_current_approved_user),
    db: Session = Depends(get_db)
):
    """Submit a new Lean statement."""
    # Rate limit for non-admin users
    if not current_user.is_admin:
        one_day_ago = datetime.utcnow() - timedelta(days=1)
        recent_count = db.query(Statement).filter(
            Statement.submitter_id == current_user.id,
            Statement.created_at >= one_day_ago
        ).count()

        if recent_count >= MAX_STATEMENTS_PER_DAY:
            raise HTTPException(
                status_code=status.HTTP_429_TOO_MANY_REQUESTS,
                detail=f"You can only submit {MAX_STATEMENTS_PER_DAY} statements per 24 hours"
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
