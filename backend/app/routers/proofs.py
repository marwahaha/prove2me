from fastapi import APIRouter, Depends, HTTPException, status
from sqlalchemy.orm import Session
from datetime import datetime
from uuid import UUID
from ..database import get_db
from ..models import User, Statement
from ..schemas import ProofSubmit, ProofResult
from ..auth import get_current_approved_user
from ..lean_runner import compile_proof
from ..prize import get_prize_settings, calculate_prize, distribute_prize

router = APIRouter(prefix="/api/proofs", tags=["proofs"])


@router.post("/{statement_id}", response_model=ProofResult)
def submit_proof(
    statement_id: UUID,
    proof_data: ProofSubmit,
    current_user: User = Depends(get_current_approved_user),
    db: Session = Depends(get_db)
):
    """Submit a proof for a statement."""
    # Get the statement
    statement = db.query(Statement).filter(Statement.id == statement_id).first()

    if not statement:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="Statement not found"
        )

    # Check if already solved
    if statement.is_solved:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail="Statement has already been solved"
        )

    # Cannot prove own statement
    if statement.submitter_id == current_user.id:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail="Cannot submit proof to your own statement"
        )

    # Compile statement + proof (no sorry allowed)
    success, error = compile_proof(statement.lean_code, proof_data.lean_code)

    if not success:
        return ProofResult(
            success=False,
            message=f"Proof failed: {error}"
        )

    # Calculate prize
    settings = get_prize_settings(db)
    total_prize = calculate_prize(statement.created_at, settings)
    submitter_share, prover_share = distribute_prize(total_prize, settings)

    # Update statement
    statement.is_solved = True
    statement.solved_at = datetime.utcnow()
    statement.solver_id = current_user.id

    # Award points
    current_user.points += prover_share

    submitter = db.query(User).filter(User.id == statement.submitter_id).first()
    if submitter:
        submitter.points += submitter_share

    db.commit()

    return ProofResult(
        success=True,
        message=f"Proof accepted! You earned {prover_share} points. Statement submitter earned {submitter_share} points.",
        points_earned=prover_share
    )
