from fastapi import APIRouter, Depends
from sqlalchemy.orm import Session
from sqlalchemy import desc
from typing import List
from ..database import get_db
from ..models import User
from ..schemas import LeaderboardEntry

router = APIRouter(prefix="/api/leaderboard", tags=["leaderboard"])


@router.get("", response_model=List[LeaderboardEntry])
def get_leaderboard(db: Session = Depends(get_db)):
    """Get users ranked by points."""
    users = db.query(User).filter(
        User.is_approved == True
    ).order_by(desc(User.points)).limit(100).all()

    return [
        LeaderboardEntry(
            rank=i + 1,
            username=user.username,
            points=user.points
        )
        for i, user in enumerate(users)
    ]
