import asyncio
import logging
from contextlib import asynccontextmanager
from datetime import datetime

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from .database import engine, Base, SessionLocal
from .models import Statement
from .routers import auth, statements, proofs, leaderboard, admin, comments, tags, users

logger = logging.getLogger(__name__)

# Create tables
Base.metadata.create_all(bind=engine)


@asynccontextmanager
async def lifespan(app: FastAPI):
    # Recover any statements mid-holding-period on startup
    from .gatekeeper import run_gatekeeper
    db = SessionLocal()
    try:
        in_progress = db.query(Statement).filter(
            Statement.holding_period_ends_at > datetime.utcnow(),
            Statement.is_solved == False,
            Statement.is_archived == False,
        ).all()
        ids = [s.id for s in in_progress]
    finally:
        db.close()

    for statement_id in ids:
        logger.info(f"Startup recovery: resuming gatekeeper for statement {statement_id}")
        asyncio.create_task(run_gatekeeper(statement_id))

    yield


app = FastAPI(
    title="Prove2Me",
    description="Lean Proof Submission Platform",
    version="1.0.0",
    lifespan=lifespan,
)

# CORS middleware for frontend
app.add_middleware(
    CORSMiddleware,
    allow_origins=["http://localhost:5173", "http://localhost:3000"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Include routers
app.include_router(auth.router)
app.include_router(statements.router)
app.include_router(proofs.router)
app.include_router(leaderboard.router)
app.include_router(admin.router)
app.include_router(comments.router)
app.include_router(tags.router)
app.include_router(users.router)


@app.get("/")
def root():
    return {"message": "Prove2Me API", "docs": "/docs"}


@app.get("/api/health")
def health():
    return {"status": "ok"}
