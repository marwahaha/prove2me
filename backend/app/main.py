from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from .database import engine, Base
from .routers import auth, statements, proofs, leaderboard, admin, comments

# Create tables
Base.metadata.create_all(bind=engine)

app = FastAPI(
    title="Prove2Me",
    description="Lean Proof Submission Platform",
    version="1.0.0"
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


@app.get("/")
def root():
    return {"message": "Prove2Me API", "docs": "/docs"}


@app.get("/api/health")
def health():
    return {"status": "ok"}
