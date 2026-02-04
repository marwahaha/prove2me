import uuid
from datetime import datetime
from sqlalchemy import Column, String, Boolean, Integer, DateTime, Text, ForeignKey
from sqlalchemy.dialects.postgresql import UUID
from sqlalchemy.orm import relationship
from .database import Base


class User(Base):
    __tablename__ = "users"

    id = Column(UUID(as_uuid=True), primary_key=True, default=uuid.uuid4)
    username = Column(String(50), unique=True, nullable=False, index=True)
    email = Column(String(255), unique=True, nullable=False, index=True)
    password_hash = Column(String(255), nullable=False)
    points = Column(Integer, default=0)
    is_admin = Column(Boolean, default=False)
    is_approved = Column(Boolean, default=False)
    created_at = Column(DateTime, default=datetime.utcnow)

    submitted_statements = relationship(
        "Statement",
        back_populates="submitter",
        foreign_keys="Statement.submitter_id"
    )
    solved_statements = relationship(
        "Statement",
        back_populates="solver",
        foreign_keys="Statement.solver_id"
    )


class Statement(Base):
    __tablename__ = "statements"

    id = Column(UUID(as_uuid=True), primary_key=True, default=uuid.uuid4)
    title = Column(String(200), nullable=False)
    definitions = Column(Text, nullable=True)
    lean_code = Column(Text, nullable=False)
    submitter_id = Column(UUID(as_uuid=True), ForeignKey("users.id"), nullable=False)
    is_solved = Column(Boolean, default=False)
    solved_at = Column(DateTime, nullable=True)
    solver_id = Column(UUID(as_uuid=True), ForeignKey("users.id"), nullable=True)
    proof_code = Column(Text, nullable=True)
    created_at = Column(DateTime, default=datetime.utcnow)

    submitter = relationship(
        "User",
        back_populates="submitted_statements",
        foreign_keys=[submitter_id]
    )
    solver = relationship(
        "User",
        back_populates="solved_statements",
        foreign_keys=[solver_id]
    )


class Setting(Base):
    __tablename__ = "settings"

    key = Column(String(50), primary_key=True)
    value = Column(String(255), nullable=False)
