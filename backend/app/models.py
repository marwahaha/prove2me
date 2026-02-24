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
    comments = relationship("Comment", back_populates="author")


class Statement(Base):
    __tablename__ = "statements"

    id = Column(UUID(as_uuid=True), primary_key=True, default=uuid.uuid4)
    title = Column(String(200), nullable=False)
    definitions = Column(Text, nullable=True)
    lean_code = Column(Text, nullable=False)
    submitter_id = Column(UUID(as_uuid=True), ForeignKey("users.id"), nullable=False)
    is_solved = Column(Boolean, default=False)
    is_disproved = Column(Boolean, default=False)
    is_archived = Column(Boolean, default=False)
    solved_at = Column(DateTime, nullable=True)
    solver_id = Column(UUID(as_uuid=True), ForeignKey("users.id"), nullable=True)
    proof_code = Column(Text, nullable=True)
    proof_imports = Column(Text, nullable=True)
    proof_theorem_name = Column(String(200), nullable=True)
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, nullable=True)
    last_edited_by_id = Column(UUID(as_uuid=True), ForeignKey("users.id"), nullable=True)
    holding_period_ends_at = Column(DateTime, nullable=True)
    gatekeeper_chat = Column(Text, nullable=True)

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
    last_edited_by = relationship(
        "User",
        foreign_keys=[last_edited_by_id]
    )
    comments = relationship("Comment", back_populates="statement")
    tags = relationship("Tag", back_populates="statement")


class Tag(Base):
    __tablename__ = "tags"

    id = Column(UUID(as_uuid=True), primary_key=True, default=uuid.uuid4)
    statement_id = Column(UUID(as_uuid=True), ForeignKey("statements.id"), nullable=False)
    tag_name = Column(String(30), nullable=False)
    tagger_id = Column(UUID(as_uuid=True), ForeignKey("users.id"), nullable=False)
    created_at = Column(DateTime, default=datetime.utcnow)

    statement = relationship("Statement", back_populates="tags")
    tagger = relationship("User")


class Comment(Base):
    __tablename__ = "comments"

    id = Column(UUID(as_uuid=True), primary_key=True, default=uuid.uuid4)
    content = Column(Text, nullable=False)
    statement_id = Column(UUID(as_uuid=True), ForeignKey("statements.id"), nullable=False)
    author_id = Column(UUID(as_uuid=True), ForeignKey("users.id"), nullable=False)
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, nullable=True)

    statement = relationship("Statement", back_populates="comments")
    author = relationship("User", back_populates="comments")


class Setting(Base):
    __tablename__ = "settings"

    key = Column(String(50), primary_key=True)
    value = Column(String(255), nullable=False)
