"""Initial migration

Revision ID: 001
Revises:
Create Date: 2024-01-01

"""
from typing import Sequence, Union

from alembic import op
import sqlalchemy as sa
from sqlalchemy.dialects import postgresql

revision: str = '001'
down_revision: Union[str, None] = None
branch_labels: Union[str, Sequence[str], None] = None
depends_on: Union[str, Sequence[str], None] = None


def upgrade() -> None:
    op.create_table(
        'users',
        sa.Column('id', postgresql.UUID(as_uuid=True), primary_key=True),
        sa.Column('username', sa.String(50), unique=True, nullable=False, index=True),
        sa.Column('email', sa.String(255), unique=True, nullable=False, index=True),
        sa.Column('password_hash', sa.String(255), nullable=False),
        sa.Column('points', sa.Integer(), default=0),
        sa.Column('is_admin', sa.Boolean(), default=False),
        sa.Column('is_approved', sa.Boolean(), default=False),
        sa.Column('created_at', sa.DateTime(), nullable=True),
    )

    op.create_table(
        'statements',
        sa.Column('id', postgresql.UUID(as_uuid=True), primary_key=True),
        sa.Column('title', sa.String(200), nullable=False),
        sa.Column('lean_code', sa.Text(), nullable=False),
        sa.Column('submitter_id', postgresql.UUID(as_uuid=True), sa.ForeignKey('users.id'), nullable=False),
        sa.Column('is_solved', sa.Boolean(), default=False),
        sa.Column('solved_at', sa.DateTime(), nullable=True),
        sa.Column('solver_id', postgresql.UUID(as_uuid=True), sa.ForeignKey('users.id'), nullable=True),
        sa.Column('created_at', sa.DateTime(), nullable=True),
    )

    op.create_table(
        'settings',
        sa.Column('key', sa.String(50), primary_key=True),
        sa.Column('value', sa.String(255), nullable=False),
    )


def downgrade() -> None:
    op.drop_table('settings')
    op.drop_table('statements')
    op.drop_table('users')
