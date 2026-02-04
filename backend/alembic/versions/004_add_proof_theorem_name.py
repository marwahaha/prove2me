"""Add proof_theorem_name column to statements

Revision ID: 004
Revises: 003
Create Date: 2024-01-01

"""
from typing import Sequence, Union

from alembic import op
import sqlalchemy as sa

revision: str = '004'
down_revision: Union[str, None] = '003'
branch_labels: Union[str, Sequence[str], None] = None
depends_on: Union[str, Sequence[str], None] = None


def upgrade() -> None:
    op.add_column('statements', sa.Column('proof_theorem_name', sa.String(200), nullable=True))


def downgrade() -> None:
    op.drop_column('statements', 'proof_theorem_name')
