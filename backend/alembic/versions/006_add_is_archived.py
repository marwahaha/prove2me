"""Add is_archived column to statements

Revision ID: 006
Revises: 005
Create Date: 2024-01-01

"""
from typing import Sequence, Union

from alembic import op
import sqlalchemy as sa

revision: str = '006'
down_revision: Union[str, None] = '005'
branch_labels: Union[str, Sequence[str], None] = None
depends_on: Union[str, Sequence[str], None] = None


def upgrade() -> None:
    op.add_column('statements', sa.Column('is_archived', sa.Boolean(), server_default='false', nullable=False))


def downgrade() -> None:
    op.drop_column('statements', 'is_archived')
