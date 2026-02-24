"""Add gatekeeper fields to statements

Revision ID: 011
Revises: 010
Create Date: 2024-01-01

"""
from typing import Sequence, Union

from alembic import op
import sqlalchemy as sa

revision: str = '011'
down_revision: Union[str, None] = '010'
branch_labels: Union[str, Sequence[str], None] = None
depends_on: Union[str, Sequence[str], None] = None


def upgrade() -> None:
    op.add_column('statements', sa.Column('holding_period_ends_at', sa.DateTime(), nullable=True))
    op.add_column('statements', sa.Column('gatekeeper_chat', sa.Text(), nullable=True))


def downgrade() -> None:
    op.drop_column('statements', 'gatekeeper_chat')
    op.drop_column('statements', 'holding_period_ends_at')
