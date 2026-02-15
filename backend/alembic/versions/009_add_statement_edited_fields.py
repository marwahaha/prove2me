"""Add updated_at and last_edited_by_id to statements

Revision ID: 009
Revises: 008
Create Date: 2024-01-01

"""
from typing import Sequence, Union

from alembic import op
import sqlalchemy as sa
from sqlalchemy.dialects import postgresql

revision: str = '009'
down_revision: Union[str, None] = '008'
branch_labels: Union[str, Sequence[str], None] = None
depends_on: Union[str, Sequence[str], None] = None


def upgrade() -> None:
    op.add_column('statements', sa.Column('updated_at', sa.DateTime(), nullable=True))
    op.add_column('statements', sa.Column('last_edited_by_id', postgresql.UUID(as_uuid=True), nullable=True))
    op.create_foreign_key('fk_statements_last_edited_by', 'statements', 'users', ['last_edited_by_id'], ['id'])


def downgrade() -> None:
    op.drop_constraint('fk_statements_last_edited_by', 'statements', type_='foreignkey')
    op.drop_column('statements', 'last_edited_by_id')
    op.drop_column('statements', 'updated_at')
