"""Create tags table

Revision ID: 008
Revises: 007
Create Date: 2024-01-01

"""
from typing import Sequence, Union

from alembic import op
import sqlalchemy as sa
from sqlalchemy.dialects import postgresql

revision: str = '008'
down_revision: Union[str, None] = '007'
branch_labels: Union[str, Sequence[str], None] = None
depends_on: Union[str, Sequence[str], None] = None


def upgrade() -> None:
    op.create_table(
        'tags',
        sa.Column('id', postgresql.UUID(as_uuid=True), primary_key=True),
        sa.Column('statement_id', postgresql.UUID(as_uuid=True), sa.ForeignKey('statements.id'), nullable=False),
        sa.Column('tag_name', sa.String(30), nullable=False),
        sa.Column('tagger_id', postgresql.UUID(as_uuid=True), sa.ForeignKey('users.id'), nullable=False),
        sa.Column('created_at', sa.DateTime(), nullable=False),
    )
    op.create_index('ix_tags_statement_id', 'tags', ['statement_id'])
    op.execute(
        "CREATE UNIQUE INDEX uq_tags_statement_tag ON tags (statement_id, lower(tag_name))"
    )


def downgrade() -> None:
    op.drop_index('uq_tags_statement_tag', if_exists=True)
    op.drop_index('ix_tags_statement_id', if_exists=True)
    op.drop_table('tags')
