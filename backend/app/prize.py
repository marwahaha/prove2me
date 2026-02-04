from datetime import datetime
from sqlalchemy.orm import Session
from .models import Setting
import json


DEFAULT_SETTINGS = {
    "base_points": 100,
    "growth_rate": 1.50,
    "submitter_share": 0.20,
}


def get_prize_settings(db: Session) -> dict:
    """Get prize settings from database, using defaults if not set."""
    settings = {}
    for key, default in DEFAULT_SETTINGS.items():
        setting = db.query(Setting).filter(Setting.key == key).first()
        if setting:
            settings[key] = json.loads(setting.value)
        else:
            settings[key] = default
    return settings


def set_prize_setting(db: Session, key: str, value) -> None:
    """Set a prize setting in the database."""
    setting = db.query(Setting).filter(Setting.key == key).first()
    if setting:
        setting.value = json.dumps(value)
    else:
        setting = Setting(key=key, value=json.dumps(value))
        db.add(setting)
    db.commit()


def calculate_prize(statement_created_at: datetime, settings: dict) -> int:
    """Calculate current prize using exponential growth."""
    base = settings['base_points']
    rate = settings['growth_rate']

    days_elapsed = (datetime.utcnow() - statement_created_at).total_seconds() / 86400
    prize = base * (rate ** days_elapsed)

    return int(prize)


def distribute_prize(prize: int, settings: dict) -> tuple[int, int]:
    """Return (submitter_share, prover_share)."""
    submitter_pct = settings['submitter_share']
    submitter_share = int(prize * submitter_pct)
    prover_share = prize - submitter_share
    return submitter_share, prover_share
