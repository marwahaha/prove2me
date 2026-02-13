from pydantic_settings import BaseSettings
from functools import lru_cache


class Settings(BaseSettings):
    database_url: str = "postgresql://localhost/prove2me"
    secret_key: str = "your-secret-key-change-in-production"
    lean_project_path: str = "/Users/macbookpro/prove2me/prove2me_lean"
    lean_bin_path: str = ""  # e.g., /home/user/.elan/bin - leave empty to use system PATH
    lean_timeout: int = 120

    class Config:
        env_file = ".env"


@lru_cache()
def get_settings() -> Settings:
    return Settings()
