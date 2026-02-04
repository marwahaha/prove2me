from pydantic_settings import BaseSettings
from functools import lru_cache


class Settings(BaseSettings):
    database_url: str = "postgresql://postgres:postgres@localhost:5432/prove2me"
    secret_key: str = "your-secret-key-change-in-production"
    lean_project_path: str = "/path/to/prove2me_lean"
    lean_timeout: int = 30

    class Config:
        env_file = ".env"


@lru_cache()
def get_settings() -> Settings:
    return Settings()
