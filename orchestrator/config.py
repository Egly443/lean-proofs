"""Configuration settings from environment variables."""

import os
from pathlib import Path
from functools import lru_cache

from dotenv import load_dotenv

load_dotenv()


class Settings:
    """Application settings loaded from environment."""

    def __init__(self):
        self.anthropic_api_key: str = os.getenv("ANTHROPIC_API_KEY", "")
        self.port: int = int(os.getenv("ORCHESTRATOR_PORT", "8000"))
        self.lean_files_dir: Path = Path(os.getenv("LEAN_FILES_DIR", "."))
        self.socket_file: Path = Path(".lean_bridge.sock")
        self.memory_file: Path = Path("agent_memory.json")

        # Proof search defaults
        self.default_max_steps: int = 600
        self.default_max_queue_size: int = 2000

        # API settings
        self.anthropic_model: str = "claude-sonnet-4-20250514"

    @property
    def has_anthropic_key(self) -> bool:
        return bool(self.anthropic_api_key and self.anthropic_api_key.startswith("sk-ant-"))


@lru_cache()
def get_settings() -> Settings:
    """Get cached settings instance."""
    return Settings()
