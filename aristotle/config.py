"""
aristotle/config.py
Configuration for the Aristotle proof runner.

Set ARISTOTLE_API_KEY in your environment before running:
    export ARISTOTLE_API_KEY="your-key-here"

Or pass it on the command line:
    ARISTOTLE_API_KEY="..." python aristotle/prove.py
"""

import os
from pathlib import Path

# ── API credentials ────────────────────────────────────────────────────────────

ARISTOTLE_API_KEY: str = os.environ.get("ARISTOTLE_API_KEY", "")

# ── Project layout (all paths relative to project root) ────────────────────────

PROJECT_ROOT = Path(__file__).parent.parent.resolve()

CONTEXT_FILES = [
    PROJECT_ROOT / "evm_model" / "Basic.lean",
    PROJECT_ROOT / "evm_model" / "ERC20.lean",
]

PROPERTY_FILES = [
    PROJECT_ROOT / "properties" / "Transfer.lean",
    PROJECT_ROOT / "properties" / "Approve.lean",
    PROJECT_ROOT / "properties" / "TransferFrom.lean",
]

RESULTS_DIR = PROJECT_ROOT / "results"

# ── Aristotle polling settings ─────────────────────────────────────────────────

POLLING_INTERVAL_SECONDS: int = 30
MAX_POLLING_FAILURES: int = 5
