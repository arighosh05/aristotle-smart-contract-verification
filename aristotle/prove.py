"""
aristotle/prove.py
Submit ERC-20 verification condition files to Aristotle and collect results.

Usage:
    cd /path/to/project
    export ARISTOTLE_API_KEY="your-key-here"
    python aristotle/prove.py

Each property file (Transfer, Approve, TransferFrom) is submitted as a
separate Aristotle job.  Results are written to results/run_<timestamp>.json
and the filled Lean output is saved to results/<module>_proved.lean.
"""

import asyncio
import json
import os
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

# ── Path setup ─────────────────────────────────────────────────────────────────
PROJECT_ROOT = Path(__file__).parent.parent.resolve()
sys.path.insert(0, str(PROJECT_ROOT))

from aristotle.config import (
    ARISTOTLE_API_KEY,
    CONTEXT_FILES,
    POLLING_INTERVAL_SECONDS,
    MAX_POLLING_FAILURES,
    PROPERTY_FILES,
    RESULTS_DIR,
)

import aristotlelib
from aristotlelib import Project, ProjectStatus

# ── Pre-flight checks ──────────────────────────────────────────────────────────

def check_api_key() -> str:
    key = ARISTOTLE_API_KEY
    if not key:
        print(
            "ERROR: ARISTOTLE_API_KEY is not set.\n"
            "  export ARISTOTLE_API_KEY='your-key-here'\n"
            "  then re-run this script.",
            file=sys.stderr,
        )
        sys.exit(1)
    return key


def check_files() -> tuple[list[str], list[Path]]:
    """Verify all source files exist. Returns (context_paths, property_files)."""
    context_paths = [str(p) for p in CONTEXT_FILES]
    for p in CONTEXT_FILES:
        if not p.exists():
            print(f"ERROR: context file not found: {p}", file=sys.stderr)
            sys.exit(1)
    for p in PROPERTY_FILES:
        if not p.exists():
            print(f"ERROR: property file not found: {p}", file=sys.stderr)
            sys.exit(1)
    return context_paths, list(PROPERTY_FILES)


# ── Proof submission ───────────────────────────────────────────────────────────

async def prove_file(
    prop_file: Path,
    context_paths: list[str],
    results_dir: Path,
) -> dict:
    """Submit one property file to Aristotle, await completion, return record."""
    module_name = prop_file.stem
    output_path = results_dir / f"{module_name}_proved.lean"

    print(f"\n{'='*60}")
    print(f"  Submitting: {prop_file.name}")
    print(f"  Output:     {output_path.relative_to(PROJECT_ROOT)}")
    print(f"{'='*60}")

    start_time = time.time()
    record = {
        "module": module_name,
        "input_file": str(prop_file.relative_to(PROJECT_ROOT)),
        "output_file": str(output_path.relative_to(PROJECT_ROOT)),
        "status": "UNKNOWN",
        "project_id": None,
        "duration_seconds": None,
        "error": None,
        "submitted_at": datetime.now(timezone.utc).isoformat(),
    }

    try:
        solution_path = await Project.prove_from_file(
            input_file_path=str(prop_file),
            context_file_paths=context_paths,
            output_file_path=str(output_path),
            wait_for_completion=True,
            polling_interval_seconds=POLLING_INTERVAL_SECONDS,
            max_polling_failures=MAX_POLLING_FAILURES,
            validate_lean_project=True,
        )

        elapsed = time.time() - start_time
        record["duration_seconds"] = round(elapsed, 1)
        record["status"] = "COMPLETE"
        record["output_file"] = str(solution_path)
        print(f"  COMPLETE in {elapsed:.0f}s → {solution_path}")

    except aristotlelib.AristotleAPIError as exc:
        elapsed = time.time() - start_time
        record["duration_seconds"] = round(elapsed, 1)
        record["status"] = "FAILED"
        record["error"] = str(exc)
        print(f"  FAILED after {elapsed:.0f}s: {exc}", file=sys.stderr)

    except Exception as exc:
        elapsed = time.time() - start_time
        record["duration_seconds"] = round(elapsed, 1)
        record["status"] = "ERROR"
        record["error"] = f"{type(exc).__name__}: {exc}"
        print(f"  ERROR after {elapsed:.0f}s: {exc}", file=sys.stderr)

    return record


# ── Results persistence ────────────────────────────────────────────────────────

def save_results(results: list[dict], results_dir: Path) -> Path:
    ts = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    out_path = results_dir / f"run_{ts}.json"
    out_path.write_text(json.dumps(results, indent=2))
    return out_path


def print_summary(results: list[dict]) -> None:
    print(f"\n{'='*60}")
    print("  RESULTS SUMMARY")
    print(f"{'='*60}")
    print(f"  {'Module':<20} {'Status':<12} {'Duration':>10}")
    print(f"  {'-'*20} {'-'*12} {'-'*10}")
    for r in results:
        dur = f"{r['duration_seconds']}s" if r["duration_seconds"] is not None else "-"
        print(f"  {r['module']:<20} {r['status']:<12} {dur:>10}")
    print(f"{'='*60}\n")


# ── Async main ─────────────────────────────────────────────────────────────────

async def main() -> None:
    os.chdir(PROJECT_ROOT)

    api_key = check_api_key()
    aristotlelib.set_api_key(api_key)

    context_paths, property_files = check_files()
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    print(f"Aristotle ERC-20 Verification Runner")
    print(f"Project root: {PROJECT_ROOT}")
    print(f"Context files: {[Path(p).name for p in context_paths]}")
    print(f"Property files: {[p.name for p in property_files]}")

    results = []
    for i, prop_file in enumerate(property_files):
        record = await prove_file(prop_file, context_paths, RESULTS_DIR)
        results.append(record)
        # Brief pause between submissions
        if i < len(property_files) - 1:
            await asyncio.sleep(5)

    summary_path = save_results(results, RESULTS_DIR)
    print_summary(results)
    print(f"Full results saved to: {summary_path.relative_to(PROJECT_ROOT)}")


if __name__ == "__main__":
    asyncio.run(main())
