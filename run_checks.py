"""Replay the exact arithmetic checks documented in README.md."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

for script in ("verify_arithmetic.py", "verify_b2_residues.py"):
    print(f"== {script} ==", flush=True)
    subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=True)

