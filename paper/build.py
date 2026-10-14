"""Build paper/main.pdf with three pdflatex passes; stop on undefined references, duplicate labels or overfull boxes."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "build"
OUT.mkdir(exist_ok=True)
for _ in range(3):
    run = subprocess.run(
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
         "-output-directory=build", "main.tex"],
        cwd=ROOT, capture_output=True, text=True, errors="replace",
    )
    if run.returncode:
        print("\n".join(run.stdout.splitlines()[-45:]))
        raise SystemExit(run.returncode)
log = (OUT / "main.log").read_text(errors="replace")
warnings = [line for line in log.splitlines() if any(s in line for s in (
    "undefined", "Overfull", "multiply defined", "Rerun to get"
))]
if warnings:
    print("\n".join(warnings))
    raise SystemExit("Unresolved manuscript build warnings; inspect build/main.log.")
shutil.copy2(OUT / "main.pdf", ROOT / "main.pdf")
print("Built main.pdf; no undefined references, duplicate labels, or overfull boxes.")
