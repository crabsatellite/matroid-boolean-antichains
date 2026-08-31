"""Incrementally build one Lean module, then reject any unexpected audit axiom.

Invoke through the Paper Infrastructure verification-receipt runner.
This is execution evidence only, never a paper-correspondence certificate.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("module")
    parser.add_argument("audit")
    parser.add_argument("--allow-axiom", action="append", default=[])
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    lean_root = root / "lean4"
    audit = (root / args.audit).resolve()
    audit.relative_to(lean_root)
    audit_text = audit.read_text(encoding="utf-8")
    endpoint_lines = [line for line in audit_text.splitlines() if line.lstrip().startswith("#print axioms ")]
    endpoints = re.findall(r"^#print axioms ([\w.']+)\s*$", audit_text, re.M)
    if len(endpoints) != len(endpoint_lines):
        raise RuntimeError("audit contains unsupported endpoint syntax")
    if not endpoints:
        raise RuntimeError("audit contains no endpoints")
    if len(endpoints) != len(set(endpoints)):
        raise RuntimeError("audit contains duplicate endpoints")
    if len(args.allow_axiom) != len(set(args.allow_axiom)) or any(
        re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name) is None
        for name in args.allow_axiom
    ):
        raise RuntimeError("allowed axiom names must be unique Lean identifiers")
    allowed = {"propext", "Classical.choice", "Quot.sound", *args.allow_axiom}
    log_path = root / "output" / ("lean-" + args.module.replace(".", "-") + ".log")
    transcript = []
    for command in (
        ["lake", "build", args.module],
        ["lake", "env", "lean", "--trust=0", str(audit.relative_to(lean_root))],
    ):
        result = subprocess.run(command, cwd=lean_root, encoding="utf-8", errors="replace",
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
        print(result.stdout, end="", flush=True)
        transcript.append(result.stdout)
        log_path.write_text("".join(transcript), encoding="utf-8")
        if result.returncode:
            return result.returncode
    output = result.stdout
    observed = {}
    for name, axioms in re.findall(r"'([\w.']+)' depends on axioms: \[([^\]]*)\]", output):
        observed[name] = {a.strip() for a in axioms.split(",") if a.strip()}
    for name in re.findall(r"'([\w.']+)' does not depend on any axioms", output):
        observed[name] = set()
    if set(observed) != set(endpoints):
        raise RuntimeError(f"audit endpoint mismatch: {set(endpoints) ^ set(observed)}")
    for name, axioms in observed.items():
        if axioms - allowed:
            raise RuntimeError(f"unexpected axioms for {name}: {axioms - allowed}")
    if re.search(r"\b(?:error|sorryAx|native_decide|ofReduceBool)\b", output):
        raise RuntimeError("audit output contains a proof escape or error")
    print(f"KERNEL_TARGET_VERIFIED {args.module} endpoints={len(endpoints)}", flush=True)
    return 0


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    raise SystemExit(main())
