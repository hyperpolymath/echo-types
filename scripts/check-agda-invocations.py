#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Check direct Agda proof commands in the maintained CI/local entrypoints.

Static policy lint only: not an Agda typecheck or a parser for arbitrary shell.
The separately reviewed full-cubical profile is not implied by this check.
"""
import re
import sys
from pathlib import Path

DEFAULTS = [".github/workflows/agda.yml", "scripts/check-grade3.sh", "scripts/verify.sh", "Justfile"]
PROFILE = {"--safe", "--without-K", "--cubical-compatible"}
CUBICAL = "proofs/agda/EchoImageFactorizationPropCubical.agda"
DENIED = {"--allow-unsolved-metas", "--with-K", "--no-without-K", "--type-in-type", "--no-termination-check", "--no-positivity-check"}
pattern = re.compile(r"^\s*(?:run:\s*)?agda\s+(.*)$")
failed = False
for filename in sys.argv[1:] or DEFAULTS:
    path = Path(filename)
    count = 0
    for line_no, line in enumerate(path.read_text().splitlines(), 1):
        match = pattern.match(line)
        if not match:
            continue
        args = set(match.group(1).split())
        if args == {"--version"}:
            continue
        count += 1
        required = {"--safe", "--cubical"} if CUBICAL in args else PROFILE
        forbidden = args & DENIED
        if CUBICAL not in args and "--cubical" in args:
            forbidden.add("--cubical")
        missing = required - args
        if missing or forbidden:
            print(f"{filename}:{line_no}: missing {sorted(missing)}, forbidden {sorted(forbidden)}", file=sys.stderr)
            failed = True
    if not count:
        print(f"{filename}: no direct Agda proof command found", file=sys.stderr)
        failed = True
if failed:
    sys.exit(1)
print("Agda invocation lint: OK (static only; no proof was checked)")
