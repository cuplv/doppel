#!/usr/bin/env python3
"""Report every escape hatch (admit, assume, tadmit, magic, ...) in the F* sources.

Two complementary checks are combined:

1. **Source scan.** Every ``.fst``/``.fsti`` file is scanned, with comments and
   string literals ignored, for the keywords ``admit``, ``assume``, ``tadmit``,
   ``magic`` and ``unsafe_coerce``, and for the options ``--admit_smt_queries``
   and ``--lax`` (e.g. in ``#push-options``).  This catches top-level
   ``assume val`` declarations, which F*'s own report does not flag.

2. **F*'s own report.** Every file is re-checked by F* (``--force``, so cached
   results are not reused) with ``--report_assumes warn``, which emits Warning
   335 at every use of ``Prims.admit`` and similar axioms, including through
   aliases that the source scan cannot see.  SMT queries are skipped
   (``--admit_smt_queries true``) because ``make verify`` has already discharged
   them, so this takes about a minute.  Dependencies are loaded from the
   ``output/`` cache, so run ``make verify`` first (``make audit`` does both).

The script exits with status 1 if anything other than the four expected
escape hatches in ``EXPECTED`` is found, and 2 if F* fails on a file.

Usage: ``scripts/audit_assumes.py [--no-fstar]`` (``--no-fstar`` runs only the
source scan, which needs no F* installation or prior build).
"""

from __future__ import annotations

import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUTPUT_DIR = "output"
FSTAR_EXE = os.environ.get("FSTAR_EXE", "fstar.exe")

# file:line of every expected escape hatch, with the reason it is there.
EXPECTED = {
    "ObservationalBisimulation.fst:39":
        "obs_bisim_up_to_partitions_implies_t_equivalence (paper Thm 4.7), proved in Lean",
    "ObservationalBisimulation.fst:68":
        "obs_bisim_up_to_partitions_implies_t_equivalence' (paper Thm 4.13), proved in Lean",
    "helpers/FStar.PartialMap.Ext.fst:15":
        "FStar.PartialMap.Ext.map: workaround for opaque FStar.PartialMap (SMD example only)",
    "helpers/FStar.PartialMap.Ext.fst:19":
        "FStar.PartialMap.Ext.sel_map: workaround for opaque FStar.PartialMap (SMD example only)",
}

KEYWORDS = re.compile(
    r"(?<![\w'])(admit|assume|tadmit|magic|unsafe_coerce)(?![\w'])"
    r"|--(admit_smt_queries|lax)\b")
WARNING_335 = re.compile(r"^\* Warning 335 at ([^(]+)\((\d+),", re.M)


def sources() -> list[str]:
    """Same source set as the Makefile: top level (non-recursive), helpers/ and
    examples/ (recursive)."""
    files = [f for f in os.listdir(REPO) if f.endswith((".fst", ".fsti"))]
    for root_dir in ("helpers", "examples"):
        for dirpath, _, names in os.walk(os.path.join(REPO, root_dir)):
            files += [os.path.relpath(os.path.join(dirpath, n), REPO)
                      for n in names if n.endswith((".fst", ".fsti"))]
    return sorted(files)


def strip_comments_and_strings(src: str) -> str:
    """Blank out comments (``//``, nested ``(* *)``) and string literals,
    preserving line structure."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if depth == 0 and src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif src.startswith("(*", i) and not src.startswith("(*)", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and src.startswith("*)", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""' + "\n" * src.count("\n", i, j))
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def source_scan(files: list[str]) -> dict[str, str]:
    hits = {}
    for f in files:
        with open(os.path.join(REPO, f), encoding="utf-8") as h:
            text = strip_comments_and_strings(h.read())
        for lineno, line in enumerate(text.split("\n"), 1):
            if KEYWORDS.search(line):
                hits[f"{f}:{lineno}"] = line.strip()
    return hits


def fstar_report(files: list[str]) -> set[str]:
    includes = []
    for d in sorted({os.path.dirname(f) or "." for f in files}):
        includes += ["--include", d]
    hits = set()
    for k, f in enumerate(files, 1):
        print(f"\r  F* report: {k}/{len(files)} files", end="", flush=True)
        cmd = [FSTAR_EXE, "--cache_dir", OUTPUT_DIR, *includes,
               "--include", OUTPUT_DIR, "--already_cached", "Prims", "--force",
               "--report_assumes", "warn", "--admit_smt_queries", "true", f]
        proc = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True)
        if proc.returncode != 0:
            print(proc.stdout + proc.stderr)
            print(f"AUDIT ERROR: F* failed on {f} (did you run 'make verify' first?)")
            sys.exit(2)
        for path, line in WARNING_335.findall(proc.stdout + proc.stderr):
            hits.add(f"{os.path.normpath(path)}:{line}")
    if sys.stdout.isatty():
        print()
    return hits


def main() -> None:
    files = sources()
    print(f"Auditing {len(files)} F* files for escape hatches...")
    scanned = source_scan(files)
    reported = fstar_report(files) if "--no-fstar" not in sys.argv else set()

    found = sorted(set(scanned) | reported)
    print("\nEscape hatches found (file:line, what it is, found by):")
    for loc in found:
        sources_ = [s for s, hit in (("source scan", loc in scanned),
                                     ("F* report", loc in reported)) if hit]
        print(f"  {loc:36} {EXPECTED.get(loc, 'UNEXPECTED')} [{', '.join(sources_)}]")
        if loc in scanned:
            print(f"      code: {scanned[loc]}")
    if not found:
        print("  (none)")

    unexpected = [loc for loc in found if loc not in EXPECTED]
    missing = [loc for loc in EXPECTED if loc not in found]
    if unexpected:
        print("\nAUDIT FAILED: unexpected escape hatches:")
        for loc in unexpected:
            print(f"  {loc}")
        sys.exit(1)
    if missing:
        print("\nNote: expected escape hatches no longer present "
              "(update EXPECTED in this script):")
        for loc in missing:
            print(f"  {loc}")
    print(f"\nAUDIT PASSED: the only escape hatches are the {len(found)} expected ones.")


if __name__ == "__main__":
    main()
