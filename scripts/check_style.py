#!/usr/bin/env python3
"""Check source layout and declaration-local typeclass assumptions.

Lean's environment linters check elaborated declarations. These checks
cover source conventions that elaboration erases. Comments and strings
are masked before checking variable commands; ordinary section variables
and typeclasses on individual declarations are permitted.
"""

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
OPEN = "([{⦃"
CLOSE = ")]}⦄"


def mask_comments_and_strings(source):
    """Preserve positions while masking comments and string literals."""
    masked = list(source)
    comments = []
    i = 0
    while i < len(source):
        start = i
        if source.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            comments.append((start, i))
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(source))):
            if source[j] != "\n":
                masked[j] = " "
    return "".join(masked), comments


def variable_typeclasses(masked):
    """Locate instance binders at the outer level of variable commands."""
    for match in re.finditer(r"\bvariable\b", masked):
        i = match.end()
        while i < len(masked):
            while i < len(masked) and masked[i].isspace():
                i += 1
            if i == len(masked) or masked[i] not in OPEN:
                break
            if masked[i] == "[":
                yield i
            depth = 1
            i += 1
            while i < len(masked) and depth:
                if masked[i] in OPEN:
                    depth += 1
                elif masked[i] in CLOSE:
                    depth -= 1
                i += 1


def check_file(path):
    """Return source-style findings, with repository-relative locations."""
    source = path.read_text(encoding="utf-8")
    masked, comments = mask_comments_and_strings(source)
    relative = path.relative_to(ROOT)
    exempt = set()
    if relative.parts[:2] == ("RS", "Assembly"):
        for start, end in comments:
            if (source.startswith("/--", start)
                    and re.match(r"\s*#guard_msgs\b", source[end:])):
                first = source.count("\n", 0, start) + 1
                last = source.count("\n", 0, end) + 1
                exempt.update(range(first, last + 1))
    findings = []
    for line, text in enumerate(source.splitlines(), 1):
        if len(text) > 80 and line not in exempt:
            findings.append(f"{relative}:{line}: {len(text)} columns (max 80)")
    for position in variable_typeclasses(masked):
        line = source.count("\n", 0, position) + 1
        findings.append(
            f"{relative}:{line}: put typeclass assumptions on declarations"
        )
    return findings


def main():
    paths = sorted((ROOT / "RS").rglob("*.lean"))
    paths += sorted(ROOT.glob("*.lean"))
    findings = [finding for path in paths for finding in check_file(path)]
    if findings:
        print("\n".join(findings), file=sys.stderr)
        return 1
    print(f"Source style passed for {len(paths)} Lean files.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
