#!/usr/bin/env python3
"""Partition the buildable modules in the pinned sunflower import graph."""

from argparse import ArgumentParser
import json
from pathlib import Path
import re


TARGET = "OAI.Combinatorics.Sunflower.FixedBase"
LONG_MODULE = "OAI.Computability.BorderVNP.DiagonalCalendarGuardedRegisteredPacket"
IMPORT = re.compile(r"(?:(?:public|meta|private)\s+)*import\s+(?:all\s+)?([\w.]+)")
COMMENTS = re.compile(r"/-|-/|--|\n")


def imports(source):
    depth = 0
    for line in source.read_text().splitlines(keepends=True):
        prefix = []
        start = 0
        for marker in COMMENTS.finditer(line):
            token = marker[0]
            if depth == 0:
                prefix.append(line[start:marker.start()])
                if token in {"--", "\n"}:
                    break
            if token == "/-":
                depth += 1
            elif token == "-/" and depth:
                depth -= 1
            start = marker.end()
        else:
            if depth == 0:
                prefix.append(line[start:])
        code = "".join(prefix).strip()
        if not code or code in {"module", "prelude"}:
            continue
        match = IMPORT.fullmatch(code)
        if not match:
            break
        yield match[1]


def ready_modules(root):
    packages = root / ".lake/packages"
    locations = {
        "OAI": root,
        "Lemmata": packages / "lemmata/lean",
        "FixedPointTheorems": packages / "fixed-point-theorems",
    }
    missing = {}
    pending = [TARGET]
    while pending:
        module = pending.pop()
        if module in missing:
            continue
        base = locations.get(module.split(".", 1)[0])
        if base is None:
            continue
        relative = Path(*module.split("."))
        source = base / relative.with_suffix(".lean")
        olean = base / ".lake/build/lib/lean" / relative.with_suffix(".olean")
        if olean.is_file() or not source.is_file():
            continue
        dependencies = tuple(imports(source))
        missing[module] = (source.stat().st_size, dependencies)
        pending.extend(dependencies)
    return {
        module: weight for module, (weight, dependencies) in missing.items()
        if not any(dependency in missing for dependency in dependencies)
    }


def partition(ready, count=12):
    regular = {module: weight for module, weight in ready.items() if module != LONG_MODULE}
    buckets = [[] for _ in range(min(count, len(regular)))]
    weights = [0] * len(buckets)
    for module in sorted(regular, key=lambda name: (-regular[name], name)):
        index = min(range(len(buckets)), key=weights.__getitem__)
        buckets[index].append(module)
        weights[index] += regular[module]
    jobs = [
        {"slot": index, "targets": " ".join(reversed(modules)), "budget": "35m", "timeout": 65}
        for index, modules in enumerate(buckets, 1)
    ]
    if LONG_MODULE in ready:
        jobs.append({"slot": "registered-packet", "targets": LONG_MODULE, "budget": "275m", "timeout": 310})
    return jobs


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path)
    args = parser.parse_args()
    print(json.dumps({"include": partition(ready_modules(args.upstream))}, separators=(",", ":")))
