#!/usr/bin/env python3
"""Extract exactly the pinned FC definitions and types for a Lean kernel type check."""

from hashlib import sha256
from pathlib import Path
import argparse
import re


FC_COMMIT = "9097e2f90e66d2f6244209cb1c07f7120d17ec53"
FC_SHA256 = "cc80f1d6c45e59838775a20735d4d77df3bb0273a582ab26cfc2a1e6ca8d4591"
NAMES = ("erdos_535", "erdos_535.variants.first_open_case", "erdos_535.variants.sunflower_strong")
REDUCTIONS = ("erdos_535_of_sunflower", "first_open_case_of_sunflower", "sunflower_strong_of_sunflower")


def extract_definitions(source):
    names = ("NoConstantPairwiseGcdCoprimeSubsets", "AllBigOmega", "f")
    declarations = []
    for name in names:
        match = re.search(
            rf"^(?:noncomputable )?def {name} \([^\n]+\n(?:  [^\n]*\n)+",
            source,
            re.MULTILINE,
        )
        if match is None:
            raise ValueError(f"Cannot extract FC definition {name}")
        declarations.append(match[0].rstrip())
    return "\n\n".join(declarations)


def extract_types(source):
    for name in NAMES:
        match = re.search(
            rf"^theorem {re.escape(name)}(?P<binders>(?: \{{[^}}]+\}}| \([^()]+\))*)"
            r" :(?P<type>.*?) := by\n",
            source,
            re.MULTILINE | re.DOTALL,
        )
        if match is None:
            raise ValueError(f"Cannot extract FC theorem {name}")
        binders = match["binders"]
        if binders:
            yield f"∀{binders},\n   {match['type'].lstrip()}"
        else:
            yield match["type"].lstrip()


def generate(source, reduction):
    imported = "Erdos535.Reduction" if reduction else "Erdos535"
    names = REDUCTIONS if reduction else NAMES
    lines = [
        f"import {imported}",
        "set_option linter.unusedVariables false",
        "open ArithmeticFunction Filter Real",
        "open scoped omega Omega",
        "namespace FCReference",
        extract_definitions(source),
    ]
    for index, signature in enumerate(extract_types(source), 1):
        lines.append(f"def target{index} : Prop :=\n  {signature}")
    lines.append("end FCReference")
    lines.append("def propositionOf {p : Prop} (_ : p) : Prop := p")
    for index, theorem in enumerate(names, 1):
        parameters = " (h : Erdos535.ExponentialSunflowerStatement)" if reduction else ""
        application = " h" if reduction else ""
        lines.extend(
            [
                f"theorem target{index}_matches{parameters} :\n"
                f"    propositionOf (@Erdos535.{theorem}{application}) = FCReference.target{index} := rfl",
                f"#print axioms Erdos535.{theorem}",
            ]
        )
    return "\n\n".join(lines) + "\n"


def comparator_module(source, candidate):
    lines = [
        "import Erdos535" if candidate else
        "import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics\n"
        "import Mathlib.NumberTheory.ArithmeticFunction.Misc",
        "set_option linter.unusedVariables false",
        "open ArithmeticFunction Filter Real",
        "open scoped omega Omega",
        "namespace FCReference",
        extract_definitions(source),
    ]
    for name, signature in zip(NAMES, extract_types(source)):
        lines.append(f"def {name} : Prop :=\n  {signature}")
        if candidate:
            lines.append(f"example : {name} := @Erdos535.{name}")
    lines.append("end FCReference")
    return "\n\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fc_source", type=Path, help=f"upstream 535.lean at {FC_COMMIT}")
    parser.add_argument("output", type=Path, help="path of the generated Lean audit module")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--reduction", action="store_true", help="check only the conditional reductions")
    mode.add_argument("--comparator", choices=("challenge", "candidate"))
    args = parser.parse_args()
    raw = args.fc_source.read_bytes()
    if sha256(raw).hexdigest() != FC_SHA256:
        parser.error(f"expected unmodified 535.lean from FC commit {FC_COMMIT}")
    source = raw.decode()
    if args.comparator:
        module = comparator_module(source, candidate=args.comparator == "candidate")
    else:
        module = generate(source, args.reduction)
    args.output.write_text(module, encoding="utf-8")


if __name__ == "__main__":
    main()
