#!/usr/bin/env python3
"""Exploratory finite checks for possible global Boolean-frame criteria."""

from __future__ import annotations

from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations
from pathlib import Path
from random import Random
import sys


VERIFY = Path(__file__).with_name("verify_matroid_boolean_antichains.py")
SPEC = spec_from_file_location("matroid_boolean_verify", VERIFY)
assert SPEC is not None and SPEC.loader is not None
MODULE = module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def complementary_coatoms(matroid, family) -> bool:
    """Test H_i join (meet of the other H_j) = top for every i."""
    if any(flat == matroid.ground for flat in family):
        return False
    return all(
        matroid.join(
            family[index],
            MODULE.meet(
                (family[j] for j in range(len(family)) if j != index),
                matroid.ground,
            ),
        )
        == matroid.ground
        for index in range(len(family))
    )


def scan(matroid, size: int) -> tuple[int, int, tuple | None]:
    proper = [flat for flat in matroid.flats() if flat != matroid.ground]
    candidates = 0
    booleans = 0
    witness = None
    for family in combinations(proper, size):
        if not complementary_coatoms(matroid, family):
            continue
        candidates += 1
        if MODULE.is_boolean_antichain(matroid, family):
            booleans += 1
        elif witness is None:
            witness = family
    return candidates, booleans, witness


def scan_three_local(matroid, size: int) -> tuple[int, int, tuple | None]:
    """Compare Booleanity with Booleanity of every three-member subfamily."""
    proper = [flat for flat in matroid.flats() if flat != matroid.ground]
    candidates = 0
    booleans = 0
    witness = None
    for family in combinations(proper, size):
        if not all(
            MODULE.is_boolean_antichain(matroid, triple)
            for triple in combinations(family, 3)
        ):
            continue
        candidates += 1
        if MODULE.is_boolean_antichain(matroid, family):
            booleans += 1
        elif witness is None:
            witness = family
    return candidates, booleans, witness


def fast_three_local_four_witness(matroid):
    proper = [flat for flat in matroid.flats() if flat != matroid.ground]
    triples = {
        index_triple
        for index_triple in combinations(range(len(proper)), 3)
        if MODULE.is_boolean_antichain(
            matroid, tuple(proper[index] for index in index_triple)
        )
    }
    for a, b, c in triples:
        for d in range(c + 1, len(proper)):
            if (
                (a, b, d) in triples
                and (a, c, d) in triples
                and (b, c, d) in triples
            ):
                family = tuple(proper[index] for index in (a, b, c, d))
                if not MODULE.is_boolean_antichain(matroid, family):
                    return family
    return None


def main() -> None:
    matroids = [
        MODULE.uniform("U(4,5)", 4, 5),
        MODULE.uniform("U(4,6)", 4, 6),
        MODULE.uniform("U(5,6)", 5, 6),
        MODULE.graphic(
            "K5",
            5,
            [(i, j) for i in range(5) for j in range(i + 1, 5)],
        ),
        MODULE.graphic(
            "K3,3",
            6,
            [(i, j) for i in range(3) for j in range(3, 6)],
        ),
    ]
    for matroid in matroids:
        candidates, booleans, witness = scan(matroid, 3)
        print(
            matroid.name,
            f"candidates={candidates}",
            f"booleans={booleans}",
            f"false_positive={witness}",
        )
        if matroid.total_rank >= 4 and matroid.size <= 6:
            local, global_count, local_witness = scan_three_local(matroid, 4)
            print(
                matroid.name,
                "three-local-size-4",
                f"candidates={local}",
                f"booleans={global_count}",
                f"false_positive={local_witness}",
            )

    random = Random(20260830)
    projective_points = list(range(1, 1 << 5))
    for sample in range(12):
        columns = random.sample(projective_points, 8)
        matroid = MODULE.binary(f"binary-sample-{sample}", columns)
        witness = fast_three_local_four_witness(matroid)
        print(matroid.name, "three-local-witness", witness)
        if witness is not None:
            break


if __name__ == "__main__":
    main()
