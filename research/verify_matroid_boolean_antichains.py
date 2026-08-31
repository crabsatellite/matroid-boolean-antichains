#!/usr/bin/env python3
"""Exact finite replay for Boolean antichains in matroid flat lattices."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, product as cartesian_product
from math import comb, factorial, prod
from typing import Any, Callable, Hashable, Iterable


Flat = frozenset[int]


@dataclass
class FiniteLattice:
    """Small exact lattice used to test the lattice-wide theorems."""

    name: str
    elements: tuple[Hashable, ...]
    leq_oracle: Callable[[Hashable, Hashable], bool]

    def __post_init__(self) -> None:
        self.bottom = next(
            element
            for element in self.elements
            if all(self.leq_oracle(element, other) for other in self.elements)
        )
        self.top = next(
            element
            for element in self.elements
            if all(self.leq_oracle(other, element) for other in self.elements)
        )
        self._meet: dict[tuple[Hashable, Hashable], Hashable] = {}
        self._join: dict[tuple[Hashable, Hashable], Hashable] = {}
        for left in self.elements:
            for right in self.elements:
                lowers = [
                    element
                    for element in self.elements
                    if self.leq_oracle(element, left)
                    and self.leq_oracle(element, right)
                ]
                uppers = [
                    element
                    for element in self.elements
                    if self.leq_oracle(left, element)
                    and self.leq_oracle(right, element)
                ]
                greatest = [
                    element
                    for element in lowers
                    if all(self.leq_oracle(other, element) for other in lowers)
                ]
                least = [
                    element
                    for element in uppers
                    if all(self.leq_oracle(element, other) for other in uppers)
                ]
                assert len(greatest) == len(least) == 1
                self._meet[left, right] = greatest[0]
                self._join[left, right] = least[0]
        self._height: dict[Hashable, int] = {}

        def compute_height(element: Hashable) -> int:
            if element in self._height:
                return self._height[element]
            predecessors = [
                other
                for other in self.elements
                if other != element and self.leq_oracle(other, element)
            ]
            value = 0 if not predecessors else 1 + max(
                compute_height(other) for other in predecessors
            )
            self._height[element] = value
            return value

        for element in self.elements:
            compute_height(element)

    def leq(self, left: Hashable, right: Hashable) -> bool:
        return self.leq_oracle(left, right)

    def meet(self, *elements: Hashable) -> Hashable:
        value = self.top
        for element in elements:
            value = self._meet[value, element]
        return value

    def join(self, *elements: Hashable) -> Hashable:
        value = self.bottom
        for element in elements:
            value = self._join[value, element]
        return value

    def height(self, element: Hashable) -> int:
        return self._height[element]


@dataclass(frozen=True)
class Matroid:
    name: str
    size: int
    rank_oracle: Callable[[Flat], int]

    @property
    def ground(self) -> Flat:
        return frozenset(range(self.size))

    def rank(self, subset: Iterable[int]) -> int:
        return self.rank_oracle(frozenset(subset))

    def closure(self, subset: Iterable[int]) -> Flat:
        subset = frozenset(subset)
        base_rank = self.rank(subset)
        return frozenset(
            element
            for element in self.ground
            if self.rank(subset | {element}) == base_rank
        )

    @property
    def bottom(self) -> Flat:
        return self.closure(())

    @property
    def total_rank(self) -> int:
        return self.rank(self.ground)

    def join(self, *flats: Flat) -> Flat:
        union: set[int] = set()
        for flat in flats:
            union.update(flat)
        return self.closure(union)

    def flats(self) -> list[Flat]:
        return [
            subset
            for mask in range(1 << self.size)
            if (subset := frozenset(i for i in range(self.size) if mask >> i & 1))
            == self.closure(subset)
        ]


def meet(selected: Iterable[Flat], top: Flat) -> Flat:
    selected = list(selected)
    return frozenset.intersection(*selected) if selected else top


def is_boolean_antichain(matroid: Matroid, family: tuple[Flat, ...]) -> bool:
    if any(flat == matroid.ground for flat in family):
        return False
    if any(a <= b or b <= a for a, b in combinations(family, 2)):
        return False
    k = len(family)
    meets: dict[int, Flat] = {}
    for mask in range(1 << k):
        meets[mask] = meet(
            (family[index] for index in range(k) if mask >> index & 1),
            matroid.ground,
        )
    if len(set(meets.values())) != 1 << k:
        return False
    for left in range(1 << k):
        for right in range(1 << k):
            if matroid.join(meets[left], meets[right]) != meets[left & right]:
                return False
    return True


def boolean_antichains(matroid: Matroid, size: int) -> set[tuple[Flat, ...]]:
    proper = [flat for flat in matroid.flats() if flat != matroid.ground]
    return {
        tuple(sorted(family, key=lambda flat: (len(flat), tuple(flat))))
        for family in combinations(proper, size)
        if is_boolean_antichain(matroid, family)
    }


def is_boolean_in_finite_lattice(
    lattice: FiniteLattice, family: tuple[Hashable, ...]
) -> bool:
    if any(element == lattice.top for element in family):
        return False
    if any(
        lattice.leq(left, right) or lattice.leq(right, left)
        for left, right in combinations(family, 2)
    ):
        return False
    k = len(family)
    faces = {
        mask: lattice.meet(
            *(family[index] for index in range(k) if mask >> index & 1)
        )
        for mask in range(1 << k)
    }
    if len(set(faces.values())) != 1 << k:
        return False
    return all(
        lattice.join(faces[left], faces[right]) == faces[left & right]
        for left in range(1 << k)
        for right in range(1 << k)
    )


def is_boolean_by_height_gaps(
    lattice: FiniteLattice, family: tuple[Hashable, ...]
) -> bool:
    k = len(family)
    bottom = lattice.meet(*family)
    atoms = tuple(
        lattice.meet(*(family[j] for j in range(k) if j != index))
        for index in range(k)
    )
    if any(lattice.height(atom) <= lattice.height(bottom) for atom in atoms):
        return False
    for mask in range(1 << k):
        atom_join = lattice.join(
            bottom, *(atoms[index] for index in range(k) if mask >> index & 1)
        )
        opposite_meet = lattice.meet(
            *(family[index] for index in range(k) if not (mask >> index & 1))
        )
        if lattice.height(atom_join) != lattice.height(opposite_meet):
            return False
    return True


def finite_lattice_boolean_counts(lattice: FiniteLattice) -> list[int]:
    proper = [element for element in lattice.elements if element != lattice.top]
    return [
        sum(
            is_boolean_in_finite_lattice(lattice, family)
            for family in combinations(proper, k)
        )
        for k in range(lattice.height(lattice.top) + 1)
    ]


def lattice_product(
    name: str, left: FiniteLattice, right: FiniteLattice
) -> FiniteLattice:
    elements = tuple(
        (left_element, right_element)
        for left_element in left.elements
        for right_element in right.elements
    )
    return FiniteLattice(
        name,
        elements,
        lambda first, second: left.leq(first[0], second[0])
        and right.leq(first[1], second[1]),
    )


def product_boolean_count(left: list[int], right: list[int], k: int) -> int:
    total = 0
    for a in range(min(k, len(left) - 1) + 1):
        for b in range(min(k, len(right) - 1) + 1):
            if a + b < k:
                continue
            coefficient = factorial(a) * factorial(b)
            coefficient //= (
                factorial(k - a)
                * factorial(k - b)
                * factorial(a + b - k)
            )
            total += coefficient * left[a] * right[b]
    return total


def is_boolean_by_reconstruction_gaps(
    matroid: Matroid, family: tuple[Flat, ...]
) -> bool:
    """Exact 2^k rank-gap certificate for the Boolean meet map."""
    k = len(family)
    bottom = meet(family, matroid.ground)
    atoms = tuple(
        meet(
            (family[j] for j in range(k) if j != index),
            matroid.ground,
        )
        for index in range(k)
    )
    if any(matroid.rank(atom) <= matroid.rank(bottom) for atom in atoms):
        return False
    for mask in range(1 << k):
        atom_join = matroid.join(
            bottom,
            *(atoms[index] for index in range(k) if mask >> index & 1),
        )
        opposite_meet = meet(
            (family[index] for index in range(k) if not (mask >> index & 1)),
            matroid.ground,
        )
        if matroid.rank(atom_join) != matroid.rank(opposite_meet):
            return False
    return True


def interval_atoms(matroid: Matroid, bottom: Flat, top: Flat) -> list[Flat]:
    bottom_rank = matroid.rank(bottom)
    return [
        flat
        for flat in matroid.flats()
        if bottom < flat <= top and matroid.rank(flat) == bottom_rank + 1
    ]


def interval_bases(matroid: Matroid, bottom: Flat, top: Flat) -> set[tuple[Flat, ...]]:
    relative_rank = matroid.rank(top) - matroid.rank(bottom)
    if relative_rank == 0:
        return {()}
    atoms = interval_atoms(matroid, bottom, top)
    return {
        tuple(sorted(basis, key=lambda flat: (len(flat), tuple(flat))))
        for basis in combinations(atoms, relative_rank)
        if matroid.join(*basis) == top
    }


def antichain_from_atoms(matroid: Matroid, bottom: Flat, atoms: tuple[Flat, ...]) -> tuple[Flat, ...]:
    coatoms = []
    for omitted in range(len(atoms)):
        retained = [atom for index, atom in enumerate(atoms) if index != omitted]
        coatoms.append(matroid.join(bottom, *retained))
    return tuple(sorted(coatoms, key=lambda flat: (len(flat), tuple(flat))))


def atoms_from_antichain(matroid: Matroid, family: tuple[Flat, ...]) -> tuple[Flat, ...]:
    atoms = []
    for omitted in range(len(family)):
        retained = [flat for index, flat in enumerate(family) if index != omitted]
        atoms.append(meet(retained, matroid.ground))
    return tuple(sorted(atoms, key=lambda flat: (len(flat), tuple(flat))))


def maximum_bijection_check(matroid: Matroid) -> None:
    rank = matroid.total_rank
    antichains = boolean_antichains(matroid, rank)
    bases = interval_bases(matroid, matroid.bottom, matroid.ground)
    assert {atoms_from_antichain(matroid, family) for family in antichains} == bases
    assert {antichain_from_atoms(matroid, matroid.bottom, basis) for basis in bases} == antichains


def weighted_basis_check(matroid: Matroid, weights: list[int]) -> None:
    rank = matroid.total_rank
    element_bases = [
        subset
        for subset in combinations(range(matroid.size), rank)
        if matroid.rank(subset) == rank
    ]
    direct = sum(prod(weights[element] for element in basis) for basis in element_bases)
    via_antichains = 0
    for family in boolean_antichains(matroid, rank):
        atoms = atoms_from_antichain(matroid, family)
        via_antichains += prod(
            sum(weights[element] for element in atom - matroid.bottom)
            for atom in atoms
        )
    assert direct == via_antichains


def rank_tight_check(matroid: Matroid) -> None:
    rank = matroid.total_rank
    for size in range(rank + 1):
        actual = {
            family
            for family in boolean_antichains(matroid, size)
            if matroid.rank(meet(family, matroid.ground)) == rank - size
        }
        predicted: set[tuple[Flat, ...]] = set()
        for bottom in matroid.flats():
            if matroid.rank(bottom) != rank - size:
                continue
            for basis in interval_bases(matroid, bottom, matroid.ground):
                predicted.add(antichain_from_atoms(matroid, bottom, basis))
        assert actual == predicted


def mobius_to_top(matroid: Matroid) -> dict[Flat, int]:
    flats = sorted(matroid.flats(), key=lambda flat: matroid.rank(flat), reverse=True)
    values: dict[Flat, int] = {}
    for flat in flats:
        if flat == matroid.ground:
            values[flat] = 1
        else:
            values[flat] = -sum(value for upper, value in values.items() if flat < upper)
    return values


def boolean_pairs_by_mobius(matroid: Matroid) -> int:
    flats = matroid.flats()
    mobius = mobius_to_top(matroid)
    ordered_spanning_pairs = sum(
        mobius[flat] * sum(lower <= flat for lower in flats) ** 2
        for flat in flats
    )
    return (ordered_spanning_pairs - 2 * len(flats) + 1) // 2


def uniform(name: str, rank: int, size: int) -> Matroid:
    return Matroid(name, size, lambda subset: min(rank, len(subset)))


def stirling_second(total: int, blocks: int) -> int:
    table = [[0] * (blocks + 1) for _ in range(total + 1)]
    table[0][0] = 1
    for n in range(1, total + 1):
        for k in range(1, min(n, blocks) + 1):
            table[n][k] = table[n - 1][k - 1] + k * table[n - 1][k]
    return table[total][blocks]


def bell_numbers(maximum: int) -> list[int]:
    values = [0] * (maximum + 1)
    values[0] = 1
    for n in range(1, maximum + 1):
        values[n] = sum(comb(n - 1, j) * values[j] for j in range(n))
    return values


def partition_lattice_boolean_pairs(n: int) -> int:
    bell = bell_numbers(n)
    weighted = [[0] * (n + 1) for _ in range(n + 1)]
    weighted[0][0] = 1
    for size in range(1, n + 1):
        for blocks in range(1, size + 1):
            weighted[size][blocks] = sum(
                comb(size - 1, first_size - 1)
                * bell[first_size] ** 2
                * weighted[size - first_size][blocks - 1]
                for first_size in range(1, size + 1)
            )
    ordered = sum(
        (-1) ** (blocks - 1) * factorial(blocks - 1) * weighted[n][blocks]
        for blocks in range(1, n + 1)
    )
    return (ordered - 2 * bell[n] + 1) // 2


def is_boolean_family_in_ideal_lattice(family: tuple[Flat, ...], top: Flat) -> bool:
    if any(ideal == top for ideal in family):
        return False
    if any(left <= right or right <= left for left, right in combinations(family, 2)):
        return False
    k = len(family)
    meets = {
        mask: meet((family[index] for index in range(k) if mask >> index & 1), top)
        for mask in range(1 << k)
    }
    if len(set(meets.values())) != 1 << k:
        return False
    return all(
        meets[left] | meets[right] == meets[left & right]
        for left in range(1 << k)
        for right in range(1 << k)
    )


def order_ideals(size: int, relations: set[tuple[int, int]]) -> list[Flat]:
    result = []
    for mask in range(1 << size):
        subset = frozenset(i for i in range(size) if mask >> i & 1)
        if all(upper not in subset or lower in subset for lower, upper in relations):
            result.append(subset)
    return result


def distributive_boolean_counts(size: int, relations: set[tuple[int, int]]) -> list[int]:
    ideals = order_ideals(size, relations)
    top = frozenset(range(size))
    direct = [
        sum(
            is_boolean_family_in_ideal_lattice(tuple(family), top)
            for family in combinations([ideal for ideal in ideals if ideal != top], k)
        )
        for k in range(size + 1)
    ]
    filters = [top - ideal for ideal in ideals if ideal != top]
    via_filters = [
        sum(all(left.isdisjoint(right) for left, right in combinations(family, 2)) for family in combinations(filters, k))
        for k in range(size + 1)
    ]
    assert direct == via_filters
    return direct


def positive_compositions(total: int, parts: int):
    if parts == 0:
        if total == 0:
            yield ()
        return
    for first in range(1, total - parts + 2):
        for tail in positive_compositions(total - first, parts - 1):
            yield (first,) + tail


def uniform_all_boolean_count(size: int, rank: int, k: int) -> int:
    """Closed block-partition count for all Boolean antichains in U(rank,size)."""
    if k == 0:
        return 1
    if k == 1:
        return sum(comb(size, bottom_size) for bottom_size in range(rank))
    ordered = 0
    for bottom_size in range(rank):
        remaining = size - bottom_size
        for used in range(k, remaining + 1):
            for block_sizes in positive_compositions(used, k):
                if bottom_size + used < rank:
                    continue
                if any(
                    bottom_size + used - block_size >= rank
                    for block_size in block_sizes
                ):
                    continue
                multinomial = factorial(remaining) // factorial(remaining - used)
                multinomial //= prod(factorial(block_size) for block_size in block_sizes)
                ordered += comb(size, bottom_size) * multinomial
    return ordered // factorial(k)


def gl_order(dimension: int, q: int) -> int:
    return prod(q**dimension - q**index for index in range(dimension))


def gaussian_binomial(n: int, k: int, q: int) -> int:
    if k < 0 or k > n:
        return 0
    numerator = prod(q ** (n - index) - 1 for index in range(k))
    denominator = prod(q ** (k - index) - 1 for index in range(k))
    return numerator // denominator


def direct_sum_decompositions(dimension: int, parts: int, q: int) -> int:
    return sum(
        gl_order(dimension, q) // prod(gl_order(part, q) for part in composition)
        for composition in positive_compositions(dimension, parts)
    ) // factorial(parts)


def subspace_boolean_count(dimension: int, size: int, q: int) -> int:
    if size == 0:
        return 1
    return sum(
        gaussian_binomial(dimension, quotient_dimension, q)
        * direct_sum_decompositions(quotient_dimension, size, q)
        for quotient_dimension in range(size, dimension + 1)
    )


def projective_plane_boolean_counts(q: int) -> list[int]:
    points = q * q + q + 1
    return [
        1,
        2 * points + 1,
        comb(points, 2) + points * q * q,
        comb(points, 3) - points * comb(q + 1, 3),
    ]


def binary(name: str, columns: list[int]) -> Matroid:
    def rank(subset: Flat) -> int:
        pivots: dict[int, int] = {}
        for index in subset:
            value = columns[index]
            while value:
                pivot = value.bit_length() - 1
                if pivot in pivots:
                    value ^= pivots[pivot]
                else:
                    pivots[pivot] = value
                    break
        return len(pivots)

    return Matroid(name, len(columns), rank)


def graphic(name: str, vertices: int, edges: list[tuple[int, int]]) -> Matroid:
    def rank(subset: Flat) -> int:
        parent = list(range(vertices))

        def find(vertex: int) -> int:
            while parent[vertex] != vertex:
                parent[vertex] = parent[parent[vertex]]
                vertex = parent[vertex]
            return vertex

        for index in subset:
            left, right = edges[index]
            left_root, right_root = find(left), find(right)
            if left_root != right_root:
                parent[left_root] = right_root
        components = len({find(vertex) for vertex in range(vertices)})
        return vertices - components

    return Matroid(name, len(edges), rank)


def main() -> None:
    chain_two = FiniteLattice("B1", (0, 1), lambda left, right: left <= right)
    diamond = FiniteLattice(
        "M3",
        (0, 1, 2, 3, 4),
        lambda left, right: left == right or left == 0 or right == 4,
    )
    pentagon = FiniteLattice(
        "N5",
        (0, 1, 2, 3, 4),
        lambda left, right: left == right
        or left == 0
        or right == 4
        or (left == 1 and right == 2),
    )
    boolean_two = lattice_product("B2", chain_two, chain_two)
    boolean_three = lattice_product("B3", boolean_two, chain_two)
    pentagon_product = lattice_product("N5xB1", pentagon, chain_two)
    diamond_product = lattice_product("M3xB1", diamond, chain_two)

    assert finite_lattice_boolean_counts(diamond) == [1, 4, 3]
    assert finite_lattice_boolean_counts(pentagon) == [1, 4, 2, 0]
    assert finite_lattice_boolean_counts(boolean_three) == [1, 7, 6, 1]

    for lattice in (
        chain_two,
        diamond,
        pentagon,
        boolean_two,
        pentagon_product,
        diamond_product,
    ):
        proper = [element for element in lattice.elements if element != lattice.top]
        for k in range(lattice.height(lattice.top) + 1):
            for family in combinations(proper, k):
                assert is_boolean_in_finite_lattice(lattice, family) == (
                    is_boolean_by_height_gaps(lattice, family)
                )

    for left, right, product_lattice in (
        (chain_two, chain_two, boolean_two),
        (boolean_two, chain_two, boolean_three),
        (pentagon, chain_two, pentagon_product),
        (diamond, chain_two, diamond_product),
    ):
        left_counts = finite_lattice_boolean_counts(left)
        right_counts = finite_lattice_boolean_counts(right)
        product_counts = finite_lattice_boolean_counts(product_lattice)
        assert product_counts == [
            product_boolean_count(left_counts, right_counts, k)
            for k in range(len(product_counts))
        ]

    examples = [
        uniform("U(2,4)", 2, 4),
        uniform("U(3,5)", 3, 5),
        binary("parallel-and-loop", [0b01, 0b01, 0b10, 0b10, 0]),
        binary("Fano", [0b001, 0b010, 0b100, 0b011, 0b101, 0b110, 0b111]),
        graphic("C4", 4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
        graphic("K4", 4, list(combinations(range(4), 2))),
        graphic("two-triangles", 6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]),
    ]
    for index, matroid in enumerate(examples):
        maximum_bijection_check(matroid)
        rank_tight_check(matroid)
        weighted_basis_check(matroid, [2 + index + element for element in range(matroid.size)])
        maximum_count = len(boolean_antichains(matroid, matroid.total_rank))
        simplified_bases = len(interval_bases(matroid, matroid.bottom, matroid.ground))
        assert maximum_count == simplified_bases
        assert len(boolean_antichains(matroid, 2)) == boolean_pairs_by_mobius(matroid)
        for k in range(matroid.total_rank + 1):
            for family in combinations(
                [flat for flat in matroid.flats() if flat != matroid.ground], k
            ):
                direct_boolean = is_boolean_antichain(matroid, family)
                rank_gap_boolean = is_boolean_by_reconstruction_gaps(matroid, family)
                assert direct_boolean == rank_gap_boolean, (
                    matroid.name,
                    family,
                    direct_boolean,
                    rank_gap_boolean,
                )
        print(
            f"{matroid.name}: rank={matroid.total_rank} flats={len(matroid.flats())} "
            f"maximum_boolean_antichains={maximum_count}"
        )

    # Rank-tight closed forms in the two lattice families emphasized by the
    # source paper.
    for n in range(1, 6):
        free = uniform(f"free-{n}", n, n)
        for k in range(n + 1):
            tight = sum(
                free.rank(meet(family, free.ground)) == n - k
                for family in boolean_antichains(free, k)
            )
            assert tight == comb(n, k)
            assert len(boolean_antichains(free, k)) == stirling_second(n + 1, k + 1)
        assert len(boolean_antichains(free, 2)) == (3**n - 2 ** (n + 1) + 1) // 2

    for n in range(2, 5):
        complete = graphic(f"K{n}-partition", n, list(combinations(range(n), 2)))
        for k in range(1, n):
            tight = sum(
                complete.rank(meet(family, complete.ground)) == (n - 1) - k
                for family in boolean_antichains(complete, k)
            )
            assert tight == stirling_second(n, k + 1) * (k + 1) ** (k - 1)
        assert len(boolean_antichains(complete, 2)) == partition_lattice_boolean_pairs(n)

    for rank, size in ((2, 4), (3, 5), (4, 5)):
        matroid = uniform(f"U({rank},{size})-tight", rank, size)
        for k in range(rank + 1):
            tight = sum(
                matroid.rank(meet(family, matroid.ground)) == rank - k
                for family in boolean_antichains(matroid, k)
            )
            expected = 1 if k == 0 else comb(size, rank - 1) if k == 1 else comb(size, rank) * comb(rank, k)
            assert tight == expected

    # The rank-gap theorem closes every layer of a uniform matroid.  The
    # formula counts a bottom set, ordered nonempty disjoint atom blocks, and
    # a leftover set, then divides by the free permutation action on blocks.
    for rank, size in ((2, 4), (3, 4), (3, 5), (4, 5), (4, 6)):
        matroid = uniform(f"U({rank},{size})-all", rank, size)
        for k in range(rank + 1):
            assert len(boolean_antichains(matroid, k)) == uniform_all_boolean_count(
                size, rank, k
            )

    # The unrestricted smaller-size statement is false: these two disjoint
    # rank-two flats form a Boolean antichain in U(3,4), but its bottom has
    # rank zero rather than the rank-one bottom required by rank-tightness.
    u34 = uniform("U(3,4)", 3, 4)
    non_tight = (frozenset({0, 1}), frozenset({2, 3}))
    assert is_boolean_antichain(u34, non_tight)
    assert u34.rank(meet(non_tight, u34.ground)) == 0 < 1
    for k in range(u34.total_rank + 1):
        ordered_gap_count = sum(
            is_boolean_by_reconstruction_gaps(u34, family)
            for family in cartesian_product(u34.flats(), repeat=k)
        )
        assert ordered_gap_count == factorial(k) * len(boolean_antichains(u34, k))

    # Complementarity against the opposite meet is not sufficient at k=3.
    u45 = uniform("U(4,5)-local-obstruction", 4, 5)
    complement_only = (
        frozenset({0, 1, 2}),
        frozenset({0, 1, 3}),
        frozenset({2, 3, 4}),
    )
    assert all(
        u45.join(
            complement_only[index],
            meet(
                (
                    complement_only[j]
                    for j in range(len(complement_only))
                    if j != index
                ),
                u45.ground,
            ),
        )
        == u45.ground
        for index in range(len(complement_only))
    )
    assert not is_boolean_antichain(u45, complement_only)
    assert not is_boolean_by_reconstruction_gaps(u45, complement_only)

    # Booleanity is not three-local: every triple below is Boolean, but the
    # four-member family has a genuine higher reconstruction gap.
    local_binary = binary("binary-three-local-obstruction", [2, 8, 15, 4, 22, 27, 31, 18])
    three_local_only = (
        frozenset({0, 1, 2, 4, 5}),
        frozenset({0, 1, 3, 5, 6}),
        frozenset({1, 2, 3, 4, 7}),
        frozenset({0, 2, 6, 7}),
    )
    assert all(
        is_boolean_antichain(local_binary, triple)
        for triple in combinations(three_local_only, 3)
    )
    assert not is_boolean_antichain(local_binary, three_local_only)
    assert not is_boolean_by_reconstruction_gaps(local_binary, three_local_only)

    # Parallel elements distinguish original bases from lattice objects.
    parallel = binary("parallel-pairs", [0b01, 0b01, 0b10, 0b10])
    assert len(boolean_antichains(parallel, 2)) == 1
    assert sum(
        parallel.rank(basis) == 2 for basis in combinations(range(parallel.size), 2)
    ) == 4

    assert [partition_lattice_boolean_pairs(n) for n in range(1, 8)] == [0, 0, 3, 45, 620, 9750, 183680]

    # Complete distributive-lattice classification: complements of the ideals
    # are pairwise disjoint nonempty order filters.
    for n in range(1, 6):
        antichain_counts = distributive_boolean_counts(n, set())
        assert antichain_counts == [stirling_second(n + 1, k + 1) for k in range(n + 1)]
        chain_relations = {(lower, upper) for lower in range(n) for upper in range(lower + 1, n)}
        chain_counts = distributive_boolean_counts(n, chain_relations)
        assert chain_counts == [1, n] + [0] * (n - 1)
    assert distributive_boolean_counts(3, {(0, 2), (1, 2)}) == [1, 4, 0, 0]

    # Complete subspace-lattice formula over F_2, replayed through dimension 3.
    for dimension in range(1, 4):
        projective = binary(
            f"PG({dimension - 1},2)",
            list(range(1, 1 << dimension)),
        )
        for k in range(dimension + 1):
            assert len(boolean_antichains(projective, k)) == subspace_boolean_count(dimension, k, 2)
    assert [subspace_boolean_count(3, k, 2) for k in range(4)] == [1, 15, 49, 28]
    assert projective_plane_boolean_counts(2) == [1, 15, 49, 28]

    print("matroid_boolean_antichains=passed finite-lattice-height-gap product-convolution projective-plane-all-sizes global-rank-gap-classification uniform-all-sizes maximum-bijection weighted-bases intervals rank-tight size-two-mobius distributive-all-sizes subspace-all-sizes closed-families negative-boundaries")


if __name__ == "__main__":
    main()
