"""Exact checks for the p^3*q B2 branch via mod 16/mod 4 and descent.

The pure Python checks reproduce the finite residue implications and polynomial
homogeneity used by P3Parity.lean. The induction and connection with the original
cuboid remain mathematical deductions; this is not an execution of Lean.
"""

from itertools import product

from verify_arithmetic import Polynomial


def difference(p, a, b, d, s, v):
    return (p * (2 * a * s + b * v))**2 - 4 * d * s * v


def addition(p, a, b, d, e, s, v):
    return (p * (2 * a * s + b * v))**2 - 2 * ((d * s)**2 + (e * v)**2)


def check_difference_residues():
    pairs = [(s, v) for s, v in product(range(16), repeat=2) if s % 2 or v % 2]
    count = 0
    for p, a, b, d in product(range(1, 16, 2), repeat=4):
        for s, v in pairs:
            if difference(p, a, b, d, s, v) % 16 == 0:
                raise AssertionError((p, a, b, d, s, v))
            count += 1
    return count


def check_sum_residues():
    pairs = [(s, v) for s, v in product(range(4), repeat=2) if s % 2 or v % 2]
    count = 0
    for p, b, d in product((1, 3), repeat=3):
        for a, e in product(range(4), repeat=2):
            for s, v in pairs:
                if addition(p, a, b, d, e, s, v) % 4 == 0:
                    raise AssertionError((p, a, b, d, e, s, v))
                count += 1
    return count


def check_homogeneity():
    p, a, b, d, e, s, v = map(Polynomial.variable, ("p", "a", "b", "d", "R", "S", "V"))
    left = difference(p, a, b, d, 2 * s, 2 * v) - 4 * difference(p, a, b, d, s, v)
    right = addition(p, a, b, d, e, 2 * s, 2 * v) - 4 * addition(p, a, b, d, e, s, v)
    if left.coefficients or right.coefficients:
        raise AssertionError("The proposed relations are not homogeneous of degree two in S,V.")


def main():
    check_homogeneity()
    print(f"B2 difference: all {check_difference_residues()} admissible residue tuples rejected.")
    print(f"B2 sum: all {check_sum_residues()} admissible residue tuples rejected.")
    print("Two polynomial homogeneity identities hold coefficient by coefficient.")


if __name__ == "__main__":
    main()

