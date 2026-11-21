"""Exact audits of selected arithmetic in the p^2*q and p^3*q cuboid proofs.

Python standard library only. Polynomial equalities are checked coefficient by
coefficient in Z[x_1,...,x_n], not by sampling the symbols. The residue checks
cover every admissible residue in the stated finite rings. The case census uses
finite index sets. This script does not establish Gaussian unique factorization,
prime-power cancellation, or the deductions connecting all of these checks to
the two complete cuboid theorems. It is not a proof-assistant kernel replay.
"""

from collections import Counter
from itertools import combinations, product
from math import comb


VARIABLES = "m n u v p q R S T W X Y U V M N h d a b".split()
ZERO_POWERS = (0,) * len(VARIABLES)


class Polynomial:
    """A sparse polynomial in fixed indeterminates with integer coefficients."""

    def __init__(self, coefficients):
        self.coefficients = {powers: value for powers, value in coefficients.items() if value}

    @classmethod
    def variable(cls, name):
        index = VARIABLES.index(name)
        powers = tuple(int(i == index) for i in range(len(VARIABLES)))
        return cls({powers: 1})

    @classmethod
    def of(cls, value):
        return value if isinstance(value, cls) else cls({ZERO_POWERS: value})

    def __add__(self, other):
        values = self.coefficients.copy()
        for powers, coefficient in self.of(other).coefficients.items():
            values[powers] = values.get(powers, 0) + coefficient
        return self.__class__(values)

    __radd__ = __add__

    def __neg__(self):
        return self.__class__({powers: -value for powers, value in self.coefficients.items()})

    def __sub__(self, other):
        return self + -self.of(other)

    def __rsub__(self, other):
        return self.of(other) + -self

    def __mul__(self, other):
        values = {}
        for left, coefficient in self.coefficients.items():
            for right, multiplier in self.of(other).coefficients.items():
                powers = tuple(a + b for a, b in zip(left, right))
                values[powers] = values.get(powers, 0) + coefficient * multiplier
        return self.__class__(values)

    __rmul__ = __mul__

    def __pow__(self, n):
        if not isinstance(n, int) or n < 0:
            raise ValueError("The checker only accepts nonnegative integer polynomial powers.")
        result = self.of(1)
        for _ in range(n):
            result *= self
        return result


m, n, u, v, p, q, R, S, T, W, X, Y, U, V, M, N, h, d, a, b = map(
    Polynomial.variable, VARIABLES
)
CHECKS = Counter()


def check(condition, group, description):
    if not condition:
        raise AssertionError(f"{group}: {description}")
    CHECKS[group] += 1


def equal(left, right, group, description):
    check(not (Polynomial.of(left) - right).coefficients, group, description)


def gaussian_mul(left, right):
    x, y = left
    z, w = right
    return x * z - y * w, x * w + y * z


def gaussian_pow(value, n):
    result = (Polynomial.of(1), Polynomial.of(0))
    for _ in range(n):
        result = gaussian_mul(result, value)
    return result


def gaussian_norm(value):
    real, imaginary = value
    return real**2 + imaginary**2


def gaussian_scale(value, scale):
    return value[0] * scale, value[1] * scale


def conj(value):
    return value[0], -value[1]


def gaussian_equal(left, right, group, description):
    equal(left[0], right[0], group, description + " real part")
    equal(left[1], right[1], group, description + " imaginary part")


def representative_indices(k):
    # Conjugation identifies (j,l) and (-j,-l). The zero pair is degenerate.
    return ((0, 1),) + tuple((j, l) for j in range(1, k + 1) for l in (-1, 0, 1))


def check_gaussian_formulas():
    group = "Gaussian polynomial identities"
    pi = (m, n)
    rho = (u, v)
    P = m**2 + n**2
    Q = u**2 + v**2
    pi_2 = (m**2 - n**2, 2 * m * n)
    rho_2 = (u**2 - v**2, 2 * u * v)
    gaussian_equal(gaussian_pow(pi, 2), pi_2, group, "pi^2")
    gaussian_equal(gaussian_pow(rho, 2), rho_2, group, "rho^2")
    gaussian_equal(gaussian_pow((R, S), 2), (R**2 - S**2, 2 * R * S), group, "pi^4")
    gaussian_equal(
        gaussian_pow((R, S), 3),
        (R * (R**2 - 3 * S**2), S * (3 * R**2 - S**2)),
        group,
        "pi^6",
    )
    equal(
        gaussian_pow((R, S), 5)[0],
        R * (R**4 - 10 * R**2 * S**2 + 5 * S**4),
        group,
        "real part of pi^10",
    )
    equal(
        gaussian_norm(gaussian_mul((R, S), (U, V))),
        (R**2 + S**2) * (U**2 + V**2),
        group,
        "multiplicativity of the Gaussian norm",
    )

    for k in (2, 3):
        reps = representative_indices(k)
        for j, l in reps:
            literal = gaussian_mul(
                gaussian_mul(gaussian_pow(pi, k + j), gaussian_pow(conj(pi), k - j)),
                gaussian_mul(gaussian_pow(rho, 1 + l), gaussian_pow(conj(rho), 1 - l)),
            )
            phase = gaussian_pow(pi_2, j)
            if not l:
                expected = gaussian_scale(phase, P ** (k - j) * Q)
            else:
                second = rho_2 if l == 1 else conj(rho_2)
                expected = gaussian_scale(gaussian_mul(phase, second), P ** (k - j))
            gaussian_equal(literal, expected, group, f"k={k}, exponent state {(j, l)}")
            equal(gaussian_norm(expected), (P**k * Q) ** 2, group, f"norm of state {(k, j, l)}")


def check_cancellation_identities():
    group = "Sum, difference, and cancellation identities"
    for upper_real, upper_imag, k in ((T, W, 2), (X, Y, 3)):
        F = upper_imag * U + upper_real * V
        G = upper_imag * U - upper_real * V
        equal(F**2 - G**2, 4 * upper_real * upper_imag * U * V, group, f"k={k}, F^2-G^2")
        equal(
            F**2 + G**2,
            2 * (upper_imag**2 * U**2 + upper_real**2 * V**2),
            group,
            f"k={k}, F^2+G^2",
        )
        q_squared = U**2 + V**2
        p_to_2k = upper_real**2 + upper_imag**2
        equal(
            F**2 + G**2 - upper_imag**2 * q_squared,
            2 * (upper_real**2 - upper_imag**2) * V**2 + upper_imag**2 * q_squared,
            group,
            f"k={k}, top type A hypotenuse",
        )
        equal(
            F**2 + G**2 - p_to_2k * V**2,
            2 * upper_imag**2 * U**2 - (p_to_2k - 2 * upper_real**2) * V**2,
            group,
            f"k={k}, type C hypotenuse",
        )

    equal((R**2 + S**2) * S**2 - 2 * (2 * R * S) ** 2, S**2 * (S**2 - 7 * R**2),
          group, "p^2*q type A parity bracket")
    equal((R - S) * (R + S), R**2 - S**2, group, "difference of squares (R,S)")
    equal((M - N) * (M + N), M**2 - N**2, group, "difference of squares (M,N)")
    equal((u - v) * (u + v), u**2 - v**2, group, "difference of squares (u,v)")
    equal(2 * (R + S) * (R - S), 2 * (R**2 - S**2), group, "difference identity with factor two")
    equal((R + S)**2 - (R - S)**2, 4 * R * S, group, "factor values determine twice the imaginary part")
    equal((U**2 + V**2) - 2 * U * V, (U - V)**2, group, "UV upper bound")
    equal((U**2 + V**2) + 2 * U * V, (U + V)**2, group, "negative UV upper bound")
    equal((a + p * h) ** 2 + 1, (a**2 + 1) + 2 * p * a * h + p**2 * h**2,
          group, "one-step Hensel lifting identity")


def check_discriminants():
    group = "p^3*q discriminant identities"
    equal(
        (2 * a * U + b * V) ** 2 - (b**2 - 4 * a * h) * V**2,
        4 * a * (a * U**2 + b * U * V + h * V**2),
        group,
        "homogeneous discriminant identity",
    )
    P4 = (R**2 + S**2) ** 2
    xp = R * (R**2 - 3 * S**2)
    yp = S * (3 * R**2 - S**2)
    tp = R**2 - S**2
    wp = 2 * R * S
    K = 3 * tp**2 - wp**2
    equal(xp * yp, R * S * K, group, "XY=RSK")
    equal(K - P4, 2 * (tp**2 - wp**2), group, "K-p^4")
    equal(K + P4, 4 * tp**2, group, "K+p^4")

    for side_sign, difference_sign in product((-1, 1), repeat=2):
        A = P4 * R**2
        B = 2 * side_sign * P4 * R * S - 4 * difference_sign * xp * yp
        C = P4 * S**2
        equal(
            B**2 - 4 * A * C,
            (4 * R * S) ** 2 * K * (K - side_sign * difference_sign * P4),
            group,
            f"B1 leg, signs {(side_sign, difference_sign)}",
        )
    for side_sign in (-1, 1):
        A = P4 * R**2 - 2 * xp**2
        B = 2 * side_sign * P4 * R * S
        C = P4 * S**2 - 2 * yp**2
        equal(
            B**2 - 4 * A * C,
            (8 * R * S * tp) ** 2 * (14 * R**2 * S**2 - R**4 - S**4),
            group,
            f"B1 hypotenuse, sign {side_sign}",
        )

    E = R**4 - 10 * R**2 * S**2 + 5 * S**4
    equal(5 * P4 - E, 4 * R**4 + 20 * R**2 * S**2, group, "upper bound for E")
    equal(5 * P4 + E, 6 * R**4 + 10 * S**4, group, "lower bound for E")


def check_residues():
    group = "Exhaustive finite residue conditions"
    squares_mod_3 = {r*r % 3 for r in range(3)}
    squares_mod_4 = {r*r % 4 for r in range(4)}
    squares_mod_8 = {r*r % 8 for r in range(8)}
    check(squares_mod_3 == {0, 1}, group, "square residues modulo 3")
    check(squares_mod_4 == {0, 1}, group, "square residues modulo 4")
    check(squares_mod_8 == {0, 1, 4}, group, "square residues modulo 8")
    for r, s in product(range(8), repeat=2):
        if r % 2 and s % 2:
            check((r*r + s*s) % 8 == 2, group, "two odd squares sum to 2 modulo 8")
        if r % 2 and s % 2 == 0:
            bracket = 14*r*r*s*s - r**4 - s**4
            check(bracket % 8 == 7, group, "B1 hypotenuse discriminant residue")
            E = r**4 - 10*r*r*s*s + 5*s**4
            check(E % 8 == 1, group, "A3 exceptional E residue")
    for s in (1, 2):
        check(5*s**4 % 3 == 2, group, "A3 exceptional E when 3 divides R")
        check((3*(s*s)-1) % 3 == 2, group, "minus-one nonsquare modulo 3")

    for r, s in product(range(9), repeat=2):
        if r % 3 and s % 3 == 0:
            check((3 * r*r - s*s) % 9 == 3, group, "A3 Y/S has exactly one factor of 3")

    # Fix a unit modulo 3 for each term whose valuation is minimal.
    # After factoring the minimal 3-power from the two legs and hypotenuse,
    # possible valuations of leading residues are fixed by the branch.
    for upper, lower, hypotenuse in product(range(3), repeat=3):
        if upper and lower and not hypotenuse:
            check((upper*upper + lower*lower - hypotenuse*hypotenuse) % 3 != 0,
                  group, "A3 v3(V)<v3(S)")
        if not upper and lower and not hypotenuse:
            check((upper*upper + lower*lower - hypotenuse*hypotenuse) % 3 != 0,
                  group, "A3 v3(V)>v3(S)")
        if upper and not hypotenuse:
            check((upper*upper + lower*lower - hypotenuse*hypotenuse) % 3 != 0,
                  group, "A3 v3(V)=v3(S)")

    for t, w in product(range(3), repeat=2):
        if (3*t*t - w*w) % 3 in squares_mod_3:
            check(w == 0, group, "K=3T^2-W^2 square forces 3 | W")
    # If |E/q^2|<5 and E/q^2 is 1 mod 8, the only possible integer is 1.
    check([i for i in range(-4, 5) if i % 8 == 1] == [1],
          group, "A3 exceptional quotient interval and congruence")


def check_valuation_arithmetic():
    group = "Affine valuation comparisons"
    # d is the positive gap between two distinct valuations.
    # Each identity below holds with arbitrary a,b,d, not just a sample.
    for alpha, beta, small in ((a, a + d, a), (a + d, a, a)):
        equal(3 + alpha + beta - 2 * small, 3 + d, group, "p^2*q unequal leg valuations")
    equal(3 + 2 * a, 2 * (a + 1) + 1, group, "p^2*q tied leg valuations give odd exponent")
    equal((2 * (a + 1) + 2) - 2 * a, 4, group, "p^2*q tied hypotenuse valuation")
    # b=a+1+d or a+1=b+d are the two strict orderings.
    equal(2 + a + (a + 1 + d) - 2 * (a + 1), 1 + d, group, "p^3*q B2 right larger")
    equal(2 + (b + d - 1) + b - 2 * b, 1 + d, group, "p^3*q B2 left larger")
    equal(2 + a + (a + 1), 2 * (a + 1) + 1, group, "p^3*q B2 tied leg valuations are odd")
    equal((2 * a + 2) - 2 * a, 2, group, "p^3*q B2 tied hypotenuse valuation")


def classify(k, triple, hypotenuse):
    top = set(i for i in triple if i[0] == k)
    if len(top) == 0:
        return "primitive p-divisibility"
    if len(top) == 1:
        return "unique p-unit"
    high_a = (k, 0)
    high_pair = {(k, -1), (k, 1)}
    if high_pair.issubset(top):
        other, = set(triple) - high_pair
        j, orientation = other
        if other == hypotenuse:
            return "paired top sum: " + (f"A{j}" if orientation == 0 else (f"B{j}" if j else "C"))
        return "paired top difference: " + (f"A{j}" if orientation == 0 else (f"B{j}" if j else "C"))

    if high_a not in top or len(top) != 2:
        raise AssertionError(f"Uncovered state {k=}, {triple=}, {hypotenuse=}")
    lower, = set(triple) - top
    j, orientation = lower
    if not orientation:
        return "unique q-unit"
    if k == 3 and j == 2:
        if high_a == hypotenuse:
            return "top A plus mixed state: exceptional 3-adic branch"
        return "top A plus mixed state: halving exponent"
    return "top A plus mixed state: incompatible prime bounds"


EXPECTED_CASE_COUNTS = {
    2: {
        "primitive p-divisibility": 12,
        "unique p-unit": 54,
        "unique q-unit": 6,
        "top A plus mixed state: incompatible prime bounds": 18,
        "paired top sum: A1": 1, "paired top difference: A1": 2,
        "paired top sum: A2": 1, "paired top difference: A2": 2,
        "paired top sum: B1": 2, "paired top difference: B1": 4,
        "paired top sum: C": 1, "paired top difference: C": 2,
    },
    3: {
        "primitive p-divisibility": 105,
        "unique p-unit": 189,
        "unique q-unit": 12,
        "top A plus mixed state: incompatible prime bounds": 18,
        "top A plus mixed state: exceptional 3-adic branch": 4,
        "top A plus mixed state: halving exponent": 8,
        "paired top sum: A1": 1, "paired top difference: A1": 2,
        "paired top sum: A2": 1, "paired top difference: A2": 2,
        "paired top sum: A3": 1, "paired top difference: A3": 2,
        "paired top sum: B1": 2, "paired top difference: B1": 4,
        "paired top sum: B2": 2, "paired top difference: B2": 4,
        "paired top sum: C": 1, "paired top difference: C": 2,
    },
}


def check_prime_size_arithmetic():
    group = "Prime-size contradictions and phase gaps"
    for j in (0, 1):
        minimum_square_exponent = 4 * (3 - j)
        phase_gaps = {abs(top - lower) for top, lower in product((-3, 3), (-j, j))}
        check(all(d <= minimum_square_exponent for d in phase_gaps),
              group, f"p^3*q mixed cases ruled out by sizes when j={j}")
    phase_gaps = {abs(top - lower) for top, lower in product((-3, 3), (-2, 2))}
    check({d for d in phase_gaps if d > 4} == {5},
          group, "p^3*q exceptional gap is exactly 5")
    check(5 < 8, group, "p^3*q gap-five halving contradicts q>p^2 after raising fourth powers")
    check(5**2 > 8, group, "p^3*q norm bounds contradict p>=5")
    for exponent in (2, 4, 6):
        # The proof needs (P^(2*exponent)-1)/2 > 2*P^exponent,
        # here only represented for P >= 5. Positivity follows from each
        # coefficient in the new nonnegative variable p, not tested points.
        shifted = p + 5
        coefficients = (shifted ** (2*exponent) - 1 - 4 * shifted**exponent).coefficients
        check(coefficients[ZERO_POWERS] > 0 and all(v > 0 for v in coefficients.values()),
              group, f"factor-split norm contradiction, exponent={exponent}")


def check_case_coverage():
    group = "Exhaustive Gaussian index and proof-route census"
    for k in (2, 3):
        chosen = representative_indices(k)
        oriented = set(product(range(-k, k + 1), (-1, 0, 1))) - {(0, 0)}
        with_conjugates = set(chosen) | {(-j, -l) for j, l in chosen}
        check(oriented == with_conjugates, group, f"k={k}, conjugation-orbit coverage")
        check(len(oriented) == 2 * len(chosen), group, f"k={k}, unique representatives")
        case_counts = Counter(classify(k, triple, hyp)
                              for triple in combinations(chosen, 3) for hyp in triple)
        check(sum(case_counts.values()) == 3 * comb(len(chosen), 3), group, f"k={k}, role count")
        check(case_counts == EXPECTED_CASE_COUNTS[k], group, f"k={k}, route census {case_counts}")
        remaining = sum(case_counts.values()) - case_counts["primitive p-divisibility"] - case_counts["unique p-unit"]
        print(f"k={k}: {len(chosen)} index states, {sum(case_counts.values())} "
              f"state/role cases, {remaining} after the minimal-p-valuation reduction")


def main():
    check_gaussian_formulas()
    check_cancellation_identities()
    check_discriminants()
    check_residues()
    check_valuation_arithmetic()
    check_prime_size_arithmetic()
    check_case_coverage()
    for group, count in CHECKS.items():
        print(f"PASS {group}: {count}")
    print(f"PASS {sum(CHECKS.values())} checks. Scope: identities, residues, route coverage.")
    print("The complete cuboid theorems are not kernel-checked by this program.")


if __name__ == "__main__":
    main()

