"""Exact scalar, polynomial, and monodromy checks for the genus-two comparisons."""

from fractions import Fraction as F
from math import comb

import sympy as sp

from issue163_fiber_check import atan_bounds


def check_football_bounds():
    radius_lower = F(83, 200)
    separation_lower = F(131, 200)
    assert (7 - radius_lower**3)**2 > 48
    assert 3 * radius_lower**2 > separation_lower**2 * (
        1 + radius_lower**2 + radius_lower**4
    )
    s = F(2, 7)
    d = separation_lower
    assert d > 2 * s / (1 + s**2)
    radius = s * (1 - d**2) / (1 - d**2 * s**2)
    closest = (d - s) / (1 - d * s)
    assert 2 * s / (1 + s) == F(4, 9)
    assert radius**2 / (closest * (1 + closest)**2) < F(69, 400)**2
    denominator = 1 - F(2, 3) * (F(2, 3) - F(69, 400))**2
    assert denominator == F(1808351, 2160000)
    assert 1 / denominator > F(11944, 10000)
    low5, _ = atan_bounds(5)
    _, high239 = atan_bounds(239)
    pi_lower = 16 * low5 - 4 * high239
    assert 2 * pi_lower / denominator > F(75050, 10000)

    parameter = F(1, 1 + 1000 * 41 * 97 * 101)
    assert parameter.denominator == 401677001
    assert 3 * F(1, 2)**2 * F(65, 200) - F(345, 10000) > F(1, 5)
    assert 500 * 10 + 115 * (10 + 70 * 100) < 10**6
    exponent = 4200000 * parameter
    # The geometric series bounds exp(x) for 0 <= x < 1.
    assert 1 / (1 - exponent) < F(1011, 1000)
    assert (2 * pi_lower / denominator) / F(1011, 1000) > F(742, 100)
    print("Reference area > 7.5050; explicit marked deformation area > 7.42.")


def check_discriminants():
    u, v = sp.symbols("u v")
    expected = {
        (17, 4): None,
        (41, 32): [1, 11],
        (41, 9): [5, 7],
        (97, 22): [1, 1, 1, 2, 7],
        (101, 91): [12],
    }
    for (prime, root), degrees in expected.items():
        assert (root * root + 1) % prime == 0
        cubic = (8 * (1 + u*v)**3 + (u + v)**3
                 + 2 * (root * (u - v))**3 + 3 * (1 - u*v)**3)
        disc = sp.Poly(sp.discriminant(cubic, v), u, modulus=prime)
        assert disc.degree() == 12 and disc.gcd(disc.diff()).is_one
        if degrees is None:
            claimed = (7*u**12 - 7*u**10 - 5*u**9 - 8*u**8 + 3*u**7
                       + 3*u**6 + 2*u**5 - 6*u**4 + u**3 - 7*u**2 - 5)
            assert disc == sp.Poly(claimed, u, modulus=prime)
        else:
            assert 401677001 % prime == 1
            factors = disc.factor_list()[1]
            assert sorted(factor.degree() for factor, _ in factors) == degrees
            print(f"p={prime}, i={root}: squarefree factor degrees {degrees}")


def compose_cycles(degree, *cycles):
    """Return images of 1 through degree, applying the rightmost cycle first."""
    images = list(range(1, degree + 1))
    for cycle in reversed(cycles):
        action = dict(zip(cycle, cycle[1:] + cycle[:1]))
        images = [action.get(i, i) for i in images]
    return images


def check_projective_monodromy():
    c = (1, 2, 3)
    t, s = (1, 2), (2, 3)
    assert compose_cycles(3, c, c, t, s, t, t, s, s) == [1, 2, 3]

    c = (1, 2, 3, 4, 5)
    bad = [(1, 3), (1, 5), (1, 2), (1, 4), (1, 2), (1, 2), (3, 4), (3, 4)]
    good = [pair for i in range(1, 5) for pair in [(i, i + 1)] * 2]
    identity = list(range(1, 6))
    assert compose_cycles(5, c, c, *bad) == identity
    assert compose_cycles(5, *good) == identity
    assert F(19, 20) * 5 + F(1, 20) / 5 == F(119, 25)
    assert F(19, 20) / 5 + F(1, 20) * 5 == F(11, 25)

    quintic_coefficients = {
        (1, 1, 1, 1, 1): 4, (2, 1, 1, 1): 2, (2, 2, 1): 0,
        (3, 1, 1): F(4, 3), (3, 2): F(-2, 3), (4, 1): 0, (5,): F(-4, 5),
    }
    for parts, coefficient in quintic_coefficients.items():
        assert sum(parts) == 5
        assert sum(F(1, k) for k in parts if k % 2) - 1 == coefficient
    assert 1 + comb(8, 2) == 29
    print("Cubic and quintic puncture relations and all seven quintic coefficients verified.")


if __name__ == "__main__":
    check_football_bounds()
    check_discriminants()
    check_projective_monodromy()
