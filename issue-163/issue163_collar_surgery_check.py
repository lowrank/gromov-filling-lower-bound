"""Rational checks for the hyperbolic thresholds and the simply branched example."""

from fractions import Fraction as F
from math import factorial

from issue163_fiber_check import atan_bounds


def exp_bounds(x):
    assert 0 <= x <= 8
    terms = [x**j / factorial(j) for j in range(33)]
    lower = sum(terms)
    tail = terms[-1] * x / 33 / (1 - x / 34)
    return lower, lower + tail


def round_down(x):
    return F(int(x * 10**8), 10**8)


def atan_exp_negative_lower(x):
    _, exp_upper = exp_bounds(x)
    y = round_down(1 / exp_upper)
    assert 0 < y < 1
    return round_down(sum((-1)**k * y**(2*k + 1) / (2*k + 1) for k in range(14)))


def check_collars(pi_lower):
    for length, multiplier in [(F(1462, 1000), 1), (F(2147, 1000), 2)]:
        modulus = 4 * atan_exp_negative_lower(length / 2) / length
        exponential, _ = exp_bounds(round_down(multiplier * pi_lower * modulus))
        assert 2 * pi_lower * (1 - 1 / exponential) > F(615, 100)
    exponential, _ = exp_bounds(round_down(pi_lower * F(1227, 1000)))
    assert 2 * pi_lower * (1 - 1 / exponential) > F(615, 100)
    length = F(987, 1000)
    width = 2 * pi_lower * atan_exp_negative_lower(length) / length
    exponential, _ = exp_bounds(round_down(2 * width))
    assert 2 * pi_lower * (exponential - 1) / (exponential + 1) > F(615, 100)
    print("Area > 6.15 at one-sided length 0.987 and two-sided lengths 1.462, 2.147.")


def check_ordinary_cover(pi_lower, pi_upper):
    s, d = F(1, 8), F(5, 12)
    assert F(16, 91) > d**2 and d > 2*s / (1 + s**2)
    radius = s * (1 - d**2) / (1 - d**2 * s**2)
    closest = (d - s) / (1 - d*s)
    assert 2*s / (1 + s) == F(2, 9) > F(47, 100)**2
    foreign_mass = radius**2 / (closest * (1 + closest)**2)
    assert foreign_mass == F(208, 10201) < F(29, 200)**2
    denominator = 1 - F(2, 3) * (F(47, 100) - F(29, 200))**2
    assert denominator == F(2231, 2400)
    assert F(63, 64) * 2 * pi_lower / denominator > F(665, 100)
    _, atan_upper = atan_bounds(8)
    line_bound = 2*pi_upper/3 + F(64, 3)*atan_upper + F(16, 3)*pi_upper*F(3, 2048)
    assert line_bound < F(48, 10)
    print("Simple S3 cover: conformal area bound > 6.65, cubic line certificate < 4.8.")


if __name__ == "__main__":
    low5, high5 = atan_bounds(5)
    low239, high239 = atan_bounds(239)
    pi_lower, pi_upper = 16*low5 - 4*high239, 16*high5 - 4*low239
    check_collars(pi_lower)
    check_ordinary_cover(pi_lower, pi_upper)
