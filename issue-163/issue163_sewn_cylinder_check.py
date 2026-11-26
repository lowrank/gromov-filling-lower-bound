"""Rational checks for the sewn-cylinder area estimates. Run with python3 -B."""

from fractions import Fraction as F
from functools import cache
from itertools import accumulate

from issue163_collar_surgery_check import exp_bounds
from issue163_fiber_check import atan_bounds


def grid(value, upper=False):
    scale = 10**12
    numerator = value.numerator * scale
    if upper:
        numerator += value.denominator - 1
    return F(numerator // value.denominator, scale)


low5, high5 = atan_bounds(5)
low239, high239 = atan_bounds(239)
PI_LO = grid(16*low5 - 4*high239)
PI_HI = grid(16*high5 - 4*low239, upper=True)


@cache
def tanh_bounds(x):
    low, high = exp_bounds(2*x)
    return grid((low-1)/(low+1)), grid((high-1)/(high+1), upper=True)


def small_atan(x):
    assert 0 <= x <= F(1, 3)
    low = sum((-1)**k * x**(2*k+1) / (2*k+1) for k in range(12))
    return grid(low), grid(low + x**25/25, upper=True)


@cache
def band_data(t):
    # Lower and upper squared norms of the horizontal and four vertical tests.
    xlo = grid(3*PI_LO**2/(100*t))
    xhi = grid(3*PI_HI**2/(100*t), upper=True)
    hlo, hhi = tanh_bounds(t)
    vlo, vhi = tanh_bounds(xlo)[0], tanh_bounds(xhi)[1]

    # Upper bound on their inner product using two half-angle identities.
    exp_hi = exp_bounds(t)[1]
    f_t = PI_HI/2 - 2*small_atan(grid(1/exp_hi))[0]
    f_x = 2*small_atan(tanh_bounds(xhi/2)[1])[1]
    return (2*PI_LO*hlo, 2*PI_HI*hhi, 8*PI_LO*vlo, 8*PI_HI*vhi,
            grid(16*f_t*f_x, upper=True))


def weights(t):
    h, _, v, _, cross = band_data(t)
    det = h*v - cross**2
    assert det > 0
    a = F(round(100*v*(h-cross)/det), 100)
    b = F(round(100*h*(v-cross)/det), 100)
    assert 0 <= a <= 1 and 0 <= b <= 1 and 2*a*b <= 1
    return a, b


def lower(t, a, b):
    h, _, v, _, cross = band_data(t)
    return (2*a-a*a)*h + (2*b-b*b)*v - 2*a*b*cross


def check_area():
    left, step = F(11, 10), F(1, 25)
    right = left + 42*step
    c = 3*PI_HI**2/100
    curvature = (16*PI_HI*c/left**3
                 + 16*(c/(2*left) + 2*c/left**2 + PI_HI*c**2/(4*left**4)))
    assert curvature < 24
    assert band_data(left)[2] > 2*PI_HI
    assert band_data(right)[0] > F(623, 100)
    for j in range(42):
        lo, hi = left + j*step, left + (j+1)*step
        a, b = weights((lo+hi)/2)
        bound = min(lower(lo, a, b), lower(hi, a, b)) - 24*step**2/8
        assert bound > F(623, 100)
        if lo <= F(8, 5):
            assert bound > 2*PI_HI
    t = F(13, 10)
    _, h_upper, _, v_upper, _ = band_data(t)
    assert max(h_upper, v_upper) < F(563, 100)
    assert lower(t, *weights(t)) > F(657, 100)
    assert F(657, 100) / F(1045, 1000) > 2*PI_HI
    assert F(623, 100) / F(1012, 1000) > F(615, 100)
    print("Four transverse strips: area > 6.23 at every height, > 2 pi through 1.6.")
    print("At height 1.3 both separate bounds are < 5.63, together they give > 6.57.")


PAIRS = [(0, 8), (1, 9), (2, 15), (3, 6), (4, 12), (5, 13), (7, 10), (11, 14)]


def cycles(permutation):
    assert sorted(permutation) == list(range(len(permutation)))
    seen = set()
    sizes = []
    for i in range(len(permutation)):
        if i in seen:
            continue
        size = 0
        while i not in seen:
            seen.add(i)
            size += 1
            i = permutation[i]
        sizes.append(size)
    return sorted(sizes)


def pairing(pairs):
    partner = [None] * (2*len(pairs))
    for a, b in pairs:
        partner[a], partner[b] = b, a
    assert sorted(partner) == list(range(len(partner)))
    return partner


def check_diagrams():
    partner = pairing(PAIRS)
    assert cycles([(p+1) % 16 for p in partner]) == [3, 3, 3, 3, 4]
    lengths = [100]*16
    lengths[2] = lengths[15] = 101
    lengths[7] = lengths[10] = 99
    ends = [0, *accumulate(lengths)]
    assert ends[-1] == 1600
    centers = [F(a+b, 2) for a, b in zip(ends, ends[1:])]
    widths = []
    for a, b in PAIRS:
        assert lengths[a] == lengths[b]
        overlap = lengths[a] - abs(centers[b]-centers[a]-800)
        if overlap > 0:
            widths.append(overlap/2)
    assert sorted(widths) == [49, 49, 50, 50] and F(49, 800) > F(3, 50)

    blocks = pairing([(0, 2), (1, 3), (4, 6), (5, 7)])
    assert cycles([(p+1) % 8 for p in blocks]) == [8]
    assert cycles([(p+4) % 8 for p in blocks]) == [2, 2, 2, 2]

    # arcsin(y) >= y, sin(x) >= x - x^3/6.
    t = F(13, 10)
    exp_lo, exp_hi = exp_bounds(t)
    sech_lo = 2/(exp_hi + 1/exp_lo)
    assert 2*sech_lo*(PI_LO/9-(PI_HI/9)**3/6) > F(34, 100)
    print("Genus-two diagrams, four strip widths, even-return obstruction and shortcut checked.")


def check_caps():
    assert PI_LO*(2-F(1, 25)) > F(61575, 10000)
    # At H=0.9 use rational lower bounds for sqrt(0.19) and sqrt(2).
    r, sqrt_two = F(435889, 10**6), F(141421, 10**5)
    assert r**2 < F(19, 100) and sqrt_two**2 < 2
    chord_radius = r - F(55, 1000)/sqrt_two
    assert chord_radius > 0 and PI_LO*(F(9, 5) + chord_radius**2) > F(615, 100)
    effective = F(51, 50)*r - PI_HI/(50*sqrt_two)
    assert effective > 0 and PI_LO*(F(9, 5) + effective**2) > F(61579, 10000)
    print("Round and two-percent belt comparisons give > 6.1575 and > 6.1579.")


if __name__ == "__main__":
    check_diagrams()
    check_area()
    check_caps()
