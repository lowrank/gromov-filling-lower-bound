"""Exact scalar replay for the occupation estimates on eroded and folded profiles."""

from fractions import Fraction as F
import json
from math import cos, expm1, log1p, pi, sin, sqrt


# These rational endpoints enclose pi, e.g. by Machin's identity below.
def atan_bounds(q):
    n = 25
    partial = sum(F((-1)**i, (2*i + 1)*q**(2*i + 1)) for i in range(n))
    other = partial + F((-1)**n, (2*n + 1)*q**(2*n + 1))
    return min(partial, other), max(partial, other)


a5, b5 = atan_bounds(5)
a239, b239 = atan_bounds(239)
p0, p1 = F(3141592653589793238, 10**18), F(3141592653589793239, 10**18)
assert p0 < 16*a5 - 4*b239 <= 16*b5 - 4*a239 < p1
B = F(6096286, 10**6)
exact_factor = F(2213775623134282058736195815563, 3583999641600000000000000000000)
assert B < exact_factor*p0*p0
D = F(615, 100)
scale = 10**18


def up(x):
    return F(-((-x.numerator*scale)//x.denominator), scale)


def down(x):
    return F((x.numerator*scale)//x.denominator, scale)


# For integral_0^1 v^k (A+C(1-v))/(2-v)^2 dv expand the positive factor.
def moment_upper(k, A, C):
    terms = 32
    total = sum(F(j+1, 2**(j+2))*(A/F(k+j+1) + C/F((k+j+1)*(k+j+2)))
                for j in range(terms))
    # Sum of (j+1)/2^(j+2) from j=terms to infinity.
    return total + F(terms+2, 2**(terms+1))*(A/F(k+terms+1) + C/F((k+terms+1)*(k+terms+2)))


def coefficients(folded, count):
    result = []
    for k in range(count+1):
        if folded:
            # Coefficient of cos(e)^k.
            integral = moment_upper(k+1, 2, 2*k+6)
            coef = F(k+1, (k+2)*(k+4))*integral
        elif k:
            # Coefficient of cos(e)^(2k).
            leading = F(k, k+1)
            coef = moment_upper(k, leading-F(k-1, k+2), leading)
        else:
            coef = 0
        result.append(up(4*coef/p0))
    return result


def cross_upper(e, folded, coef):
    at_zero = up(1/p0 + p1/4)
    # For t in [0,1], replace each higher power by t^(count+1) and
    # use C(1) plus positive coefficients at powers 0 through count.
    t = 1 - e*e/2 + e**4/24
    if not folded:
        t = t*t
    t = up(t)
    powers = [F(1)]
    tail_low = F(1)
    for _ in coef:
        powers.append(up(powers[-1]*t))
        tail_low = down(tail_low*t)
    return up(at_zero*powers[-1] + sum(a*(p - tail_low) for a, p in zip(coef, powers)))


def shell_budget(folded, coef):
    def excess(e):
        return max(F(0), cross_upper(e, folded, coef)-1)

    # M(e) = D - B sigma(e)^2; enclose each increment from above.
    def sigma(e, p):
        return (p-3*e)/(p+e) if folded else (p-2*e)/(p+2*e)

    total = excess(F(0))*(D-B)
    end = F(24 if folded else 20, 200)
    for j in range(int(end*200)):
        e, f = F(j, 200), F(j+1, 200)
        increment = B*(sigma(e, p1)**2 - sigma(f, p0)**2)
        total += excess(e)*increment
    assert excess(end) == 0, "positive part persists past the final shell"
    # Using B below the action is valid for cumulative M(e) at every shell.
    return up(total)


def height_filtered_cross(coef):
    height = F(1, 5)
    worst = F(0)
    for j in range(120):
        lo, hi = F(j, 1000), F(j+1, 1000)
        cosine_up = 1-lo**2/2+lo**4/24
        # Lower endpoint of the necessary interval for sqrt(S) when z >= height.
        root_low = (height**2*(1-hi**2/2)-hi**2*F(49, 50))/(height**2+(1-height**2)*hi**2)
        assert 0 < root_low < 1 and F(49, 50)**2 > 1-height**2
        first = down(root_low**2)
        width = (1-first)/64
        tail = F(0)
        for i in range(64):
            left = first+i*width
            right = left+width
            ratio = (1-left)/(1-left+2*(1-cosine_up)*left)
            tail += up(width*(4-F(2, 3)*(1-right))*ratio**2)
        full = cross_upper(lo, True, coef)
        worst = max(worst, (9*full+min(full, tail/p0))/10)
    assert cross_upper(F(12, 100), True, coef) < 1
    return up(worst)


def independent_gradient_quadrature(n):
    # Numerical diagnostic only. The exact conclusions below use fractions.
    e = 0.1
    length = pi/2-e
    log_scale = log1p(length/e)
    ramps = []
    flats = []
    for i in range(n):
        t = (i+0.5)/n
        a = e*expm1(log_scale*t)
        ramps.append((a, (a+e)*log_scale/n))
        flats.append((length+2*e*t, 2*e/n))

    def multiplier(z_sq):
        return 0.9+0.1*max(0, min(1, (sqrt(max(0, z_sq))-0.2)/0.01))

    cross = mixed = 0.0
    for a, aw in ramps:
        ca = sin(a+e)
        for v, vw in ramps:
            z_sq = 4*sin(a)*sin(v)*sin(e)*sin(a+v+e)/sin(a+v)**2
            cross += aw*vw*multiplier(z_sq)*z_sq/(ca*sin(v+e))**2
        for b, bw in flats:
            z_sq = 1-(cos(a+e)/sin(b-a))**2
            mixed += aw*bw*multiplier(z_sq)*z_sq/ca**2
    return (cross+sqrt(2)*mixed)/pi


eroded_coef, folded_coef = coefficients(False, 256), coefficients(True, 256)
eroded, both = shell_budget(False, eroded_coef), shell_budget(True, folded_coef)
filtered = height_filtered_cross(folded_coef)
assert filtered < F(999, 1000)
assert F(1959, 1000)*p0 > F(615438, 100000)
assert eroded < F(94717, 10**6)
assert both < F(119694, 10**6)
assert 2*p0-D-eroded > F(3846, 10**5)
assert 2*p0-D-both > F(1349, 10**5)
peak_upper = 1/p0 + p1/4
assert D+(2*p0-D-both)/peak_upper > F(616222, 10**5)
assert D+(2*p0-D-eroded)/peak_upper > F(618485, 10**5)
assert F(8, 3)/p0 < F(848827, 10**6)
assert F(1349, 10**5)/(p1/2-1) > F(236, 10**4)

# Explicit 0.001-neighborhood at eroded widths <= 0.05.
sigma = (p0-F(1, 10))/(p0+F(1, 10))
r = F(1, 1000)/sigma
d_bound = r/(1-2*r/p0)
kappa = 1-4*(r+d_bound)/p0
assert kappa > 0 and D-B*(sigma*kappa)**2 < F(812, 1000)
print(json.dumps({
    "eroded_net_excess_budget_upper": str(eroded),
    "eroded_and_folded_net_excess_budget_upper": str(both),
    "required_exterior_positive_excess_eroded": "0.03846",
    "required_exterior_positive_excess_combined": "0.01349",
    "area_plus_exterior_excess_over_peak_combined": "6.16222",
    "area_plus_exterior_excess_over_peak_eroded": "6.18485",
    "clipped_net_density_upper": "0.848827",
    "height_filtered_cross_upper_through_width_0.12": str(filtered),
    "height_filtered_action_lower": "6.15438",
    "independent_gradient_midpoint_diagnostic": {
        n: round(independent_gradient_quadrature(n), 7) for n in (64, 128)
    },
}, indent=2))
