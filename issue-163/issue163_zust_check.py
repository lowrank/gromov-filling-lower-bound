"""Rational checks for the angular Fourier deficit and the two-angle comass tests."""
from fractions import Fraction as F
import json


def atan_reciprocal(q, terms=36):
    terms_sum = sum(F((-1)**i, (2*i+1)*q**(2*i+1)) for i in range(terms))
    next_sum = terms_sum + F((-1)**terms, (2*terms+1)*q**(2*terms+1))
    return min(terms_sum, next_sum), max(terms_sum, next_sum)


def floor_at(x, places):
    return (x.numerator * 10**places) // x.denominator


def decimal(x, places=12, upper=False):
    value = -floor_at(-x, places) if upper else floor_at(x, places)
    return f"{value // 10**places}.{value % 10**places:0{places}d}"


a5, b5 = atan_reciprocal(5)
a239, b239 = atan_reciprocal(239)
pi_lo, pi_hi = 16*a5-4*b239, 16*b5-4*a239
# log(2) = 2 atanh(1/3). Bound the tail by a geometric series.
terms = 40
log_lo = sum(F(2, (2*i+1)*3**(2*i+1)) for i in range(terms))
log_hi = log_lo + F(2, (2*terms+1)*3**(2*terms+1))*F(9, 8)
angle_ceiling_lo = 4*pi_lo*(pi_lo+F(3, 2)-2*log_hi)/7
angle_ceiling = 4*pi_hi*(pi_hi+F(3, 2)-2*log_lo)/7
raw_ceiling = 2*pi_hi**2/(1+pi_lo**2/4)
assert decimal(angle_ceiling, upper=True) == decimal(angle_ceiling_lo, upper=True) == "5.843897829067"
assert raw_ceiling < F(5692796486865, 10**12)

# x(a) = sin(arcsin(cos(3a))/3). At index 3k, k positive odd,
# the complex cosine coefficient is 3 sqrt(3)/(pi*(9k^2-1)).
def triple_deficit(k_max):
    return 108*sum(F(3*k-1, (9*k*k-1)**2) for k in range(1, k_max+1, 2))/pi_hi**2


triple_cap = pi_hi*(1-triple_deficit(3))/2
assert triple_cap < 2*pi_lo/F(615, 100)
triple_cap_refined = pi_hi*(1-triple_deficit(49))/2
action_lower = 2*pi_lo-4*b5/7
limit_upper = (1+pi_hi**2/4)/pi_lo - (F(20, 9)+pi_lo**2/4)/(14*pi_hi)
assert action_lower > F(61703, 10000) and limit_upper < F(998, 1000)


def finite_width_lower():
    # k = tan(epsilon) = 1/25, tan(eta) = 1/5. The normalized angles
    # change variables to a square with rational endpoints and integrand.
    B = F(626, 625)
    count = 32
    grid = [F(j*j, j*j+(count-j)**2)/B for j in range(count+1)]
    cells = list(zip(grid, grid[1:]))
    moments = [[(hi**(p+1)-lo**(p+1))/(p+1) for p in range(6)] for lo, hi in cells]
    # The powers are those of U*V, with the factor B included in each coefficient.
    base = (4*B, -4*B**2, 0, 0)
    penalty = (0, 16*B**2/7, -32*B**3/7, 16*B**4/7)
    total = 0
    precision = 10**15
    for i, first in enumerate(cells):
        for j in range(i+1):
            corners = [(u+v-2*u*v, 1-B*u*v-(u+v-2*u*v)) for u in first for v in cells[j]]
            can_cut = min(d for d, _ in corners) < 5*max(abs(h) for _, h in corners)
            m, n = moments[i], moments[j]
            mass, first_moment = F(), F()
            for p, (coef, loss) in enumerate(zip(base, penalty), start=1):
                c = coef-loss if can_cut else coef
                mass += c*m[p]*n[p]
                first_moment += c*(m[p+1]*n[p]+m[p]*n[p+1]-2*m[p+1]*n[p+1])
            assert mass > 0 and first_moment > 0
            lower = mass**3/first_moment**2
            total += (1 if i == j else 2) * (lower.numerator*precision//lower.denominator)
    return F(total, precision)/pi_hi


finite = finite_width_lower()
assert finite > F(102531, 100000) and 2*pi_hi/finite < F(6129, 1000)
print(json.dumps({
    "raw_limit_norm_lower": decimal((1+pi_lo**2/4)/pi_hi),
    "raw_area_ceiling": decimal(raw_ceiling, upper=True),
    "visual_angle_ceiling": decimal(angle_ceiling, upper=True),
    "triple_wave_two_mode_comass_upper": decimal(triple_cap, upper=True),
    "triple_wave_25_mode_comass_upper": decimal(triple_cap_refined, upper=True),
    "two_angle_action_lower": decimal(action_lower),
    "two_angle_limiting_comass_upper": decimal(limit_upper, upper=True),
    "two_angle_finite_comass_lower": decimal(finite),
    "two_angle_area_ceiling": decimal(2*pi_hi/finite, upper=True),
    "distinct_rational_rectangles": 32*33//2,
}, indent=2))
