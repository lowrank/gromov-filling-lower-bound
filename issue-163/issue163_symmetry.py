"""One-dimensional symmetry and collar tests. Run with Python 3.8 or later."""
from fractions import Fraction as Q
from math import cos, exp, isqrt, log, pi, sqrt

UNIT = 10**30


def root_bounds(x):
    n = isqrt(x.numerator * UNIT**2 // x.denominator)
    return Q(n, UNIT), Q(n + 1, UNIT)


def atan_bounds(q):
    # Alternating series, with an even number of terms.
    n = 60
    partial = sum(Q((-1)**j, (2*j + 1)*q**(2*j + 1)) for j in range(n))
    return partial, partial + Q(1, (2*n + 1)*q**(2*n + 1))


a, b = atan_bounds(5), atan_bounds(239)
PI_LO, PI_HI = 16*a[0] - 4*b[1], 16*a[1] - 4*b[0]


def mean_series(x):
    """Enclose the angular mean of sqrt(1 + sqrt(x) cos(theta))."""
    assert 0 <= x < 1
    total, term = Q(1), x/16
    for m in range(1, 129):
        total -= term
        term *= x * Q(16*m*m - 1, 16*(m+1)**2)
    return total - term/(1-x), total


def angular_cost(x, cosh_bounds):
    low, high = mean_series(x)
    assert low > 0
    return cosh_bounds[0]*low**2, cosh_bounds[1]*high**2


def balanced(k):
    low, high = root_bounds(k)
    return angular_cost(((k-1)/(k+1))**2, ((k+1)/(2*high), (k+1)/(2*low)))


def collar(shear):
    x = shear**2
    return angular_cost(x/(4+x), root_bounds(1+x/4))


def lower_area(cost, fraction=Q(1)):
    return 2*PI_LO / (1+fraction*(cost[1]-1))


def upper_area(cost):
    return 2*PI_HI/cost[0]


def p_bounds(z):
    # p(log z), including z < 1 by symmetry.
    c = (z+1/z)/2
    low, high = mean_series(((z-1/z)/(2*c))**2)
    a, b = root_bounds(c)
    return low*a, high*b


def paired_cost(k, q, z):
    lo, hi = p_bounds(z)
    a, b = p_bounds(k/z)
    u, v = root_bounds(q)
    return (lo + u*a)**2/(2*(1+q)), (hi + v*b)**2/(2*(1+q))


def fit(k, q):
    # Only this exploratory minimizer uses floats. Re-evaluate its rounded proposal below.
    cos2 = [cos((i+.5)*pi/96)**2 for i in range(96)]
    def mean(z):
        return sum(sqrt(z*a+(1-a)/z) for a in cos2)/len(cos2)
    def score(s):
        return mean(exp(s)) + sqrt(q)*mean(k/exp(s))
    lo, hi = 0., log(k)
    for _ in range(70):
        a, b = (2*lo+hi)/3, (lo+2*hi)/3
        if score(a) < score(b):
            hi = b
        else:
            lo = a
    return Q(round(10000*exp((lo+hi)/2)), 10000)


def floor_decimal(x, places=9):
    n = x.numerator * 10**places // x.denominator
    return f"{n // 10**places}.{n % 10**places:0{places}d}"


def main():
    for k in (Q(3,2), Q(8,5), Q(81,50), Q(2)):
        c = balanced(k)
        print("equal areas, K =", str(k), "conditional lower bound", floor_decimal(lower_area(c)))
    assert lower_area(balanced(Q(8,5))) > Q(6155,1000)
    assert upper_area(balanced(Q(81,50))) < Q(615,100)
    # Strict brackets for the largest balanced distortion meeting 6.15.
    assert lower_area(balanced(Q(161488,100000))) > Q(615,100)
    assert upper_area(balanced(Q(161489,100000))) < Q(615,100)
    print("balanced threshold between 1.61488 and 1.61489")
    for k, q in ((Q(2),Q(2)), (Q(3),Q(4))):
        z = fit(float(k),float(q))
        c = paired_cost(k,q,z)
        print("paired K, q =", str(k), str(q), "trial exp(s) =", str(z),
              "conditional lower bound", floor_decimal(lower_area(c)))
        if k == 3:
            assert c[1] < 1
    assert paired_cost(Q(3), Q(4), Q(2))[1] < Q(994, 1000)
    uniform = collar(Q(2,5))
    concentrated = collar(Q(4))
    print("shear 0.4 throughout", floor_decimal(lower_area(uniform)))
    print("same twist in one tenth", floor_decimal(lower_area(concentrated,Q(1,10))))
    assert lower_area(uniform) > Q(6191,1000)
    assert 2*PI_HI / (1+(concentrated[0]-1)/10) < Q(5738,1000)


if __name__ == "__main__":
    main()
