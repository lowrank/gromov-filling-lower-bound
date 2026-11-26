"""Rational checks for the area thresholds and the path law on a spherical belt."""

from fractions import Fraction as F

from issue163_fiber_check import atan_bounds


def tanh_bounds(t):
    """Bound tanh(t) with the positive Taylor series for exp(2t)."""
    x = 2*t
    term = total = F(1)
    for k in range(1, 41):
        term *= x/k
        total += term
    ratio = x/41
    assert 0 < ratio < 1
    upper = total + term*ratio/(1-ratio)
    return (total-1)/(total+1), (upper-1)/(upper+1)


def main():
    a5, b5 = atan_bounds(5)
    a239, b239 = atan_bounds(239)
    p_lo, p_hi = 16*a5-4*b239, 16*b5-4*a239
    target = F(123, 20)

    def sampled_bound(n, pi_bound):
        return 2*pi_bound*(1-F(1, 2*n))**2

    assert sampled_bound(46, p_hi) < target
    assert sampled_bound(47, p_lo) > F(61502116, 10**7)
    assert 2*p_lo*F(47, 48) > F(615228, 10**5)
    assert F(16048137, 10**7) < p_lo**2/target <= p_hi**2/target < F(16048138, 10**7)

    for width, count, lower in [(F(227, 100), 1, F(615047, 10**5)),
                                (F(34, 100), 3, F(617280, 10**5))]:
        height_lo, _ = tanh_bounds(width)
        assert 2*p_lo*count*height_lo > lower > target
    assert 4*p_lo*F(3, 5)/(1+F(22, 100)) > F(618018, 10**5)

    # Independent height check. After dividing height by the belt height,
    # z = sqrt(1-u^2) sin(t), with u uniform on [0,1], t uniform on [0,pi].
    # The even moments of a uniform height are 1/(2k+1).
    factor_u = factor_t = F(1)
    for k in range(1, 13):
        factor_u *= F(2*k, 2*k+1)
        factor_t *= F(2*k-1, 2*k)
        assert factor_u*factor_t == F(1, 2*k+1)
    print('47 sampled pairs in the marked round class: lower bound > 6.1502116')
    print('One band of half-width 2.27: > 6.15047; three of half-width 0.34: > 6.17280')
    print('Two overlapping bands with H=0.6 and normalized overlap at most 0.22: > 6.18018')
    print('The first twelve even height moments agree exactly with uniform belt area.')


if __name__ == '__main__':
    main()
