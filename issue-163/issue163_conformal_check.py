"""Rational checks for the conformal path and projective-line estimates."""

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


def check_projective_lines(pi_lo, pi_hi):
    # Successive differences of 1/(2*(k-1/2)^2) equal
    # k^(-3) * (1-1/(4*k^2))^(-2), so the tail bounds telescope.
    m = 64
    partial = sum(F(1, k**3) for k in range(1, m+1))
    tail_upper = F(2, (2*m+1)**2)
    tail_lower = tail_upper * (1-F(1, 4*(m+1)**2))**2
    d_lo = F(1, 3) + 13*(partial+tail_lower)/(12*pi_hi**2)
    d_hi = F(1, 3) + 13*(partial+tail_upper)/(12*pi_lo**2)
    assert F(13504192, 10**6) < 2*pi_lo/d_hi <= 2*pi_hi/d_lo < F(13504193, 10**6)
    assert F(2149258, 10**6) < 1/d_hi <= 1/d_lo < F(2149259, 10**6)
    assert 2*pi_lo*(1-F(2, 3)*F(317, 10000)) > F(123, 20)
    assert F(1, 3) + F(8, 3)*F(1, 20) == F(7, 15)
    r, delta = F(1, 16), F(1, 10**6)
    assert delta <= r**3/40 and 2*delta/(1+delta**2) < F(1, 20)
    assert F(11, 10)**2 * F(101, 100) < 2*F(9, 10)*F(99, 100)**2
    assert 2*pi_lo*(1-r**2)/(1+r**2) > F(623428, 10**5)
    for shift in range(3):
        assert sum((shift-j) % 3 == j for j in range(3)) == 1
    print('Cyclic genus-two example gives area > 13.504192 and distortion threshold > 2.149258.')
    print('Clustered branch points: the second projection gives area > 6.23428.')


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
    check_projective_lines(p_lo, p_hi)

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
