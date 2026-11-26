"""Exact scalar checks for the signed distance transfer and its Fourier test."""

from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from math import factorial
from pathlib import Path


def atan_bounds(q):
    count = 25
    total = sum(F((-1)**k, (2*k+1)*q**(2*k+1)) for k in range(count))
    next_term = F((-1)**count, (2*count+1)*q**(2*count+1))
    return min(total, total+next_term), max(total, total+next_term)


def det(u, v):
    return u[0]*v[1] - u[1]*v[0]


def sub(u, v):
    return u[0]-v[0], u[1]-v[1]


def hull(points):
    ordered = sorted(set(points))

    def chain(points):
        result = []
        for p in points:
            while len(result) >= 2 and det(sub(result[-1], result[-2]), sub(p, result[-2])) <= 0:
                result.pop()
            result.append(p)
        return result[:-1]

    return chain(ordered) + chain(reversed(ordered))


def signed_discrepancy_test():
    # Three sheets with deliberately different arrays. Check both expressions
    # for every minor, then impose a rank-one difference with arbitrarily large rows.
    signs = (1, 1, -1)
    base = [(1, 2), (-5, 7), (3, 1), (4, -2)]
    varied = [base, [(3, 5), (4, 2), (1, -1), (-7, 1)], [(5, 2), (1, 4), (9, 6), (1, -9)]]
    rank_one = [[(x+j*k*101, y-j*k*202) for j, (x, y) in enumerate(base)] for k in range(3)]
    for rows in (varied, rank_one):
        nonzero = False
        for r, s in combinations(range(len(base)), 2):
            summed = [tuple(sum(sign*branch[label][axis] for sign, branch in zip(signs, rows))
                            for axis in range(2)) for label in (r, s)]
            left = sum(sign*det(branch[r], branch[s]) for sign, branch in zip(signs, rows)) - det(*summed)
            right = sum(signs[i]*signs[k]*det(sub(rows[i][r], rows[k][r]), sub(rows[i][s], rows[k][s]))
                        for i, k in combinations(range(len(rows)), 2))
            assert left == right
            nonzero |= left != 0
        assert nonzero == (rows is varied)


def first_moment_lower_squared(rows, n, unit, p_lo, p_hi):
    # Evaluate the equiangular sample moment using a rational angle center.
    # Taylor's real remainder and the 1-Lipschitz sine and cosine cover the errors.
    p = F(314159265, 10**8)
    assert p < p_lo < p_hi < p+F(4, 10**9)
    sine_error = (F(22, 7)**22 / factorial(22)) + (p_hi-p)
    cosine_error = (F(22, 7)**23 / factorial(23)) + (p_hi-p)
    error = sine_error + cosine_error
    a_re = a_im = 0
    for j, (x, y) in enumerate(rows):
        angle = j*p/n
        sine = sum((-1)**k*angle**(2*k+1)/factorial(2*k+1) for k in range(11))
        cosine = sum((-1)**k*angle**(2*k)/factorial(2*k) for k in range(12))
        a_re += x*cosine-y*sine
        a_im += y*cosine+x*sine
    a_re /= n*unit
    a_im /= n*unit
    sinc_lo = 1 - (p_hi/(2*n))**2/6
    return sinc_lo**4 * (max(0, abs(a_re)-error)**2 + max(0, abs(a_im)-error)**2)


def check_quarter_turn(rows, unit, pi_lo, area):
    signed = [tuple(z) for z in rows] + [(-x, -y) for x, y in rows]
    count = len(signed)
    shifted = signed[count//4:] + signed[:count//4]
    determinants = [F(det(z, w), unit**2) for z, w in zip(signed, shifted)]
    mean = sum(determinants)/count
    assert min(determinants) > F(27922, 10**5)
    assert F(6043893, 10**7) < mean < F(6043894, 10**7)
    assert pi_lo**2/(2*mean) > F(816, 100)
    assert pi_lo**2/(1+mean) > F(61516, 10**4)
    required_mean = pi_lo**2/(2*area)
    assert required_mean > F(8024068, 10**7)
    budget = (1-required_mean)/2
    assert budget < F(98797, 10**6)
    sample_lo, continuous_lo = F(4447530, 10**7), F(43513, 10**5)
    for sign in (1, -1):
        # Twice the orthogonal projection in integer units.
        proj = [(x-sign*v, y+sign*u) for (x, y), (u, v) in zip(signed, shifted)]
        norm_squared = F(sum(x*x+y*y for x, y in proj), 4*unit**2*count)
        midpoint_squared = F(sum((x+u)**2+(y+v)**2 for (x, y), (u, v)
                                 in zip(proj, proj[1:]+proj[:1])), 16*unit**2*count)
        assert norm_squared > sample_lo**2 and midpoint_squared > continuous_lo**2
    assert 1-budget/sample_lo**2 > F(5005, 10**4)
    assert 1-budget/(sample_lo-F(1, 20))**2 > F(3659, 10**4)
    assert 1-budget/(continuous_lo-F(1, 20))**2 > F(1, 3)


def main():
    a5, b5 = atan_bounds(5)
    a239, b239 = atan_bounds(239)
    p_lo = F(3141592653589793238, 10**18)
    p_hi = F(3141592653589793239, 10**18)
    assert p_lo < 16*a5-4*b239 < 16*b5-4*a239 < p_hi
    area = F(123, 20)
    action_lo = F(2213775623134282058736195815563, 3583999641600000000000000000000)*p_lo**2
    gaps = [2*p_lo*F(111, 112)-area, 2*p_lo*F(223, 224)-area, 2*p_lo-area]
    assert gaps[0] > F(770854, 10**7) and gaps[2] > F(1331853, 10**7)
    for gap, target in zip(gaps, [667579, 910499, 1153418]):
        assert gap > 0 and 3*gap**2 > 4*F(target, 10**7)**2
    assert gaps[0] > F(1435, 1000)*(area-action_lo)
    assert 3*gaps[0]**2 > 4*(F(1242, 1000)*(area-action_lo))**2
    assert 4*p_lo**2/area-2*p_hi > F(1360695, 10**7)
    signed_discrepancy_test()

    filename = Path(__file__).with_name('issue163_planar_witness.json')
    contents = filename.read_bytes()
    assert sha256(contents).hexdigest() == 'c68acffd8bc66d90e359550a783cac92c0b31fe7817577a374075167d36350e9'
    record = json.loads(contents)
    rows = record['neighbor_planar_vectors']
    n, unit = len(rows), record['phase_denominator']
    assert n == 112 and unit == 10**8 and all(x*x+y*y <= unit**2 for x, y in rows)
    check_quarter_turn(rows, unit, p_lo, area)
    polygon = hull([tuple(row) for row in rows] + [(-x, -y) for x, y in rows])
    polygon_area = F(sum(det(v, polygon[(i+1) % len(polygon)]) for i, v in enumerate(polygon)), 2*unit**2)
    assert F(9847407, 10**7)*p_hi < polygon_area < F(9847408, 10**7)*p_lo

    old_raw_lower = F(999701031, 10**9)  # issue163_planar_comass.cjs, same pinned rows
    cap = F(9999999, 10**7)
    coeffs = [6500, -2040, -800, -200, 0, 0, 0, -900] + [-60]*12 + [-4]*35 + [0]
    coeffs += coeffs[-2::-1]
    profile = [2000*(55-j)+2*j-55 for j in range(n)]
    assert [j for j, value in enumerate(profile) if abs(value)>55*2000] == [111] and profile[-1] < 0
    assert max(abs(v-w) for v, w in zip(profile, profile[1:]+[-profile[0]])) < 2000
    anchor_addition = -F(sum(c*det(rows[-1], z) for c, z in zip(coeffs, rows[:-1], strict=True)), 10**6*unit**2)
    old_lower = old_raw_lower/cap
    new_lower = (old_raw_lower+anchor_addition)/cap
    assert old_lower > F(99970, 10**5) and new_lower > F(99922, 10**5)
    anti_energy_lo = p_lo**2*first_moment_lower_squared(rows, n, unit, p_lo, p_hi)/8
    assert anti_energy_lo > F(139, 1000) and anti_energy_lo > 170*(1-new_lower)
    print('112-pair discrepancy > 0.0667579, 224-pair > 0.0910499, dense > 0.1153418 at area 6.15')
    print(f'Witness hull has {len(polygon)} vertices; normalized area in (0.9847407, 0.9847408)')
    print('Witness excluded on >50.05% of area; RMS distance >0.05 on >36.59% (grid shifts)')
    print('First Fourier map has e-J > 0.139; signed anchor field density > 0.99922')


if __name__ == '__main__':
    main()
