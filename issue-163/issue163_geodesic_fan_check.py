"""Exact cyclic-order and two-field checks using the archived planar witness."""

from fractions import Fraction as F
from functools import cmp_to_key
from hashlib import sha256
import json
from math import isqrt, pi, tan
from pathlib import Path
import subprocess

from issue163_fiber_check import atan_bounds, det


HERE = Path(__file__).resolve().parent
N = 112


def angular_compare(u, v):
    def half(p):
        return 0 if p[1] > 0 or (p[1] == 0 and p[0] > 0) else 1

    if half(u) != half(v):
        return half(u) - half(v)
    cross = det(u, v)
    return (cross < 0) - (cross > 0)


def check_rotation(rows, labels, cosine, expected):
    ordered = sorted(labels, key=cmp_to_key(lambda i, j: angular_compare(rows[i], rows[j])))
    # Each circular gap exceeds twice the allowed angular error.
    for i, j in zip(ordered, ordered[1:] + ordered[:1]):
        u, v = rows[i], rows[j]
        dot = u[0]*v[0] + u[1]*v[1]
        assert det(u, v) > 0
        if dot > 0:
            assert dot**2 < (2*cosine**2 - 1)**2 * sum(x*x for x in u) * sum(x*x for x in v)
    genera = []
    for order in [ordered, ordered[::-1]]:
        successor = dict(zip(order, order[1:] + order[:1]))
        permutation = {j: successor[labels[k-1]] for k, j in enumerate(labels)}
        boundaries = 0
        while permutation:
            i = next(iter(permutation))
            boundaries += 1
            while i in permutation:
                i = permutation.pop(i)
        genera.append((len(labels) - boundaries) // 2)
    assert tuple(genera) == expected


def check_realizing_directions(rows, unit):
    # Approximate sqrt((unit^2-S)/S) from below by a dyadic. The resulting
    # direction vector differs from the exact unit vector by at most 2^-48.
    scale = 2**48
    first, second = [], []
    for x, y in rows:
        squared = x*x + y*y
        q = isqrt((unit**2 - squared) * scale**2 // squared)
        first.append((scale*x - q*y, scale*y + q*x))
        second.append((-scale*x - q*y, -scale*y + q*x))
    cosine = 1 - F(1, 10**12)
    assert 1 - F(2, scale) > cosine
    check_rotation(first + second, list(range(2*N)), cosine, (98, 102))


def monotone_slopes(rows, unit):
    # Pool adjacent blocks whose mean half-angle slope decreases.
    blocks = []
    for x, y in rows:
        blocks.append((F(y, unit + x), 1))
        while len(blocks) > 1:
            a, m = blocks[-2]
            b, n = blocks[-1]
            if a*n <= b*m:
                break
            blocks[-2:] = [(a+b, m+n)]
    den = 10**6
    pooled = [F(round(den*total/count), den) for total, count in blocks for _ in range(count)]
    slopes = [s + F(j, 10**9) for j, s in enumerate(pooled)]
    assert all(a < b for a, b in zip(slopes, slopes[1:])) and slopes[0] > 0
    return slopes


def on_circle(t):
    return (1-t*t)/(1+t*t), 2*t/(1+t*t)


def evaluate(bins, rows, anchor):
    # Load the verified chamber coefficients in their native integer representation.
    loader = """
const {loadProfile,HERM_DEN} = require('./issue163_midpoint.cjs');
const data = loadProfile('issue163_inputs', JSON.parse(process.argv[1]));
console.log(JSON.stringify([HERM_DEN, data.cap, data.w],
    (_, value) => typeof value === 'bigint' ? value.toString() : value));
"""
    reply = subprocess.run(["node", "-e", loader, json.dumps(bins)], cwd=HERE,
                           check=True, capture_output=True, text=True)
    scale, cap, weights = json.loads(reply.stdout)
    raw = sum(2*int(weights[i][j])*det(rows[i], rows[j])
              for i in range(N) for j in range(i+1, N)) / int(scale)
    if anchor:
        half = [6500, -2040, -800, -200, 0, 0, 0, -900] + [-60]*12 + [-4]*35
        coefficients = half + [0] + half[::-1]
        raw += sum(c*det(rows[i], rows[-1]) for i, c in enumerate(coefficients)) / 10**6
    quarter = sum((1 if i < N//2 else -1) * det(rows[i], rows[(i+N//2) % N])
                  for i in range(N)) / N
    return raw * F(10**12, int(cap)), quarter


def check_calibration(rows, unit):
    neighbor = [on_circle(t) for t in monotone_slopes(rows, unit)]
    # Trigonometry only proposes rational parameters for the second legal test.
    first = [on_circle(F(round(10**6 * tan(pi*j/(2*N))), 10**6)) for j in range(N//2)]
    center = first + [(-y, x) for x, y in first]
    for test in [neighbor, center]:
        assert all(x*x + y*y == 1 for x, y in test)
        full = test + [(-x, -y) for x, y in test]
        order = sorted(range(2*N), key=cmp_to_key(lambda i, j: angular_compare(full[i], full[j])))
        assert all((a+1) % (2*N) == b for a, b in zip(order, order[1:] + order[:1]))
    profiles = [
        [55-j + F(2*j-55, 2000) for j in range(N)],
        [F(1 if j <= 56 else -1, 100) for j in range(N)],
    ]
    for profile, high_count in zip(profiles, (1, 0)):
        full = profile + [-u for u in profile]
        assert all(abs(a-b) < 1 for a, b in zip(full, full[1:] + full[:1]))
        assert all(u.denominator != 1 for u in full)
        assert sum(u > 55 for u in full) == high_count
    w1, q1 = evaluate([int(u+56) for u in profiles[0]], neighbor, True)
    w2, q2 = evaluate([int(u+56) for u in profiles[1]], center, False)
    assert q2 == 1
    b = F(2213775623134282058736195815563, 3583999641600000000000000000000)
    first_weight = (b - w2/2) / (w1 - w2*q1)
    second_weight = F(1, 2) - first_weight*q1
    assert min(first_weight, second_weight) > 0
    _, high5 = atan_bounds(5)
    low239, _ = atan_bounds(239)
    ceiling = (16*high5 - 4*low239)**2 * (first_weight + second_weight)
    assert ceiling < F(612048, 100000)
    print(f"Ordered neighboring test W={float(w1):.8f}, Q={float(q1):.8f}.")
    print(f"Ordered two-test ceiling < 6.12048 (upper estimate {float(ceiling):.8f}).")


if __name__ == "__main__":
    data = (HERE / "issue163_planar_witness.json").read_bytes()
    assert sha256(data).hexdigest() == "c68acffd8bc66d90e359550a783cac92c0b31fe7817577a374075167d36350e9"
    record = json.loads(data)
    rows, unit = record["neighbor_planar_vectors"], record["phase_denominator"]
    full = rows + [(-x, -y) for x, y in rows]
    radius = F(99999995, 10**8)
    assert all(unit**2 * radius**2 < x*x + y*y <= unit**2 for x, y in full)
    labels = [i for i in range(2*N) if i % N not in (53, 57, 63, 66, 72)]
    check_rotation(full, labels, radius, (98, 100))
    check_realizing_directions(rows, unit)
    short = [0, 11, 15, 33, 36, 79, 84, 97, 105, 111]
    check_rotation(full, short + [i+N for i in short], 2*(radius-F(1, 400))-1, (6, 6))
    print("Minimum genus for the exact witness: 98. Error at most 1/400 requires genus at least 6.")
    check_calibration(rows, unit)
