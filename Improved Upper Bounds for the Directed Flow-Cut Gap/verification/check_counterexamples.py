#!/usr/bin/env python3
"""Exact finite checks for v3 source-audit counterexamples; no external packages.

This is a mathematical source audit, not a Lean proof or a counterexample to the
headline flow-cut bound. Fractions are exact. Logarithmic comparisons and the multiplicative-update
trajectory use floating logarithms, with explicit error margins. The symbolic
arguments in ../CORRECTIONS.md establish their asymptotic scope. Run: python3 check_counterexamples.py.
"""
from fractions import Fraction as F
from math import inf, log, log1p
import json


def chain_distance(weights, s, t, deleted=frozenset()):
    if s in deleted or t in deleted or s > t:
        return inf
    if any(v in deleted for v in range(s, t + 1)):
        return inf
    return sum((weights[v] for v in range(s + 1, t)), F(0))


def min_chain_cut(n, s, t, cap, deleted=frozenset()):
    """Minimum total-weight fractional cut, with deleted nodes fixed to one.

    Optimality is exact: an unhit unique path requires internal total >=1;
    this construction uses exactly one. If already hit/unreachable, zero
    additional mass is both feasible and minimal by nonnegativity.
    """
    weights = [F(int(v in deleted)) for v in range(n)]
    if s > t or any(v in deleted for v in range(s + 1, t)):
        return weights
    remaining = F(1)
    for v in range(s + 1, t):
        if v not in deleted:
            weights[v] = min(cap, remaining)
            remaining -= weights[v]
    assert remaining == 0
    assert chain_distance(weights, s, t) >= 1
    assert all(w == 1 if v in deleted else 0 <= w <= cap
               for v, w in enumerate(weights))
    return weights


def check_lemma18(L):
    assert L >= 5
    n = L + 3
    unit = [F(1)] * n
    P = {(s, t) for s in range(n) for t in range(n)
         if chain_distance(unit, s, t) >= L}
    reachable = {(s, t) for s, t in P if s < t}
    assert reachable == {(0, L + 1), (0, L + 2), (1, L + 2)}
    assert len(P) == n * (n - 1) // 2 + 3
    initial_mass = F(len(P) * n, L)
    cap = F(4, L)
    current = {p: min_chain_cut(n, *p, cap) for p in P}
    candidate_mass = sum((sum(w) for w in current.values()), F(0))
    assert candidate_mass == 3
    assert initial_mass > log(n) * candidate_mass
    # Algorithm switches to epoch 2 and chooses this allowed oracle minimizer.
    selected = (0, L + 1)
    d = F(2, L)  # Every d in the open interval (0,4/L) gives the same cut.
    X = {v for v in range(n)
         if chain_distance(current[selected], 0, v) <= d
         <= chain_distance(current[selected], 0, v) + current[selected][v]}
    assert X == {1}
    P.remove(selected)
    mass = sum((sum((w[v] for v in range(n) if v not in X), F(0))
                for p, w in current.items() if p in P), F(0))
    assert mass == 2 - F(4, L) > 0
    next_candidates = {p: min_chain_cut(n, *p, F(16, L), X) for p in P}
    next_mass = sum((sum((w[v] for v in range(n) if v not in X), F(0))
                     for w in next_candidates.values()), F(0))
    assert next_mass == 1
    assert mass <= log(n) * next_mass  # No switch before the second round.
    assert all(chain_distance(unit, *p, X) == inf for p in P)
    assert chain_distance(current[(1, L + 2)], 1, L + 2) == 1
    assert not any(v in X for v in range(2, L + 2))
    return {"L": L, "n": n, "initial_demands": len(P) + 1,
            "initial_mass": str(initial_mass), "first_candidate_mass": 3,
            "selected": selected, "level": str(d), "X": sorted(X),
            "second_round_mass": str(mass), "second_candidate_mass": 1,
            "remaining_demand_paths_in_G_minus_X": 0,
            "uncut_remaining_demand": [1, L + 2]}


def simple_paths(vertices, edges, s, t):
    if s == t:
        return [(s,)]
    out = []
    def visit(path):
        if path[-1] == t:
            out.append(tuple(path))
            return
        for v in vertices:
            if (path[-1], v) in edges and v not in path:
                visit(path + [v])
    visit([s])
    return out


def check_theorem29():
    V = ("v", "u", "t")
    E = {("v", "u"), ("u", "v"), ("u", "t")}
    w = {"v": F(0), "u": F(1), "t": F(0)}
    paths = simple_paths(V, E, "v", "t")
    assert paths == [("v", "u", "t")]
    assert min(sum((w[x] for x in p[1:-1]), F(0)) for p in paths) == 1
    assert w["v"] <= F(1, 2 * len(V))
    assert any(b == "v" for a, b in E) and any(a == "v" for a, b in E)
    E2 = {(a, b) for a, b in E if a != "v" and b != "v"}
    E2 |= {(a, b) for a, x in E for y, b in E if x == y == "v"}
    V2 = ("u", "t")
    reachable_far = []
    for a in V2:
        for b in V2:
            ps = simple_paths(V2, E2, a, b)
            if ps and min(sum((w[x] for x in p[1:-1]), F(0)) for p in ps) >= 1:
                reachable_far.append((a, b))
    assert reachable_far == []
    return {"original_demand": ["v", "t"], "forced_cut_vertex": "u",
            "contracted": "v", "reduced_edges": sorted(E2),
            "reduced_reachable_far_pairs": reachable_far,
            "valid_reduced_cut": [], "original_cut_valid": False}


def check_base_path_constant():
    """Fixed-parameter structural witness; not an Algorithm 2 execution."""
    L, lam, n = 8, F(1), 11
    path = tuple(range(1, 10))
    w = [F(1, L)] * n
    heights = [chain_distance(w, 0, v) for v in path]
    assert len(path) - 1 == L
    assert all(a + F(1, L) == b for a, b in zip(heights, heights[1:]))
    assert heights[-1] == 1
    assert chain_distance(w, 0, 10) >= 1
    mass = sum(w)
    assert 1 == F(8, 11) * mass
    suffix = path[-(len(path) // 4):]
    base_score = len(suffix)
    average_degree = F(len(path), n)
    printed_rhs = L * average_degree / lam
    assert base_score == 2 < printed_rhs == F(72, 11)
    return {"lemma": 19, "L": L, "lambda": str(lam), "n": n,
            "path": path, "source": 0, "target": 10,
            "average_degree": str(average_degree), "base_score": base_score,
            "printed_fixed_lambda_rhs": str(printed_rhs),
            "scope": "Structural witness conditions; not a full algorithm-state counterexample. Enlarging lambda preserves the asymptotic argument."}


def check_unscaled_update(n):
    """Actual cheapest-edge oracle on the weighted two-edge chain.

    With log costs a,b and increments A,B, D=a-b remains in [-B,A].
    Consequently q/T = (B+D/T)/(A+B). This is a trajectory check,
    not a certified floating-point or asymptotic Lean proof.
    """
    assert n >= 3
    epsilon = F(1, 2 * n)
    A = log1p(1 / float(epsilon))
    B = log1p(1 / float(1 - epsilon))
    rounds = max(4096, n)
    first = second = 0.0
    selected_small = 0
    tolerance = 2e-6
    for _ in range(rounds):
        if first <= second:
            first += A
            selected_small += 1
        else:
            second += B
        assert -B - tolerance <= first - second <= A + tolerance
    fraction = F(selected_small, rounds)
    limit = B / (A + B)
    assert limit - B / (rounds * (A + B)) - tolerance <= float(fraction)
    assert float(fraction) <= limit + A / (rounds * (A + B)) + tolerance
    return {"n": n, "small_weight": str(epsilon), "rounds": rounds,
            "small_edge_selections": selected_small,
            "small_edge_fraction": str(fraction),
            "predicted_limit": limit,
            "fraction_divided_by_small_weight": str(fraction / epsilon)}


if __name__ == "__main__":
    result = {"lemma18": [check_lemma18(L) for L in (5, 9, 29)],
              "theorem29": check_theorem29(),
              "lemma19_constant_bookkeeping": check_base_path_constant(),
              "charging_real_sigma_rounding": {"sigma": "3/2", "indices": [0, 1],
                  "count_exceeds_sigma": F(2) > F(3, 2),
                  "span_below_sigma": F(1) < F(3, 2)},
              "theorem33_unscaled_update": [check_unscaled_update(n) for n in (16, 256, 4096, 65536)],
              "theorem33_log_ratios": [
                  {"m": m, "x_log_1_plus_inverse_x": (2.0 ** -m) * log(1 + 2.0 ** m)}
                  for m in (4, 16, 64)]}
    print(json.dumps(result, indent=2))
