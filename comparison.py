import time
import random
from itertools import combinations

# --- Solver implementations ---

def resolution_solver(cnf):
    """
    Resolution-based SAT solver.
    Returns True if satisfiable, False if unsatisfiable.
    """
    clauses = set(cnf)
    new = set()
    while True:
        for ci, cj in combinations(clauses, 2):
            for l in ci:
                if -l in cj:
                    resolvent = (ci.union(cj)) - {l, -l}
                    if not resolvent:
                        return False  # Derived empty clause => UNSAT
                    new.add(frozenset(resolvent))
        if new.issubset(clauses):
            return True  # No new clauses => SAT
        clauses |= new
        new.clear()

def dp_solver(cnf):
    """
    Davis–Putnam algorithm.
    Returns True if satisfiable, False if unsatisfiable.
    """
    if not cnf:
        return True
    if any(len(c) == 0 for c in cnf):
        return False
    lit = next(iter(next(iter(cnf))))
    var = abs(lit)
    pos = [c for c in cnf if var in c]
    neg = [c for c in cnf if -var in c]
    others = [c for c in cnf if var not in c and -var not in c]
    resolvents = []
    for c1 in pos:
        for c2 in neg:
            r = (c1.union(c2)) - {var, -var}
            resolvents.append(frozenset(r))
    return dp_solver(others + resolvents)

def dpll_solver(cnf, assignment=None):
    """
    DPLL with unit propagation and pure literal elimination.
    Returns True if satisfiable, False if unsatisfiable.
    """
    if assignment is None:
        assignment = {}
    # Unit propagation
    while True:
        units = [c for c in cnf if len(c) == 1]
        if not units:
            break
        l = next(iter(units[0]))
        var, val = abs(l), (l > 0)
        assignment[var] = val
        new_cnf = []
        for c in cnf:
            if l in c:
                continue
            if -l in c:
                reduced = frozenset(x for x in c if x != -l)
                if not reduced:
                    return False
                new_cnf.append(reduced)
            else:
                new_cnf.append(c)
        cnf = new_cnf

    # Pure literal elimination
    lits = {l for c in cnf for l in c}
    pures = [l for l in lits if -l not in lits]
    for l in pures:
        var, val = abs(l), (l > 0)
        assignment[var] = val
        cnf = [c for c in cnf if l not in c]

    if not cnf:
        return True
    if any(len(c) == 0 for c in cnf):
        return False

    # Branch on a literal
    lit = next(iter(next(iter(cnf))))
    var = abs(lit)
    for val in (True, False):
        branch_lit = var if val else -var
        new_cnf = []
        for c in cnf:
            if branch_lit in c:
                continue
            if -branch_lit in c:
                reduced = frozenset(x for x in c if x != -branch_lit)
                new_cnf.append(reduced)
            else:
                new_cnf.append(c)
        if dpll_solver(new_cnf, dict(assignment)):
            return True
    return False

# --- CNF Generators ---

def generate_random_cnf(n_vars, n_clauses, clause_size=3):
    cnf = []
    for _ in range(n_clauses):
        clause = set()
        while len(clause) < clause_size:
            var = random.randint(1, n_vars)
            lit = var if random.choice((True, False)) else -var
            clause.add(lit)
        cnf.append(frozenset(clause))
    return cnf

# --- Some hand-crafted examples ---

examples = {
    "Simple SAT": [
        frozenset([1, -2]),
        frozenset([2, 3]),
        frozenset([-1, -3]),
    ],
    "Simple UNSAT": [
        frozenset([1]),
        frozenset([-1]),
    ],
    "XOR (unsat by 2-SAT)": [
        frozenset([1, 2]),
        frozenset([-1, -2]),
        frozenset([1, -2]),
        frozenset([-1, 2]),
    ],
    "Pigeonhole 2 pigeons → 1 hole UNSAT": [
        # pigeon 1 in hole A or B
        frozenset([1, 2]),
        # pigeon 2 in hole A or B
        frozenset([3, 4]),
        # no two pigeons in the same hole:
        # ¬(p1,A ∧ p2,A) → (-1 or -3)
        frozenset([-1, -3]),
        # ¬(p1,B ∧ p2,B) → (-2 or -4)
        frozenset([-2, -4]),
    ]
}

# --- Benchmark harness ---

def run_solver(name, solver, cnf):
    start = time.time()
    res = solver(cnf)
    elapsed = time.time() - start
    return "SAT" if res else "UNSAT", elapsed

if __name__ == "__main__":
    # 1) Hand-crafted examples
    print("=== Hand-Crafted Examples ===")
    for desc, cnf in examples.items():
        print(f"\n{desc}:")
        for name, sol in (("Resolution", resolution_solver),
                          ("DP", dp_solver),
                          ("DPLL", dpll_solver)):
            sat_unsat, t = run_solver(name, sol, cnf)
            print(f"  {name:<10} → {sat_unsat} in {t:.6f}s")

    # 2) Random benchmarks: vary vars, clauses, clause size
    print("\n=== Random Benchmarks ===")
    random.seed(42)
    for n_vars, n_clauses, c_size in [
        (4, 6, 3),
        (6, 12, 3),
        (8, 16, 3),
        (10, 40, 4),
    ]:
        cnf = generate_random_cnf(n_vars, n_clauses, clause_size=c_size)
        print(f"\n{n_vars} vars, {n_clauses} clauses, size={c_size}")
        for name, sol in (("Resolution", resolution_solver),
                          ("DP", dp_solver),
                          ("DPLL", dpll_solver)):
            sat_unsat, t = run_solver(name, sol, cnf)
            print(f"  {name:<10} → {sat_unsat} in {t:.6f}s")
