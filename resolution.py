import time
import copy
from typing import List, Optional

Clause = List[int]
CNFFormula = List[Clause]


def parse_formula() -> CNFFormula:

    return [[1, -2], [2, 3], [-1, -3]]


def resolution_solver(cnf: CNFFormula) -> bool:
    clauses = set(frozenset(c) for c in cnf)

    new = set()
    while True:
        pairs = [(c1, c2) for c1 in clauses for c2 in clauses if c1 != c2]
        for (ci, cj) in pairs:
            resolvents = resolve(ci, cj)
            if frozenset() in resolvents:
                return False
            new.update(resolvents)
        if new.issubset(clauses):
            return True
        clauses.update(new)


def resolve(ci: frozenset, cj: frozenset) -> List[frozenset]:
    resolvents = []
    for literal in ci:
        if -literal in cj:
            resolvent = (ci.union(cj)) - {literal, -literal}
            resolvents.append(frozenset(resolvent))
    return resolvents


def dp_solver(cnf: CNFFormula) -> bool:
    return dp_recursive(cnf, [])


def dp_recursive(cnf: CNFFormula, assignment: List[int]) -> bool:
    if [] in cnf:
        return False
    if not cnf:
        return True

    variable = abs(cnf[0][0])
    new_cnf_true = simplify(cnf, variable)
    new_cnf_false = simplify(cnf, -variable)

    return dp_recursive(new_cnf_true, assignment + [variable]) or dp_recursive(new_cnf_false, assignment + [-variable])


def simplify(cnf: CNFFormula, literal: int) -> CNFFormula:
    new_cnf = []
    for clause in cnf:
        if literal in clause:
            continue
        new_clause = [x for x in clause if x != -literal]
        new_cnf.append(new_clause)
    return new_cnf


def dpll_solver(cnf: CNFFormula) -> bool:
    return dpll_recursive(cnf, [])


def dpll_recursive(cnf: CNFFormula, assignment: List[int]) -> bool:
    if [] in cnf:
        return False
    if not cnf:
        return True


    unit_clauses = [c for c in cnf if len(c) == 1]
    while unit_clauses:
        unit = unit_clauses[0][0]
        assignment.append(unit)
        cnf = simplify(cnf, unit)
        if [] in cnf:
            return False
        unit_clauses = [c for c in cnf if len(c) == 1]


    literals = {lit for clause in cnf for lit in clause}
    for lit in list(literals):
        if -lit not in literals:
            cnf = simplify(cnf, lit)
            assignment.append(lit)

    if not cnf:
        return True

    variable = abs(cnf[0][0])
    return dpll_recursive(simplify(cnf, variable), assignment + [variable]) or \
           dpll_recursive(simplify(cnf, -variable), assignment + [-variable])


def benchmark_solver(name: str, solver_func, cnf: CNFFormula):
    cnf_copy = copy.deepcopy(cnf)
    start = time.time()
    result = solver_func(cnf_copy)
    duration = time.time() - start
    print(f"{name:10s} | Result: {'SAT' if result else 'UNSAT'} | Time: {duration:.6f} seconds")


def main():
    cnf = parse_formula()
    print("Running SAT solvers on formula:", cnf)
    benchmark_solver("Resolution", resolution_solver, cnf)
    benchmark_solver("DP", dp_solver, cnf)
    benchmark_solver("DPLL", dpll_solver, cnf)


if __name__ == "__main__":
    main()