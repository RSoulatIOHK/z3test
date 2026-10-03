"""Direct uniqueness strategy: finite-field oracles, budgets and explanations."""
import itertools
from z3 import *


def run(formulas, expected, **options):
    goal = Goal()
    goal.add(*formulas)
    residual = With(Tactic('ff-unique'), **options)(goal)
    assert len(residual) == 1
    # Use the exact BV translation to check residual goals independently of
    # the native field algebra and the uniqueness implementation.
    solver = Then('ff2bv', 'smt').solver()
    solver.add(*residual[0])
    assert solver.check() == expected, (formulas, residual, solver.reason_unknown())
    if expected == sat:
        model = solver.model()
        assert all(is_true(model.eval(f, model_completion=True)) for f in formulas), (formulas, model)
    return residual[0]


def main():
    checks = 0
    for prime in [2, 3, 5, 7]:
        field = FiniteFieldSort(prime)
        a, b, c, d = Consts('a b c d', field)
        variables = [a, b, c, d]
        for mask in [15, 7, 0]:
            guards = [v*v == v for i, v in enumerate(variables) if mask & (1 << i)]
            for weight in [1, 2, prime-1]:
                formulas = guards + [a+weight*b == c+weight*d, a != c]
                expected = sat if any(
                    all(not (mask & (1 << i)) or v*v % prime == v for i, v in enumerate(values))
                    and (values[0]+weight*values[1]-values[2]-weight*values[3]) % prime == 0
                    and values[0] != values[2]
                    for values in itertools.product(range(prime), repeat=4)) else unsat
                for options in [{}, {'ff.unique_equalities': True}, {'ff.unique_work': 1}]:
                    run(formulas, expected, **options)
                    checks += 1
        # Boolean case splitting must close both branches. A resource limit or
        # missing premise must leave a satisfiable residual goal intact.
        formulas = [a*a == a, b*b == b, a*b == 1, a+b == 1]
        run(formulas, unsat)
        run(formulas, unsat, **{'ff.unique_nodes': 1})
        for omitted in [2, 3]:
            run([f for i, f in enumerate(formulas) if i != omitted], sat)
        # Scaled functional definitions carry root consequences without relying
        # on the variable names or an assumed nonzero symbolic coefficient.
        run([c == a*b, 2*d == 2*a*b, c != d], sat if prime == 2 else unsat)
        run([a*c == a*b, c != b], sat)
        checks += 6
    print(f'{checks} direct uniqueness checks against exact BV solving and finite-field oracles passed')


if __name__ == '__main__':
    main()
