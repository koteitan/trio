"""Exhaustively check PassRootRes, V3ExpT1V.lean, below SRO.

A case is a counted child c of the last column's row-1 parent r,
with c < x, DepX M x false c, and cof(last(v(c))) = big(v(r)).
The conclusion is that c has no earlier counted sibling. No sampling.
"""
from collections import Counter
from probe_inv2 import SRO, dependencies, main
from probe_inv3_prefix import Ctx, cof, last


def measure_passroot(matrix):
    M = list(matrix)
    counts, examples = Counter(input=1), {}
    if not M < SRO:
        counts['outside_SRO'] += 1
        return counts, examples
    counts['below_SRO'] += 1
    x = len(M) - 1
    if x < 1 or M[x][1] == 0 or M[x][2] != 0:
        return counts, examples
    C = Ctx(M)
    if not C.ok:
        counts['eval_failed'] += 1
        examples['eval_failed'] = {'matrix': M}
        return counts, examples
    counts['t1_evaluated'] += 1
    r = C.e.par(1, x)
    if r is None:
        return counts, examples
    D = dependencies(C, x)
    children = C.CL(r)
    for index, c in enumerate(children):
        if c >= x or (False, c) not in D:
            continue
        counts['dependent_frames'] += 1
        if cof(last(C.v(c))) != ('big', C.v(r)):
            continue
        counts['PassRootRes.cases'] += 1
        if index != 0:
            counts['PassRootRes.failures'] += 1
            examples.setdefault('PassRootRes', {
                'matrix': M, 'x': x, 'r': r, 'c': c,
                'earlier_counted': children[:index],
                'later_counted': children[index+1:],
                'v_r': C.v(r), 'last_v_c': last(C.v(c)),
                'cof_last_v_c': cof(last(C.v(c))),
            })
    return counts, examples


if __name__ == '__main__':
    main(measure_fn=measure_passroot, fields=('PassRootRes',),
         case_unit='passing dependent counted child at r',
         definitions=('V3ExpT1V.lean: PassRootRes',))
