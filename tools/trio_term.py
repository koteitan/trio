"""Python port of lean/Term.lean translate + olt and lean/Cnf.lean cnf.

Terms: Z = None, P a1 a2 b c = (a1, a2, b, c).
Columns: (x, y, z); translate maps column (x,y,z) to P y z (children) (siblings)
where children = maximal following block with row0 > x.
"""

def translate(S):
    if not S:
        return None
    p = S[0]
    rest = S[1:]
    i = 0
    while i < len(rest) and rest[i][0] > p[0]:
        i += 1
    return (p[1], p[2], translate(rest[:i]), translate(rest[i:]))

def olt(x, y):
    if x is None:
        return y is not None
    if y is None:
        return False
    a1, a2, b, c = x
    e1, e2, f, g = y
    if a1 != e1:
        return a1 < e1
    if a2 != e2:
        return a2 < e2
    if b != f:
        return olt(b, f)
    return olt(c, g)

def cnf(t):
    while t is not None:
        a1, a2, b, c = t
        if not cnf(b):
            return False
        if c is not None:
            e1, e2, f, g = c
            if olt((a1, a2, b, None), (e1, e2, f, None)):
                return False
        t = c
    return True
