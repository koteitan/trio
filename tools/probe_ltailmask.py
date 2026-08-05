"""Is the machine's ambient lift exactly a mask lift of the tail?

    (L)  Lift1 ((0,v,z) :: R) t  =  (0, v+t, z) :: mlift R v t

i.e. `ltail v z R t = mlift R v t`.  If so, the whole obligation language of the
machine is "plant a root over a MASK-LIFTED tail", and since the mask lift
distributes over grafts at a constant threshold (probe_mliftgraft) the language
is closed under exactly the operation `Lift1` was not closed under.
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

def anc0(X, j):
    out = []; p = j
    while p is not None:
        out.append(p); p = trio.parent(X, 0, p)
    return out

def coneV(A, v):
    return {j for j in range(len(A)) if all(A[y][1] > v for y in anc0(A, j))}

def mlift(A, v, t):
    C = coneV(A, v)
    return [(c[0], c[1] + (t if i in C else 0), c[2]) for i, c in enumerate(A)]

def cone(X):
    return {i for i in range(len(X)) if trio.is_ancestor(X, 1, 0, i)}

def Lift1(X, t):
    C = cone(X)
    return [(c[0], c[1] + (t if i in C else 0), c[2]) for i, c in enumerate(X)]

COLS = [(a,b,c) for a in range(4) for b in range(4) for c in range(2)]
rnd = random.Random(9182)
tot = bad = 0; ex = None
badarg = 0
for _ in range(200000):
    v = rnd.randrange(3); z = rnd.randrange(2); t = rnd.randrange(1,3)
    R = [rnd.choice(COLS) for _ in range(rnd.randrange(1,4))]
    N = [(0,v,z)] + R
    lhs = Lift1(N, t)
    rhs = [(0, v+t, z)] + mlift(R, v, t)
    tot += 1
    if lhs != rhs:
        bad += 1
        if all(c[0] > 0 for c in R):
            badarg += 1
        if ex is None:
            ex = (v,z,t,R,lhs,rhs)
print(f"samples: {tot}   (L) violations: {bad}  (of which argOK tails: {badarg})")
if ex:
    print(f"  ex v={ex[0]} z={ex[1]} t={ex[2]} R={ex[3]}")
    print(f"    lhs={ex[4]}")
    print(f"    rhs={ex[5]}")
