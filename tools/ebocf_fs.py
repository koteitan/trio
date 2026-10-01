# Denis's fundamental sequences for Extended Buchholz terms (googology wiki "Extended Buchholz's function"), on Ytosk term tuples.
# G0 = "zero": the diagonalization starts at gamma[0] = 0 (BM4 expansion matches this better); "omega": gamma[0] = Omega_mu (Denis).
import sys
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import ytosk_eval as Y
Z=(); ONE=Y.ONE
def summ(t):
    out=[]
    while t: out.append((t[0],t[1],Z)); t=t[2]
    return out
def build(ss):
    t=Z
    for s in reversed(ss): t=(s[0],s[1],t)
    return t
def is_succ(t):
    s=summ(t); return bool(s) and s[-1]==ONE
def pred(t):
    s=summ(t); return build(s[:-1])
def cof(t):
    """None for 0, ('1',) successor, ('w',), ('Om', C) where C = Omega_{mu+1} term (psi_{mu+1}(0))"""
    if not t: return None
    s=summ(t)
    if len(s)>=2: return cof(s[-1])
    nu,b,_=t
    if not b:
        if not nu: return ('1',)
        if is_succ(nu): return ('Om',(nu,Z,Z))
        return cof(nu)
    if is_succ(b): return ('w',)
    cb=cof(b)
    if cb[0]=='w': return cb
    C=cb[1]  # Omega_{mu+1}, mu+1 = C[0]
    mu=pred(C[0])
    if Y.lt(mu,nu): return cb
    return ('w',)
def mul(t,n):
    r=Z
    for _ in range(n): r=Y.add(r,t)
    return r
def nat(n): return mul(ONE,n)
G0='zero'
def fs(t, eta):
    """t[eta]; eta is int for cof w, term for cof Omega"""
    s=summ(t)
    if len(s)>=2:
        return Y.add(build(s[:-1]), fs(s[-1],eta)) if True else None
    nu,b,_=t
    if not b:
        if not nu: return Z
        if is_succ(nu): return eta if not isinstance(eta,int) else nat(eta)
        return (fs(nu,eta),Z,Z)
    if is_succ(b): return mul((nu,pred(b),Z), eta)
    cb=cof(b)
    if cb[0]=='w': return (nu, fs(b,eta), Z)
    C=cb[1]; mu=pred(C[0])
    if Y.lt(mu,nu): return (nu, fs(b,eta), Z)
    # diagonalize
    g=Z if G0=='zero' else (mu,Z,Z)
    for _ in range(eta): g=(mu, fs(b,g), Z)
    return (nu, fs(b,g), Z)
