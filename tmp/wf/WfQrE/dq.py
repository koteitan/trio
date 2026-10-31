"""Generalized substitution DQ (WfQrE): tN is t with the fsD hole path followed, and at each sum level on the path
some summands Q inserted before the new last summand, each in [newlast, oldlast).
dq(t, tN, eta) -> None (no such decomposition) or list of (depth, Q) with nonempty Q."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
from probe_inv3_prefix import Z, fs, fsD, summ, lt, cof, isSucc, init, last
from probe_inv3_prefix import le, sumN
def mk(l):
    t=Z
    for s in reversed(l):t=(s[0],s[1],t)
    return t
def dq(t,tN,eta,depth=0):
    if not t:return [] if not tN else None
    s=summ(t);sN=summ(tN)
    if len(sN)<len(s) or sN[:len(s)-1]!=s[:-1]:return None
    Q=sN[len(s)-1:-1];l=s[-1];lN=sN[-1]
    if any(not(le(lN,q) and lt(q,l)) for q in Q):return None
    rest=dq1(l,lN,eta,depth+1)
    if rest is None:return None
    return ([(depth,Q)] if Q else [])+rest
def dq1(t,tN,eta,depth):
    a,b,_=t
    if not b:
        if not a:return [] if tN==t else None
        if isSucc(a):return [] if tN==eta else None
        if tN[1]!=Z or tN[2]!=Z:return None
        return dq(a,tN[0],eta,depth)
    if isSucc(b):return [] if tN==fsD(t,eta) else None
    if cof(b)[0]=='big':return [] if tN==(a,fs(b,eta),Z) else None
    if tN[0]!=a or tN[2]!=Z:return None
    return dq(b,tN[1],eta,depth)
