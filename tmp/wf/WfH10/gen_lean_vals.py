import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Y,Z
from lhd_exact import comps
s=sys.argv[1]
M=[tuple(map(int,t.split(','))) for t in s.strip('()').split(')(')]
C=H.Ctx(M)
def L(t):
 if not t:return 'z'
 return '(psi %s %s %s)'%(L(t[0]),L(t[1]),L(t[2]))
print('def oTab : List T := ['+', '.join(L(C.o(i)) for i in range(len(M)))+']')
print('def vTab : List T := ['+', '.join(L(C.v(i)) for i in range(len(M)))+']')
om=C.vOpt1(27);W=C.bumpW(18);O1=((Z,Z,Z),Z,Z)
print('-- V',L(om),'W',L(W))
print('-- comps z V',[L(g) for g in comps(Z,om)],'comps z Om1',[L(g) for g in comps(Z,O1)],'Gc',[L(g) for g in comps(Z,Z)])
