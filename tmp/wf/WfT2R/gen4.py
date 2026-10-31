# WfT2R4: root descent with bad columns (t2_assembleRootX and the three root engines)
import re
D='/home/koteitan/proofs/trio/Ytosk/lean/Ytosk/'
X2=open(D+'WfT2X2.lean').read()
X3=open(D+'WfT2X3.lean').read()
# --- t2_assembleRootX from t2_assembleOTX
s=X2.index('theorem t2_assembleOTX')
e=X2.index('\nend Ytosk.WfT2X',s)
A=X2[s:e]
A=A.replace('theorem t2_assembleOTX','theorem t2_assembleRootX')
# conclusion
K='      ∀ i, i < bnd → (S true i ∨ W true i) → (cvals N σ i).Pairwise (fun a b => b ≤ a)) :\n'
cs=A.index(K)
ce=A.index(':= by\n',cs)
extra='''      ∀ i, i < bnd → (S true i ∨ W true i) → (cvals N σ i).Pairwise (fun a b => b ≤ a))
    (hGN : Good3 N σ) (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0)
    (hposN : ∀ j, bnd ≤ j → j < N.length → entry N 0 j ≠ 0) (hposM : entry M 0 bnd ≠ 0)
    (hRD : ∀ R, R < bnd → Anc0 M R bnd → col M R = (0, 0, 0) → DepS M S true R ∧ ¬ W true R)
    (hWle : ∀ i, i < bnd → W true i → σ.o i ≤ ρ.o i) :
    isOT (root N σ) = true ∧ root N σ < root M ρ '''
A=A[:cs]+extra+A[ce:]
# body tail
t=A.index('  apply good_below_ofX')
A=A[:t]+'''  apply root_gen hlenM hbN hcol hposN hposM hR01 hR12 h00 hG hGN
  · intro i hi
    by_cases hd : DepS M S true i
    · by_cases hw : W true i
      · exact hWle i hi hw
      · exact le_of_lt (hdl true i hd hi hw).lt
    · rw [(hoff i hi).1 hd]
  · intro R hR hRA hR0
    obtain ⟨hDR, hWR⟩ := hRD R hR hRA hR0
    exact (hdl true R hDR hR hWR).lt
'''
open('/home/koteitan/proofs/trio/tmp/wf/WfT2R/assembleRoot.lean','w').write(A)
QM=open(D+'V3T2QM.lean').read().split('\n')
TV=open(D+'V3T2V.lean').read().split('\n')
qn_extra='\n'.join(QM[251:275])+'\n'   # lines 252..275 : hWle and hRD
sv_extra='\n'.join(TV[228:238])+'\n'   # lines 229..238 : hRD
def section_of(name):
    i=X3.index('theorem '+name)
    s=X3.rindex('\nsection\n',0,i)+1
    e=X3.index('\nend\n',i)
    return X3[s:e+5]
def conv(name,newname,pre,extra_args):
    T=section_of(name)
    T=T.replace('theorem '+name,'theorem '+newname)
    k=T.index(' :\n    ∀ i, i < r + L → isOT (σ.o i) = true')
    ce=T.index(':= by\n',k)
    T=T[:k]+'\n    (hGN : Good3 (TRIO.gexp M r L d0 d1 n) σ) :\n    isOT (root (TRIO.gexp M r L d0 d1 n) σ) = true ∧ root (TRIO.gexp M r L d0 d1 n) σ < root M ρ '+T[ce:]
    a=T.index('  exact t2_assembleOTX')
    T=T[:a]+pre+T[a:].replace('exact t2_assembleOTX','exact t2_assembleRootX',1)
    endi=T.rindex('\n\n\nend')  if '\n\n\nend' in T else T.rindex('\n\nend')
    T=T[:endi]+'\n    '+extra_args+T[endi:]
    return T
sv=conv('t2_sv_belowX','t2_sv_rootX',sv_extra,
 "hGN hR01 hR12 h00 (fun j hj0 hj => by\n      have := e0_NQ_pos (d1 := d1) (qp := 0) hlen hL hA hp hL hd0e hn2 hj0 (by rw [hlN] at hj; exact hj)\n      omega)\n    (by have := anc0_e0_lt hA (by omega); omega) hRD (fun i _ h => h.elim)")
qr_pre='''  have hRD : ∀ R, R < r + L → Anc0 M R (r + L) → col M R = (0, 0, 0) →
      DepS M S true R ∧ ¬ (fun _ _ => False : Bool → Nat → Prop) true R := by
    intro R hR hRA _
    have hxn : ∀ p, ((∃ t, par M 0 p = some t ∧ col M p = bump M t) ∨ isUpg M p = true) →
        p ≠ r + L := by
      intro p hp' e
      subst e
      rcases hp' with ⟨t, hpt, hb⟩ | hu
      · rw [hp] at hpt; cases hpt; exact hXb hb
      · rw [isUpg_x_false hXu] at hu; cases hu
    exact ⟨(hiff true R hR).mpr (dep_anc_xG hUAT hZ2 hR12 hBE hx hxn hRA), id⟩
'''
def conv_qr():
    name='t2_qr_belowX'
    T=section_of(name)
    T=T.replace('theorem '+name,'theorem t2_qr_rootX')
    k=T.index(' :\n    ∀ i, i < r + L → isOT (σ.o i) = true')
    ce=T.index(':= by\n',k)
    T=T[:k]+'\n    (hGN : Good3 (TRIO.gexp M r L d0 d1 n) σ) :\n    isOT (root (TRIO.gexp M r L d0 d1 n) σ) = true ∧ root (TRIO.gexp M r L d0 d1 n) σ < root M ρ '+T[ce:]
    a=T.index('  have hgb := good_below_ofX')
    endi=T.rindex('\nend')
    T=T[:a]+"""  apply root_N2 hlen hL hp hd0e hn2 hXu hXb hrb he2r hIU hR0 hR01 hR12 h00 hG hGN
  · intro i hi
    by_cases hd : DepS M S true i
    · exact le_of_lt (hdl true i hd hi id).lt
    · rw [(hoff i hi).1 hd]
  · intro R hR hRA _
    have hxn : ∀ p, ((∃ t, par M 0 p = some t ∧ col M p = bump M t) ∨ isUpg M p = true) →
        p ≠ r + L := by
      intro p hp' e
      subst e
      rcases hp' with ⟨t, hpt, hb⟩ | hu
      · rw [hp] at hpt; cases hpt; exact hXb hb
      · rw [isUpg_x_false hXu] at hu; cases hu
    exact (hdl true R ((hiff true R hR).mpr (dep_anc_xG hUAT hZ2 hR12 hBE hx hxn hRA)) hR id).lt

"""+T[endi+1:]
    return T
qr=conv_qr()
qn=conv('t2_qn_belowX','t2_qn_rootX',qn_extra,
 "hGN hR01 hR12 h00 (fun j hj0 hj => by\n      have := e0_NQ_pos (d1 := d1) hlen hL hA hp hqp hd0e hn2 hj0 (by rw [hlN] at hj; exact hj)\n      omega)\n    (by have := anc0_e0_lt hA (by omega); omega) hRD hWle")
H='''/-
**WfT2R4: the root descent of `M[n]` with bad absorption columns (2026-11-01, t = 2 Bad2 route).**

`t2_assembleRootX`: `t2_assembleOTX` (WfT2X2) with the conclusion of `t2_assemble` (V3T2G): the root value drops.
The calls `PX` of `deps_lhd_otX` give `σ < ρ` also at bad columns (`PX.lt`), and the roots are never bad.
`t2_sv_rootX`・`t2_qr_rootX`・`t2_qn_rootX`: the engines `t2_*_belowX` (WfT2X3) with the root conclusion; the root
hypotheses (`hRD`, `hposN`, `hposM`, `hWle`) are those of `t2_sv_main`・`t2_qr_main`・`t2_qn_main`.
-/
import Ytosk.WfT2R3

namespace Ytosk.WfT2X

open T Classical Ytosk.WfAbsW

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

'''
open(D+'WfT2R4.lean','w').write(H+A+'\n'+sv+'\n'+qr+'\n'+qn+'\nend Ytosk.WfT2X\n')
