import re
D='/home/koteitan/proofs/trio/Ytosk/lean/Ytosk/'
X4=open(D+'WfT2X4.lean').read()
s=X4.index('theorem t2BelowXS_ofX'); e=X4.index('\n/-- **`T2BelowXAll`',s)
T=X4[s:e].rstrip()+'\n'
T=T.replace('theorem t2BelowXS_ofX','theorem t2_root_ofX')
G='(TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r)'
T=T.replace('    T2BelowXSX M ρ r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) := by',
f'''    ∀ n, 2 ≤ n → (∀ m, 1 ≤ m → m < n → ∀ τ, Cons {G} m) τ → Good3 {G} m) τ) →
      ∀ σ, Cons {G} n) σ →
      (∀ j, r + L ≤ j → j < {G} n).length → isOT (σ.o j) = true ∧ isOT (σ.v j) = true) →
      Good3 {G} n) σ →
      isOT (root {G} n) σ) = true ∧ root {G} n) σ < root M ρ := by''')
T=T.replace('  intro n hn hGP σ hCN hOTx\n','  intro n hn hGP σ hCN hOTx hGN\n')
L=T.split('\n'); out=[]; i=0
while i<len(L):
    l=L[i]
    m=re.match(r'(\s*)have hbx := (t2_\w+)_belowX(.*)',l)
    if m:
        out.append(f'{m.group(1)}exact {m.group(2)}_rootX{m.group(3)}')
        i+=1
        while not L[i].strip().startswith('intro i hi'):
            out.append(L[i]); i+=1
        out[-1]=out[-1]+' hGN'
        ind=len(L[i])-len(L[i].lstrip())
        i+=1
        while i<len(L) and (L[i].strip()=='' or len(L[i])-len(L[i].lstrip())>=ind):
            i+=1
        continue
    out.append(l); i+=1
T='\n'.join(out)
H='''/-
**WfT2R5: the root descent of every `M[n]` (`n ≥ 2`, `t = 2`) from `T2BelowXResAtX` (2026-11-01).**

`t2_root_ofX`: the proof of `t2BelowXS_ofX` (WfT2X4) with the root engines of WfT2R4 in place of the `below` ones.
-/
import Ytosk.WfT2R4

namespace Ytosk.WfT2X

open T Classical Ytosk.WfAbsW

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

'''
open(D+'WfT2R5.lean','w').write(H+T+'\n\nend Ytosk.WfT2X\n')
