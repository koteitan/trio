from pathlib import Path
import re
D=Path('Ytosk/lean/Ytosk')
P=D/'V3SeedPF.lean'
assert not P.exists()
def extract(file,name,kind='theorem'):
 s=(D/(file+'.lean')).read_text();start=s.index(kind+' '+name+' ')
 m=re.search(r'\n(?:/--|theorem |end(?: |\n)|namespace )',s[start+1:])
 return s[start:start+1+m.start()].rstrip()+'\n' if m else s[start:]
header='''/- QPHs/QF3s seed producers on the consistent V3 context. -/
import Ytosk.V3SeedFOC2
import Ytosk.V3T2CopyV3

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

'''
qr=extract('V3T2SeedQRL','T2SeedQRRes','structure')
qr=qr[:qr.index('  vs :')]+qr[qr.index('  w1 :'):qr.index('  dom :')]
qn='''structure QNRel (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop where
  σB : sh (ρ.v r) (qnS M ρ r L q) (t2B (ρ.v r) ρ Lc) = t2B (ρ.v r) ρ Lc
  Bc : ∀ g ∈ summands (t2B (ρ.v r) ρ Lc), ¬ g < psi (succ (qnS M ρ r L q)) z z
  base : ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ∧
    ∀ k, ρ.v r < tqN (ρ.v r) (qnS M ρ r L q) t1 k ∧
      ¬ shf (ρ.v r) (qnS M ρ r L q) (tqN (ρ.v r) (qnS M ρ r L q) t1 k) < succ (qnS M ρ r L q)
'''
sv=extract('V3T2SeedSV','T2SeedSVRes','structure');sv=sv[0:sv.index('  decP :')]+sv[sv.index('  rw :'):sv.index('  lhd :')]
cr=extract('V3T2SeedC','T2SeedCRes','structure');cr=cr[:cr.index('  lhd :')]
header+=qr.replace('T2SeedQRRes','QRRel')+'\n'+qn+'\n'+sv.replace('T2SeedSVRes','SVRel')+'\n'+cr.replace('T2SeedCRes','CRel')+'\n'
# All copied proofs below either discard the old residual or use only prefix
# Good3/PO. Local proof names prevent accidental use of stronger old versions.
seq=[('V3T2SeedQR','o_r_level_qr'),('V3T2SeedQRL','seed_r_value_qr'),
 ('V3T2SeedQN','qn_frame'),('V3T2SeedQN','o_r_level_qn'),('V3T2SeedQNV','seed_r_value_qn'),
 ('V3T2SeedSV','sv_frame'),('V3T2SeedSV','o_r_level_sv'),('V3T2SeedSV','seed_r_value_sv'),
 ('V3T2SeedC','C_frame'),('V3T2SeedC','o_r_level_C'),('V3T2SeedC','seed_r_value_C'),
 ('V3PSeedQRG','seed_frame_data_qr'),('V3PSeedQNG','seed_frame_data_qn'),('V3PSeedSVG','seed_frame_data_sv'),
 ('V3QNFC','qn_take_t1'),('V3QNFC','t2SeedQNFC_holds'),('V3SVFix','t2SeedSVFix_holds'),('V3CFix','t2SeedCFix_of'),
 ('V3PSeedQRG','seed_frames_qr'),('V3PSeedQNG','seed_frames_qn'),('V3PSeedSVG','seed_frames_sv'),('V3PSeedCG','seed_frames_C')]
renames={name:name+'V3' for _,name in seq}
parts=[]
for file,name in seq:
 s=extract(file,name)
 s=s.replace('(R : Res3W M ρ rk)','(Ctx : StepCtx3 M ρ rk)').replace('I R ', 'I Ctx ')
 s=s.replace('t2CopyResAll_holds M ρ rk hM hS I Ctx','t2CopyResV3 hM hS I')
 s=s.replace('have hdrop := R.hdrop','have hdrop := (Ctx.drop (by omega)).1')
 old='have hG1 := good3_take hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop'
 new='''have J1 := Ctx.pre (M.length - 1) (by omega) (by omega)
  have hG1 := good3_congr J1.good (agree_of_cons J1.cons hC1 J1.rank)'''
 s=s.replace(old,new)
 # The removed final base conjunct was not consumed: existing callers extract
 # only its first two components.
 s=s.replace('(hch k).2.1','(hch k).2').replace('(hch (n - 2)).2.1','(hch (n - 2)).2')
 for a,b in renames.items():s=re.sub(r'\b'+a+r'\b',b,s)
 for a,b in [('T2SeedQRRes','QRRel'),('T2SeedQNRes','QNRel'),('T2SeedSVRes','SVRel'),('T2SeedCRes','CRel')]:s=s.replace(a,b)
 parts.append(s)
P.write_text(header+'\n'.join(parts)+'\nend Ytosk.V3Main.SeedPF\n')
