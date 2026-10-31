import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfT2R')
from gen import gen
copies=['pathLvAll_pre_t2','seed_C_data','t2SeedPreShapeC_of','vsmallRAll_expand_t2','t2VRAV2_of','t2VRASeed_of','t2SeedPreShapeSVC_of',
 't2VRASeedSVC_of','t2VRAPre_of','seed_lev_of','t2VRASeedC_of','source_v_base_nonseed','root_v_base_original',
 'source_v_base_live','source_v_base_pair','clField_expand_t2','frameOT_expand_t2','root_v_original',
 't2CopyK_FDshAt_of_path','t2FDCopyRes_of_path','bumpFields_expand_t2','hR2_t2','hR2_t2_ofW','rootP_expand_t2',
 'fc3_expand_t2','fc3_expand_t2S','ph3c_expand_t2','ph3c_expand_t2S','t2_val_expand','hExp_t2_inv3V2','expT2V2_of',
 'vsmallF_expand_t2','vsmallF_expand_t2V','clField_expand_t2SK','frameClosed_expand_t2K','t2VSFCV2_of','t2VSFCV2_of2',
 't2VRASeedG_of','r2V2_of']
ren=[(n,n+'XR') for n in copies]+[
 ('T2BelowXResAt','WfT2X.T2BelowXResAtX'),('T2BelowXResV2','WfT2X.T2BelowXResV2X'),
 ('t2BelowXS_of','WfT2X.t2BelowXS_ofX'),('t2BelowXE_of','WfT2X.t2BelowXE_ofX'),
 ('frame_of_shape','WfT2X.frame_of_shapeX'),('rw_frame_of_shape','WfT2X.rw_frame_of_shapeX'),
 ('pathLv_of_shape','pathLv_of_shapeXR'),('qVSF_of_shape','WfT2X.qVSF_of_shapeX'),
 ('clField_of_shape','WfT2X.clField_of_shapeX'),('clField_of_shapeS','WfT2X.clField_of_shapeSX'),('FrameShape','WfAbsW.FrameShapeX')]
opens={'V3FDCopyRoot.lean':'T FDCopy','V3PT2G.lean':'T','V3PSeedAllG.lean':'T','V3ExpT2V2.lean':'T','V3T2VSFC.lean':'T','V3T2SeedFrV2.lean':'T','V3FDCopy.lean':'T'}
H1=open('/home/koteitan/proofs/trio/tmp/wf/WfT2R/h1.lean').read()
H2=open('/home/koteitan/proofs/trio/tmp/wf/WfT2R/h2.lean').read()
H3=open('/home/koteitan/proofs/trio/tmp/wf/WfT2R/h3.lean').read()
f=lambda names: [ (fn,[n]) for fn,n in names]
g1=[('V3T2VRAPre.lean','pathLvAll_pre_t2'),('V3T2VRASV.lean','seed_C_data'),('V3T2VRASV.lean','t2SeedPreShapeC_of'),('V3T2VRA.lean','vsmallRAll_expand_t2'),
 ('V3T2VRA.lean','t2VRAV2_of'),('V3T2VRASeed.lean','t2VRASeed_of'),('V3T2VRASV.lean','t2SeedPreShapeSVC_of'),
 ('V3T2VRASV.lean','t2VRASeedSVC_of'),('V3T2VRAPre.lean','t2VRAPre_of'),('V3T2VRASV.lean','seed_lev_of'),
 ('V3T2VRASV.lean','t2VRASeedC_of'),('V3T2VRASeed.lean','t2VRASeedG_of')]
g2=[('V3FDCopy.lean','source_v_base_nonseed'),('V3FDCopy.lean','root_v_base_original'),('V3FDCopy.lean','source_v_base_live'),
 ('V3FDCopy.lean','source_v_base_pair'),('V3ExpT2FO.lean','clField_expand_t2'),('V3ExpT2FO.lean','frameOT_expand_t2'),
 ('V3FDCopyRoot.lean','root_v_original'),('V3FDCopyRoot.lean','t2CopyK_FDshAt_of_path'),('V3FDCopyRoot.lean','t2FDCopyRes_of_path')]
g3=[('V3ExpT2BD.lean','bumpFields_expand_t2'),('V3ExpT2RP.lean','rootP_expand_t2'),
 ('V3PT2G.lean','fc3_expand_t2'),('V3PSeedAllG.lean','fc3_expand_t2S'),('V3PT2G.lean','ph3c_expand_t2'),('V3PSeedAllG.lean','ph3c_expand_t2S'),
 ('V3ExpT2Inv2.lean','t2_val_expand'),
 ('V3T2VSF.lean','vsmallF_expand_t2'),('V3T2VSF.lean','vsmallF_expand_t2V'),('V3RwClCopy.lean','clField_expand_t2SK'),
 ('V3T2VSFC.lean','frameClosed_expand_t2K'),('V3T2VSFC.lean','t2VSFCV2_of'),('V3T2SeedFrV2.lean','t2VSFCV2_of2')]
which=sys.argv[1]
if which=='1': gen('WfT2R1.lean',H1,f(g1),ren,opens)
if which=='2': gen('WfT2R2.lean',H2,f(g2),ren,opens)
if which=='3': gen('WfT2R3.lean',H3,f(g3),ren,opens)

import re
PATCH={'1':[
("""                rcases hshp with ⟨hv, _, _⟩ | ⟨hv, _⟩ | ⟨hN, _⟩
                · exact hv
                · exact hv
                · rw [hN] at hCL; simp at hCL""",
"""                rcases hshp with (⟨hv, _, _⟩ | ⟨hv, _⟩ | ⟨hN, _⟩) | ⟨hv, _⟩
                · exact hv
                · exact hv
                · rw [hN] at hCL; simp at hCL
                · exact hv"""),
("""              (fun a Lv cv cv' h1 h2 h3 h4 h5 => qVRAt_low a Lv cv cv' u h1 h2 h3 h4 h5)
              I.cons""","""              (fun a Lv cv cv' h1 h2 h3 h4 h5 => qVRAt_low a Lv cv cv' u h1 h2 h3 h4 h5)
              (WfT2X.qVRAt_lowV u) I.cons"""),
]
,'2':[
("""  rcases hsh with ⟨hv, _, _⟩ | ⟨hv, _⟩ | ⟨_, hnil⟩
  · exact hv.trans hvi.symm
  · exact hv.trans hvi.symm
  · rw [hnil] at hci
    simp at hci
""","""  rcases hsh with (⟨hv, _, _⟩ | ⟨hv, _⟩ | ⟨_, hnil⟩) | ⟨hv, _⟩
  · exact hv.trans hvi.symm
  · exact hv.trans hvi.symm
  · rw [hnil] at hci
    simp at hci
  · exact hv.trans hvi.symm
"""),
("""    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → Q a Lv cv')
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk) (hM : Std M) (hS : M ≠ SRO)""",
"""    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → Q a Lv cv')
    (hQlowV : ∀ a Lv s s', Q a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) → isOT (psi s' z z) = true →
      Q a Lv (psi s' z z))
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk) (hM : Std M) (hS : M ≠ SRO)"""),
("""            exact WfT2X.clField_of_shapeX hQlow hsh (fun""","""            exact WfT2X.clField_of_shapeX hQlow hQlowV hsh
              (fun d hd => hGN.ot_o d (mem_children (cl_mem_children hd)).2) (fun"""),
("""  clField_expand_t2XR qFO_sh (fun _ _ _ _ h _ _ => h) hB""","""  clField_expand_t2XR qFO_sh (fun _ _ _ _ h _ _ => h) WfT2X.qFO_lowV hB"""),
]
,'3':[
("qT2F_low hB","qT2F_low qT2F_lowVXR hB"),("qT2P_low hB","qT2P_low qT2P_lowVXR hB"),
("""      (∀ s y s' y', cv = psi s y z → cv' = psi s' y' z → s' ≠ s → y' = z) → Q a Lv cv')
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk) (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hQM : CLField Q M ρ)
    (hQT : ∀ τ, Cons (M.take (M.length - 1)) τ → CLField Q (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames Q M) (hKM""","""      (∀ s y s' y', cv = psi s y z → cv' = psi s' y' z → s' ≠ s → y' = z) → Q a Lv cv')
    (hQlowV : ∀ a Lv s s', Q a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) → isOT (psi s' z z) = true →
      Q a Lv (psi s' z z))
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk) (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hQM : CLField Q M ρ)
    (hQT : ∀ τ, Cons (M.take (M.length - 1)) τ → CLField Q (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames Q M) (hKM"""),
("WfT2X.clField_of_shapeSX hQlow I.cons","WfT2X.clField_of_shapeSX hQlow hQlowV I.cons"),
("qFCo_low hB","qFCo_low WfT2X.qFCo_lowV hB"),
]}
fn={'1':'WfT2R1.lean','2':'WfT2R2.lean','3':'WfT2R3.lean'}[which]
P='/home/koteitan/proofs/trio/Ytosk/lean/Ytosk/'+fn
t=open(P).read()
for a,b in PATCH.get(which,[]):
    assert a in t, a[:80]
    t=t.replace(a,b)
open(P,'w').write(t)
