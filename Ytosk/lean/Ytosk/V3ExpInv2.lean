/-
Closure preservation for one t = 1 copy, using the redesigned invariant.
PH3cG and FC3 need only structure, consistency, goodness and rank.
TP1C and TP1WC follow from PH3cG once their leaf obligations are supplied.
-/
import Ytosk.V3Inv2
import Ytosk.V3PT1G
import Ytosk.V3TP1CutG
import Ytosk.V3ExpT1A
import Ytosk.V3ExpT1V

namespace Ytosk

open T

/-- The two closure fields survive each copy without the false old fields. -/
theorem expStep_closure_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1 (fun N σ => PH3cG N σ ∧ FC3 N σ) M r L d0 ρ := by
  have hp := G.expStep_ph3c_t1S S I.cons I.good I.rank I.ph hlen hL hd0e h1 hx2
  have hf := G.expStep_fc3_t1S S I.cons I.good I.rank I.fc3 hlen hL hd0e h1 hx2
  intro n hn ρP Z hCP hGP hPP hCN hGN ho hv hle hlex hH
  exact ⟨hp n hn ρP Z hCP hGP hPP.1 hCN hGN ho hv hle hlex hH,
    hf n hn ρP Z hCP hGP hPP.2 hCN hGN ho hv hle hlex hH⟩

/-- The already proved value fields transported at a t = 1 copy.
The seed-local fields, absorption, VSmallF and VSmallRAll are still separate. -/
structure CopyCoreV2 (N : Mat) (σ : Valn) : Prop where
  cons : Cons N σ
  good : Good3 N σ
  fc : FrameClosed N σ
  fo : FrameOT N σ
  kd : BumpKidsDec N σ
  td : BumpTermDec N σ
  ph : PH3cG N σ
  fc3 : FC3 N σ
  rootS : ∀ i ∈ roots N, Single (σ.o i)
  rootP : RootP N σ

/-- Extract the part of Inv3V2 whose one-copy preservation is proved. -/
theorem Inv3V2.copyCore {N : Mat} {σ : Valn} {rk : Bool → Nat → Nat}
    (I : Inv3V2 N σ rk) : CopyCoreV2 N σ :=
  ⟨I.cons, I.good, I.fc, I.fo, I.kd, I.td, I.ph, I.fc3, I.rootS, I.rootP⟩

/-- Ten fields of Inv3V2 survive each t = 1 copy, using only the chain's
usual step premises. No old global absorption or trigger is assumed. -/
theorem expStep_core_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1 CopyCoreV2 M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hfc := expStep_frameClosed_t1S S I.cons I.good I.rank I.fc hlen hL hd0e h1 hx2
  have hfo := expStep_frameOT_t1 hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2 hq I.fo
  have hbd := expStep_bumpDec_t1 hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2 hq
    I.good ⟨I.kd, I.td⟩
  have hrp := expStep_rootP_t1 hlen hL hd0e S.z2 S.uat S.r12 S.bumpE2 S.r01 S.e00 h1 hx2 I.rootP
  have hcl := expStep_closure_inv3V2 S I hlen hL hd0e h1 hx2
  intro n hn ρP Z hCP hGP hPP hCN hGN ho hv hle hlex hH
  have hfcN := hfc n hn ρP Z hCP hGP hPP.fc hCN hGN ho hv hle hlex hH
  have hfoN := hfo n hn ρP Z hCP hGP hPP.fo hCN hGN ho hv hle hlex hH
  obtain ⟨hkdN, htdN⟩ := hbd n hn ρP Z hCP hGP ⟨hPP.kd, hPP.td⟩ hCN hGN ho hv hle hlex hH
  have hrpN := hrp n hn ρP Z hCP hGP hPP.rootP hCN hGN ho hv hle hlex hH
  obtain ⟨hphN, hfc3N⟩ := hcl n hn ρP Z hCP hGP ⟨hPP.ph, hPP.fc3⟩ hCN hGN ho hv hle hlex hH
  exact ⟨hCN, hGN, hfcN, hfoN, hkdN, htdN, hphN, hfc3N, rootS_of_good hCN hGN, hrpN⟩

/-- VSmallF is transported once the last-summand component residual is
supplied. The unchanged initial summands do not contribute components. -/
theorem expStep_vsmallF_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hRes : VSFRes2 M r L d0 ρ) :
    ExpStepT1 (fun N σ => VrLe r ρ N σ ∧ VSmallF N σ) M r L d0 ρ :=
  expStep_vsmallFS S I.cons I.good I.rank I.vs hlen hL hd0e h1 hx2
    (vsfRes_of_values I.cons I.good I.rank hRes)

/-- The proved core and VSmallF are carried together. The sole extra
residual here concerns components of changed last summands. -/
theorem expStep_core_vsmallF_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hRes : VSFRes2 M r L d0 ρ) :
    ExpStepT1 (fun N σ => CopyCoreV2 N σ ∧ VrLe r ρ N σ ∧ VSmallF N σ) M r L d0 ρ :=
  expStep_and (expStep_core_inv3V2 S I hlen hL hd0e h1 hx2)
    (expStep_vsmallF_inv3V2 S I hlen hL hd0e h1 hx2 hRes)

/-- The unchanged, true value fields needed by the VSmallF producer. -/
theorem Inv3V2.valInv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (I : Inv3V2 M ρ rk) : ValInv M ρ :=
  ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩

/-- VSmallF with only the passing-root ordering residual, rather than a
component bound at every new valuation and every chain index. -/
theorem expStep_vsmallF_pass_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hPR : PassRootRes M r L ρ) :
    ExpStepT1 (fun N σ => VrLe r ρ N σ ∧ VSmallF N σ) M r L d0 ρ :=
  expStep_vsmallF2S S I.cons I.rank I.valInv hlen hL hd0e h1 hx2 hPR

/-- The eleven proved value fields, together with the bound on v(r) used
when the next copy is attached. PassRootRes itself is still a premise. -/
theorem expStep_core_vsmallF_pass_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hPR : PassRootRes M r L ρ) :
    ExpStepT1 (fun N σ => CopyCoreV2 N σ ∧ VrLe r ρ N σ ∧ VSmallF N σ) M r L d0 ρ :=
  expStep_and (expStep_core_inv3V2 S I hlen hL hd0e h1 hx2)
    (expStep_vsmallF_pass_inv3V2 S I hlen hL hd0e h1 hx2 hPR)

/-- The drop supplies the bound on v(r) needed to start the VSmallF carry. -/
theorem vrle_prefix_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length)
    (h1 : par M 1 (r + L) = some r)
    (R : DropRes M (r + L) ρ (drop1 M (r + L) rk))
    (I1 : Inv3V2 (M.take (r + L)) (drop1 M (r + L) rk) rk) :
    VrLe r ρ (M.take (r + L)) (drop1 M (r + L) rk) := by
  have hrx : r < r + L := par_lt M 1 _ r h1
  have hdrop := drop_all hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good I1.cons I1.rank
    I.vs R.vst I.fc I.fo R.argT
    (bump_drop hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good I1.cons I1.rank
      I.kd I.td R.ab R.ws) R.ua
  rcases (hdrop r hrx).2.1 with h | ⟨h, _⟩
  · exact h.le
  · exact (le_iff _ _).mpr (Or.inl h.1)

/-- Leaf obligations left in the t = 1 TP1 producer. They concern the new
valuation, rather than any old global trigger or absorption predicate. -/
def T1LeavesV2 (M : Mat) (r L d0 : Nat) : Prop :=
  ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L d0 0 n) σ →
    Good3 (TRIO.gexp M r L d0 0 n) σ →
    TP1LeafG (TRIO.gexp M r L d0 0 n) σ ∧ TP1WLeafG (TRIO.gexp M r L d0 0 n) σ

/-- Once the two leaf obligations hold, PH3cG supplies TP1C and TP1WC
at every new copy. TrigOmC and TrigCutG are not premises. -/
theorem expStep_tp1_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hLeaves : T1LeavesV2 M r L d0) :
    ExpStepT1 (fun N σ => PH3cG N σ ∧ FC3 N σ ∧ TP1C N σ ∧ TP1WC N σ) M r L d0 ρ := by
  have hstep := expStep_closure_inv3V2 S I hlen hL hd0e h1 hx2
  intro n hn ρP Z hCP hGP hPP hCN hGN ho hv hle hlex hH
  obtain ⟨hp, hf⟩ := hstep n hn ρP Z hCP hGP ⟨hPP.1, hPP.2.1⟩ hCN hGN ho hv hle hlex hH
  obtain ⟨hLeaf, hWLeaf⟩ := hLeaves n hn _ hCN hGN
  exact ⟨hp, hf, tp1C_of_ph3cG hCN ⟨hGN.ot_o, hGN.ot_v⟩ hp hLeaf,
    tp1WC_of_ph3cG hCN ⟨hGN.ot_o, hGN.ot_v⟩ hp hWLeaf⟩

/-- The non-equal t = 1 branch carries the proved core and decreases the
root without assuming a separate one-copy preservation theorem. The drop
and the prefix invariant remain premises. -/
theorem qn_core_final_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L d0 : Nat}
    (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (S : SInv M) (I : Inv3V2 M ρ rk)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hqr : par M 0 (r + L) ≠ some r)
    (R : DropRes M (r + L) ρ (drop1 M (r + L) rk))
    (I1 : Inv3V2 (M.take (r + L)) (drop1 M (r + L) rk) rk)
    : ∀ n, 2 ≤ n → ∃ ρN, CopyCoreV2 (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧
      root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hrM : r < M.length := by omega
  obtain ⟨br, hro⟩ := o_psi_sub I.cons hrM
  rw [sf_ot (I.good.ot_v r hrM)] at hro
  have hdrop := drop_all hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good I1.cons I1.rank
    I.vs R.vst I.fc I.fo R.argT
    (bump_drop hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good I1.cons I1.rank
      I.kd I.td R.ab R.ws) R.ua
  have hne : (drop1 M (r + L) rk).o r ≠ ρ.o r :=
    ne_of_lt (o_r_strict0 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2
      h1 hx2 hqr I.cons I.good I1.cons I1.rank hdrop)
  intro n hn
  obtain ⟨ρN, _, _, _, _, IN, hot, hlt⟩ :=
    t1_main_vlocS hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
      h1 hx2 hqr I.cons I.good I.rank I.vs I.fc I.fo I.tp1 I.tplos I.ads I.aus R.argT
      I.kd I.td R.ab R.ws R.vst R.ua hne rfl hro I.rootS I.rootP I1.good
      CopyCoreV2 I1.copyCore (expStep_core_inv3V2 S I hlen hL hd0e h1 hx2) n hn
  exact ⟨ρN, IN, hot, hlt⟩


/-- The equal t = 1 branch also carries the proved core without a
separate step assumption. The drop, prefix, and seed component residual
remain explicit. -/
theorem qr_core_final_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L d0 : Nat}
    (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (S : SInv M) (I : Inv3V2 M ρ rk)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hq : par M 0 (r + L) = some r) (hNB : ¬ Bad2 M)
    (R : DropRes M (r + L) ρ (drop1 M (r + L) rk))
    (I1 : Inv3V2 (M.take (r + L)) (drop1 M (r + L) rk) rk)
    : ∀ n, 2 ≤ n → ∃ ρN, CopyCoreV2 (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧
      root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  intro n hn
  obtain ⟨ρN, _, _, _, _, IN, hot, hlt⟩ :=
    qr_final4S hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
      h1 hx2 hq I.cons I.good I.rank I.vs I.fc I.fo R.argT I.kd I.td R.ab R.ws R.vst R.ua
      I.tp1w (I.tplowAt hlen h1) I.auwl I.auw0 (I.adwAt hlen h1) I.tp1 I.trigs I.tplon I.adn I.rootS I.rootP
      CopyCoreV2 I1.copyCore (expStep_core_inv3V2 S I hlen hL hd0e h1 hx2) n hn
  exact ⟨ρN, IN, hot, hlt⟩

/-- The qn branch also carries VSmallF, with the fixed-matrix passing-root
residual as its only extra premise beyond the core branch. -/
theorem qn_vsmallF_final_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L d0 : Nat}
    (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (S : SInv M) (I : Inv3V2 M ρ rk)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hqr : par M 0 (r + L) ≠ some r)
    (R : DropRes M (r + L) ρ (drop1 M (r + L) rk))
    (I1 : Inv3V2 (M.take (r + L)) (drop1 M (r + L) rk) rk)
    (hPR : PassRootRes M r L ρ) : ∀ n, 2 ≤ n → ∃ ρN, CopyCoreV2 (TRIO.gexp M r L d0 0 n) ρN ∧
      VSmallF (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧
      root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hrM : r < M.length := by omega
  obtain ⟨br, hro⟩ := o_psi_sub I.cons hrM
  rw [sf_ot (I.good.ot_v r hrM)] at hro
  have hdrop := drop_all hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good I1.cons I1.rank
    I.vs R.vst I.fc I.fo R.argT
    (bump_drop hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good I1.cons I1.rank
      I.kd I.td R.ab R.ws) R.ua
  have hne : (drop1 M (r + L) rk).o r ≠ ρ.o r :=
    ne_of_lt (o_r_strict0 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2
      h1 hx2 hqr I.cons I.good I1.cons I1.rank hdrop)
  intro n hn
  obtain ⟨ρN, _, _, _, _, IN, hot, hlt⟩ :=
    t1_main_vlocS hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
      h1 hx2 hqr I.cons I.good I.rank I.vs I.fc I.fo I.tp1 I.tplos I.ads I.aus R.argT
      I.kd I.td R.ab R.ws R.vst R.ua hne rfl hro I.rootS I.rootP I1.good
      (fun N σ => CopyCoreV2 N σ ∧ VrLe r ρ N σ ∧ VSmallF N σ)
        ⟨I1.copyCore, vrle_prefix_inv3V2 S I hlen h1 R I1, I1.vs⟩
        (expStep_core_vsmallF_pass_inv3V2 S I hlen hL hd0e h1 hx2 hPR) n hn
  exact ⟨ρN, IN.1, IN.2.2, hot, hlt⟩

/-- The qr branch also carries VSmallF, with the fixed-matrix passing-root
residual as its only extra premise beyond the core branch. -/
theorem qr_vsmallF_final_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L d0 : Nat}
    (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (S : SInv M) (I : Inv3V2 M ρ rk)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hq : par M 0 (r + L) = some r) (hNB : ¬ Bad2 M)
    (R : DropRes M (r + L) ρ (drop1 M (r + L) rk))
    (I1 : Inv3V2 (M.take (r + L)) (drop1 M (r + L) rk) rk)
    (hPR : PassRootRes M r L ρ) : ∀ n, 2 ≤ n → ∃ ρN, CopyCoreV2 (TRIO.gexp M r L d0 0 n) ρN ∧
      VSmallF (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧
      root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  intro n hn
  obtain ⟨ρN, _, _, _, _, IN, hot, hlt⟩ :=
    qr_final4S hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
      h1 hx2 hq I.cons I.good I.rank I.vs I.fc I.fo R.argT I.kd I.td R.ab R.ws R.vst R.ua
      I.tp1w (I.tplowAt hlen h1) I.auwl I.auw0 (I.adwAt hlen h1) I.tp1 I.trigs I.tplon I.adn I.rootS I.rootP
      (fun N σ => CopyCoreV2 N σ ∧ VrLe r ρ N σ ∧ VSmallF N σ)
        ⟨I1.copyCore, vrle_prefix_inv3V2 S I hlen h1 R I1, I1.vs⟩
        (expStep_core_vsmallF_pass_inv3V2 S I hlen hL hd0e h1 hx2 hPR) n hn
  exact ⟨ρN, IN.1, IN.2.2, hot, hlt⟩

end Ytosk
