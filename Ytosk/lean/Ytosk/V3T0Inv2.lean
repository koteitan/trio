/-
**3 行・t = 0 の展開を Inv3V2 に接続する（2026-10-16、t0）。**

`t0_final_inv3V2`: M の SInv・Inv3V2、1 列落としの残り DropRes・AbsSR、落とした行列の Inv3V2 から、
N = M[n]（n ≥ 2）の Inv3V2・根の標準性・根の下降を組み立てる。旧 Inv3（偽の欄を含む）は使わない（V3T0C の Inv3C）。

- Cons・Good3・Rk・FrameClosed・FrameOT・BumpKidsDec・BumpTermDec・rootP・下降: t0_core。
- VSmallF: t0_vsmallF_atC（D の部分は T0DF から、M の VSmallRP は M の VSmallRAll から）。
- PH3cG・FC3: G.ph3c_N_t0・G.fc3_N_t0（M と M.take x の PH3cG・FC3、側条件は t0_core と同じ式で出す）。
- TP1C・TP1WC: N の PH3cG と葉の条件 TP1LeafG・TP1WLeafG から。
- VSmallRAll: vsmallRAll_N_t0（V3T0VSRAllN、M の VSmallRAll から、残りなし）。
- 名前つきの残り: 切り口 T0CutResGGC、N の葉の条件、N の最後の列の枠の 10 欄（TakeFrameV2 N）。
-/
import Ytosk.V3T0C
import Ytosk.V3T0VSRA
import Ytosk.V3TakeInv2
import Ytosk.V3PT0G
import Ytosk.V3ResV2
import Ytosk.V3T0VSRAllN

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- `Inv3V2` with the structural invariants gives the core bundle of the `t = 0` engine. -/
theorem Inv3V2.toC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V2 M ρ rk) :
    Inv3C M ρ rk :=
  ⟨S.r0p, S.z2, S.sibDec, S.z1c, S.uat, S.uab, S.r12, S.bumpE2, S.r01, S.e00, I.cons, I.good, I.rank,
    I.vs, I.fc, I.fo, I.kd, I.td, I.rootS, I.rootP⟩

/-- **The cut residual with the G3 cut** (`T0CutResGG`) with the core bundles in place of the old `Inv3`. -/
def T0CutResGGC : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3C M ρ rk →
    Res3C M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z →
      (split y (psi (succ s) z z)).2 = z →
      spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ≠ z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      ∀ P a x T', y = app P (psi a x z) → y' = app P T' →
      ∀ κ ∈ cutsNSG s (psi a x z), spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = app P κ → κ < T'


/-- **`T0DF` from the core bundles**, `PH3cG` and `VSmallRA` of `M` (as `t0DF_ofU`). -/
theorem t0DF_ofC (hCut : T0CutResGGC) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M)
    (hS : M ≠ SRO) (I : Inv3C M ρ rk) (R : Res3C M ρ rk) (hab : AbsSR M ρ) (hPH : PH3cG M ρ) (hVA : VSmallRA M ρ) :
    T0DF M ρ := by
  intro r L hlen hL hp he1 n hn σ hCN
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hab0 := hab r (by rw [show M.length - 1 = r + L by omega]; exact hp)
    (by rw [show M.length - 1 = r + L by omega]; exact he1)
  have h := t0_otdU hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab hab0 hDr.ws hDr.vst hDr.ua I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    (hVA.toP (r + L) r) hPH (hCut M ρ rk r L hM hS I R hlen hL hp he1)
    (t0_shape3C hM hS I R hlen hL hp he1) (t0IVResC_holds M ρ rk r L hM hS I R hlen hL hp he1) n hn σ hCN
  intro i hi
  refine ⟨fun hd => ?_, (h i hi).2⟩
  obtain ⟨h1, h2, _, h4, h5⟩ := (h i hi).1 hd
  exact ⟨h1, h2, trivial, h4, h5⟩

/-- **`t = 0`, `n ≥ 2`: Inv3V2 of `N = M[n]`** from `T0DF M ρ` (the `D` induction's output), the standard root value and its descent.
Named residuals: the cut `T0CutResGGC`, and for `N` the leaves `TP1LeafG`・`TP1WLeafG`
and the ten last-column frame fields (`TakeFrameV2 N`). -/
theorem t0_final_inv3V2D {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (hM : Std M) (hS : M ≠ SRO) (S : SInv M) (I : Inv3V2 M ρ rk)
    (hlen : r + L + 1 = M.length) (hL : 0 < L) (hp : par M 0 (r + L) = some r)
    (he1 : entry M 1 (r + L) = 0)
    (R : DropRes M (M.length - 1) ρ (drop1 M (M.length - 1) rk)) (hAbW : T0AbsW M r L ρ)
    (I1 : Inv3V2 (M.take (r + L)) (drop1 M (r + L) rk) rk)
    (hDF : T0DF M ρ)
    (hLeaf : ∀ n, 2 ≤ n → ∀ σ rkN, Cons (TRIO.gexp M r L 0 0 n) σ → Rk (TRIO.gexp M r L 0 0 n) rkN →
      Good3 (TRIO.gexp M r L 0 0 n) σ →
      TP1LeafG (TRIO.gexp M r L 0 0 n) σ ∧ TP1WLeafG (TRIO.gexp M r L 0 0 n) σ)
    (hFrm : ∀ n, 2 ≤ n → ∀ σ rkN, Cons (TRIO.gexp M r L 0 0 n) σ → Rk (TRIO.gexp M r L 0 0 n) rkN →
      Good3 (TRIO.gexp M r L 0 0 n) σ → TakeFrameV2 (TRIO.gexp M r L 0 0 n) σ rkN) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (TRIO.gexp M r L 0 0 n) ρN rkN ∧
      isOT (root (TRIO.gexp M r L 0 0 n) ρN) = true ∧ root (TRIO.gexp M r L 0 0 n) ρN < root M ρ := by
  intro n hn2
  have hn : 1 ≤ n := by omega
  have IC := I.toC S
  have RC : Res3C M ρ rk := ⟨R⟩
  have hx : r + L + 1 = M.length := hlen
  have hDr := R
  rw [show M.length - 1 = r + L by omega] at hDr
  have hx2 : entry M 2 (r + L) = 0 := S.r12 _ he1
  obtain ⟨σ, rkN, hCN, hRN, hGN, hFON, hFCN, hKDN, hTDN, _, hpN, hot, hlt⟩ :=
    t0_core hlen hL S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00 hp he1 I.cons I.good
      I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab hAbW hDr.ws hDr.vst hDr.ua I.rootS I.rootP
      (fun n hn g hg hc => counted_last0 hlen hL hp he1 S.r0p S.z2 S.sibDec S.z1c S.uab S.r12 hn hg hc)
      (fun n hn σ hCN => ⟨fun i hi hd => ((hDF r L hlen hL hp he1 n hn σ hCN i hi).1 hd).1,
        t0_vsmallNewN hlen hL hp he1 S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 I.cons I.good I.rank hn hCN⟩)
      n hn2
  have hctx : T0CtxC M ρ rk r L n σ rkN :=
    ⟨hM, hS, IC, RC, hlen, hL, hp, he1, trivial, hn2, hCN, hRN, hGN, hFON, hFCN, hKDN, hTDN⟩
  have hvs := t0_vsmallF_atC (t0VSD_atC hDF.toH) t0IVResC_holds r L n σ rkN hctx
  -- the side facts of the frames of `N` (as in `t0_core`)
  have hcnt := hcnt_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  set ρ' := drop1 M (r + L) rk with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hdrop := drop_all (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.vs hDr.vst
    I.fc I.fo hDr.argT
    (bump_drop (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.kd I.td hDr.ab hDr.ws)
    hDr.ua
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hnx : ¬ DepX M (r + L) false (r + L) := not_depX_v_x he1
  have hD := dep_strict0 (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 hdrop hx2 hp hnx
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hvC := t0_vals hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp S.r0p S.z2 S.sibDec S.z1c S.uat S.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp S.r0p S.z2 S.sibDec S.z1c S.uat S.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i) := by
    intro i hi
    have h := hvD i (by rw [hlN]; omega)
    exact ⟨fun hd => by rw [h.1 (fun h' => hd h'.2), tau_o_lt hi],
      fun hd => by rw [h.2 (fun h' => hd h'.2), tau_v_lt hi]⟩
  have hσB : ∀ i, r ≤ i → i < N.length → σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧
      σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i :=
    fun i hri hiN => ⟨(hvC i hiN).1 (fun h => by omega), (hvC i hiN).2 (fun h => by omega)⟩
  have hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ := by
    intro k hk
    have : k * L + L ≤ n * L := by
      have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
    rw [(hσB _ (by omega) (by rw [hlN]; omega)).1]
    exact tau_o_root hk hL
  have hσlast : σ.o (r + (n - 1) * L) = ρ'.o r := by
    have hnl : (n - 1) * L + L = n * L := by rw [← Nat.succ_mul]; congr 1; omega
    rw [(hσB _ (by omega) (by rw [hlN]; omega)).1]
    have := tau_o_last (r := r) (L := L) (n := n) (ρ := ρ) (ρ' := ρ') (oMid := omid M r L ρ) hL
    rwa [Nat.add_zero, Nat.add_zero] at this
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 hx2 hn2 I.cons I.good
  have hlt0 : ρ'.o r < ρ.o r :=
    hD true r (depLike_r hlen hL hp hx2 (depLike_depX M (r + L))) (by omega)
  have hO'le : ρ'.o r ≤ omid M r L ρ := by
    obtain ⟨_, s', y', hs'⟩ := (hdrop r (by omega)).1.2
    have h := hlt0
    rw [hs', hor] at h
    rw [hs', hom]
    rcases psi_lt_psi_z_iff.mp h with h1 | ⟨rfl, h2⟩
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h1))
    · exact psi_le_psi_arg ((lt_succ_iff (x := _)).mp h2)
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z := by
    intro s' y' hs hne
    obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
    rw [hs] at hy0; simp only [psi.injEq] at hy0
    have hv'ot := (hdrop r (by omega)).2.2
    rw [sf_ot hv'ot] at hy0
    have hCv : ChgX M (r + L) false r := by
      by_contra hn'; apply hne; rw [hy0.1]; exact (hoff r (by omega)).2 hn'
    have hT := (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hCv).1 rfl (by omega)
    have ho := o_of_no_counted hC1 hrT hv'ot hT.2.1
    rw [hs] at ho; simp only [psi.injEq] at ho; exact ho.2.1
  have hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d := fun d hd hdd =>
    le_of_lt ((hDF r L hlen hL hp he1 n hn2 σ hCN d hd).1 hdd).2.1.1
  have hss : ∀ d, d < r → σ.v d ≠ ρ.v d → σ.o d = psi (σ.v d) z z := by
    intro d hd hne
    have hdv : DepX M (r + L) false d := by
      by_contra hn'; exact hne ((hoffD d hd).2 hn')
    exact ((hDF r L hlen hL hp he1 n hn2 σ hCN d hd).1 (DepX.ov hdv)).2.2.2.1 hne
  have hLastN : ∀ g, par M 0 r = some g → Counted M g r → Counted N g (r + (n - 1) * L) :=
    fun g hg hc => counted_last0 hlen hL hp he1 S.r0p S.z2 S.sibDec S.z1c S.uab S.r12 hn2 hg hc
  have hph : PH3cG N σ := G.ph3c_N_t0 hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 hx2 hn2
    I.cons I.good hCN hGN.toOT I.ph I1.ph hσB hoffD hσmid hσlast hLastN hC1 I1.good (le_of_lt hlt0) hO'le
    hy' hdl hss
  have hfc3 : FC3 N σ := G.fc3_N_t0 hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 hx2 hn2
    I.cons I.good hCN hGN.toOT I.fc3 I1.fc3 hσB hoffD hσmid hσlast hLastN hC1 I1.good (le_of_lt hlt0) hO'le
    hy' hdl hss
  have hvra : VSmallRAll N σ := vsmallRAll_N_t0 hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 hx2 hn2
    I.cons I.good hCN hGN.toOT hC1 hRk1 I1.good hdrop hσB hoffD hσmid hσlast hLastN hO'le hy' hdl hss I.vra
  obtain ⟨hTP, hTPW⟩ := hLeaf n hn2 σ rkN hCN hRN hGN
  have F := hFrm n hn2 σ rkN hCN hRN hGN
  exact ⟨σ, rkN, ⟨hCN, hGN, hRN, hvs, hFCN, hFON, hKDN, hTDN, hph, hfc3, hvra,
    F.ads, F.aus, tp1C_of_ph3cG hCN hGN.toOT hph hTP, F.tplos, tp1WC_of_ph3cG hCN hGN.toOT hph hTPW,
    F.tplow, F.auwl, F.auw0, F.adw, F.trigs, F.tplon, F.adn, rootS_of_good hCN hGN, hpN⟩, hot, hlt⟩

/-- **`t = 0`, `n ≥ 2`: Inv3V2 of `N = M[n]`**, the standard root value and its descent.
Named residuals: the cut `T0CutResGGC`, and for `N` the leaves `TP1LeafG`・`TP1WLeafG`
and the ten last-column frame fields (`TakeFrameV2 N`). -/
theorem t0_final_inv3V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (hM : Std M) (hS : M ≠ SRO) (S : SInv M) (I : Inv3V2 M ρ rk)
    (hlen : r + L + 1 = M.length) (hL : 0 < L) (hp : par M 0 (r + L) = some r)
    (he1 : entry M 1 (r + L) = 0)
    (R : DropRes M (M.length - 1) ρ (drop1 M (M.length - 1) rk)) (hab : AbsSR M ρ)
    (I1 : Inv3V2 (M.take (r + L)) (drop1 M (r + L) rk) rk)
    (hCut : T0CutResGGC)
    (hLeaf : ∀ n, 2 ≤ n → ∀ σ rkN, Cons (TRIO.gexp M r L 0 0 n) σ → Rk (TRIO.gexp M r L 0 0 n) rkN →
      Good3 (TRIO.gexp M r L 0 0 n) σ →
      TP1LeafG (TRIO.gexp M r L 0 0 n) σ ∧ TP1WLeafG (TRIO.gexp M r L 0 0 n) σ)
    (hFrm : ∀ n, 2 ≤ n → ∀ σ rkN, Cons (TRIO.gexp M r L 0 0 n) σ → Rk (TRIO.gexp M r L 0 0 n) rkN →
      Good3 (TRIO.gexp M r L 0 0 n) σ → TakeFrameV2 (TRIO.gexp M r L 0 0 n) σ rkN) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (TRIO.gexp M r L 0 0 n) ρN rkN ∧
      isOT (root (TRIO.gexp M r L 0 0 n) ρN) = true ∧ root (TRIO.gexp M r L 0 0 n) ρN < root M ρ :=
  t0_final_inv3V2D hM hS S I hlen hL hp he1 R
    (T0AbsW.of_strong (hab r (by rw [show M.length - 1 = r + L by omega]; exact hp)
      (by rw [show M.length - 1 = r + L by omega]; exact he1))) I1
    (t0DF_ofC hCut hM hS (I.toC S) ⟨R⟩ hab I.ph I.vra.toLast) hLeaf hFrm

/-- `t0_shape` from the structural invariants. -/
theorem t0_shapeS {M : Mat} (S : SInv M)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (hs0 : TRIO.srow M (M.length - 1) = 0) :
    ∃ r L, r + L + 1 = M.length ∧ 0 < L ∧ par M 0 (r + L) = some r ∧ entry M 1 (r + L) = 0 ∧
      ∀ n, expand M n = TRIO.gexp M r L 0 0 n := by
  obtain ⟨r, hr⟩ := parLast_of S.e00 S.r01 S.r12 hz
  have hrx : r < M.length - 1 := par_lt M _ _ r hr
  rw [hs0] at hr
  have he1 : entry M 1 (M.length - 1) = 0 := by
    unfold TRIO.srow at hs0
    rw [← entry_eq, ← entry_eq] at hs0
    split_ifs at hs0 <;> omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hz
    rw [col_eq_entries, entry_eq, entry_eq, entry_eq, h0, h1, h2]
  refine ⟨r, M.length - 1 - r, by omega, by omega, by rw [show r + (M.length - 1 - r) = M.length - 1 by omega]; exact hr,
    by rw [show r + (M.length - 1 - r) = M.length - 1 by omega]; exact he1, fun n => ?_⟩
  exact expand_eq_gexp_t0 M n (by omega) hzT (by rw [hs0]; exact hr) hs0

/-- **A residual field `F` of `N = M[n]`** (`t = 0`, `n ≥ 2`) in top's step context, for a valuation of `N`
with `Cons`・`Rk`・`Good3`. -/
def T0NRes (F : Mat → Valn → (Bool → Nat → Nat) → Prop) : Prop :=
  ∀ M ρ rk r L, StepCtxV2 M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r →
    entry M 1 (r + L) = 0 → ∀ n, 2 ≤ n → ∀ σ rkN, Cons (TRIO.gexp M r L 0 0 n) σ →
      Rk (TRIO.gexp M r L 0 0 n) rkN → Good3 (TRIO.gexp M r L 0 0 n) σ → F (TRIO.gexp M r L 0 0 n) σ rkN

/-- **top's `ExpT0V2`** from the cut residual and the two residual fields of `N`. -/
theorem expT0V2_of2 (hCut : T0CutResGGC)
    (hLeaf : T0NRes (fun N σ _ => TP1LeafG N σ ∧ TP1WLeafG N σ)) (hFrm : T0NRes TakeFrameV2) :
    ExpT0V2 := by
  intro M ρ rk C hz hs0 n hn2
  obtain ⟨r, L, hlen, hL, hp, he1, hexp⟩ := t0_shapeS C.S hz hs0
  rw [hexp n]
  have hpre := (C.pre (r + L) (by omega) (by omega)).1
  obtain ⟨ρN, rkN, IN, _, _⟩ := t0_final_inv3V2 C.std C.ne C.S C.I hlen hL hp he1 C.R.drop C.R.abS hpre hCut
    (hLeaf M ρ rk r L C hlen hL hp he1) (hFrm M ρ rk r L C hlen hL hp he1)
    n hn2
  exact ⟨ρN, rkN, IN⟩

/-- The earlier interface of `expT0V2_of2` with the `VSmallRAll` residual of `N`, which is now proved
(`vsmallRAll_N_t0`) and not used. -/
theorem expT0V2_of (hCut : T0CutResGGC) (_hVRA : T0NRes (fun N σ _ => VSmallRAll N σ))
    (hLeaf : T0NRes (fun N σ _ => TP1LeafG N σ ∧ TP1WLeafG N σ)) (hFrm : T0NRes TakeFrameV2) :
    ExpT0V2 :=
  expT0V2_of2 hCut hLeaf hFrm

end Ytosk
