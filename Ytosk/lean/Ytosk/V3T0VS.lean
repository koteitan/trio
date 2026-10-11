/-
**3 行・t = 0: N = M[n] の VSmallF を、v が変わる子の枠だけに帰着。**

VSmallF は枠の性質（`QVS`）なので `frameQ_N_t0` で運ぶ。M・M.take x の枠は Inv3 から。r より前の D の子の枠は、
子の v が変わらなければ M の枠と同じ（数える子を持つ列の v は変わらない、状態 B も同じ）。g の枠は `g_frames_t0`。
残り（実測 C′ で例外 0、どちらも第 1 の選択肢 comps ≤ Ω_{v′} で成り立つ）:
- `T0VSResD`: r より前の枠で v が変わる子 c（15 万件）。
- `T0VSResG`: g の枠で M.take x の o′(r) の添字が変わる場合（1.2 万件、r は M.take x でも数えられる）。
-/
import Ytosk.V3ExpT0H
import Ytosk.V3T0Frm

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- `VSmallF` as a frame property. -/
def QVS (a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → ∀ g ∈ comps a s, g ≤ psi s z z ∨ g ≤ spArg a z (sumN Lv)

theorem qvs_of_vsmallF {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (h : VSmallF M ρ) :
    ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      QVS (ρ.v i) (Lc.map ρ.o) (ρ.o c) := by
  intro i hi Lc c R hCL s y hcv
  have hcM : c < M.length := (mem_children (cl_mem_children (show c ∈ CL M i by rw [hCL]; simp))).2
  have he := o_cl_eq hC hG hcM
  rw [hcv] at he; simp only [psi.injEq] at he
  rw [he.1]
  exact h i hi Lc c R hCL

theorem vsmallF_of_qvs {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
    (h : ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      QVS (ρ.v i) (Lc.map ρ.o) (ρ.o c)) : VSmallF M ρ := by
  intro i hi Lc c R hCL
  have hcM : c < M.length := (mem_children (cl_mem_children (show c ∈ CL M i by rw [hCL]; simp))).2
  exact h i hi Lc c R hCL _ _ (o_cl_eq hC hG hcM)

/-- **Residual (D)**: a counted child before `r` whose `v` changes in `N`. -/
def T0VSResD : Prop :=
  ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN →
    ∀ i (Lc : List Nat) c (R : List Nat), i < r → c < r → CL M i = Lc ++ c :: R → σ.v c ≠ ρ.v c →
      ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o))

/-- **Residual (G)**: at `g = P_0(r)` (with `r` counted), the subscript of `o′(r)` in `M.take x` changes. -/
def T0VSResG : Prop :=
  ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN →
    ∀ g, par M 0 r = some g → Counted M g r → ∀ Lc : List Nat, CL M g = Lc ++ [r] →
      (drop1 M (r + L) rk).v r ≠ ρ.v r →
      ∀ g' ∈ comps (ρ.v g) ((drop1 M (r + L) rk).v r),
        g' ≤ psi ((drop1 M (r + L) rk).v r) z z ∨ g' ≤ spArg (ρ.v g) z (sumN (Lc.map ρ.o))

/-- **`VSmallF` of `N = M[n]`** (`t = 0`) from the two residuals. -/
theorem t0_vsmallF (hD : T0VSResD) (hGr : T0VSResG) : T0Field VSmallF := by
  intro M ρ rk r L n σ rkN hctx
  obtain ⟨hM, hS, I, R, hlen, hL, hp, he1, _, hn2, hCN, hRN, hGN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  set ρ' := drop1 M (r + L) rk with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hVT : ValInv (M.take (r + L)) ρ' :=
    drop_pres hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hDr hC1 hRk1
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hvC := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
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
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good
  have hFO := qvs_of_vsmallF I.cons I.good I.vs
  have hFOT := qvs_of_vsmallF hC1 hVT.g hVT.vs
  apply vsmallF_of_qvs hCN hGN
  apply frameQ_N_t0 hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hGN.toOT QVS
    (ρ' := ρ') hFO hFOT hσB hoffD
  · -- the frame of `g` with `r` counted
    intro g hg hgc
    have hgr : g < r := par_lt M 0 r g hg
    have hrg : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
    have hσvg : σ.v g = ρ.v g := by
      apply (hoffD g hgr).2
      intro hdv
      exact uncnt_of_depv (show r + L + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp
        (by omega) hdv hrg hgc
    apply g_frames_t0 hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hGN.toOT QVS
      hg hgc (fun c hc hd => (hoffD c hc).1 hd) hσvg hσmid hσlast
      (counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn2 hg hgc)
      (fun Lc c R hCL => hFO g (by omega) Lc c R hCL)
    intro Lc j cv hCL hcv s y hsy g' hg'
    -- the state grows with the middle copies
    have hgM : g < M.length := by omega
    obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hgM
    rw [hCL] at hsM hpM
    simp only [List.map_append, List.map_singleton] at hsM hpM
    have hOr : omid M r L ρ < ρ.o r := by
      rw [hom, hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one _⟩)
    have hsO : Single (omid M r L ρ) :=
      ⟨isOT_omid hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN,
        by rw [hom]; exact ⟨_, _, rfl⟩⟩
    have hmono : spArg (ρ.v g) z (sumN (Lc.map ρ.o)) ≤
        spArg (ρ.v g) z (sumN (Lc.map ρ.o ++ List.replicate j (omid M r L ρ))) := by
      have hs : ∀ t ∈ Lc.map ρ.o ++ List.replicate j (omid M r L ρ), Single t := by
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact hsM t (List.mem_append_left _ ht)
        · rw [(List.mem_replicate.mp ht).2]; exact hsO
      have hpw : (Lc.map ρ.o ++ List.replicate j (omid M r L ρ)).Pairwise (fun a b => b ≤ a) := by
        have hp1 := List.pairwise_append.mp hpM
        refine List.pairwise_append.mpr ⟨hp1.1, List.pairwise_replicate.mpr (Or.inr (le_refl _)), ?_⟩
        intro a ha b hb
        rw [(List.mem_replicate.mp hb).2]
        exact le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp))
      rw [sumN_append_dec hs hpw, spArg_app]
      apply le_spArg
      exact isOT_sumN _ (fun t ht => (hs t (List.mem_append_right _ ht)).1)
    have hold : ∀ g'' ∈ comps (ρ.v g) (ρ.v r), g'' ≤ psi (ρ.v r) z z ∨
        g'' ≤ spArg (ρ.v g) z (sumN (Lc.map ρ.o ++ List.replicate j (omid M r L ρ))) := by
      intro g'' hg''
      rcases I.vs g hgM Lc r [] hCL g'' hg'' with h | h
      · exact Or.inl h
      · exact Or.inr (le_trans h hmono)
    rcases hcv with rfl | rfl
    · rw [hom] at hsy; simp only [psi.injEq] at hsy
      rw [← hsy.1] at hg' ⊢
      exact hold g' hg'
    · have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
      obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
      rw [hsy] at hy0; simp only [psi.injEq] at hy0
      rw [sf_ot (hVT.g.ot_v r hrT)] at hy0
      rw [hy0.1] at hg' ⊢
      by_cases hv : ρ'.v r = ρ.v r
      · rw [hv] at hg' ⊢; exact hold g' hg'
      · rcases hGr M ρ rk r L n σ rkN hctx g hg hgc Lc hCL hv g' hg' with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans h hmono)
  · -- the `D` frames before `r`
    intro i hi hng Lc c R hCL hDc s y hsy g' hg'
    have hcCL : c ∈ CL M i := by rw [hCL]; simp
    have hcM : c ∈ children M i := cl_mem_children hcCL
    have hccnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
    have hcr : c < r := by
      by_cases hig : par M 0 r = some i
      · have hle := children_g_le hlen hL hp hig hcM
        rcases Nat.lt_or_ge c r with h | h
        · exact h
        · exfalso; have : c = r := by omega
          rw [this] at hccnt; exact hng ⟨hig, hccnt⟩
      · exact children_lt_r hlen hL hp hi hig hcM
    have hcN : c < N.length := by rw [hlN]; omega
    have he := o_cl_eq hCN hGN hcN
    rw [hsy] at he; simp only [psi.injEq] at he
    rw [he.1] at hg' ⊢
    by_cases hv : σ.v c = ρ.v c
    · rw [hv] at hg' ⊢
      exact I.vs i (by omega) Lc c R hCL g' hg'
    · exact hD M ρ rk r L n σ rkN hctx i Lc c R hi hcr hCL hv g' hg'

end Ytosk
