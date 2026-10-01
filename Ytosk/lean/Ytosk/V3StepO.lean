/-
**3 行・t = 1: o の枠の 1 段（最後の数える子が変わる場合）。**

列 i の数える子のうち最後の子 c だけが D に入るとき、c について「貼り合わせの値 = fsD(o(c), ζ)、穴 HoleT、
fsD が標準形で小さい」が成り立っていれば、i についても同じことが成り立つ（`stepO_last`）。
枠の条件（書き換えの持続 (W)、低い部分の保存 (L)、y = 0 のときの条件、帯の条件）は仮定。
-/
import Ytosk.V3Hole

namespace Ytosk

open T

/-- The state before the last counted child. -/
noncomputable def preState (M : Mat) (ρ : Valn) (i : Nat) (L : List Nat) : T :=
  spArg (ρ.v i) z (sumN (nzs (L.map (cnt M ρ i))))

section
variable {M : Mat} {x i : Nat} {ρ ρN : Valn} {ζ μ br vr seed : T} {L R : List Nat} {c : Nat}

/-- The counted values split at the last counted child. -/
theorem cvals_split (hch : children M i = L ++ c :: R) (hcb : col M c ≠ bump M i)
    (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
    (hR : ∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hcz : ρ.o c ≠ z) :
    cvals M ρ i = nzs (L.map (cnt M ρ i)) ++ [ρ.o c] := by
  unfold cvals
  rw [hch, List.map_append, List.map_cons, cnt_cnt ρ hcb hcu, nzs_append]
  have : nzs (ρ.o c :: R.map (cnt M ρ i)) = [ρ.o c] := by
    have hRz : nzs (R.map (cnt M ρ i)) = [] := nzs_zeros _ (fun t ht => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact cnt_unc ρ (hR d hd))
    simp only [nzs, List.filter_cons, ne_eq, hcz, not_false_eq_true, decide_true, ↓reduceIte,
      List.cons.injEq, true_and]
    exact hRz
  rw [this]

/-- **The frame decomposition**: `o(i) = ψ_{v(i)}(spArg(v(i), B, o(c)))`. -/
theorem o_frame (hC : Cons M ρ) (hG : Good3 M ρ) (hiM : i < M.length)
    (hch : children M i = L ++ c :: R) (hcb : col M c ≠ bump M i)
    (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
    (hR : ∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hcM : c < M.length) :
    ρ.o i = psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (ρ.o c)) z := by
  have hcs := single_o hC hG hcM
  have hsplit := cvals_split hch hcb hcu hR (single_ne_z hcs)
  have hdec := hG.dec i hiM
  have hsing := cvals_single hC hG i
  rw [hsplit] at hdec hsing
  rw [o_spArg hC hG hiM, hsplit, sumN_snoc_dec hsing hdec, spArg_app]
  rfl

theorem not_succ_arg_of_holeT {s y : T} (hy : y ≠ z) (h : HoleT μ br vr (psi s y z)) :
    isSucc y = false := by
  rcases h with h | ⟨a', _, hD⟩
  · exact not_succ_of_cof_big (cof_psi_inv hy h).1
  · cases hD with
    | here _ hc _ => exact not_succ_of_cof_big hc
    | arg _ hs _ => exact hs
    | sub ha _ _ => exact absurd rfl hy

/-- **One `o` frame where the last counted child changes.** -/
theorem stepO_last (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length) (hi : i < x)
    (hch : children M i = L ++ c :: R) (hcb : col M c ≠ bump M i)
    (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
    (hR : ∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hLnd : ∀ d ∈ L, Counted M i d → ¬ DepX M x true d) (hv : ¬ DepX M x false i)
    (hcM : c < M.length)
    (hcz : (glue M x ρ ρN ζ).o c = fsD (ρ.o c) ζ) (hHc : HoleT μ br vr (ρ.o c))
    (hokc : isOT (fsD (ρ.o c) ζ) = true ∧ fsD (ρ.o c) ζ < ρ.o c) (hcS' : Single (fsD (ρ.o c) ζ))
    (hleaf : ∀ s y, ρ.o c = psi s y z → y = z → ∀ s' y', psi s' y' z ∈ summands (fsD (psi s y z) ζ) →
      y' ≤ preState M ρ i L ∨ s' < ρ.v i)
    (hW : ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L) y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true → lt (preState M ρ i L) (fsD y ζ) = true)
    (hL : ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L) y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 ζ ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z → (split (fsD y ζ) (psi (succ s) z z)).2 = z))
    (hpass : ∀ s y, ρ.o c = psi s y z → cof (psi s y z) = .big μ →
      lt μ (ρ.v i) = true ∨ (ρ.v i = vr ∧ step (ρ.v i) (preState M ρ i L) s y z = br))
    (hμ : μ = vr) (hbr : br ≠ z) (hcbr : cof br = .big μ) :
    oRhs M (glue M x ρ ρN ζ) i = fsD (ρ.o i) ζ ∧ HoleT μ br vr (ρ.o i) := by
  have hiM : i < M.length := by omega
  obtain ⟨s, y, hcv⟩ := o_psi_form hC hcM
  have hcot : isOT (psi s y z) = true := by rw [← hcv]; exact hG.ot_o c hcM
  have hHc' : HoleT μ br vr (psi s y z) := by rw [← hcv]; exact hHc
  have hframe := o_frame hC hG hiM hch hcb hcu hR hcM
  rw [hcv, spArg_single] at hframe
  -- the state before `c`
  set B := preState M ρ i L with hB
  have hsplit := cvals_split hch hcb hcu hR (by rw [hcv]; simp)
  have hdec := hG.dec i hiM
  rw [hsplit] at hdec
  have hsL : ∀ t ∈ nzs (L.map (cnt M ρ i)), Single t := by
    intro t ht
    have := cvals_single hC hG i t (by rw [hsplit]; exact List.mem_append_left _ ht)
    exact this
  have hBge : ∀ q ∈ summands B, psi s y z ≤ q := by
    have hS := sumN_dec _ hsL (List.pairwise_append.mp hdec).1
    rw [hB]; unfold preState
    apply spArg_summands_ge ⟨s, y, rfl⟩ _ z hS.1
    · intro q hq; rw [hS.2] at hq
      have := (List.pairwise_append.mp hdec).2.2 q hq (ρ.o c) (List.mem_singleton_self _)
      rw [hcv] at this; exact this
    · intro q hq; simp [summands] at hq
  refine ⟨?_, ?_⟩
  · apply hF_o_last hC hx hi hch hcb hcu hcz ?_ hR hv (hG.ot_v i hiM) ?_ (single_o hC hG hcM) hcS'
      (by rw [← hsplit]; exact hG.dec i hiM) (le_of_lt hokc.2)
    · -- the frame condition
      rw [hcv]
      apply frameD_gen hcot (by rw [← hcv]; exact hokc) (holeT_not_succ hHc')
        (fun hy => not_succ_arg_of_holeT hy hHc') (hleaf s y hcv) (hW s y hcv) (hL s y hcv)
      intro htr
      have hot := hG.ot_o i hiM
      rw [hframe] at hot
      unfold step at hot
      rw [if_neg htr, add_eq_app_of_ge ⟨s, y, rfl⟩ _ hBge] at hot
      exact isOT_arg hot
    · intro d hd
      by_cases hcd : Counted M i d
      · have hdc : d < c := by
          have hsort := children_sorted M i
          rw [hch] at hsort
          have := List.pairwise_append.mp hsort
          exact this.2.2 d hd c List.mem_cons_self
        rw [cnt_cnt _ hcd.1 hcd.2, cnt_cnt _ hcd.1 hcd.2]
        have hcx : c ≤ x := by omega
        exact glue_o_lt ρ ρN ζ (by omega) (hLnd d hd hcd)
      · have : col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true) := by
          by_cases h1 : col M d = bump M i
          · exact Or.inl h1
          · right; by_contra h2; exact hcd ⟨h1, h2⟩
        rw [cnt_unc _ this, cnt_unc _ this]
    · intro t ht
      exact cnt_single hC hG i t (by rw [hch, List.map_append]; exact List.mem_append_left _ ht)
  · rw [hframe]
    exact holeT_oframe hcot hHc' hμ hbr hcbr (hpass s y hcv)

/-- **One `o` frame where only the subscript changes** (no counted children). -/
theorem stepO_sub (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length) (hi : i < x)
    (hnc : ∀ d ∈ children M i, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hv : DepX M x false i) (hHv : HoleT μ br vr (ρ.v i))
    (hokv : isOT (fsD (ρ.v i) ζ) = true ∧ fsD (ρ.v i) ζ < ρ.v i) :
    oRhs M (glue M x ρ ρN ζ) i = fsD (ρ.o i) ζ ∧ HoleT μ br vr (ρ.o i) := by
  have hiM : i < M.length := by omega
  have hvz := holeT_ne_z hHv
  have hvs := holeT_not_succ hHv
  refine ⟨hF_o_sub hC hx hi hnc hv (hG.ot_v i hiM) hokv.1 hvz hvs, ?_⟩
  have hcv : cvals M ρ i = [] := by
    unfold cvals
    exact nzs_zeros _ (fun t ht => by obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact cnt_unc ρ (hnc d hd))
  rw [o_spArg hC hG hiM, hcv]
  exact holeT_sub hvz hvs hHv

/-- **One upgrade frame** (`v(i) = v(U i)`, no row-1 parent value). -/
theorem stepV_upg (hC : Cons M ρ) (hx : x + 1 = M.length) (hi : i < x) {k : Nat} (hk : k < x)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i = 0) (hu : upg M i = some k)
    (hp : vOpt (glue M x ρ ρN ζ) (par M 1 i) = z) (hpM : vOpt ρ (par M 1 i) = z)
    (hkd : DepX M x false k) (hV : Single (ρ.v k)) (hV' : Single (fsD (ρ.v k) ζ))
    (hHk : HoleT μ br vr (ρ.v k)) :
    vRhs M (glue M x ρ ρN ζ) i = fsD (ρ.v i) ζ ∧ HoleT μ br vr (ρ.v i) := by
  have hiM : i < M.length := by omega
  refine ⟨hF_v_upg hC hx hi hk h1 h2 hu hp hpM hkd hV hV', ?_⟩
  have hvi : ρ.v i = ρ.v k := by
    rw [(hC i hiM).2]
    unfold vRhs
    rw [if_neg h1, if_pos h2, hu, hpM]
    obtain ⟨hot, s, y, hsy⟩ := hV
    simp only [add_z_left]
    rw [hsy]; simp only [last]; rw [← hsy, sf_ot hot]
  rw [hvi]; exact hHk

end

end Ytosk
