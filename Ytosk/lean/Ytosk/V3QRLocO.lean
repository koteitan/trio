/-
**3 行・t = 1・q = r: o の枠の等式（1 段）。**

列 i の最後の数える子 c（D）について、枠の等式 fsD(o(i), Zf i) = ψ_{v(i)}(spArg(v(i), B, fsD(o(c), Zf c))):
- 引き上げなし（`qr_frame_nolift`）: Zf i = Zf c。子に対角化の点があり、(W)・(L) が成り立てば `frameD_gen`。
- 引き上げ（`qr_frame_lift`）: o(c) = A = ψ_μ(b + Ω_{μ+1}) で書き換えが起きる枠、Zf i = next(Zf c)。
- r の枠（`qr_frame_r`）: 子は x（値 Ω_{μ+1}）、spArg(μ, b, ζ) = b + ζ のとき。鎖の 2 項目以降では
  これが成り立つ（`spArg_qnext`）。
- (L)(ii) の補題 `lo_keep_Q`: y ≠ b_r なら、最後の項 Ω_a（a 極限）の条件を η₀ ≤ ζ で。
-/
import Ytosk.V3QRAsm

namespace Ytosk

open T

/-- **`spArg(μ, b, next ζ) = b + next ζ`** (the frame at `r` on the chain after the seed). -/
theorem spArg_qnext {μ b ζ : T} (hb : AllGeT (psi (succ μ) z z) b) (hζz : ζ ≠ z)
    (hζ : ζ < psi (succ μ) z z) (hot : isOT (qnext μ b ζ) = true) :
    spArg μ b (qnext μ b ζ) = app b (qnext μ b ζ) := by
  unfold qnext at hot ⊢
  rw [spArg_cons]; show step μ b μ (app b ζ) z = _
  have hy : app b ζ ≠ z := fun h => hζz (app_eq_z h).2
  have htr : lt b (app b ζ) = true ∧ lt (psi μ z z) (psi μ (app b ζ) z) = true := by
    have hpos : z < app b ζ := by
      revert hy; cases app b ζ with
      | z => intro h; exact absurd rfl h
      | psi a c d => intro _; exact T.z_lt_psi a c d
    refine ⟨lt_app_of hζz, ?_⟩
    show psi μ z z < psi μ (app b ζ) z
    rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hpos⟩
  unfold step
  rw [if_pos htr, H_eq hot, split_b_app hb hζ]
  simp [hζz]

/-- **The frame at `r`**: the child `x` has the value `Ω_{μ+1}`. -/
theorem qr_frame_r {μ b ζ : T} (hsp : spArg μ b ζ = app b ζ) :
    fsD (psi μ (app b (psi (succ μ) z z)) z) ζ =
      psi μ (spArg μ b (fsD (psi (succ μ) z z) ζ)) z := by
  rw [fsD_A, fsD_leaf (isSucc_succ μ) (succ_ne_z μ), hsp]; rfl

/-- The rewrite of the child `A`: `spArg(a, B, A) = b + Ω_{μ+1}`. -/
theorem spArg_A {a B μ b : T} (hb : AllGeT (psi (succ μ) z z) b)
    (hAot : isOT (psi μ (app b (psi (succ μ) z z)) z) = true)
    (htr : lt B (app b (psi (succ μ) z z)) = true ∧
      lt (psi a z z) (psi μ (app b (psi (succ μ) z z)) z) = true) :
    spArg a B (psi μ (app b (psi (succ μ) z z)) z) = app b (psi (succ μ) z z) := by
  have hall : ∀ q ∈ summands (app b (psi (succ μ) z z)), ¬ q < psi (succ μ) z z := by
    intro q hq
    rw [summands_app] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hb q hq
    · simp [summands] at hq; rw [hq]; exact lt_irrefl' _
  have hsp := split_app_of (B := app b (psi (succ μ) z z)) (X := z) hall (Or.inl rfl)
  rw [app_z_right] at hsp
  rw [spArg_cons]; show step a B μ _ z = _
  unfold step
  rw [if_pos htr, H_eq hAot, hsp]
  simp

section
variable {M : Mat} {ρ : Valn} {i c : Nat} {L R : List Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hiM : i < M.length)
  (hch : children M i = L ++ c :: R) (hcb : col M c ≠ bump M i)
  (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
  (hR : ∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) (hcM : c < M.length)
include hC hG hiM hch hcb hcu hR hcM

/-- **A lifted frame**: the child is `A` and rewrites; the parent moves by `next ζ`. -/
theorem qr_frame_lift {μ b ζ : T} (hb : AllGeT (psi (succ μ) z z) b)
    (hcA : ρ.o c = psi μ (app b (psi (succ μ) z z)) z)
    (hAζ : isOT (qnext μ b ζ) = true)
    (htr : lt (preState M ρ i L) (app b (psi (succ μ) z z)) = true ∧
      lt (psi (ρ.v i) z z) (psi μ (app b (psi (succ μ) z z)) z) = true)
    (hζ : ζ < psi (succ μ) z z) (hζz : ζ ≠ z) (hBζ : lt (preState M ρ i L) (app b ζ) = true) :
    fsD (ρ.o i) (qnext μ b ζ) =
      psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (fsD (ρ.o c) ζ)) z := by
  have hAot : isOT (psi μ (app b (psi (succ μ) z z)) z) = true := by rw [← hcA]; exact hG.ot_o c hcM
  rw [o_frame hC hG hiM hch hcb hcu hR hcM, hcA, fsD_A]
  have hX := spArg_A hb hAot htr
  exact o_lift hb hAot hAζ htr hζ hζz hBζ
    (by rw [hX]; intro h; exact absurd (app_eq_z h).2 (by simp))
    (by rw [hX]; exact not_succ_of_cof_big cof_br)

/-- **A frame without a lift**: the child has a diagonal point, (W) and (L) hold at `ζ`. -/
theorem qr_frame_nolift {ζ a' br μ vr : T} (hD : DiagAt a' br μ (ρ.o c)) (ha' : ¬ lt vr a' = true)
    (hok : isOT (fsD (ρ.o c) ζ) = true ∧ fsD (ρ.o c) ζ < ρ.o c)
    (hW : ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L) y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true → lt (preState M ρ i L) (fsD y ζ) = true)
    (hL : ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L) y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 ζ ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z → (split (fsD y ζ) (psi (succ s) z z)).2 = z)) :
    fsD (ρ.o i) ζ = psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (fsD (ρ.o c) ζ)) z := by
  obtain ⟨s, y, hcv⟩ := o_psi_form hC hcM
  have hcot : isOT (psi s y z) = true := by rw [← hcv]; exact hG.ot_o c hcM
  have hHc : HoleT μ br vr (psi s y z) := Or.inr ⟨a', ha', by rw [← hcv]; exact hD⟩
  have hD' : DiagAt a' br μ (psi s y z) := by rw [← hcv]; exact hD
  have hframe := o_frame hC hG hiM hch hcb hcu hR hcM
  have hframe2 := hframe
  rw [hcv, spArg_single] at hframe2
  set B := preState M ρ i L with hB
  have hsplit := cvals_split hch hcb hcu hR (by rw [hcv]; simp)
  have hdec := hG.dec i hiM
  rw [hsplit] at hdec
  have hsL : ∀ t ∈ nzs (L.map (cnt M ρ i)), Single t := by
    intro t ht
    exact cvals_single hC hG i t (by rw [hsplit]; exact List.mem_append_left _ ht)
  have hBge : ∀ q ∈ summands B, psi s y z ≤ q := by
    have hS := sumN_dec _ hsL (List.pairwise_append.mp hdec).1
    rw [hB]; unfold preState
    apply spArg_summands_ge ⟨s, y, rfl⟩ _ z hS.1
    · intro q hq; rw [hS.2] at hq
      have := (List.pairwise_append.mp hdec).2.2 q hq (ρ.o c) (List.mem_singleton_self _)
      rw [hcv] at this; exact this
    · intro q hq; simp [summands] at hq
  rw [hframe, hcv]
  apply node_fsD
  apply frameD_gen hcot (by rw [← hcv]; exact hok) (holeT_not_succ hHc)
    (fun hy => not_succ_arg_of_holeT hy hHc) ?_ (hW s y hcv) (hL s y hcv)
  · intro htr
    have hot := hG.ot_o i hiM
    rw [hframe2] at hot
    unfold step at hot
    rw [if_neg htr, add_eq_app_of_ge ⟨s, y, rfl⟩ _ hBge] at hot
    exact isOT_arg hot
  · -- the leaf condition: `o(c) = Ω_s` with `s` a limit
    intro hyz s' y' hmem
    subst hyz
    have hsz : s ≠ z := by
      intro h; subst h
      have := DiagAt.not_succ hD'
      have h1 : isSucc (psi z z z) = true := rfl
      rw [h1] at this; cases this
    have hss := DiagAt.not_omega_succ hD'
    rw [fsD_sub hsz hss] at hmem
    simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hmem
    obtain ⟨_, rfl, _⟩ := hmem
    exact Or.inl (z_le _)

end

end Ytosk
