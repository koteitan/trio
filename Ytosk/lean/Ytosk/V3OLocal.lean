/-
**3 行・t = 1・q ≠ r: o の枠の局所条件を、形・持続・低い部分から作る。**

`OLocal` のうち
- fsD(o(c), ζ) が項 1 つ（`single_fsD`、穴と標準形から）、
- 葉の条件（o(c) = Ω_s: s が後者なら c = x で親 q ≠ r なので F1、s が極限なら引数 0）、
- 通過条件（位置と F1、`t1_hole` と同じ）
は導ける。残るのは書き換えの持続 (W) と低い部分の保存 (L)（`olocal_of`）。
-/
import Ytosk.V3HoleT1

namespace Ytosk

open T

theorem step_ne_z {a b s y : T} (hc : isOT (psi s y z) = true) : step a b s y z ≠ z := by
  rcases step_cases (a := a) (b := b) hc with ⟨B, hB⟩ | ⟨hy, _, hyz, _⟩
  · rw [hB]; intro h; exact absurd (app_eq_z h).2 (by simp)
  · rw [hy]; exact hyz

/-- `fsD` of a single summand with a hole is a single summand (when standard and `ζ` is single). -/
theorem single_fsD {t ζ : T} (ht : ∃ s y, t = psi s y z) (hns : isSucc t = false)
    (hy : ∀ s y, t = psi s y z → y ≠ z → isSucc y = false) (hζ : ∃ a X, ζ = psi a X z)
    (hot : isOT (fsD t ζ) = true) : Single (fsD t ζ) := by
  refine ⟨hot, ?_⟩
  obtain ⟨s, y, rfl⟩ := ht
  by_cases hyz : y = z
  · subst hyz
    by_cases hsz : s = z
    · subst hsz; have h1 : isSucc (psi z z z) = true := rfl; rw [h1] at hns; cases hns
    · by_cases hss : isSucc s = true
      · rw [fsD_leaf hss hsz]; exact hζ
      · rw [fsD_sub hsz (by simpa using hss)]; exact ⟨_, _, rfl⟩
  · rw [fsD_psi hyz (hy s y rfl hyz)]; exact ⟨_, _, rfl⟩

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ br vr ζ : T}

/-- **The `o` local conditions** from the shape, the hole, persistence and the low part. -/
theorem olocal_of (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hrx : r < x) (hAr : Anc0 M r x) (hro : ρ.o r = psi vr br z) (hqr : par M 0 x ≠ some r)
    (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
    (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
    (hHole : ∀ b i, DepX M x b i → (i < x ∨ (i = x ∧ b = true)) →
      HoleT μ br vr (valB ρ b i) ∧ DiagLe μ br vr r i (valB ρ b i))
    (hζ : ∃ X, ζ = psi μ X z) (hox : fsD (ρ.o x) ζ = ζ)
    (hok : ∀ t, isOT t = true → HoleT μ br vr t → isOT (fsD t ζ) = true)
    (hW : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → DepX M x true c →
      ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L) y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true → lt (preState M ρ i L) (fsD y ζ) = true)
    (hL : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → DepX M x true c →
      ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L) y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 ζ ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z → (split (fsD y ζ) (psi (succ s) z z)).2 = z)) :
    ∀ i, i < x → DepX M x true i → OLocal M x ρ ζ μ vr br i := by
  intro i hi hd
  have hiM : i < M.length := by omega
  rcases hOS i hi hd with ha | ⟨hv, L, c, R, hch, hcb, hcu, hR, hLnd⟩
  · exact Or.inl ha
  right
  -- `c` is in `D`
  have hcmem : c ∈ children M i := by rw [hch]; exact List.mem_append_right _ List.mem_cons_self
  have hdc : DepX M x true c := by
    cases hd with
    | leaf => omega
    | @ochild _ c' hc' hb' hu' hd' =>
      have : c' = c := by
        rw [hch] at hc'
        rcases List.mem_append.mp hc' with h | h
        · exact absurd hd' (hLnd c' h ⟨hb', hu'⟩)
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · rcases hR c' h with h' | h'
            · exact absurd h' hb'
            · exact absurd h' hu'
      rw [← this]; exact hd'
    | ov hv' => exact absurd hv' hv
  have hcM := (mem_children hcmem).2
  have hic := (mem_children hcmem).1
  have hcx : c ≤ x := by omega
  have hcpos : c < x ∨ (c = x ∧ true = true) := by
    rcases Nat.lt_or_ge c x with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, rfl⟩
  obtain ⟨hHc, hDc⟩ := hHole true c hdc hcpos
  simp only [valB, cond_true] at hHc hDc
  have hframe := o_frame hC hG hiM hch hcb hcu hR hcM
  have hpar : r < c → r ≤ i := fun h => par0_ge_of_anc hAr h hcx (mem_children_iff.mp hcmem).2
  refine ⟨hv, L, c, R, hch, hcb, hcu, hR, hLnd, ?_, ?_, hW i L c R hi hd hch hdc,
    hL i L c R hi hd hch hdc, ?_⟩
  · -- single
    obtain ⟨X, hX⟩ := hζ
    apply single_fsD (o_psi_form hC hcM) (holeT_not_succ hHc)
      (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHc)) ⟨μ, X, hX⟩
      (hok _ (hG.ot_o c hcM) hHc)
  · -- the leaf condition
    intro s y hcv hyz s' y' hmem
    subst hyz
    by_cases hsz : s = z
    · subst hsz
      have := holeT_not_succ hHc; rw [hcv] at this
      have h1 : isSucc (psi z z z) = true := rfl; rw [h1] at this; cases this
    by_cases hss : isSucc s = true
    · -- `c = x`
      have hcxe : c = x := by
        rcases Nat.lt_or_ge c x with h | h
        · exfalso
          rcases hOS c h hdc with ⟨hvc, hnc⟩ | ⟨_, L', c', R', hch', hcb', hcu', hR', _⟩
          · obtain ⟨hHv, _⟩ := hHole false c hvc (Or.inl h)
            simp only [valB, cond_false] at hHv
            have hoc := o_nocnt hC hG hcM hnc
            rw [hcv] at hoc
            have hs : s = ρ.v c := (T.psi.inj hoc).1
            rw [hs, holeT_not_succ hHv] at hss; cases hss
          · have hc'M := (mem_children (by rw [hch']; exact List.mem_append_right _ List.mem_cons_self :
              c' ∈ children M c)).2
            have hfr := o_frame hC hG hcM hch' hcb' hcu' hR' hc'M
            obtain ⟨s3, y3, hc3⟩ := o_psi_form hC hc'M
            rw [hc3, spArg_single, hcv] at hfr
            have h3 : isOT (psi s3 y3 z) = true := by rw [← hc3]; exact hG.ot_o c' hc'M
            exact step_ne_z h3 (T.psi.inj hfr).2.1.symm
        · omega
      subst hcxe
      have hix : par M 0 c = some i := (mem_children_iff.mp hcmem).2
      have hri : r < i := by
        rcases Nat.eq_or_lt_of_le (hpar hrx) with h | h
        · exact absurd (h ▸ hix) hqr
        · exact h
      right
      rw [← hcv, hox] at hmem
      obtain ⟨X, hX⟩ := hζ
      rw [hX] at hmem
      simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hmem
      obtain ⟨rfl, _, _⟩ := hmem
      exact hF1 i hri hi hd hv
    · left
      rw [fsD_sub hsz (by simpa using hss)] at hmem
      simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hmem
      obtain ⟨_, rfl, _⟩ := hmem
      exact z_le _
  · -- the passing condition
    intro s y hcv hcof
    have hrc : r < c := by
      by_contra h
      obtain ⟨a', _, hD⟩ := hDc (by omega)
      rw [hcv] at hD
      exact DiagAt.cof_ne hD hcof
    rcases Nat.eq_or_lt_of_le (hpar hrc) with h | h
    · right
      have h' := hframe
      rw [hcv, spArg_single, ← h, hro] at h'
      rw [← h]
      exact ⟨(T.psi.inj h').1.symm, (T.psi.inj h').2.1.symm⟩
    · exact Or.inl (hF1 i h hi hd hv)

end

end Ytosk
