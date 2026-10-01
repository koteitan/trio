/-
**2 行・t = 1・q ≠ r の経路で、低い部分の有無が fsD で変わらない（条件 (L)）。**

経路の列 p の引数の最後の加数は、p より下の経路の列 d の値で、d = x（葉 Ω_{μ+1}）なら p = q。
q ≠ r なら q の添字は μ より大きいので、葉が高い部分に現れることはない。
-/
import Ytosk.TwoRowF

namespace Ytosk

open T

theorem last_app : ∀ (B : T) {c : T}, c ≠ z → last (app B c) = last c
  | z, _, _ => by simp
  | psi a b B', c, hc => by
    simp only [app_psi]
    cases hB : app B' c with
    | z => exact absurd (app_eq_z hB).2 hc
    | psi d e f =>
      show last (psi a b (psi d e f)) = last c
      rw [← hB, ← last_app B' hc]
      rw [hB]; rfl

theorem init_app_last : ∀ (t : T), app (init t) (last t) = t
  | z => rfl
  | psi a b z => rfl
  | psi a b (psi c d e) => by
    show app (psi a b (init (psi c d e))) (last (psi c d e)) = psi a b (psi c d e)
    rw [app_psi, init_app_last (psi c d e)]

theorem last_mem : ∀ {t : T}, t ≠ z → last t ∈ summands t
  | z, h => absurd rfl h
  | psi a b z, _ => by simp [last, summands]
  | psi a b (psi c d e), _ => by
    show last (psi c d e) ∈ psi a b z :: summands (psi c d e)
    exact List.mem_cons_of_mem _ (last_mem (by simp))

theorem last_single {t : T} (h : ∃ s y, t = psi s y z) : ∃ s y, last t = psi s y z := by
  obtain ⟨s, y, rfl⟩ := h; exact ⟨s, y, rfl⟩

/-- With no lower part, the last summand is at least the bound. -/
theorem last_ge_of_lo_z {y t : T} (hlo : (split y t).2 = z) (hy : y ≠ z) : ¬ last y < t := by
  have hbpl := split_app t y
  rw [hlo, app_z_right] at hbpl
  have hpge := split_fst_ge t y
  rw [hbpl] at hpge
  exact hpge _ (last_mem hy)

theorem succ_lt_succ' {x y : T} (h : x < y) : succ x < succ y :=
  lt_of_le_of_lt (succ_le_of_lt h) (lt_succ_self y)

theorem omS_lt_omS {x y : T} (h : x < y) : psi (succ x) z z < psi (succ y) z z := by
  rw [psi_lt_psi_z_iff]; exact Or.inl (succ_lt_succ' h)

/-- **Where the last summand of a path argument comes from.** -/
theorem path_last {M : Mat} {x q : Nat} {μ : T} (hG : Good2 M) (hx : x + 1 = M.length)
    (hq : par M 0 x = some q) (hvx : vr M x = succ μ) (hqμ : lt μ (vr M q) = true) :
    ∀ p, Anc0 M p x → p < x → ∃ d, Anc0 M d x ∧ p < d ∧
      last (argOf (o2r M p)) = o2r M d ∧ (d = x → p = q) := by
  have key : ∀ m p, x - p ≤ m → Anc0 M p x → p < x → ∃ d, Anc0 M d x ∧ p < d ∧
      last (argOf (o2r M p)) = o2r M d ∧ (d = x → p = q) := by
    intro m
    induction m with
    | zero => intro p h1 _ h3; omega
    | succ m ih =>
      intro p hm hp hpx
      obtain ⟨c, hc, hcA⟩ := anc0_child hp (by omega)
      have hpc := par_lt M 0 c p hc
      obtain ⟨y, hy⟩ := o2r_sub hG c
      have hcot : isOT (psi (vr M c) y z) = true := by rw [← hy]; exact hG.ot c
      rw [o2r_frame hG hx hcA hc, hy, spArg_single]
      show ∃ d, _ ∧ _ ∧ last (step (vr M p) (bst M p c) (vr M c) y z) = _ ∧ _
      rcases step_cases (a := vr M p) (b := bst M p c) hcot with ⟨B, hB⟩ | ⟨h1, hlo, h3, _⟩
      · refine ⟨c, hcA, hpc, ?_, ?_⟩
        · rw [hB, last_app B (by simp), hy]; rfl
        · intro hcx; subst hcx; rw [hq] at hc; cases hc; rfl
      · rw [h1]
        have hcx : c < x := by
          rcases Nat.eq_or_lt_of_le hcA.le with h' | h'
          · exfalso; subst h'
            rw [o2r_leaf hx (isOT_vr hG.f1 c)] at hy; cases hy; exact h3 rfl
          · exact h'
        obtain ⟨d, hdA, hcd, hld, hdx⟩ := ih c (by omega) hcA hcx
        rw [hy] at hld
        refine ⟨d, hdA, by omega, hld, fun hd => ?_⟩
        exfalso
        have hcq := hdx hd
        subst hd; subst hcq
        have hge := last_ge_of_lo_z hlo h3
        rw [show argOf (psi (vr M c) y z) = y from rfl] at hld
        rw [hld, o2r_leaf hx (isOT_vr hG.f1 _), hvx] at hge
        exact hge (omS_lt_omS hqμ)
  exact fun p => key _ p (Nat.le_refl _)

end Ytosk
