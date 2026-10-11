/-
**3 行・t = 2・q ≠ r: x より前の Good3（Good3 N を仮定しない）。**

`t2_qn_main`（V3T2QM）を `t2_assembleOT` に替えた写し。種 v(q) の ◁ は `v_bump_lost`、標準形は仮定
（`vq_N` で出る）。種 o(P_0 q) と弱い呼び出し o(q) は仮定。
-/
import Ytosk.V3T2QM
import Ytosk.V3ExpT2AO

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L d0 d1 n qp : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hp : par M 0 (r + L) = some (r + qp)) (hqp : qp < L)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn2 : 2 ≤ n)
  (hxb : col M (r + L) = bump M (r + qp)) (hBE : BumpE2 M)
include hlen hL hA hp hqp hd0e hn2 hxb hBE

omit hBE in
/-- **`t = 2`, `q ≠ r`: Good3 of `M[n]` before `x`.** -/
theorem t2_qn_below (hBE : BumpE2 M) (hZ2 : Z2 M) (hUAT : UAT M) (hR12 : R12 M) (hR01 : R01 M)
    (h00 : entry M 0 0 = 0) (he2r : entry M 2 r = 0) {pq : Nat} (hpq : par M 0 (r + qp) = some pq)
    (hqb : col M (r + qp) ≠ bump M pq) (he2pq : entry M 2 pq = 0) (hCLq : CL M (r + qp) = [])
    (hpqCL : CL M pq ≠ [])
    (hIUt : ∀ c, c < r + L → c ≠ r + qp → topped M c = true → isUpg (TRIO.gexp M r L d0 d1 n) c = isUpg M c)
    -- the shape of `D` in `M`
    (hP1q : ∀ m, par M 1 (r + qp) = some m → ¬ DepS M (SQ (r + qp) pq) false m)
    (hqL : ∀ d ∈ children M (r + qp), col M d = bump M (r + qp) → ∀ e ∈ children M d,
      ¬ DepS M (SQ (r + qp) pq) true e)
    (hDvNil : ∀ c, c < r + L → DepS M (SQ (r + qp) pq) false c → CL M c = [])
    (hOS : ∀ i, i < r + L → ¬ SQ (r + qp) pq true i → ¬ WQ (r + qp) true i →
      DepS M (SQ (r + qp) pq) true i → ¬ DepS M (SQ (r + qp) pq) false i →
      ∃ L c R, children M i = L ++ c :: R ∧ Counted M i c ∧ DepS M (SQ (r + qp) pq) true c ∧
        (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ L, Counted M i d → ¬ DepS M (SQ (r + qp) pq) true d))
    (hVSh : ∀ i, i < r + L → ¬ SQ (r + qp) pq false i → DepS M (SQ (r + qp) pq) false i →
      (∀ m, par M 1 i = some m → ¬ DepS M (SQ (r + qp) pq) false m) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
        children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M (SQ (r + qp) pq) true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M (SQ (r + qp) pq) true e)))
    -- values
    {ρ σ : Valn} {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN)
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ)
    (hKD : BumpKidsDec M ρ)
    (hAbs : AbsWN M (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ)
    (hVSN : T2VSN (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ)
    (hHA : T2HardA M (TRIO.gexp M r L d0 d1 n) (r + L) pq ρ σ)
    (hOTout : ∀ b j, r + L ≤ j → j < (TRIO.gexp M r L d0 d1 n).length → isOT (valB σ b j) = true)
    (hvqot : isOT (σ.v (r + qp)) = true)
    (hseed : Lhd z (σ.o pq) (ρ.o pq) ∧ isOT (σ.o pq) = true)
    (hsdec : (cvals (TRIO.gexp M r L d0 d1 n) σ pq).Pairwise (fun a b => b ≤ a))
    (hqot : isOT (σ.o (r + qp)) = true)
    (hqdec : (cvals (TRIO.gexp M r L d0 d1 n) σ (r + qp)).Pairwise (fun a b => b ≤ a)) :
    ∀ i, i < r + L → isOT (σ.o i) = true ∧ isOT (σ.v i) = true ∧
      (cvals (TRIO.gexp M r L d0 d1 n) σ i).Pairwise (fun a b => b ≤ a) ∧
      (¬ SQ (r + qp) pq true i → ¬ WQ (r + qp) true i →
        FrameShape M (TRIO.gexp M r L d0 d1 n) ρ σ i) ∧
      (¬ WQ (r + qp) true i → σ.o i ≤ ρ.o i) ∧
      (¬ SQ (r + qp) pq false i → DepS M (SQ (r + qp) pq) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children (TRIO.gexp M r L d0 d1 n) i = Lb ++ [j] ∧
          col M j = bump M i ∧ col (TRIO.gexp M r L d0 d1 n) j = bump (TRIO.gexp M r L d0 d1 n) i ∧
          children M j = Kb ++ [k] ∧ children (TRIO.gexp M r L d0 d1 n) j = Kb ++ [k] ∧
          (∀ d ∈ Kb, σ.o d = ρ.o d) ∧
          (∀ d ∈ Lb, bumpTerm (TRIO.gexp M r L d0 d1 n) σ i d = bumpTerm M ρ i d) ∧
          (∀ d ∈ Lb, ∀ e ∈ children M d, e < r + L → σ.o e = ρ.o e) ∧
          Lhd z (σ.o k) (ρ.o k) ∧ isOT (σ.o k) = true) ∧
      (¬ DepS M (SQ (r + qp) pq) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < r + L → σ.o k = ρ.o k) := by
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hqx : r + qp < r + L := by omega
  have hqM : r + qp < M.length := by omega
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hp⟩
  have hpqq : pq < r + qp := par_lt M 0 _ _ hpq
  have he2q := e2_q hlen hp hxb hBE
  have he1q : entry M 1 (r + qp) ≠ 0 := by
    have h1 : entry M 1 (r + L) = entry M 1 (r + qp) :=
      e1_of_col (show col M (r + L) = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from hxb)
    intro h0; rw [← h1] at h0; have := hR12 _ h0; have := e2_x hxb; omega
  have hxN2 : entry (TRIO.gexp M r L d0 d1 n) 2 (r + L) = 0 := by
    rw [(entry_xprimeQ hlen hL hA hp hqp hd0e (by omega) hn2).1, he2r]
  have hcolN : ∀ i, i < r + L → col (TRIO.gexp M r L d0 d1 n) i = col M i := fun i hi => col_gexp_pre hlen (by omega) hi
  have hbumpN : ∀ i, i < r + L → bump (TRIO.gexp M r L d0 d1 n) i = bump M i := fun i hi => by
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi]
  have hchN : ∀ i, i < r + L → children (TRIO.gexp M r L d0 d1 n) i = children M i :=
    fun i hi => children_N2Q hlen hL hA hp hqp hd0e (by omega) hn2 hi
  have hnu : upg M (r + L - 1) ≠ some (r + L) := fun h =>
    upg_not_x hlen hA hp hxb hBE h (le_refl _) (by omega)
  have hupgN : ∀ i, i < r + L → upg (TRIO.gexp M r L d0 d1 n) i = upg M i := fun i hi =>
    upg_NQ hlen hL hA hp hqp hd0e hn2 he2r hnu hi
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hp] at h'; exact (Option.some.inj h').symm
  have hcntS : ∀ i c, i < r + L → i ≠ pq → c ∈ children M i → c < r + L →
      (Counted (TRIO.gexp M r L d0 d1 n) i c ↔ Counted M i c) := by
    intro i c hi hipq hc hcx
    apply counted_NQ hlen hL hA hp hqp hd0e hn2 hxb hIUt hi hcx
    intro h; apply hipq
    have h' := (mem_children_iff.mp hc).2; rw [h, hpq] at h'; exact (Option.some.inj h').symm
  have hbjN : ∀ i j, i < r + L → j ∈ children (TRIO.gexp M r L d0 d1 n) i → r + L ≤ j → col (TRIO.gexp M r L d0 d1 n) j ≠ bump (TRIO.gexp M r L d0 d1 n) i := by
    intro i j hi hj hjx hb
    have hjl := (mem_children hj).2
    rw [hlN] at hjl
    rcases par0_tail2Q hlen hL hA hp hqp hd0e (by omega) hjx hjl with ⟨hjx', _⟩ | ⟨p', hp', hp'1, _⟩
    · rw [hjx'] at hb
      have := e2_of_col (show col (TRIO.gexp M r L d0 d1 n) (r + L) = (entry (TRIO.gexp M r L d0 d1 n) 0 i + 1, entry (TRIO.gexp M r L d0 d1 n) 1 i, 1) from hb)
      omega
    · rw [(mem_children_iff.mp hj).2] at hp'; cases hp'; omega
  have hoff := t2_off_gen (S := SQ (r + qp) pq) (bnd := r + L) hC hCN hRN (by omega) (by rw [hlN]; omega)
    (fun i hi _ => hchN i hi) (DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (Or.inr (DepS.seed (Or.inl ⟨rfl, rfl⟩))) (fun i hq hb => by have h' := (mem_children_iff.mp hq).2; rw [hpq] at h'; cases h'; exact hqb hb)
    (fun y i hi => entry_gexp_pre hlen (by omega) y hi) (fun i hi => par_gexp_pre hlen (by omega) 1 hi)
    (fun i hi _ => hupgN i hi)
    (fun i c hi hd hc hcx => hcntS i c hi (fun h => hd (DepS.seed (Or.inr ⟨rfl, h⟩))) hc hcx)
    (fun i c hi hc hcx => by
      obtain ⟨_, rfl⟩ := hxc i c hc hcx
      exact DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i k hi hk hkx => (upg_not_x hlen hA hp hxb hBE hk hkx hi).elim)
    hbjN
    (fun i j hi hj hjx _ => by
      obtain ⟨_, rfl⟩ := hxc i j hj hjx
      exact DepS.seed (Or.inl ⟨rfl, rfl⟩))
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc j k hk hkx
      have h' := (mem_children_iff.mp hj).2; rw [hpq] at h'; cases h'
      exact absurd hjb hqb)
  -- the seed `v(q)`
  have hcqM : children M (r + qp) =
      (children M (r + qp)).filter (fun d => decide (d < r + L)) ++ [r + L] :=
    split_last_max _ _ (children_sorted M _) hxq (fun d hd => by have := (mem_children hd).2; omega)
  have hvq : Lhd z (σ.v (r + qp)) (ρ.v (r + qp)) := by
    apply v_bump_lost (L := (children M (r + qp)).filter (fun d => decide (d < r + L))) (j := r + L)
      hC hG hCN hqM (by rw [hlN]; omega) he1q (by omega)
      (entry_gexp_pre hlen (by omega) 1 hqx) (entry_gexp_pre hlen (by omega) 2 hqx)
    · rw [par_gexp_pre hlen (by omega) 1 hqx]
      cases hm : par M 1 (r + qp) with
      | none => rfl
      | some m =>
        show σ.v m = ρ.v m
        exact (hoff m (by have := par_lt M 1 _ m hm; omega)).2 (hP1q m hm)
    · exact hcqM
    · rw [hchN _ hqx]; exact hcqM
    · intro d hd
      have hdx : d < r + L := by have := (List.mem_filter.mp hd).2; simpa using this
      have hdM : d ∈ children M (r + qp) := (List.mem_filter.mp hd).1
      apply bumpTerm_eq_of
      · rw [hcolN d hdx, hbumpN _ hqx]
      · intro hb
        rw [hchN d hdx]
        apply List.map_congr_left
        intro e he
        have hex : e < r + L := by
          have hel := (mem_children he).2
          by_contra h'
          have hex' : e = r + L := by omega
          have h'' := (mem_children_iff.mp he).2
          rw [hex', hp] at h''
          have hdq : d = r + qp := (Option.some.inj h'').symm
          have := (mem_children hdM).1
          omega
        exact (hoff e hex).1 (hqL d hdM hb e he)
    · unfold bumpTerm; rw [if_pos hxb, children_last_nil hlen]; exact omega_z
    · unfold bumpTerm
      rw [if_neg]
      intro hb
      have := e2_of_col (show col (TRIO.gexp M r L d0 d1 n) (r + L) = (entry (TRIO.gexp M r L d0 d1 n) 0 (r + qp) + 1, entry (TRIO.gexp M r L d0 d1 n) 1 (r + qp), 1) from hb)
      omega
  have hCLnil : ∀ c, c < r + L → ¬ WQ (r + qp) true c → CL M c = [] → CL (TRIO.gexp M r L d0 d1 n) c = [] := by
    intro c hc hw hcl
    by_cases hcpq : c = pq
    · exact (hpqCL (by rw [← hcpq]; exact hcl)).elim
    · have hcq : c ≠ r + qp := fun h => hw ⟨rfl, h⟩
      unfold CL at hcl ⊢
      rw [hchN c hc, ← hcl]
      apply List.filter_congr
      intro d hd
      have hdx : d < r + L := by
        have := (mem_children hd).2
        by_contra h'
        exact hcq (hxc c d hd (by omega)).2
      simp only [hcntS c d hc hcpq hd hdx]
  have hSeed : ∀ b i, SQ (r + qp) pq b i → i < r + L → DepS M (SQ (r + qp) pq) b i →
      (∀ i, i < r + L → (¬ DepS M (SQ (r + qp) pq) true i → σ.o i = ρ.o i) ∧
        (¬ DepS M (SQ (r + qp) pq) false i → σ.v i = ρ.v i)) →
      (∀ b' i', rkM b' i' < rkM b i → DepS M (SQ (r + qp) pq) b' i' → i' < r + L →
        ¬ WQ (r + qp) b' i' → Lhd z (valB σ b' i') (valB ρ b' i') ∧ isOT (valB σ b' i') = true) →
      Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true := by
    rintro b i (⟨hb, hi'⟩ | ⟨hb, hi'⟩) _ _ _ _
    · subst hb; rw [hi']; exact ⟨hvq, hvqot⟩
    · subst hb; rw [hi']
      exact hseed
  exact t2_assembleOT (S := SQ (r + qp) pq) (W := WQ (r + qp)) (bnd := r + L) hC hG hRM hCN hRN
    hF hFO hVS hTD hKD hlen (by rw [hlN]; omega) hchN
    (Or.inr ⟨rfl, rfl⟩) (Or.inr (Or.inl ⟨rfl, rfl⟩)) (fun i hq hb => by have h' := (mem_children_iff.mp hq).2; rw [hpq] at h'; cases h'; exact hqb hb)
    (fun y i hi => entry_gexp_pre hlen (by omega) y hi) (fun i hi => par_gexp_pre hlen (by omega) 1 hi)
    (fun i hi _ => hupgN i hi)
    (fun i c hi hd hc hcx => hcntS i c hi (fun h => hd (Or.inr ⟨rfl, h⟩)) hc hcx)
    (fun i c hi hc hcx => by obtain ⟨_, rfl⟩ := hxc i c hc hcx; exact Or.inr ⟨rfl, rfl⟩)
    (fun i k hi hk hkx => (upg_not_x hlen hA hp hxb hBE hk hkx hi).elim)
    hbjN
    (fun i j hi hj hjx _ => by obtain ⟨_, rfl⟩ := hxc i j hj hjx; exact Or.inl ⟨rfl, rfl⟩)
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc j k hk hkx
      have h' := (mem_children_iff.mp hj).2; rw [hpq] at h'; cases h'
      exact absurd hjb hqb)
    (fun i h => by obtain ⟨-, hi⟩ := h; rw [hi]; exact DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i h => by cases h.1)
    (fun i c hc _ h => by
      obtain ⟨-, hc'⟩ := h
      have h' := (mem_children_iff.mp hc).2; rw [hc', hpq] at h'; cases h'
      exact Or.inr ⟨rfl, rfl⟩)
    (fun i j c _ _ hj hjb hc h => by
      obtain ⟨-, hc'⟩ := h
      have h' := (mem_children_iff.mp hc).2; rw [hc', hpq] at h'; cases h'
      have := e2_of_col (show col M _ = (entry M 0 i + 1, entry M 1 i, 1) from hjb)
      omega)
    (fun c hc _ _ hd => hDvNil c hc hd) (fun c hc hw _ hd => hCLnil c hc hw (hDvNil c hc hd))
    hCLnil hOS hVSh hAbs hSeed hVSN hHA
    (fun i h => by rcases h with h | h; exact absurd h.1 (by decide); exact h.2) hOTout
    (fun _ i _ h => by obtain ⟨-, hi⟩ := h; rw [hi]; exact hqot)
    (fun _ i _ hs => by
      rcases hs with (⟨h, _⟩ | ⟨_, hi⟩) | ⟨_, hi⟩
      · cases h
      · rw [hi]; exact hsdec
      · rw [hi]; exact hqdec)


end

end Ytosk
