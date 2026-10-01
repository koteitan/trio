/-
**F1（行 1 の親の行 1 はちょうど 1 小さい）は trio 本体の不変条件 r1ok・z0ok から出る。**

r1ok・z0ok は展開で保たれる（trio 本体の `r1ok_oper`・`z0ok_oper`）。r1ok から行 1 の +1 規律（`nextrel1_snd_succ`）、
行 1 の親の存在は「行 0 の祖先をたどると行 0 が 0（z0ok で行 1 も 0）の列に着く」ことから。
-/
import Ytosk.TwoRowW
import Invariant

namespace Ytosk

open T

/-- `climb` finds something when some point of the chain passes the test. -/
theorem climb_ne_none {s : Nat → Option Nat} (hs : ∀ q q', s q = some q' → q' < q) {ok : Nat → Bool} :
    ∀ f q, q < f → (∃ a, Relation.ReflTransGen (StepRel s) a q ∧ ok a = true) →
      climb s ok f (some q) ≠ none
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, q, hqf, ⟨a, ha, hok⟩ => by
    simp only [climb]
    split
    · simp
    · rename_i hq
      rcases Relation.ReflTransGen.cases_tail ha with h | ⟨c, hc1, hc2⟩
      · subst h; exact absurd hok hq
      · unfold StepRel at hc2
        rw [hc2]
        exact climb_ne_none hs f c (by have := hs q c hc2; omega) ⟨a, hc1, hok⟩

theorem entry_getD (M : Mat) (j : Nat) :
    (M.getD j (0, 0, 0)).1 = entry M 0 j ∧ (M.getD j (0, 0, 0)).2.1 = entry M 1 j := ⟨rfl, rfl⟩

/-- Under `r1ok`, a column with positive row 0 has a row-0 parent. -/
theorem par0_some_r1ok {M : Mat} (hr1 : TRIO.r1ok M) {j : Nat} (hj : j < M.length)
    (h0 : 0 < entry M 0 j) : ∃ k, par M 0 j = some k ∧ entry M 0 k + 1 = entry M 0 j := by
  obtain ⟨k, hkj, hk, hbet, _⟩ := hr1 j hj h0
  refine ⟨k, ?_, hk⟩
  rw [par0_spec]
  refine ⟨hkj, by change (M.getD k (0,0,0)).1 < (M.getD j (0,0,0)).1 at *; omega, fun l h1 h2 => hbet l h1 h2⟩

/-- **F1 from the trio invariants.** -/
theorem F1_of_trio {M : Mat} (hr1 : TRIO.r1ok M) (hz0 : TRIO.z0ok M) : F1 M := by
  intro j hj1
  have hj : j < M.length := by
    by_contra h
    have : entry M 1 j = 0 := by
      unfold entry; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    omega
  -- `j` has positive row 0 (else z0ok makes row 1 zero)
  have h0 : 0 < entry M 0 j := by
    rcases Nat.eq_zero_or_pos (entry M 0 j) with h | h
    · have := (hz0 j hj h).1; change entry M 1 j = 0 at this; omega
    · exact h
  -- an ancestor with row 0 equal to 0
  have hanc : ∀ e c, entry M 0 c ≤ e → c < M.length → Anc0 M c j →
      ∃ a, Anc0 M a j ∧ a < j ∧ entry M 1 a < entry M 1 j := by
    intro e
    induction e with
    | zero =>
      intro c hc hcl hcA
      have hc0 : entry M 0 c = 0 := by omega
      have hcj : c ≠ j := by intro h; subst h; omega
      refine ⟨c, hcA, lt_of_le_of_ne hcA.le hcj, ?_⟩
      have := (hz0 c hcl hc0).1; change entry M 1 c = 0 at this; omega
    | succ e ih =>
      intro c hc hcl hcA
      rcases Nat.eq_zero_or_pos (entry M 0 c) with h | h
      · exact ih c (by omega) hcl hcA
      · obtain ⟨k, hk, hke⟩ := par0_some_r1ok hr1 hcl h
        have hkc := par_lt M 0 c k hk
        exact ih k (by omega) (by omega) (anc0_up hk hcA)
  obtain ⟨a, haA, haj, hae⟩ := hanc _ j (Nat.le_refl _) hj (Anc0.refl j)
  obtain ⟨k, hk, _⟩ := par0_some_r1ok hr1 hj h0
  have hkj := par_lt M 0 j k hk
  have hak : Anc0 M a k := anc0_par haA (by omega) hk
  have hpar : par M 1 j = climb (par M 0) (fun q => decide (entry M 1 q < entry M 1 j)) (j + 1)
      (par M 0 j) := rfl
  have hne : par M 1 j ≠ none := by
    rw [hpar, hk]
    exact climb_ne_none (par_lt M 0) (j + 1) k (by omega) ⟨a, rtg_of_anc0 hak, by simpa using hae⟩
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hne
  refine ⟨m, hm, ?_⟩
  have := TRIO.nextrel1_snd_succ hr1 ((par1_iff M hj).mp hm)
  change entry M 1 j = entry M 1 m + 1 at this
  omega

/-- F1 for every expansion. -/
theorem F1_expand {M : Mat} (hr1 : TRIO.r1ok M) (hz0 : TRIO.z0ok M) (hM : 2 ≤ M.length) (k : Nat) :
    F1 (expand M k) := by
  rw [expand_eq_oper M k hM]
  exact F1_of_trio (TRIO.r1ok_oper hr1) (TRIO.z0ok_oper hz0)

/-- **The two-row `t = 1`, `q ≠ r` chain with F1 from the trio invariants.** Remaining hypothesis: W2. -/
theorem twoRow_chain_trio {M : Mat} {r q : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hG : Good2 M) (hb1 : 0 < entry M 1 (M.length - 1))
    (hr1 : TRIO.r1ok M) (hz0 : TRIO.z0ok M)
    (hq : par M 0 (M.length - 1) = some q) (hqμ : lt (vr M r) (vr M q) = true)
    (hc1 : o2r (expand M 1) r = psi (vr M r) (fs (argOf (o2r M r)) z) z)
    (hW2 : ∀ h p s y, Anc0 M p (M.length - 1) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true → bst M h p ≤ fsD y z) :
    ∀ k, 2 ≤ k →
      o2r (expand M k) r = gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) (k - 1) ∧
      ∀ h, Anc0 M h (M.length - 1) →
        o2r (expand M k) h =
          fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) (k - 2)) :=
  twoRow_chain_gam hM hz hr ht1 hG hb1 hq hqμ (fun k _ => F1_expand hr1 hz0 hM k) hc1 hW2

end Ytosk
