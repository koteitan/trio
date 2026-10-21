/-
**最初でない数える子の添字の成分は前の状態で押さえられる（SubB、2026-10-21、lead）。**

`SubB N σ`: 列 k の数える子 c が最初でない（CL N k = Lc ++ c :: R、Lc ≠ []）とき、すべての段 u ≤ v(k) で
v(c) の成分は 0・前の状態 B = spArg v(k) 0 (Σ o(Lc)) 以下・v(k) の成分以下。
測定（tmp/claude/ntsub2.py）: std_a・d3s・Cprime・ext1 の約 100 万枠で例外 0。最初の子では偽。数えない子に広げても偽。

t = 2 の qn の残り `T2SeedQNDom1` は M の SubB から出る（`t2SeedQNDom1_of_subB`）:
s′ = V + ω^S と v(q) = V + ω^{S+1} で、s′ の成分は V の成分か v(q) の成分以下（`comps_add_omega_succ`）。
-/
import Ytosk.V3T2SeedQNK
import Ytosk.V3T0B

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Value property**: the components of a non-first counted child's subscript are `0`, below the state before
it, or below a component of the parent's subscript, at every level `u ≤ v(k)`. -/
def SubB (N : Mat) (σ : Valn) : Prop :=
  ∀ k (Lc : List Nat) c (R : List Nat), CL N k = Lc ++ c :: R → Lc ≠ [] →
    ∀ u, ¬ lt (σ.v k) u = true → ∀ g ∈ comps u (σ.v c),
      g = z ∨ g ≤ spArg (σ.v k) z (sumN (Lc.map σ.o)) ∨ ∃ d ∈ comps u (σ.v k), g ≤ d

/-- **Candidate residual**: every standard matrix has `SubB`. -/
def HSubB : Prop := ∀ N σ, Std N → Cons N σ → Good3 N σ → SubB N σ

/-- The components of `W` are components of `V + W`. -/
theorem comps_add_right (u : T) : ∀ (V W : T), ∀ g ∈ comps u W, g ∈ comps u (add V W)
  | z, W, g, hg => by show g ∈ comps u W; exact hg
  | psi a b c, z, g, hg => by simp [comps] at hg
  | psi a b c, psi d e f, g, hg => by
    rw [add_psi_psi]
    split
    · exact hg
    · simp only [comps, List.mem_append]; exact Or.inr (comps_add_right u c (psi d e f) g hg)

/-- **The components of `ω^G` are below those of `ω^{G+1}`.** -/
theorem comps_omega_succ {G : T} (hG : isOT G = true) (u : T) :
    ∀ g ∈ comps u (omega G), ∃ h ∈ comps u (omega (app G one)), g ≤ h := by
  obtain ⟨s, b', h1, h2⟩ := omega_succ_form hG
  intro g hg
  rw [h1] at hg; rw [h2]
  by_cases hsu : lt s u = true
  · simp [comps, hsu] at hg
  · simp only [comps, hsu, Bool.false_eq_true, if_false, List.append_nil, List.mem_cons,
      List.mem_append] at hg ⊢
    rcases hg with rfl | hg | hg
    · exact ⟨app g one, Or.inl rfl, le_of_lt (lt_app_one g)⟩
    · exact ⟨g, Or.inr (Or.inl (by rw [comps_app]; exact List.mem_append_left _ hg)), le_refl _⟩
    · exact ⟨g, Or.inr (Or.inr hg), le_refl _⟩

/-- **`V + ω^G` against `V + ω^{G+1}`**: a component is one of `V` or below one of `V + ω^{G+1}`. -/
theorem comps_add_omega_succ {V G : T} (hG : isOT G = true) (u : T) :
    ∀ g ∈ comps u (add V (omega G)), g ∈ comps u V ∨ ∃ h ∈ comps u (add V (omega (app G one))), g ≤ h := by
  intro g hg
  rcases comps_add u V _ g hg with h | h
  · exact Or.inl h
  · obtain ⟨h', hh', hle⟩ := comps_omega_succ hG u g h
    exact Or.inr ⟨h', comps_add_right u V _ h' hh', hle⟩

/-- **`v(q) = V + ω^{S+1}`** (qn; `s′ = qnS = V + ω^S`). -/
theorem qn_vq_eq {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) :
    ρ.v q = add (ρ.v r) (omega (app (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
      (bumpTerm M ρ q))) one)) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 q r hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, _, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he2q : entry M 2 q = 1 := I.be q (r + L) hxq Txb
  have he1q : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  have h1lt := (par2_facts I.z2 (show r + L < M.length by omega) hr).2
  have hp1q : par M 1 q = some r := par1_of_child hpq (by omega)
  have hsplit := split_last_max _ _ (children_sorted M q) hxq
    (fun d hd => by have := (mem_children hd).2; omega)
  set Lq := (children M q).filter (fun d => decide (d < r + L)) with hLqd
  have hbx : bumpTerm M ρ q (r + L) = one := by
    unfold bumpTerm; rw [if_pos Txb, children_last (by omega)]; rfl
  have hqM : q < M.length := by omega
  have hv := (I.cons q hqM).2
  unfold vRhs at hv
  rw [if_neg (by omega), if_neg (by omega), hp1q, hsplit, List.map_append, List.map_singleton, hbx] at hv
  change ρ.v q = sf (add (ρ.v r) (omega (sumN (one :: (Lq.map (bumpTerm M ρ q) ++ [one]))))) at hv
  set S := sumN (one :: Lq.map (bumpTerm M ρ q)) with hSdef
  have hOT : ∀ t ∈ one :: Lq.map (bumpTerm M ρ q), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm I.good q d
  have hSot : isOT S = true := isOT_sumN _ hOT
  have hS1 : sumN (one :: (Lq.map (bumpTerm M ρ q) ++ [one])) = sf (add S one) := by
    simp only [hSdef, sumN, List.foldl_cons, List.foldl_append, List.foldl_nil]
  rw [hS1] at hv
  have hA1 : isOT (add S one) = true := isOT_add hSot rfl
  rw [sf_ot hA1] at hv
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  have hW : isOT (add (ρ.v r) (omega (add S one))) = true := isOT_add hVot (isOT_omega hA1)
  rw [sf_ot hW, add_one_eq_app] at hv
  exact hv

/-- **`T2SeedQNDom1` from `SubB` of `M`** at the frame `(r, Lc, q)`. -/
theorem t2SeedQNDom1_of_subB {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (hSB : SubB M ρ) {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCL : CL M r = Lc ++ [q]) :
    T2SeedQNDom1 M ρ r L q Lc := by
  intro hL u hu g hg
  have hOT : ∀ t ∈ one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q),
      isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm I.good q d
  rcases comps_add_omega_succ (isOT_sumN _ hOT) u g hg with h | ⟨h', hh', hle⟩
  · exact Or.inr (Or.inr ⟨g, h, le_refl _⟩)
  · rw [← qn_vq_eq hM hS I hlen hr hq hqr] at hh'
    rcases hSB r Lc q [] hCL hL u hu h' hh' with h0 | hB | ⟨d, hd, hdle⟩
    · subst h0
      left
      rcases (le_iff _ _).mp hle with h | h
      · exact absurd h (T.not_lt_z _)
      · exact h
    · exact Or.inr (Or.inl (le_trans hle hB))
    · exact Or.inr (Or.inr ⟨d, hd, le_trans hle hdle⟩)

end Ytosk

#print axioms Ytosk.t2SeedQNDom1_of_subB
