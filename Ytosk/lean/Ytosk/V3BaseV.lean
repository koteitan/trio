/-
**基底 Mlen L の評価（明示的な値）と依存の順位。**

値は Ω の塔 P^k(β)（P(t) = ψ_t(0)）。β は最後のブロックの形で決まる: L ≡ 1 (mod 3)（SRO[n]）なら β = 1、
L ≡ 0 (mod 3)（SRO[n] の最後の列を落としたもの）なら β = ω²。K(i) を i より後ろの D の列の数として
- A・D の列: v = P^{K(i)}(β)、o = P^{K(i)+1}(β)
- B の列: v = ω、o = ψ_ω(o(i+1))（子がなければ ψ_ω(0)）
- 根: v = 0、o = ψ_0(o(1))（L = 1 なら 1）
順位は列の番号が右ほど小さい（根の v だけ 0）。
-/
import Ytosk.V3BaseM

namespace Ytosk

open T

/-! ## Ω の塔 -/

/-- `P^k(β)` with `P(t) = ψ_t(0)`. -/
def tw (β : T) : Nat → T
  | 0 => β
  | k + 1 => psi (tw β k) z z

/-- `ω`. -/
def wT : T := psi z one z

/-- `ω²`. -/
def w2 : T := psi z two z

/-- The admissible bases. -/
def GoodBase (β : T) : Prop := β = one ∨ β = w2

section
variable {β : T} (hβ : GoodBase β)
include hβ

theorem GoodBase.ne_z : β ≠ z := by rcases hβ with rfl | rfl <;> decide

theorem GoodBase.ot : isOT β = true := by rcases hβ with rfl | rfl <;> decide

theorem tw_ne_z : ∀ k, tw β k ≠ z
  | 0 => hβ.ne_z
  | _ + 1 => by simp [tw]

theorem isOT_tw : ∀ k, isOT (tw β k) = true
  | 0 => hβ.ot
  | k + 1 => by
    have := isOT_tw k
    simp [tw, isOT, comps, this]

theorem sf_tw (k : Nat) : sf (tw β k) = tw β k := sf_ot (isOT_tw hβ k)

theorem last_tw : ∀ k, last (tw β k) = tw β k
  | 0 => by rcases hβ with rfl | rfl <;> decide
  | _ + 1 => rfl

theorem omega_tw_succ (k : Nat) : omega (tw β (k + 1)) = tw β (k + 1) := by
  apply omega_psi_fix (isOT_tw hβ k)
  rw [E0, psi_lt_psi_z_iff]
  have hne := tw_ne_z hβ k
  rintro (h | ⟨h, _⟩)
  · cases hk : tw β k with
    | z => exact hne hk
    | psi a b c => rw [hk] at h; exact absurd h (by simp [lt_iff_lt, lt])
  · exact hne h

/-- The components of a tower are `0` or `2`. -/
theorem comps_tw (u : T) : ∀ k, ∀ g ∈ comps u (tw β k), g = z ∨ (g = two ∧ β = w2)
  | 0, g, hg => by
    rcases hβ with rfl | rfl
    · left
      simp only [tw, one, comps] at hg
      split_ifs at hg <;> simp at hg <;> exact hg
    · simp only [tw, w2, two, one, comps] at hg
      split_ifs at hg with h1
      · simp at hg
      · simp at hg
        rcases hg with h | h
        · right; exact ⟨h, rfl⟩
        · left; exact h
  | k + 1, g, hg => by
    simp only [tw, comps] at hg
    split_ifs at hg
    · simp at hg
    · simp at hg
      rcases hg with h | h
      · left; exact h
      · exact comps_tw u k g h

theorem z_lt_tw (k : Nat) : z < tw β k := by
  have := tw_ne_z hβ k
  cases h : tw β k with
  | z => exact absurd h this
  | psi a b c => exact T.z_lt_psi _ _ _

theorem two_lt_tw (h : β = w2) : ∀ k, two < tw β k
  | 0 => by subst h; decide
  | k + 1 => by
    show two < psi (tw β k) z z
    unfold two
    rw [psi_lt_psi]
    left
    exact z_lt_tw hβ k

theorem comps_tw_lt (u : T) (k : Nat) : ∀ g ∈ comps u (tw β k), g < tw β k := by
  intro g hg
  rcases comps_tw hβ u k g hg with rfl | ⟨rfl, h⟩
  · exact z_lt_tw hβ k
  · exact two_lt_tw hβ h k

theorem isOT_psi_tw (a : T) (ha : isOT a = true) (k : Nat) : isOT (psi a (tw β k) z) = true := by
  rw [isOT_psi_iff]
  exact ⟨ha, isOT_tw hβ k, rfl, z_le _, comps_tw_lt hβ a k⟩

end

/-! ## 和 -/

theorem sumN_cons_zeros {x : T} (hx : isOT x = true) :
    ∀ {l : List T}, (∀ t ∈ l, t = z) → sumN (x :: l) = x := by
  intro l hl
  unfold sumN
  simp only [List.foldl_cons, add_z_left, sf_ot hx]
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [hl a (by simp)]
    simp only [List.foldl_cons, add_z_right, sf_ot hx]
    exact ih (fun s hs => hl s (List.mem_cons_of_mem _ hs))

theorem sumN_single {x : T} (hx : isOT x = true) : sumN [x] = x :=
  sumN_cons_zeros hx (by simp)

/-! ## 評価 -/

/-- The number of `D` columns after `i`. -/
def Kd (L i : Nat) : Nat := (L - 1) / 3 - i / 3

/-- The valuation of `Mlen L` with base `β`. -/
def bval (L : Nat) (β : T) : Valn where
  o i := if i = 0 then psi z (if 1 < L then tw β (Kd L 1 + 1) else z) z
    else if (i - 1) % 3 = 1 then psi wT (if i + 1 < L then tw β (Kd L (i + 1) + 1) else z) z
    else tw β (Kd L i + 1)
  v i := if i = 0 then z else if (i - 1) % 3 = 1 then wT else tw β (Kd L i)

/-- The base fits the length. -/
def BaseFit (L : Nat) (β : T) : Prop := (L % 3 = 1 ∧ β = one) ∨ (L % 3 = 0 ∧ β = w2)

theorem BaseFit.good {L : Nat} {β : T} (h : BaseFit L β) : GoodBase β := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

section
variable {L : Nat} {β : T}

theorem bval_v0 : (bval L β).v 0 = z := rfl

theorem vOpt_par1 (i : Nat) : vOpt (bval L β) (par (Mlen L) 1 i) = z := by
  rcases Nat.lt_or_ge i L with hi | hi
  · rcases Nat.eq_zero_or_pos i with h | h
    · subst h; rw [Mlen_par1_0]; rfl
    · rw [Mlen_par1 hi h]; rfl
  · cases hp : par (Mlen L) 1 i with
    | none => rfl
    | some m =>
      exfalso
      have hmi := par_lt _ 1 i m hp
      obtain ⟨p, hp0, _⟩ := anc0_par_exists (anc0_of_par _ 1 m i hp) (by omega)
      exact par0_out (by simpa using hi) hp0

theorem bval_o0 : (bval L β).o 0 = psi z (if 1 < L then tw β (Kd L 1 + 1) else z) z := rfl

theorem bval_oAD {i : Nat} (h0 : i ≠ 0) (hk : (i - 1) % 3 ≠ 1) :
    (bval L β).o i = tw β (Kd L i + 1) := by
  show (if i = 0 then _ else _) = _
  rw [if_neg h0, if_neg hk]

theorem bval_oB {i : Nat} (h0 : i ≠ 0) (hk : (i - 1) % 3 = 1) :
    (bval L β).o i = psi wT (if i + 1 < L then tw β (Kd L (i + 1) + 1) else z) z := by
  show (if i = 0 then _ else _) = _
  rw [if_neg h0, if_pos hk]

theorem bval_vAD {i : Nat} (h0 : i ≠ 0) (hk : (i - 1) % 3 ≠ 1) :
    (bval L β).v i = tw β (Kd L i) := by
  show (if i = 0 then _ else _) = _
  rw [if_neg h0, if_neg hk]

theorem bval_vB {i : Nat} (h0 : i ≠ 0) (hk : (i - 1) % 3 = 1) : (bval L β).v i = wT := by
  show (if i = 0 then _ else _) = _
  rw [if_neg h0, if_pos hk]

theorem cnt_root {c : Nat} (hc : c ∈ children (Mlen L) 0) :
    cnt (Mlen L) (bval L β) 0 c = if c = 1 then (bval L β).o 1 else z := by
  classical
  rw [cnt_eq_ite]
  have := Mlen_counted hc
  by_cases h1 : c = 1
  · subst h1; rw [if_pos (this.mpr (Or.inl ⟨rfl, rfl⟩)), if_pos rfl]
  · rw [if_neg (fun h => by have := this.mp h; omega), if_neg h1]

/-- **The valuation satisfies the evaluator's equations.** -/
theorem bval_cons (hF : BaseFit L β) : Cons (Mlen L) (bval L β) := by
  classical
  have hβ := hF.good
  intro i hi
  rw [Mlen_length] at hi
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · -- the root
    subst h0
    refine ⟨?_, by unfold vRhs; rw [Mlen_e1 hi, if_pos rfl]; rfl⟩
    unfold oRhs
    rw [bval_o0, bval_v0]
    by_cases hL : 1 < L
    · obtain ⟨t, ht, htm⟩ := Mlen_children_0 hL
      have ho1 : (bval L β).o 1 = tw β (Kd L 1 + 1) := bval_oAD one_ne_zero (by decide)
      rw [ht, List.map_cons, cnt_root (by rw [ht]; simp), if_pos rfl, ho1]
      rw [sumN_cons_zeros (isOT_tw hβ _) (by
          intro s hs
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
          rw [cnt_root (by rw [ht]; exact List.mem_cons_of_mem _ hc),
            if_neg (by have := htm c hc; omega)])]
      rw [if_pos hL, sf_ot (isOT_psi_tw hβ z rfl _)]
    · rw [Mlen_children_nil (Or.inl (by omega)), List.map_nil, sumN_nil, if_neg hL]
      decide
  -- the other columns
  have hi0 : i ≠ 0 := by omega
  have e1 : entry (Mlen L) 1 i = 1 := by rw [Mlen_e1 hi, if_neg hi0]
  have hk3 : (i - 1) % 3 = 0 ∨ (i - 1) % 3 = 1 ∨ (i - 1) % 3 = 2 := by omega
  rcases hk3 with hk | hk | hk
  · -- A
    have e2 : entry (Mlen L) 2 i = 1 := by rw [Mlen_e2 hi, if_neg hi0, if_neg (by omega)]
    have hi1 : i + 1 < L := by
      rcases hF with ⟨hL, _⟩ | ⟨hL, _⟩ <;> omega
    have hch := Mlen_children_AB hi1 h0 (by omega)
    have hb : col (Mlen L) (i + 1) = bump (Mlen L) i := (Mlen_col_eq_bump hi1 h0 rfl).mpr hk
    have hvi : (bval L β).v i = tw β (Kd L i) := bval_vAD hi0 (by omega)
    refine ⟨?_, ?_⟩
    · unfold oRhs
      rw [hch, List.map_cons, List.map_nil]
      unfold cnt; rw [if_pos hb, sumN_single rfl, hvi, bval_oAD hi0 (by omega)]
      rw [show psi (tw β (Kd L i)) z z = tw β (Kd L i + 1) from rfl, sf_tw hβ]
    · unfold vRhs
      rw [e1, e2, if_neg one_ne_zero, if_neg one_ne_zero, vOpt_par1, add_z_left, hch,
        List.map_cons, List.map_nil, hvi]
      unfold bumpTerm; rw [if_pos hb]
      by_cases hi2 : i + 2 < L
      · rw [Mlen_children_AB (i := i + 1) (by omega) (by omega) (by omega), List.map_cons,
          List.map_nil]
        have hoD : (bval L β).o (i + 1 + 1) = tw β (Kd L i) := by
          rw [bval_oAD (by omega) (by omega)]
          congr 1; unfold Kd; omega
        obtain ⟨k, hk'⟩ : ∃ k, Kd L i = k + 1 := ⟨Kd L i - 1, by unfold Kd; omega⟩
        rw [hoD, hk', sumN_single (isOT_tw hβ _), omega_tw_succ hβ,
          sumN_one_cons_gt ⟨isOT_tw hβ _, tw β k, z, rfl⟩ (by
            show one < psi (tw β k) z z
            unfold one; rw [psi_lt_psi]; left; exact z_lt_tw hβ k),
          sumN_single (isOT_tw hβ _), omega_tw_succ hβ, sf_tw hβ]
      · -- the partial last block: `β = ω²`
        have hb2 : β = w2 := by rcases hF with ⟨hL, _⟩ | ⟨_, h⟩ <;> [omega; exact h]
        rw [Mlen_children_nil (i := i + 1) (Or.inl (by omega)), List.map_nil, sumN_nil]
        have hK : Kd L i = 0 := by unfold Kd; omega
        rw [hK, hb2]
        decide
  · -- B
    have e2 : entry (Mlen L) 2 i = 1 := by rw [Mlen_e2 hi, if_neg hi0, if_neg (by omega)]
    have hvi : (bval L β).v i = wT := bval_vB hi0 hk
    have hnb : ∀ j, j = i + 1 → j < L → col (Mlen L) j ≠ bump (Mlen L) i := by
      intro j hj hjL h
      exact absurd ((Mlen_col_eq_bump hjL h0 hj).mp h) (by omega)
    refine ⟨?_, ?_⟩
    · unfold oRhs
      rw [hvi, bval_oB hi0 hk]
      by_cases hi1 : i + 1 < L
      · rw [Mlen_children_AB hi1 h0 (by omega), List.map_cons, List.map_nil, cnt_eq_ite,
          if_pos ((Mlen_counted (by rw [Mlen_children_AB hi1 h0 (by omega)]; simp)).mpr
            (Or.inr ⟨h0, hk⟩)), bval_oAD (by omega) (by omega),
          sumN_single (isOT_tw hβ _), sf_ot (isOT_psi_tw hβ wT rfl _), if_pos hi1]
      · rw [Mlen_children_nil (Or.inl (by omega)), List.map_nil, sumN_nil, if_neg hi1]
        decide
    · unfold vRhs
      rw [e1, e2, if_neg one_ne_zero, if_neg one_ne_zero, vOpt_par1, add_z_left, hvi]
      by_cases hi1 : i + 1 < L
      · rw [Mlen_children_AB hi1 h0 (by omega), List.map_cons, List.map_nil]
        unfold bumpTerm; rw [if_neg (hnb (i + 1) rfl hi1)]
        decide
      · rw [Mlen_children_nil (Or.inl (by omega)), List.map_nil]
        decide
  · -- D
    have e2 : entry (Mlen L) 2 i = 0 := by rw [Mlen_e2 hi, if_neg hi0, if_pos hk]
    have hvi : (bval L β).v i = tw β (Kd L i) := bval_vAD hi0 (by omega)
    refine ⟨?_, ?_⟩
    · unfold oRhs
      rw [Mlen_children_nil (Or.inr (Or.inl ⟨h0, hk⟩)), List.map_nil, sumN_nil, hvi,
        bval_oAD hi0 (by omega)]
      rw [show psi (tw β (Kd L i)) z z = tw β (Kd L i + 1) from rfl, sf_tw hβ]
    · unfold vRhs
      rw [e1, e2, if_neg one_ne_zero, if_pos rfl, vOpt_par1, add_z_left, hvi]
      by_cases hi1 : i + 1 < L
      · rw [Mlen_upg_D hi1 h0 hk]
        simp only
        have hvA : (bval L β).v (i + 1) = tw β (Kd L i) := by
          rw [bval_vAD (by omega) (by omega)]
          congr 1; unfold Kd; omega
        rw [hvA, last_tw hβ, sf_tw hβ]
      · rw [Mlen_upg_none (by omega)]
        simp only
        have hb1 : β = one := by rcases hF with ⟨_, h⟩ | ⟨hL, _⟩ <;> [exact h; omega]
        have hK : Kd L i = 0 := by unfold Kd; omega
        rw [hK, hb1]
        decide

/-! ## 順位 -/

/-- The ranking: right columns rank lower; `v(0)` ranks lowest. -/
def brk (L : Nat) : Bool → Nat → Nat
  | true, i => 2 * (L - i) + 1
  | false, i => if i = 0 then 0 else 2 * (L - i)

theorem brk_rk {L' : Nat} (hL : L' ≤ L) : Rk (Mlen L') (brk L) := by
  intro i hi
  rw [Mlen_length] at hi
  refine ⟨?_, fun c hc _ _ => ?_, fun h1 => ⟨fun m hm => ?_, fun _ k hk => ?_,
    fun _ j hj _ k hk => ?_⟩⟩
  · simp only [brk]; split_ifs <;> omega
  · have := (mem_children hc); rw [Mlen_length] at this
    simp only [brk]; omega
  · have hi0 : i ≠ 0 := by intro h; subst h; rw [Mlen_e1 hi, if_pos rfl] at h1; exact h1 rfl
    rw [Mlen_par1 hi (Nat.pos_of_ne_zero hi0)] at hm; cases hm
    simp only [brk, if_neg hi0, ↓reduceIte]; omega
  · have := Mlen_upg_iff.mp hk
    simp only [brk, if_neg (show i ≠ 0 by omega), if_neg (show k ≠ 0 by omega)]; omega
  · have hi0 : i ≠ 0 := by intro h; subst h; rw [Mlen_e1 hi, if_pos rfl] at h1; exact h1 rfl
    have h1' := (mem_children hj); have h2' := (mem_children hk)
    rw [Mlen_length] at h1' h2'
    simp only [brk, if_neg hi0]; omega

end

end Ytosk
