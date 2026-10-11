/-
**基底 Mlen L の評価は Inv3 の値の不変条件を満たす。**

ほとんどの項目は次の 3 つで片づく:
- 引き金が立たない（`no_trig`）: 子 c の o(c) = ψ_s(y) は、A・D の子なら y = 0、A の下の B なら
  ψ_{v(i)}(0) > ψ_ω(y)（v(i) は Ω の塔か ω²）。
- 行 1 の親の値が 0（`vOpt_par1`）: AbsD・AbsU などの「吸収」は空。
- 子は高々 1 つ（根を除く）、根の数える子は 1 だけ: 並びの単調性は自明。
TPLo だけは中身がある: 穴のある a = P^{k+1}(1) では fsD(a, η) = P^k(η) で、これは 1 や ω+1 より小さくない。
-/
import Ytosk.V3BaseV
import Ytosk.V3TopB

namespace Ytosk

open T

/-! ## 項の補題 -/

theorem lt_z_false (x : T) : lt x z = false := by cases x <;> rfl

theorem pairwise_short {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.length ≤ 1 → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | _ :: _ :: _, h => by simp at h

theorem nzs_length_le (l : List T) : (nzs l).length ≤ l.length := List.length_filter_le _ _

/-- The tower over `η`. -/
theorem tw_ne_z_of {η : T} (hη : η ≠ z) : ∀ k, tw η k ≠ z
  | 0 => hη
  | _ + 1 => by simp [tw]

theorem fsD_tw_one (η : T) : ∀ k, fsD (tw one (k + 1)) η = tw η k
  | 0 => by simp [tw, fsD, isSucc, last, one]
  | k + 1 => by
    show fsD (psi (tw one (k + 1)) z z) η = psi (tw η k) z z
    have hne : tw one (k + 1) ≠ z := by show psi _ z z ≠ z; intro h; cases h
    have hs : isSucc (tw one (k + 1)) = false := by
      show (last (psi (tw one k) z z) == one) = false
      simp only [last, one, beq_iff_eq, T.psi.injEq, and_true]
      simp only [beq_eq_false_iff_ne, ne_eq, T.psi.injEq, and_true]
      exact tw_ne_z (Or.inl rfl) k
    simp only [fsD, if_true, if_neg hne, hs, Bool.false_eq_true, if_false]
    rw [fsD_tw_one η k]

theorem ohole_tw {β : T} (hβ : GoodBase β) : ∀ k, OHole (tw β k) → β = one ∧ 1 ≤ k
  | 0, h => by
    rcases hβ with rfl | rfl
    · simp [tw, OHole, one] at h
    · simp [tw, OHole, w2, two, isSucc, last, one] at h
  | k + 1, h => by
    simp only [tw, OHole, if_true] at h
    obtain ⟨_, h | h⟩ := h
    · rcases k with _ | k
      · rcases hβ with rfl | rfl
        · exact ⟨rfl, le_rfl⟩
        · simp [tw, w2, two, isSucc, last, one] at h
      · simp [tw, isSucc, last, one] at h
        exact absurd h (tw_ne_z hβ k)
    · exact ⟨(ohole_tw hβ k h).1, by omega⟩

theorem cof_tw_one : ∀ k, cof (tw one (k + 1)) = .big z
  | 0 => by simp [tw, cof, isSucc, last, one, init]
  | k + 1 => by
    show cof (psi (tw one (k + 1)) z z) = .big z
    have hne : tw one (k + 1) ≠ z := by show psi _ z z ≠ z; intro h; cases h
    have hs : isSucc (tw one (k + 1)) = false := by
      show (last (psi (tw one k) z z) == one) = false
      simp only [beq_eq_false_iff_ne, ne_eq, last, one, T.psi.injEq, and_true]
      exact tw_ne_z (Or.inl rfl) k
    simp only [cof, if_true, if_neg hne, hs, Bool.false_eq_true, if_false]
    exact cof_tw_one k

/-- The tower over `ψ_μ(Ω_{μ+1})` is not below `1` or `ω + 1`. -/
theorem tw_eta_not_lt (μ : T) (k : Nat) :
    ¬ tw (etaOm μ) k < one ∧ ¬ tw (etaOm μ) k < psi z one one := by
  have hne : tw (etaOm μ) k ≠ z := tw_ne_z_of (by simp [etaOm]) k
  refine ⟨fun h => hne (lt_one_iff.mp h), fun h => ?_⟩
  rcases k with _ | k
  · simp only [tw, etaOm] at h
    rw [psi_lt_psi] at h
    rcases h with h | ⟨rfl, h⟩ | ⟨rfl, h, _⟩
    · exact absurd h (by simp [lt_iff_lt, lt_z_false])
    · rw [lt_one_iff] at h; cases h
    · cases h
  · simp only [tw] at h
    rw [psi_lt_psi] at h
    rcases h with h | ⟨h, _⟩ | ⟨h, _⟩
    · exact absurd h (by simp [lt_iff_lt, lt_z_false])
    · exact tw_ne_z_of (by simp [etaOm]) k h
    · exact tw_ne_z_of (by simp [etaOm]) k h

/-! ## 基底の評価の形 -/

section
variable {L : Nat} {β : T} (hF : BaseFit L β)
include hF

theorem bval_ot_o {i : Nat} (hi : i < L) : isOT ((bval L β).o i) = true := by
  have hβ := hF.good
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; rw [bval_o0]
    split_ifs
    · exact isOT_psi_tw hβ z rfl _
    · decide
  · by_cases hk : (i - 1) % 3 = 1
    · rw [bval_oB (by omega) hk]
      split_ifs
      · exact isOT_psi_tw hβ wT rfl _
      · decide
    · rw [bval_oAD (by omega) hk]; exact isOT_tw hβ _

theorem bval_ot_v (i : Nat) : isOT ((bval L β).v i) = true := by
  have hβ := hF.good
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; rfl
  · by_cases hk : (i - 1) % 3 = 1
    · rw [bval_vB (by omega) hk]; decide
    · rw [bval_vAD (by omega) hk]; exact isOT_tw hβ _

/-- A children's `o` has argument `0`, unless it is the `B` under an `A`. -/
theorem child_o {i c : Nat} (hc : c ∈ children (Mlen L) i) :
    (∃ s, (bval L β).o c = psi s z z) ∨ (1 ≤ i ∧ (i - 1) % 3 = 0 ∧ c = i + 1) := by
  obtain ⟨hcL, hp⟩ := mem_children_iff.mp hc
  rw [Mlen_length] at hcL
  have hic := par_lt _ 0 c i hp
  by_cases hk : (c - 1) % 3 = 1
  · right
    rw [Mlen_par0_BD hcL (by omega) (by omega)] at hp; cases hp
    omega
  · left
    exact ⟨_, bval_oAD (by omega) hk⟩

/-- The subscript of an `A` column is above `ω`. -/
theorem vA_big {i : Nat} (hi : i < L) (h1 : 1 ≤ i) (hk : (i - 1) % 3 = 0) (y : T) :
    lt (psi ((bval L β).v i) z z) (psi wT y z) = false := by
  have hβ := hF.good
  rw [bval_vAD (by omega) (by omega)]
  have hK : β = w2 ∨ 1 ≤ Kd L i := by
    rcases hF with ⟨hL, _⟩ | ⟨_, h⟩
    · right; unfold Kd; omega
    · left; exact h
  rcases Nat.eq_zero_or_pos (Kd L i) with h0 | h0
  · rcases hK with hb | hK
    · rw [h0, hb]; rfl
    · omega
  · obtain ⟨k, hk'⟩ : ∃ k, Kd L i = k + 1 := ⟨Kd L i - 1, by omega⟩
    rw [hk']
    have hne := tw_ne_z hβ k
    cases hb : lt (psi (tw β (k + 1)) z z) (psi wT y z) with
    | false => rfl
    | true =>
      exfalso
      have h : psi (tw β (k + 1)) z z < psi wT y z := hb
      rw [psi_lt_psi] at h
      rcases h with h | ⟨h, _⟩ | ⟨h, _⟩
      · show False
        have h' : psi (tw β k) z z < psi z one z := h
        rw [psi_lt_psi] at h'
        rcases h' with h' | ⟨h', _⟩ | ⟨h', _⟩
        · exact absurd h' (by simp [lt_iff_lt, lt_z_false])
        · exact hne h'
        · exact hne h'
      · have h' : psi (tw β k) z z = psi z one z := h
        injection h' with h1; exact hne h1
      · have h' : psi (tw β k) z z = psi z one z := h
        injection h' with h1; exact hne h1

/-- **No frame triggers.** -/
theorem no_trig {i c : Nat} (hi : i < L) (hc : c ∈ children (Mlen L) i) {s y B : T}
    (ho : (bval L β).o c = psi s y z) (h1 : lt B y = true)
    (h2 : lt (psi ((bval L β).v i) z z) (psi s y z) = true) : False := by
  rcases child_o hF hc with ⟨s', hs'⟩ | ⟨hi1, hk, rfl⟩
  · rw [hs'] at ho; cases ho; rw [lt_z_false] at h1; cases h1
  · rw [bval_oB (by omega) (by omega)] at ho; cases ho
    rw [vA_big hF hi hi1 hk] at h2; cases h2

/-- The counted children: `1` under the root, `i + 1` under a `B`. -/
theorem CL_split {i c : Nat} {L' R : List Nat} (h : CL (Mlen L) i = L' ++ c :: R) :
    L' = [] ∧ c ∈ children (Mlen L) i ∧ ((i = 0 ∧ c = 1) ∨ (1 ≤ i ∧ (i - 1) % 3 = 1 ∧ c = i + 1)) := by
  have hmem : ∀ a ∈ CL (Mlen L) i, a ∈ children (Mlen L) i ∧
      ((i = 0 ∧ a = 1) ∨ (1 ≤ i ∧ (i - 1) % 3 = 1 ∧ a = i + 1)) := by
    intro a ha
    have hac := cl_mem_children ha
    have hcnt : Counted (Mlen L) i a := by unfold CL at ha; simpa using (List.mem_filter.mp ha).2
    refine ⟨hac, ?_⟩
    rcases (Mlen_counted hac).mp hcnt with h | h
    · left; exact h
    · right
      obtain ⟨_, hp⟩ := mem_children_iff.mp hac
      have hia := par_lt _ 0 a i hp
      have haL : a < L := by have := (mem_children hac).2; simpa using this
      by_cases hk : (a - 1) % 3 = 0
      · rw [Mlen_par0_A haL (by omega) hk] at hp; cases hp; omega
      · rw [Mlen_par0_BD haL (by omega) hk] at hp; cases hp; omega
  have hc := hmem c (by rw [h]; simp)
  refine ⟨?_, hc.1, hc.2⟩
  cases L' with
  | nil => rfl
  | cons a t =>
    exfalso
    have ha := hmem a (by rw [h]; simp)
    have hs : (CL (Mlen L) i).Pairwise (· < ·) := (children_sorted _ i).filter _
    rw [h] at hs
    have := List.rel_of_pairwise_cons hs (List.mem_append_right _ (List.mem_cons_self))
    omega

theorem Mlen_children_len {i : Nat} (h1 : 1 ≤ i) : (children (Mlen L) i).length ≤ 1 := by
  by_cases h : i + 1 < L ∧ (i - 1) % 3 ≠ 2
  · rw [Mlen_children_AB h.1 h1 h.2]; simp
  · rw [Mlen_children_nil (by omega)]; simp

end

/-! ## Inv3 の値の項目 -/

section
variable {L : Nat} {β : T} (hF : BaseFit L β)
include hF

theorem base_good3 : Good3 (Mlen L) (bval L β) := by
  classical
  refine ⟨fun i hi => bval_ot_o hF (by simpa using hi), fun i _ => bval_ot_v hF i, fun i hi => ?_⟩
  unfold cvals
  apply pairwise_short
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    by_cases hL : 1 < L
    · obtain ⟨t, ht, htm⟩ := Mlen_children_0 hL
      rw [ht, List.map_cons]
      unfold nzs
      rw [List.filter_cons]
      have hz : List.filter (fun t => decide (t ≠ z)) (t.map (cnt (Mlen L) (bval L β) 0)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro s hs
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
        rw [cnt_root (by rw [ht]; exact List.mem_cons_of_mem _ hc), if_neg (by have := htm c hc; omega)]
        simp
      rw [hz]; split_ifs <;> simp
    · rw [Mlen_children_nil (Or.inl (by simp at hi ⊢; omega))]; simp [nzs]
  · exact le_trans (nzs_length_le _) (by rw [List.length_map]; exact Mlen_children_len hF h0)

theorem base_vsmallF : VSmallF (Mlen L) (bval L β) := by
  have hβ := hF.good
  intro i hi L' c R h
  obtain ⟨_, hc, hcase⟩ := CL_split hF h
  have hcL : c < L := by have := (mem_children hc).2; simpa using this
  intro g hg
  left
  have hvc : (bval L β).v c = tw β (Kd L c) := bval_vAD (by omega) (by omega)
  rw [hvc] at hg ⊢
  rcases comps_tw hβ _ _ g hg with rfl | ⟨rfl, _⟩
  · exact z_le _
  · left; show two < psi (tw β (Kd L c)) z z; unfold two; rw [psi_lt_psi]; left; exact z_lt_tw hβ _

theorem base_frameClosed : FrameClosed (Mlen L) (bval L β) := by
  intro i hi L' c R h s y ho htr
  obtain ⟨_, hc, _⟩ := CL_split hF h
  exact absurd (no_trig hF (by simpa using hi) hc ho htr.1 htr.2) id

theorem base_frameOT : FrameOT (Mlen L) (bval L β) := by
  intro i hi L' c R h
  obtain ⟨rfl, _, _⟩ := CL_split hF h
  show isOT (psi ((bval L β).v i) z z) = true
  rw [isOT_psi_iff]
  exact ⟨bval_ot_v hF i, rfl, rfl, z_le _, fun g hg => by simp [comps] at hg⟩

theorem base_kd : BumpKidsDec (Mlen L) (bval L β) := by
  intro i _ _ j hj _
  apply pairwise_short
  rw [List.length_map]
  exact Mlen_children_len hF (by have := (mem_children hj).1; omega)

theorem base_td : BumpTermDec (Mlen L) (bval L β) := by
  intro i h1 _
  apply pairwise_short
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    rcases Nat.lt_or_ge 0 L with hL | hL
    · rw [Mlen_e1 hL, if_pos rfl] at h1; exact absurd rfl h1
    · rw [Mlen_children_nil (Or.inr (Or.inr hL))]; simp [nzs]
  · exact le_trans (nzs_length_le _) (by rw [List.length_map]; exact Mlen_children_len hF h0)

theorem base_ad : AbsD (Mlen L) (bval L β) := by
  intro i _ _ _ _ q hq; rw [vOpt_par1] at hq; simp [summands] at hq

theorem base_au : AbsU (Mlen L) (bval L β) := by
  intro i k _ _ q hq; rw [vOpt_par1] at hq; simp [summands] at hq

theorem base_auw : AbsUW (Mlen L) (bval L β) := by
  intro i k _ _ _ q hq; rw [vOpt_par1] at hq; simp [summands] at hq

theorem base_adw : AbsDW (Mlen L) (bval L β) := by
  intro _ _ _ _ _ _ _ i _ _ _ _ _ _ q hq; rw [vOpt_par1] at hq; simp [summands] at hq

theorem base_adn : AbsDN (Mlen L) (bval L β) := by
  intro i _ _ _ _ _ _ q hq; rw [vOpt_par1] at hq; simp [summands] at hq

theorem base_tp1 : TP1C (Mlen L) (bval L β) := by
  intro i L' c R h _ s y ho h1 h2 _
  have hc : c ∈ children (Mlen L) i := by rw [h]; simp
  have hi : i < L := by have := (mem_children hc); simp at this; omega
  exact absurd (no_trig hF hi hc ho h1 h2) id

theorem base_tp1w : TP1WC (Mlen L) (bval L β) := by
  intro i L' c R h _ s y ho h1 h2 _ _
  have hc : c ∈ children (Mlen L) i := by rw [h]; simp
  have hi : i < L := by have := (mem_children hc); simp at this; omega
  exact absurd (no_trig hF hi hc ho h1 h2) id

theorem base_trig : TrigOmC (Mlen L) (bval L β) := by
  intro i L' c R h _ s ν ho h1 h2
  have hc : c ∈ children (Mlen L) i := by rw [h]; simp
  have hi : i < L := by have := (mem_children hc); simp at this; omega
  exact absurd (no_trig hF hi hc ho h1 h2) id

/-- The `o` values with a nonzero argument: the root and the `B` columns, the argument a tower. -/
theorem o_arg {c : Nat} (hc : c < L) {s y : T} (ho : (bval L β).o c = psi s y z) (hy : y ≠ z) :
    ∃ k, y = tw β (k + 1) ∧ (s = z ∨ s = wT) := by
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · subst h0; rw [bval_o0] at ho; cases ho
    split_ifs at hy ⊢ with h
    · exact ⟨_, rfl, Or.inl rfl⟩
    · exact absurd rfl hy
  · by_cases hk : (c - 1) % 3 = 1
    · rw [bval_oB (by omega) hk] at ho; cases ho
      split_ifs at hy ⊢ with h
      · exact ⟨_, rfl, Or.inr rfl⟩
      · exact absurd rfl hy
    · rw [bval_oAD (by omega) hk] at ho; cases ho; exact absurd rfl hy

/-- The hole of the last summand of the argument is that of `P^{k+1}(1)`. -/
theorem tplo_shape {c : Nat} (hc : c < L) {s y a : T} (ho : (bval L β).o c = psi s y z)
    (hl : last y = psi a z z) (hOa : OHole a) :
    ∃ k, β = one ∧ a = tw one (k + 1) ∧ (s = z ∨ s = wT) := by
  have hβ := hF.good
  have hy : y ≠ z := by rintro rfl; simp [last] at hl
  obtain ⟨k, rfl, hs⟩ := o_arg hF hc ho hy
  have : last (tw β (k + 1)) = psi (tw β k) z z := rfl
  rw [this] at hl; cases hl
  obtain ⟨hb, hk⟩ := ohole_tw hβ k hOa
  subst hb
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact ⟨k', rfl, rfl, hs⟩

omit hF in
theorem tplo_core {s : T} (hs : s = z ∨ s = wT) (η : T) (μ : T) (hη : η = etaOm μ) (k : Nat) :
    ¬ psi (fsD (tw one (k + 1)) η) z z < psi (succ s) z z := by
  rw [fsD_tw_one, hη, psi_lt_psi_z_iff]
  rintro (h | ⟨_, h⟩)
  · rcases hs with rfl | rfl
    · exact (tw_eta_not_lt μ k).1 h
    · exact (tw_eta_not_lt μ k).2 h
  · exact absurd h (by simp [lt_iff_lt, lt_z_false])

theorem base_tplo : TPLo (Mlen L) (bval L β) := by
  intro c hc s y ho _ a hl _ hOa
  obtain ⟨k, _, rfl, hs⟩ := tplo_shape hF (by simpa using hc) ho hl hOa
  exact tplo_core hs _ _ rfl k

theorem base_tplow : TPLoW (Mlen L) (bval L β) := by
  intro _ _ _ _ _ _ _ c hc _ s y ho _ _ a hl _ hOa hcof
  obtain ⟨k, _, rfl, _⟩ := tplo_shape hF (by simp at hc; omega) ho hl hOa
  rw [cof_tw_one] at hcof; cases hcof

theorem base_tplonAll : TPLoNAll (Mlen L) (bval L β) := by
  intro c hc s y ho _ a hl _ hOa hcof
  obtain ⟨k, _, rfl, _⟩ := tplo_shape hF (by simpa using hc) ho hl hOa
  rw [cof_tw_one] at hcof; cases hcof

theorem base_tplon : TPLoN (Mlen L) (bval L β) := tplon_of_all (base_tplonAll hF)

theorem base_rootS (hL : 1 ≤ L) : ∀ i ∈ roots (Mlen L), Single ((bval L β).o i) := by
  intro i hi
  rw [Mlen_roots hL] at hi
  simp at hi; subst hi
  exact ⟨bval_ot_o hF hL, _, _, bval_o0⟩

theorem base_rootP (hL : 1 ≤ L) : ((roots (Mlen L)).map (bval L β).o).Pairwise (fun a b => b ≤ a) := by
  rw [Mlen_roots hL]; simp

end

end Ytosk
