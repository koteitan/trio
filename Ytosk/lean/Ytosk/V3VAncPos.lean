/-
**VAncPos を VAnc m j* に減らす（2026-10-24）。**

行 2 = 1 の列 c（m = P₁(c)）で、足す項 X = bumpX c の添字 s が正のとき:
- s = v(j*) となる孫 j*（c の bump 子 j の子）がある（`bumpX_index`: omega・sumN の頭の添字をたどる）。
- VAnc m j* があれば VAnc m c が出る（`vAnc_of_vAnc_index`）。落ちる v(m) の加数 t < X の成分は、段 u ≤ s では
  Ω_s ≤ Ω_{v(c)} 以下か s の成分（= X の成分）以下、段 u > s では成分がない。
- j* が m の行 1 の子孫なら、VAnc m j* は鎖の上の帰納法の仮定から出る（`vAnc_chain_rk`。鎖の列の順位は
  rk false j* < rk true j* < rk false c 以下）。
- そうでないときの VAnc m j* が残り `VAncJ`。
測定: VAnc m j* は j* が m の行 1 の子孫でない場合も例外 0（tmp/claude/vjstar4.py、std_a・d3s・ext2）。
-/
import Ytosk.V3VAncInd

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## 頭の添字 -/

theorem head_add_or : ∀ x y : T, head (add x y) = head x ∨ head (add x y) = head y
  | z, y => Or.inr rfl
  | psi a b c, z => Or.inl rfl
  | psi a b c, psi d e f => by
    rw [add_psi_psi]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- The head of a standard sum is the head of the start or of one of the summands. -/
theorem head_foldl_sf : ∀ (l : List T) (acc : T), isOT acc = true → (∀ t ∈ l, isOT t = true) →
    head (l.foldl (fun a b => sf (add a b)) acc) = head acc ∨
      ∃ t ∈ l, head (l.foldl (fun a b => sf (add a b)) acc) = head t
  | [], acc, _, _ => Or.inl rfl
  | t :: l, acc, hacc, hl => by
    simp only [List.foldl_cons]
    have ht : isOT t = true := hl t (List.mem_cons_self ..)
    have hot := isOT_add hacc ht
    rw [sf_ot hot]
    rcases head_foldl_sf l (add acc t) hot (fun t' h => hl t' (List.mem_cons_of_mem _ h)) with h | ⟨t', ht', h⟩
    · rcases head_add_or acc t with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨t, List.mem_cons_self .., h.trans h'⟩
    · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', h⟩

theorem head_sumN {l : List T} (hl : ∀ t ∈ l, isOT t = true) (h : sumN l ≠ z) :
    ∃ t ∈ l, head (sumN l) = head t := by
  rcases head_foldl_sf l z rfl hl with h' | h'
  · exfalso
    unfold sumN at h
    cases hs : l.foldl (fun a b => sf (add a b)) z with
    | z => exact h hs
    | psi => rw [hs] at h'; simp [head] at h'
  · exact h'

/-- **A positive subscript of `ω^x` is the subscript of the head of `x`.** -/
theorem omega_index {x s y : T} (h : omega x = psi s y z) (hs : s ≠ z) : ∃ b c, x = psi s b c := by
  unfold omega at h
  split_ifs at h
  · cases h; exact absurd rfl hs
  · cases x with
    | z => simp [one] at h; exact absurd h.1.symm hs
    | psi s' b c => simp only [psi.injEq] at h; exact ⟨b, c, by rw [h.1]⟩

/-- The `o` value has subscript `v`. -/
theorem o_index {N : Mat} {σ : Valn} (hC : Cons N σ) (hG : Good3 N σ) {i : Nat} (hi : i < N.length) :
    ∃ y, σ.o i = psi (σ.v i) y z := by
  rw [(hC i hi).1]
  unfold oRhs
  show ∃ y, add (sp (sf (σ.v i)) z (sf _)) (sf z) = psi (σ.v i) y z
  rw [sp_eq_spArg, sf_ot (hG.ot_v i hi)]
  exact ⟨_, rfl⟩

/-- **The subscript of the bump term is `v` of a bump grandchild.** -/
theorem bumpX_index {N : Mat} {σ : Valn} (hC : Cons N σ) (hG : Good3 N σ) {c : Nat} {s Y : T}
    (hX : bumpX N σ c = psi s Y z) (hs : s ≠ z) :
    ∃ j ∈ children N c, col N j = bump N c ∧ ∃ js ∈ children N j, σ.v js = s := by
  obtain ⟨b, c', hx⟩ := omega_index hX hs
  have hl : ∀ t ∈ one :: (children N c).map (bumpTerm N σ c), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG c d
  obtain ⟨t, ht, hh⟩ := head_sumN hl (by rw [hx]; simp)
  rw [hx] at hh
  simp only [head] at hh
  rcases List.mem_cons.mp ht with rfl | ht
  · simp [one] at hh; exact absurd hh.1 hs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  unfold bumpTerm at hh
  split_ifs at hh with hcol
  · refine ⟨j, hj, hcol, ?_⟩
    obtain ⟨s', y', hom⟩ := omega_psi_form (sumN ((children N j).map σ.o))
    rw [hom] at hh
    simp only [psi.injEq] at hh
    obtain ⟨rfl, -⟩ := hh
    obtain ⟨b2, c2, hx2⟩ := omega_index hom hs
    have hl2 : ∀ t ∈ (children N j).map σ.o, isOT t = true := by
      intro t ht
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
      exact hG.ot_o k (mem_children hk).2
    obtain ⟨t2, ht2, hh2⟩ := head_sumN hl2 (by rw [hx2]; simp)
    obtain ⟨js, hjs, rfl⟩ := List.mem_map.mp ht2
    obtain ⟨y, hy⟩ := o_index hC hG (mem_children hjs).2
    rw [hx2, hy] at hh2
    simp only [head, psi.injEq] at hh2
    exact ⟨js, hjs, hh2.1.symm⟩

/-! ## VAnc m j* から VAnc m c -/

/-- Below `ψ_s(Y)`, a standard term has no components at a level above `s`. -/
theorem comps_below_high {s Y u : T} (hsu : s < u) : ∀ (t : T), isOT t = true → head t < psi s Y z →
    comps u t = []
  | z, _, _ => rfl
  | psi a b c, ht, hlt => by
    simp only [head] at hlt
    have has : a ≤ s := by
      rw [psi_lt_psi_z_iff] at hlt
      rcases hlt with h | ⟨h, _⟩
      · exact le_of_lt h
      · exact le_of_eq h
    have hau : lt a u = true := lt_of_le_of_lt has hsu
    obtain ⟨_, _, hc, hhc, _⟩ := isOT_psi_iff.mp ht
    simp only [comps, hau, if_true, List.nil_append]
    cases c with
    | z => rfl
    | psi a' b' c' =>
      exact comps_below_high hsu (psi a' b' c') hc (lt_of_le_of_lt hhc (by
        rw [psi_lt_psi_z_iff] at hlt ⊢; exact hlt))

/-- The dropped part of `add V ψ_s(Y)`: standard, below `ψ_s(Y)`, with components among those of `V₀`. -/
theorem dropOK_sub {s Y V₀ : T} : ∀ V, isOT V = true → (∀ u, ∀ g ∈ comps u V, g ∈ comps u V₀) →
    DropOK (psi s Y z) (fun t => isOT t = true ∧ head t < psi s Y z ∧ ∀ u, ∀ g ∈ comps u t, g ∈ comps u V₀) V
  | z, _, _ => trivial
  | psi a b c, hV, hsub => by
    unfold DropOK
    split_ifs with h
    · exact ⟨hV, h, hsub⟩
    · refine dropOK_sub c (isOT_rest hV) (fun u g hg => hsub u g ?_)
      simp only [comps, List.mem_append]
      exact Or.inr hg

/-- **`VAnc m c` from `VAnc m j*`** when `v(c) = v(m) + ψ_s(Y)` and `v(j*) = s`. -/
theorem vAnc_of_vAnc_index {σ : Valn} {m c js : Nat} {s Y : T} (hmo : isOT (σ.v m) = true)
    (hv : σ.v c = add (σ.v m) (psi s Y z)) (hjs : σ.v js = s) (hA : VAnc σ m js) : VAnc σ m c := by
  have hsc : s < σ.v c := by
    rw [hv]; exact lt_of_lt_of_le (sub_lt_psi s Y z) (le_add_single _ ⟨s, Y, rfl⟩)
  have hD : ∀ u t, (isOT t = true ∧ head t < psi s Y z ∧ ∀ u, ∀ g ∈ comps u t, g ∈ comps u (σ.v m)) →
      ∀ g ∈ comps u t, g ≤ psi (σ.v c) z z ∨ ∃ x ∈ comps u (psi s Y z), g ≤ x := by
    intro u t ⟨hto, hth, hsub⟩ g hg
    by_cases hsu : s < u
    · rw [comps_below_high hsu t hto hth] at hg; simp at hg
    · rcases hA u g (hsub u g hg) with h | ⟨d, hd, h⟩
      · left
        rw [hjs] at h
        exact le_trans h (psi_le_psi_of (Or.inl hsc))
      · right
        rw [hjs] at hd
        refine ⟨d, ?_, h⟩
        have hsu' : lt s u = false := by
          cases hb : lt s u with
          | false => rfl
          | true => exact absurd hb hsu
        simp only [comps, hsu', Bool.false_eq_true, if_false, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr (Or.inr hd))
  intro u g hg
  rcases comps_add_of_dropOK (hD u) (σ.v m) (dropOK_sub (σ.v m) hmo (fun _ _ h => h)) g hg with h | ⟨x, hx, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, by rw [hv]; exact hx, h⟩

/-! ## 鎖の上の帰納法の仮定 -/

/-- **`VAnc` along a row-1 chain** whose columns all have rank below `rk false c`. -/
theorem vAnc_chain_rk {N : Mat} {σ : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ) (hG : Good3 N σ)
    (hR : Rk N rk) {c : Nat} (ih : ∀ e, e < N.length → rk false e < rk false c → VAncAt N σ e) :
    ∀ n p e, e < n → TRIO.le1 N p e → rk false e < rk false c → VAnc σ p e
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, p, e, hen, h, hrk => by
    by_cases hep : e = p
    · subst hep; exact vAnc_refl σ e
    · obtain ⟨m, hm, hpm⟩ := le1_par1_down h hep
      have hme : m < e := par_lt N 1 e m hm
      have he : e < N.length := h.2.1
      have hnr := (par1_iff N he).mp hm
      have he1 : entry N 1 e ≠ 0 := by
        intro h0
        have h' := hnr.2.2.2.1
        rw [show TRIO.entry N 1 e = entry N 1 e from rfl, h0] at h'
        omega
      have hrm : rk false m < rk false e := ((hR e he).2.2 he1).1 m hm
      exact vAnc_trans (vMono1_of hC hG e m he hm)
        (vAnc_chain_rk hC hG hR ih n p m (by omega) hpm (by omega)) (ih e he hrk m hm)

/-! ## 残り -/

/-- **Residual (standard matrices): `VAnc m j*` off the row-1 chain.** For a bump column `c` (row-1 parent `m`)
whose added term has the positive subscript `v(j*)` of a bump grandchild `j*` that is not a row-1 descendant of
`m`, `VAnc m j*` holds, given `VAnc` at every column of lower `v`-rank. -/
def VAncJ : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Good3 N σ → Rk N rk →
    ∀ c m j js, c < N.length → entry N 1 c ≠ 0 → entry N 2 c ≠ 0 → par N 1 c = some m →
      j ∈ children N c → col N j = bump N c → js ∈ children N j → σ.v js ≠ z →
      (∃ Y, bumpX N σ c = psi (σ.v js) Y z) → ¬ TRIO.le1 N m js →
      (∀ e, e < N.length → rk false e < rk false c → VAncAt N σ e) → VAnc σ m js

/-- **`VAncPos` from `VAncJ`.** -/
theorem vAncPos_of_J (hJ : VAncJ) : VAncPos := by
  intro N σ rk hS hne hC hG hR c hc he1 he2 ih h0 m hm
  have hmc : m < c := par_lt N 1 c m hm
  have hmo : isOT (σ.v m) = true := hG.ot_v m (by omega)
  obtain ⟨s, Y, hX⟩ := omega_psi_form (sumN (one :: (children N c).map (bumpTerm N σ c)))
  have hX' : bumpX N σ c = psi s Y z := hX
  have hs : s ≠ z := by rintro rfl; exact h0 Y hX'
  have hv : σ.v c = add (σ.v m) (psi s Y z) := by
    have hv := (hC c hc).2
    unfold vRhs at hv
    rw [if_neg he1, if_neg he2, hm] at hv
    simp only [vOpt] at hv
    rw [hX] at hv
    rwa [sf_ot (isOT_add hmo (hX' ▸ isOT_bumpX hG c))] at hv
  obtain ⟨j, hj, hcol, js, hjs, hvjs⟩ := bumpX_index hC hG hX' hs
  have hjsN : js < N.length := (mem_children hjs).2
  have hrk : rk false js < rk false c :=
    lt_trans (hR js hjsN).1 (((hR c hc).2.2 he1).2.2 he2 j hj hcol js hjs)
  have hA : VAnc σ m js := by
    by_cases hle : TRIO.le1 N m js
    · exact vAnc_chain_rk hC hG hR ih (js + 1) m js (Nat.lt_succ_self _) hle hrk
    · exact hJ N σ rk hS hne hC hG hR c m j js hc he1 he2 hm hj hcol hjs (hvjs ▸ hs)
        ⟨Y, hvjs ▸ hX'⟩ hle ih
  exact vAnc_of_vAnc_index hmo hv hvjs hA

end Ytosk
