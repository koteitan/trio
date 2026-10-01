/-
**3 行・t = 1・q ≠ r: 枠の条件 (W) を値の不変条件 TP1 から。**

- 穴の段 `holeLev`: 共終数 Ω_{μ+1} の項と、対角化の点 ψ_{a'}(b)（cof b = Ω_{μ+1}）の下の項で μ（`holeLev_holeT`）。
- 値の不変条件 **TP1**: 書き換えの枠（B < y、ψ_{v(i)}(0) < ψ_s(y)）で穴のある y について B < fsD(y, ψ_{holeLev y}(1))。
- 始点 seed = o_{M.take x}(r) の引数は 0 でない（M.take x で r の最初の子 r+1 は数える子、`seed_arg_ne_z`）。
  よって ψ_μ(1) ≤ seed、鎖のすべての項も ψ_μ(1) 以上。
- (W)（`hW_of_TP1`）: TP1 と穴と fsD の単調性から。
-/
import Ytosk.V3ValT1R

namespace Ytosk

open T

/-! ## 穴の段 -/

/-- The level `μ` of the `Ω_{μ+1}` hole that `fsD` acts on. -/
def holeLev : T → T
  | z => z
  | psi _ _ (psi c d e) => holeLev (psi c d e)
  | psi a b z =>
    if b = z then (if isSucc a then init a else holeLev a)
    else match cof b with
      | .big μ => μ
      | _ => holeLev b

theorem holeLev_cof : ∀ {t μ : T}, cof t = .big μ → holeLev t = μ
  | z, _, h => by simp [cof] at h
  | psi _ _ (psi c d e), μ, h => by
    show holeLev (psi c d e) = μ
    exact holeLev_cof (t := psi c d e) (by simpa [cof] using h)
  | psi a b z, μ, h => by
    unfold holeLev
    unfold cof at h
    by_cases hb : b = z
    · rw [if_pos hb] at h ⊢
      by_cases ha : a = z
      · rw [if_pos ha] at h; cases h
      · rw [if_neg ha] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs] at h ⊢; cases h; rfl
        · rw [if_neg hs] at h ⊢; exact holeLev_cof h
    · rw [if_neg hb] at h ⊢
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h
        cases hcb : cof b with
        | big μ' =>
          rw [hcb] at h; simp only at h
          split at h
          · cases h; rfl
          · cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- Below a diagonal point the cofinality is `ω`. -/
theorem DiagAt.cof_omega {a b μ t : T} (h : DiagAt a b μ t) : cof t = .omega := by
  induction h with
  | here hb hc hμ =>
    have hs := not_succ_of_cof_big hc
    unfold cof
    rw [if_neg hb, if_neg (by rw [hs]; simp), hc]
    simp only
    rw [if_neg hμ]
  | rest _ ih => simpa [cof] using ih
  | @arg a' b' hb hs _ ih =>
    unfold cof
    rw [if_neg hb, if_neg (by rw [hs]; simp), ih]
  | @sub a' ha hs _ ih =>
    unfold cof
    rw [if_pos rfl, if_neg ha, if_neg (by rw [hs]; simp)]
    exact ih

theorem DiagAt.holeLev_eq {a b μ t : T} (h : DiagAt a b μ t) : Ytosk.holeLev t = μ := by
  induction h with
  | here hb hc _ =>
    unfold holeLev
    rw [if_neg hb, hc]
  | rest _ ih => exact ih
  | @arg a' b' hb _ hD ih =>
    unfold holeLev
    rw [if_neg hb, hD.cof_omega]
    exact ih
  | @sub a' _ hs _ ih =>
    unfold holeLev
    rw [if_pos rfl, if_neg (by rw [hs]; simp)]
    exact ih

/-- **The level of a hole.** -/
theorem holeLev_holeT {μ br vr t : T} (h : HoleT μ br vr t) : holeLev t = μ := by
  rcases h with h | ⟨_, _, hD⟩
  · exact holeLev_cof h
  · exact hD.holeLev_eq

/-! ## 値の不変条件 TP1 -/

/-- **Value invariant TP1** (persistence of the rewriting): at a rewriting frame with a hole in the
argument `y`, the state `B` stays below `fsD(y, ψ_μ(1))`, `μ` the level of the hole
(SRO より下の L8 網羅で 3.9 万枠、例外 0; 数えない子では引き金は起きない). -/
def TP1 (M : Mat) (ρ : Valn) : Prop :=
  ∀ i L c R, children M i = L ++ c :: R → ∀ s y, ρ.o c = psi s y z →
    lt (preState M ρ i L) y = true → lt (psi (ρ.v i) z z) (psi s y z) = true → OHole y →
    lt (preState M ρ i L) (fsD y (psi (holeLev y) one z)) = true

/-! ## 始点の引数は 0 でない -/

theorem add_ne_z_left : ∀ {x : T} (y : T), x ≠ z → add x y ≠ z
  | z, _, h => absurd rfl h
  | psi a b c, z, _ => by simp [add]
  | psi a b c, psi d e f, _ => by
    simp only [add]
    split <;> simp

theorem H_ne_z {s y : T} (hy : y ≠ z) : H s y ≠ z := by
  unfold H
  by_cases ht : cut (add s one) y = z
  · rw [ht, add_z_left]
    have hlt : lt (psi s z z) (psi s y z) = true := by
      show psi s z z < psi s y z
      rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, lt_of_le_of_ne (z_le y) (Ne.symm hy)⟩
    simp only [sub, hlt, if_true]
    simp
  · exact add_ne_z_left _ ht

theorem step_ne_z' (a b s y c : T) : step a b s y c ≠ z := by
  unfold step
  split
  · rename_i h
    apply H_ne_z
    intro hy; rw [hy] at h; exact T.not_lt_z _ h.1
  · exact add_ne_z_right _ (by simp)

theorem spArg_ne_z (a : T) : ∀ (c b : T), (b ≠ z ∨ c ≠ z) → spArg a b c ≠ z
  | z, b, h => by
    rcases h with h | h
    · exact h
    · exact absurd rfl h
  | psi s y c, b, _ => by
    rw [spArg_cons]
    exact spArg_ne_z a c _ (Or.inl (step_ne_z' a b s y c))

theorem foldl_sf_ne_z : ∀ (l : List T) (acc : T), (acc ≠ z ∨ ∃ t ∈ l, t ≠ z) →
    l.foldl (fun a b => sf (add a b)) acc ≠ z
  | [], acc, h => by
    rcases h with h | ⟨t, ht, _⟩
    · exact h
    · simp at ht
  | t :: l, acc, h => by
    simp only [List.foldl_cons]
    apply foldl_sf_ne_z l
    by_cases hacc : acc ≠ z
    · exact Or.inl (sf_ne_z (add_ne_z_left _ hacc))
    · rcases h with h | ⟨t', ht', hne⟩
      · exact absurd h hacc
      · rcases List.mem_cons.mp ht' with rfl | ht'
        · exact Or.inl (sf_ne_z (add_ne_z_right _ hne))
        · exact Or.inr ⟨t', ht', hne⟩

/-- **The argument of `o(i)` is nonzero when `i` has a counted child.** -/
theorem o_arg_ne_z {N : Mat} {ρ : Valn} {i c : Nat} (hC : Cons N ρ) (hi : i < N.length)
    (hc : c ∈ children N i) (hcnt : Counted N i c) :
    ∃ σ, ρ.o i = psi (sf (ρ.v i)) σ z ∧ σ ≠ z := by
  have hcl := (mem_children hc).2
  have hoc : ρ.o c ≠ z := by
    rw [(hC c hcl).1]; unfold oRhs; exact sf_ne_z (by simp)
  have hmem : ρ.o c ∈ (children N i).map (cnt N ρ i) := by
    refine List.mem_map.mpr ⟨c, hc, ?_⟩
    rw [cnt_eq_ite, if_pos hcnt]
  have hS : sumN ((children N i).map (cnt N ρ i)) ≠ z :=
    foldl_sf_ne_z _ z (Or.inr ⟨_, hmem, hoc⟩)
  refine ⟨spArg (sf (ρ.v i)) z (sf (sumN ((children N i).map (cnt N ρ i)))), ?_,
    spArg_ne_z _ _ _ (Or.inr (sf_ne_z hS))⟩
  rw [(hC i hi).1]
  unfold oRhs
  show add (sp (sf (ρ.v i)) z (sf _)) (sf z) = _
  rw [sp_eq_spArg]
  rfl

/-! ## M.take x で r の最初の子は数える子 -/

section
variable {M : Mat} {x r : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (h1 : par M 1 x = some r) (hqr : par M 0 x ≠ some r)
include hx hR0 hSD h1

/-- **`r` has no bump child.** -/
theorem no_bump_child_r : ∀ j ∈ children M r, col M j ≠ bump M r := by
  intro j hj hjb
  have hA := anc0_of_par M 1 r x h1
  have hrx : r ≠ x := by have := par_lt M 1 x r h1; omega
  obtain ⟨p, hpr, hpx⟩ := anc0_child hA hrx
  have hpl : p < M.length := by have := hpx.le; omega
  have hpM : p ∈ children M r := mem_children_iff.mpr ⟨hpl, hpr⟩
  have hp1 := e1_path_child h1 hA hrx hpr hpx
  have hpj : par M 0 j = some r := (mem_children_iff.mp hj).2
  have hrp := par_lt M 0 p r hpr
  have hjl := (mem_children hj).2
  rcases Nat.lt_trichotomy j p with hjp | rfl | hpj'
  · obtain ⟨L, R, hLR⟩ := List.append_of_mem hj
    obtain ⟨hL, _⟩ := sib_order (children_sorted M r) hLR
    have hpR : p ∈ R := by
      have : p ∈ L ++ j :: R := hLR ▸ hpM
      rcases List.mem_append.mp this with h | h
      · have := hL p h; omega
      · rcases List.mem_cons.mp h with h | h
        · omega
        · exact h
    have hle := sib_le hSD R L j hLR p hpR
    rw [hjb] at hle
    unfold colLe bump at hle
    have e0 : (col M p).1 = entry M 0 p := rfl
    have e1 : (col M p).2.1 = entry M 1 p := rfl
    simp only at hle
    rw [e0, e1] at hle
    have := hR0 p r hpr
    omega
  · have := e1_of_col (show col M j = (entry M 0 r + 1, entry M 1 r, 1) from hjb); omega
  · have hA' := anc_between hpx j (by omega) (by omega)
    have := (anc0_par hA' (by omega) hpj).le
    omega

include hZ2 hZ1 hUAB hqr in
/-- **In `M.take x`, the first child `r + 1` of `r` is counted.** -/
theorem first_child_counted_take :
    r + 1 ∈ children (M.take x) r ∧ Counted (M.take x) r (r + 1) := by
  have hA := anc0_of_par M 1 r x h1
  have hrx : r < x := par_lt M 1 x r h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hrq : r ≤ q := par0_ge_of_anc hA hrx (Nat.le_refl _) hq
  have hqr' : q ≠ r := fun e => hqr (e ▸ hq)
  have hqx := par_lt M 0 x q hq
  have hr1x : r + 1 < x := by omega
  have hpar : par M 0 (r + 1) = some r := child_succ hA (by omega)
  have hmemM : r + 1 ∈ children M r := mem_children_iff.mpr ⟨by omega, hpar⟩
  have hmemT : r + 1 ∈ children (M.take x) r := by
    rw [children_take, List.mem_filter]; exact ⟨hmemM, by simpa using hr1x⟩
  refine ⟨hmemT, ?_, ?_⟩
  · rw [col_take M hr1x, bump_take M hrx]
    exact no_bump_child_r hx hR0 hSD h1 (r + 1) hmemM
  · rintro ⟨hiu, htop⟩
    obtain ⟨k, hk, hu⟩ := (isUpg_take M (by omega) (r + 1)).mp hiu
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    rcases hcase with h | ⟨hAk, hlt⟩
    · have hkr : k = r := by omega
      rw [hkr] at hu
      have := leaf_of_upg_next hR0 hu x hA
      omega
    · have he2 : entry M 2 (r + 1) = 1 := by have := upg_target_e2 hu; have := hZ2 (r + 1); omega
      obtain ⟨p', hp', hp'k⟩ := anc0_child hAk (by omega)
      have hp'k' := hp'k.le
      have hp'x : p' < x := by omega
      have hp'M : p' ∈ children M (r + 1) := mem_children_iff.mpr ⟨by omega, hp'⟩
      have hp'T : p' ∈ children (M.take x) (r + 1) := by
        rw [children_take, List.mem_filter]; exact ⟨hp'M, by simpa using hp'x⟩
      unfold topped at htop
      cases hl : (children (M.take x) (r + 1)).getLast? with
      | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hp'T; simp at hp'T
      | some ℓ =>
        rw [hl] at htop
        simp only [decide_eq_true_eq] at htop
        have hlast : children (M.take x) (r + 1) = (children (M.take x) (r + 1)).dropLast ++ [ℓ] := by
          rw [List.dropLast_append_getLast? _ hl]
        have hall := all_bump_of_last (R0P_take hR0 x) (Z2_take hZ2 x) (SibDec_take hSD x)
          (Z1C_take hZ1 x) (by rw [entry_take M 2 hr1x]; exact he2) hlast htop p' hp'T
        rw [col_take M hp'x, bump_take M hr1x] at hall
        exact hUAB k (r + 1) hu (by omega) p' hp'M hall hp'k

end

end Ytosk
