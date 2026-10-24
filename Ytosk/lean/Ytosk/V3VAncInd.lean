/-
**HVAncStd を順位の帰納法で（2026-10-24）。**

VAncStep（行 1 の親 m = P₁(c) で v(m) の成分は Ω_{v(c)} 以下か v(c) の成分以下）を、v の計算の順位
rk false c についての帰納法で示す。v(c) = v(m) + X で、add が落とす v(m) の加数だけが問題になる。
- 行 2 = 0・upg c = k: v(c) = v(k)（`v_upg_eq`）、P₁(k) = m（`upg_spec`）、k の順位は低い（帰納法の仮定）。
- 行 2 = 0・upg なし: X = 1 で、落ちる加数はない。
- 行 2 = 1・X = ψ_0(Y)（添字 0）: 落ちる加数 q < X は ψ_0(y)（y < Y）で、段 0 の成分は y 以下（標準形）、
  段 > 0 の成分はない。よって X の成分 Y で押さえられる（`comps_below_psi0`）。
- 行 2 = 1・X の添字が正: 残り `VAncPos`（帰納法の仮定つき）。
測定: X の添字が 0 の場合は std_a・d3s・ext2 で X の成分だけで押さえられる（tmp/claude/vcase.py）。
-/
import Ytosk.V3VAncStd
import Ytosk.V3DropRel
import Ytosk.V3BumpDrop

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## add が落とす部分 -/

/-- The part of `V` dropped by `add V X` (with `h` the head of `X`) satisfies `D`: checked at the first
dropped summand. -/
def DropOK (h : T) (D : T → Prop) : T → Prop
  | z => True
  | psi a b c => if psi a b z < h then D (psi a b c) else DropOK h D c

/-- **Components of `V` in `add V X`**: the kept summands are kept, and the dropped part is handled by `D`. -/
theorem comps_add_of_dropOK {d e f B u : T} {D : T → Prop}
    (hD : ∀ t, D t → ∀ g ∈ comps u t, g ≤ B ∨ ∃ x ∈ comps u (psi d e f), g ≤ x) :
    ∀ V, DropOK (psi d e z) D V → ∀ g ∈ comps u V, g ≤ B ∨ ∃ x ∈ comps u (add V (psi d e f)), g ≤ x
  | z, _, g, hg => by simp [comps] at hg
  | psi a b c, hV, g, hg => by
    rw [add_psi_psi]
    unfold DropOK at hV
    split_ifs at hV ⊢ with hlt
    · exact hD _ hV g hg
    · simp only [comps, List.mem_append] at hg ⊢
      rcases hg with hg | hg
      · exact Or.inr ⟨g, Or.inl hg, le_refl _⟩
      · rcases comps_add_of_dropOK hD c hV g hg with h | ⟨x, hx, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, Or.inr hx, h⟩

/-- Nothing is dropped by adding `1`. -/
theorem dropOK_one {D : T → Prop} : ∀ V, DropOK (psi z z z) D V
  | z => trivial
  | psi a b c => by
    unfold DropOK
    rw [if_neg]
    · exact dropOK_one c
    · intro h
      rw [psi_lt_psi_z_iff] at h
      rcases h with h | ⟨_, h⟩
      · exact absurd h (not_lt_of_ge (z_le a))
      · exact absurd h (not_lt_of_ge (z_le b))

/-! ## 添字 0 の項を足すとき -/

/-- **Below `ψ_0(Y)`**: the components of a standard `V` with head below `ψ_0(Y)` are at most `Y`
(at level `0`), and there are none at a positive level. -/
theorem comps_below_psi0 {Y : T} : ∀ (V : T), isOT V = true → head V < psi z Y z →
    ∀ u, ∀ g ∈ comps u V, ∃ d ∈ comps u (psi z Y z), g ≤ d
  | z, _, _, u, g, hg => by simp [comps] at hg
  | psi a b c, hV, hlt, u, g, hg => by
    simp only [head] at hlt
    rw [psi_lt_psi_z_iff] at hlt
    have ha : a = z := by
      rcases hlt with h | ⟨h, _⟩
      · exact absurd h (not_lt_of_ge (z_le a))
      · exact h
    subst ha
    have hbY : b < Y := by
      rcases hlt with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' z)
      · exact h
    obtain ⟨_, _, hc, hhc, hcb⟩ := isOT_psi_iff.mp hV
    simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · split at hg
      · simp at hg
      · rename_i hzu
        have hu : u = z := by
          cases u with
          | z => rfl
          | psi => exact absurd rfl hzu
        subst hu
        refine ⟨Y, by simp [comps, lt], ?_⟩
        simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · exact le_of_lt hbY
        · exact le_of_lt (lt_trans' (hcb g hg) hbY)
        · simp at hg
    · cases c with
      | z => simp [comps] at hg
      | psi a' b' c' =>
        refine comps_below_psi0 (psi a' b' c') hc ?_ u g hg
        exact lt_of_le_of_lt hhc (by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hbY⟩)

/-- For a standard `V`, the dropped part of `add V ψ_0(Y)` is below `ψ_0(Y)`. -/
theorem dropOK_psi0 {Y : T} : ∀ V, isOT V = true →
    DropOK (psi z Y z) (fun t => isOT t = true ∧ head t < psi z Y z) V
  | z, _ => trivial
  | psi a b c, hV => by
    unfold DropOK
    split_ifs with h
    · exact ⟨hV, h⟩
    · exact dropOK_psi0 c (isOT_rest hV)

/-- **Adding `ψ_0(Y)` keeps `VAnc`**: every component of a standard `V` is at most a component of
`add V ψ_0(Y)`. -/
theorem comps_add_psi0 {Y B : T} {V : T} (hV : isOT V = true) (u : T) :
    ∀ g ∈ comps u V, g ≤ B ∨ ∃ x ∈ comps u (add V (psi z Y z)), g ≤ x :=
  comps_add_of_dropOK (D := fun t => isOT t = true ∧ head t < psi z Y z)
    (fun t ht g hg => Or.inr (comps_below_psi0 t ht.1 ht.2 u g hg)) V (dropOK_psi0 V hV)

/-! ## 順位の帰納法 -/

/-- `VAnc` from the row-1 parent at one column. -/
def VAncAt (N : Mat) (σ : Valn) (c : Nat) : Prop := ∀ m, par N 1 c = some m → VAnc σ m c

/-- The added term of a bump column. -/
def bumpX (N : Mat) (σ : Valn) (c : Nat) : T := omega (sumN (one :: (children N c).map (bumpTerm N σ c)))

/-- **Residual (standard matrices): the bump step with a positive subscript.** A column `c` with row 2 = 1
whose added term `X = bumpX` is not `ψ_0(·)` has `VAnc` from its row-1 parent, given `VAnc` at every column of
lower `v`-rank. -/
def VAncPos : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Good3 N σ → Rk N rk →
    ∀ c, c < N.length → entry N 1 c ≠ 0 → entry N 2 c ≠ 0 →
      (∀ e, e < N.length → rk false e < rk false c → VAncAt N σ e) →
      (∀ Y, bumpX N σ c ≠ psi z Y z) → VAncAt N σ c

theorem isOT_bumpX {N : Mat} {σ : Valn} (hG : Good3 N σ) (c : Nat) : isOT (bumpX N σ c) = true := by
  refine isOT_omega (isOT_sumN _ ?_)
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · rfl
  · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG c d

/-- **One step**: `VAncAt` at `c` from `VAncAt` at the columns of lower rank, except the residual case. -/
theorem vAncAt_step (hP : VAncPos) {N : Mat} {σ : Valn} {rk : Bool → Nat → Nat} (hS : Std N) (hne : N ≠ SRO)
    (hC : Cons N σ) (hG : Good3 N σ) (hR : Rk N rk) {c : Nat} (hc : c < N.length)
    (ih : ∀ e, e < N.length → rk false e < rk false c → VAncAt N σ e) : VAncAt N σ c := by
  intro m hm
  have hnr := (par1_iff N hc).mp hm
  have he1 : entry N 1 c ≠ 0 := by
    intro h0
    have h' := hnr.2.2.2.1
    rw [show TRIO.entry N 1 c = entry N 1 c from rfl, h0] at h'
    omega
  have hmc : m < c := par_lt N 1 c m hm
  have hmo : isOT (σ.v m) = true := hG.ot_v m (by omega)
  by_cases h2 : entry N 2 c = 0
  · cases hu : upg N c with
    | some k =>
      have hk := upg_lt hc hu
      obtain ⟨m', hm1, hm2, _, _⟩ := upg_spec hu
      rw [hm] at hm1
      cases hm1
      have hvk : σ.v c = σ.v k := v_upg_eq hC hc he1 h2 hu (by rw [hm]; exact hmo)
        (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
      have hrk := ((hR c hc).2.2 he1).2.1 h2 k hu
      have hA := ih k hk hrk m hm2
      intro u g hg
      rw [hvk]
      exact hA u g hg
    | none =>
      have hv := (hC c hc).2
      unfold vRhs at hv
      rw [if_neg he1, if_pos h2, hm, hu] at hv
      simp only [vOpt] at hv
      have hot : isOT (add (σ.v m) one) = true := isOT_add hmo isOT_one
      rw [sf_ot hot] at hv
      intro u g hg
      rw [hv]
      exact comps_add_of_dropOK (D := fun _ => False) (fun _ h => h.elim) _ (dropOK_one _) g hg
  · by_cases h0 : ∃ Y, bumpX N σ c = psi z Y z
    · obtain ⟨Y, hY⟩ := h0
      have hv := (hC c hc).2
      unfold vRhs at hv
      rw [if_neg he1, if_neg h2, hm] at hv
      simp only [vOpt] at hv
      have hX : omega (sumN (one :: (children N c).map (bumpTerm N σ c))) = psi z Y z := hY
      rw [hX] at hv
      have hot : isOT (add (σ.v m) (psi z Y z)) = true := isOT_add hmo (hY ▸ isOT_bumpX hG c)
      rw [sf_ot hot] at hv
      intro u g hg
      rw [hv]
      exact comps_add_psi0 hmo u g hg
    · exact hP N σ rk hS hne hC hG hR c hc he1 h2 ih (fun Y hY => h0 ⟨Y, hY⟩) m hm

/-- **`VAncStep` from the residual `VAncPos`** by induction on the `v`-rank. -/
theorem vAncStep_of_pos (hP : VAncPos) {N : Mat} {σ : Valn} {rk : Bool → Nat → Nat} (hS : Std N)
    (hne : N ≠ SRO) (hC : Cons N σ) (hG : Good3 N σ) (hR : Rk N rk) : VAncStep N σ := by
  have key : ∀ n c, rk false c = n → c < N.length → VAncAt N σ c := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro c hcn hc
      exact vAncAt_step hP hS hne hC hG hR hc (fun e he hlt => ihn _ (hcn ▸ hlt) e rfl he)
  intro c m hc hm
  exact key _ c rfl hc m hm

/-- **`HVAncStd` from `VAncPos`.** -/
theorem hVAncStd_of_pos (hP : VAncPos) : HVAncStd :=
  fun _ _ _ hS hne hC hG hR => vAncStep_of_pos hP hS hne hC hG hR

end Ytosk
