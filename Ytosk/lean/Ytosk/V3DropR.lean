/-
**落とす補題を HardArg なしで: 関係 `RelR` を各列で運ぶ（`po_of_R`・`drop_all_R`）。**

`HardArg`（M.take x の難しい枠の上界）は 1 枠の情報だけでは偽（desc.md の反例）。代わりに、値が変わる各列 c で
主張 `RClaim c`（c の新旧の状態 `H p y′`・`H p y` が `RelR` の関係）を、落とす補題の順位の帰納法の中で運ぶ。
難しい枠ではこれと Buchholz の補題 3.4 の形（`hard_of_relR`）から上界が出る。

残りの仮定（すべて C′ で例外 0）:
- `VSmallR M ρ`（1 行列の値の不変条件）: 子が書き換える枠では、子の添字の成分が親の段以下のすべての段で
  `Ω_s` 以下・状態 `B` 以下・親の添字の成分以下（`VSmallF` を全段に広げた形）。
- `VSmallNewR`: 添字が変わった最後の数える子について同じ（古い子が書き換える枠だけ）。
- `ShadowC`: 古い子だけが書き換え、`B` が `hi(y)` の先頭部分でない（影の）枠では、新しい状態が閉じている。
- `TailNR`: `M` で最後の数える子の後ろにある子（x か、数え方が変わる子）は書き換えない。
-/
import Ytosk.V3RelR

namespace Ytosk

open T

/-- **Value invariant**: in a frame where the child `ψ_s(y)` rewrites and `y` has a high part, the
components of the child's subscript at every level `u ≤ v(i)` are at most `Ω_s`, at most the state `B`, or at
most a component of `v(i)`. (Without the high part it is false on standard matrices: T0Ext, 50 cases with
`y = 1`, `B = 0`.) -/
def VSmallR (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL M i = L ++ c :: R →
    ∀ s y, ρ.o c = psi s y z →
    (lt (spArg (ρ.v i) z (sumN (L.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
    (split y (psi (succ s) z z)).1 ≠ z →
    ∀ u, ¬ lt (ρ.v i) u = true → ∀ g ∈ comps u s,
      g ≤ psi s z z ∨ g ≤ spArg (ρ.v i) z (sumN (L.map ρ.o)) ∨ ∃ d ∈ comps u (ρ.v i), g ≤ d

/-- **Drop hypothesis**: the same for a changed subscript of the last counted child of `M.take x`, where the
old child rewrites. -/
def VSmallNewR (M : Mat) (x : Nat) (ρ ρ' : Valn) : Prop :=
  ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (M.take x) i = Lc ++ [cs] → ρ'.v cs ≠ ρ.v cs →
    ∀ s y, ρ.o cs = psi s y z →
    (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
    ¬ ((split y (psi (succ s) z z)).1 = spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ∧ ρ.v i < ρ'.v cs) →
    ∀ u, ¬ lt (ρ.v i) u = true → ∀ g ∈ comps u (ρ'.v cs),
      g ≤ psi (ρ'.v cs) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ∨ ∃ d ∈ comps u (ρ.v i), g ≤ d

/-- **Drop hypothesis**: in a shadow frame (only the old child rewrites and `B` is not a prefix of `hi(y)`),
the new state `B + c′` is closed up to the components of `v(i)`. -/
def ShadowC (M : Mat) (x : Nat) (ρ ρ' : Valn) : Prop :=
  ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (M.take x) i = Lc ++ [cs] →
    ∀ s y s' y', ρ.o cs = psi s y z → ρ'.o cs = psi s' y' z →
    (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
    ¬ (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s' y' z) = true) →
    (¬ ∃ R, (split y (psi (succ s) z z)).1 = app (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) R) →
    ∀ u, ¬ lt (ρ.v i) u = true →
      ∀ g ∈ comps u (app (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) (psi s' y' z)),
        g < app (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) (psi s' y' z) ∨ ∃ d ∈ comps u (ρ.v i), g ≤ d

/-- **Drop hypothesis**: the children of `i` in `M` after its last counted child in `M.take x` do not rewrite. -/
def TailNR (M : Mat) (x : Nat) (ρ : Valn) : Prop :=
  ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat) (Tl : List Nat), CL (M.take x) i = Lc ++ [cs] →
    CL M i = Lc ++ [cs] ++ Tl → Tl ≠ [] →
    spArg (ρ.v i) z (sumN ((Lc ++ [cs] ++ Tl).map ρ.o)) =
      app (spArg (ρ.v i) z (sumN ((Lc ++ [cs]).map ρ.o))) (sumN (Tl.map ρ.o))

/-- **The claim carried at a column**: the new and old states of `o` (for a parent rewriting at any level
`q ≤ p`, with the components of `p` bounded) are in the relation `RelR q`. -/
def RClaim (ρ ρ' : Valn) (i : Nat) : Prop :=
  ∀ p y y' q, ρ.o i = psi p y z → ρ'.o i = psi p y' z → ¬ lt p q = true →
    (∀ u, ¬ lt q u = true → ∀ g ∈ comps u p, g ≤ psi p z z ∨ g < H p y' ∨ ∃ d ∈ comps u q, g ≤ d) →
    RelR q (H p y') (H p y)

theorem H_z (p : T) : H p z = z := by
  unfold H
  have h1 : cut (add p one) z = z := rfl
  rw [h1]
  have h2 : sub (psi p z z) (psi p z z) = z := by
    simp only [sub]; rw [if_neg (show ¬ lt (psi p z z) (psi p z z) = true from lt_irrefl' _)]
  rw [h2]; rfl

theorem rclaim_eq {ρ ρ' : Valn} {i : Nat} (h : ρ'.o i = ρ.o i) : RClaim ρ ρ' i := by
  intro p y y' q hy hy' _ _
  rw [h, hy] at hy'; simp only [psi.injEq] at hy'; rw [hy'.2.1]; exact relR_refl _ _

theorem rclaim_zero {ρ ρ' : Valn} {i : Nat} {p' : T} (h : ρ'.o i = psi p' z z) : RClaim ρ ρ' i := by
  intro p y y' q _ hy' _ _
  rw [h] at hy'; simp only [psi.injEq] at hy'; rw [← hy'.2.1, H_z]
  intro u _ c _ _ g hg; simp [comps] at hg

/-- Every summand of the state after a child is at least the child. -/
theorem step_summands_ge {a B s y : T} (hc : isOT (psi s y z) = true)
    (hBc : ∀ r ∈ summands B, psi s y z ≤ r) : ∀ r ∈ summands (step a B s y z), psi s y z ≤ r := by
  unfold step
  split_ifs
  · exact H_summands_ge hc
  · rw [add_eq_app_of_ge ⟨s, y, rfl⟩ B hBc, summands_app]
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hBc r hr
    · simp [summands] at hr; rw [hr]

/-- **The frame relation for a weak child** `ψ_{s′}(0)` replacing `ψ_s(0)`. -/
theorem lhdE_frame_weak {a B s s' : T} (hc : isOT (psi s z z) = true) (hwk : WkVA s' s) (hwc : WCS a s')
    (hBc : ∀ r ∈ summands B, psi s z z ≤ r) :
    LhdE (psi a (step a B s' z z) z) (psi a (step a B s z z) z) := by
  have hBc' : ∀ r ∈ summands B, psi s' z z ≤ r :=
    fun r hr => le_trans (le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl hwk.1))) (hBc r hr)
  rw [step_leaf, step_leaf, add_eq_app_of_ge ⟨s, z, rfl⟩ B hBc, add_eq_app_of_ge ⟨s', z, rfl⟩ B hBc']
  have hdrop := drop_child_lhdD (a := a) (B := B) hc hBc (fun h => absurd h.1 (T.not_lt_z _))
  rw [step_leaf, add_eq_app_of_ge ⟨s, z, rfl⟩ B hBc] at hdrop
  rcases hdrop with h | h
  · simp only [psi.injEq] at h
    exact absurd h.2.1 (ne_of_lt (lt_app_of (by simp)))
  right
  apply lhd_weak_childA h (by simp)
  · intro u hu g hg
    exact (self_small_weakA hwc hwk.2.1 u hu g hg).imp (fun h1 => le_trans h1 (le_app_psi hBc')) id
  · exact app_lt_app_left B (psi_lt_psi_z_iff.mpr (Or.inl hwk.1))

/-- **The frame relation for a leaf child** `ψ_{w′}(0)` replacing any `ψ_s(y)` (the old child may rewrite; its
frame has `FrameDom`): the new state `B + ψ_{w′}(0)` is below the old one, and the new child's components are
at most itself or a component of `a`. -/
theorem lhdE_frame_leaf {a B s y w' : T} (hc : isOT (psi s y z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hdom : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → FrameDom a B s (H s y))
    (hlt : psi w' z z < psi s y z) (h1 : one ≤ w') (hwc : WCS a w') :
    LhdE (psi a (step a B w' z z) z) (psi a (step a B s y z) z) := by
  have hBc' : ∀ r ∈ summands B, psi w' z z ≤ r := fun r hr => le_trans (le_of_lt hlt) (hBc r hr)
  have hnew : step a B w' z z = app B (psi w' z z) := by
    rw [step_leaf]; exact add_eq_app_of_ge ⟨w', z, rfl⟩ B hBc'
  have hw's : w' ≤ s := by
    rcases psi_lt_psi_z_iff.mp hlt with h | ⟨h, _⟩
    · exact le_of_lt h
    · rw [h]
  -- the new state is below the old one
  have hgt : app B (psi w' z z) < step a B s y z := by
    unfold step
    split_ifs with ht
    · rw [H_eq hc]
      have hBhi := B_le_hi hc ht.1 hBc
      have hall : ∀ q ∈ summands (split y (psi (succ s) z z)).1, psi w' z z < q := by
        intro q hq
        have := split_fst_ge (psi (succ s) z z) y q hq
        exact lt_of_lt_of_le (psi_lt_psi_z_iff.mpr (Or.inl (lt_of_le_of_lt hw's (lt_succ_self s))))
          (not_lt.mp this)
      rcases (le_iff _ _).mp hBhi with hBlt | hBeq
      · apply app_lt_of_lt (lt_of_lt_of_le hBlt (le_app_self _ _))
        intro q hq
        rw [summands_app] at hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hall q hq
        · split at hq
          · simp [summands] at hq
          · simp [summands] at hq; rw [hq]; exact hlt
      · have hlo : (split y (psi (succ s) z z)).2 ≠ z := by
          intro h0
          have hy := split_app (psi (succ s) z z) y
          rw [h0, app_z_right, ← hBeq] at hy
          rw [hy] at ht; exact lt_irrefl' _ ht.1
        rw [if_neg hlo, ← hBeq]
        exact app_lt_app_left B hlt
    · rw [add_eq_app_of_ge ⟨s, y, rfl⟩ B hBc]
      exact app_lt_app_left B hlt
  have hdrop := drop_child_lhdD (a := a) hc hBc hdom
  rw [hnew]
  rcases hdrop with h | h
  · exfalso
    simp only [psi.injEq] at h
    have hBlt : B < app B (psi w' z z) := by
      have := app_lt_app_left B (show z < psi w' z z from T.z_lt_psi _ _ _)
      rwa [app_z_right] at this
    exact lt_irrefl' B (lt_of_lt_of_eq (lt_trans hBlt hgt) h.2.1.symm)
  right
  apply lhd_weak_childA h (by simp)
  · intro u hu g hg
    exact (self_small_weakA hwc h1 u hu g hg).imp (fun h2 => le_trans h2 (le_app_psi hBc')) id
  · exact hgt

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hVS : VSmallF M ρ) (hVN : VSmallNew M x ρ ρ') (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
  (hVR : VSmallR M ρ) (hVNR : VSmallNewR M x ρ ρ') (hSh : ShadowC M x ρ ρ') (hTNR : TailNR M x ρ)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hVR hVNR hSh hTNR

/-- **One `o` step of the drop.** -/
theorem po_of_R {i : Nat} (hi : i < x) (hv : PV M ρ ρ' i)
    (hch : ∀ c ∈ children (M.take x) i, Counted (M.take x) i c →
      PO ρ ρ' c ∧ PV M ρ ρ' c ∧ RClaim ρ ρ' c) :
    PO ρ ρ' i ∧ RClaim ρ ρ' i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : i < (M.take x).length := by omega
  have hiM : i < M.length := by omega
  have hoff := chg_off hx hC hG hC' hRk'
  unfold PO
  by_cases hCo : ChgX M x true i
  swap
  · have ho := (hoff i hi).1 hCo
    refine ⟨?_, rclaim_eq ho⟩
    rw [ho]
    exact ⟨Or.inl (Or.inl rfl), single_o hC hG hiM⟩
  by_cases hCv : ChgX M x false i
  · -- `v(i)` changes: no counted child in `M.take x`
    have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl hi
    have ho' := o_of_no_counted hC' hiT hv.2 hT.2.1
    refine ⟨⟨?_, by rw [ho']; exact ⟨by rw [isOT_psi_iff]; exact ⟨hv.2, rfl, rfl, z_le _,
      fun g hg => by simp [comps] at hg⟩, _, _, rfl⟩⟩, ?_⟩
    by_cases hl : LhdE (ρ'.v i) (ρ.v i)
    · rw [ho', o_spArg hC hG hiM]; exact Or.inl (lhdE_oq_v hl)
    rcases hv.1 with h | ⟨hW, -, -⟩
    · exact absurd h hl
    · right
      refine ⟨?_, Or.inr hl⟩
      rw [ho', o_spArg hC hG hiM]
      exact ⟨_, _, _, rfl, rfl, hW⟩
    · exact rclaim_zero ho'
  · -- `v(i)` does not change
    have hv' : ρ'.v i = ρ.v i := (hoff i hi).2 hCv
    obtain ⟨Tl, hTl⟩ := cl_prefix hx hR0 hZ2 hSD hZ1 hUAT hi
    have hvot : isOT (ρ.v i) = true := hG.ot_v i hiM
    rcases List.eq_nil_or_concat (CL (M.take x) i) with hnil | ⟨Lc, cs, hcl⟩
    · have hn : ∀ c ∈ children (M.take x) i, ¬ Counted (M.take x) i c := by
        intro c hc hcnt
        have : c ∈ CL (M.take x) i := by unfold CL; exact List.mem_filter.mpr ⟨hc, by simpa using hcnt⟩
        rw [hnil] at this; simp at this
      refine ⟨⟨Or.inl (o_frame_empty hC hG hF hC' hiT hiM hv' hnil), ?_⟩,
        rclaim_zero (o_of_no_counted hC' hiT (by rw [hv']; exact hvot) hn)⟩
      rw [o_of_no_counted hC' hiT (by rw [hv']; exact hvot) hn]
      exact ⟨by rw [isOT_psi_iff]; exact ⟨by rw [hv']; exact hvot, rfl, rfl, z_le _,
        fun g hg => by simp [comps] at hg⟩, _, _, rfl⟩
    · rw [List.concat_eq_append] at hcl
      have hcsT : cs ∈ children (M.take x) i ∧ Counted (M.take x) i cs := by
        have : cs ∈ CL (M.take x) i := by rw [hcl]; simp
        unfold CL at this; rw [List.mem_filter] at this; exact ⟨this.1, by simpa using this.2⟩
      obtain ⟨hPOc, hPVc, hRCc⟩ := hch cs hcsT.1 hcsT.2
      -- the earlier counted children do not change
      have hsame : ∀ d ∈ Lc, ρ'.o d = ρ.o d := by
        intro d hd
        have hdT : d ∈ CL (M.take x) i := by rw [hcl]; simp [hd]
        have hdc : d ∈ children (M.take x) i := by unfold CL at hdT; exact (List.mem_filter.mp hdT).1
        have hdcs : d < cs := by
          have hs := (children_sorted (M.take x) i).filter (fun c => decide (Counted (M.take x) i c))
          change (CL (M.take x) i).Pairwise _ at hs
          rw [hcl] at hs
          exact (List.pairwise_append.mp hs).2.2 d hd cs (by simp)
        have hdx : d < x := by
          rw [children_take, List.mem_filter] at hdc; simpa using hdc.2
        by_contra hne
        have hCd : ChgX M x true d := by
          by_contra hn; exact hne ((hoff d hdx).1 hn)
        exact chg_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hdc hCd cs hcsT.1 hdcs hcsT.2
      have hclM : CL M i = Lc ++ [cs] ++ Tl := by rw [hTl, hcl]
      have hcsM0 : cs < M.length := by
        have := (mem_children (cl_mem_children (show cs ∈ CL M i by rw [hclM]; simp))).2; omega
      have hcsx0 : cs < (M.take x).length := (mem_children hcsT.1).2
      have hvM : ∀ s y, ρ.o cs = psi s y z → s = ρ.v cs := by
        intro s y h
        obtain ⟨y0, hy0⟩ := o_psi_sub hC hcsM0
        rw [h] at hy0; simp only [psi.injEq] at hy0
        rw [hy0.1, sf_ot (hG.ot_v cs hcsM0)]
      have hvT : ∀ s y, ρ'.o cs = psi s y z → s = ρ'.v cs := by
        intro s y h
        obtain ⟨y0, hy0⟩ := o_psi_sub hC' hcsx0
        rw [h] at hy0; simp only [psi.injEq] at hy0
        rw [hy0.1, sf_ot hPVc.2]
      have hfr := hVS i hiM Lc cs Tl (by rw [hclM]; simp)
      have hchgv : ρ'.v cs ≠ ρ.v cs → ρ'.o cs = psi (ρ'.v cs) z z := by
        intro hvs
        have hCv : ChgX M x false cs := by
          by_contra hn; exact hvs ((hoff cs (by rw [hlenT] at hcsx0; exact hcsx0)).2 hn)
        have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl (by rw [hlenT] at hcsx0; exact hcsx0)
        exact o_of_no_counted hC' hcsx0 hPVc.2 hT.2.1
      have hssT : ∀ s y s' y', ρ.o cs = psi s y z → ρ'.o cs = psi s' y' z → y' ≠ z → s' = s := by
        intro s y s' y' h h' hy'
        rw [hvT s' y' h', hvM s y h]
        by_contra hvs
        rw [hchgv hvs] at h'; simp only [psi.injEq] at h'; exact hy' h'.2.1.symm
      have hsubA : ∀ s' y', ρ'.o cs = psi s' y' z → ∀ g ∈ comps (ρ.v i) s',
          g ≤ psi s' z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) := by
        intro s' y' h'
        rw [hvT s' y' h']
        by_cases hvs : ρ'.v cs = ρ.v cs
        · rw [hvs]; exact hfr
        · exact hVN i hi Lc cs hcl hvs
      have hpar : par M 0 cs = some i := by
        have := (mem_children_iff.mp hcsT.1).2
        rwa [par_take M 0 cs (by have := (mem_children hcsT.1).2; rw [List.length_take] at this; omega)] at this
      have hrelA := rel_of_po_pv hPOc hPVc hpar hvT hvM
      have hPOrel := o_frame_eval hC hG hF hC' hiT hiM hv' hcl hclM hsame hPOc.2 hrelA hssT
      have hcsM : cs < M.length := by
        have := (mem_children (cl_mem_children (show cs ∈ CL M i by rw [hclM]; simp))).2; omega
      obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
      rw [hclM] at hsM hpM
      simp only [List.map_append, List.map_cons, List.map_nil] at hsM hpM
      have hle' : ρ'.o cs ≤ ρ.o cs := by
        rcases hPOc.1 with h | ⟨h, -⟩
        · exact h.le
        · exact DRelOA.le (Or.inr h)
      have hp1 := List.pairwise_append.mp hpM
      have hLc : ∀ t ∈ Lc.map ρ.o, ρ.o cs ≤ t := fun t ht =>
        (List.pairwise_append.mp hp1.1).2.2 t ht _ (by simp)
      have hmapT : (CL (M.take x) i).map ρ'.o = Lc.map ρ.o ++ [ρ'.o cs] := by
        rw [hcl, List.map_append, List.map_singleton]
        congr 1; exact List.map_congr_left hsame
      have hsT : ∀ c ∈ CL (M.take x) i, Single (ρ'.o c) := by
        intro c hc
        rw [hcl] at hc
        rcases List.mem_append.mp hc with hc | hc
        · rw [hsame c hc]; exact hsM _ (by simp only [List.mem_append, List.mem_map, List.mem_cons]; exact Or.inl (Or.inl ⟨c, hc, rfl⟩))
        · simp at hc; rw [hc]; exact hPOc.2
      have hpT : ((CL (M.take x) i).map ρ'.o).Pairwise (fun a b => b ≤ a) := by
        rw [hmapT]
        exact List.pairwise_append.mpr ⟨(List.pairwise_append.mp hp1.1).1, by simp,
          fun t ht b hb => by simp at hb; rw [hb]; exact le_trans hle' (hLc t ht)⟩
      obtain ⟨s', y', hs'y'⟩ := hPOc.2.2
      have hform := o_last_form hC' hiT (by rw [hv']; exact hvot) hcl hsT hpT hs'y'
      have hLm : Lc.map ρ'.o = Lc.map ρ.o := List.map_congr_left hsame
      rw [hLm, hv'] at hform
      have hBot := hFO i hiM Lc cs Tl (by rw [hclM]; simp)
      have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (by simp [ht])) (List.pairwise_append.mp hp1.1).1
      have hBge : ∀ t, Single t → t ≤ ρ.o cs →
          ∀ q ∈ summands (spArg (ρ.v i) z (sumN (Lc.map ρ.o))), t ≤ q := by
        intro t ht htc
        obtain ⟨s0, y0, rfl⟩ := ht.2
        apply spArg_summands_ge ⟨s0, y0, rfl⟩ _ z hLs.1
        · rw [hLs.2]; intro q hq; exact le_trans htc (hLc q hq)
        · simp [summands]
      have hSi : isOT (psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s' y' z) z) = true := by
        rcases hPOc.1 with hrelL | ⟨⟨w1, w2, X, e1, _, _⟩, _⟩
        · -- a `⊴` child: one frame by `node_ot_hard`
          obtain ⟨s, y, hsy⟩ := (single_o hC hG hcsM).2
          have hcsS := single_o hC hG hcsM
          rw [hsy] at hcsS
          rw [hs'y', hsy] at hrelL
          have hCL : CL M i = Lc ++ cs :: Tl := by rw [hclM]; simp
          have hsLc : ∀ t ∈ Lc.map ρ.o ++ [ρ.o cs], Single t := fun t ht => hsM t (by
            rcases List.mem_append.mp ht with h | h
            · simp only [List.mem_append, List.mem_cons]; exact Or.inl (Or.inl h)
            · simp at h; rw [h]; simp)
          have hpLc : (Lc.map ρ.o ++ [ρ.o cs]).Pairwise (fun a b => b ≤ a) := hp1.1
          have hstate : spArg (ρ.v i) z (sumN ((Lc ++ [cs]).map ρ.o)) =
              step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z := by
            rw [List.map_append, List.map_singleton, sumN_append_dec hsLc hpLc,
              sumN_singleton (single_o hC hG hcsM), spArg_app, hsy, spArg_single]
          have hot : isOT (psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z) z) = true := by
            rw [← hstate]
            cases Tl with
            | nil =>
              have ho := o_spArg hC hG hiM
              rw [cvals_eq_map hC hG i, hclM] at ho
              simp only [List.append_nil] at ho
              rw [← ho]; exact hG.ot_o i hiM
            | cons c0 Tl' => exact hFO i hiM (Lc ++ [cs]) c0 Tl' (by rw [hclM])
          exact node_ot_hard hcsS.1 (by rw [← hs'y']; exact hPOc.2.1) hrelL
            (hBge _ (single_o hC hG hcsM) (le_refl _) |> fun h => by rw [hsy] at h; exact h)
            (hssT s y s' y' hsy hs'y') (by rw [hvM s y hsy]; exact hfr) (hsubA s' y' hs'y')
            (fun hss has ht' ht hhi => by
              subst hss
              have hhz : (split y (psi (succ s') z z)).1 ≠ z := by
                intro h; rw [h] at hhi; exact T.not_lt_z _ hhi
              have hc' : isOT (psi s' y' z) = true := by rw [← hs'y']; exact hPOc.2.1
              have hyy : y' ≤ y := by
                rcases (le_iff _ _).mp hrelL.le with h | h
                · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
                  · exact absurd h (lt_irrefl' _)
                  · exact le_of_lt h
                · simp only [psi.injEq] at h; rw [h.2.1]
              have hot' : isOT (psi (ρ.v i) (H s' y) z) = true := by
                have := hot; unfold step at this; rw [if_pos ht] at this; exact this
              apply hard_of_relR hc' has hvot hot' (H_mono hc' hcsS.1 hyy)
              apply hRCc s' y y' (ρ.v i) hsy hs'y'
                (fun h => lt_irrefl' _ (lt_trans (show ρ.v i < s' from has) h))
              intro u hu g hg
              rcases hVR i hiM Lc cs Tl hCL s' y hsy ht hhz u hu g hg with h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl (lt_of_le_of_lt h (lt_of_lt_of_le ht'.1 (le_H hc'))))
              · exact Or.inr (Or.inr h))
            hot hBot
        · -- a weak child `ψ_{w′}(0)`: the argument is `0`
          rw [hs'y'] at e1; simp only [psi.injEq] at e1
          apply step_ot_of_leB hBot (by rw [← hs'y']; exact hPOc.2.1)
          · exact hBge _ hPOc.2 hle' |> fun h => by rw [hs'y'] at h; exact h
          · exact hsubA s' y' hs'y'
          · intro _ g hg; rw [e1.2.1] at hg; simp [comps] at hg
      refine ⟨⟨Or.inl hPOrel, by rw [hform]; exact ⟨hSi, _, _, rfl⟩⟩, ?_⟩
      -- the claim at `i`
      intro p yy yy' q hyy hyy' hqp hhyp
      have hoM : ρ.o i = psi (ρ.v i) (spArg (ρ.v i) z (sumN ((Lc ++ [cs] ++ Tl).map ρ.o))) z := by
        have ho := o_spArg hC hG hiM
        rw [cvals_eq_map hC hG i, hclM] at ho
        exact ho
      rw [hoM] at hyy
      rw [hform] at hyy'
      simp only [psi.injEq] at hyy hyy'
      obtain ⟨rfl, rfl, -⟩ := hyy
      obtain ⟨-, rfl, -⟩ := hyy'
      obtain ⟨s, y, hsy⟩ := (single_o hC hG hcsM).2
      have hcsS := single_o hC hG hcsM
      have hc : isOT (psi s y z) = true := by rw [← hsy]; exact hcsS.1
      have hc' : isOT (psi s' y' z) = true := by rw [← hs'y']; exact hPOc.2.1
      have hBc : ∀ r ∈ summands (spArg (ρ.v i) z (sumN (Lc.map ρ.o))), psi s y z ≤ r := by
        have := hBge _ hcsS (le_refl _); rw [hsy] at this; exact this
      have hCL : CL M i = Lc ++ cs :: Tl := by rw [hclM]; simp
      have hsLc : ∀ t ∈ Lc.map ρ.o ++ [ρ.o cs], Single t := fun t ht => hsM t (by
        rcases List.mem_append.mp ht with h | h
        · simp only [List.mem_append, List.mem_cons]; exact Or.inl (Or.inl h)
        · simp at h; rw [h]; simp)
      have hpLc : (Lc.map ρ.o ++ [ρ.o cs]).Pairwise (fun a b => b ≤ a) := hp1.1
      have hstate : spArg (ρ.v i) z (sumN ((Lc ++ [cs]).map ρ.o)) =
          step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z := by
        rw [List.map_append, List.map_singleton, sumN_append_dec hsLc hpLc,
          sumN_singleton (single_o hC hG hcsM), spArg_app, hsy, spArg_single]
      have hY0 : isOT (psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z) z)
          = true := by
        rw [← hstate]
        cases Tl with
        | nil =>
          have ho := o_spArg hC hG hiM
          rw [cvals_eq_map hC hG i, hclM] at ho
          simp only [List.append_nil] at ho
          rw [← ho]; exact hG.ot_o i hiM
        | cons c0 Tl' => exact hFO i hiM (Lc ++ [cs]) c0 Tl' (by rw [hclM])
      have hrel : (LhdE (psi s' y' z) (psi s y z) ∧ (y' ≠ z → s' = s)) ∨
          (y' = z ∧ WkVA s' s ∧ WCS (ρ.v i) s') := by
        rcases hrelA with h | ⟨⟨w1, w2, X, e1, e2, hW⟩, hwc⟩
        · rw [hs'y', hsy] at h; exact Or.inl ⟨h, hssT s y s' y' hsy hs'y'⟩
        · have hwc' := hwc w1 e1
          rw [hs'y'] at e1; rw [hsy] at e2
          simp only [psi.injEq] at e1 e2
          right; refine ⟨e1.2.1, ?_, ?_⟩
          · rw [e1.1, e2.1]; exact hW
          · rw [e1.1]; exact hwc' 
      have hN : LhdE (psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s' y' z) z)
          (psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z) z) := by
        rcases hrel with ⟨hl, hss⟩ | ⟨rfl, hwk⟩
        · exact node_lhdD hc hc' hl hBc hss (fun hr => hF i hiM Lc cs Tl hCL s y hsy hr)
        · exact lhdE_frame_leaf hc hBc (fun hr => hF i hiM Lc cs Tl hCL s y hsy hr)
            (psi_lt_psi_z_iff.mpr (Or.inl hwk.1.1)) hwk.1.2.1 hwk.2
      have hRF := relR_frame (q := q) hc hc' hBc hrel hSi hY0 hN
        (fun hss q' hq' hyp' => by subst hss; exact hRCc s' y y' q' hsy hs'y' hq' hyp')
        (hVR i hiM Lc cs Tl hCL s y hsy)
        (fun ht hne hup u hu g hg => by
          have hv's : s' = ρ'.v cs := hvT s' y' hs'y'
          have hvs : s = ρ.v cs := hvM s y hsy
          have hne' : ρ'.v cs ≠ ρ.v cs := by rw [← hv's, ← hvs]; exact hne
          rw [hv's] at hg hup ⊢
          exact hVNR i hi Lc cs hcl hne' s y hsy ht hup u hu g hg)
        (hSh i hi Lc cs hcl s y s' y' hsy hs'y') hqp hhyp
      by_cases hTl : Tl = []
      · subst hTl
        rw [List.append_nil, hstate]; exact hRF
      · have hX'Y : step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s' y' z ≤
            step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z := by
          rcases (le_iff _ _).mp hN.le with h | h
          · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
            · exact absurd h (lt_irrefl' _)
            · exact le_of_lt h
          · simp only [psi.injEq] at h; rw [h.2.1]
        have hTNRi := hTNR i hi Lc cs Tl hcl hclM hTl
        obtain ⟨t0, Tl', rfl⟩ : ∃ t0 Tl', Tl = t0 :: Tl' := by
          cases Tl with
          | nil => exact absurd rfl hTl
          | cons t0 Tl' => exact ⟨t0, Tl', rfl⟩
        rw [hTNRi, hstate]
        have hsTl : ∀ t ∈ (t0 :: Tl').map ρ.o, Single t := fun t ht => hsM t (by
          simp only [List.mem_append]; exact Or.inr ht)
        have hpTl : ((t0 :: Tl').map ρ.o).Pairwise (fun a b => b ≤ a) := hp1.2.1
        have hsum : sumN ((t0 :: Tl').map ρ.o) = app (ρ.o t0) (sumN (Tl'.map ρ.o)) := by
          rw [List.map_cons]; exact sumN_cons_dec (by simpa using hsTl) (by simpa using hpTl)
        have ht0S : Single (ρ.o t0) := hsTl _ (by simp)
        obtain ⟨st, et, het⟩ := ht0S.2
        have ht0c : ρ.o t0 ≤ ρ.o cs := hp1.2.2 _ (by simp) _ (by simp)
        have hY : isOT (psi (ρ.v i) (app (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
            (sumN ((t0 :: Tl').map ρ.o))) z) = true := by
          have := hG.ot_o i hiM
          rw [hoM, hTNRi, hstate] at this
          exact this
        apply relR_tail hRF (H_mono hSi hY0 hX'Y) hY0 hY
        · rw [hsum, het]; simp [app]
        · intro r hr
          rw [hsum, het]
          show psi st et z ≤ r
          rw [← het]
          exact le_trans ht0c (by rw [hsy]; exact step_summands_ge hc hBc r hr)

/-- **One `v` step of the drop.** The bump-type frame (`hBump`) and the absorption at `x − 1` (`hX1`)
are hypotheses. -/
theorem pv_of_R {i : Nat} (hi : i < x) (hWC : WeakCS M x ρ ρ')
    (hBump : ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV M ρ ρ' i)
    (hX1 : ∀ k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
        (WCSP M ρ i (add (vOpt ρ (par M 1 i)) one) ∧
          (∀ g ∈ comps z (add (vOpt ρ (par M 1 i)) one), g < psi (add (vOpt ρ (par M 1 i)) one) z z) ∧
          NBParX M x i))
    (hup : ∀ k, upg (M.take x) i = some k → PV M ρ ρ' k ∧
      ∀ j ∈ children (M.take x) k, col (M.take x) j = bump (M.take x) k →
        ∀ k' ∈ children (M.take x) j, Single (ρ'.o k')) :
    PV M ρ ρ' i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : i < (M.take x).length := by omega
  have hiM : i < M.length := by omega
  have hoff := chg_off hx hC hG hC' hRk'
  by_cases hCv : ChgX M x false i
  swap
  · rw [PV, (hoff i hi).2 hCv]
    exact ⟨Or.inl (Or.inl rfl), hG.ot_v i hiM⟩
  have h1 := chgx_e1 hCv
  by_cases h2 : entry M 2 i = 0
  swap
  · exact hBump hCv h1 h2
  -- the row-1 parent does not change
  have hV : vOpt ρ' (par (M.take x) 1 i) = vOpt ρ (par M 1 i) := by
    rw [par_take M 1 i hi]
    cases hp : par M 1 i with
    | none => rfl
    | some m =>
      show ρ'.v m = ρ.v m
      have hm := par_lt M 1 i m hp
      apply (hoff m (by omega)).2
      intro hCm
      exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCm).1 rfl (by omega) |>.2.2 i hi hp
  have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  have hoot : ∀ k, ∀ j ∈ children M k, col M j = bump M k → ∀ k' ∈ children M j, isOT (ρ.o k') = true :=
    fun k j _ _ k' hk' => hG.ot_o k' (mem_children hk').2
  -- `v′(i)` when the upgrade is gone or absent
  have hv1 : upg (M.take x) i = none → ρ'.v i = sf (add (vOpt ρ (par M 1 i)) one) := by
    intro hu
    rw [(hC' i hiT).2]; unfold vRhs
    rw [entry_take M 1 hi, entry_take M 2 hi, if_neg h1, if_pos h2, hu, hV]
  by_cases hix : i + 1 < x
  · have hupT : upg (M.take x) i = upg M i := upg_take M hix
    cases hu : upg M i with
    | none =>
      have e1 := hv1 (by rw [hupT, hu])
      have e2 : ρ.v i = sf (add (vOpt ρ (par M 1 i)) one) := by
        rw [(hC i hiM).2]; unfold vRhs; rw [if_neg h1, if_pos h2, hu]
      rw [PV, e1, ← e2]
      exact ⟨Or.inl (Or.inl rfl), hG.ot_v i hiM⟩
    | some k =>
      have huT : upg (M.take x) i = some k := by rw [hupT, hu]
      obtain ⟨hPVk, hook⟩ := hup k huT
      have ek : ρ.v i = ρ.v k := v_upg_eq hC hiM h1 h2 hu hVot (hoot k)
      have ek' : ρ'.v i = ρ'.v k := v_upg_eq hC' hiT (by rw [entry_take M 1 hi]; exact h1)
        (by rw [entry_take M 2 hi]; exact h2) huT (by rw [hV]; exact hVot)
        (fun j hj hjb k' hk' => (hook j hj hjb k' hk').1)
      unfold PV
      rw [ek, ek']
      refine ⟨?_, hPVk.2⟩
      rcases hPVk.1 with h | ⟨hW, -, _⟩
      · exact Or.inl h
      · by_cases hlv : LhdE (ρ'.v k) (ρ.v k)
        · exact Or.inl hlv
        right
        refine ⟨hW, ?_, ?_⟩
        · have h' := hWC i hi (by rw [ek, ek']; exact hlv)
          rw [ek'] at h'; exact h'
        obtain ⟨m, _, _, _, hcase⟩ := upg_spec hu
        rcases hcase with rfl | ⟨hA, hki⟩
        · left
          intro c hc _
          have := leaf_of_upg_next hR0 hu c (Anc0.step (mem_children_iff.mp hc).2 (Anc0.refl i))
          have := (mem_children hc).1; omega
        · exfalso
          have hk : k < x := by omega
          have hCk : ChgX M x false k := by
            by_contra hn
            have := (hoff k hk).2 hn
            rw [this] at hW; exact lt_irrefl' _ hW.1
          exact no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
            ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCk).1 rfl hk) hk hu hA hki
  · -- `i = x − 1`
    have hixe : i + 1 = x := by omega
    have huT : upg (M.take x) i = none := by
      have : i = x - 1 := by omega
      rw [this]; exact upg_take_last M (by omega) (by omega)
    have e1 := hv1 huT
    have hot1 : isOT (add (vOpt ρ (par M 1 i)) one) = true := isOT_add hVot rfl
    unfold PV
    rw [e1, sf_ot hot1]
    refine ⟨?_, hot1⟩
    cases hu : upg M i with
    | none =>
      have e2 : ρ.v i = sf (add (vOpt ρ (par M 1 i)) one) := by
        rw [(hC i hiM).2]; unfold vRhs; rw [if_neg h1, if_pos h2, hu]
      rw [e2, sf_ot hot1]; exact Or.inl (Or.inl rfl)
    | some k =>
      have ek : ρ.v i = ρ.v k := v_upg_eq hC hiM h1 h2 hu hVot (hoot k)
      have hk := upg_lt hiM hu
      obtain ⟨m, hm1, hm2, hcol, _⟩ := upg_spec hu
      have hk1 : entry M 1 k ≠ 0 := by
        have : entry M 1 k = (col M k).2.1 := rfl
        rw [this, hcol]; exact h1
      have hk2 : entry M 2 k ≠ 0 := by
        have : entry M 2 k = (col M k).2.2 := rfl
        rw [this, hcol]; simp
      have hVk : vOpt ρ (par M 1 k) = vOpt ρ (par M 1 i) := by rw [hm1, hm2]
      obtain ⟨sW, yW, hvk, hWot, hW1⟩ := v_bump_form hC hk hk1 hk2 (by rw [hVk]; exact hVot) (hoot k)
      rw [hVk] at hvk
      rw [ek, hvk]
      by_cases hR : ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < psi sW yW z → Lhd z r (psi sW yW z)
      · have := v_frame_xm1 hVot hWot hW1 (fun r hr _ hlt => hR r hr hlt)
        rw [sf_ot hot1] at this
        exact Or.inl this
      · -- the weak alternative: `v′ = V + 1 < V + W`, `x` is the only possible counted child
        obtain ⟨hwc, -, hnb⟩ := (hX1 k _ hixe hu hvk (by simp)).resolve_left hR
        rcases (le_iff _ _).mp (add_le_add_single (vOpt ρ (par M 1 i)) ⟨z, z, rfl⟩ ⟨sW, yW, rfl⟩ hW1)
          with hlt | heq
        · refine Or.inr ⟨⟨hlt, le_add_single _ ⟨z, z, rfl⟩, hot1⟩, hwc, ?_⟩
          by_cases hxc : par M 0 x = some i
          · exact Or.inr (Or.inl ⟨fun c hc _ => by have := mem_children hc; omega, hnb.nb_of_child hxc,
              k, _, by omega, hu, hvk, by simp, hR⟩)
          · refine Or.inl fun c hc _ => hxc ?_
            have := mem_children hc
            obtain rfl : c = x := by omega
            exact (mem_children_iff.mp hc).2
        · exact Or.inl (Or.inl heq)

/-- **The drop lemma** (modulo the bump-type frames and the absorption at `x − 1`): at every column of
`M.take x`, `o` and `v` are `⊴` the values in `M` or weakly below them, and standard. -/
theorem drop_all_R
    (hBump : (∀ i, i < x → (∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < x →
        PO ρ ρ' k ∧ PV M ρ ρ' k) → ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV M ρ ρ' i) ∧
      WeakCS M x ρ ρ')
    (hX1 : ∀ i k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
        (WCSP M ρ i (add (vOpt ρ (par M 1 i)) one) ∧
          (∀ g ∈ comps z (add (vOpt ρ (par M 1 i)) one), g < psi (add (vOpt ρ (par M 1 i)) one) z z) ∧
          NBParX M x i)) :
    ∀ i, i < x → (PO ρ ρ' i ∧ RClaim ρ ρ' i) ∧ PV M ρ ρ' i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have key : ∀ N, ∀ i, i < x → (rk true i ≤ N → PO ρ ρ' i ∧ RClaim ρ ρ' i) ∧
      (rk false i ≤ N → PV M ρ ρ' i) := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      have hPV : ∀ i, i < x → rk false i ≤ N → PV M ρ ρ' i := by
        intro i hi hN
        obtain ⟨_, _, hR⟩ := hRk' i (by omega)
        apply pv_of_R hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hVR hVNR hSh hTNR hi hBump.2
        · intro hCv h1 h2
          apply hBump.1 i hi _ hCv h1 h2
          intro j hj hjb k hk hkx
          have hjx : j < x := by have := (mem_children hk).1; omega
          have hjT : j ∈ children (M.take x) i := by
            rw [children_take, List.mem_filter]; exact ⟨hj, by simpa using hjx⟩
          have hkT : k ∈ children (M.take x) j := by
            rw [children_take, List.mem_filter]; exact ⟨hk, by simpa using hkx⟩
          have hlt := (hR (by rw [entry_take M 1 hi]; exact h1)).2.2 (by rw [entry_take M 2 hi]; exact h2)
            j hjT (by rw [col_take M hjx, bump_take M hi]; exact hjb) k hkT
          have hlt2 := (hRk' k (by omega)).1
          exact ⟨((ih _ (by omega) k hkx).1 (Nat.le_refl _)).1, (ih _ (by omega) k hkx).2 (Nat.le_refl _)⟩
        · exact fun k W => hX1 i k W
        · intro k hk
          have h1 : entry (M.take x) 1 i ≠ 0 := by
            intro he; unfold upg at hk; rw [if_pos (Or.inl he)] at hk; cases hk
          have h2 : entry (M.take x) 2 i = 0 := by
            by_contra he
            have := upg_target_e2 hk
            unfold upg at hk
            split at hk
            · cases hk
            · rename_i hc
              have hz := hZ2 i
              rw [entry_take M 2 hi] at he hc
              exact hc (Or.inr (Or.inl (by omega)))
          have hlt := (hR h1).2.1 h2 k hk
          have hkx : k < x := by have := upg_lt (show i < (M.take x).length by omega) hk; omega
          refine ⟨(ih _ (by omega) k hkx).2 (Nat.le_refl _), fun j hj hjb k' hk' => ?_⟩
          have hk'x : k' < x := by have := (mem_children hk').2; omega
          have hk1 : entry (M.take x) 1 k ≠ 0 := by
            obtain ⟨m, _, _, hcol, _⟩ := upg_spec hk
            have : entry (M.take x) 1 k = (col (M.take x) k).2.1 := rfl
            rw [this, hcol]; exact h1
          have hk2 : entry (M.take x) 2 k ≠ 0 := by
            obtain ⟨m, _, _, hcol, _⟩ := upg_spec hk
            have : entry (M.take x) 2 k = (col (M.take x) k).2.2 := rfl
            rw [this, hcol]; simp
          have hlt2 := (hRk' k (by omega)).2.2 hk1 |>.2.2 hk2 j hj hjb k' hk'
          exact ((ih _ (by omega) k' hk'x).1 (Nat.le_refl _)).1.2
      refine fun i hi => ⟨fun hN => ?_, hPV i hi⟩
      obtain ⟨hvo, hc, _⟩ := hRk' i (by omega)
      apply po_of_R hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hVR hVNR hSh hTNR hi
      · exact hPV i hi (by omega)
      · intro c hcT hcnt
        have hlt := hc c hcT hcnt.1 hcnt.2
        have hcx : c < x := by have := (mem_children hcT).2; omega
        have hlt2 := (hRk' c (by omega)).1
        exact ⟨((ih _ (by omega) c hcx).1 (Nat.le_refl _)).1, (ih _ (by omega) c hcx).2 (Nat.le_refl _),
          ((ih _ (by omega) c hcx).1 (Nat.le_refl _)).2⟩
  intro i hi
  exact ⟨(key _ i hi).1 (Nat.le_refl _), (key _ i hi).2 (Nat.le_refl _)⟩

end

end Ytosk
