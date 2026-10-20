/-
**落とす補題の組み立て（順位の帰納法）。**

M′ = M.take x の各列で、
- o: `DRelO`（⊴ か弱い関係）、弱いなら M 側の引数は 0、o′ は標準形の単一の項（`PO`）。
- v: `DRelV`、v′ は標準形、v′ の成分 ≤ Ω_{v′}（`VSmallV`）、弱いなら M で数える子なし（`PV`）。
値の不変条件（`VSmall`・`FrameClosed`・`FrameOT`）と、のりしろの枠（`hBump`）・x − 1 の吸収（`hX1`）を仮定にとる。
-/
import Ytosk.V3DropRel
import Ytosk.V3StepOT

namespace Ytosk

open T

/-- The components of a subscript are at most `Ω_v`. -/
def VSmallV (t : T) : Prop := ∀ u, ∀ g ∈ comps u t, g ≤ psi t z z

/-- **Value invariant**: every `v` is small in this sense. (False on matrices reachable from SRO, e.g.
`v = ψ_0(Ω_{Ω_1} + …)`; the drop lemma uses `VSmallF` and `VSmallNew` instead.) -/
def VSmall (M : Mat) (ρ : Valn) : Prop := ∀ i, i < M.length → VSmallV (ρ.v i)

/-- **Value invariant** (frame form): for every counted child `c` of `i`, the components of `v(c)` at the
level `v(i)` are at most `Ω_{v(c)}` or at most the state `B` before `c`.
(2026-10-02 弱めた形。以前は「≤ Ω_{v(c)}」と書き換える枠での `VSmallV`。どちらも標準形で偽:
`v(c) = ψ_0(Ω_{Ω_1} + ψ_0(Ω_{Ω_1}))` の成分 Ω_{Ω_1}。書き換える枠の添字の成分は `FrameClosed` が受け持つ。) -/
def VSmallF (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL M i = L ++ c :: R →
    ∀ g ∈ comps (ρ.v i) (ρ.v c), g ≤ psi (ρ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (L.map ρ.o))

/-- **Hypothesis on the drop**: the same for a last counted child of `M.take x` whose `v` changes. -/
def VSmallNew (M : Mat) (x : Nat) (ρ ρ' : Valn) : Prop :=
  ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (M.take x) i = Lc ++ [cs] → ρ'.v cs ≠ ρ.v cs →
    ∀ g ∈ comps (ρ.v i) (ρ'.v cs), g ≤ psi (ρ'.v cs) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o))

/-- **Value invariant**: every state of every frame gives a standard `ψ`. -/
def FrameOT (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL M i = L ++ c :: R →
    isOT (psi (ρ.v i) (spArg (ρ.v i) z (sumN (L.map ρ.o))) z) = true

theorem VSmallV.subSmall {t : T} (h : VSmallV t) (a : T) : SubSmall a t := fun u _ g hg => h u g hg

/-- The claim at an `o` call. (2026-10-12: the weak alternative without the component condition `CS`; the
component condition is in `PV`.) -/
def PO (ρ ρ' : Valn) (i : Nat) : Prop :=
  (LhdE (ρ'.o i) (ρ.o i) ∨
    (WkOA (ρ'.o i) (ρ.o i) ∧ ((∃ w, ρ.o i = psi w z z) ∨ ¬ LhdE (ρ'.v i) (ρ.v i)))) ∧ Single (ρ'.o i)

/-- The parent of `i` is not a bump child. -/
def NBPar (M : Mat) (i : Nat) : Prop :=
  ∀ p g, par M 0 i = some p → par M 0 p = some g → col M p ≠ bump M g

/-- **The easy `t = 0` shape** (2026-10-17): the parent `r` of `x` is not a bump child, and when `r = x − 1`
its parent is not a bump child either. Outside it the `t = 0` engines use the strong absorption at `x − 1`
(`UpgAbsXW.toX`); inside, `r ≠ x − 1` needs no absorption (`PO.zero_of_ne`) and `r = x − 1` is the weak leaf
(`po_lhd_or_weak`, V3T0Weak). -/
def T0Easy (M : Mat) (x : Nat) : Prop := NBPar M x ∧ (par M 0 x = some (x - 1) → NBPar M (x - 1))

/-- **The component condition of a weak `v`** (2026-10-12; 2026-10-17 without the side conditions): countable
components, or components at the levels `u ≤ v(P_0 i)` countable or dominated by a component of `v(P_0 i)`
(ext1: (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)(5,1,1)(6,1,0)(2,1,0)(3,2,1)(4,2,1)(5,1,0), `i = 11`).
The earlier side conditions "the parent of `i` is not a bump child" and "`i` is not an upgrade target" are false
on standard matrices (expP: …(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,2,0), desc.md 2026-10-17); the component
condition at such columns is the hypothesis `WeakCS` (inside `BumpWeakSrc`). -/
def WCSP (M : Mat) (ρ : Valn) (i : Nat) (w : T) : Prop :=
  CS w ∨ WCS (vOpt ρ (par M 0 i)) w

theorem WCSP.wcs {M : Mat} {ρ : Valn} {i p : Nat} {w : T} (h : WCSP M ρ i w) (hp : par M 0 i = some p) :
    WCS (ρ.v p) w := by
  rcases h with h | h
  · exact WCS.of_cs h _
  · rw [hp] at h; exact h


/-- **The upgrade of `x − 1` fails the absorption condition** of `UpgAbsX` (the only source of a weak `v` at
`x − 1` with a counted child). -/
def UpgBad (M : Mat) (ρ : Valn) (i : Nat) : Prop :=
  ∃ k W, i + 2 = M.length ∧ upg M i = some k ∧ ρ.v k = add (vOpt ρ (par M 1 i)) W ∧ W ≠ z ∧
    ¬ ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W

/-- **The counted children of a weak column** (2026-10-12): none, or only the last column `x` when the parent
is not a bump child (T2Ext: `x − 1` loses its upgrade to an ancestor and has `x` as its counted child). -/
def CntX (M : Mat) (ρ : Valn) (i : Nat) : Prop :=
  (∀ c ∈ children M i, ¬ Counted M i c) ∨
    ((∀ c ∈ children M i, Counted M i c → c + 1 = M.length) ∧ NBPar M i ∧ UpgBad M ρ i)

/-- The claim at a `v` call. -/
def PV (M : Mat) (ρ ρ' : Valn) (i : Nat) : Prop :=
  (LhdE (ρ'.v i) (ρ.v i) ∨
    (WkVA (ρ'.v i) (ρ.v i) ∧ WCSP M ρ i (ρ'.v i) ∧ CntX M ρ i)) ∧
    isOT (ρ'.v i) = true

/-- **Hypothesis on the drop** (2026-10-17): every weakly changed `v` of `M.take x` has the component condition
`WCSP`. (The drop lemma derived it before from the side conditions of the old `WCSP`, which are false.) -/
def WeakCS (M : Mat) (x : Nat) (ρ ρ' : Valn) : Prop :=
  ∀ i, i < x → ¬ LhdE (ρ'.v i) (ρ.v i) → WCSP M ρ i (ρ'.v i)

/-- Under a bump child a weak column has no counted child. -/
theorem CntX.nocnt_of_bump {M : Mat} {ρ : Valn} {k j i : Nat} (h : CntX M ρ k)
    (hk : par M 0 k = some j) (hj : par M 0 j = some i) (hb : col M j = bump M i) :
    ∀ c ∈ children M k, ¬ Counted M k c := by
  rcases h with h | ⟨_, hn, _⟩
  · exact h
  · exact absurd hb (hn j i hk hj)

/-- **The relation of a child for `o_frame_eval`** from its `PO` and `PV`: a weak `o` with a `⊴` subscript is
`⊴`, a weak subscript carries the component condition at the parent. -/
theorem rel_of_po_pv {M : Mat} {ρ ρ' : Valn} {c i : Nat} (hPO : PO ρ ρ' c) (hPV : PV M ρ ρ' c)
    (hp : par M 0 c = some i) (hvT : ∀ s y, ρ'.o c = psi s y z → s = ρ'.v c)
    (hvM : ∀ s y, ρ.o c = psi s y z → s = ρ.v c) :
    LhdE (ρ'.o c) (ρ.o c) ∨ (WkOA (ρ'.o c) (ρ.o c) ∧
      ∀ w', ρ'.o c = psi w' z z → WCS (ρ.v i) w') := by
  rcases hPO.1 with h | ⟨hW, -⟩
  · exact Or.inl h
  rcases hPV.1 with hl | ⟨_, hwc, _⟩
  · left
    obtain ⟨w', w, X, h1, h2, _⟩ := hW
    rw [h1, h2, hvT _ _ h1, hvM _ _ h2]
    exact lhdE_oq_v hl
  · right
    refine ⟨hW, fun w' h' => ?_⟩
    rw [hvT _ _ h']
    exact hwc.wcs hp

/-- A changed `v` has row 1 nonzero. -/
theorem chgx_e1 {M : Mat} {x i : Nat} (h : ChgX M x false i) : entry M 1 i ≠ 0 := by
  cases h with
  | supg hne =>
    intro he; apply hne
    unfold upg; rw [if_pos (Or.inl he)]
  | snb h1 _ _ _ => exact h1
  | vpar h1 _ _ => exact h1
  | vupg h1 _ _ _ => exact h1
  | vbump h1 _ _ _ _ _ => exact h1

/-- The value of `o` through the last counted child. -/
theorem o_last_form {N : Mat} {σ : Valn} {i cs : Nat} {Lc : List Nat} {s y : T}
    (hC : Cons N σ) (hi : i < N.length) (hvot : isOT (σ.v i) = true) (hcl : CL N i = Lc ++ [cs])
    (hs : ∀ c ∈ CL N i, Single (σ.o c)) (hp : ((CL N i).map σ.o).Pairwise (fun a b => b ≤ a))
    (hcs : σ.o cs = psi s y z) :
    σ.o i = psi (σ.v i) (step (σ.v i) (spArg (σ.v i) z (sumN (Lc.map σ.o))) s y z) z := by
  rw [o_cl_loc hC hi hvot hs hp, hcl, List.map_append, List.map_singleton]
  rw [hcl, List.map_append, List.map_singleton] at hp
  have hs' : ∀ t ∈ Lc.map σ.o ++ [σ.o cs], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact hs c (by rw [hcl]; simp [hc])
    · simp at ht; rw [ht]; exact hs cs (by rw [hcl]; simp)
  rw [sumN_append_dec hs' hp, sumN_singleton (hs' _ (by simp)), spArg_app, hcs, spArg_single]

/-- **A bump-type `v` is `V + W`** with `W = ω^p` a single summand at least `1`. -/
theorem v_bump_form {N : Mat} {σ : Valn} {k : Nat} (hC : Cons N σ) (hk : k < N.length)
    (h1 : entry N 1 k ≠ 0) (h2 : entry N 2 k ≠ 0) (hVot : isOT (vOpt σ (par N 1 k)) = true)
    (hoot : ∀ j ∈ children N k, col N j = bump N k → ∀ k' ∈ children N j, isOT (σ.o k') = true) :
    ∃ sW yW, σ.v k = add (vOpt σ (par N 1 k)) (psi sW yW z) ∧ isOT (psi sW yW z) = true ∧
      one ≤ psi sW yW z := by
  have hY : isOT (sumN (one :: (children N k).map (bumpTerm N σ k))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      unfold bumpTerm
      split
      · rename_i hjb
        apply isOT_omega; apply isOT_sumN
        intro t' ht'
        obtain ⟨k', hk', rfl⟩ := List.mem_map.mp ht'
        exact hoot j hj hjb k' hk'
      · rfl
  obtain ⟨sW, yW, hWf⟩ := (single_omega hY).2
  refine ⟨sW, yW, ?_, by rw [← hWf]; exact isOT_omega hY, by rw [← hWf]; exact one_le_omega hY⟩
  rw [(hC k hk).2]; unfold vRhs
  rw [if_neg h1, if_neg h2, hWf, sf_ot (isOT_add hVot (by rw [← hWf]; exact isOT_omega hY))]

theorem vsmall_add_one {V : T} (hV : isOT V = true) (hs : VSmallV V) : VSmallV (add V one) := by
  have hge : ∀ q ∈ summands V, one ≤ q := by
    intro q hq
    obtain ⟨a, b, rfl⟩ : ∃ a b, q = psi a b z := by
      clear hs hV
      induction V with
      | z => simp [summands] at hq
      | psi a b c _ _ ih =>
        simp only [summands, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact ⟨a, b, rfl⟩
        · exact ih hq
    exact one_le_of_ne_z (by simp)
  have he : add V one = app V one := add_eq_app_of_ge (c := one) ⟨z, z, rfl⟩ V hge
  rw [he]
  have hlt : V < app V one := by
    have := app_lt_app_left V (show z < one from T.z_lt_psi _ _ _)
    rwa [app_z_right] at this
  intro u g hg
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact le_trans (hs u g hg) (le_of_lt (by rw [psi_lt_psi_z_iff]; exact Or.inl hlt))
  · have : g = z := by
      simp only [one, comps, List.mem_append] at hg
      split at hg
      · simp at hg
      · simp at hg; exact hg
    rw [this]; exact z_le _

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hVS : VSmallF M ρ) (hVN : VSmallNew M x ρ ρ') (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
  (hArgT : ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (M.take x) i = Lc ++ [cs] → ∀ s y,
    ρ'.o cs = psi s y z → ¬ lt s (ρ.v i) = true →
    ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hArgT

/-- **One `o` step of the drop.** -/
theorem po_of {i : Nat} (hi : i < x) (hv : PV M ρ ρ' i)
    (hch : ∀ c ∈ children (M.take x) i, Counted (M.take x) i c → PO ρ ρ' c ∧ PV M ρ ρ' c) :
    PO ρ ρ' i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : i < (M.take x).length := by omega
  have hiM : i < M.length := by omega
  have hoff := chg_off hx hC hG hC' hRk'
  unfold PO
  by_cases hCo : ChgX M x true i
  swap
  · rw [(hoff i hi).1 hCo]
    exact ⟨Or.inl (Or.inl rfl), single_o hC hG hiM⟩
  by_cases hCv : ChgX M x false i
  · -- `v(i)` changes: no counted child in `M.take x`
    have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl hi
    have ho' := o_of_no_counted hC' hiT hv.2 hT.2.1
    refine ⟨?_, by rw [ho']; exact ⟨by rw [isOT_psi_iff]; exact ⟨hv.2, rfl, rfl, z_le _,
      fun g hg => by simp [comps] at hg⟩, _, _, rfl⟩⟩
    by_cases hl : LhdE (ρ'.v i) (ρ.v i)
    · rw [ho', o_spArg hC hG hiM]; exact Or.inl (lhdE_oq_v hl)
    rcases hv.1 with h | ⟨hW, -, -⟩
    · exact absurd h hl
    · right
      refine ⟨?_, Or.inr hl⟩
      rw [ho', o_spArg hC hG hiM]
      exact ⟨_, _, _, rfl, rfl, hW⟩
  · -- `v(i)` does not change
    have hv' : ρ'.v i = ρ.v i := (hoff i hi).2 hCv
    obtain ⟨Tl, hTl⟩ := cl_prefix hx hR0 hZ2 hSD hZ1 hUAT hi
    have hvot : isOT (ρ.v i) = true := hG.ot_v i hiM
    rcases List.eq_nil_or_concat (CL (M.take x) i) with hnil | ⟨Lc, cs, hcl⟩
    · have hn : ∀ c ∈ children (M.take x) i, ¬ Counted (M.take x) i c := by
        intro c hc hcnt
        have : c ∈ CL (M.take x) i := by unfold CL; exact List.mem_filter.mpr ⟨hc, by simpa using hcnt⟩
        rw [hnil] at this; simp at this
      refine ⟨Or.inl (o_frame_empty hC hG hF hC' hiT hiM hv' hnil), ?_⟩
      rw [o_of_no_counted hC' hiT (by rw [hv']; exact hvot) hn]
      exact ⟨by rw [isOT_psi_iff]; exact ⟨by rw [hv']; exact hvot, rfl, rfl, z_le _,
        fun g hg => by simp [comps] at hg⟩, _, _, rfl⟩
    · rw [List.concat_eq_append] at hcl
      have hcsT : cs ∈ children (M.take x) i ∧ Counted (M.take x) i cs := by
        have : cs ∈ CL (M.take x) i := by rw [hcl]; simp
        unfold CL at this; rw [List.mem_filter] at this; exact ⟨this.1, by simpa using this.2⟩
      obtain ⟨hPOc, hPVc⟩ := hch cs hcsT.1 hcsT.2
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
      -- a changed `v(cs)`: `cs` has no counted child in `M.take x`
      have hchgv : ρ'.v cs ≠ ρ.v cs → ρ'.o cs = psi (ρ'.v cs) z z := by
        intro hvs
        have hCv : ChgX M x false cs := by
          by_contra hn; exact hvs ((hoff cs (by rw [hlenT] at hcsx0; exact hcsx0)).2 hn)
        have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl (by rw [hlenT] at hcsx0; exact hcsx0)
        exact o_of_no_counted hC' hcsx0 hPVc.2 hT.2.1
      have hcsx' : cs < x := by rw [hlenT] at hcsx0; exact hcsx0
      have hpar : par M 0 cs = some i := by
        have := (mem_children_iff.mp hcsT.1).2; rwa [par_take M 0 cs hcsx'] at this
      refine ⟨Or.inl (o_frame_eval hC hG hF hC' hiT hiM hv' hcl hclM hsame hPOc.2
        (rel_of_po_pv hPOc hPVc hpar hvT hvM)
        (fun s y s' y' h h' hy' => by
          rw [hvT s' y' h', hvM s y h]
          by_contra hvs
          rw [hchgv hvs] at h'; simp only [psi.injEq] at h'; exact hy' h'.2.1.symm)), ?_⟩
      -- `o′(i)` is standard
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
      rw [hform, hLm, hv']
      refine ⟨?_, _, _, rfl⟩
      have hBot := hFO i hiM Lc cs Tl (by rw [hclM]; simp)
      have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (by simp [ht])) (List.pairwise_append.mp hp1.1).1
      apply step_ot_of_leB hBot (by rw [← hs'y']; exact hPOc.2.1)
      · apply spArg_summands_ge ⟨s', y', rfl⟩ _ z hLs.1
        · rw [hLs.2]; intro q hq; rw [← hs'y']; exact le_trans hle' (hLc q hq)
        · simp [summands]
      · rw [hvT s' y' hs'y']
        by_cases hvs : ρ'.v cs = ρ.v cs
        · rw [hvs]; exact hfr
        · exact hVN i hi Lc cs hcl hvs
      · intro hsa g hg
        exact hArgT i hi Lc cs hcl s' y' hs'y' hsa g hg

/-- **One `v` step of the drop.** The bump-type frame (`hBump`) and the absorption at `x − 1` (`hX1`)
are hypotheses. -/
theorem pv_of {i : Nat} (hi : i < x) (hWC : WeakCS M x ρ ρ')
    (hBump : ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV M ρ ρ' i)
    (hX1 : ∀ k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
        (WCSP M ρ i (add (vOpt ρ (par M 1 i)) one) ∧
          (∀ g ∈ comps z (add (vOpt ρ (par M 1 i)) one), g < psi (add (vOpt ρ (par M 1 i)) one) z z) ∧
          NBPar M i))
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
        · refine Or.inr ⟨⟨hlt, le_add_single _ ⟨z, z, rfl⟩, hot1⟩, hwc,
            Or.inr ⟨fun c hc _ => ?_, hnb, k, _, by omega, hu, hvk, by simp, hR⟩⟩
          have := mem_children hc; omega
        · exact Or.inl (Or.inl heq)

/-- **The drop lemma** (modulo the bump-type frames and the absorption at `x − 1`): at every column of
`M.take x`, `o` and `v` are `⊴` the values in `M` or weakly below them, and standard. -/
theorem drop_all
    (hBump : (∀ i, i < x → (∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < x →
        PO ρ ρ' k ∧ PV M ρ ρ' k) → ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV M ρ ρ' i) ∧
      WeakCS M x ρ ρ')
    (hX1 : ∀ i k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
        (WCSP M ρ i (add (vOpt ρ (par M 1 i)) one) ∧
          (∀ g ∈ comps z (add (vOpt ρ (par M 1 i)) one), g < psi (add (vOpt ρ (par M 1 i)) one) z z) ∧
          NBPar M i)) :
    ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have key : ∀ N, ∀ i, i < x → (rk true i ≤ N → PO ρ ρ' i) ∧ (rk false i ≤ N → PV M ρ ρ' i) := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      have hPV : ∀ i, i < x → rk false i ≤ N → PV M ρ ρ' i := by
        intro i hi hN
        obtain ⟨_, _, hR⟩ := hRk' i (by omega)
        apply pv_of hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hArgT hi hBump.2
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
          exact ⟨(ih _ (by omega) k hkx).1 (Nat.le_refl _), (ih _ (by omega) k hkx).2 (Nat.le_refl _)⟩
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
          exact ((ih _ (by omega) k' hk'x).1 (Nat.le_refl _)).2
      refine fun i hi => ⟨fun hN => ?_, hPV i hi⟩
      obtain ⟨hvo, hc, _⟩ := hRk' i (by omega)
      apply po_of hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hArgT hi
      · exact hPV i hi (by omega)
      · intro c hcT hcnt
        have hlt := hc c hcT hcnt.1 hcnt.2
        have hcx : c < x := by have := (mem_children hcT).2; omega
        have hlt2 := (hRk' c (by omega)).1
        exact ⟨(ih _ (by omega) c hcx).1 (Nat.le_refl _), (ih _ (by omega) c hcx).2 (Nat.le_refl _)⟩
  intro i hi
  exact ⟨(key _ i hi).1 (Nat.le_refl _), (key _ i hi).2 (Nat.le_refl _)⟩

end

end Ytosk
