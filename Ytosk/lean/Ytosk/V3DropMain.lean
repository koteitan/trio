/-
**落とす補題の組み立て（順位の帰納法）。**

M′ = M.take x の各列で、
- o: `DRelO`（⊴ か弱い関係）、弱いなら M 側の引数は 0、o′ は標準形の単一の項（`PO`）。
- v: `DRelV`、v′ は標準形、v′ の成分 ≤ Ω_{v′}（`VSmallV`）、弱いなら M で数える子なし（`PV`）。
値の不変条件（`VSmall`・`FrameClosed`・`FrameOT`）と、のりしろの枠（`hBump`）・x − 1 の吸収（`hX1`）を仮定にとる。
-/
import Ytosk.V3DropRel

namespace Ytosk

open T

/-- The components of a subscript are at most `Ω_v`. -/
def VSmallV (t : T) : Prop := ∀ u, ∀ g ∈ comps u t, g ≤ psi t z z

/-- **Value invariant**: every `v` is small in this sense. -/
def VSmall (M : Mat) (ρ : Valn) : Prop := ∀ i, i < M.length → VSmallV (ρ.v i)

/-- **Value invariant**: every state of every frame gives a standard `ψ`. -/
def FrameOT (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL M i = L ++ c :: R →
    isOT (psi (ρ.v i) (spArg (ρ.v i) z (sumN (L.map ρ.o))) z) = true

theorem VSmallV.subSmall {t : T} (h : VSmallV t) (a : T) : SubSmall a t := fun u _ g hg => h u g hg

/-- The claim at an `o` call. -/
def PO (ρ ρ' : Valn) (i : Nat) : Prop :=
  (LhdE (ρ'.o i) (ρ.o i) ∨ (WkO (ρ'.o i) (ρ.o i) ∧ ∃ w, ρ.o i = psi w z z)) ∧ Single (ρ'.o i)

/-- The claim at a `v` call. -/
def PV (M : Mat) (ρ ρ' : Valn) (i : Nat) : Prop :=
  (LhdE (ρ'.v i) (ρ.v i) ∨ (WkV (ρ'.v i) (ρ.v i) ∧ ∀ c ∈ children M i, ¬ Counted M i c)) ∧
    isOT (ρ'.v i) = true ∧ VSmallV (ρ'.v i)

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

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hVS : VSmall M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
  (hStep : ∀ a B s y, isOT (psi a B z) = true → isOT (psi s y z) = true →
    (∀ q ∈ summands B, psi s y z ≤ q) → SubSmall a s → isOT (psi a (step a B s y z) z) = true)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hF hFO hStep

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
    have ho' := o_of_no_counted hC' hiT hv.2.1 hT.2.1
    refine ⟨?_, by rw [ho']; exact ⟨by rw [isOT_psi_iff]; exact ⟨hv.2.1, rfl, rfl, z_le _,
      fun g hg => by simp [comps] at hg⟩, _, _, rfl⟩⟩
    rcases hv.1 with h | ⟨hW, hnc⟩
    · rw [ho', o_spArg hC hG hiM]; exact Or.inl (lhdE_oq_v h)
    · right
      have ho := o_of_no_counted hC hiM (hG.ot_v i hiM) hnc
      rw [ho', ho]
      exact ⟨⟨_, _, z, rfl, rfl, hW⟩, _, rfl⟩
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
      refine ⟨Or.inl (o_frame_eval hC hG hF hC' hiT hiM hv' hcl hclM hsame hPOc.2 hPOc.1
        (fun s y h => by
          have hs : s = ρ.v cs := by
            obtain ⟨y0, hy0⟩ := o_psi_sub hC (show cs < M.length by
              have := (mem_children (cl_mem_children (show cs ∈ CL M i by rw [hclM]; simp))).2; omega)
            rw [h] at hy0; simp only [psi.injEq] at hy0
            rw [hy0.1, sf_ot (hG.ot_v cs (by
              have := (mem_children (cl_mem_children (show cs ∈ CL M i by rw [hclM]; simp))).2; omega))]
          rw [hs]; exact (hVS cs (by
            have := (mem_children (cl_mem_children (show cs ∈ CL M i by rw [hclM]; simp))).2; omega)).subSmall _)
        (fun s y h => by
          have hcsx : cs < (M.take x).length := (mem_children hcsT.1).2
          obtain ⟨y0, hy0⟩ := o_psi_sub hC' hcsx
          rw [h] at hy0; simp only [psi.injEq] at hy0
          rw [hy0.1, sf_ot hPVc.2.1]; exact hPVc.2.2.subSmall _)), ?_⟩
      -- `o′(i)` is standard
      have hcsM : cs < M.length := by
        have := (mem_children (cl_mem_children (show cs ∈ CL M i by rw [hclM]; simp))).2; omega
      obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
      rw [hclM] at hsM hpM
      simp only [List.map_append, List.map_cons, List.map_nil] at hsM hpM
      have hle' : ρ'.o cs ≤ ρ.o cs := by
        rcases hPOc.1 with h | ⟨h, _⟩
        · exact h.le
        · exact DRelO.le (Or.inr h)
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
      apply hStep _ _ _ _ hBot (by rw [← hs'y']; exact hPOc.2.1)
      · apply spArg_summands_ge ⟨s', y', rfl⟩ _ z hLs.1
        · rw [hLs.2]; intro q hq; rw [← hs'y']; exact le_trans hle' (hLc q hq)
        · simp [summands]
      · have hcsx : cs < (M.take x).length := (mem_children hcsT.1).2
        obtain ⟨y0, hy0⟩ := o_psi_sub hC' hcsx
        rw [hs'y'] at hy0; simp only [psi.injEq] at hy0
        rw [hy0.1, sf_ot hPVc.2.1]; exact hPVc.2.2.subSmall _
end

end Ytosk
