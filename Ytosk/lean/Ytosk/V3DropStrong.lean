/-
**落とす補題の強い形: M′ の値についての仮定 hArgT を狭める。**

`node_ot` の仮定 hy（引数どうしの ◁_η）を、それが使われる場合（書き換え同士・添字同じ・a < s・高い部分が違う）の
成分の上界そのものに置き換えた `node_ot_hard`。これで o の枠の標準形は
- 弱い子（o′ = ψ_{w′}(0)）では仮定なし、
- ⊴ の子では「難しい場合」の成分の上界だけを仮定
にでき、`drop_all` の hArgT（s′ ≥ a のすべての枠）を狭い仮定 `HardArg` に替えられる（`drop_all_hard`）。
-/
import Ytosk.V3DropMain
import Ytosk.V3NodeOT

namespace Ytosk

open T

/-- **One frame keeps the new parent standard.** -/
theorem node_ot_hard {a B s' y' s y : T}
    (hc : isOT (psi s y z) = true) (hc' : isOT (psi s' y' z) = true)
    (hrel : LhdE (psi s' y' z) (psi s y z))
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hsub : SubSmall a s) (hsub' : SubSmall a s')
    (hBcl : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) →
      (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → Closed a B)
    (hy : s' = s → lt a s = true → (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) →
      (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) →
      (split y' (psi (succ s) z z)).1 < (split y (psi (succ s) z z)).1 → ∀ g ∈ comps a y', g ≤ H s y')
    (hot : isOT (psi a (step a B s y z) z) = true) (hBot : isOT (psi a B z) = true) :
    isOT (psi a (step a B s' y' z) z) = true := by
  have ha := isOT_sub hBot
  have hX'ot : isOT (step a B s' y' z) = true := isOT_step (isOT_arg hBot) hc'
  rcases hrel with h | hl
  · simp only [psi.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h; exact hot
  by_cases ht' : lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true
  · by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
    · -- both rewrite
      have hst : step a B s y z = H s y := by unfold step; rw [if_pos ht]
      have hst' : step a B s' y' z = H s' y' := by unfold step; rw [if_pos ht']
      rcases psi_lt_psi_z_iff.mp hl.1 with hss | ⟨hs, hyy⟩
      · obtain ⟨hcomp, hyle⟩ := comps_le_of_sub_lt hl hss hsub'
        rw [hst', H_of_le_om hc' (ne_z_of_lt ht'.1) hyle] at hX'ot ⊢
        exact ot_parent_small ha hX'ot (closed_of_le_om hcomp a (lt_irrefl' a))
      · subst s'
        rw [hst] at hot
        rw [hst'] at hX'ot ⊢
        rcases split_mono (psi (succ s) z z) hyy with hhi | ⟨hhi, hlo⟩
        · -- different high parts
          have has := le_of_trig ht.2
          have hcy : ∀ g ∈ comps a y', g ≤ H s y' := by
            by_cases has' : lt a s = true
            · exact hy rfl has' ht' ht hhi
            · have has2 : a = s := le_antisymm has (not_lt.mp has')
              subst has2
              intro g hg
              exact le_trans (le_of_lt (comps_lt hc' g hg))
                (y_le_step (B := B) hc' (fun q hq => le_trans (le_of_lt hl.1) (hBc q hq))
                  (lt_irrefl' _) |>.trans (le_of_eq hst'))
          apply ot_parent_small ha hX'ot
          have hOm := om_le_H hc' (ne_z_of_lt ht'.1)
          intro g hg
          have hsu : ¬ s < a := not_lt.mpr has
          have hHX := H_eq hc'
          rw [hHX] at hg
          rw [comps_app] at hg
          rcases List.mem_append.mp hg with hg | hg
          · apply hcy
            have e := split_app (psi (succ s) z z) y'
            have : g ∈ comps a (app (split y' (psi (succ s) z z)).1 (split y' (psi (succ s) z z)).2) := by
              rw [comps_app]; exact List.mem_append_left _ hg
            rwa [e] at this
          · split at hg
            · simp [comps] at hg
            · rw [comps_psi_z_of_ge hsu] at hg
              simp only [List.mem_cons, List.mem_append] at hg
              rcases hg with rfl | hg | hg
              · exact y_le_step (B := B) hc' (fun q hq => le_trans (le_of_lt hl.1) (hBc q hq))
                  (not_lt.mpr has) |>.trans (le_of_eq hst')
              · exact hcy g hg
              · exact le_trans (hsub a (lt_irrefl' a) g hg) hOm
        · -- same high part: argument-level `◁`
          have hlo0 : (split y (psi (succ s) z z)).2 ≠ z := by
            intro h; rw [h] at hlo; exact T.not_lt_z _ hlo
          apply ot_parent_lhd hot hX'ot
          rw [H_eq hc', H_eq hc, if_neg hlo0, hhi]
          by_cases hl' : (split y' (psi (succ s) z z)).2 = z
          · rw [if_pos hl', app_z_right]; exact lhdE_prefix _ _
          · rw [if_neg hl']; exact lhdE_app _ (Or.inr hl)
    · -- only the new child rewrites: `B = 0`, `X' = c'`, `X = c`
      have hac : psi a z z < psi s y z := lt_trans (show psi a z z < psi s' y' z from ht'.2) hl.1
      have hyB : ¬ B < y := fun h => ht ⟨h, hac⟩
      rcases psi_lt_psi_z_iff.mp hl.1 with hss | ⟨rfl, hyy⟩
      · obtain ⟨_, hyle⟩ := comps_le_of_sub_lt hl hss hsub'
        by_cases hBz : B = z
        · subst hBz
          have hyz : y = z := by
            by_contra h; exact hyB (lt_of_le_of_ne (z_le _) (Ne.symm h))
          subst hyz
          have hst' : step a z s' y' z = psi s' y' z := by
            unfold step; rw [if_pos ht', H_of_le_om hc' (ne_z_of_lt ht'.1) hyle]
          have hst : step a z s z z = psi s z z := by unfold step; rw [if_neg ht]; rfl
          rw [hst] at hot
          rw [hst'] at hX'ot ⊢
          exact ot_parent_lhd hot hX'ot (Or.inr hl)
        · exfalso
          have hcB : psi s y z ≤ B := le_trans (hBc _ (head_mem_summands hBz)) (head_le_self B)
          have hy'c : y' ≤ psi s y z :=
            le_trans hyle (le_trans (psi_le_psi_arg (z_le y')) (le_of_lt hl.1))
          exact lt_irrefl' B (lt_of_lt_of_le (show B < y' from ht'.1) (le_trans hy'c hcB))
      · exact absurd (lt_trans (show B < y' from ht'.1) hyy) hyB
  · by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
    · -- only the old child rewrites: the small route
      have hst' : step a B s' y' z = app B (psi s' y' z) := by
        unfold step; rw [if_neg ht', step_add (fun q hq => le_trans (le_of_lt hl.1) (hBc q hq))]
      rw [hst'] at hX'ot ⊢
      exact ot_parent_small ha hX'ot
        (closed_tn hl ht' ht hBc (hBcl ht' ht) hsub hsub' a (lt_irrefl' a))
    · -- no rewrite
      exact ot_parent_lhd hot hX'ot (lhdE_step_nn' (Or.inr hl) ht' ht hBc)

/-- **The remaining hypothesis on `M.take x`** (narrowed from `hArgT`): in a frame of `M.take x` whose last
counted child `cs` is in the `⊴` relation with the same subscript `s > v(i)`, both the old and the new child
rewrite the state, and the high parts differ, the components of the new argument at the level `v(i)` are
at most `H s y′`. -/
def HardArg (M : Mat) (x : Nat) (ρ ρ' : Valn) : Prop :=
  ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (M.take x) i = Lc ++ [cs] → ∀ s y' y,
    ρ'.o cs = psi s y' z → ρ.o cs = psi s y z → lt (ρ.v i) s = true →
    (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s y' z) = true) →
    (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
    (split y' (psi (succ s) z z)).1 < (split y (psi (succ s) z z)).1 →
    ∀ g ∈ comps (ρ.v i) y', g ≤ H s y'

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hVS : VSmall M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
  (hHard : HardArg M x ρ ρ')
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hF hFO hHard

/-- **One `o` step of the drop.** -/
theorem po_of_hard {i : Nat} (hi : i < x) (hv : PV M ρ ρ' i)
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
      have hsub' : SubSmall (ρ.v i) s' := by
        have hcsx : cs < (M.take x).length := (mem_children hcsT.1).2
        obtain ⟨y0, hy0⟩ := o_psi_sub hC' hcsx
        rw [hs'y'] at hy0; simp only [psi.injEq] at hy0
        rw [hy0.1, sf_ot hPVc.2.1]; exact hPVc.2.2.subSmall _
      have hBge : ∀ t, Single t → t ≤ ρ.o cs →
          ∀ q ∈ summands (spArg (ρ.v i) z (sumN (Lc.map ρ.o))), t ≤ q := by
        intro t ht htc
        obtain ⟨s0, y0, rfl⟩ := ht.2
        apply spArg_summands_ge ⟨s0, y0, rfl⟩ _ z hLs.1
        · rw [hLs.2]; intro q hq; exact le_trans htc (hLc q hq)
        · simp [summands]
      rcases hPOc.1 with hrelL | ⟨⟨w1, w2, X, e1, _, _⟩, _⟩
      · -- a `⊴` child: one frame by `node_ot_hard`
        obtain ⟨s, y, hsy⟩ := (single_o hC hG hcsM).2
        have hcsS := single_o hC hG hcsM
        rw [hsy] at hcsS
        rw [hs'y', hsy] at hrelL
        have hsub : SubSmall (ρ.v i) s := by
          obtain ⟨y0, hy0⟩ := o_psi_sub hC hcsM
          rw [hsy] at hy0; simp only [psi.injEq] at hy0
          rw [hy0.1, sf_ot (hG.ot_v cs hcsM)]; exact (hVS cs hcsM).subSmall _
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
          hsub hsub' (fun _ hr => hF i hiM Lc cs Tl hCL s y hsy hr)
          (fun hss has ht' ht hhi => by
            subst hss
            exact hHard i hi Lc cs hcl s' y' y hs'y' hsy has ht' ht hhi)
          hot hBot
      · -- a weak child `ψ_{w′}(0)`: the argument is `0`
        rw [hs'y'] at e1; simp only [psi.injEq] at e1
        apply step_ot_of_le hBot (by rw [← hs'y']; exact hPOc.2.1)
        · exact hBge _ hPOc.2 hle' |> fun h => by rw [hs'y'] at h; exact h
        · exact hsub'
        · intro _ g hg; rw [e1.2.1] at hg; simp [comps] at hg

/-- **One `v` step of the drop.** The bump-type frame (`hBump`) and the absorption at `x − 1` (`hX1`)
are hypotheses. -/
theorem pv_of_hard {i : Nat} (hi : i < x)
    (hBump : ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV M ρ ρ' i)
    (hX1 : ∀ k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W)
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
    exact ⟨Or.inl (Or.inl rfl), hG.ot_v i hiM, hVS i hiM⟩
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
  have hVs : VSmallV (vOpt ρ (par M 1 i)) := by
    cases hp : par M 1 i with
    | none => intro u g hg; simp [vOpt, comps] at hg
    | some m => exact hVS m (by have := par_lt M 1 i m hp; omega)
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
      exact ⟨Or.inl (Or.inl rfl), hG.ot_v i hiM, hVS i hiM⟩
    | some k =>
      have huT : upg (M.take x) i = some k := by rw [hupT, hu]
      obtain ⟨hPVk, hook⟩ := hup k huT
      have ek : ρ.v i = ρ.v k := v_upg_eq hC hiM h1 h2 hu hVot (hoot k)
      have ek' : ρ'.v i = ρ'.v k := v_upg_eq hC' hiT (by rw [entry_take M 1 hi]; exact h1)
        (by rw [entry_take M 2 hi]; exact h2) huT (by rw [hV]; exact hVot)
        (fun j hj hjb k' hk' => (hook j hj hjb k' hk').1)
      unfold PV
      rw [ek, ek']
      refine ⟨?_, hPVk.2.1, hPVk.2.2⟩
      rcases hPVk.1 with h | ⟨hW, _⟩
      · exact Or.inl h
      · right
        refine ⟨hW, ?_⟩
        obtain ⟨m, _, _, _, hcase⟩ := upg_spec hu
        rcases hcase with rfl | ⟨hA, hki⟩
        · intro c hc _
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
    refine ⟨?_, hot1, vsmall_add_one hVot hVs⟩
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
      have := v_frame_xm1 hVot hWot hW1 (fun r hr _ hlt =>
        hX1 k _ hixe hu hvk (by simp) r hr hlt)
      rw [sf_ot hot1] at this
      exact Or.inl this

/-- **The drop lemma** (modulo the bump-type frames and the absorption at `x − 1`): at every column of
`M.take x`, `o` and `v` are `⊴` the values in `M` or weakly below them, and standard. -/
theorem drop_all_hard
    (hBump : ∀ i, i < x → (∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < x →
        PO ρ ρ' k ∧ PV M ρ ρ' k) → ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV M ρ ρ' i)
    (hX1 : ∀ i k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) :
    ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have key : ∀ N, ∀ i, i < x → (rk true i ≤ N → PO ρ ρ' i) ∧ (rk false i ≤ N → PV M ρ ρ' i) := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      have hPV : ∀ i, i < x → rk false i ≤ N → PV M ρ ρ' i := by
        intro i hi hN
        obtain ⟨_, _, hR⟩ := hRk' i (by omega)
        apply pv_of_hard hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hF hFO hHard hi
        · intro hCv h1 h2
          apply hBump i hi _ hCv h1 h2
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
      apply po_of_hard hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hF hFO hHard hi
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
