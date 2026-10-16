/-
**`deps_lhd_otW` から hHard を外した形、段の集合つき（`deps_lhd_otW_RU`、2026-10-12、t2）。**

`deps_lhd_otW_R`（V3DepRW）の RClaim を t0-exp の `RClaimU`（段 u を集合 U に限った RelRU）に替えたもの。
VSmallR（全段）は標準形で偽（M13）なので、要る段だけにする。子への依頼は U を変えないので、要る段は
D の道の上の祖先 k の v(k)（`PathLvS`、t = 0 の PathLv を DepS で一般にしたもの）と、枠自身の v(i) だけ。
仮定: VSmallR の代わりに道の段だけの `hVR`、書き換えの一致 hTA（T2TrigN）、種の RClaimU、種の v は変わらない（hSv）。
hVSN・hVNRN は要らない: 種でない列 c で v(c) が変わるなら c は数える子を持たず o(c) = ψ_{v(c)}(0)（vs_changed_bound、書き換えない）。
-/
import Ytosk.V3DepR
import Ytosk.V3DepOTW
import Ytosk.V3RelRU
import Ytosk.V3T0OT
import Ytosk.V3T0DepU
import Ytosk.V3T0TrigG
import Ytosk.V3VSF
import Ytosk.V3T0DepS

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The levels carried down the `D` path** (`DepS` form of `PathLv`): `u = v(k)` for a frame `(k, c)` whose old
child rewrites, and the levels of `k` when the frame `(k, c)` rewrites. -/
inductive PathLvS (M : Mat) (S : Bool → Nat → Prop) (bnd : Nat) (ρ : Valn) : Nat → T → Prop
  | top {k c : Nat} {Lc : List Nat} {s y : T} : k < bnd → c < bnd → CL M k = Lc ++ [c] →
      DepS M S true k → DepS M S true c → ρ.o c = psi s y z →
      (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v k) z z) (psi s y z) = true) →
      PathLvS M S bnd ρ c (ρ.v k)
  | step {k c : Nat} {Lc : List Nat} {s y u : T} : k < bnd → c < bnd → CL M k = Lc ++ [c] →
      DepS M S true k → DepS M S true c → ρ.o c = psi s y z →
      (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v k) z z) (psi s y z) = true) →
      PathLvS M S bnd ρ k u → PathLvS M S bnd ρ c u

/-- **`VSmallR` only at the levels of the path** (`DepS` form of `VSmallRP`). -/
def VSmallRS (M : Mat) (S : Bool → Nat → Prop) (bnd : Nat) (ρ : Valn) : Prop :=
  ∀ k c (Lc : List Nat) s y, k < bnd → c < bnd → CL M k = Lc ++ [c] → DepS M S true k → DepS M S true c →
    ρ.o c = psi s y z →
    (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v k) z z) (psi s y z) = true) →
    (split y (psi (succ s) z z)).1 ≠ z →
    ∀ u, (u = ρ.v k ∨ PathLvS M S bnd ρ k u) → ¬ lt (ρ.v k) u = true → ∀ g ∈ comps u s,
      g ≤ psi s z z ∨ g ≤ spArg (ρ.v k) z (sumN (Lc.map ρ.o)) ∨ ∃ d ∈ comps u (ρ.v k), g ≤ d

/-- **`N`-side hypothesis: the cut in the last summand** (`t = 0`: `hCutN`): at a `D` frame whose old child
rewrites with a zero low part, a state `P + κ` with `κ` a cut of the old last summand `ψ_a(x)` is below the new
tail `T′`. With `PH3cG` of `M` and the right-end change it gives the agreement of the rewrites (`trig_agreeG`). -/
def T2CutN (M : Mat) (S : Bool → Nat → Prop) (bnd : Nat) (ρ σ : Valn) : Prop :=
  ∀ i c (Lc : List Nat), i < bnd → c < bnd → CL M i = Lc ++ [c] → DepS M S true c →
    ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z →
    (split y (psi (succ s) z z)).2 = z →
    spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ≠ z →
    Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
    ∀ P a x T', y = app P (psi a x z) → y' = app P T' →
    ∀ κ ∈ cutsNSG s (psi a x z), spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = app P κ → κ < T'

theorem deps_lhd_otW_RU {M N : Mat} {S W : Bool → Nat → Prop} {bnd : Nat} {ρ σ : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hRM : Rk M rk)
    (hbM : bnd ≤ M.length) (hbN : bnd ≤ N.length)
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ)
    (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hSv : ∀ c, S true c → σ.v c = ρ.v c)
    (hVR : VSmallRS M S bnd ρ) (hPH : PH3cG M ρ) (hClB : RwClosed M ρ)
    (hoff : ∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i))
    (hOTout : ∀ b j, bnd ≤ j → j < N.length → isOT (valB σ b j) = true)
    (hWv : ∀ i, ¬ W false i)
    (hWo : ∀ i c, c ∈ children M i → Counted M i c → W true c → S true i)
    (hWb : ∀ i j c, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → j ∈ children M i → col M j = bump M i →
      c ∈ children M j → W true c → S false i)
    (hWot : ∀ i, i < bnd → W true i → isOT (σ.o i) = true)
    (hSeed : ∀ b i, S b i → i < bnd → DepS M S b i →
      (∀ b' i', rk b' i' < rk b i → DepS M S b' i' → i' < bnd → ¬ W b' i' →
        Lhd z (valB σ b' i') (valB ρ b' i') ∧ isOT (valB σ b' i') = true) →
      Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true)
    (hSeedR : ∀ i, S true i → i < bnd → DepS M S true i →
      ∀ U : T → Prop, (∀ u, U u → PathLvS M S bnd ρ i u) → RClaimU U ρ σ i)
    (hSeedRE : ∀ i, S true i → i < bnd → DepS M S true i → σ.v i = ρ.v i →
      ∀ X X', ρ.o i = psi (ρ.v i) X z → σ.o i = psi (ρ.v i) X' z → X' ≠ X → REr X X')
    (hDvNil : ∀ c, c < bnd → ¬ W true c → ¬ S true c → DepS M S false c → CL M c = [])
    (hDvNilN : ∀ c, c < bnd → ¬ W true c → DepS M S false c → CL N c = [])
    (hCLnil : ∀ c, c < bnd → ¬ W true c → CL M c = [] → CL N c = [])
    (hOc : ∀ i, i < bnd → ¬ S true i → ¬ W true i → DepS M S true i → ¬ DepS M S false i →
      ∃ Lc c, CL M i = Lc ++ [c] ∧ CL N i = Lc ++ [c] ∧ DepS M S true c ∧ c < bnd ∧
        ∀ d ∈ Lc, ¬ DepS M S true d ∧ d < bnd)
    (hVc : ∀ i, i < bnd → ¬ S false i → DepS M S false i →
      entry N 1 i = entry M 1 i ∧ entry N 2 i = entry M 2 i ∧ par N 1 i = par M 1 i ∧
      (∀ m, par M 1 i = some m → ¬ DepS M S false m) ∧ upg N i = upg M i ∧
      (∀ k, upg M i = some k → DepS M S false k → k < bnd) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children N i = Lb ++ [j] ∧
        col M j = bump M i ∧ col N j = bump N i ∧ children M j = Kb ++ [k] ∧
        children N j = Kb ++ [k] ∧ k < bnd ∧ entry N 1 k = entry M 1 k ∧
        (∀ d ∈ Kb, ¬ DepS M S true d ∧ d < bnd) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M S true e) ∧
        (∀ d ∈ Lb, bumpTerm N σ i d = bumpTerm M ρ i d)))
    (hupgK : ∀ i k, i < bnd → upg M i = some k → ∀ j ∈ children N k, col N j = bump N k →
      ∀ k' ∈ children N j, k' < bnd → j ∈ children M k ∧ col M j = bump M k ∧ k' ∈ children M j)
    (hAbs : AbsWN M N bnd ρ σ) :
    ∀ b i, DepS M S b i → i < bnd → ¬ W b i →
      (Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true) ∧ (b = true → ∀ U : T → Prop, (∀ u, U u → PathLvS M S bnd ρ i u) → RClaimU U ρ σ i) ∧
      (b = true → σ.v i = ρ.v i → ∀ X X', ρ.o i = psi (ρ.v i) X z → σ.o i = psi (ρ.v i) X' z → X' ≠ X → REr X X') := by
  -- standard values outside `D` (below `bnd`) and from `bnd` on
  have hOTo : ∀ j, j < N.length → (j < bnd → ¬ DepS M S true j) → isOT (σ.o j) = true := by
    intro j hj hnd
    rcases Nat.lt_or_ge j bnd with h | h
    · rw [(hoff j h).1 (hnd h)]; exact hG.ot_o j (by omega)
    · exact hOTout true j h hj
  have hOTv : ∀ j, j < N.length → (j < bnd → ¬ DepS M S false j) → isOT (σ.v j) = true := by
    intro j hj hnd
    rcases Nat.lt_or_ge j bnd with h | h
    · rw [(hoff j h).2 (hnd h)]; exact hG.ot_v j (by omega)
    · exact hOTout false j h hj
  have key : ∀ K, ∀ b i, rk b i ≤ K → DepS M S b i → i < bnd → ¬ W b i →
      (Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true) ∧ (b = true → ∀ U : T → Prop, (∀ u, U u → PathLvS M S bnd ρ i u) → RClaimU U ρ σ i) ∧
      (b = true → σ.v i = ρ.v i → ∀ X X', ρ.o i = psi (ρ.v i) X z → σ.o i = psi (ρ.v i) X' z → X' ≠ X → REr X X') := by
    intro K
    induction K using Nat.strongRecOn with
    | _ K ih =>
      intro b i hK hD hi hWi
      have hiM : i < M.length := by omega
      have hiN : i < N.length := by omega
      obtain ⟨hRv, hRc, hRr⟩ := hRM i hiM
      -- the standard value of a call of smaller rank
      have hotlt : ∀ b' j, rk b' j < rk b i → j < N.length → isOT (valB σ b' j) = true := by
        intro b' j hlt hj
        rcases Nat.lt_or_ge j bnd with h | h
        · by_cases hd : DepS M S b' j
          · by_cases hw : W b' j
            · cases b'
              · exact absurd hw (hWv j)
              · exact hWot j h hw
            · exact (ih _ (by omega) b' j (le_refl _) hd h hw).1.2
          · cases b'
            · exact hOTv j hj (fun _ => hd)
            · exact hOTo j hj (fun _ => hd)
        · exact hOTout b' j h hj
      by_cases hs : S b i
      · refine ⟨hSeed b i hs hi hD (fun b' i' hlt hD' hi' hW' => (ih _ (by omega) b' i' (le_refl _) hD' hi' hW').1),
          fun hb => by subst hb; exact hSeedR i hs hi hD, (fun hb => by subst hb; exact hSeedRE i hs hi hD)⟩
      cases b with
      | true =>
        show (Lhd z (σ.o i) (ρ.o i) ∧ isOT (σ.o i) = true) ∧ (true = true → ∀ U : T → Prop, (∀ u, U u → PathLvS M S bnd ρ i u) → RClaimU U ρ σ i) ∧ (true = true → σ.v i = ρ.v i → ∀ X X', ρ.o i = psi (ρ.v i) X z → σ.o i = psi (ρ.v i) X' z → X' ≠ X → REr X X')
        by_cases hv : DepS M S false i
        · -- through `v`
          obtain ⟨⟨hIH, hIHot⟩, -⟩ := ih _ (by omega) false i (le_refl _) hv hi (hWv i)
          change Lhd z (σ.v i) (ρ.v i) at hIH
          change isOT (σ.v i) = true at hIHot
          have hclM := hDvNil i hi hWi hs hv
          have ho : σ.o i = psi (σ.v i) z z :=
            o_of_no_counted hCN hiN hIHot (no_cnt_of_cl_nil (hDvNilN i hi hWi hv))
          have hoM0 := o_of_no_counted hC hiM (hG.ot_v i hiM) (no_cnt_of_cl_nil hclM)
          refine ⟨?_, fun _ _ _ => rclaim_zeroU ho, fun _ hvi X X' hX hX' hne => ?_⟩
          rotate_left
          · exfalso
            rw [hoM0] at hX; rw [ho, hvi] at hX'
            simp only [psi.injEq] at hX hX'
            exact hne (by rw [← hX.2.1, ← hX'.2.1])
          rw [ho, hoM0]
          refine ⟨lhd_of_lhdE_lt (lhdE_oq_v (Or.inr hIH)) (psi_lt_psi_z_iff.mpr (Or.inl hIH.1)), ?_⟩
          rw [isOT_psi_iff]
          exact ⟨hIHot, rfl, rfl, z_le _, fun g hg => by simp [comps] at hg⟩
        · obtain ⟨Lc, c, hclM, hclN, hdc, hcb, hLc⟩ := hOc i hi hs hWi hD hv
          have hv' := (hoff i hi).2 hv
          have hcCL : c ∈ CL M i := by rw [hclM]; simp
          have hcch := cl_mem_children hcCL
          have hcnt : Counted M i c := by
            unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
          have hrkc : rk true c < rk true i := hRc c hcch hcnt.1 hcnt.2
          have hWc : ¬ W true c := fun hw => hs (hWo i c hcch hcnt hw)
          obtain ⟨⟨hIH, hIHot⟩, hIHR', hIHRE'⟩ := ih _ (by omega) true c (le_refl _) hdc hcb hWc
          have hIHR := hIHR' rfl
          change Lhd z (σ.o c) (ρ.o c) at hIH
          change isOT (σ.o c) = true at hIHot
          have hcM : c < M.length := (mem_children hcch).2
          have hcN : c < N.length := by omega
          have hsame : ∀ d ∈ Lc, σ.o d = ρ.o d := fun d hd => (hoff d (hLc d hd).2).1 (hLc d hd).1
          have hcS : Single (σ.o c) := ⟨hIHot, o_psi_form hCN hcN⟩
          have hvM : ∀ s y, ρ.o c = psi s y z → s = ρ.v c := by
            intro s y h
            obtain ⟨y0, hy0⟩ := o_psi_sub hC hcM
            rw [h] at hy0; simp only [psi.injEq] at hy0
            rw [hy0.1, sf_ot (hG.ot_v c hcM)]
          have hchv : σ.v c ≠ ρ.v c → σ.o c = psi (σ.v c) z z := by
            intro hne
            have hdv : DepS M S false c := by by_contra hn'; exact hne ((hoff c hcb).2 hn')
            have hvot := (ih _ (by have := hRM c hcM; omega) false c (le_refl _) hdv hcb (hWv c)).1.2
            exact o_of_no_counted hCN hcN hvot
              (no_cnt_of_cl_nil (hDvNilN c hcb hWc hdv))
          have hsv : ∀ s y s' y', ρ.o c = psi s y z → σ.o c = psi s' y' z → σ.v c = ρ.v c → s' = s := by
            intro s y s' y' hsy hs'y' hvc
            obtain ⟨y0, hy0⟩ := o_psi_sub hCN hcN
            rw [hs'y'] at hy0; simp only [psi.injEq] at hy0
            rw [hy0.1, hvc, sf_ot (hG.ot_v c hcM), ← hvM s y hsy]
          have hss : ∀ s y s' y', ρ.o c = psi s y z → σ.o c = psi s' y' z → y' ≠ z → s' = s := by
            intro s y s' y' hsy hs'y' hy'
            apply hsv s y s' y' hsy hs'y'
            by_contra hvc
            have := hchv hvc
            rw [hs'y'] at this; simp only [psi.injEq] at this; exact hy' this.2.1
          -- the counted values of `N` at `i`: standard and non-increasing
          obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
          rw [hclM] at hsM hpM
          simp only [List.map_append, List.map_cons, List.map_nil] at hsM hpM
          have hsN : ∀ d ∈ CL N i, Single (σ.o d) := by
            intro d hd
            rw [hclN] at hd
            rcases List.mem_append.mp hd with hd | hd
            · rw [hsame d hd]; exact hsM _ (List.mem_append_left _ (List.mem_map_of_mem hd))
            · simp at hd; rw [hd]; exact hcS
          have hpN : ((CL N i).map σ.o).Pairwise (fun a b => b ≤ a) := by
            rw [hclN, List.map_append, List.map_singleton, List.map_congr_left hsame]
            have hp1 := List.pairwise_append.mp hpM
            refine List.pairwise_append.mpr ⟨hp1.1, by simp, fun t ht b hb => ?_⟩
            simp at hb; rw [hb]
            exact le_trans (le_of_lt hIH.1) (hp1.2.2 t ht _ (by simp))
          have hyarg : ∀ s, ρ.o c = psi s z z → ∃ s', σ.o c = psi s' z z := by
            intro s hs0
            have hclc : CL M c = [] := by
              by_contra hne
              have hlt := arg_lt_of_cl hC hG hcM hne
              rw [o_cl_eq hC hG hcM] at hs0
              simp only [psi.injEq] at hs0
              rw [hs0.2.1] at hlt; exact lt_irrefl' _ hlt
            have hvot : isOT (σ.v c) = true := by
              by_cases hdv : DepS M S false c
              · exact (ih _ (by have := hRM c hcM; omega) false c (le_refl _) hdv hcb (hWv c)).1.2
              · rw [(hoff c hcb).2 hdv]; exact hG.ot_v c hcM
            exact ⟨_, o_of_no_counted hCN hcN hvot (no_cnt_of_cl_nil (hCLnil c hcb hWc hclc))⟩
          have hLi := o_frame_lhdS hC hG hF hCN hiM hiN hv' hclN hclM hsame hsN hIH hyarg hss hpN
          obtain ⟨s, y, hsy⟩ := (single_o hC hG hcM).2
          obtain ⟨s', y', hs'y'⟩ := hcS.2
          have hformN := o_last_form hCN hiN (by rw [hv']; exact hG.ot_v i hiM) hclN hsN hpN hs'y'
          have hLm : Lc.map σ.o = Lc.map ρ.o := List.map_congr_left hsame
          have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht))
            (List.pairwise_append.mp hpM).1
          have hBc : ∀ q ∈ summands (spArg (ρ.v i) z (sumN (Lc.map ρ.o))), psi s y z ≤ q := by
            apply spArg_summands_ge ⟨s, y, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
            · rw [hLs.2]; intro q hq; rw [← hsy]
              exact (List.pairwise_append.mp hpM).2.2 q hq _ (by simp)
            · simp [summands]
          have hfr := hVS i hiM Lc c [] (by rw [hclM])
          have hsvc : s = ρ.v c := hvM s y hsy
          have hsub : ∀ g ∈ comps (ρ.v i) s, g ≤ psi s z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) := by
            rw [hsvc]; exact hfr
          have hs'v : s' = σ.v c := by
            obtain ⟨y0, hy0⟩ := o_psi_sub hCN hcN
            rw [hs'y'] at hy0; simp only [psi.injEq] at hy0
            have hvot : isOT (σ.v c) = true := by
              by_cases hdv : DepS M S false c
              · exact (ih _ (by have := hRM c hcM; omega) false c (le_refl _) hdv hcb (hWv c)).1.2
              · rw [(hoff c hcb).2 hdv]; exact hG.ot_v c hcM
            rw [hy0.1, sf_ot hvot]
          have hsub' : ∀ g ∈ comps (ρ.v i) s', g ≤ psi s' z z ∨
              g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) := by
            by_cases hvc : σ.v c = ρ.v c
            · rw [hs'v, hvc, ← hsvc]; exact hsub
            · rw [hs'v]
              by_cases hsc : S true c
              · exact absurd (hSv c hsc) hvc
              · -- a changed `v(c)` off the seeds: `c` has no counted child, `vs_changed_bound`
                have hdv : DepS M S false c := by by_contra hn'; exact hvc ((hoff c hcb).2 hn')
                obtain ⟨⟨hlv, hvot⟩, -⟩ := ih _ (by have := hRM c hcM; omega) false c (le_refl _) hdv hcb (hWv c)
                change Lhd z (σ.v c) (ρ.v c) at hlv
                change isOT (σ.v c) = true at hvot
                have hclc := hDvNil c hcb hWc hsc hdv
                have hoc := o_of_no_counted hC hcM (hG.ot_v c hcM) (no_cnt_of_cl_nil hclc)
                rw [hsy] at hoc; simp only [psi.injEq] at hoc
                have hy0 : y = z := hoc.2.1
                rw [← hsvc] at hlv
                have hot0 : isOT (psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s z z) z) = true := by
                  have hfm := o_last_form hC hiM (hG.ot_v i hiM) hclM (fun d hd => single_o hC hG
                    (mem_children (cl_mem_children hd)).2) (by
                      rw [hclM, List.map_append, List.map_singleton]; exact hpM) hsy
                  rw [hy0] at hfm; rw [← hfm]
                  exact hG.ot_o i hiM
                exact vs_changed_bound hvot hlv (by rw [hy0] at hBc; exact hBc) hsub hot0
          have hot : isOT (psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z) z) = true := by
            rw [← o_last_form hC hiM (hG.ot_v i hiM) hclM (fun d hd => single_o hC hG
              (mem_children (cl_mem_children hd)).2) (by
                rw [hclM, List.map_append, List.map_singleton]; exact hpM) hsy]
            exact hG.ot_o i hiM
          have hBot := hFO i hiM Lc c [] (by rw [hclM])
          -- a changed `v(c)`: off the seeds `c` has no counted child, so `y = 0` (and `y′ = 0`)
          have hvchg : σ.v c ≠ ρ.v c → y = z := by
            intro hne'
            have hsc : ¬ S true c := fun hsc => hne' (hSv c hsc)
            have hdv : DepS M S false c := by by_contra hn'; exact hne' ((hoff c hcb).2 hn')
            have hclc := hDvNil c hcb hWc hsc hdv
            have hoc := o_of_no_counted hC hcM (hG.ot_v c hcM) (no_cnt_of_cl_nil hclc)
            rw [hsy] at hoc; simp only [psi.injEq] at hoc
            exact hoc.2.1
          -- the right-end change at `c` and the agreement of the rewrites
          have hREc : σ.v c = ρ.v c → y' ≠ y → REr y y' := by
            intro hvc hne
            have hs' : s' = s := by rw [hs'v, hvc, ← hsvc]
            exact hIHRE' rfl hvc y y' (by rw [hsy, hsvc]) (by rw [hs'y', hs', hsvc]) hne
          have htos : σ.v c = ρ.v c → (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧
              lt (psi (ρ.v i) z z) (psi s y z) = true) →
              (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s y' z) = true) ∨
                ((split y (psi (succ s) z z)).2 = z ∧ ∃ P a' x T', y = app P (psi a' x z) ∧ y' = app P T' ∧
                  ∃ κ ∈ cutsNSG s (psi a' x z), spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = app P κ ∧ ¬ κ < T') := by
            intro hvc htr
            by_cases hyy : y' = y
            · rw [hyy]; exact Or.inl htr
            exact trig_or_shadow (hREc hvc hyy) (fun hB => hPH i hiM Lc c [] (by rw [hclM]) s y hsy hB htr) htr
          have hSi : isOT (psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s' y' z) z) = true := by
            apply node_ot_hard (by rw [← hsy]; exact hG.ot_o c hcM) (by rw [← hs'y']; exact hIHot)
              (Or.inr (by rw [← hs'y', ← hsy]; exact hIH)) hBc (fun hy' => hss s y s' y' hsy hs'y' hy')
              hsub hsub' _ hot hBot
            intro hss' has ht' ht hhi
            rw [hss'] at ht' hs'y'
            have hc'1 : isOT (psi s y' z) = true := by rw [← hs'y']; exact hIHot
            have hc01 : isOT (psi s y z) = true := by rw [← hsy]; exact hG.ot_o c hcM
            have hyy : y' ≤ y := by
              have h := hIH.1; rw [hs'y', hsy] at h
              rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
              · exact absurd h (lt_irrefl' _)
              · exact le_of_lt h
            have hot' : isOT (psi (ρ.v i) (H s y) z) = true := by
              have := hot; unfold step at this; rw [if_pos ht] at this; exact this
            have hhz : (split y (psi (succ s) z z)).1 ≠ z := by
              intro h; rw [h] at hhi; exact T.not_lt_z _ hhi
            refine hard_of_relRU (U := fun u => u = ρ.v i) hc'1 has (hG.ot_v i hiM) hot' (H_mono hc'1 hc01 hyy) ?_ rfl
            apply hIHR (fun u => u = ρ.v i)
              (fun u hu => by subst hu; exact PathLvS.top hi hcb hclM hD hdc hsy ht)
              s y y' (ρ.v i) hsy hs'y' (fun h => lt_irrefl' _ (lt_trans (show ρ.v i < s from has) h))
            intro u hu' hu g hg
            subst hu'
            rcases hVR i c Lc s y hi hcb hclM hD hdc hsy ht hhz _ (Or.inl rfl) hu g hg with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl (lt_of_le_of_lt h (lt_of_lt_of_le ht'.1 (le_H hc'1))))
            · exact Or.inr (Or.inr h)
          refine ⟨⟨hLi, by rw [hformN, hLm, hv']; exact hSi⟩, fun _ => ?_, fun _ => ?_⟩
          -- the claim at `i`
          intro U hU p yy yy' q hyy hyy' hqp hhyp
          have hoM : ρ.o i = psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z) z := by
            rw [o_last_form hC hiM (hG.ot_v i hiM) hclM (fun d hd => single_o hC hG
              (mem_children (cl_mem_children hd)).2) (by
                rw [hclM, List.map_append, List.map_singleton]; exact hpM) hsy]
          have hoN : σ.o i = psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s' y' z) z := by
            rw [hformN, hLm, hv']
          have hLi' := hLi
          rw [hoM] at hyy; rw [hoN] at hyy'
          rw [hoN, hoM] at hLi'
          simp only [psi.injEq] at hyy hyy'
          obtain ⟨rfl, rfl, -⟩ := hyy
          obtain ⟨-, rfl, -⟩ := hyy'
          have hc0 : isOT (psi s y z) = true := by rw [← hsy]; exact hG.ot_o c hcM
          have hc'0 : isOT (psi s' y' z) = true := by rw [← hs'y']; exact hIHot
          have hlc : Lhd z (psi s' y' z) (psi s y z) := by rw [← hs'y', ← hsy]; exact hIH
          exact relR_frameU hc0 hc'0 hBc (Or.inl ⟨Or.inr hlc, fun hy' => hss s y s' y' hsy hs'y' hy'⟩) hSi hot
            (Or.inr hLi')
            (fun htr hss0 q' hq' hyp' => by
              subst hss0
              exact hIHR U (fun u hu => PathLvS.step hi hcb hclM hD hdc hsy htr (hU u hu)) s' y y' q' hsy hs'y' hq' hyp')
            (fun htr hhz u hu => hVR i c Lc s y hi hcb hclM hD hdc hsy htr hhz u (Or.inr (hU u hu)))
            (fun ht hne _ => by
              -- a changed `v(c)`: `y = 0`, the old child does not rewrite
              exfalso
              have hvs : s = ρ.v c := hvM s y hsy
              have hne' : σ.v c ≠ ρ.v c := by rw [← hs'v, ← hvs]; exact hne
              have := ht.1; rw [hvchg hne'] at this; exact T.not_lt_z _ this)
            (fun ht hnt _ => by
              by_cases hvc : σ.v c = ρ.v c
              · have es : s' = s := by rw [hs'v, hvc, ← hsvc]
                rw [es] at hnt ⊢
                rcases htos hvc ht with hnew | ⟨hlo, P1, a1, x1, T1, e1, -, κ1, hκ1, hBk1, -⟩
                · exact absurd hnew hnt
                · have hyy : y' ≠ y := fun e => hnt (by rw [e]; exact ht)
                  obtain ⟨P0, a0, x0, T0, -, e2, hT0⟩ := hREc hvc hyy
                  have hyz' : y' ≠ z := by rw [e2]; exact app_ne_z_right hT0
                  have hyz : y ≠ z := fun e => by rw [e] at ht; exact T.not_lt_z _ ht.1
                  have hhz : (split y (psi (succ s) z z)).1 ≠ z := by
                    intro h0
                    have e := split_app (psi (succ s) z z) y
                    rw [h0, hlo] at e; simp [app] at e; exact hyz e.symm
                  have hl' : Lhd z (psi s y' z) (psi s y z) := by have h := hlc; rw [es] at h; exact h
                  exact shadow_hSh hBc ht hnt hyz' hl' (hClB i hiM Lc c [] (by rw [hclM]) s y hsy ht (by
                    have e := split_app (psi (succ s) z z) y
                    rw [hlo, app_z_right] at e
                    rw [e]; exact ht.1) (by
                    rintro ⟨R1, hR1⟩
                    have e := split_app (psi (succ s) z z) y
                    rw [hlo, app_z_right] at e
                    rw [e, e1] at hR1
                    rw [hBk1, app_assoc] at hR1
                    have h2 := app_left_cancel0 hR1
                    have hκt : κ1 = psi a1 x1 z := by
                      rcases mem_cutsNSG_psi.mp hκ1 with ⟨u, _, rfl⟩ | ⟨u, _, rfl⟩ | ⟨u, hu, _⟩
                      · simp only [app, psi.injEq] at h2; rw [h2.1, h2.2.1]
                      · simp only [app, psi.injEq] at h2; rw [h2.2.1]
                      · simp [cutsNSG] at hu
                    have hBy : spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = y := by rw [hBk1, hκt, e1]
                    have := ht.1; rw [hBy] at this; exact lt_irrefl' _ this))
                    (fun u hu hau g hg => hVR i c Lc s y hi hcb hclM hD hdc hsy ht hhz u
                      (Or.inr (hU u hu)) hau g hg)
              · exfalso; have := ht.1; rw [hvchg hvc] at this; exact T.not_lt_z _ this)
            hqp hhyp
          -- the right-end change at `i`
          intro _ X X' hX hX' hne
          have hoM : ρ.o i = psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z) z := by
            rw [o_last_form hC hiM (hG.ot_v i hiM) hclM (fun d hd => single_o hC hG
              (mem_children (cl_mem_children hd)).2) (by
                rw [hclM, List.map_append, List.map_singleton]; exact hpM) hsy]
          have hoN : σ.o i = psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s' y' z) z := by
            rw [hformN, hLm, hv']
          rw [hoM] at hX; rw [hoN] at hX'
          simp only [psi.injEq] at hX hX'
          rw [← hX.2.1, ← hX'.2.1] at hne ⊢
          have hc0 : isOT (psi s y z) = true := by rw [← hsy]; exact hG.ot_o c hcM
          have hc'0 : isOT (psi s' y' z) = true := by rw [← hs'y']; exact hIHot
          have hlc : Lhd z (psi s' y' z) (psi s y z) := by rw [← hs'y', ← hsy]; exact hIH
          by_cases hvc : σ.v c = ρ.v c
          · have es : s' = s := by rw [hs'v, hvc, ← hsvc]
            rw [es] at hne hc'0 hlc ⊢
            have hyy' : y' ≠ y := fun h => hne (by rw [h])
            have hlt : y' < y := by
              rcases psi_lt_psi_z_iff.mp hlc.1 with h | ⟨_, h⟩
              · exact absurd h (lt_irrefl' _)
              · exact h
            by_cases hold : lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true
            · rcases htos hvc hold with hnew | ⟨hlo, P, a', x, T', e1, e2, κ, hκ, hBk, hnk⟩
              · exact re_step hc0 hc'0 hBc hlt (hREc hvc hyy') (fun _ => hnew)
              · by_cases hnew : lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧
                    lt (psi (ρ.v i) z z) (psi s y' z) = true
                · exact re_step hc0 hc'0 hBc hlt (hREc hvc hyy') (fun _ => hnew)
                · exact re_shadow hc0 hBc hlt hold hnew hlo e1 hBk
            · exact re_step hc0 hc'0 hBc hlt (hREc hvc hyy') (fun h => absurd h hold)
          · have hy0 := hvchg hvc
            have hy'0 : y' = z := by
              have h := hchv hvc; rw [hs'y'] at h; simp only [psi.injEq] at h; exact h.2.1
            have hdv : DepS M S false c := by by_contra hn'; exact hvc ((hoff c hcb).2 hn')
            have hlv : Lhd z (σ.v c) (ρ.v c) :=
              (ih _ (by have := hRM c hcM; omega) false c (le_refl _) hdv hcb (hWv c)).1.1
            rw [hy0] at hBc ⊢; rw [hy'0]
            rw [hs'v, hsvc]
            rw [hsvc] at hBc
            exact re_leaf hlv.1 hBc
      | false =>
        show (Lhd z (σ.v i) (ρ.v i) ∧ isOT (σ.v i) = true) ∧ (false = true → ∀ U : T → Prop, (∀ u, U u → PathLvS M S bnd ρ i u) → RClaimU U ρ σ i) ∧ (false = true → σ.v i = ρ.v i → ∀ X X', ρ.o i = psi (ρ.v i) X z → σ.o i = psi (ρ.v i) X' z → X' ≠ X → REr X X')
        refine ⟨?_, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
        obtain ⟨he1, he2, hpar, hpnd, hupg, hupgb, hbsh⟩ := hVc i hi hs hD
        have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
          cases hpp : par M 1 i with
          | none => rfl
          | some m => exact hG.ot_v m (by have := par_lt M 1 i m hpp; omega)
        have hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i) := by
          rw [hpar]
          cases hpp : par M 1 i with
          | none => rfl
          | some m =>
            have := par_lt M 1 i m hpp
            exact (hoff m (by omega)).2 (hpnd m hpp)
        have hVot' : isOT (vOpt σ (par N 1 i)) = true := by rw [hV]; exact hVot
        cases hD with
        | seed h => exact absurd h hs
        | vpar h1 hpm hdm => exact absurd hdm (hpnd _ hpm)
        | @vupg _ k h1 h2 hu hdk =>
          have hkb := hupgb k hu hdk
          have hkM : k < M.length := by omega
          obtain ⟨⟨hIH, hIHot⟩, -⟩ := ih _ (by have := (hRr h1).2.1 h2 k hu; omega) false k (le_refl _) hdk hkb (hWv k)
          change Lhd z (σ.v k) (ρ.v k) at hIH
          change isOT (σ.v k) = true at hIHot
          have ek : ρ.v i = ρ.v k :=
            v_upg_eq hC hiM h1 h2 hu hVot (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
          have ek' : σ.v i = σ.v k := by
            apply v_upg_eq hCN hiN (by rw [he1]; exact h1) (by rw [he2]; exact h2) (by rw [hupg]; exact hu)
              hVot'
            intro j hj hjb k' hk'
            have hk'N := (mem_children hk').2
            rcases Nat.lt_or_ge k' bnd with hk'b | hk'b
            · obtain ⟨hjM, hjbM, hk'M⟩ := hupgK i k hi hu j hj hjb k' hk' hk'b
              obtain ⟨m, hm1, hm2, hcol, _⟩ := upg_spec hu
              have hk1 : entry M 1 k ≠ 0 := by
                have : entry M 1 k = (col M k).2.1 := rfl
                rw [this, hcol]; exact h1
              have hk2 : entry M 2 k ≠ 0 := by
                have : entry M 2 k = (col M k).2.2 := rfl
                rw [this, hcol]; simp
              have hlt1 := ((hRM k hkM).2.2 hk1).2.2 hk2 j hjM hjbM k' hk'M
              have hlt2 := (hRr h1).2.1 h2 k hu
              exact hotlt true k' (by omega) hk'N
            · exact hOTout true k' hk'b hk'N
          rw [ek, ek']; exact ⟨hIH, hIHot⟩
        | @vbump _ j0 k0 h1 h2 hj0 hjb0 hk0 hdk0 =>
          obtain ⟨Lb, Kb, j, k, hch, hchN, hjb, hjbN, hchj, hchjN, hkb, he1k, hKnd, hLnd, hbL⟩ := hbsh h2
          have hjj : j0 = j := by
            rw [hch] at hj0
            rcases List.mem_append.mp hj0 with h | h
            · exact absurd hdk0 (hLnd j0 h k0 hk0)
            · exact List.mem_singleton.mp h
          subst hjj
          have hkk : k0 = k := by
            rw [hchj] at hk0
            rcases List.mem_append.mp hk0 with h | h
            · exact absurd hdk0 (hKnd k0 h).1
            · exact List.mem_singleton.mp h
          subst hkk
          have hkM : k0 < M.length := (mem_children (show k0 ∈ children M j0 by rw [hchj]; simp)).2
          have hkN : k0 < N.length := by omega
          have hj : j0 ∈ children M i := by rw [hch]; simp
          have hk : k0 ∈ children M j0 := by rw [hchj]; simp
          obtain ⟨⟨hIH, hIHot⟩, -⟩ :=
            ih _ (by have := (hRr h1).2.2 h2 j0 hj hjb k0 hk; omega) true k0 (le_refl _) hdk0 hkb
              (fun hw => hs (hWb i j0 k0 h1 h2 hj hjb hk hw))
          change Lhd z (σ.o k0) (ρ.o k0) at hIH
          change isOT (σ.o k0) = true at hIHot
          have hKv : Kb.map σ.o = Kb.map ρ.o :=
            List.map_congr_left (fun d hd => (hoff d (hKnd d hd).2).1 (hKnd d hd).1)
          have hbjM : bumpTerm M ρ i j0 = omega (sumN (Kb.map ρ.o ++ [ρ.o k0])) := by
            unfold bumpTerm; rw [if_pos hjb, hchj, List.map_append, List.map_singleton]
          have hbjN : bumpTerm N σ i j0 = omega (sumN (Kb.map ρ.o ++ [σ.o k0])) := by
            unfold bumpTerm; rw [if_pos hjbN, hchjN, List.map_append, List.map_singleton, hKv]
          have hdec := hKD i h1 h2 j0 hj hjb
          rw [hchj, List.map_append, List.map_singleton] at hdec
          have hsK : ∀ u ∈ Kb.map ρ.o, Single u := fun u hu => by
            obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
            exact single_o hC hG (by have := (hKnd d hd).2; omega)
          have hk0S : Single (σ.o k0) := ⟨hIHot, o_psi_form hCN hkN⟩
          have hform : (∃ s y y', ρ.o k0 = psi s y z ∧ σ.o k0 = psi s y' z) ∨
              (∃ w' w Y, σ.o k0 = psi w' z z ∧ ρ.o k0 = psi w Y z ∧ LhdE w' w ∧ one ≤ w') := by
            obtain ⟨y1, hy1⟩ := o_psi_sub hC hkM
            rw [sf_ot (hG.ot_v k0 hkM)] at hy1
            by_cases hvk : σ.v k0 = ρ.v k0
            · obtain ⟨y0, hy0⟩ := o_psi_sub hCN hkN
              rw [hvk, sf_ot (hG.ot_v k0 hkM)] at hy0
              exact Or.inl ⟨_, _, _, hy1, hy0⟩
            · have hdv : DepS M S false k0 := by by_contra hn'; exact hvk ((hoff k0 hkb).2 hn')
              have hrk0 : rk false k0 < rk false i := by
                have := (hRM k0 hkM).1; have := (hRr h1).2.2 h2 j0 hj hjb k0 hk; omega
              obtain ⟨⟨hvIH, hvIHot⟩, -⟩ := ih _ (by omega) false k0 (le_refl _) hdv hkb (hWv k0)
              change Lhd z (σ.v k0) (ρ.v k0) at hvIH
              change isOT (σ.v k0) = true at hvIHot
              have hWk0 : ¬ W true k0 := fun hw => hs (hWb i j0 k0 h1 h2 hj hjb hk hw)
              have ho0 : σ.o k0 = psi (σ.v k0) z z := o_of_no_counted hCN hkN hvIHot
                (no_cnt_of_cl_nil (hDvNilN k0 hkb hWk0 hdv))
              have he1k' : entry M 1 k0 ≠ 0 := by
                intro he; apply hvk
                rw [v_z_of_e1 hC hkM he, v_z_of_e1 hCN hkN (by rw [he1k]; exact he)]
              have hv0 : σ.v k0 ≠ z := v_ne_z_of_e1 hCN hkN (by rw [he1k]; exact he1k')
              exact Or.inr ⟨_, _, _, ho0, hy1, Or.inr hvIH, one_le_of_ne_z hv0⟩
          obtain ⟨hS, hlt, hG'ot⟩ := g_brel hsK hdec (single_o hC hG hkM) hk0S hIH hform
          have hGot : isOT (sumN (Kb.map ρ.o ++ [ρ.o k0])) = true := isOT_sumN _ (fun u hu => by
            rcases List.mem_append.mp hu with h | h
            · exact (hsK u h).1
            · simp at h; rw [h]; exact hG.ot_o k0 hkM)
          refine ⟨v_bump_lhdW hC hG hCN hiM hiN h1 h2 he1 he2 hV hch hchN hbL hbjM hbjN hGot hG'ot hS hlt
            hTD (hAbs i hi h1 h2), ?_⟩
          -- the new `v` is `V + ω^Y` with `V`, `Y` standard
          have hmapN : (children N i).map (bumpTerm N σ i) = Lb.map (bumpTerm M ρ i) ++ [omega
              (sumN (Kb.map ρ.o ++ [σ.o k0]))] := by
            rw [hchN, List.map_append, List.map_singleton, hbjN, List.map_congr_left hbL]
          have hY : isOT (sumN (one :: (children N i).map (bumpTerm N σ i))) = true := by
            apply isOT_sumN
            intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · rfl
            · rw [hmapN] at ht
              rcases List.mem_append.mp ht with ht | ht
              · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i d
              · simp at ht; rw [ht]; exact isOT_omega hG'ot
          have hot : isOT (add (vOpt σ (par N 1 i))
              (omega (sumN (one :: (children N i).map (bumpTerm N σ i))))) = true :=
            isOT_add hVot' (isOT_omega hY)
          change isOT (σ.v i) = true
          rw [(hCN i hiN).2]; unfold vRhs
          rw [if_neg (by rw [he1]; exact h1), if_neg (by rw [he2]; exact h2), sf_ot hot]
          exact hot
  exact fun b i hD hi hW => key _ b i (le_refl _) hD hi hW


/-! ### 道の段を D に依らずにとる形（M だけの不変条件 `VSmallRA`）

`PathLvA`: すべての枠 (k, c)（c は k の最後の数える子、古い子が書き換え）で段を運ぶ。D の道の段 `PathLvS` を含む。
`VSmallRA` は t = 0・t = 2 で共通の M の不変条件になる。 -/

/-- **The levels carried down rewriting frames**, for all frames (not only `D`). -/
inductive PathLvA (M : Mat) (ρ : Valn) : Nat → T → Prop
  | top {k c : Nat} {Lc : List Nat} {s y : T} : CL M k = Lc ++ [c] → ρ.o c = psi s y z →
      (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v k) z z) (psi s y z) = true) → PathLvA M ρ c (ρ.v k)
  | step {k c : Nat} {Lc : List Nat} {s y u : T} : CL M k = Lc ++ [c] → ρ.o c = psi s y z →
      (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v k) z z) (psi s y z) = true) → PathLvA M ρ k u → PathLvA M ρ c u

theorem PathLvS.toA {M : Mat} {S : Bool → Nat → Prop} {bnd : Nat} {ρ : Valn} {i : Nat} {u : T}
    (h : PathLvS M S bnd ρ i u) : PathLvA M ρ i u := by
  induction h with
  | top _ _ hcl _ _ hsy ht => exact PathLvA.top hcl hsy ht
  | step _ _ hcl _ _ hsy ht _ ih => exact PathLvA.step hcl hsy ht ih

/-- **`VSmallR` at the levels of the rewriting frames above** (all frames of `M`). -/
def VSmallRA (M : Mat) (ρ : Valn) : Prop :=
  ∀ k c (Lc : List Nat) s y, CL M k = Lc ++ [c] → ρ.o c = psi s y z →
    (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v k) z z) (psi s y z) = true) →
    (split y (psi (succ s) z z)).1 ≠ z →
    ∀ u, (u = ρ.v k ∨ PathLvA M ρ k u) → ¬ lt (ρ.v k) u = true → ∀ g ∈ comps u s,
      g ≤ psi s z z ∨ g ≤ spArg (ρ.v k) z (sumN (Lc.map ρ.o)) ∨ ∃ d ∈ comps u (ρ.v k), g ≤ d

theorem VSmallRA.toS {M : Mat} {ρ : Valn} (h : VSmallRA M ρ) (S : Bool → Nat → Prop) (bnd : Nat) :
    VSmallRS M S bnd ρ :=
  fun k c Lc s y _ _ hcl _ _ hsy ht hhz u hu => h k c Lc s y hcl hsy ht hhz u (hu.imp id PathLvS.toA)

/-- `T2CutN` at all frames of `M` (no `D` condition). -/
def T2CutA (M N : Mat) (bnd : Nat) (ρ σ : Valn) : Prop :=
  ∀ i c (Lc : List Nat), i < bnd → c < bnd → CL M i = Lc ++ [c] →
    ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z →
    (split y (psi (succ s) z z)).2 = z →
    spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ≠ z →
    Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
    ∀ P a x T', y = app P (psi a x z) → y' = app P T' →
    ∀ κ ∈ cutsNSG s (psi a x z), spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = app P κ → κ < T'

theorem T2CutA.toN {M N : Mat} {bnd : Nat} {ρ σ : Valn} (h : T2CutA M N bnd ρ σ) (S : Bool → Nat → Prop) :
    T2CutN M S bnd ρ σ :=
  fun i c Lc hi hc hcl _ => h i c Lc hi hc hcl

/-- **The replacement of `T2Hard` and `T2VSN`** (one seed `p`, residual part): `VSmallRA` and `PH3cG` of `M`,
the cut condition `T2CutA` (with `PH3cG` and the right-end change it gives the agreement of the rewrites),
and `RClaimU` and the right-end change at the seed. (`T2VSN` and `VSmallNewR` are not needed: off the seeds
a changed `v(c)` has no counted child, and `v` of the seed does not change.) -/
def T2HardB (M N : Mat) (bnd p : Nat) (ρ σ : Valn) : Prop :=
  VSmallRA M ρ ∧ PH3cG M ρ ∧ RwClosed M ρ ∧
    (∀ U : T → Prop, (∀ u, U u → PathLvA M ρ p u) → RClaimU U ρ σ p) ∧
    (∀ X X', ρ.o p = psi (ρ.v p) X z → σ.o p = psi (ρ.v p) X' z → X' ≠ X → REr X X')

/-- `T2HardB` and an unchanged `v` of the seed. -/
def T2HardA (M N : Mat) (bnd p : Nat) (ρ σ : Valn) : Prop :=
  T2HardB M N bnd p ρ σ ∧ σ.v p = ρ.v p

theorem T2HardA.of_B {M N : Mat} {bnd p : Nat} {ρ σ : Valn} (h : T2HardB M N bnd p ρ σ) (hv : σ.v p = ρ.v p) :
    T2HardA M N bnd p ρ σ := ⟨h, hv⟩

theorem T2HardA.seed {M N : Mat} {bnd p : Nat} {ρ σ : Valn} (h : T2HardA M N bnd p ρ σ) (S : Bool → Nat → Prop)
    (hSp : ∀ i, S true i → i = p) :
    ∀ i, S true i → i < bnd → DepS M S true i →
      ∀ U : T → Prop, (∀ u, U u → PathLvS M S bnd ρ i u) → RClaimU U ρ σ i := by
  intro i hs _ _ U hU
  have := hSp i hs; subst this
  exact h.1.2.2.2.1 U (fun u hu => (hU u hu).toA)

theorem T2HardA.sv {M N : Mat} {bnd p : Nat} {ρ σ : Valn} (h : T2HardA M N bnd p ρ σ) (S : Bool → Nat → Prop)
    (hSp : ∀ i, S true i → i = p) : ∀ c, S true c → σ.v c = ρ.v c := by
  intro c hs
  have := hSp c hs; subst this
  exact h.2

theorem T2HardA.re {M N : Mat} {bnd p : Nat} {ρ σ : Valn} (h : T2HardA M N bnd p ρ σ) (S : Bool → Nat → Prop)
    (hSp : ∀ i, S true i → i = p) :
    ∀ i, S true i → i < bnd → DepS M S true i → σ.v i = ρ.v i →
      ∀ X X', ρ.o i = psi (ρ.v i) X z → σ.o i = psi (ρ.v i) X' z → X' ≠ X → REr X X' := by
  intro i hs _ _ _
  have := hSp i hs; subst this
  exact h.1.2.2.2.2

end Ytosk
