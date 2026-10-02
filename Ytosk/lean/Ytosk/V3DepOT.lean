/-
**変わる呼び出しの標準形: ◁ と isOT を同時に伝える（`deps_lhd_ot`）。**

`deps_lhd_gen`（V3DepLhd）は N の Good3 を仮定して ◁ を出す。ここでは N の Good3 を仮定せず、
D の呼び出しの値の ◁ と標準形を M の順位についての帰納法で同時に出す。
- 種の呼び出しは仮定（◁ と標準形）。
- v を通る o: ψ_{v′}(0) は v′ が標準形なら標準形。
- 最後の数える子を通る o: 枠 1 段の標準形は `node_ot_hard`（V3DropStrong）。仮定は M の FrameOT・VSmallF、
  N 側の 2 つ: 添字が変わった新しい子の VSmallNew 型（`hVSN`）と、難しい場合（添字同じ・a < s・新旧とも書き換え・
  高い部分が違う）の成分の上界 comps_a y′ ≤ H(s, y′)（`hHard`）。実測: t = 2 の N の D の枠 17.9 万件のうち
  難しい場合 2.2 万件で上界は例外 0（C′ 8000 行列、n = 2, 3）。
- 上げの v: 行き先の v と同じ。のりしろの v: V + ω^Y で V・Y が標準形。
- bnd 以後（t = 2 では写し）の値の標準形は仮定 `hOTout`。
-/
import Ytosk.V3DepLhd
import Ytosk.V3DropMain
import Ytosk.V3DropStrong

namespace Ytosk

open T

/-- `o_frame_lhdT` with the standard values of the counted children of `i` in `N` given directly. -/
theorem o_frame_lhdS {M N : Mat} {ρ σ : Valn} {i c : Nat} {Lc : List Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hF : FrameClosed M ρ) (hCN : Cons N σ)
    (hiM : i < M.length) (hiN : i < N.length) (hv : σ.v i = ρ.v i)
    (hclN : CL N i = Lc ++ [c]) (hclM : CL M i = Lc ++ [c])
    (hsame : ∀ d ∈ Lc, σ.o d = ρ.o d)
    (hsN : ∀ d ∈ CL N i, Single (σ.o d))
    (hl : Lhd z (σ.o c) (ρ.o c))
    (hy : ∀ s, ρ.o c = psi s z z → ∃ s', σ.o c = psi s' z z)
    (hss : ∀ s y s' y', ρ.o c = psi s y z → σ.o c = psi s' y' z → y' ≠ z → s' = s)
    (hpN0 : ((CL N i).map σ.o).Pairwise (fun a b => b ≤ a)) :
    Lhd z (σ.o i) (ρ.o i) := by
  have hcM : c < M.length := (mem_children (cl_mem_children (show c ∈ CL M i by rw [hclM]; simp))).2
  have hcs' : Single (σ.o c) := hsN c (by rw [hclN]; simp)
  have hE := o_frame_evalG hC hG hF hCN hiN hiM hv hclN (Tl := []) (by rw [hclM, List.append_nil]) hsame
    hcs' (Or.inl (Or.inr hl)) (fun s y s' y' h h' hy' => hss s y s' y' h h' hy')
  apply lhd_of_lhdE_lt hE
  have hvot : isOT (ρ.v i) = true := hG.ot_v i hiM
  set a := ρ.v i with ha
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
  rw [hclM] at hsM hpM
  have hpM' := hpM
  simp only [List.map_append, List.map_cons, List.map_nil] at hpM'
  obtain ⟨s, y, hsy⟩ := (single_o hC hG hcM).2
  obtain ⟨s', y', hs'y'⟩ := hcs'.2
  have hformM := o_last_form hC hiM hvot hclM (fun d hd => single_o hC hG
    (mem_children (cl_mem_children hd)).2) (by rw [hclM]; exact hpM) hsy
  have hformN := o_last_form hCN hiN (by rw [hv]; exact hvot) hclN hsN hpN0 hs'y'
  have hLm : Lc.map σ.o = Lc.map ρ.o := List.map_congr_left hsame
  rw [hLm, hv] at hformN
  rw [hformN, hformM]
  apply psi_lt_psi_z_iff.mpr; right; refine ⟨rfl, ?_⟩
  have hsL : ∀ t ∈ Lc.map ρ.o, Single t := fun t ht => hsM t (by
    simp only [List.map_append]; exact List.mem_append_left _ ht)
  have hp1 := List.pairwise_append.mp hpM'
  have hLs := sumN_dec (Lc.map ρ.o) hsL hp1.1
  have hc : isOT (psi s y z) = true := by rw [← hsy]; exact hG.ot_o c hcM
  have hc' : isOT (psi s' y' z) = true := by rw [← hs'y']; exact hcs'.1
  apply step_lt hc hc'
  · left; rw [← hsy, ← hs'y']; exact hl
  · intro q hq
    apply spArg_summands_ge ⟨s, y, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq; rw [← hsy]; exact hp1.2.2 q hq _ (by simp)
    · simp [summands]
    · exact hq
  · intro ht' hlt
    have := hss s y s' y' hsy hs'y' (ne_z_of_lt ht'.1)
    rw [this] at hlt; exact absurd hlt (lt_irrefl' _)
  · intro hyz
    rw [hyz] at hsy
    obtain ⟨s'', h''⟩ := hy s hsy
    rw [hs'y'] at h''; simp only [psi.injEq] at h''; exact h''.2.1

/-- **`◁` and standard form through `DepS M S`**, without the evaluation `Good3` of `N`: the changed calls
below `bnd` drop by `◁` and are standard. The standard form of a frame with a lowered last child is the
lemma `node_ot_hard` with `FrameOT`, `VSmallF` of `M` and two hypotheses on `N`: the subscript bound of a
changed last child (`hVSN`) and the bound of the hard case (`hHard`); the values of `N` from `bnd` on are
standard by hypothesis (`hOTout`). -/
theorem deps_lhd_ot {M N : Mat} {S : Bool → Nat → Prop} {bnd : Nat} {ρ σ : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hRM : Rk M rk)
    (hbM : bnd ≤ M.length) (hbN : bnd ≤ N.length)
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ)
    (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hVSN : ∀ i (Lc : List Nat) c, i < bnd → CL N i = Lc ++ [c] → σ.v c ≠ ρ.v c →
      ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)))
    (hHard : ∀ i (Lc : List Nat) c s y y', i < bnd → CL N i = Lc ++ [c] → ρ.o c = psi s y z →
      σ.o c = psi s y' z → lt (ρ.v i) s = true →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s y' z) = true) →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
      (split y' (psi (succ s) z z)).1 < (split y (psi (succ s) z z)).1 →
      ∀ g ∈ comps (ρ.v i) y', g ≤ H s y')
    (hoff : ∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i))
    (hOTout : ∀ b j, bnd ≤ j → j < N.length → isOT (valB σ b j) = true)
    (hSeed : ∀ b i, S b i → i < bnd → DepS M S b i →
      (∀ b' i', rk b' i' < rk b i → DepS M S b' i' → i' < bnd →
        Lhd z (valB σ b' i') (valB ρ b' i') ∧ isOT (valB σ b' i') = true) →
      Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true)
    (hDvNil : ∀ c, c < bnd → DepS M S false c → CL M c = [])
    (hCLnil : ∀ c, c < bnd → CL M c = [] → CL N c = [])
    (hOc : ∀ i, i < bnd → ¬ S true i → DepS M S true i → ¬ DepS M S false i →
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
    (hAbs : ∀ i, i < bnd → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i)) :
    ∀ b i, DepS M S b i → i < bnd → Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true := by
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
  have key : ∀ K, ∀ b i, rk b i ≤ K → DepS M S b i → i < bnd →
      Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true := by
    intro K
    induction K using Nat.strongRecOn with
    | _ K ih =>
      intro b i hK hD hi
      have hiM : i < M.length := by omega
      have hiN : i < N.length := by omega
      obtain ⟨hRv, hRc, hRr⟩ := hRM i hiM
      -- the standard value of a call of smaller rank
      have hotlt : ∀ b' j, rk b' j < rk b i → j < N.length → isOT (valB σ b' j) = true := by
        intro b' j hlt hj
        rcases Nat.lt_or_ge j bnd with h | h
        · by_cases hd : DepS M S b' j
          · exact (ih _ (by omega) b' j (le_refl _) hd h).2
          · cases b'
            · exact hOTv j hj (fun _ => hd)
            · exact hOTo j hj (fun _ => hd)
        · exact hOTout b' j h hj
      by_cases hs : S b i
      · exact hSeed b i hs hi hD (fun b' i' hlt hD' hi' => ih _ (by omega) b' i' (le_refl _) hD' hi')
      cases b with
      | true =>
        show Lhd z (σ.o i) (ρ.o i) ∧ isOT (σ.o i) = true
        by_cases hv : DepS M S false i
        · -- through `v`
          obtain ⟨hIH, hIHot⟩ := ih _ (by omega) false i (le_refl _) hv hi
          change Lhd z (σ.v i) (ρ.v i) at hIH
          change isOT (σ.v i) = true at hIHot
          have hclM := hDvNil i hi hv
          have ho : σ.o i = psi (σ.v i) z z :=
            o_of_no_counted hCN hiN hIHot (no_cnt_of_cl_nil (hCLnil i hi hclM))
          rw [ho, o_of_no_counted hC hiM (hG.ot_v i hiM) (no_cnt_of_cl_nil hclM)]
          refine ⟨lhd_of_lhdE_lt (lhdE_oq_v (Or.inr hIH)) (psi_lt_psi_z_iff.mpr (Or.inl hIH.1)), ?_⟩
          rw [isOT_psi_iff]
          exact ⟨hIHot, rfl, rfl, z_le _, fun g hg => by simp [comps] at hg⟩
        · obtain ⟨Lc, c, hclM, hclN, hdc, hcb, hLc⟩ := hOc i hi hs hD hv
          have hv' := (hoff i hi).2 hv
          have hcCL : c ∈ CL M i := by rw [hclM]; simp
          have hcch := cl_mem_children hcCL
          have hcnt : Counted M i c := by
            unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
          have hrkc : rk true c < rk true i := hRc c hcch hcnt.1 hcnt.2
          obtain ⟨hIH, hIHot⟩ := ih _ (by omega) true c (le_refl _) hdc hcb
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
            have hvot := (ih _ (by have := hRM c hcM; omega) false c (le_refl _) hdv hcb).2
            exact o_of_no_counted hCN hcN hvot
              (no_cnt_of_cl_nil (hCLnil c hcb (hDvNil c hcb hdv)))
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
          refine ⟨o_frame_lhdS hC hG hF hCN hiM hiN hv' hclN hclM hsame hsN hIH ?_ hss hpN, ?_⟩
          · intro s hs0
            have hclc : CL M c = [] := by
              by_contra hne
              have hlt := arg_lt_of_cl hC hG hcM hne
              rw [o_cl_eq hC hG hcM] at hs0
              simp only [psi.injEq] at hs0
              rw [hs0.2.1] at hlt; exact lt_irrefl' _ hlt
            have hvot : isOT (σ.v c) = true := by
              by_cases hdv : DepS M S false c
              · exact (ih _ (by have := hRM c hcM; omega) false c (le_refl _) hdv hcb).2
              · rw [(hoff c hcb).2 hdv]; exact hG.ot_v c hcM
            exact ⟨_, o_of_no_counted hCN hcN hvot (no_cnt_of_cl_nil (hCLnil c hcb hclc))⟩
          · -- standard form of the frame with the lowered last child
            obtain ⟨s, y, hsy⟩ := (single_o hC hG hcM).2
            obtain ⟨s', y', hs'y'⟩ := hcS.2
            have hformN := o_last_form hCN hiN (by rw [hv']; exact hG.ot_v i hiM) hclN hsN hpN hs'y'
            have hLm : Lc.map σ.o = Lc.map ρ.o := List.map_congr_left hsame
            rw [hformN, hLm, hv']
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
                · exact (ih _ (by have := hRM c hcM; omega) false c (le_refl _) hdv hcb).2
                · rw [(hoff c hcb).2 hdv]; exact hG.ot_v c hcM
              rw [hy0.1, sf_ot hvot]
            have hsub' : ∀ g ∈ comps (ρ.v i) s', g ≤ psi s' z z ∨
                g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) := by
              by_cases hvc : σ.v c = ρ.v c
              · rw [hs'v, hvc, ← hsvc]; exact hsub
              · rw [hs'v]; exact hVSN i Lc c hi hclN hvc
            have hot : isOT (psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z) z) = true := by
              rw [← o_last_form hC hiM (hG.ot_v i hiM) hclM (fun d hd => single_o hC hG
                (mem_children (cl_mem_children hd)).2) (by
                  rw [hclM, List.map_append, List.map_singleton]; exact hpM) hsy]
              exact hG.ot_o i hiM
            have hBot := hFO i hiM Lc c [] (by rw [hclM])
            apply node_ot_hard (by rw [← hsy]; exact hG.ot_o c hcM) (by rw [← hs'y']; exact hIHot)
              (Or.inr (by rw [← hs'y', ← hsy]; exact hIH)) hBc (fun hy' => hss s y s' y' hsy hs'y' hy')
              hsub hsub' _ hot hBot
            intro hss' has ht' ht hhi
            rw [hss'] at ht' hs'y'
            exact hHard i Lc c s y y' hi hclN hsy hs'y' has ht' ht hhi
      | false =>
        show Lhd z (σ.v i) (ρ.v i) ∧ isOT (σ.v i) = true
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
          obtain ⟨hIH, hIHot⟩ := ih _ (by have := (hRr h1).2.1 h2 k hu; omega) false k (le_refl _) hdk hkb
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
          obtain ⟨hIH, hIHot⟩ :=
            ih _ (by have := (hRr h1).2.2 h2 j0 hj hjb k0 hk; omega) true k0 (le_refl _) hdk0 hkb
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
              obtain ⟨hvIH, hvIHot⟩ := ih _ (by omega) false k0 (le_refl _) hdv hkb
              change Lhd z (σ.v k0) (ρ.v k0) at hvIH
              change isOT (σ.v k0) = true at hvIHot
              have ho0 : σ.o k0 = psi (σ.v k0) z z := o_of_no_counted hCN hkN hvIHot
                (no_cnt_of_cl_nil (hCLnil k0 hkb (hDvNil k0 hkb hdv)))
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
          refine ⟨v_bump_lhd hC hG hCN hiM hiN h1 h2 he1 he2 hV hch hchN hbL hbjM hbjN hGot hG'ot hS hlt
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
  exact fun b i hD hi => key _ b i (le_refl _) hD hi

end Ytosk
