/-
**3 行・t = 2・q ≠ r で x − 1 が祖先 k へ上げる場合の n ≤ 1（M[n] = M.take x）。**

標準形の例: (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,1,0)(4,2,1)、x = 9、r = 5、q = 6、
upg 8 = 4。M.take x では x − 1 が最後の列になって上げを失う。

- 種は 4 つ（`SQU`）: v(q)・o(q)・o(pq)・v(x − 1)。弱い呼び出しはない。
  - v(x − 1): V + 1 ◁ V + W（`v_upg_drop`、吸収は UpgAbsX）。
  - v(q): x − 1 は q の最後の bump の子 d の部分木にあり、d の最後の子 e の o が ⊴ で変わる。
    さらに x が消える。V + ω^{S′} ◁ V + ω^{S+1}（`v_bump_drop_upg`）。
  - o(q): q に数える子はない（M でも M.take x でも）ので v(q) から。
  - o(pq): 落とす補題の PO から（今までと同じ）。
- k は topped でない（UAT、k ≠ x）ので、k の数え方は M.take x でも変わらない。
-/
import Ytosk.V3T2T

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The seeds for `q ≠ r` when `x − 1` upgrades: `v(q)`, `o(q)`, `o(pq)` and `v(a)` (`a = x − 1`). -/
def SQU (q pq a : Nat) : Bool → Nat → Prop :=
  fun b i => i = q ∨ (b = true ∧ i = pq) ∨ (b = false ∧ i = a)

/-- **The seed `v(q)`**: the children of `i` are `L ++ [d, x]` in `M` and `L ++ [d]` in `N`; the bump term of
`d` goes from `ω^G` to `ω^G′` (`G′ = G` or the strong relation), and the leaf bump child `x` is lost. -/
theorem v_bump_drop_upg {M N : Mat} {ρ σ : Valn} {i d x : Nat} {L : List Nat} {G' G : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hiM : i < M.length) (hiN : i < N.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (he1 : entry N 1 i = entry M 1 i)
    (he2 : entry N 2 i = entry M 2 i) (hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i))
    (hchM : children M i = L ++ [d, x]) (hchN : children N i = L ++ [d])
    (hbL : ∀ d' ∈ L, bumpTerm N σ i d' = bumpTerm M ρ i d')
    (hbdM : bumpTerm M ρ i d = omega G) (hbdN : bumpTerm N σ i d = omega G')
    (hbxM : bumpTerm M ρ i x = one)
    (hGot : isOT G = true) (hG'ot : isOT G' = true) (hS : G' = G ∨ BRelS G' G)
    (hTD : BumpTermDec M ρ)
    (hAbs : ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < psi z two z → q < bumpW M ρ i →
      Lhd z q (bumpW M ρ i)) :
    Lhd z (σ.v i) (ρ.v i) := by
  set V := vOpt ρ (par M 1 i) with hVdef
  have hVot : isOT V = true := by
    rw [hVdef]
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  set Lb := L.map (bumpTerm M ρ i) with hLb
  have hLbot : ∀ t ∈ Lb, isOT t = true := fun t ht => by
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i d
  have hmapM : (children M i).map (bumpTerm M ρ i) = (Lb ++ [omega G]) ++ [one] := by
    rw [hchM, show L ++ [d, x] = (L ++ [d]) ++ [x] by simp, List.map_append, List.map_append,
      List.map_singleton, List.map_singleton, hbdM, hbxM]
  have hmapN : (children N i).map (bumpTerm N σ i) = Lb ++ [omega G'] := by
    rw [hchN, List.map_append, List.map_singleton, hbdN, List.map_congr_left hbL]
  set Pl := nzs Lb with hPl
  have hsumX : ∀ Y, isOT Y = true → sumN (one :: (Lb ++ [omega Y])) = sumN (one :: Pl ++ [omega Y]) := by
    intro Y hY
    rw [sumN_nzs (l := one :: (Lb ++ [omega Y])) (fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · rcases List.mem_append.mp ht with ht | ht
        · exact hLbot t ht
        · simp at ht; rw [ht]; exact isOT_omega hY)]
    simp only [nzs, List.filter_cons, List.filter_append]
    simp [one, omega_ne_z Y]
    rw [hPl, nzs]; simp
  have hsP : ∀ q ∈ Pl, Single q := by
    intro q hq
    rw [hPl, nzs, List.mem_filter] at hq
    obtain ⟨hq, hqz⟩ := hq
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
    unfold bumpTerm at hqz ⊢
    by_cases hb : col M d = bump M i
    · rw [if_pos hb]
      exact single_omega (by
        apply isOT_sumN; intro t ht
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o k (mem_children hk).2)
    · rw [if_neg hb] at hqz; simp at hqz
  have hdecP := hTD i h1 h2
  rw [hmapM, nzs_append, nzs_append, nzs_single (omega_ne_z G), nzs_single (by decide : one ≠ z)]
    at hdecP
  have hpre := List.pairwise_append.mp (List.pairwise_append.mp hdecP).1
  have hpP : Pl.Pairwise (fun a b => b ≤ a) := hpre.1
  have hPt : ∀ q ∈ Pl, omega G ≤ q := fun q hq => hpre.2.2 q hq _ (by simp)
  have hPot : ∀ t ∈ one :: Pl, isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · exact (hsP t ht).1
  have hp'ot : isOT (sumN (one :: Pl ++ [omega G'])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPot t h
    · simp at h; rw [h]; exact isOT_omega hG'ot)
  have hpot : isOT (sumN (one :: Pl ++ [omega G])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPot t h
    · simp at h; rw [h]; exact isOT_omega hGot)
  set S := sumN (one :: Pl ++ [omega G]) with hSdef
  set S' := sumN (one :: Pl ++ [omega G']) with hS'def
  have hsumM : sumN (one :: (children M i).map (bumpTerm M ρ i)) = succ S := by
    rw [hmapM, ← List.cons_append, sumN_snoc, hsumX G hGot, add_one_eq_succ hpot,
      sf_ot (isOT_succ hpot)]
  have ev : ρ.v i = add V (omega (succ S)) := by
    rw [(hC i hiM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, hsumM, sf_ot (isOT_add hVot (isOT_omega (isOT_succ hpot)))]
  have ev' : σ.v i = add V (omega S') := by
    rw [(hCN i hiN).2]; unfold vRhs
    rw [he1, he2, if_neg h1, if_neg h2, hV, hmapN, hsumX G' hG'ot,
      sf_ot (isOT_add hVot (isOT_omega hp'ot))]
  have hE : LhdE (omega S') (omega S) := by
    rcases hS with hS | hS
    · rw [hS'def, hS]; exact Or.inl rfl
    · have hp := brelS_p hsP hpP hPt (single_omega hG'ot) (single_omega hGot) (brelS_omega hG'ot hGot hS)
      exact brelS_lhdE (brelS_omega hp'ot hpot hp)
  have hW : Lhd z (omega S') (omega (succ S)) := by
    rcases hE with h | h
    · rw [h]; exact lhd_omega_succ hpot
    · exact lhd_trans h (lhd_omega_succ hpot)
  have hbW : bumpW M ρ i = omega (succ S) := by
    unfold bumpW; rw [hsumM]
  have hEv : LhdE (σ.v i) (ρ.v i) := by
    rw [ev', ev]
    apply v_strong hVot (single_omega hp'ot) (single_omega (isOT_succ hpot)) (Or.inr hW)
    intro q hq hn hlt'
    by_cases hWE : omega (succ S) < E0
    · exact lhd_lt_small (isOT_mem_summands hVot hq) hWE hlt'
    · rw [← hbW]
      apply hAbs q hq _ (by rw [hbW]; exact hlt')
      intro hq2
      apply hn
      have h2le : two ≤ S' :=
        two_le_sumN_one_cons (by simp) (fun t ht => by
          rcases List.mem_append.mp ht with h | h
          · exact hsP t h
          · simp at h; rw [h]; exact single_omega hG'ot)
      have hom : psi z two z ≤ omega S' := by
        rw [← omega_small two_lt_E0]
        rcases (le_iff _ _).mp h2le with h' | h'
        · exact le_of_lt (omega_lt_omega isOT_two hp'ot h')
        · rw [h']
      exact lt_of_lt_of_le hq2 hom
  apply lhd_of_lhdE_lt hEv
  rw [ev', ev]
  exact add_lt_add_left _ hW.1

section
variable {M : Mat} {r L qp : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hp : par M 0 (r + L) = some (r + qp)) (hqp : qp < L)
  (hxb : col M (r + L) = bump M (r + qp)) (hBE : BumpE2 M)
include hlen hL hA hp hqp hxb hBE

/-- **`t = 2`, `q ≠ r`, `x − 1` upgrades to `k`, `n ≤ 1`** (`M[n] = M.take x`). -/
theorem t2_qnu_take (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M)
    (hR12 : R12 M) (hR01 : R01 M)
    (h00 : entry M 0 0 = 0) {pq : Nat} (hpq : par M 0 (r + qp) = some pq)
    (hqb : col M (r + qp) ≠ bump M pq) (he2pq : entry M 2 pq = 0) (hCLq : CL M (r + qp) = [])
    (hpqCL : CL M pq ≠ []) {k : Nat} (hu : upg M (r + L - 1) = some k)
    -- the shape of `D` in `M`
    (hP1q : ∀ m, par M 1 (r + qp) = some m → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false m)
    (hP1a : ∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false m)
    (hqsh : ∃ Lb d Kb e, children M (r + qp) = Lb ++ [d, r + L] ∧ children M d = Kb ++ [e] ∧
      (∀ f ∈ Kb, ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true f) ∧
      (∀ d' ∈ Lb, ∀ e' ∈ children M d', ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true e'))
    (hDvNil : ∀ c, c < r + L → DepS M (SQU (r + qp) pq (r + L - 1)) false c → CL M c = [])
    (hOS : ∀ i, i < r + L → ¬ (SQU (r + qp) pq (r + L - 1)) true i →
      DepS M (SQU (r + qp) pq (r + L - 1)) true i → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false i →
      ∃ Lp c R, children M i = Lp ++ c :: R ∧ Counted M i c ∧ DepS M (SQU (r + qp) pq (r + L - 1)) true c ∧
        (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ Lp, Counted M i d → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true d))
    (hVSh : ∀ i, i < r + L → ¬ (SQU (r + qp) pq (r + L - 1)) false i → DepS M (SQU (r + qp) pq (r + L - 1)) false i →
      (∀ m, par M 1 i = some m → ¬ DepS M (SQU (r + qp) pq (r + L - 1)) false m) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
        children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M (SQU (r + qp) pq (r + L - 1)) true e)))
    -- values
    {ρ σ : Valn} {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons (M.take (r + L)) σ) (hGN : Good3 (M.take (r + L)) σ) (hRN : Rk (M.take (r + L)) rkN)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hUA : UpgAbsX M (r + L) ρ)
    (hAbs : ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i))
    (hseed : Lhd z (σ.o pq) (ρ.o pq)) :
    isOT (root (M.take (r + L)) σ) = true ∧ root (M.take (r + L)) σ < root M ρ := by
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hqx : r + qp < r + L := by omega
  have hqM : r + qp < M.length := by omega
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hp⟩
  have hpqq : pq < r + qp := par_lt M 0 _ _ hpq
  have he2q := e2_q hlen hp hxb hBE
  have he1q : entry M 1 (r + qp) ≠ 0 := by
    have h1 : entry M 1 (r + L) = entry M 1 (r + qp) :=
      e1_of_col (show col M (r + L) = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from hxb)
    intro h0; rw [← h1] at h0; have := hR12 _ h0; have := e2_x hxb; omega
  have hcolN : ∀ i, i < r + L → col (M.take (r + L)) i = col M i := fun i hi => col_take M hi
  have hbumpN : ∀ i, i < r + L → bump (M.take (r + L)) i = bump M i := fun i hi => bump_take M hi
  have hchN : ∀ i, i < r + L → i ≠ r + qp → children (M.take (r + L)) i = children M i := by
    intro i _ hiq
    rw [children_take, children_filter_x hlen (fun h => hiq (by
      have h' := (mem_children_iff.mp h).2; rw [hp] at h'; exact (Option.some.inj h').symm))]
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hp] at h'; exact (Option.some.inj h').symm
  have hchx : ∀ i c, c ∈ children M i → i ≠ r + qp → c < r + L := by
    intro i c hc hiq; by_contra h; exact hiq (hxc i c hc (by omega)).2
  -- the upgrade target `k`
  have hax : r + L - 1 < r + L := by omega
  have hkx : k < r + L := by
    by_contra h
    exact upg_not_x hlen hA hp hxb hBE hu (by omega) hax
  have hkT : topped M k = false := hUAT _ k hu (by omega)
  have hcqM : children M (r + qp) =
      (children M (r + qp)).filter (fun d => decide (d < r + L)) ++ [r + L] :=
    split_last_max _ _ (children_sorted M _) hxq (fun d hd => by have := (mem_children hd).2; omega)
  have hqT : topped M (r + qp) = true := by
    unfold topped; rw [hcqM]; simp [hxb]
  have hkq : k ≠ r + qp := by intro h; rw [h, hqT] at hkT; cases hkT
  have hupgN : ∀ i, i < r + L → i ≠ r + L - 1 → upg (M.take (r + L)) i = upg M i := by
    intro i hi hia; exact upg_take M (by omega)
  have hcntS : ∀ i c, i < r + L → i ≠ pq → c ∈ children M i → c < r + L →
      (Counted (M.take (r + L)) i c ↔ Counted M i c) := by
    intro i c hi hipq hc hcx
    by_cases hck : c = k
    · rw [hck]
      unfold Counted
      rw [col_take M hkx, bump_take M hi,
        topped_take_eq hlen hkx (fun h => hkq (hxc k (r + L) h (le_refl _)).2), hkT]
      simp
    by_contra h
    rcases cnt_change hlen hi hcx h with h' | h'
    · apply hipq
      have hc' := (mem_children_iff.mp h').2; rw [hp] at hc'
      have hcq : c = r + qp := (Option.some.inj hc').symm
      have h'' := (mem_children_iff.mp hc).2; rw [hcq, hpq] at h''; exact (Option.some.inj h'').symm
    · rw [hu] at h'; exact hck (Option.some.inj h').symm
  have hCLnil : ∀ c, c < r + L → CL M c = [] → CL (M.take (r + L)) c = [] := by
    intro c hc hcl
    by_cases hcpq : c = pq
    · exact (hpqCL (by rw [← hcpq]; exact hcl)).elim
    · unfold CL at hcl ⊢
      rw [List.filter_eq_nil_iff] at hcl ⊢
      intro d hd hdc
      rw [children_take, List.mem_filter] at hd
      have hdx : d < r + L := by simpa using hd.2
      exact hcl d hd.1 (decide_eq_true ((hcntS c d hc hcpq hd.1 hdx).mp (of_decide_eq_true hdc)))
  -- the roots
  have hRD : ∀ R, R < r + L → Anc0 M R (r + L) → col M R = (0, 0, 0) →
      DepS M (SQU (r + qp) pq (r + L - 1)) true R ∧ ¬ (fun _ _ => False : Bool → Nat → Prop) true R := by
    intro R hR hRA hR0
    have he2R : entry M 2 R = 0 := e2_of_col hR0
    have hRq : R ≠ r + qp := by intro h; rw [h] at he2R; omega
    have hRq' : Anc0 M R (r + qp) := anc0_par hRA (by omega) hp
    have hRpq : Anc0 M R pq := anc0_par hRq' hRq hpq
    refine ⟨?_, id⟩
    apply path_upS hUAT hZ2 hR12 hBE (pq - R) R pq (le_refl _) (by omega) hRpq (ne_of_e2z he2pq)
      (DepS.seed (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    intro t _ htpq
    have := htpq.le
    exact ⟨r + L, by omega, Anc0.step hp (Anc0.step hpq (Anc0.refl pq)), not_anc_out (by omega) (by omega)⟩
  -- the seeds
  have hSeed : ∀ b i, (SQU (r + qp) pq (r + L - 1)) b i → i < r + L → DepS M (SQU (r + qp) pq (r + L - 1)) b i →
      (∀ i, i < r + L → (¬ DepS M (SQU (r + qp) pq (r + L - 1)) true i → σ.o i = ρ.o i) ∧
        (¬ DepS M (SQU (r + qp) pq (r + L - 1)) false i → σ.v i = ρ.v i)) →
      (∀ b' i', rkM b' i' < rkM b i → DepS M (SQU (r + qp) pq (r + L - 1)) b' i' → i' < r + L →
        ¬ (fun _ _ => False : Bool → Nat → Prop) b' i' → Lhd z (valB σ b' i') (valB ρ b' i')) →
      Lhd z (valB σ b i) (valB ρ b i) := by
    intro b i hs _ _ hoff ih
    rcases hs with hiq | ⟨hb, hipq⟩ | ⟨hb, hia⟩
    · subst hiq
      cases b with
      | true =>
        show Lhd z (σ.o (r + qp)) (ρ.o (r + qp))
        have hv : Lhd z (σ.v (r + qp)) (ρ.v (r + qp)) :=
          ih false (r + qp) (hRM (r + qp) hqM).1 (DepS.seed (Or.inl rfl)) hqx id
        rw [o_of_no_counted hCN (by rw [hlT]; omega) (hGN.ot_v _ (by rw [hlT]; omega))
            (no_cnt_of_cl_nil (hCLnil _ hqx hCLq)),
          o_of_no_counted hC hqM (hG.ot_v _ hqM) (no_cnt_of_cl_nil hCLq)]
        exact lhd_of_lhdE_lt (lhdE_oq_v (Or.inr hv)) (psi_lt_psi_z_iff.mpr (Or.inl hv.1))
      | false =>
        show Lhd z (σ.v (r + qp)) (ρ.v (r + qp))
        obtain ⟨Lb, d, Kb, e, hchq, hchd, hKnd, hLnd⟩ := hqsh
        have hs := children_sorted M (r + qp)
        rw [hchq] at hs
        have hp3 := List.pairwise_append.mp hs
        have hdx : d < r + L := (List.pairwise_cons.mp hp3.2.1).1 (r + L) (by simp)
        have hLd : ∀ d' ∈ Lb, d' < d := fun d' hd' => hp3.2.2 d' hd' d (by simp)
        have hdM : d ∈ children M (r + qp) := by rw [hchq]; simp
        have hdq : d ≠ r + qp := by have := (mem_children hdM).1; omega
        have hall := all_bump_of_last hR0 hZ2 hSD hZ1 he2q
          (show children M (r + qp) = (Lb ++ [d]) ++ [r + L] by rw [hchq]; simp) hxb
        have hdb : col M d = bump M (r + qp) := hall d hdM
        have heM : e ∈ children M d := by rw [hchd]; simp
        have hex : e < r + L := hchx d e heM hdq
        have heMl : e < M.length := (mem_children heM).2
        have heN : e < (M.take (r + L)).length := by rw [hlT]; exact hex
        have hcqN : children (M.take (r + L)) (r + qp) = Lb ++ [d] := by
          rw [children_take]
          have h := hcqM.symm.trans (show children M (r + qp) = (Lb ++ [d]) ++ [r + L] by rw [hchq]; simp)
          exact List.append_inj_left' h rfl
        have hV : vOpt σ (par (M.take (r + L)) 1 (r + qp)) = vOpt ρ (par M 1 (r + qp)) := by
          rw [par_take M 1 _ hqx]
          cases hm : par M 1 (r + qp) with
          | none => rfl
          | some m =>
            show σ.v m = ρ.v m
            exact (hoff m (by have := par_lt M 1 _ m hm; omega)).2 (hP1q m hm)
        have hbL : ∀ d' ∈ Lb, bumpTerm (M.take (r + L)) σ (r + qp) d' = bumpTerm M ρ (r + qp) d' := by
          intro d' hd'
          have hd'x : d' < r + L := by have := hLd d' hd'; omega
          have hd'M : d' ∈ children M (r + qp) := by rw [hchq]; simp [hd']
          have hd'q : d' ≠ r + qp := by have := (mem_children hd'M).1; omega
          apply bumpTerm_eq_of
          · rw [hcolN d' hd'x, hbumpN _ hqx]
          · intro _
            rw [hchN d' hd'x hd'q]
            apply List.map_congr_left
            intro e' he'
            exact (hoff e' (hchx d' e' he' hd'q)).1 (hLnd d' hd' e' he')
        have hKv : Kb.map σ.o = Kb.map ρ.o := List.map_congr_left (fun f hf => by
          have hfM : f ∈ children M d := by rw [hchd]; simp [hf]
          exact (hoff f (hchx d f hfM hdq)).1 (hKnd f hf))
        have hbdM : bumpTerm M ρ (r + qp) d = omega (sumN (Kb.map ρ.o ++ [ρ.o e])) := by
          unfold bumpTerm; rw [if_pos hdb, hchd, List.map_append, List.map_singleton]
        have hbdN : bumpTerm (M.take (r + L)) σ (r + qp) d = omega (sumN (Kb.map ρ.o ++ [σ.o e])) := by
          unfold bumpTerm
          rw [if_pos (by rw [hcolN d hdx, hbumpN _ hqx]; exact hdb), hchN d hdx hdq, hchd,
            List.map_append, List.map_singleton, hKv]
        have hbxM : bumpTerm M ρ (r + qp) (r + L) = one := by
          unfold bumpTerm; rw [if_pos hxb, children_last_nil hlen]; exact omega_z
        have hsK : ∀ u ∈ Kb.map ρ.o, Single u := fun u hu => by
          obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hu
          exact single_o hC hG (mem_children (show f ∈ children M d by rw [hchd]; simp [hf])).2
        have hGot : isOT (sumN (Kb.map ρ.o ++ [ρ.o e])) = true := isOT_sumN _ (fun u hu => by
          rcases List.mem_append.mp hu with h | h
          · exact (hsK u h).1
          · simp at h; rw [h]; exact hG.ot_o e heMl)
        have hrel : (sumN (Kb.map ρ.o ++ [σ.o e]) = sumN (Kb.map ρ.o ++ [ρ.o e]) ∨
            BRelS (sumN (Kb.map ρ.o ++ [σ.o e])) (sumN (Kb.map ρ.o ++ [ρ.o e]))) ∧
            isOT (sumN (Kb.map ρ.o ++ [σ.o e])) = true := by
          by_cases hDe : DepS M (SQU (r + qp) pq (r + L - 1)) true e
          · have hrke : rkM true e < rkM false (r + qp) :=
              ((hRM (r + qp) hqM).2.2 he1q).2.2 (by omega) d hdM hdb e heM
            have hIH : Lhd z (σ.o e) (ρ.o e) := ih true e hrke hDe hex id
            have hdec := hKD (r + qp) he1q (by omega) d hdM hdb
            rw [hchd, List.map_append, List.map_singleton] at hdec
            have hform : (∃ s y y', ρ.o e = psi s y z ∧ σ.o e = psi s y' z) ∨
                (∃ w' w Y, σ.o e = psi w' z z ∧ ρ.o e = psi w Y z ∧ LhdE w' w ∧ one ≤ w') := by
              obtain ⟨y1, hy1⟩ := o_psi_sub hC heMl
              rw [sf_ot (hG.ot_v e heMl)] at hy1
              by_cases hve : σ.v e = ρ.v e
              · obtain ⟨y0, hy0⟩ := o_psi_sub hCN heN
                rw [sf_ot (hGN.ot_v e heN), hve] at hy0
                exact Or.inl ⟨_, _, _, hy1, hy0⟩
              · have hdv : DepS M (SQU (r + qp) pq (r + L - 1)) false e := by
                  by_contra hn'; exact hve ((hoff e hex).2 hn')
                have ho0 : σ.o e = psi (σ.v e) z z :=
                  o_of_no_counted hCN heN (hGN.ot_v e heN)
                    (no_cnt_of_cl_nil (hCLnil e hex (hDvNil e hex hdv)))
                have hvIH : Lhd z (σ.v e) (ρ.v e) :=
                  ih false e (by have := (hRM e heMl).1; omega) hdv hex id
                have he1e : entry M 1 e ≠ 0 := by
                  intro he; apply hve
                  rw [v_z_of_e1 hC heMl he, v_z_of_e1 hCN heN (by rw [entry_take M 1 hex]; exact he)]
                have hv0 : σ.v e ≠ z := v_ne_z_of_e1 hCN heN (by rw [entry_take M 1 hex]; exact he1e)
                exact Or.inr ⟨_, _, _, ho0, hy1, Or.inr hvIH, one_le_of_ne_z hv0⟩
            obtain ⟨hS, _, hG'ot⟩ := g_brel hsK hdec (single_o hC hG heMl) (single_o hCN hGN heN) hIH hform
            exact ⟨Or.inr hS, hG'ot⟩
          · rw [(hoff e hex).1 hDe]; exact ⟨Or.inl rfl, hGot⟩
        exact v_bump_drop_upg hC hG hCN hqM (by rw [hlT]; omega) he1q (by omega)
          (entry_take M 1 hqx) (entry_take M 2 hqx) hV hchq hcqN hbL hbdM hbdN hbxM hGot hrel.2 hrel.1
          hTD (hAbs _ hqx he1q (by omega))
    · subst hb; rw [hipq]; exact hseed
    · subst hb; rw [hia]
      show Lhd z (σ.v (r + L - 1)) (ρ.v (r + L - 1))
      apply v_upg_drop hZ2 hC hG hCN (by omega) (by omega) (by rw [hlT]; omega) hu
        (entry_take M 1 (by omega)) (entry_take M 2 (by omega)) _ (upg_take_last M (by omega) (by omega))
        (show r + L - 1 + 1 = r + L by omega) hUA
      rw [par_take M 1 _ (by omega)]
      cases hm : par M 1 (r + L - 1) with
      | none => rfl
      | some m =>
        show σ.v m = ρ.v m
        exact (hoff m (by have := par_lt M 1 _ m hm; omega)).2 (hP1a m hm)
  exact t2_assemble (S := SQU (r + qp) pq (r + L - 1)) (W := fun _ _ => False) (bnd := r + L) (p := r + qp)
    hC hG hRM hCN hGN hRN hF hVS hTD hKD hR01 hR12 h00 hlen (by rw [hlT]) (fun i hi hiq => hchN i hi hiq)
    (Or.inl (Or.inl rfl)) (Or.inr (Or.inl rfl))
    (fun i hq hb => by have h' := (mem_children_iff.mp hq).2; rw [hpq] at h'; cases h'; exact hqb hb)
    (fun y i hi => entry_take M y hi) (fun i hi => par_take M 1 i hi)
    (fun i hi hs => hupgN i hi (fun h => hs (Or.inr (Or.inr ⟨rfl, h⟩))))
    (fun i c hi hs hc hcx => hcntS i c hi (fun h => hs (Or.inr (Or.inl ⟨rfl, h⟩))) hc hcx)
    (fun i c hi hc hcx => by obtain ⟨_, rfl⟩ := hxc i c hc hcx; exact Or.inl (Or.inl rfl))
    (fun i k hi hk hkx => (upg_not_x hlen hA hp hxb hBE hk hkx hi).elim)
    (fun i j hi hj hjx _ => by have := (mem_children hj).2; rw [hlT] at this; omega)
    (fun i j hi hj hjx _ => by obtain ⟨_, rfl⟩ := hxc i j hj hjx; exact Or.inl rfl)
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc j k hk hkx
      have h' := (mem_children_iff.mp hj).2; rw [hpq] at h'; cases h'
      exact absurd hjb hqb)
    (fun j hj0 hj => by rw [hlT] at hj; omega)
    (by have := anc0_e0_lt hA (by omega); omega)
    (fun i h => h.elim) (fun i h => h) (fun i c _ _ h => h.elim) (fun i j c _ _ _ _ _ h => h.elim)
    (fun c hc _ _ hd => hDvNil c hc hd) (fun c hc _ _ hd => hCLnil c hc (hDvNil c hc hd))
    (fun c hc _ hcl => hCLnil c hc hcl) (fun i hi hns _ hD hv => hOS i hi hns hD hv) hVSh hRD
    (fun i _ h => h.elim) hAbs hSeed

end

end Ytosk
