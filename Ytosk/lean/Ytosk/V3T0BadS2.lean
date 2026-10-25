/-
**種 S2 の弱い最後の項の版（2026-10-25、Bad2・t = 0 の r = p 用）。**

旧の `t0_S2G` は最後の写しの bump 項 `O′ = ω^{G0′}` について `O′ ⊴ ω^{G0}` を仮定していた。Bad2 の r = p では偽
（r の最後の子 x − 1 の値が弱く変わる）。代わりに和の段の `ω^{G0} + O′ ◁ ω^{G0 + 1}` を仮定する（`s2_p2W`）。
-/
import Ytosk.V3T0BadS3

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The `p` level of seed S2 with a weak last copy** (as `s2_p2`, from `O + O′ ◁ X` and `O′ ≤ O`). -/
theorem s2_p2W {Pl : List T} {O O' X : T} {n : Nat} (hn : 2 ≤ n)
    (hsP : ∀ q ∈ Pl, Single q) (hpP : Pl.Pairwise (fun a b => b ≤ a)) (hPt : ∀ q ∈ Pl, X ≤ q)
    (hO : Single O) (hO' : Single O') (hX : Single X) (hOX : O < X)
    (hlm : ∀ k, Lhd z (mulT O k) X)
    (hsh : ∃ s b', O = psi s b' z ∧ X = psi s (app b' one) z) (hT1 : Lhd z (app O O') X) (hO'le : O' ≤ O) :
    BRelS (sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O']))) (sumN (one :: Pl ++ [X])) ∧
      sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O'])) < sumN (one :: Pl ++ [X]) := by
  rcases (le_iff _ _).mp hO'le with hl0 | heq
  swap
  · rw [heq]
    have : List.replicate (n - 1) O ++ [O] = List.replicate n O := by
      rw [← List.replicate_succ']; congr 1; omega
    rw [this]
    exact s2_p (by omega) hsP hpP hPt hO hX hOX hlm hsh
  obtain ⟨s, b', rfl, rfl⟩ := hsh
  set O := psi s b' z with hOdef
  set X := psi s (app b' one) z with hXdef
  have hRs : ∀ t ∈ List.replicate (n - 1) O ++ [O'], Single t := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · rw [(List.mem_replicate.mp h).2]; exact hO
    · simp at h; rw [h]; exact hO'
  have hRp : (List.replicate (n - 1) O ++ [O']).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_append.mpr ⟨List.pairwise_replicate.mpr (Or.inr (le_refl _)), by simp,
      fun a ha b hb => by
        simp at hb; rw [hb, (List.mem_replicate.mp ha).2]; exact le_of_lt hl0⟩
  have hsumR : sumN (List.replicate (n - 1) O ++ [O']) = app (mulT O (n - 1)) O' := by
    rw [sumN_snoc_dec hRs hRp, sumN_replicate hO]
  have hT : Lhd z (app (mulT O (n - 1)) O') X :=
    lhd_mulT_mono hT1 (le_of_lt hl0) hO'.2 (n - 1) (by omega)
  obtain ⟨m, hm⟩ : ∃ m, n - 1 = m + 1 := ⟨n - 2, by omega⟩
  have hTf : app (mulT O (n - 1)) O' = psi s b' (app (mulT O m) O') := by
    rw [hm, show mulT O (m + 1) = app O (mulT O m) from rfl, app_assoc, hOdef, app_psi, app_z]
  have hone : one < X := by
    unfold one; rw [hXdef, psi_lt_psi]
    rcases lt_or_ge z s with h | h
    · exact Or.inl h
    · have hs : s = z := le_antisymm h (z_le _)
      subst hs
      exact Or.inr (Or.inl ⟨rfl, lt_of_le_of_lt (z_le b') (lt_app_one b')⟩)
  have hO1 : one < O := lt_of_le_of_lt (one_le_of_ne_z (single_ne_z hO')) hl0
  cases Pl with
  | nil =>
    simp only [List.cons_append, List.nil_append]
    rw [onep_self hX hone]
    rw [show List.replicate (n - 1) O ++ [O'] = O :: (List.replicate m O ++ [O']) by
      rw [hm, List.replicate_succ, List.cons_append]]
    rw [sumN_one_cons_gt hO hO1, ← List.cons_append, ← List.replicate_succ, ← hm, hsumR]
    refine ⟨?_, hT.1⟩
    by_cases hE : X < E0
    · exact Or.inl ⟨Or.inr hT, hE⟩
    · rw [hTf] at hT ⊢
      refine Or.inr (Or.inl ⟨Or.inr hT, ?_, s, b', app (mulT O m) O', app b' one, z, rfl, rfl⟩)
      intro hlt
      obtain ⟨hv, hb⟩ := lt_E0_iff.mp hlt
      exact hE (lt_E0_iff.mpr ⟨hv, app_one_lt_Om hb⟩)
  | cons q Pr =>
    have hq := hsP q (by simp)
    have hq1 : one < q := lt_of_lt_of_le hone (hPt q (by simp))
    simp only [List.cons_append]
    rw [sumN_one_cons_gt hq hq1, sumN_one_cons_gt hq hq1, ← List.cons_append, ← List.cons_append]
    have hall : ∀ t ∈ (q :: Pr) ++ [X], Single t := fun t ht => by
      rcases List.mem_append.mp ht with h | h
      · exact hsP t h
      · simp at h; rw [h]; exact hX
    have hpall : ((q :: Pr) ++ [X]).Pairwise (fun a b => b ≤ a) :=
      List.pairwise_append.mpr ⟨hpP, by simp, fun a ha b hb => by simp at hb; rw [hb]; exact hPt a ha⟩
    have hall' : ∀ t ∈ (q :: Pr) ++ (List.replicate (n - 1) O ++ [O']), Single t := fun t ht => by
      rcases List.mem_append.mp ht with h | h
      · exact hsP t h
      · exact hRs t h
    have hpall' : ((q :: Pr) ++ (List.replicate (n - 1) O ++ [O'])).Pairwise (fun a b => b ≤ a) :=
      List.pairwise_append.mpr ⟨hpP, hRp, fun a ha b hb => by
        have hb' : b ≤ O := by
          rcases List.mem_append.mp hb with h | h
          · rw [(List.mem_replicate.mp h).2]
          · simp at h; rw [h]; exact le_of_lt hl0
        exact le_trans hb' (le_trans (le_of_lt hOX) (hPt a ha))⟩
    rw [sumN_append_dec hall hpall, sumN_append_dec hall' hpall', hsumR, sumN_singleton hX]
    have hS : sumN (q :: Pr) ≠ z := sumN_ne_z hsP hpP (by simp)
    refine ⟨?_, app_lt_app_left _ hT.1⟩
    have := brelS_app_same hS (Or.inr hT) z
    simpa using this

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN

/-- **Seed S2 with a weak last copy** (as `t0_S2G`). -/
theorem t0_S2GW {g : Nat} (hg : par M 0 r = some g) (hjb : col M r = bump M g)
    (h1 : entry M 1 g ≠ 0) (h2 : entry M 2 g ≠ 0)
    (hTD : BumpTermDec M ρ) (hAbs : AbsWN M (TRIO.gexp M r L 0 0 n) r ρ σ)
    (hbF : ∀ d, d ∈ children M g → d < r →
      bumpTerm (TRIO.gexp M r L 0 0 n) σ g d = bumpTerm M ρ g d)
    (hbroot : ∀ k, k + 1 < n → bumpTerm (TRIO.gexp M r L 0 0 n) σ g (r + k * L) =
      omega (sumN ((children (M.take (r + L)) r).map ρ.o)))
    {O' : T} (hblast : bumpTerm (TRIO.gexp M r L 0 0 n) σ g (r + (n - 1) * L) = O') (hO'S : Single O')
    (hT1 : Lhd z (app (omega (sumN ((children (M.take (r + L)) r).map ρ.o))) O')
      (omega (app (sumN ((children (M.take (r + L)) r).map ρ.o)) one)))
    (hO'le : O' ≤ omega (sumN ((children (M.take (r + L)) r).map ρ.o)))
    (hV : vOpt σ (par (TRIO.gexp M r L 0 0 n) 1 g) = vOpt ρ (par M 1 g)) :
    Lhd z (σ.v g) (ρ.v g) := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hgr : g < r := par_lt M 0 r g hg
  have hgM : g < M.length := by omega
  have hgN : g < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  set G0 := sumN ((children (M.take (r + L)) r).map ρ.o) with hG0
  have hG0ot : isOT G0 = true := isOT_sumN _ (fun t ht => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    rw [children_take, List.mem_filter] at hc
    exact hG.ot_o c (mem_children hc.1).2)
  -- the bump term of `r` in `M`
  have hbr : bumpTerm M ρ g r = omega (app G0 one) := by
    unfold bumpTerm
    rw [if_pos hjb]
    have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
    rw [children_split_x (x := r + L) hlen hxr, List.map_append, List.map_singleton,
      o_x_one hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG, sumN_snoc,
      ← children_take, ← hG0, sf_ot (isOT_add hG0ot rfl), add_one_eq_app]
  -- the children of `g`
  set F := (children M g).filter (fun d => decide (d < r)) with hFdef
  have hchM : children M g = F ++ [r] := children_g_last hlen hL hp hg
  set f : Nat → Nat := fun k => r + k * L with hfdef
  have hchN : children (TRIO.gexp M r L 0 0 n) g = F ++ (List.range n).map f := by
    rw [children_g0 hlen hL hp hn hg, hchM, List.append_assoc]
    congr 1
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [hfdef]
  set Lb := F.map (bumpTerm M ρ g) with hLb
  set O := omega G0 with hOdef
  set X := omega (app G0 one) with hXdef
  have hmapM : (children M g).map (bumpTerm M ρ g) = Lb ++ [X] := by
    rw [hchM, List.map_append, List.map_singleton, hbr]
  have hmapN : (children (TRIO.gexp M r L 0 0 n) g).map (bumpTerm (TRIO.gexp M r L 0 0 n) σ g) =
      Lb ++ (List.replicate (n - 1) O ++ [O']) := by
    rw [hchN, List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro d hd
      have := List.mem_filter.mp hd
      exact hbF d this.1 (by simpa using this.2)
    · have hr : List.range n = List.range (n - 1) ++ [n - 1] := by
        rw [← List.range_succ]; congr 1; omega
      rw [hr, List.map_append]
      congr 1
      · rw [List.eq_replicate_iff]
        refine ⟨by simp, fun b hb => ?_⟩
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
        exact hbroot k (by have := List.mem_range.mp hk; omega)
      · simp only [List.map_cons, List.map_nil]
        exact congrArg (fun t => [t]) hblast
  -- the shapes
  obtain ⟨sO, bO, hOf, hXf⟩ := omega_succ_form hG0ot
  have hO : Single O := single_omega hG0ot
  have hXot : isOT (app G0 one) = true := by have := isOT_succ hG0ot; simpa [succ] using this
  have hX : Single X := single_omega hXot
  have hOX : O < X := omega_lt_omega hG0ot hXot (lt_app_one G0)
  have hlm : ∀ k, Lhd z (mulT O k) X := by
    intro k; rw [hOdef, hXdef, hOf, hXf]; exact lhd_mulT k
  -- the `p` level
  set V := vOpt ρ (par M 1 g) with hVdef
  have hVot : isOT V = true := by
    rw [hVdef]
    cases hpp : par M 1 g with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 g m hpp; omega)
  have hLbot : ∀ t ∈ Lb, isOT t = true := fun t ht => by
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG g d
  set Pl := nzs Lb with hPl
  have hnzT : ∀ (T0 : List T), (∀ t ∈ T0, Single t) →
      sumN (one :: (Lb ++ T0)) = sumN (one :: Pl ++ T0) := by
    intro T0 hT0
    rw [sumN_nzs (l := one :: (Lb ++ T0)) (fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · rcases List.mem_append.mp ht with ht | ht
        · exact hLbot t ht
        · exact (hT0 t ht).1)]
    have hT : T0.filter (fun t => !decide (t = z)) = T0 := by
      rw [List.filter_eq_self]; intro t ht; simpa using single_ne_z (hT0 t ht)
    simp only [nzs, List.filter_cons, List.filter_append]
    simp [one]
    rw [hT, hPl, nzs]; simp
  have hsP : ∀ q ∈ Pl, Single q := by
    intro q hq
    rw [hPl, nzs, List.mem_filter] at hq
    obtain ⟨hq, hqz⟩ := hq
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
    unfold bumpTerm at hqz ⊢
    by_cases hb : col M d = bump M g
    · rw [if_pos hb]
      exact single_omega (by
        apply isOT_sumN; intro t ht
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o k (mem_children hk).2)
    · rw [if_neg hb] at hqz; simp at hqz
  have hdecP := hTD g h1 h2
  rw [hmapM, nzs_append, nzs_single (single_ne_z hX)] at hdecP
  have hpre := List.pairwise_append.mp hdecP
  have hpP : Pl.Pairwise (fun a b => b ≤ a) := hpre.1
  have hPt : ∀ q ∈ Pl, X ≤ q := fun q hq => hpre.2.2 q hq _ (by simp)
  have hT0s : ∀ t ∈ List.replicate (n - 1) O ++ [O'], Single t := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · rw [(List.mem_replicate.mp h).2]; exact hO
    · simp at h; rw [h]; exact hO'S
  obtain ⟨hS, hlt⟩ := s2_p2W hn2 hsP hpP hPt hO hO'S hX hOX hlm ⟨sO, bO, hOf, hXf⟩ hT1 hO'le
  have hPot : ∀ t ∈ one :: Pl, isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · exact (hsP t ht).1
  have hp'ot : isOT (sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O']))) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPot t h
    · exact (hT0s t h).1)
  have hpot : isOT (sumN (one :: Pl ++ [X])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPot t h
    · simp at h; rw [h]; exact hX.1)
  have ev : ρ.v g = add V (omega (sumN (one :: Pl ++ [X]))) := by
    rw [(hC g hgM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, hmapM, hnzT [X] (by simp [hX]),
      sf_ot (isOT_add hVot (isOT_omega hpot))]
  have ev' : σ.v g = add V (omega (sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O'])))) := by
    rw [(hCN g hgN).2]; unfold vRhs
    rw [entry_pre0 hlen hn 1 (by omega), entry_pre0 hlen hn 2 (by omega), if_neg h1, if_neg h2, hV,
      hmapN, hnzT (List.replicate (n - 1) O ++ [O']) hT0s,
      sf_ot (isOT_add hVot (isOT_omega hp'ot))]
  have hW := brelS_lhdE (brelS_omega hp'ot hpot hS)
  have hbW : bumpW M ρ g = omega (sumN (one :: Pl ++ [X])) := by
    unfold bumpW; rw [hmapM, hnzT [X] (by simp [hX])]
  have hbWN : bumpW (TRIO.gexp M r L 0 0 n) σ g =
      omega (sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O']))) := by
    unfold bumpW; rw [hmapN, hnzT (List.replicate (n - 1) O ++ [O']) hT0s]
  have hE : LhdE (σ.v g) (ρ.v g) := by
    rw [ev', ev]
    apply v_strong hVot (single_omega hp'ot) (single_omega hpot) hW
    intro q hq hn' hlt'
    by_cases hWE : omega (sumN (one :: Pl ++ [X])) < E0
    · exact lhd_lt_small (isOT_mem_summands hVot hq) hWE hlt'
    · rw [← hbW]
      apply hAbs g (par_lt M 0 r g hg) h1 h2 q hq _ (by rw [hbWN]; exact hn') (by rw [hbW]; exact hlt')
      intro hq2
      apply hn'
      have h2le : two ≤ sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O'])) :=
        two_le_sumN_one_cons (by simp) (fun t ht => by
          rcases List.mem_append.mp ht with h | h
          · exact hsP t h
          · exact hT0s t h)
      have hom : psi z two z ≤ omega (sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O']))) := by
        rw [← omega_small two_lt_E0]
        rcases (le_iff _ _).mp h2le with h' | h'
        · exact le_of_lt (omega_lt_omega isOT_two hp'ot h')
        · rw [h']
      exact lt_of_lt_of_le hq2 hom
  apply lhd_of_lhdE_lt hE
  rw [ev', ev]
  exact add_lt_add_left _ (omega_lt_omega hp'ot hpot hlt)

end

/-- **Seed S2 from the sum-level fact `ω^{G0} + ω^{G0′} ◁ ω^{G0 + 1}`** (`t0_S2GW`; `G0`, `G0′` the sums of the children
of `r` in `M.take x` under `ρ`, `ρ′`). -/
theorem t0_S2_of_sum {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (I : Inv3C M ρ rk) (D : T0DropF M ρ rk) (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0) (hAbW : T0AbsW M r L ρ)
    (hT1M : Lhd z (app (omega (sumN ((children (M.take (r + L)) r).map ρ.o)))
      (omega (sumN ((children (M.take (r + L)) r).map (drop1 M (r + L) rk).o))))
      (omega (app (sumN ((children (M.take (r + L)) r).map ρ.o)) one)))
    {n : Nat} (hn2 : 2 ≤ n) {σ : Valn} (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) :
    ∀ g, par M 0 r = some g → col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 →
      Lhd z (σ.v g) (ρ.v g) := by
  have K := t0NCtx_of I D hlen hL hp he1 hn2 hCN
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  set ρ' := drop1 M (r + L) rk with hρ'
  have hDP := D.po
  rw [show M.length - 1 = r + L by omega] at hDP
  have hdrop : ∀ k, k < r + L → PO ρ ρ' k ∧ PV M ρ ρ' k := hDP
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hnl : (n - 1) * L + L = n * L := by rw [← Nat.succ_mul]; congr 1; omega
  intro g hg hjb h1 h2
  have hgr : g < r := par_lt M 0 r g hg
  have hrc : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
  have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
  have hgD : DepX M (r + L) false g := DepX.vbump h1 h2 hrc hjb hxr DepX.leaf
  obtain ⟨_, hpnd, hcase⟩ := dv_shape hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp (by omega) hgD
  rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j', k', hch, _, hchj, _, hKnd, hLnd⟩
  · exact absurd h2' h2
  · have hchM := children_g_last hlen hL hp hg
    have hjr : j' = r := by
      have := congrArg List.getLast? (hch.symm.trans hchM)
      simpa using this
    subst hjr
    -- the children of `r` in `M.take x` and the last copy
    have hG0'ot : isOT (sumN ((children (M.take (j' + L)) j').map ρ'.o)) = true := isOT_sumN _ (fun t ht => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
      exact K.GT.ot_o c (mem_children hc).2)
    have hG0ot : isOT (sumN ((children (M.take (j' + L)) j').map ρ.o)) = true := isOT_sumN _ (fun t ht => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
      rw [children_take, List.mem_filter] at hc
      exact I.good.ot_o c (mem_children hc.1).2)
    have hcopy : ∀ k, k < n → bumpTerm N σ g (j' + k * L) =
        omega (sumN (((children M j').filter (fun c => decide (c < j' + L))).map
          (σ.o ∘ shk j' (k * L)))) := by
      intro k hk
      have hcolk : col N (j' + k * L) = bump N g := by
        rw [col_root0 hlen hL hp hn hk, bump_pre0 hlen hL hp hn (by omega)]; exact hjb
      unfold bumpTerm
      rw [if_pos hcolk]
      have hch0 := children_copy0 hlen hL hp hn (k := k) (q := 0) hk hL
      rw [Nat.add_zero, Nat.add_zero] at hch0
      rw [hch0, List.map_map]
    apply t0_S2GW (O' := omega (sumN ((children (M.take (j' + L)) j').map ρ'.o))) hlen hL hp hn I.r0p I.z2
      I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hg hjb h1 h2 I.td (hAbW n hn2 σ hCN)
    · intro d hd hdr
      have hdL : d ∈ Lb := by
        rw [hch] at hd
        rcases List.mem_append.mp hd with h | h
        · exact h
        · simp at h; omega
      have hdg : par M 0 j' ≠ some d := by
        intro h'; rw [hg] at h'; cases h'; have := (mem_children hd).1; omega
      apply bumpTerm_eq_of
      · rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
      · intro _
        rw [children_pre0 hlen hL hp hn hdr hdg]
        apply List.map_congr_left
        intro e he
        have her := children_lt_r hlen hL hp hdr hdg he
        exact (K.offD e her).1 (hLnd d hdL e he).2
    · intro k hkn
      rw [hcopy k (by omega), children_take]
      congr 1; congr 1
      apply List.map_congr_left
      intro c hc
      rw [List.mem_filter] at hc
      have hcgt := (mem_children hc.1).1
      have hcx : c < j' + L := by simpa using hc.2
      obtain ⟨q', rfl⟩ : ∃ q', c = j' + q' := ⟨c - j', by omega⟩
      simp only [Function.comp]
      rw [shk_B, (K.σB _ (by omega) (by
        rw [hlN]; have : k * L + L ≤ n * L := by
          have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this
          exact this
        omega)).1, tau_o_mid hkn (by omega) (by omega)]
    · rw [hcopy (n - 1) (by omega), children_take]
      congr 1; congr 1
      apply List.map_congr_left
      intro c hc
      rw [List.mem_filter] at hc
      have hcgt := (mem_children hc.1).1
      have hcx : c < j' + L := by simpa using hc.2
      obtain ⟨q', rfl⟩ : ∃ q', c = j' + q' := ⟨c - j', by omega⟩
      simp only [Function.comp]
      rw [shk_B, (K.σB _ (by omega) (by rw [hlN]; omega)).1, tau_o_last (by omega)]
    · exact single_omega hG0'ot
    · exact hT1M
    · exact omega_le_omega hG0'ot hG0ot (g0le_of_po I.good K.GT hdrop)
    · rw [par1_pre0 hlen hL hp hn hgr]
      cases hpp : par M 1 g with
      | none => rfl
      | some m =>
        have := par_lt M 1 g m hpp
        exact (K.offD m (by omega)).2 (hpnd m hpp)

/-- **The sum-level fact from `O′ ⊴ O`** (`O = ψ_s(b′)`, `X = ψ_s(b′ + 1)`). -/
theorem lhd_sum_of_lhdE {s b' O' : T} (h : LhdE O' (psi s b' z)) :
    Lhd z (app (psi s b' z) O') (psi s (app b' one) z) := by
  have h1 : LhdE (app (psi s b' z) O') (mulT (psi s b' z) 2) := by
    rw [mulT_succ']
    have e : mulT (psi s b' z) 1 = psi s b' z := by simp [mulT, app_z_right]
    rw [e]; exact lhdE_app _ h
  have h2 : Lhd z (mulT (psi s b' z) 2) (psi s (app b' one) z) := lhd_mulT 2
  exact lhd_of_lhdE_lt (LhdE.trans h1 (Or.inr h2)) (lt_of_le_of_lt h1.le h2.1)

/-- **Residual: the hard seeds of a `Bad2` matrix at `t = 0`, S2 also at the `M` level** (2026-10-25): S3 as in
`T0BadSeedsH4`; S2 (`r ≠ x − 1`, `r` a bump child of `g`): `ω^{G0′} ⊴ ω^{G0}` or `ω^{G0} + ω^{G0′} ◁ ω^{G0 + 1}`
(`t0_S2_of_sum`); and for `r ≠ x − 1` the first copy root still counts at `g` in `N`. -/
def T0BadSeedsH5 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ g pp, par M 0 r = some g → par M 0 g = some pp → entry M 1 pp ≠ 0 → entry M 2 pp ≠ 0 →
      col M g = bump M pp →
      Lhd z ((drop1 M (r + L) rk).o r) (ρ.o r) ∨
        ∀ w', (drop1 M (r + L) rk).o r = psi w' z z →
          ∀ u, ¬ w' < u → ∀ e ∈ comps u w', ∃ d ∈ z :: comps u (ρ.v r), e ≤ d) ∧
    (∀ g, par M 0 r = some g → r ≠ r + L - 1 → col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 →
      LhdE (omega (sumN ((children (M.take (r + L)) r).map (drop1 M (r + L) rk).o)))
          (omega (sumN ((children (M.take (r + L)) r).map ρ.o))) ∨
        Lhd z (app (omega (sumN ((children (M.take (r + L)) r).map ρ.o)))
          (omega (sumN ((children (M.take (r + L)) r).map (drop1 M (r + L) rk).o))))
          (omega (app (sumN ((children (M.take (r + L)) r).map ρ.o)) one))) ∧
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → ∀ g, par M 0 r = some g →
      r ≠ r + L - 1 → Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g r

theorem t0BadSeedsH4_of (hDU : HDropU) (hBE : HBumpExt) (h5 : T0BadSeedsH5) : T0BadSeedsH4 := by
  intro M ρ rk hM hS hB I r L hlen hL hp he1
  obtain ⟨hS3, hS2M, hcnt⟩ := h5 M ρ rk hM hS hB I r L hlen hL hp he1
  refine ⟨hS3, fun n hn2 σ hCN g hg => ⟨fun hrx => hcnt n hn2 σ hCN g hg hrx, fun hrx hjb h1 h2 => ?_⟩⟩
  have S := sInv_std hM hS
  have IC := I.toC S
  have D := T0DropF.of_U hDU hM hS (by omega) I
  have hG0ot : isOT (sumN ((children (M.take (r + L)) r).map ρ.o)) = true := isOT_sumN _ (fun t ht => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    rw [children_take, List.mem_filter] at hc
    exact I.good.ot_o c (mem_children hc.1).2)
  have hT1M : Lhd z (app (omega (sumN ((children (M.take (r + L)) r).map ρ.o)))
      (omega (sumN ((children (M.take (r + L)) r).map (drop1 M (r + L) rk).o))))
      (omega (app (sumN ((children (M.take (r + L)) r).map ρ.o)) one)) := by
    rcases hS2M g hg hrx hjb h1 h2 with h | h
    · obtain ⟨sO, bO, hOf, hXf⟩ := omega_succ_form hG0ot
      rw [hOf, hXf]; rw [hOf] at h
      exact lhd_sum_of_lhdE h
    · exact h
  exact t0_S2_of_sum IC D hlen hL hp he1 (t0AbsW_of_U hDU hBE hM hS I hlen hp he1) hT1M hn2 hCN g hg hjb h1 h2

end Ytosk
