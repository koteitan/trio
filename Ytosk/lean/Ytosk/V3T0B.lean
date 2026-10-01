/-
**3 行・t = 0: g の v の枠（種 S2）。**

r が g ののりしろの子（g の行 1・2 が 0 でない）のとき、v(g) = V + ω^{1 + P + ω^G}（G は r の子の和）。
N ではコピーの根もすべて g ののりしろの子で、その子の和はどれも G0（x を除いた r の子の和、
最後のコピーでも同じ値であることを仮定に置く。実測で例外 0）。M では r の子の和は G0 + 1（x の値 1）。
- ω^{G0} = ψ_s(b′) なら ω^{G0+1} = ψ_s(b′ + 1)（`omega_succ_form`）。
- ψ_s(b′) を n 個 ◁ ψ_s(b′ + 1)（`lhd_mulT`）、和の段は `s2_p`、あとは ω と加法（`v_strong`）。
-/
import Ytosk.V3T0F

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem app_one_lt_E0 : ∀ {G : T}, G < E0 → app G one < E0
  | z, _ => one_lt_E0
  | psi s b c, h => by
    rw [app_psi]
    exact lt_E0_iff.mpr (lt_E0_iff.mp h)

/-- **`ω^{G+1}` has the same subscript as `ω^G` and the argument plus one.** -/
theorem omega_succ_form {G : T} (hG : isOT G = true) :
    ∃ s b', omega G = psi s b' z ∧ omega (app G one) = psi s (app b' one) z := by
  by_cases hE : G < E0
  · exact ⟨z, G, omega_small hE, omega_small (app_one_lt_E0 hE)⟩
  · cases G with
    | z => exact absurd (T.z_lt_psi _ _ _) hE
    | psi s b c =>
      have hG1 : isOT (psi s b (app c one)) = true := by
        have := isOT_succ hG; simpa [succ] using this
      have hE1 : ¬ psi s b (app c one) < E0 := fun h => hE (lt_E0_rest h)
      refine ⟨s, _, omega_big hG hE, ?_⟩
      rw [app_psi, omega_big hG1 hE1]
      congr 1
      split_ifs with h
      · rw [app_assoc']
      · rw [app_assoc', app_psi]

theorem app_one_lt_Om : ∀ {b : T}, b < Om one → app b one < Om one
  | z, _ => by show psi z z z < psi (psi z z z) z z; rw [psi_lt_psi]; exact Or.inl (T.z_lt_psi _ _ _)
  | psi s c d, h => by
    unfold Om at h ⊢
    rw [app_psi, psi_lt_psi]
    rw [psi_lt_psi] at h
    rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩
    · exact Or.inl h
    · exact absurd h (T.not_lt_z _)
    · exact absurd h (T.not_lt_z _)

/-- **The `p` level of the `g` frame** (`t = 0`): `1 + P + ψ_s(b′)·n` against `1 + P + ψ_s(b′ + 1)`. -/
theorem s2_p {Pl : List T} {O X : T} {n : Nat} (hn : 1 ≤ n)
    (hsP : ∀ q ∈ Pl, Single q) (hpP : Pl.Pairwise (fun a b => b ≤ a)) (hPt : ∀ q ∈ Pl, X ≤ q)
    (hO : Single O) (hX : Single X) (hOX : O < X)
    (hlm : ∀ k, Lhd z (mulT O k) X)
    (hsh : ∃ s b', O = psi s b' z ∧ X = psi s (app b' one) z) :
    BRelS (sumN (one :: Pl ++ List.replicate n O)) (sumN (one :: Pl ++ [X])) ∧
      sumN (one :: Pl ++ List.replicate n O) < sumN (one :: Pl ++ [X]) := by
  obtain ⟨s, b', rfl, rfl⟩ := hsh
  have hone : one < psi s (app b' one) z := by
    unfold one; rw [psi_lt_psi]
    rcases lt_or_ge z s with h | h
    · exact Or.inl h
    · have hs : s = z := le_antisymm h (z_le _)
      subst hs
      exact Or.inr (Or.inl ⟨rfl, lt_of_le_of_lt (z_le b') (lt_app_one b')⟩)
  cases Pl with
  | nil =>
    simp only [List.cons_append, List.nil_append]
    rw [onep_self hX hone]
    obtain ⟨k, hk1, hk⟩ : ∃ k, 1 ≤ k ∧ sumN (one :: List.replicate n (psi s b' z)) = mulT (psi s b' z) k := by
      by_cases hO1 : one < psi s b' z
      · refine ⟨n, hn, ?_⟩
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        rw [List.replicate_succ, sumN_one_cons_gt hO hO1, ← List.replicate_succ, sumN_replicate hO]
      · have hO1' : psi s b' z = one := (onep_two hO hO1).1
        refine ⟨n + 1, by omega, ?_⟩
        rw [show one :: List.replicate n (psi s b' z) = List.replicate (n + 1) (psi s b' z) by
          rw [List.replicate_succ, hO1'], sumN_replicate hO]
    rw [hk]
    refine ⟨?_, (hlm k).1⟩
    by_cases hE : psi s (app b' one) z < E0
    · exact Or.inl ⟨Or.inr (hlm k), hE⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      refine Or.inr (Or.inl ⟨Or.inr (hlm _), ?_, s, b', mulT (psi s b' z) k', app b' one, z, ?_, rfl⟩)
      · intro hlt
        simp only [mulT, app_psi, app_z] at hlt
        obtain ⟨hs, hb⟩ := lt_E0_iff.mp hlt
        exact hE (lt_E0_iff.mpr ⟨hs, app_one_lt_Om hb⟩)
      · simp [mulT]
  | cons q Pr =>
    have hq := hsP q (by simp)
    have hq1 : one < q := lt_of_lt_of_le hone (hPt q (by simp))
    simp only [List.cons_append]
    rw [sumN_one_cons_gt hq hq1, sumN_one_cons_gt hq hq1, ← List.cons_append, ← List.cons_append]
    have hall : ∀ t ∈ (q :: Pr) ++ [psi s (app b' one) z], Single t := fun t ht => by
      rcases List.mem_append.mp ht with h | h
      · exact hsP t h
      · simp at h; rw [h]; exact hX
    have hpall : ((q :: Pr) ++ [psi s (app b' one) z]).Pairwise (fun a b => b ≤ a) :=
      List.pairwise_append.mpr ⟨hpP, by simp, fun a ha b hb => by simp at hb; rw [hb]; exact hPt a ha⟩
    have hall' : ∀ t ∈ (q :: Pr) ++ List.replicate n (psi s b' z), Single t := fun t ht => by
      rcases List.mem_append.mp ht with h | h
      · exact hsP t h
      · rw [(List.mem_replicate.mp h).2]; exact hO
    have hpall' : ((q :: Pr) ++ List.replicate n (psi s b' z)).Pairwise (fun a b => b ≤ a) :=
      List.pairwise_append.mpr ⟨hpP, List.pairwise_replicate.mpr (Or.inr (le_refl _)),
        fun a ha b hb => by rw [(List.mem_replicate.mp hb).2]; exact le_trans (le_of_lt hOX) (hPt a ha)⟩
    rw [sumN_append_dec hall hpall, sumN_append_dec hall' hpall', sumN_replicate hO,
      sumN_singleton hX]
    have hS : sumN (q :: Pr) ≠ z := sumN_ne_z hsP hpP (by simp)
    refine ⟨?_, app_lt_app_left _ (hlm n).1⟩
    have := brelS_app_same hS (Or.inr (hlm n)) z
    simpa using this

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : Good3 (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

/-- **Seed S2**: when `r` is a bump child of its parent `g` (rows 1 and 2 of `g` nonzero), `v(g)`
drops by `◁` in `N`. -/
theorem t0_S2 {g : Nat} (hg : par M 0 r = some g) (hjb : col M r = bump M g)
    (h1 : entry M 1 g ≠ 0) (h2 : entry M 2 g ≠ 0)
    (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ)
    (hbF : ∀ d, d ∈ children M g → d < r →
      bumpTerm (TRIO.gexp M r L 0 0 n) σ g d = bumpTerm M ρ g d)
    (hbroot : ∀ k, k < n → bumpTerm (TRIO.gexp M r L 0 0 n) σ g (r + k * L) =
      omega (sumN ((children (M.take (r + L)) r).map ρ.o)))
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
      o_x_one hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN, sumN_snoc,
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
      Lb ++ List.replicate n O := by
    rw [hchN, List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro d hd
      have := List.mem_filter.mp hd
      exact hbF d this.1 (by simpa using this.2)
    · rw [List.eq_replicate_iff]
      refine ⟨by simp, fun b hb => ?_⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
      exact hbroot k (List.mem_range.mp hk)
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
  obtain ⟨hS, hlt⟩ := s2_p (by omega : 1 ≤ n) hsP hpP hPt hO hX hOX hlm
    ⟨sO, bO, hOf, hXf⟩
  have hPot : ∀ t ∈ one :: Pl, isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · exact (hsP t ht).1
  have hp'ot : isOT (sumN (one :: Pl ++ List.replicate n O)) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPot t h
    · rw [(List.mem_replicate.mp h).2]; exact hO.1)
  have hpot : isOT (sumN (one :: Pl ++ [X])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPot t h
    · simp at h; rw [h]; exact hX.1)
  have ev : ρ.v g = add V (omega (sumN (one :: Pl ++ [X]))) := by
    rw [(hC g hgM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, hmapM, hnzT [X] (by simp [hX]),
      sf_ot (isOT_add hVot (isOT_omega hpot))]
  have ev' : σ.v g = add V (omega (sumN (one :: Pl ++ List.replicate n O))) := by
    rw [(hCN g hgN).2]; unfold vRhs
    rw [entry_pre0 hlen hn 1 (by omega), entry_pre0 hlen hn 2 (by omega), if_neg h1, if_neg h2, hV,
      hmapN, hnzT (List.replicate n O) (fun t ht => by rw [(List.mem_replicate.mp ht).2]; exact hO),
      sf_ot (isOT_add hVot (isOT_omega hp'ot))]
  have hW := brelS_lhdE (brelS_omega hp'ot hpot hS)
  have hbW : bumpW M ρ g = omega (sumN (one :: Pl ++ [X])) := by
    unfold bumpW; rw [hmapM, hnzT [X] (by simp [hX])]
  have hE : LhdE (σ.v g) (ρ.v g) := by
    rw [ev', ev]
    apply v_strong hVot (single_omega hp'ot) (single_omega hpot) hW
    intro q hq hn' hlt'
    by_cases hWE : omega (sumN (one :: Pl ++ [X])) < E0
    · exact lhd_lt_small (isOT_mem_summands hVot hq) hWE hlt'
    · rw [← hbW]
      apply hAbs g h1 h2 (fun _ _ _ _ => v_z_of_e1 hC (by omega) he1) q hq _ (by rw [hbW]; exact hlt')
      intro hq2
      apply hn'
      have h2le : two ≤ sumN (one :: Pl ++ List.replicate n O) :=
        two_le_sumN_one_cons (by simp; omega) (fun t ht => by
          rcases List.mem_append.mp ht with h | h
          · exact hsP t h
          · rw [(List.mem_replicate.mp h).2]; exact hO)
      have hom : psi z two z ≤ omega (sumN (one :: Pl ++ List.replicate n O)) := by
        rw [← omega_small two_lt_E0]
        rcases (le_iff _ _).mp h2le with h' | h'
        · exact le_of_lt (omega_lt_omega isOT_two hp'ot h')
        · rw [h']
      exact lt_of_lt_of_le hq2 hom
  apply lhd_of_lhdE_lt hE
  rw [ev', ev]
  exact add_lt_add_left _ (omega_lt_omega hp'ot hpot hlt)

end

end Ytosk
