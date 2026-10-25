/-
**種 S3 の弱い最後の項の版（2026-10-25、Bad2・t = 0 の r = x − 1 用）。**

旧の `t0_S3` は最後の写しの根の値 `o′(r) ◁ o(r)` を仮定していた（hlB）。Bad2 の r = x − 1 ではこれが偽。代わりに
和の段の `omid + o′(r) ◁ o(r)`（m = 1）を仮定する: 写しが増えても成分の集合は同じで検査の範囲が狭まるだけなので、
`m ≥ 1` のすべてで `omid·m + o′(r) ◁ o(r)`（`lhd_mulT_mono`）。
-/
import Ytosk.V3T0BadNode

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem comps_mulT_sub (u O : T) : ∀ k, ∀ g ∈ comps u (mulT O k), g ∈ comps u O
  | 0, g, hg => by simp [mulT, comps] at hg
  | k + 1, g, hg => by
    rw [show mulT O (k + 1) = app O (mulT O k) from rfl, comps_app] at hg
    rcases List.mem_append.mp hg with h | h
    · exact h
    · exact comps_mulT_sub u O k g h

/-- **More copies keep `◁`**: from `O + o′ ◁ X` (`O = ψ_v(B0)`, `X = ψ_v(B0 + 1)`, `o′ ≤ O`) to `O·k + o′ ◁ X`. -/
theorem lhd_mulT_mono {v B0 o' : T} (hT1 : Lhd z (app (psi v B0 z) o') (psi v (app B0 one) z))
    (ho' : o' ≤ psi v B0 z) (hof : ∃ s y, o' = psi s y z) :
    ∀ k, 1 ≤ k → Lhd z (app (mulT (psi v B0 z) k) o') (psi v (app B0 one) z) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨s, y, rfl⟩ := hof
  have hsum : ∀ q ∈ summands (mulT (psi v B0 z) j), psi s y z ≤ q := fun q hq => by
    rw [summands_mulT ⟨_, _, rfl⟩ j q hq]; exact ho'
  have hge : app (psi v B0 z) (psi s y z) ≤ app (mulT (psi v B0 z) (j + 1)) (psi s y z) := by
    rw [show mulT (psi v B0 z) (j + 1) = app (psi v B0 z) (mulT (psi v B0 z) j) from rfl, app_assoc]
    exact app_le_app_left _ (le_app_of_ge _ hsum)
  refine ⟨?_, fun u c h1 h2 g hg => ?_⟩
  · refine lt_of_le_of_lt (app_le_app_left _ ho') ?_
    rw [← mulT_succ']
    exact (lhd_mulT (η := z) (j + 2)).1
  · rw [comps_app] at hg
    apply hT1.2 u c (lt_of_le_of_lt hge h1) h2 g
    rw [comps_app]
    rcases List.mem_append.mp hg with h | h
    · exact List.mem_append_left _ (comps_mulT_sub u _ _ g h)
    · exact List.mem_append_right _ h

/-- **The `G` level of seed S3 with a weak last summand** (as `g3_brel`, from `O + o′ ◁ X`). -/
theorem g3_brelW {Kv : List T} {B0 v o' : T} {n : Nat} (hn : 2 ≤ n)
    (hsK : ∀ u ∈ Kv, Single u) (hpK : (Kv ++ [psi v (app B0 one) z]).Pairwise (fun a b => b ≤ a))
    (hX : Single (psi v (app B0 one) z)) (hO : Single (psi v B0 z)) (ho' : Single o')
    (hT1 : Lhd z (app (psi v B0 z) o') (psi v (app B0 one) z)) (ho'O : o' ≤ psi v B0 z) :
    BRelS (sumN (Kv ++ (List.replicate (n - 1) (psi v B0 z) ++ [o'])))
        (sumN (Kv ++ [psi v (app B0 one) z])) ∧
      sumN (Kv ++ (List.replicate (n - 1) (psi v B0 z) ++ [o'])) < sumN (Kv ++ [psi v (app B0 one) z]) ∧
      isOT (sumN (Kv ++ (List.replicate (n - 1) (psi v B0 z) ++ [o']))) = true := by
  set O := psi v B0 z with hOdef
  set X := psi v (app B0 one) z with hXdef
  have hOX : O < X := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one B0⟩)
  -- the tail
  have hRs : ∀ t ∈ List.replicate (n - 1) O ++ [o'], Single t := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · rw [(List.mem_replicate.mp h).2]; exact hO
    · simp at h; rw [h]; exact ho'
  have hRp : (List.replicate (n - 1) O ++ [o']).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_append.mpr ⟨List.pairwise_replicate.mpr (Or.inr (le_refl _)), by simp,
      fun a ha b hb => by
        simp at hb; rw [hb, (List.mem_replicate.mp ha).2]; exact ho'O⟩
  have hsumR : sumN (List.replicate (n - 1) O ++ [o']) = app (mulT O (n - 1)) o' := by
    rw [sumN_snoc_dec hRs hRp, sumN_replicate hO]
  have hT : Lhd z (app (mulT O (n - 1)) o') X :=
    lhd_mulT_mono hT1 ho'O (by obtain ⟨_, s', y', h⟩ := ho'; exact ⟨s', y', h⟩) (n - 1) (by omega)
  have hpK1 := List.pairwise_append.mp hpK
  have hKX : ∀ u ∈ Kv, X ≤ u := fun u hu => hpK1.2.2 u hu X (by simp)
  have hall : ∀ t ∈ Kv ++ (List.replicate (n - 1) O ++ [o']), Single t := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hsK t h
    · exact hRs t h
  have hpall : (Kv ++ (List.replicate (n - 1) O ++ [o'])).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_append.mpr ⟨hpK1.1, hRp, fun a ha b hb => by
      have hb' : b ≤ O := by
        rcases List.mem_append.mp hb with h | h
        · rw [(List.mem_replicate.mp h).2]
        · simp at h; rw [h]; exact ho'O
      exact le_trans hb' (le_trans (le_of_lt hOX) (hKX a ha))⟩
  have hallX : ∀ t ∈ Kv ++ [X], Single t := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hsK t h
    · simp at h; rw [h]; exact hX
  have hot : isOT (sumN (Kv ++ (List.replicate (n - 1) O ++ [o']))) = true :=
    isOT_sumN _ (fun t ht => (hall t ht).1)
  rw [sumN_append_dec hall hpall, sumN_append_dec hallX hpK, hsumR, sumN_singleton hX] at *
  refine ⟨?_, app_lt_app_left _ hT.1, hot⟩
  by_cases hK : Kv = []
  · subst hK
    simp only [sumN_nil, app_z]
    by_cases hE : X < E0
    · exact Or.inl ⟨Or.inr hT, hE⟩
    · obtain ⟨m, hm⟩ : ∃ m, n - 1 = m + 1 := ⟨n - 2, by omega⟩
      have hTf : app (mulT O (n - 1)) o' = psi v B0 (app (mulT O m) o') := by
        rw [hm, show mulT O (m + 1) = app O (mulT O m) from rfl, app_assoc, hOdef, app_psi, app_z]
      rw [hTf] at hT ⊢
      refine Or.inr (Or.inl ⟨Or.inr hT, ?_, v, B0, app (mulT O m) o', app B0 one, z, rfl, rfl⟩)
      intro hlt
      obtain ⟨hv, hb⟩ := lt_E0_iff.mp hlt
      exact hE (lt_E0_iff.mpr ⟨hv, app_one_lt_Om hb⟩)
  · have hS : sumN Kv ≠ z := sumN_ne_z hsK hpK1.1 hK
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

/-- **Seed S3 with a weak last copy** (as `t0_S3`, from `omid + o′(r) ◁ o(r)`). -/
theorem t0_S3W {g p : Nat} (hg : par M 0 r = some g) (hpg : par M 0 g = some p)
    (hjb : col M g = bump M p) (h1 : entry M 1 p ≠ 0) (h2 : entry M 2 p ≠ 0)
    (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ) (hAbs : AbsWN M (TRIO.gexp M r L 0 0 n) r ρ σ)
    {Lb : List Nat} (hchp : children M p = Lb ++ [g])
    (hbL : ∀ d ∈ Lb, bumpTerm (TRIO.gexp M r L 0 0 n) σ p d = bumpTerm M ρ p d)
    (hKv : ∀ d ∈ children M g, d < r → σ.o d = ρ.o d)
    {B0 : T} (hor : ρ.o r = psi (ρ.v r) (app B0 one) z)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = psi (ρ.v r) B0 z)
    (hT1 : Lhd z (app (psi (ρ.v r) B0 z) (σ.o (r + (n - 1) * L))) (ρ.o r))
    (hlo : σ.o (r + (n - 1) * L) ≤ psi (ρ.v r) B0 z)
    (hV : vOpt σ (par (TRIO.gexp M r L 0 0 n) 1 p) = vOpt ρ (par M 1 p))
    (hOTr : ∀ k, k < n → isOT (σ.o (r + k * L)) = true) :
    Lhd z (σ.v p) (ρ.v p) := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hgr : g < r := par_lt M 0 r g hg
  have hpgl : p < g := par_lt M 0 g p hpg
  have hpM : p < M.length := by omega
  have hpN : p < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hgp : g ∈ children M p := mem_children_iff.mpr ⟨by omega, hpg⟩
  have hrp : par M 0 r ≠ some p := by rw [hg]; intro h; cases h; omega
  have hchN : children (TRIO.gexp M r L 0 0 n) p = Lb ++ [g] := by
    rw [children_pre0 hlen hL hp hn (by omega) hrp, hchp]
  -- the children of `g`
  set F := (children M g).filter (fun d => decide (d < r)) with hFdef
  have hchM : children M g = F ++ [r] := children_g_last hlen hL hp hg
  have hchgN : children (TRIO.gexp M r L 0 0 n) g =
      F ++ (r :: (List.range (n - 1)).map (fun k => r + (k + 1) * L)) := by
    rw [children_g0 hlen hL hp hn hg, hchM, List.append_assoc]; rfl
  set O := psi (ρ.v r) B0 z with hOdef
  have hrN : r < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hO : Single O := by
    rw [← show σ.o (r + 0 * L) = O from hσmid 0 (by omega)]
    exact ⟨hOTr 0 (by omega), o_psi_form hCN (by rw [hlN]; omega)⟩
  have hmapN : (r :: (List.range (n - 1)).map (fun k => r + (k + 1) * L)).map σ.o =
      List.replicate (n - 1) O ++ [σ.o (r + (n - 1) * L)] := by
    obtain ⟨m, hm⟩ : ∃ m, n - 1 = m + 1 := ⟨n - 2, by omega⟩
    have hl : (r :: (List.range (n - 1)).map (fun k => r + (k + 1) * L)) =
        (List.range n).map (fun k => r + k * L) := by
      rw [show n = (n - 1) + 1 by omega, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.zero_mul, Nat.add_zero, Nat.add_sub_cancel]
      rfl
    rw [hl, show n = (n - 1) + 1 by omega, List.range_succ, List.map_append, List.map_append,
      Nat.add_sub_cancel]
    congr 1
    rw [List.map_map, List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
    exact hσmid k (by have := List.mem_range.mp hk; omega)
  have hFv : F.map σ.o = F.map ρ.o := List.map_congr_left (fun d hd => by
    have := List.mem_filter.mp hd
    exact hKv d this.1 (by simpa using this.2))
  have hbjM : bumpTerm M ρ p g = omega (sumN (F.map ρ.o ++ [ρ.o r])) := by
    unfold bumpTerm; rw [if_pos hjb, hchM, List.map_append, List.map_singleton]
  have hbjN : bumpTerm (TRIO.gexp M r L 0 0 n) σ p g =
      omega (sumN (F.map ρ.o ++ (List.replicate (n - 1) O ++ [σ.o (r + (n - 1) * L)]))) := by
    unfold bumpTerm
    rw [if_pos (by rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]; exact hjb),
      hchgN, List.map_append, hmapN, hFv]
  -- the `G` level
  have hdec := hKD p h1 h2 g hgp hjb
  rw [hchM, List.map_append, List.map_singleton] at hdec
  have hsK : ∀ u ∈ F.map ρ.o, Single u := fun u hu => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
    exact single_o hC hG (by have := (mem_children (List.mem_filter.mp hd).1).2; exact this)
  have hX : Single (ρ.o r) := single_o hC hG (by omega)
  rw [hor] at hdec hX hT1 hbjM
  have hnl : (n - 1) * L + L ≤ n * L := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right L (by omega)
  have hlastN : r + (n - 1) * L < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  obtain ⟨hS, hlt, hG'ot⟩ := g3_brelW hn2 hsK hdec hX hO ⟨hOTr (n - 1) (by omega), o_psi_form hCN hlastN⟩ hT1 hlo
  have hGot : isOT (sumN (F.map ρ.o ++ [psi (ρ.v r) (app B0 one) z])) = true := isOT_sumN _ (fun u hu => by
    rcases List.mem_append.mp hu with h | h
    · exact (hsK u h).1
    · simp at h; rw [h]; exact hX.1)
  exact v_bump_lhdW hC hG hCN hpM hpN h1 h2 (entry_pre0 hlen hn 1 (by omega))
    (entry_pre0 hlen hn 2 (by omega)) hV hchp hchN hbL hbjM hbjN hGot hG'ot hS hlt hTD
    (hAbs p (lt_trans (par_lt M 0 g p hpg) (par_lt M 0 r g hg)) h1 h2)

end

/-- **Seed S3 from the sum-level fact `omid + o′(r) ◁ o(r)`** (any `r`; `t0_S3W`). -/
theorem t0_S3_of_sum {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (I : Inv3C M ρ rk) (D : T0DropF M ρ rk) (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0) (hAbW : T0AbsW M r L ρ)
    (hT1M : Lhd z (app (omid M r L ρ) ((drop1 M (r + L) rk).o r)) (ρ.o r))
    {n : Nat} (hn2 : 2 ≤ n) {σ : Valn} (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) :
    ∀ g, par M 0 r = some g → ∀ pp, par M 0 g = some pp → entry M 1 pp ≠ 0 → entry M 2 pp ≠ 0 →
      col M g = bump M pp → Lhd z (σ.v pp) (ρ.v pp) := by
  have K := t0NCtx_of I D hlen hL hp he1 hn2 hCN
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hDr : DepX M (r + L) true r := depLike_r hlen hL hp hx2 (depLike_depX M (r + L))
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good
  intro g hg pp hpg h1 h2 hjb
  have hgr : g < r := par_lt M 0 r g hg
  have hrc : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
  have hppg := par_lt M 0 g pp hpg
  have hgp : g ∈ children M pp := mem_children_iff.mpr ⟨by omega, hpg⟩
  have hpD : DepX M (r + L) false pp := DepX.vbump h1 h2 hgp hjb hrc hDr
  obtain ⟨_, hpnd, hcase⟩ := dv_shape hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp (by omega) hpD
  rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j', k', hch, _, hchj, _, hKnd, hLnd⟩
  · exact absurd h2' h2
  · have hjg : j' = g := by
      by_contra hne
      have hgL : g ∈ Lb := by
        rw [hch] at hgp
        rcases List.mem_append.mp hgp with h | h
        · exact h
        · simp at h; exact absurd h.symm hne
      exact (hLnd g hgL r hrc).2 hDr
    subst hjg
    have hkr : k' = r := by
      have hchM := children_g_last hlen hL hp hg
      rw [hchj] at hchM
      have := congrArg List.getLast? hchM
      simpa using this
    rw [hkr] at hchj
    have hLj : ∀ d ∈ Lb, d < j' :=
      (sib_order (children_sorted M pp) (R := []) (by rw [hch])).1
    apply t0_S3W hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hg hpg hjb h1 h2
      I.td I.kd (hAbW n hn2 σ hCN) hch
    · intro d hd
      have hdg : par M 0 r ≠ some d := fun h =>
        (hLnd d hd r (mem_children_iff.mpr ⟨by have := hLj d hd; omega, h⟩)).2 hDr
      have hdj := hLj d hd
      apply bumpTerm_eq_of
      · rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
      · intro _
        rw [children_pre0 hlen hL hp hn (by omega) hdg]
        apply List.map_congr_left
        intro e he
        have her := children_lt_r hlen hL hp (by omega) hdg he
        exact (K.offD e her).1 (hLnd d hd e he).2
    · intro d hd hdr
      have hdK : d ∈ Kb := by
        rw [hchj] at hd
        rcases List.mem_append.mp hd with h | h
        · exact h
        · simp at h; omega
      exact (K.offD d hdr).1 (hKnd d hdK)
    · exact hor
    · intro k hk; rw [K.σmid k hk, hom]
    · rw [K.σlast, ← hom]; exact hT1M
    · rw [K.σlast, ← hom]; exact K.le
    · rw [par1_pre0 hlen hL hp hn (by omega)]
      cases hpp : par M 1 pp with
      | none => rfl
      | some m =>
        have := par_lt M 1 pp m hpp
        exact (K.offD m (by omega)).2 (hpnd m hpp)
    · intro k hk
      by_cases hkn : k + 1 < n
      · rw [K.σmid k hkn]; exact isOT_omid hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN
      · rw [show k = n - 1 by omega, K.σlast]; exact K.GT.ot_o r (by rw [List.length_take]; omega)

/-- **The sum-level fact from the drop `o′ ◁ X`** (`o′ ≤ O`): `O + o′ ◁ X` (as in `g3_brel`). -/
theorem lhd_sum_of_lhd {v B0 o' : T} (hl : Lhd z o' (psi v (app B0 one) z)) (ho' : o' ≤ psi v B0 z) :
    Lhd z (app (psi v B0 z) o') (psi v (app B0 one) z) := by
  have hOX : psi v B0 z < psi v (app B0 one) z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one B0⟩)
  have hlO : LhdE o' (psi v B0 z) := by
    rcases (le_iff _ _).mp ho' with h | h
    · exact Or.inr (lhd_restrict hl h (le_of_lt hOX))
    · exact Or.inl h
  have h1 : LhdE (app (psi v B0 z) o') (mulT (psi v B0 z) 2) := by
    rw [mulT_succ']
    have e : mulT (psi v B0 z) 1 = psi v B0 z := by simp [mulT, app_z_right]
    rw [e]; exact lhdE_app _ hlO
  have h2 : Lhd z (mulT (psi v B0 z) 2) (psi v (app B0 one) z) := lhd_mulT 2
  exact lhd_of_lhdE_lt (LhdE.trans h1 (Or.inr h2)) (lt_of_le_of_lt h1.le h2.1)

/-- **Residual: the hard seeds of a `Bad2` matrix at `t = 0`, narrowed again** (2026-10-25): for `r ≠ x − 1` the
first copy root still counts at `g` in `N` and S2; for S3 only the `M`-level fact that the drop at `r` is `◁` or the
sum `omid + o′(r) ◁ o(r)` holds (`t0_S3_of_sum`). -/
def T0BadSeedsH3 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ g pp, par M 0 r = some g → par M 0 g = some pp → entry M 1 pp ≠ 0 → entry M 2 pp ≠ 0 →
      col M g = bump M pp →
      Lhd z ((drop1 M (r + L) rk).o r) (ρ.o r) ∨
        Lhd z (app (omid M r L ρ) ((drop1 M (r + L) rk).o r)) (ρ.o r)) ∧
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → ∀ g, par M 0 r = some g →
      (r ≠ r + L - 1 → Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g r) ∧
      (r ≠ r + L - 1 → col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → Lhd z (σ.v g) (ρ.v g))

theorem t0BadSeedsH2_of (hDU : HDropU) (hBE : HBumpExt) (h3 : T0BadSeedsH3) : T0BadSeedsH2 := by
  intro M ρ rk hM hS hB I r L hlen hL hp he1 n hn2 σ hCN g hg
  have S := sInv_std hM hS
  have IC := I.toC S
  have D := T0DropF.of_U hDU hM hS (by omega) I
  obtain ⟨hS3M, hrest⟩ := h3 M ρ rk hM hS hB I r L hlen hL hp he1
  obtain ⟨hc, hs2⟩ := hrest n hn2 σ hCN g hg
  refine ⟨hc, hs2, fun pp hpg h1 h2 hjb => ?_⟩
  have K := t0NCtx_of IC D hlen hL hp he1 hn2 hCN
  have hn : 1 ≤ n := by omega
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 (S.r12 _ he1) hn2
    I.cons I.good
  have hsum : Lhd z (app (omid M r L ρ) ((drop1 M (r + L) rk).o r)) (ρ.o r) := by
    rcases hS3M g pp hg hpg h1 h2 hjb with hl | hl
    · rw [hom, hor]; rw [hor] at hl
      exact lhd_sum_of_lhd hl (by rw [← hom]; exact K.le)
    · exact hl
  exact t0_S3_of_sum IC D hlen hL hp he1 (t0AbsW_of_U hDU hBE hM hS I hlen hp he1) hsum hn2 hCN g hg pp hpg
    h1 h2 hjb

/-- **The sum-level fact with a weak leaf** `ψ_{w′}(0)` (`w′ < v`): `ψ_v(B0) + ψ_{w′}(0) ◁ ψ_v(B0 + 1)` when every
component of `w′` is `0` or below a component of `v` (at every level `u ≤ w′`). -/
theorem lhd_sum_weak {v B0 w' : T} (hB0 : isOT (app B0 one) = true) (hw : w' < v)
    (hdom : ∀ u, ¬ w' < u → ∀ g ∈ comps u w', ∃ d ∈ z :: comps u v, g ≤ d) :
    Lhd z (app (psi v B0 z) (psi w' z z)) (psi v (app B0 one) z) := by
  have hleaf : psi w' z z ≤ psi v B0 z := le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl hw))
  have hbO : psi v B0 z ≤ app (psi v B0 z) (psi w' z z) := le_app_self _ _
  refine ⟨?_, fun u c h1 h2 g hg => ?_⟩
  · refine lt_of_le_of_lt (app_le_app_left _ hleaf) ?_
    have e : app (psi v B0 z) (psi v B0 z) = mulT (psi v B0 z) 2 := by simp [mulT, app_z_right]
    rw [e]; exact (lhd_mulT (η := z) 2).1
  obtain ⟨C, R, rfl, hC1, hC2⟩ := between_psi (lt_of_le_of_lt hbO h1) h2
  have hz : z ∈ comps u (psi v C R) ++ Gc u z := List.mem_append_right _ (by simp [Gc])
  rw [comps_app] at hg
  by_cases hvu : v < u
  · exfalso
    have h1' : lt v u = true := hvu
    have h2' : lt w' u = true := lt_trans hw hvu
    simp [comps, h1', h2'] at hg
  have hc : comps u (psi v C R) = C :: (comps u C ++ comps u v) ++ comps u R := by
    have h' : lt v u = false := by simpa [lt_iff_lt] using hvu
    simp [comps, h']
  have hin : ∀ d, d ∈ C :: (comps u C ++ comps u v) → d ∈ comps u (psi v C R) ++ Gc u z := fun d hd =>
    List.mem_append_left _ (by rw [hc]; exact List.mem_append_left _ hd)
  rw [comps_psi_z_of_ge hvu] at hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨C, hin C List.mem_cons_self, hC1⟩
    rcases List.mem_append.mp hg with hg | hg
    · rcases (le_iff _ _).mp hC1 with hlt | heq
      · obtain ⟨d, hd, hgd⟩ := (lhd_pred_succ hB0).2 u C hlt hC2 g hg
        rcases List.mem_append.mp hd with hd | hd
        · exact ⟨d, hin d (List.mem_cons_of_mem _ (List.mem_append_left _ hd)), hgd⟩
        · exact ⟨d, List.mem_append_right _ hd, hgd⟩
      · subst heq
        exact ⟨g, hin g (List.mem_cons_of_mem _ (List.mem_append_left _ hg)), le_refl _⟩
    · exact ⟨g, hin g (List.mem_cons_of_mem _ (List.mem_append_right _ hg)), le_refl _⟩
  · by_cases hwu : w' < u
    · have h2' : lt w' u = true := hwu
      simp [comps, h2'] at hg
    rw [comps_psi_z_of_ge hwu] at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨z, hz, le_refl _⟩
    have hg' : g ∈ comps u w' := by simpa [comps] using hg
    obtain ⟨d, hd, hgd⟩ := hdom u hwu g hg'
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨z, hz, hgd⟩
    · exact ⟨d, hin d (List.mem_cons_of_mem _ (List.mem_append_right _ hd)), hgd⟩

/-- **Residual: the hard seeds of a `Bad2` matrix at `t = 0`, S3 as a component fact** (2026-10-25): where S3
applies, the drop at `r` is `◁`, or the weak leaf `o′(r) = ψ_{w′}(0)` has every component of `w′` equal to `0` or below
a component of `v(r)` (`lhd_sum_weak`). The other two fields as in `T0BadSeedsH3`. -/
def T0BadSeedsH4 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ g pp, par M 0 r = some g → par M 0 g = some pp → entry M 1 pp ≠ 0 → entry M 2 pp ≠ 0 →
      col M g = bump M pp →
      Lhd z ((drop1 M (r + L) rk).o r) (ρ.o r) ∨
        ∀ w', (drop1 M (r + L) rk).o r = psi w' z z →
          ∀ u, ¬ w' < u → ∀ e ∈ comps u w', ∃ d ∈ z :: comps u (ρ.v r), e ≤ d) ∧
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → ∀ g, par M 0 r = some g →
      (r ≠ r + L - 1 → Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g r) ∧
      (r ≠ r + L - 1 → col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → Lhd z (σ.v g) (ρ.v g))

theorem t0BadSeedsH3_of (hDU : HDropU) (h4 : T0BadSeedsH4) : T0BadSeedsH3 := by
  intro M ρ rk hM hS hB I r L hlen hL hp he1
  obtain ⟨hS3M, hrest⟩ := h4 M ρ rk hM hS hB I r L hlen hL hp he1
  refine ⟨fun g pp hg hpg h1 h2 hjb => ?_, hrest⟩
  rcases hS3M g pp hg hpg h1 h2 hjb with hl | hdom
  · exact Or.inl hl
  have S := sInv_std hM hS
  have IC := I.toC S
  have D := T0DropF.of_U hDU hM hS (by omega) I
  have K := t0NCtx_of IC D hlen hL hp he1 (le_refl 2) (cons_of_rk (rk_N0 hlen hL hp (by omega : 1 ≤ 2)
    S.r0p S.z2 (S.r12 _ he1) (le_refl 2) I.rank))
  have hDP := D.po
  rw [show M.length - 1 = r + L by omega] at hDP
  obtain ⟨hPO, hPV⟩ := hDP r (by omega)
  rcases po_lhd_or_weak I.cons I.good K.C1 (by omega) (by omega) hPO hPV hg K.nz K.lt with hl | ⟨_, w', hw', hWk, -⟩
  · exact Or.inl hl
  right
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp (by omega : 1 ≤ 2) S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1
    (S.r12 _ he1) (le_refl 2) I.cons I.good
  have hot := I.good.ot_o r (by omega)
  rw [hor] at hot ⊢
  rw [hom, hw']
  exact lhd_sum_weak (isOT_arg hot) hWk.1 (hdom w' hw')

end Ytosk
