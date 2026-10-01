/-
**3 行・t = 0: g が P_0(g) = p ののりしろの子のときの v(p) の枠（種 S3）。**

v(p) = V + ω^{1 + P + ω^G}（G は g の子の o の和）。M では g の最後の子は r で、G = K + o_M(r)、
o_M(r) = ψ_v(Y0 + 1)。N ではコピーの根もすべて g の子で、G′ = K + ψ_v(Y0)·(n − 1) + o′(r)
（o′(r) は落とした値で o′(r) ◁ o_M(r)）。
- o′(r) ≤ ψ_v(Y0)（添字 v で引数 ≤ Y0）なので o′(r) ⊴ ψ_v(Y0)（`lhd_restrict`）、
  ψ_v(Y0)·(n − 1) + o′(r) ⊴ ψ_v(Y0)·n ◁ ψ_v(Y0 + 1)（`lhd_mulT`）。G の段は `g3_brel`、
  あとは `v_bump_lhd`。
実測（sro_L8_K3・sro_L9_K4・std3_L8_K3、n = 2, 3）で例外 0。
-/
import Ytosk.V3T0B

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The `G` level of the seed S3**: `K + ψ_v(Y0)·(n − 1) + o′` against `K + ψ_v(Y0 + 1)`, where
`o′ ◁ ψ_v(Y0 + 1)`. -/
theorem g3_brel {Kv : List T} {B0 v o' : T} {n : Nat} (hn : 2 ≤ n)
    (hsK : ∀ u ∈ Kv, Single u) (hpK : (Kv ++ [psi v (app B0 one) z]).Pairwise (fun a b => b ≤ a))
    (hX : Single (psi v (app B0 one) z)) (hO : Single (psi v B0 z)) (ho' : Single o')
    (hl : Lhd z o' (psi v (app B0 one) z)) :
    BRelS (sumN (Kv ++ (List.replicate (n - 1) (psi v B0 z) ++ [o'])))
        (sumN (Kv ++ [psi v (app B0 one) z])) ∧
      sumN (Kv ++ (List.replicate (n - 1) (psi v B0 z) ++ [o'])) < sumN (Kv ++ [psi v (app B0 one) z]) ∧
      isOT (sumN (Kv ++ (List.replicate (n - 1) (psi v B0 z) ++ [o']))) = true := by
  set O := psi v B0 z with hOdef
  set X := psi v (app B0 one) z with hXdef
  have hOX : O < X := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one B0⟩)
  -- `o' ≤ O`
  obtain ⟨_, s', y', ho'f⟩ := id ho'
  have ho'O : o' ≤ O := by
    have h : psi s' y' z < psi v (app B0 one) z := by rw [← ho'f]; exact hl.1
    rw [ho'f, hOdef]
    rcases psi_lt_psi_z_iff.mp h with h1 | ⟨rfl, h2⟩
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h1))
    · have : y' ≤ B0 := (lt_succ_iff (x := B0)).mp h2
      exact psi_le_psi_arg this
  have hlO : LhdE o' O := by
    rcases (le_iff _ _).mp ho'O with h | h
    · exact Or.inr (lhd_restrict hl h (le_of_lt hOX))
    · exact Or.inl h
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
  have hT : Lhd z (app (mulT O (n - 1)) o') X := by
    have h1 : LhdE (app (mulT O (n - 1)) o') (mulT O n) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [mulT_succ', show m + 1 - 1 = m by omega]
      exact lhdE_app _ hlO
    have h2 : Lhd z (mulT O n) X := by rw [hOdef, hXdef]; exact lhd_mulT n
    exact lhd_of_lhdE_lt (LhdE.trans h1 (Or.inr h2)) (lt_of_le_of_lt h1.le h2.1)
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
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : Good3 (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

/-- **Seed S3**: when `g = P_0(r)` is a bump child of its parent `p` (rows 1 and 2 of `p` nonzero),
`v(p)` drops by `◁` in `N`. -/
theorem t0_S3 {g p : Nat} (hg : par M 0 r = some g) (hpg : par M 0 g = some p)
    (hjb : col M g = bump M p) (h1 : entry M 1 p ≠ 0) (h2 : entry M 2 p ≠ 0)
    (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ) (hAbs : BumpAbsC M (r + L) ρ)
    {Lb : List Nat} (hchp : children M p = Lb ++ [g])
    (hbL : ∀ d ∈ Lb, bumpTerm (TRIO.gexp M r L 0 0 n) σ p d = bumpTerm M ρ p d)
    (hKv : ∀ d ∈ children M g, d < r → σ.o d = ρ.o d)
    {B0 : T} (hor : ρ.o r = psi (ρ.v r) (app B0 one) z)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = psi (ρ.v r) B0 z)
    (hσlast : Lhd z (σ.o (r + (n - 1) * L)) (ρ.o r))
    (hV : vOpt σ (par (TRIO.gexp M r L 0 0 n) 1 p) = vOpt ρ (par M 1 p)) :
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
    exact single_o hCN hGN (by rw [hlN]; omega)
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
  rw [hor] at hdec hX hσlast hbjM
  have hnl : (n - 1) * L + L ≤ n * L := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right L (by omega)
  have hlastN : r + (n - 1) * L < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  obtain ⟨hS, hlt, hG'ot⟩ := g3_brel hn2 hsK hdec hX hO (single_o hCN hGN hlastN) hσlast
  have hGot : isOT (sumN (F.map ρ.o ++ [psi (ρ.v r) (app B0 one) z])) = true := isOT_sumN _ (fun u hu => by
    rcases List.mem_append.mp hu with h | h
    · exact (hsK u h).1
    · simp at h; rw [h]; exact hX.1)
  exact v_bump_lhd hC hG hCN hpM hpN h1 h2 (entry_pre0 hlen hn 1 (by omega))
    (entry_pre0 hlen hn 2 (by omega)) hV hchp hchN hbL hbjM hbjN hGot hG'ot hS hlt hTD
    (hAbs p h1 h2 (fun _ _ _ _ => v_z_of_e1 hC (by omega) he1))

end

end Ytosk
