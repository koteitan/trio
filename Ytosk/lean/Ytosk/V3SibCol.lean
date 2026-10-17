/-
**UpgSibVHard を同じ列の兄弟の値の条件 SibColW に帰着（2026-10-17、lead）。**

`SibColW N τ`: 同じ親の隣り合う子 u < w で col u = col w なら v(w) ≤ v(u)（上げの有無を問わない）。
測定（tmp/lead/probes/sibcolall.py）: std_a・d3s・Cprime の標本で例外 0。

- (i)（col b = col a）は SibColW そのもの。
- (ii)（e1 b < e1 a、e2 b = 0、upg b = b + 1）: g = P_1 b は m = P_0 b の真の祖先。u を g の子で m の祖先
  とすると、b + 1 は g の子で u の次の子（u の部分木は b で終わる）。R1S と P_1 b = g から e1 u = e1 b = e1 g + 1、
  SibDec から e2 u = 1、よって col u = col (b + 1)。v(b) = v(b + 1)（`v_upg_eq`）≤ v(u)（SibColW）
  ≤ v(m)（`v_le_path_anchor`: u から m への道で v は減らない。V3SibV の `key` を取り出したもの）≤ v(a)。
-/
import Ytosk.V3SibV

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Adjacent siblings with the same column**: the later one has at most the `v` of the earlier one. -/
def SibColW (N : Mat) (τ : Valn) : Prop :=
  ∀ p u w, u ∈ children N p → w ∈ children N p → u < w → (∀ e ∈ children N p, u < e → w ≤ e) →
    col N u = col N w → τ.v w ≤ τ.v u

/-- **`v` along the row-0 path from an anchor** (the `key` of `upgSibV_of_hard`): `k` is a child of
`g = P_1 b` with row-1 parent `g` and column `(e0 g + 1, e1 b, e2 g + 1)`, and `m = P_0 b` has `e2 m = 0`.
Every column `j` on the path from `k` to `m` has `v(k) ≤ v(j)`. -/
theorem v_le_path_anchor {N : Mat} {τ : Valn} {rk : Bool → Nat → Nat} (hX : SInvX N) (hJ : RowJ N)
    (hC : Cons N τ) (hR : Rk N rk) (hG : Good3 N τ) {g b m k : Nat}
    (hg : par N 1 b = some g) (hpb : par N 0 b = some m) (hbL : b < N.length) (he2m : entry N 2 m = 0)
    (hpk : par N 0 k = some g) (hp1k : par N 1 k = some g)
    (hcolk : col N k = (entry N 0 g + 1, entry N 1 b, entry N 2 g + 1)) :
    ∀ j, Anc0 N k j → Anc0 N j m → τ.v k ≤ τ.v j := by
  obtain ⟨hAgb, hgb, he1g, hgpath⟩ := par1_facts hg
  have hAmb : Anc0 N m b := anc0_of_par N 0 m b hpb
  have hmb : m < b := par_lt N 0 b m hpb
  have hbC : b ∈ children N m := mem_children_iff.mpr ⟨hbL, hpb⟩
  have hAgk : Anc0 N g k := anc0_of_par N 0 g k hpk
  have hgk := par_lt N 0 k g hpk
  have he1k : entry N 1 k = entry N 1 b := by
    have : entry N 1 k = (col N k).2.1 := by rw [entry_col]
    rw [this, hcolk]
  have he2k' : entry N 2 k = entry N 2 g + 1 := by
    have : entry N 2 k = (col N k).2.2 := by rw [entry_col]
    rw [this, hcolk]
  have he2g : entry N 2 g = 0 := by have := hX.z2 k; omega
  have he0k : entry N 0 k = entry N 0 g + 1 := hX.r0p k g hpk
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hkj hjm
  by_cases hjk : j = k
  · rw [hjk]
  have hgj : Anc0 N g j := hAgk.trans hkj
  have hkjlt : k < j := lt_of_le_of_ne hkj.le (Ne.symm hjk)
  have hjmle := hjm.le
  have hejb : entry N 1 b ≤ entry N 1 j :=
    hgpath j hgj (hjm.trans hAmb) (by omega) (by omega)
  have hjL : j < N.length := by omega
  obtain ⟨x, hx, hgx, hAgx⟩ := par1_near hgj (by omega) (by omega)
  rcases Nat.eq_or_lt_of_le hgx with hxg | hxg
  · -- `P_1 j = g`: row 1 of `j` equals that of `k`
    subst hxg
    have hjpath := (par1_facts hx).2.2.2
    have he1jk : entry N 1 j ≤ entry N 1 k := hjpath k hAgk hkj (by omega) (Ne.symm hjk)
    have he2j : entry N 2 j = 0 ∨ entry N 2 j = 1 := by have := hX.z2 j; omega
    rcases he2j with he2j | he2j
    · -- `j` is upgraded to `k`
      have hj1 : j + 1 < N.length := by
        rcases Nat.eq_or_lt_of_le hjmle with h | h
        · omega
        · omega
      have hAj1 : Anc0 N j (j + 1) := by
        rcases Nat.eq_or_lt_of_le hjmle with h | h
        · rw [h]; exact anc_between hAmb (m + 1) (by omega) (by omega)
        · exact anc_between hjm (j + 1) (by omega) (by omega)
      have he0j1 := anc0_e0_lt hAj1 (by omega)
      have he0kj := anc0_e0_lt hkj (Ne.symm hjk)
      have hujk : upg N j = some k := upg_of_anc_target hj1 (by omega) he2j hx hp1k
        (by rw [hcolk, show entry N 1 b = entry N 1 j by omega]) hkj (Ne.symm hjk) (by omega)
      have := v_upg_eq hC hjL (by omega) he2j hujk (vOpt_ot hG hjL)
        (fun j' _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
      rw [this]
    · -- `e2 j = 1` is impossible
      exfalso
      obtain ⟨x', hpj, hkx'⟩ : ∃ x', par N 0 j = some x' ∧ Anc0 N k x' := by
        cases hkj with
        | refl => exact absurd rfl hjk
        | step hp hA => exact ⟨_, hp, hA⟩
      have hJj := hJ j x' (by omega) hpj
      have he1x' : entry N 1 b ≤ entry N 1 x' := by
        by_cases hx'k : x' = k
        · rw [hx'k]; omega
        · exact hgpath x' (hAgk.trans hkx') ((anc0_of_par N 0 x' j hpj).trans (hjm.trans hAmb))
            (by have := hkx'.le; omega) (by have := par_lt N 0 j x' hpj; omega)
      have he0j := hX.r0p j x' hpj
      have hjb : col N j = bump N x' := by
        rw [entry_col N j]; unfold bump; rw [he0j, he2j, show entry N 1 j = entry N 1 x' by omega]
      have hjc : j ∈ children N x' := mem_children_iff.mpr ⟨hjL, hpj⟩
      have he2x' := hX.toSInv.bumpE2 x' j hjc hjb
      by_cases hx'k : x' = k
      · subst hx'k
        have hjm' : j ≠ m := by intro h; rw [h] at he2j; omega
        obtain ⟨c, hpc, hAcm⟩ := anc0_child hjm hjm'
        have hcL : c < N.length := by have := hAcm.le; omega
        have hcc : c ∈ children N j := mem_children_iff.mpr ⟨hcL, hpc⟩
        have hjc' := par_lt N 0 c j hpc
        have he1c : entry N 1 b ≤ entry N 1 c :=
          hgpath c (hgj.trans (anc0_of_par N 0 j c hpc)) (hAcm.trans hAmb) (by omega)
            (by have := hAcm.le; omega)
        obtain ⟨_, hleaf, _, _⟩ := hX.loc.2.2.2 x' j c hjc hjb hcc (by omega)
        by_cases hcm : c = m
        · rw [hcm] at hleaf; rw [hleaf] at hbC; simp at hbC
        · obtain ⟨c2, hpc2, hAc2m⟩ := anc0_child hAcm hcm
          have : c2 ∈ children N c := mem_children_iff.mpr ⟨by
            have := hAc2m.le; omega, hpc2⟩
          rw [hleaf] at this; simp at this
      · obtain ⟨x'', hpx', hkx''⟩ : ∃ x'', par N 0 x' = some x'' ∧ Anc0 N k x'' := by
          cases hkx' with
          | refl => exact absurd rfl hx'k
          | step hp hA => exact ⟨_, hp, hA⟩
        have hJx' := hJ x' x'' (by omega) hpx'
        have he1x'' : entry N 1 b ≤ entry N 1 x'' := by
          by_cases hx''k : x'' = k
          · rw [hx''k]; omega
          · exact hgpath x'' (hAgk.trans hkx'')
              ((anc0_of_par N 0 x'' x' hpx').trans ((anc0_of_par N 0 x' j hpj).trans (hjm.trans hAmb)))
              (by have := hkx''.le; omega)
              (by have := par_lt N 0 x' x'' hpx'; have := par_lt N 0 j x' hpj; omega)
        have he0x' := hX.r0p x' x'' hpx'
        have hx'b : col N x' = bump N x'' := by
          rw [entry_col N x']; unfold bump
          rw [he0x', he2x', show entry N 1 x' = entry N 1 x'' by omega]
        have hx'c : x' ∈ children N x'' := mem_children_iff.mpr ⟨by
          have := par_lt N 0 j x' hpj; omega, hpx'⟩
        have := (hX.loc.2.2.2 x'' x' j hx'c hx'b hjc (by omega)).1
        omega
  · -- `P_1 j` is below `g`: it is on the path from `k`
    have hAxj : Anc0 N x j := anc0_of_par N 1 x j hx
    have hxj := par_lt N 1 j x hx
    have hkx : k ≤ x := by
      by_contra hlt
      have hAxk : Anc0 N x k := anc_between hAxj k (by omega) hkj.le
      have := (anc0_par hAxk (by omega) hpk).le; omega
    have hAkx : Anc0 N k x := anc_between hkj x hkx hxj.le
    exact le_trans (ih x hxj hAkx (hAxj.trans hjm))
      (le_of_lt (v_par1_lt hC hG hR _ j x (Nat.le_refl _) hjL (by omega) hx))

/-- **`UpgSibVHard` from `SibColW`.** -/
theorem upgSibVHard_of_col {N : Mat} {τ : Valn} {rk : Bool → Nat → Nat} (hX : SInvX N) (hJ : RowJ N)
    (hC : Cons N τ) (hR : Rk N rk) (hG : Good3 N τ) (hW : SibColW N τ) : UpgSibVHard N τ := by
  intro p a b ha hb hab hcons hua _ _ hcase
  rcases hcase with ⟨hcol, _⟩ | ⟨h1, h0, he2b0, hk⟩
  · exact hW p a b ha hb hab hcons hcol.symm
  have hpa : par N 0 a = some p := (mem_children_iff.mp ha).2
  have hpb : par N 0 b = some p := (mem_children_iff.mp hb).2
  have haL := (mem_children ha).2
  have hbL := (mem_children hb).2
  have hpL : p < N.length := by have := (mem_children ha).1; omega
  -- the shape of `a`
  obtain ⟨m, hm1, hm0, he1a, _⟩ := upg_facts hua
  have hmp : m = p := by rw [hpa] at hm0; exact (Option.some.inj hm0).symm
  subst hmp
  obtain ⟨m', hm1', hp1a, hcola, _⟩ := upg_spec hua
  rw [hm1] at hm1'; cases hm1'
  obtain ⟨he1a0, _⟩ := upg_e12 hua
  have he2a' : entry N 2 a = entry N 2 m + 1 := by
    have : entry N 2 a = (col N a).2.2 := by rw [entry_col]
    rw [this, hcola]
  have he2m : entry N 2 m = 0 := by have := hX.z2 a; omega
  have hlt1a : entry N 1 m < entry N 1 a := (par1_facts hp1a).2.2.1
  have he1a0' : entry N 1 a ≠ 0 := by omega
  have hvp := hG.ot_v m hpL
  have hbot : ∀ i j, isOT (bumpTerm N τ i j) = true := fun i j => isOT_bumpTerm hG i j
  have hWot : ∀ i, isOT (sumN (one :: (children N i).map (bumpTerm N τ i))) = true := by
    intro i; apply isOT_sumN; intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact hbot i j
  have hva : τ.v a = add (τ.v m) (omega (sumN (one :: (children N a).map (bumpTerm N τ a)))) := by
    rw [(hC a haL).2]; unfold vRhs; rw [if_neg he1a0', if_neg (by omega), hp1a]
    exact sf_ot (isOT_add hvp (isOT_omega (hWot a)))
  have hma : τ.v m ≤ τ.v a := by rw [hva]; exact le_add_of_single _ (omega_psi_form _)
  -- `g = P_1 b`, a proper ancestor of `m`
  have hR1a := hX.r1s a m hpa
  have he1bm : entry N 1 b ≤ entry N 1 m := by omega
  obtain ⟨g, hg⟩ := par1_exists hX.e00 hX.r01 (show 0 < entry N 1 b by omega)
  obtain ⟨hAgb, hgb, he1g, hgpath⟩ := par1_facts hg
  have hbm : m < b := (mem_children hb).1
  have hgm : g ≠ m := by intro h; rw [h] at he1g; omega
  have hAmb : Anc0 N m b := anc0_of_par N 0 m b hpb
  have hAgm : Anc0 N g m := anc0_par hAgb (by omega) hpb
  -- the target `b + 1`, a child of `g`
  obtain ⟨g', hg', hpk, he1k, _⟩ := upg_facts hk
  rw [hg] at hg'; cases hg'
  obtain ⟨g2, hg2, hp1k, hcolk, _⟩ := upg_spec hk
  rw [hg] at hg2; cases hg2
  have hkL : b + 1 < N.length := upg_succ_lt hk
  have hvbk : τ.v b = τ.v (b + 1) := v_upg_eq hC hbL h0 he2b0 hk (vOpt_ot hG hbL)
    (fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
  -- `u`: the child of `g` above `m`; `b + 1` is the next child of `g`
  obtain ⟨u, hpu, hAum⟩ := anc0_child hAgm hgm
  have hgu := par_lt N 0 u g hpu
  have hum := hAum.le
  have huL : u < N.length := by omega
  have huC : u ∈ children N g := mem_children_iff.mpr ⟨huL, hpu⟩
  have hkC : b + 1 ∈ children N g := mem_children_iff.mpr ⟨hkL, hpk⟩
  have hAub : Anc0 N u b := hAum.trans hAmb
  have hcons' : ∀ e ∈ children N g, u < e → b + 1 ≤ e := by
    intro e he hue
    by_contra hlt
    have hAue : Anc0 N u e := anc_between hAub e hue.le (by omega)
    have hpe := (mem_children_iff.mp he).2
    have := (anc0_par hAue (by omega) hpe).le
    omega
  -- `col u = col (b + 1)`
  have he2k' : entry N 2 (b + 1) = entry N 2 g + 1 := by
    have : entry N 2 (b + 1) = (col N (b + 1)).2.2 := by rw [entry_col]
    rw [this, hcolk]
  have he2g : entry N 2 g = 0 := by have := hX.z2 (b + 1); omega
  have he0u : entry N 0 u = entry N 0 g + 1 := hX.r0p u g hpu
  have he1u1 : entry N 1 u ≤ entry N 1 g + 1 := hX.r1s u g hpu
  have he1k1 : entry N 1 (b + 1) ≤ entry N 1 g + 1 := hX.r1s (b + 1) g hpk
  have he1ub : entry N 1 b ≤ entry N 1 u :=
    hgpath u (anc0_of_par N 0 g u hpu) hAub (by omega) (by omega)
  obtain ⟨l1, l2, hsplit⟩ := consec_split (children_sorted N g) huC hkC (by omega)
    (fun e he ⟨h1', h2'⟩ => by have := hcons' e he h1'; omega)
  have hSD := hX.loc.1 g l1 l2 u (b + 1) hsplit
  unfold colLe at hSD
  rw [hcolk, entry_col N u] at hSD
  simp only at hSD
  have he2u : entry N 2 u = 1 := by have := hX.z2 u; omega
  have hcolu : col N u = col N (b + 1) := by
    rw [hcolk, entry_col N u, he0u, he2u, he2g, show entry N 1 u = entry N 1 b by omega]
  have hku : τ.v (b + 1) ≤ τ.v u := hW g u (b + 1) huC hkC (by omega) hcons' hcolu
  have hp1u : par N 1 u = some g := par1_of_child hpu (by omega)
  have hum' : τ.v u ≤ τ.v m := v_le_path_anchor hX hJ hC hR hG hg hpb hbL he2m hpu hp1u
    (by rw [hcolu, hcolk]) m hAum (Anc0.refl m)
  rw [hvbk]; exact le_trans hku (le_trans hum' hma)

/-- **Two counted adjacent children**: `Good3.dec` gives `o(w) ≤ o(u)`, hence `v(w) ≤ v(u)`. -/
theorem v_le_of_counted_pair {N : Mat} {τ : Valn} (hC : Cons N τ) (hG : Good3 N τ) {p u w : Nat}
    (hu : u ∈ children N p) (hw : w ∈ children N p) (huw : u < w)
    (hcons : ∀ e ∈ children N p, u < e → w ≤ e) (hcu : Counted N p u) (hcw : Counted N p w) :
    τ.v w ≤ τ.v u := by
  have hpL : p < N.length := by have := (mem_children hu).1; have := (mem_children hu).2; omega
  obtain ⟨l1, l2, hsplit⟩ := consec_split (children_sorted N p) hu hw huw
    (fun e he ⟨h1, h2⟩ => by have := hcons e he h1; omega)
  obtain ⟨yu, hyu⟩ := o_form hC hG (mem_children hu).2
  obtain ⟨yw, hyw⟩ := o_form hC hG (mem_children hw).2
  have hcntu : cnt N τ p u = τ.o u := by unfold cnt; rw [if_neg hcu.1, if_neg hcu.2]
  have hcntw : cnt N τ p w = τ.o w := by unfold cnt; rw [if_neg hcw.1, if_neg hcw.2]
  have hd := hG.dec p hpL
  unfold cvals at hd
  rw [hsplit, List.map_append, List.map_cons, List.map_cons, hcntu, hcntw,
    show τ.o u :: τ.o w :: l2.map (cnt N τ p) = [τ.o u] ++ ([τ.o w] ++ l2.map (cnt N τ p)) from rfl,
    nzs_append, nzs_append, nzs_append, nzs_single (by rw [hyu]; simp), nzs_single (by rw [hyw]; simp)] at hd
  have h1 := (List.pairwise_append.mp hd).2.1
  have h2 := (List.pairwise_append.mp h1).2.2 (τ.o u) (by simp) (τ.o w) (by simp)
  have := lev_le_of_le h2
  rw [hyu, hyw] at this
  exact this

/-- A bump child has no bump child (`BumpLeaf`: such a grandchild would have row 2 equal to `0`). -/
theorem bumpTerm_bump_child_z {N : Mat} {τ : Valn} (hX : SInvX N) {p c : Nat} (hc : c ∈ children N p)
    (hcb : col N c = bump N p) : ∀ j ∈ children N c, bumpTerm N τ c j = z := by
  intro j hj
  unfold bumpTerm
  rw [if_neg]
  intro hjb
  have he1c : entry N 1 c = entry N 1 p := by
    have := congrArg (fun q => q.2.1) hcb; simp only [bump] at this; rw [entry_col] at this; exact this
  have he1j : entry N 1 j = entry N 1 c := by
    have := congrArg (fun q => q.2.1) hjb; simp only [bump] at this; rw [entry_col] at this; exact this
  have he2j : entry N 2 j = 1 := by
    have := congrArg (fun q => q.2.2) hjb; simp only [bump] at this; rw [entry_col] at this; exact this
  have := (hX.loc.2.2.2 p c j hc hcb hj (by omega)).1
  omega

/-- `sumN (one :: L) = one` when every term of `L` is `0`. -/
theorem sumN_one_zeros {L : List T} (h : ∀ t ∈ L, t = z) : sumN (one :: L) = sumN [one] := by
  have hot : ∀ t ∈ one :: L, isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · rw [h t ht]; rfl
  rw [sumN_nzs hot, show one :: L = [one] ++ L from rfl, nzs_append, nzs_zeros L h, List.append_nil,
    nzs_single (by simp [one])]

/-- **Two bump children of the same column** have the same `v`. -/
theorem v_bump_sib {N : Mat} {τ : Valn} (hX : SInvX N) (hC : Cons N τ) {p u w : Nat}
    (hu : u ∈ children N p) (hw : w ∈ children N p) (hbu : col N u = bump N p) (hbw : col N w = bump N p) :
    τ.v w = τ.v u := by
  have hpu : par N 0 u = some p := (mem_children_iff.mp hu).2
  have hpw : par N 0 w = some p := (mem_children_iff.mp hw).2
  have e1 : ∀ c, col N c = bump N p → entry N 1 c = entry N 1 p := fun c h => by
    have := congrArg (fun q => q.2.1) h; simp only [bump] at this; rw [entry_col] at this; exact this
  have e2 : ∀ c, col N c = bump N p → entry N 2 c = 1 := fun c h => by
    have := congrArg (fun q => q.2.2) h; simp only [bump] at this; rw [entry_col] at this; exact this
  have hp1 : par N 1 u = par N 1 w := by
    rw [par1_find, par1_find, ancL_eq hpu, ancL_eq hpw, e1 u hbu, e1 w hbw]
  have hsum : ∀ c, c ∈ children N p → col N c = bump N p →
      sumN (one :: (children N c).map (bumpTerm N τ c)) = sumN [one] := fun c hc hcb =>
    sumN_one_zeros (fun t ht => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht; exact bumpTerm_bump_child_z hX hc hcb j hj)
  rw [(hC w (mem_children hw).2).2, (hC u (mem_children hu).2).2]
  unfold vRhs
  rw [e1 u hbu, e1 w hbw, e2 u hbu, e2 w hbw]
  by_cases h0 : entry N 1 p = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0, if_neg one_ne_zero, if_neg one_ne_zero, hp1, hsum u hu hbu, hsum w hw hbw]

/-- **`SibColW` outside two counted children and two bump children** (the residual form): the column is not
the bump column of `p`, and one of `u`, `w` is an upgraded topped child. -/
def SibColU (N : Mat) (τ : Valn) : Prop :=
  ∀ p u w, u ∈ children N p → w ∈ children N p → u < w → (∀ e ∈ children N p, u < e → w ≤ e) →
    col N u = col N w → col N u ≠ bump N p → ¬ (Counted N p u ∧ Counted N p w) → τ.v w ≤ τ.v u

theorem sibColW_of_U {N : Mat} {τ : Valn} (hX : SInvX N) (hC : Cons N τ) (hG : Good3 N τ)
    (h : SibColU N τ) : SibColW N τ := by
  intro p u w hu hw huw hcons hcol
  by_cases hb : col N u = bump N p
  · exact le_of_eq (v_bump_sib hX hC hu hw hb (hcol ▸ hb))
  by_cases hc : Counted N p u ∧ Counted N p w
  · exact v_le_of_counted_pair hC hG hu hw huw hcons hc.1 hc.2
  · exact h p u w hu hw huw hcons hcol hb hc

end Ytosk
