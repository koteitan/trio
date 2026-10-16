/-
**UpgSibV を難しい 2 つの形に絞る（2026-10-17、top）。**

UpgSibV（V3CBigV）の前件: 同じ親 p の隣り合う子 a < b、a は a − 1 から上げられ topped、b は b − 1 から
上げられない。このとき col a = (e0 p + 1, y, 1)、P_1 a = p、e2 p = 0（y = e1 (a − 1)）。SibDec で
col b ≤ col a なので、場合は次の 4 つ。
- e1 b < y: y = e1 p + 1（R1S）なので e1 b ≤ e1 p。e2 b = 1 なら RowJ で e1 b = e1 p となり b = bump(p)、
  BumpE2 で e2 p = 1 と矛盾。よって e2 b = 0。e1 b = 0 なら v(b) = 0。e1 b ≠ 0 なら g = P_1 b は p の真の祖先で、
  v(b) ≤ v(p) ≤ v(a) を示す（`v_chain_lt`・`v_par1_lt`）:
  - upg b = none: v(b) = v(g) + 1、v(g) < v(p) なので v(b) ≤ v(p)。
  - upg b = k（g の子で b の祖先）: v(b) = v(k)。k から p への道の列 j で v(k) ≤ v(j) を j の帰納法で示す。
    P_1 j が g より下なら道の上にあり帰納法と v_par1_lt。P_1 j = g なら e1 j = e1 k で、e2 j = 0 なら
    upg j = k（`upg_of_anc_target`）で v(j) = v(k)。e2 j = 1 は RowJ・BumpE2 で j が親の bump 子になり、
    親が k なら j の道の上の子が BumpLeaf で葉になって p に子があることと矛盾、親が k でなければ
    BumpLeaf で e2 j = 0 となり矛盾。
  - upg b = b + 1（次の列、b の後ろの g の子）: 難しい形（`UpgSibVHard` の右）。標本では起きない。
- col b = col a で a に子がある: 難しい（`UpgSibVHard` の左）。S1 の値の版。
- col b = col a で a に子がない: S1 から sub(b) ≤ sub(a) = [col a] なので b にも子がなく、v(b) = v(a)。
- col b = (e0 p + 1, y, 0): b の上げの的は次の列 b + 1（p の子で列 (e0 p + 1, y, 1)）しかありえず、
  S1 の (b, b + 1) で矛盾。よって upg b = none、v(b) = v(p) + 1 ≤ v(p) + ω^{W_a} = v(a)。
`upgSibV_of_hard`: SInvX・RowJ・S1・Cons・Rk・Good3 と `UpgSibVHard` から UpgSibV。
-/
import Ytosk.V3CBigV
import Ytosk.V3EqSibS1
import Ytosk.V3OmegaLhd

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The hard shapes of `UpgSibV`**: the same column with `a` having children, or a smaller row 1. -/
def UpgSibVHard (N : Mat) (τ : Valn) : Prop :=
  ∀ p a b, a ∈ children N p → b ∈ children N p → a < b → (∀ e ∈ children N p, a < e → b ≤ e) →
    upg N (a - 1) = some a → topped N a = true → upg N (b - 1) ≠ some b →
    (col N b = col N a ∧ children N a ≠ []) ∨
      (entry N 1 b < entry N 1 a ∧ entry N 1 b ≠ 0 ∧ entry N 2 b = 0 ∧ upg N b = some (b + 1)) →
      τ.v b ≤ τ.v a

/-- A column without children is its own subtree. -/
theorem subT_leaf {N : Mat} {a : Nat} (h : children N a = []) : subT N a = [col N a] := by
  unfold subT
  rcases tw_drop N (a + 1) (fun q => decide (entry N 0 a < q.1)) with h0 | ⟨hl, hp, _⟩
  · rw [h0]
  · exfalso
    have he : entry N 0 a < entry N 0 (a + 1) := by
      have : entry N 0 (a + 1) = (col N (a + 1)).1 := by rw [entry_col]
      rw [this]; simpa using hp
    have hc : a + 1 ∈ children N a := mem_children_iff.mpr ⟨hl, par0_next he⟩
    rw [h] at hc; simp at hc

/-- A column with a child has a nonempty tail in its subtree. -/
theorem subT_tail_ne {N : Mat} {b c : Nat} (hc : c ∈ children N b) :
    (N.drop (b + 1)).takeWhile (fun q => decide (entry N 0 b < q.1)) ≠ [] := by
  have hpc : par N 0 c = some b := (mem_children_iff.mp hc).2
  have hcL := (mem_children hc).2
  obtain ⟨hbc, he, hbet⟩ := (par0_spec N).mp hpc
  have hl : b + 1 < N.length := by omega
  have he1 : entry N 0 b < entry N 0 (b + 1) := by
    rcases Nat.eq_or_lt_of_le (show b + 1 ≤ c by omega) with h | h
    · rw [h]; exact he
    · have := hbet (b + 1) (by omega) h; omega
  rw [List.drop_eq_getElem_cons hl, ← col_getElem' hl, List.takeWhile_cons]
  have : (col N (b + 1)).1 = entry N 0 (b + 1) := by rw [entry_col]
  rw [this]
  simp [he1]

/-- **`UpgSibV` from its hard shapes.** -/
theorem upgSibV_of_hard {N : Mat} {τ : Valn} {rk : Bool → Nat → Nat} (hX : SInvX N) (hJ : RowJ N)
    (hS1 : S1 N) (hC : Cons N τ) (hR : Rk N rk) (hG : Good3 N τ)
    (hH : UpgSibVHard N τ) : UpgSibV N τ := by
  intro p a b ha hb hab hcons hua htop hnub
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
  have he0a : entry N 0 a = entry N 0 m + 1 := by
    have : entry N 0 a = (col N a).1 := by rw [entry_col]
    rw [this, hcola]
  have he2a' : entry N 2 a = entry N 2 m + 1 := by
    have : entry N 2 a = (col N a).2.2 := by rw [entry_col]
    rw [this, hcola]
  have he2m : entry N 2 m = 0 := by have := hX.z2 a; omega
  have he2a : entry N 2 a = 1 := by omega
  have hlt1a : entry N 1 m < entry N 1 a := (par1_facts hp1a).2.2.1
  have he1a0' : entry N 1 a ≠ 0 := by omega
  -- the consecutive pair in the children list
  obtain ⟨l1, l2, hsplit⟩ := consec_split (children_sorted N m) ha hb hab
    (fun e he ⟨h1, h2⟩ => by have := hcons e he h1; omega)
  have hSD := hX.loc.1 m l1 l2 a b hsplit
  have hS := hS1 m l1 l2 a b hsplit
  have he0b : entry N 0 b = entry N 0 m + 1 := hX.r0p b m hpb
  unfold colLe at hSD
  rw [entry_col N b, entry_col N a] at hSD
  simp only at hSD
  have hvp := hG.ot_v m hpL
  -- `v(a) = v(m) + ω^{W_a}`
  have hbot : ∀ i j, isOT (bumpTerm N τ i j) = true := fun i j => isOT_bumpTerm hG i j
  have hWot : ∀ i, isOT (sumN (one :: (children N i).map (bumpTerm N τ i))) = true := by
    intro i; apply isOT_sumN; intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact hbot i j
  have hva : τ.v a = add (τ.v m) (omega (sumN (one :: (children N a).map (bumpTerm N τ a)))) := by
    rw [(hC a haL).2]; unfold vRhs; rw [if_neg he1a0', if_neg (by omega), hp1a]
    exact sf_ot (isOT_add hvp (isOT_omega (hWot a)))
  by_cases h1 : entry N 1 b < entry N 1 a
  · have hR1a := hX.r1s a m hpa
    have he2b0 : entry N 2 b = 0 := by
      by_contra hne
      have hJb := hJ b m hne hpb
      have he2b1 : entry N 2 b = 1 := by have := hX.z2 b; omega
      have hbb : col N b = bump N m := by
        rw [entry_col N b]; unfold bump; rw [he0b, he2b1, show entry N 1 b = entry N 1 m by omega]
      have := hX.toSInv.bumpE2 m b hb hbb; omega
    by_cases h0 : entry N 1 b = 0
    · have hvb : τ.v b = z := by rw [(hC b hbL).2]; unfold vRhs; rw [if_pos h0]
      rw [hvb]; exact z_le _
    -- `v(b) ≤ v(m) ≤ v(a)`
    have hma : τ.v m ≤ τ.v a := by rw [hva]; exact le_add_of_single _ (omega_psi_form _)
    have he1bm : entry N 1 b ≤ entry N 1 m := by omega
    obtain ⟨g, hg⟩ := par1_exists hX.e00 hX.r01 (show 0 < entry N 1 b by omega)
    obtain ⟨hAgb, hgb, he1g, hgpath⟩ := par1_facts hg
    have hbm : m < b := (mem_children hb).1
    have hgm : g ≠ m := by intro h; rw [h] at he1g; omega
    have hAmb : Anc0 N m b := anc0_of_par N 0 m b hpb
    have hAgm : Anc0 N g m := anc0_par hAgb (by omega) hpb
    have hgm' : g < m := lt_of_le_of_ne hAgm.le hgm
    have hvg := hG.ot_v g (by omega)
    have hbm' : τ.v b ≤ τ.v a := by
      cases hk : upg N b with
      | none =>
        have hvb : τ.v b = add (τ.v g) one := by
          rw [(hC b hbL).2]; unfold vRhs; rw [if_neg h0, if_pos he2b0, hg, hk]
          exact sf_ot (isOT_add hvg isOT_one)
        have hlt : τ.v g < τ.v m := v_chain_lt hC hG hR m hgm' hpL hAgm (fun s h1s h2s h3s => by
          have := hgpath s h1s (h2s.trans hAmb) h3s (by have := h2s.le; omega); omega)
        rw [hvb, add_one_eq_succ hvg]
        exact le_trans (succ_le_of_lt hlt) hma
      | some k =>
        obtain ⟨g', hg', hpk, he1k, hcase⟩ := upg_facts hk
        rw [hg] at hg'; cases hg'
        rcases hcase with hk1 | ⟨hAkb, hkb⟩
        · -- the next column: the remaining hard shape
          rw [hk1] at hk
          exact hH m a b ha hb hab hcons hua htop hnub (Or.inr ⟨h1, h0, he2b0, hk⟩)
        · obtain ⟨g2, hg2, hp1k, hcolk, _⟩ := upg_spec hk
          rw [hg] at hg2; cases hg2
          have hvbk : τ.v b = τ.v k := v_upg_eq hC hbL h0 he2b0 hk (vOpt_ot hG hbL)
            (fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
          rw [hvbk]
          have hAkm : Anc0 N k m := anc0_par hAkb (by omega) hpb
          have hAgk : Anc0 N g k := anc0_of_par N 0 g k hpk
          have hgk := par_lt N 0 k g hpk
          have he2k' : entry N 2 k = entry N 2 g + 1 := by
            have : entry N 2 k = (col N k).2.2 := by rw [entry_col]
            rw [this, hcolk]
          have he2g : entry N 2 g = 0 := by have := hX.z2 k; omega
          have he0k : entry N 0 k = entry N 0 g + 1 := hX.r0p k g hpk
          -- every column `j` on the path from `k` to `m` has `v(k) ≤ v(j)`
          have key : ∀ j, Anc0 N k j → Anc0 N j m → τ.v k ≤ τ.v j := by
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
                  · have := (mem_children ha).1; omega
                  · omega
                have hAj1 : Anc0 N j (j + 1) := by
                  rcases Nat.eq_or_lt_of_le hjmle with h | h
                  · rw [h]; exact anc_between (anc0_of_par N 0 m a hpa) (m + 1) (by omega)
                      (by have := (mem_children ha).1; omega)
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
                  · rw [hcm] at hleaf; rw [hleaf] at ha; simp at ha
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
          exact le_trans (key m hAkm (Anc0.refl m)) hma
    exact hbm'
  have he1b : entry N 1 b = entry N 1 a := by omega
  have hp1b : par N 1 b = some m := par1_of_child hpb (by omega)
  have he2b : entry N 2 b = 0 ∨ entry N 2 b = 1 := by have := hX.z2 b; omega
  rcases he2b with he2b | he2b
  · -- `col b = (e0 m + 1, y, 0)`: `b` is not upgraded
    have hub : upg N b = none := by
      cases hk : upg N b with
      | none => rfl
      | some k =>
        exfalso
        obtain ⟨m2, hm2, hpk, _, hcase⟩ := upg_facts hk
        rw [hp1b] at hm2; cases hm2
        rcases hcase with hk1 | ⟨hAkb, hkb⟩
        · subst hk1
          obtain ⟨m3, hm3, _, hcolk, _⟩ := upg_spec hk
          rw [hp1b] at hm3; cases hm3
          have hkL : b + 1 < N.length := upg_succ_lt hk
          have hkC : b + 1 ∈ children N m := mem_children_iff.mpr ⟨hkL, hpk⟩
          obtain ⟨k1, k2, hsplit2⟩ := consec_split (children_sorted N m) hb hkC (by omega)
            (fun e _ ⟨h1, h2⟩ => by omega)
          have hS2 := hS1 m k1 k2 b (b + 1) hsplit2
          unfold subT at hS2
          have hlt := (seqLtB_cons_false hS2).1
          have := colLtB_false hlt
          rw [hcolk, entry_col N b] at this
          simp only at this
          omega
        · have := (anc0_par hAkb (by omega) hpb).le
          have := par_lt N 0 k m hpk; omega
    have hvb : τ.v b = add (τ.v m) one := by
      rw [(hC b hbL).2]; unfold vRhs; rw [if_neg (by omega), if_pos he2b, hp1b, hub]
      exact sf_ot (isOT_add hvp isOT_one)
    rw [hvb, hva]
    exact add_le_add_left _ (one_le_omega (hWot a))
  · -- the same column
    have hcolab : col N b = col N a := by
      rw [entry_col N b, entry_col N a, he1b, he2b, he2a, he0b, he0a]
    by_cases hca : children N a = []
    · -- `a` has no children: neither has `b`
      have hcb : children N b = [] := by
        by_contra hne
        obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
        have htw := subT_tail_ne hc
        rw [subT_leaf hca] at hS
        unfold subT at hS
        rw [hcolab] at hS
        have h2 := (seqLtB_cons_false hS).2 rfl
        cases htw' : (N.drop (b + 1)).takeWhile (fun q => decide (entry N 0 b < q.1)) with
        | nil => exact htw htw'
        | cons q U => rw [htw'] at h2; simp [seqLtB] at h2
      have hvb : τ.v b = τ.v a := by
        rw [(hC b hbL).2, (hC a haL).2]; unfold vRhs
        rw [if_neg (by omega), if_neg (by omega), if_neg he1a0', if_neg (by omega), hp1b, hp1a, hcb, hca]
        rfl
      exact le_of_eq hvb
    · exact hH m a b ha hb hab hcons hua htop hnub (Or.inl ⟨hcolab, hca⟩)

end Ytosk
