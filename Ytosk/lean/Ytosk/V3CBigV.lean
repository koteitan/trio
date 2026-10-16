/-
**T2SeedCBig を値の残り UpgSibV に帰着（2026-10-16、top）。**

- 旧 `t2SeedCBig_of`（V3CBig）は構造の残り `T2SeedCNext` を使うが、T2SeedCNext は標準形で偽:
  (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(2,1,1)(1,1,1)(2,1,1)(3,0,0)(2,1,0)(1,1,1)(2,1,1)
  （(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(2,1,1)(1,1,1)(2,1,1)(3,0,0)(2,1,0)(2,0,0)[2] の接頭辞）。
  r = 0、q = 12、d = 4（数えない）、dn = 8（数える）で、upg(7) ≠ 8。T2SeedCBig 自体はこの行列で成り立つ。
- `UpgSibV N τ`: 同じ親の隣り合う子 a < b で、a が a − 1 から上げられ topped、b が b − 1 から上げられないなら
  v(b) ≤ v(a)。行列ごとの値の主張（測定: tools/probe_upgsibv.py）。
- `t2SeedCBig_of_sibV`: 旧証明の右からの帰納法で、dn が dn − 1 から上げられない場合だけを替える。
  そのとき dn は数える子（数えない子は上げられる）で、decP から s′ < v(dn)、UpgSibV で v(dn) ≤ v(d)。
-/
import Ytosk.V3CBig

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The value residual for consecutive siblings**: an upgraded, topped child `a` of `p` whose next sibling `b`
is not upgraded from `b − 1` has `v(b) ≤ v(a)`. -/
def UpgSibV (N : Mat) (τ : Valn) : Prop :=
  ∀ p a b, a ∈ children N p → b ∈ children N p → a < b → (∀ e ∈ children N p, a < e → b ≤ e) →
    upg N (a - 1) = some a → topped N a = true → upg N (b - 1) ≠ some b → τ.v b ≤ τ.v a

namespace G

open Classical in
/-- **`T2SeedCBig` from `UpgSibV`** (C, with t2's `T2SeedCRes`). -/
theorem t2SeedCBig_of_sibV {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hRes : T2SeedCRes M ρ r L q)
    (hSib : ∀ τ, Cons (M.take (r + L)) τ → Good3 (M.take (r + L)) τ → UpgSibV (M.take (r + L)) τ) : T2SeedCBig M ρ r L q := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 q r hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, _, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have hqnc := qP_C hM hS I hlen hr hq hqr hncl hRes.un
  -- the drop and `M.take x`
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := drop_all hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs R.drop.vst
    I.fc I.fo R.drop.argT
    (bump_drop hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td R.drop.ab R.drop.ws)
    R.drop.ua
  have hG1 := good3_take hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop
  rw [show M.length - 1 = r + L by omega] at hRk1 hC1 hG1
  have hTS : M.take (r + L) ≠ SRO := ne_SRO_of_rk hRk1
  obtain ⟨hXT, hJT⟩ := sInvXJ_std (std_take hM (r + L) (by omega)) hTS
  have hTlen : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  -- the columns of the children of `r`
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he2q : entry M 2 q = 1 := hX.loc.2.2.1 q (r + L) hxq Txb
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have he1x : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  have hcolr : ∀ c ∈ children (M.take (r + L)) r, entry (M.take (r + L)) 1 c = entry (M.take (r + L)) 1 r + 1 ∧
      entry (M.take (r + L)) 2 c = 1 ∧ par (M.take (r + L)) 1 c = some r := by
    intro c hc
    have hcx : c < r + L := by have := (mem_children hc).2; omega
    have hpcT := (mem_children_iff.mp hc).2
    have hpc : par M 0 c = some r := by rwa [par_take M 0 c hcx] at hpcT
    have hcq : c ≤ q := by
      by_contra hlt
      have hA : Anc0 M q c := anc_between (anc0_of_par M 0 q (r + L) hq) c (by omega) (le_of_lt hcx)
      have := (anc0_par hA (by omega) hpc).le; omega
    have hcol := t_child_col hX hpq (by omega) he2q (by omega) (mem_children_iff.mpr ⟨by omega, hpc⟩) hcq
    have hcqx := t_col_x hX hpq (by omega) he2q (by omega)
    have h1 : entry M 1 c = entry M 1 r + 1 := by
      have : entry M 1 c = (col M c).2.1 := rfl; rw [this, hcol, hcqx]
    have h2 : entry M 2 c = 1 := by
      have : entry M 2 c = (col M c).2.2 := rfl; rw [this, hcol, hcqx]
    refine ⟨by rw [entry_take M 1 hcx, entry_take M 1 (by omega)]; exact h1,
      by rw [entry_take M 2 hcx]; exact h2, ?_⟩
    rw [par_take M 1 c hcx]; exact par1_of_child hpc (by omega)
  have hqT : q ∈ children (M.take (r + L)) r := by
    rw [children_take, List.mem_filter]
    exact ⟨mem_children_iff.mpr ⟨by omega, hpq⟩, by simpa using hqx⟩
  -- an uncounted child is topped and upgraded from the previous column
  have huncnt : ∀ c ∈ children (M.take (r + L)) r, ¬ Counted (M.take (r + L)) r c →
      topped (M.take (r + L)) c = true ∧ upg (M.take (r + L)) (c - 1) = some c := by
    intro c hc hnc
    have hb : col (M.take (r + L)) c ≠ bump (M.take (r + L)) r := by
      intro h
      have : entry (M.take (r + L)) 1 c = (col (M.take (r + L)) c).2.1 := rfl
      rw [h] at this; simp [bump] at this; have := (hcolr c hc).1; omega
    have hut : isUpg (M.take (r + L)) c = true ∧ topped (M.take (r + L)) c = true := by
      by_contra hn; exact hnc ⟨hb, hn⟩
    refine ⟨hut.2, ?_⟩
    unfold isUpg at hut
    obtain ⟨i, _, hi⟩ := List.any_eq_true.mp hut.1
    have hu : upg (M.take (r + L)) i = some c := of_decide_eq_true hi
    by_cases hci : c = i + 1
    · rw [hci, Nat.add_sub_cancel]; rw [hci] at hu; exact hu
    · have := hXT.toSInv.uat i c hu hci; rw [this] at hut; simp at hut
  refine ⟨fun τ hτ => ?_⟩
  have hG : Good3 (M.take (r + L)) τ := good3_congr hG1 (agree_of_cons hC1 hτ hRk1)
  have hrT : r < (M.take (r + L)).length := by omega
  -- counted children are above `s′`
  have hcntd : ∀ d ∈ children (M.take (r + L)) r, Counted (M.take (r + L)) r d → qnS M ρ r L q < τ.v d := by
    intro d hd hcnt
    have hdCL : d ∈ CL (M.take (r + L)) r := List.mem_filter.mpr ⟨hd, decide_eq_true hcnt⟩
    obtain ⟨hsing, hdec⟩ := cl_vals hτ hG hrT
    rcases (CL (M.take (r + L)) r).eq_nil_or_concat with hnil | ⟨Lc, c0, hLc⟩
    · rw [hnil] at hdCL; simp at hdCL
    rw [List.concat_eq_append] at hLc
    obtain ⟨s, y, hc0, hs⟩ := hRes.decP τ hτ Lc c0 hLc
    have hc0T : c0 < (M.take (r + L)).length :=
      (mem_children (cl_mem_children (show c0 ∈ CL (M.take (r + L)) r by rw [hLc]; simp))).2
    have hdT := (mem_children hd).2
    have hvc0 : τ.v c0 = s := by
      rw [o_cl_eq hτ hG hc0T] at hc0; simp only [psi.injEq] at hc0; exact hc0.1
    have hle : τ.o c0 ≤ τ.o d := by
      rw [hLc] at hdCL hdec
      rcases List.mem_append.mp hdCL with h | h
      · exact (List.pairwise_append.mp (List.pairwise_map.mp hdec)).2.2 d h c0 (by simp)
      · simp at h; rw [h]
    have hl := lev_le_of_le hle
    rw [o_cl_eq hτ hG hc0T, o_cl_eq hτ hG hdT] at hl
    simp only [lev_psi] at hl
    rw [hvc0] at hl
    exact lt_of_lt_of_le hs hl
  -- induction from the right
  have key : ∀ n d, q - d ≤ n → d ∈ children (M.take (r + L)) r → d < q → qnS M ρ r L q < τ.v d := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro d hn hd hdq
    by_cases hcnt : Counted (M.take (r + L)) r d
    · exact hcntd d hd hcnt
    -- the next sibling
    have hex : ∃ e, e ∈ children (M.take (r + L)) r ∧ d < e := ⟨q, hqT, hdq⟩
    let dn := Nat.find hex
    obtain ⟨hdn, hddn⟩ := Nat.find_spec hex
    have hcons : ∀ e ∈ children (M.take (r + L)) r, d < e → dn ≤ e :=
      fun e he hde => Nat.find_min' hex ⟨he, hde⟩
    have hdnq : dn ≤ q := hcons q hqT hdq
    by_cases hu : upg (M.take (r + L)) (dn - 1) = some dn
    swap
    · -- `dn` is not upgraded from `dn − 1`: it is counted and below `q`, and `v(dn) ≤ v(d)`
      have hdnc : Counted (M.take (r + L)) r dn := by
        by_contra hdnc; exact hu (huncnt dn hdn hdnc).2
      have hle := hSib τ hτ hG r d dn hd hdn hddn hcons (huncnt d hd hcnt).2 (huncnt d hd hcnt).1 hu
      exact lt_of_lt_of_le (hcntd dn hdn hdnc) hle
    have hlt := upg_next_lt hXT hτ hG hd hdn hddn hcons (hcolr d hd).1 (hcolr d hd).2.1 (hcolr d hd).2.2
      (hcolr dn hdn).2.1 (hcolr dn hdn).2.2 (huncnt d hd hcnt).1 hu
    have hlt' : τ.v dn < τ.v d := hlt
    rcases Nat.eq_or_lt_of_le hdnq with h | h
    · rw [h] at hlt'; rw [← hRes.vqP τ hτ]; exact hlt'
    · exact lt_trans (ih (q - dn) (by omega) dn le_rfl hdn h) hlt'
  intro d hd hdq _
  exact key (q - d) d le_rfl hd hdq

end G

end Ytosk
