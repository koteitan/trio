/-
**種の状態は σ で動かない（closure、2026-10-12）。**

t = 2 の種の列 r（行 2 = 0）と、r の行 2 = 1 の子 x（e1 x > e1 r）。V = v(r)、σ = σ_{V, V+1}。
x へ上げる列がなければ、x より前の r の子 d の値 o(d) は σ で動かない。したがって t2 の
`T2SeedQRRes.σB`（x より前の状態 B は σ(B) = B）が出る。

構造の不変条件（SInvX・RowJ）と評価の式（Cons・Good3・Rk）だけから示す。保存の証明は要らない。
実測: 5 集合と、構造の条件を満たす長さ 8 以下の全行列 94 万個（非標準形を含む）で例外 0。

証明の筋（列 c は r < c < x）:
- 「隠れた列」: v(p) ≤ V の列 p（r < p）の真の子孫。σ は添字が V 以下の ψ の引数に入らないので、
  隠れた列の値は σ に見えない。見える列 c について、順位の帰納法で σ(o c) = o c と
  （V < v c なら）f(v c) = v c を示す。
- P_1(c) が r より上: v(c) ≤ V（上げなしは v(P_1 c) + 1 ≤ V、上げありは `upg_anc_spine`）。
  行 2 = 1 なら親も同じ形で、いちばん上の行 2 = 0 の列が c を隠す。
- P_1(c) = r・行 2 = 0: 必ず上げる。r の子は兄弟の減少ですべて x と同じ列 (e0 r + 1, e1 r + 1, 1)
  なので、c を含む r の子 d が上げの形をしている（`t_upg_ne`）。
- P_1(c) = r・行 2 = 1: v(c) = V + ω^W（ω^W ≥ ω なので f(v c) = V + 1 + ω^W = v c）。
- P_1(c) が (r, c) の中: 帰納法の仮定から f(v(P_1 c)) = v(P_1 c)。
-/
import Ytosk.V3ExpT2GV
import Ytosk.V3T0Sh3
import Ytosk.V3ExpT1A
import Ytosk.V3SubstC
import Ytosk.V3PhiLevLink
import Ytosk.V3InvW

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## 構造 -/

section
variable {M : Mat} (hX : SInvX M) (hJ : RowJ M) {r x : Nat} (hrx : par M 0 x = some r)
  (hxM : x < M.length) (he2x : entry M 2 x = 1) (he1x : entry M 1 r < entry M 1 x) (he2r : entry M 2 r = 0)
include hX hrx

theorem t_rx : r < x := par_lt M 0 x r hrx

theorem t_e0x : entry M 0 x = entry M 0 r + 1 := hX.r0p x r hrx

/-- Columns strictly between `r` and `x` have row 0 above that of `r`. -/
theorem t_e0_mid {j : Nat} (hj1 : r < j) (hj2 : j < x) : entry M 0 r + 1 ≤ entry M 0 j := by
  obtain ⟨_, _, hbet⟩ := (par0_spec M).mp hrx
  have := hbet j hj1 hj2
  rw [t_e0x hX hrx] at this; exact this

theorem t_anc_r {c : Nat} (h1 : r ≤ c) (h2 : c ≤ x) : Anc0 M r c :=
  anc_between (anc0_of_par M 0 r x hrx) c h1 h2

/-- **Descendants of a column in `(r, x)` stay before `x`.** -/
theorem t_desc_lt {c c' : Nat} (h1 : r < c) (h2 : c < x) (hA : Anc0 M c c') : c' < x := by
  by_contra hc
  have hle : x ≤ c' := by omega
  have := anc0_interval hA x (by omega) hle
  have := t_e0_mid hX hrx h1 h2
  rw [t_e0x hX hrx] at *; omega

theorem t_mem_children {c : Nat} (hp : par M 0 c = some r) (hc : c < M.length) : c ∈ children M r := by
  unfold children; rw [List.mem_filter, List.mem_range]; exact ⟨hc, by simp [hp]⟩

theorem t_par_of_mem {c : Nat} (h : c ∈ children M r) : par M 0 c = some r := by
  unfold children at h; rw [List.mem_filter] at h; simpa using h.2

include hxM he2x he1x

theorem t_col_x : col M x = (entry M 0 r + 1, entry M 1 r + 1, 1) := by
  have h1 := hX.r1s x r hrx
  have h0 := t_e0x hX hrx
  show (entry M 0 x, entry M 1 x, entry M 2 x) = _
  rw [h0, he2x]; congr 2; omega

/-- **Every child of `r` up to `x` has the column of `x`** (siblings do not increase, and the column of
`x` is the largest a child of `r` can have). -/
theorem t_child_col {d : Nat} (hd : d ∈ children M r) (hdx : d ≤ x) : col M d = col M x := by
  rcases Nat.eq_or_lt_of_le hdx with rfl | hlt
  · rfl
  obtain ⟨s, t, hst⟩ := List.append_of_mem hd
  have hxmem : x ∈ children M r := t_mem_children hX hrx hrx hxM
  have hxt : x ∈ t := by
    rw [hst] at hxmem
    rcases List.mem_append.mp hxmem with hs | ht
    · have hsort := children_sorted M r
      rw [hst, List.pairwise_append] at hsort
      have := hsort.2.2 x hs d (by simp); omega
    · rcases List.mem_cons.mp ht with h | h
      · omega
      · exact h
  have hle := sib_le hX.loc.1 t s d hst x hxt
  have hpd := t_par_of_mem hX hrx hd
  have h0 : entry M 0 d = entry M 0 r + 1 := hX.r0p d r hpd
  have h1 : entry M 1 d ≤ entry M 1 r + 1 := hX.r1s d r hpd
  have h2 : entry M 2 d ≤ 1 := hX.z2 d
  rw [t_col_x hX hrx hxM he2x he1x]
  rw [t_col_x hX hrx hxM he2x he1x] at hle
  unfold colLe at hle
  show (entry M 0 d, entry M 1 d, entry M 2 d) = _
  have e0 : (col M d).1 = entry M 0 d := rfl
  have e1 : (col M d).2.1 = entry M 1 d := rfl
  have e2 : (col M d).2.2 = entry M 2 d := rfl
  simp only [e0, e1, e2] at hle
  rw [h0]; congr 2 <;> omega

include he2r

/-- The child of `r` above a column `c ∈ (r, x)`. -/
theorem t_top_child {c : Nat} (h1 : r < c) (h2 : c < x) :
    ∃ d, par M 0 d = some r ∧ Anc0 M d c ∧ col M d = col M x := by
  obtain ⟨d, hpd, hdc⟩ := anc0_child (t_anc_r hX hrx (le_of_lt h1) (le_of_lt h2)) (by omega)
  have := hdc.le
  refine ⟨d, hpd, hdc, t_child_col hX hrx hxM he2x he1x (t_mem_children hX hrx hpd (by omega))
    (by omega)⟩

/-- **A column with `P_1 = r` and row 2 zero upgrades** (`b1`). -/
theorem t_upg_ne {c : Nat} (h1 : r < c) (h2 : c < x) (he1 : entry M 1 c ≠ 0) (he2 : entry M 2 c = 0)
    (hm : par M 1 c = some r) : upg M c ≠ none := by
  obtain ⟨d, hpd, hdc, hcold⟩ := t_top_child hX hrx hxM he2x he1x he2r h1 h2
  have hcx := t_col_x hX hrx hxM he2x he1x
  have hd1 : entry M 1 d = entry M 1 r + 1 := by
    have : entry M 1 d = (col M d).2.1 := rfl; rw [this, hcold, hcx]
  have hd2 : entry M 2 d = 1 := by
    have : entry M 2 d = (col M d).2.2 := rfl; rw [this, hcold, hcx]
  have hdne : d ≠ c := fun h => by rw [h] at hd2; omega
  have hdr : d ≠ r := fun h => by have := par_lt M 0 d r hpd; omega
  obtain ⟨_, _, hlt1, hbet⟩ := par1_facts hm
  have hc1 : entry M 1 c = entry M 1 r + 1 := by
    have := hbet d (anc0_of_par M 0 r d hpd) hdc hdr hdne; omega
  have hcolL : col M d = (entry M 0 r + 1, entry M 1 c, entry M 2 r + 1) := by
    rw [hcold, hcx, hc1, he2r]
  have hc1M : c + 1 < M.length := by omega
  by_cases hnext : entry M 0 r + 1 < entry M 0 (c + 1)
  · have hpd1 : par M 1 d = some r := par1_of_child hpd (by omega)
    rw [upg_of_anc_target hc1M he1 he2 hm hpd1 hcolL hdc hdne hnext]; simp
  · -- `c + 1` is a child of `r`
    have hge : entry M 0 r + 1 ≤ entry M 0 (c + 1) := by
      rcases Nat.lt_or_ge (c + 1) x with h | h
      · exact t_e0_mid hX hrx (by omega) h
      · have : c + 1 = x := by omega
        rw [this, t_e0x hX hrx]
    have hp : par M 0 (c + 1) = some r := by
      rw [par0_spec]
      refine ⟨by omega, by omega, fun j hj1 hj2 => ?_⟩
      have := t_e0_mid hX hrx hj1 (by omega); omega
    have hcol1 : col M (c + 1) = col M x :=
      t_child_col hX hrx hxM he2x he1x (t_mem_children hX hrx hp hc1M) (by omega)
    have hp1 : par M 1 (c + 1) = some r := by
      apply par1_of_child hp
      have : entry M 1 (c + 1) = (col M (c + 1)).2.1 := rfl
      rw [this, hcol1, hcx]; show entry M 1 r < entry M 1 r + 1; omega
    have hu : upg M c = some (c + 1) := by
      unfold upg
      rw [if_neg (show ¬ (entry M 1 c = 0 ∨ entry M 2 c = 1 ∨ c + 1 = M.length) by omega), hm]
      dsimp only
      rw [if_pos ⟨hp1, by rw [hcol1, hcx, hc1, he2r]⟩]
    rw [hu]; simp

end

/-! ## `P_1(c)` が r より上: v(c) ≤ v(r) -/

section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hX : SInvX M) (hJ : RowJ M)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) {r x : Nat} (hrx : par M 0 x = some r)
  (hxM : x < M.length) (he2r : entry M 2 r = 0)
include hX hJ hC hG hR hrx hxM he2r

/-- **Row 2 zero, `P_1(c)` above `r`**: `v(c) ≤ v(r)`. -/
theorem t_above0 {c m : Nat} (h1 : r < c) (h2 : c < x) (he1 : entry M 1 c ≠ 0) (he2 : entry M 2 c = 0)
    (hm : par M 1 c = some m) (hmr : m < r) : ¬ ρ.v r < ρ.v c := by
  have hcM : c < M.length := by omega
  have hrM : r < M.length := by omega
  have hAr := t_anc_r hX hrx (le_of_lt h1) (le_of_lt h2)
  obtain ⟨hmc, _, he1m, hbet⟩ := par1_facts hm
  have hAmr : Anc0 M m r := by
    rcases anc0_total hmc hAr with h | h
    · exact h
    · have := h.le; omega
  have hre1 : entry M 1 c ≤ entry M 1 r := hbet r hAmr hAr (by omega) (by omega)
  have hvm : isOT (vOpt ρ (par M 1 c)) = true := vOpt_ot hG hcM
  have hbk : ∀ k, ∀ j ∈ children M k, col M j = bump M k → ∀ k' ∈ children M j, isOT (ρ.o k') = true :=
    fun k j _ _ k' hk' => hG.ot_o k' (mem_children hk').2
  cases hu : upg M c with
  | none =>
    -- `v(c) = v(m) + 1` and `v(m) < v(r)`
    have hvc : ρ.v c = succ (ρ.v m) := by
      rw [(hC c hcM).2]; unfold vRhs
      rw [if_neg he1, if_pos he2, hm, hu]
      have hmot := hG.ot_v m (by have := hmc.le; omega)
      show sf (add (ρ.v m) one) = _
      rw [sf_ot (isOT_add hmot isOT_one), add_one_eq_succ hmot]
    have hfind : (ancL M r).find? (fun q => decide (entry M 1 q < entry M 1 c)) = some m := by
      have hp := hm
      rw [par1_find] at hp
      obtain ⟨S, hS, hSp⟩ := ancL_through hAr (by omega)
      rw [hS, List.find?_append, List.find?_cons] at hp
      have hSn : S.find? (fun q => decide (entry M 1 q < entry M 1 c)) = none := by
        rw [List.find?_eq_none]
        intro s hs
        obtain ⟨hrs, hsc, hArs, hAsc⟩ := hSp s hs
        have := hbet s (Anc0.trans hAmr hArs) hAsc (by omega) (by omega)
        simp; omega
      rw [hSn, Option.none_or, decide_eq_false (by omega)] at hp
      exact hp
    have hlt := v_find_lt hC hG hR r hrM (entry M 1 c) m hre1 hfind
    rw [hvc]
    exact not_lt_of_ge (succ_le_of_lt hlt)
  | some k =>
    have hvck := v_upg_eq hC hcM he1 he2 hu hvm (hbk k)
    obtain ⟨m', hm', hpk, _, hcase⟩ := upg_facts hu
    rw [hm] at hm'; cases hm'
    have he0m : entry M 0 m < entry M 0 r := anc0_e0_lt hAmr (by omega)
    have he0k : entry M 0 k = entry M 0 m + 1 := hX.r0p k m hpk
    rcases hcase with hk | ⟨hAkc, hkc⟩
    · exfalso
      subst hk
      rcases Nat.lt_or_ge (c + 1) x with h | h
      · have := t_e0_mid hX hrx (by omega) h; omega
      · have : c + 1 = x := by omega
        rw [this, t_e0x hX hrx] at he0k; omega
    · have hAkr : Anc0 M k r := by
        rcases anc0_total hAkc hAr with h | h
        · exact h
        · exfalso
          by_cases hrk : r = k
          · subst hrk
            have := upg_target_e2 hu; omega
          · have := anc0_e0_lt h hrk; omega
      have hsp := (upg_anc_spine hX.r0p hX.z2 (uab_of_bumpLeaf hX.loc.2.2.2) hX.loc.2.2.1 hJ hC hG hR
        hcM hu hAkc hkc r hAkr hAr (by omega)).2
      rw [hvck]
      exact not_lt_of_ge hsp

end

/-- **Visible columns**: in `(r, x)` and not below a column `p ∈ (r, ·)` with `v(p) ≤ v(r)`. -/
def TVis (M : Mat) (ρ : Valn) (r x c : Nat) : Prop :=
  r < c ∧ c < x ∧ ∀ p, r < p → Anc0 M p c → p ≠ c → ρ.v r < ρ.v p

section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hX : SInvX M) (hJ : RowJ M)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) {r x : Nat} (hrx : par M 0 x = some r)
  (hxM : x < M.length) (he2r : entry M 2 r = 0)
include hX hJ hC hG hR hrx hxM he2r

/-- **`P_1(c)` above `r`, `c` visible**: `v(c) ≤ v(r)`. Row 2 one is impossible: the parent has the same
row 1 and the same `P_1`, and the topmost such column has row 2 zero and hides `c`. -/
theorem t_above : ∀ c, TVis M ρ r x c → entry M 1 c ≠ 0 → ∀ m, par M 1 c = some m → m < r →
    ¬ ρ.v r < ρ.v c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro hV he1 m hm hmr
  obtain ⟨h1, h2, hvis⟩ := hV
  by_cases he2 : entry M 2 c = 0
  · exact t_above0 hX hJ hC hG hR hrx hxM he2r h1 h2 he1 he2 hm hmr
  exfalso
  have he2c : entry M 2 c = 1 := by have := hX.z2 c; omega
  have hAr := t_anc_r hX hrx (le_of_lt h1) (le_of_lt h2)
  obtain ⟨hmc, _, _, hbet⟩ := par1_facts hm
  have hAmr : Anc0 M m r := by
    rcases anc0_total hmc hAr with h | h
    · exact h
    · have := h.le; omega
  have hre1 : entry M 1 c ≤ entry M 1 r := hbet r hAmr hAr (by omega) (by omega)
  obtain ⟨p0, hp0⟩ := par0_some_of (M := M) h1 (by have := t_e0_mid hX hrx h1 h2; omega)
  have hAp0 : Anc0 M r p0 := anc0_par hAr (by omega) hp0
  have hp0c : p0 < c := par_lt M 0 c p0 hp0
  have hJ0 : entry M 1 p0 ≤ entry M 1 c := hJ c p0 (by omega) hp0
  have hp0r : p0 ≠ r := by
    intro h; subst h
    have hcb : col M c = bump M p0 := by
      show (entry M 0 c, entry M 1 c, entry M 2 c) = (entry M 0 p0 + 1, entry M 1 p0, 1)
      rw [hX.r0p c p0 hp0, he2c]; congr 2; omega
    have := hX.loc.2.2.1 p0 c (t_mem_children hX hp0 hp0 (by omega)) hcb
    omega
  have hrp0 : r < p0 := by have := hAp0.le; omega
  have hAp0c : Anc0 M p0 c := anc0_of_par M 0 p0 c hp0
  have he1p0 : entry M 1 p0 = entry M 1 c := by
    have := hbet p0 (Anc0.trans hAmr hAp0) hAp0c (by omega) (by omega); omega
  have hm0 : par M 1 p0 = some m := by
    have hp := hm
    rw [par1_find, ancL_eq hp0, List.find?_cons, decide_eq_false (by omega)] at hp
    rw [par1_find, he1p0]; exact hp
  have hV0 : TVis M ρ r x p0 :=
    ⟨hrp0, by omega, fun p hp hA hne => hvis p hp (Anc0.trans hA hAp0c) (by have := hA.le; omega)⟩
  exact ih p0 hp0c hV0 (by omega) m hm0 hmr (hvis p0 hrp0 hAp0c (by omega))

end

/-! ## σ の補題 -/

theorem t_bump_par1 {M : Mat} {c j m : Nat} (hj : j ∈ children M c) (hb : col M j = bump M c)
    (hm : par M 1 c = some m) : par M 1 j = some m := by
  have hpj : par M 0 j = some c := by unfold children at hj; rw [List.mem_filter] at hj; simpa using hj.2
  have he : entry M 1 j = entry M 1 c := by
    have : entry M 1 j = (col M j).2.1 := rfl; rw [this, hb]; rfl
  have hn : ¬ entry M 1 c < entry M 1 j := by omega
  rw [par1_find, ancL_eq hpj, List.find?_cons, decide_eq_false hn, he]
  rw [par1_find] at hm; exact hm

theorem t_par_of_child {M : Mat} {c j : Nat} (hj : j ∈ children M c) : par M 0 j = some c := by
  unfold children at hj; rw [List.mem_filter] at hj; simpa using hj.2

/-- `V + 1 + X = V + X` for a single `X ≠ 1`. -/
theorem t_add_succ {V X : T} (hV : isOT V = true) (hX : ∃ d e, X = psi d e z) (h1 : X ≠ one) :
    add (succ V) X = add V X := by
  obtain ⟨d, e, rfl⟩ := hX
  rw [← add_one_eq_succ hV, add_assoc']
  congr 1
  apply add_eq_right_of_head_lt
  show one < psi d e z
  rcases lt_trichotomy one (psi d e z) with h | h | h
  · exact h
  · exact absurd h.symm h1
  · exfalso
    rw [one, T.psi_lt_psi] at h
    rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> exact T.not_lt_z _ h

/-- **`sp` does not see its level** when every summand's subscript is above both levels. -/
theorem spArg_level {a a' : T} : ∀ {b S : T}, (∀ q ∈ summands S, a < lev q ∧ a' < lev q) →
    spArg a b S = spArg a' b S
  | _, z, _ => rfl
  | b, psi s y c, h => by
    have hs := h (psi s y z) (by simp [summands])
    simp only [lev_psi] at hs
    have e1 : lt (psi a z z) (psi s y c) = true := T.psi_lt_psi.mpr (Or.inl hs.1)
    have e2 : lt (psi a' z z) (psi s y c) = true := T.psi_lt_psi.mpr (Or.inl hs.2)
    rw [spArg_cons, spArg_cons]
    have hst : step a b s y c = step a' b s y c := by unfold step; simp only [e1, e2]
    rw [hst]
    exact spArg_level (fun q hq => h q (by simp [summands, hq]))

/-! ## 本体: 見える列の値は σ で動かない -/

section
open Classical
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hX : SInvX M) (hJ : RowJ M)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hR : Rk M rk) {r x : Nat} (hrx : par M 0 x = some r)
  (hxM : x < M.length) (he2x : entry M 2 x = 1) (he1x : entry M 1 r < entry M 1 x)
  (he2r : entry M 2 r = 0)
  (hux : ∀ i, upg M i = some x → ρ.v r < ρ.v x → shf (ρ.v r) (succ (ρ.v r)) (ρ.v x) = ρ.v x)
include hX hJ hC hG hR hrx hxM he2x he1x he2r hux

/-- **The main induction**: for a visible column `c`, `σ(o c) = o c`, and `f(v c) = v c` when `V < v c`. -/
theorem t_main : ∀ n c, TVis M ρ r x c →
    (rk true c ≤ n → sh (ρ.v r) (succ (ρ.v r)) (ρ.o c) = ρ.o c) ∧
    (rk false c ≤ n → ρ.v r < ρ.v c → shf (ρ.v r) (succ (ρ.v r)) (ρ.v c) = ρ.v c) := by
  have hrM : r < M.length := by have := t_rx hX hrx; omega
  have hV : isOT (ρ.v r) = true := hG.ot_v r hrM
  have hV' : isOT (succ (ρ.v r)) = true := isOT_succ hV
  have hVV : ρ.v r < succ (ρ.v r) := lt_succ_self _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hVc
  obtain ⟨h1, h2, hvis⟩ := hVc
  have hcM : c < M.length := by omega
  have hRc := hR c hcM
  constructor
  · -- the `o` equation
    intro hn
    by_cases hlt : ρ.v r < ρ.v c
    · have hf := (ih (rk false c) (by have := hRc.1; omega) c ⟨h1, h2, hvis⟩).2 le_rfl hlt
      have hvo := hG.ot_v c hcM
      have hl : ∀ t ∈ (children M c).map (cnt M ρ c), isOT t = true := by
        intro t ht
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp ht
        unfold cnt; split_ifs
        · rfl
        · rfl
        · exact hG.ot_o c' (mem_children hc').2
      have hS := isOT_sumN _ hl
      have hmap : (children M c).map (sh (ρ.v r) (succ (ρ.v r)) ∘ cnt M ρ c) =
          (children M c).map (cnt M ρ c) := by
        apply List.map_congr_left
        intro c' hc'
        simp only [Function.comp]
        rw [cnt_eq_ite]
        split_ifs with hcnt
        · have hpc' := t_par_of_child hc'
          have hcc' : c < c' := par_lt M 0 c' c hpc'
          have hA : Anc0 M c c' := anc0_of_par M 0 c c' hpc'
          have hT : TVis M ρ r x c' := by
            refine ⟨by omega, t_desc_lt hX hrx h1 h2 hA, fun p hp hpc hne => ?_⟩
            have hpc0 : Anc0 M p c := anc0_par hpc hne hpc'
            by_cases hpe : p = c
            · rw [hpe]; exact hlt
            · exact hvis p hp hpc0 hpe
          exact (ih (rk true c') (by have := hRc.2.1 c' hc' hcnt.1 hcnt.2; omega) c' hT).1 le_rfl
        · exact sh_z
      rw [(hC c hcM).1]; unfold oRhs
      rw [← sf_psi_sh_gt hV hV' hVV hvo hS hlt, hf, sh_sumN hV hV' hVV hl, List.map_map, hmap]
    · obtain ⟨y, hy⟩ := o_psi_sub hC hcM
      rw [hy, sf_ot (hG.ot_v c hcM), sh_psi_le hlt, sh_z]
  · -- the `v` equation
    intro hn hlt
    have he1 : entry M 1 c ≠ 0 := by
      intro h0
      rw [(hC c hcM).2] at hlt; unfold vRhs at hlt; rw [if_pos h0] at hlt; exact T.not_lt_z _ hlt
    obtain ⟨m, hm⟩ : ∃ m, par M 1 c = some m := by
      obtain ⟨Rt, hRt, he0, _⟩ := root_exists hX.e00 c
      have hRe1 : entry M 1 Rt = 0 := hX.r01 Rt he0
      have hRtc : Rt ≠ c := by
        intro h; subst h; have := t_e0_mid hX hrx h1 h2; omega
      obtain ⟨m, hm, _, _⟩ := par1_near hRt hRtc (by omega)
      exact ⟨m, hm⟩
    have hRc1 := hRc.2.2 he1
    obtain ⟨hmc, hmlt, _, _⟩ := par1_facts hm
    have hmM : m < M.length := by omega
    -- the bump terms are fixed when `V ≤ v(P_1 c)`
    have hW : entry M 2 c ≠ 0 → ρ.v r ≤ ρ.v m →
        sh (ρ.v r) (succ (ρ.v r)) (sumN (one :: (children M c).map (bumpTerm M ρ c))) =
          sumN (one :: (children M c).map (bumpTerm M ρ c)) := by
      intro he2 hVm
      have hl : ∀ t ∈ one :: (children M c).map (bumpTerm M ρ c), isOT t = true := by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · rfl
        · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG c j
      rw [sh_sumN hV hV' hVV hl, List.map_cons, sh_one, List.map_map]
      congr 2
      apply List.map_congr_left
      intro j hj
      simp only [Function.comp]
      unfold bumpTerm
      split_ifs with hb
      · have hpj := t_par_of_child hj
        have hcj : c < j := par_lt M 0 j c hpj
        have hjM : j < M.length := (mem_children hj).2
        have hj1 : entry M 1 j ≠ 0 := by
          have : entry M 1 j = (col M j).2.1 := rfl; rw [this, hb]; exact he1
        have hpj1 := t_bump_par1 hj hb hm
        have hvj : ρ.v r < ρ.v j :=
          lt_of_le_of_lt hVm (v_par1_lt hC hG hR (rk false j) j m le_rfl hjM hj1 hpj1)
        have hlk : ∀ t ∈ (children M j).map ρ.o, isOT t = true := by
          intro t ht
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
          exact hG.ot_o k (mem_children hk).2
        have hmapk : (children M j).map (sh (ρ.v r) (succ (ρ.v r)) ∘ ρ.o) = (children M j).map ρ.o := by
          apply List.map_congr_left
          intro k hk
          simp only [Function.comp]
          have hpk := t_par_of_child hk
          have hjk : j < k := par_lt M 0 k j hpk
          have hAck : Anc0 M c k := Anc0.trans (anc0_of_par M 0 c j hpj) (anc0_of_par M 0 j k hpk)
          have hT : TVis M ρ r x k := by
            refine ⟨by omega, t_desc_lt hX hrx h1 h2 hAck, fun p hp hpk' hne => ?_⟩
            have hpj' : Anc0 M p j := anc0_par hpk' hne hpk
            by_cases hpe : p = j
            · rw [hpe]; exact hvj
            · have hpc : Anc0 M p c := anc0_par hpj' hpe hpj
              by_cases hpe' : p = c
              · rw [hpe']; exact hlt
              · exact hvis p hp hpc hpe'
          exact (ih (rk true k) (by have := hRc1.2.2 he2 j hj hb k hk; omega) k hT).1 le_rfl
        rw [sh_omega hV hV' hVV (isOT_sumN _ hlk), sh_sumN hV hV' hVV hlk, List.map_map, hmapk]
      · exact sh_z
    have hWot : isOT (sumN (one :: (children M c).map (bumpTerm M ρ c))) = true := by
      apply isOT_sumN
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG c j
    have hvmot := hG.ot_v m hmM
    rcases lt_trichotomy m r with hmr | hmr | hrm
    · exact absurd hlt (t_above hX hJ hC hG hR hrx hxM he2r c ⟨h1, h2, hvis⟩ he1 m hm hmr)
    · -- `P_1(c) = r`
      have hrm' : r = m := hmr.symm
      subst hrm'
      by_cases he2 : entry M 2 c = 0
      · obtain ⟨k, hu⟩ := Option.ne_none_iff_exists'.mp
          (t_upg_ne hX hrx hxM he2x he1x he2r h1 h2 he1 he2 hm)
        have hvck := v_upg_eq hC hcM he1 he2 hu (vOpt_ot hG hcM)
          (fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
        obtain ⟨m', hm', hpk, _, hcase⟩ := upg_facts hu
        rw [hm] at hm'; cases hm'
        rw [hvck] at hlt ⊢
        by_cases hkx : k = x
        · subst hkx; exact hux c hu hlt
        have hkx' : k < x := by
          rcases hcase with h | ⟨_, h⟩ <;> omega
        have hT : TVis M ρ r x k := by
          refine ⟨par_lt M 0 k r hpk, hkx', fun p hp hpk' hne => ?_⟩
          have := (anc0_par hpk' hne hpk).le; omega
        exact (ih (rk false k) (by have := hRc1.2.1 he2 k hu; omega) k hT).2 le_rfl hlt
      · have hvc : ρ.v c = add (ρ.v r) (omega (sumN (one :: (children M c).map (bumpTerm M ρ c)))) := by
          rw [(hC c hcM).2]; unfold vRhs; rw [if_neg he1, if_neg he2, hm]
          exact sf_ot (isOT_add hvmot (isOT_omega hWot))
        rw [hvc, shf_add hV hV' hVV hV (isOT_omega hWot) (le_refl _), shf_self,
          sh_omega hV hV' hVV hWot, hW he2 (le_refl _)]
        exact t_add_succ hV (omega_psi_form _) (bumpOmega_ne_one hC hG c)
    · -- `P_1(c)` strictly between `r` and `c`
      have hTm : TVis M ρ r x m :=
        ⟨hrm, by omega, fun p hp hpm hne => hvis p hp (Anc0.trans hpm hmc) (by have := hpm.le; omega)⟩
      have hvm : ρ.v r < ρ.v m := hvis m hrm hmc (by omega)
      have hfm := (ih (rk false m) (by have := hRc1.1 m hm; omega) m hTm).2 le_rfl hvm
      by_cases he2 : entry M 2 c = 0
      · cases hu : upg M c with
        | none =>
          have hvc : ρ.v c = add (ρ.v m) one := by
            rw [(hC c hcM).2]; unfold vRhs; rw [if_neg he1, if_pos he2, hm, hu]
            exact sf_ot (isOT_add hvmot isOT_one)
          rw [hvc, shf_add hV hV' hVV hvmot isOT_one (le_of_lt hvm), hfm, sh_one]
        | some k =>
          have hvck := v_upg_eq hC hcM he1 he2 hu (vOpt_ot hG hcM)
            (fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
          obtain ⟨m', hm', hpk, _, hcase⟩ := upg_facts hu
          rw [hm] at hm'; cases hm'
          rw [hvck] at hlt ⊢
          have hkx : k ≠ x := by
            intro h; subst h; rw [hrx] at hpk; cases hpk; omega
          have hkx' : k < x := by
            rcases hcase with h | ⟨_, h⟩ <;> omega
          have hT : TVis M ρ r x k := by
            refine ⟨by have := par_lt M 0 k m hpk; omega, hkx', fun p hp hpk' hne => ?_⟩
            have hpm : Anc0 M p m := anc0_par hpk' hne hpk
            by_cases hpe : p = m
            · rw [hpe]; exact hvm
            · exact hvis p hp (Anc0.trans hpm hmc) (by have := hpm.le; omega)
          exact (ih (rk false k) (by have := hRc1.2.1 he2 k hu; omega) k hT).2 le_rfl hlt
      · have hvc : ρ.v c = add (ρ.v m) (omega (sumN (one :: (children M c).map (bumpTerm M ρ c)))) := by
          rw [(hC c hcM).2]; unfold vRhs; rw [if_neg he1, if_neg he2, hm]
          exact sf_ot (isOT_add hvmot (isOT_omega hWot))
        rw [hvc, shf_add hV hV' hVV hvmot (isOT_omega hWot) (le_of_lt hvm), hfm,
          sh_omega hV hV' hVV hWot, hW he2 (le_of_lt hvm)]


/-- **Children of `r` before `x` are fixed by σ.** -/
theorem t_child_fix {d : Nat} (hd : d ∈ children M r) (hdx : d < x) :
    sh (ρ.v r) (succ (ρ.v r)) (ρ.o d) = ρ.o d := by
  have hpd := t_par_of_child hd
  have hT : TVis M ρ r x d := ⟨par_lt M 0 d r hpd, hdx, fun p hp hpd' hne => by
    have := (anc0_par hpd' hne hpd).le; omega⟩
  exact (t_main hX hJ hC hG hR hrx hxM he2x he1x he2r hux (rk true d) d hT).1 le_rfl

/-- `v(d) = V + ω^W > V + 1` for a child `d` of `r` before `x`. -/
theorem t_child_lev {d : Nat} (hd : d ∈ children M r) (hdx : d < x) :
    succ (ρ.v r) < ρ.v d := by
  have hrM : r < M.length := by have := t_rx hX hrx; omega
  have hV : isOT (ρ.v r) = true := hG.ot_v r hrM
  have hpd := t_par_of_child hd
  have hdM : d < M.length := (mem_children hd).2
  have hcol := t_child_col hX hrx hxM he2x he1x hd (le_of_lt hdx)
  have hcx := t_col_x hX hrx hxM he2x he1x
  have he1 : entry M 1 d = entry M 1 r + 1 := by
    have : entry M 1 d = (col M d).2.1 := rfl; rw [this, hcol, hcx]
  have he2 : entry M 2 d = 1 := by
    have : entry M 2 d = (col M d).2.2 := rfl; rw [this, hcol, hcx]
  have hm : par M 1 d = some r := par1_of_child hpd (by omega)
  have hWot : isOT (sumN (one :: (children M d).map (bumpTerm M ρ d))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG d j
  have hvd : ρ.v d = add (ρ.v r) (omega (sumN (one :: (children M d).map (bumpTerm M ρ d)))) := by
    rw [(hC d hdM).2]; unfold vRhs; rw [if_neg (by omega), if_neg (by omega), hm]
    exact sf_ot (isOT_add hV (isOT_omega hWot))
  obtain ⟨s', y', hsy⟩ := omega_psi_form (sumN (one :: (children M d).map (bumpTerm M ρ d)))
  rw [hvd, ← t_add_succ hV (omega_psi_form _) (bumpOmega_ne_one hC hG d), hsy]
  exact lt_add_principal s' y' _

/-- **The seed state is fixed by σ** (t2 の `T2SeedQRRes.σB`): `CL M r = Lc ++ [x]` and
`B = spArg V 0 (Σ o(Lc))` satisfies `σ_{V, V+1}(B) = B`. -/
theorem t_sigmaB {Lc : List Nat} (hCL : CL M r = Lc ++ [x]) :
    sh (ρ.v r) (succ (ρ.v r)) (spArg (ρ.v r) z (sumN (Lc.map ρ.o))) = spArg (ρ.v r) z (sumN (Lc.map ρ.o)) := by
  have hrM : r < M.length := by have := t_rx hX hrx; omega
  have hV : isOT (ρ.v r) = true := hG.ot_v r hrM
  have hV' : isOT (succ (ρ.v r)) = true := isOT_succ hV
  have hVV : ρ.v r < succ (ρ.v r) := lt_succ_self _
  have hmemL : ∀ d ∈ Lc, d ∈ children M r ∧ d < x := by
    intro d hdL
    have hdCL : d ∈ CL M r := by rw [hCL]; exact List.mem_append_left _ hdL
    have hdc : d ∈ children M r := (List.mem_filter.mp hdCL).1
    have hsort : (CL M r).Pairwise (· < ·) := (children_sorted M r).filter _
    rw [hCL, List.pairwise_append] at hsort
    exact ⟨hdc, hsort.2.2 d hdL x (by simp)⟩
  have hl : ∀ t ∈ Lc.map ρ.o, isOT t = true := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hG.ot_o d (mem_children (hmemL d hd).1).2
  have hS := isOT_sumN _ hl
  have hfix : sh (ρ.v r) (succ (ρ.v r)) (sumN (Lc.map ρ.o)) = sumN (Lc.map ρ.o) := by
    rw [sh_sumN hV hV' hVV hl, List.map_map]
    congr 1
    apply List.map_congr_left
    intro d hd
    exact t_child_fix hX hJ hC hG hR hrx hxM he2x he1x he2r hux (hmemL d hd).1 (hmemL d hd).2
  have hlev : ∀ q ∈ summands (sumN (Lc.map ρ.o)), succ (ρ.v r) < lev q := by
    intro q hq
    have hsing : ∀ t ∈ Lc.map ρ.o, Single t := by
      intro t ht
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
      exact single_o hC hG (mem_children (hmemL d hd).1).2
    obtain ⟨d, hdL, rfl⟩ := List.mem_map.mp (summands_sumN_sub hsing q hq)
    obtain ⟨hdc, hdx⟩ := hmemL d hdL
    obtain ⟨y, hy⟩ := o_psi_sub hC (mem_children hdc).2
    rw [hy, lev_psi, sf_ot (hG.ot_v d (mem_children hdc).2)]
    exact t_child_lev hX hJ hC hG hR hrx hxM he2x he1x he2r hux hdc hdx
  have h1 := sh_spArg hV hV' hVV hV (le_refl _) (b := z) rfl hS
    (Or.inr (fun q hq => ne_of_gt (lt_trans hVV (hlev q hq))))
  rw [shf_self, sh_z, hfix] at h1
  rw [← h1]
  exact spArg_level (fun q hq => ⟨hlev q hq, lt_trans hVV (hlev q hq)⟩)

end

/-! ## t2 の設定での形 -/

/-- **`T2SeedQRRes.σB`** in t2's setting (`t = 2`, `q = r`, no upgrade into `x = r + L`,
`CL M r = Lc ++ [x]`). The right side is `t2B (ρ.v r) ρ Lc` unfolded. -/
theorem tame_sigmaB_std {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L)) {Lc : List Nat}
    (hCLM : CL M r = Lc ++ [r + L]) :
    sh (ρ.v r) (succ (ρ.v r)) (spArg (ρ.v r) z (sumN (Lc.map ρ.o))) = spArg (ρ.v r) z (sumN (Lc.map ρ.o)) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hxM : r + L < M.length := by omega
  obtain ⟨he2r, he1x⟩ := par2_facts hX.z2 hxM hr
  have he2x : entry M 2 (r + L) = 1 := by
    obtain ⟨_, _, _, he2, _, _⟩ := (par2_iff M hxM).mp hr
    have h' : entry M 2 r < entry M 2 (r + L) := he2
    have := hX.z2 (r + L); omega
  exact t_sigmaB hX hJ I.cons I.good I.rank hq hxM he2x he1x he2r
    (fun i hu => absurd hu (hXu i)) hCLM

end Ytosk
