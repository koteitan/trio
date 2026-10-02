/-
**背骨の補題: v の呼び出しは背骨の o に依存しない。**

c の真の祖先の列を「背骨」とよぶ。背骨の上（または c）の列 a で、a と c の間の背骨の列の行 1 がすべて
e1(a) 以上（`InvC M c a`）なら、v(a) は c の真の祖先 y の o(y) に依存しない（`not_depS_spine`）。
- a = c なら: v(c) は c の祖先の o に依存しない（ANC）。
- a が c の祖先なら: a と c の間の背骨の列の o にも依存しない（VIS）。

証明: v(a) から届く呼び出しの集合を含む、前向きに閉じた集合 `SpG` を作る。
- 背骨の列 i では v の呼び出しだけで、`InvC M c i`（o の呼び出しは入らない）。
- c とその子孫の列は制限なし。
- 横の枝の列 i は、分岐点 bp（背骨の上、i と c の共通の祖先で最も深いもの）で `InvC M c bp`。
  さらに i が c より左（i < c）なら、bp と i の間に行 1 が e1(bp) 以下の列がある（左の証人）。
  左の証人があると P_1(i) は bp にならないので、枝の最後の列 i から i + 1 への上げが背骨に乗ることはない。
のりしろの辺で背骨の列に落ちることは BumpLeaf で除かれる（行 1 が大きいのりしろの孫は葉）。
実測: C′ の 3000 行列の 126 万組で例外 0（tools 外の scratchpad probe_spine.py）。
-/
import Ytosk.V3ExpT2G

namespace Ytosk

open T

/-! ## 補題 -/

theorem anc0_antisymm {M : Mat} {a b : Nat} (h1 : Anc0 M a b) (h2 : Anc0 M b a) : a = b := by
  have := h1.le; have := h2.le; omega

theorem anc0_of_child {M : Mat} {i c : Nat} (h : c ∈ children M i) : Anc0 M i c :=
  Anc0.step (mem_children_iff.mp h).2 (Anc0.refl i)

/-- **The facts of `P_1`.** -/
theorem par1_facts {M : Mat} {i m : Nat} (hm : par M 1 i = some m) :
    Anc0 M m i ∧ m < i ∧ entry M 1 m < entry M 1 i ∧
      ∀ w, Anc0 M m w → Anc0 M w i → w ≠ m → w ≠ i → entry M 1 i ≤ entry M 1 w := by
  obtain ⟨hmem, hlt, hmax⟩ := (par1_some_iff M i m).mp hm
  refine ⟨anc0_of_mem_ancL hmem, mem_ancL_lt hmem, hlt, fun w h1 h2 h3 h4 => hmax w (mem_ancL_of_anc h2 h4) ?_⟩
  have := h1.le; omega

/-- **The facts of `upg`**: the target is a row-0 child of `P_1`, with the same row 1. -/
theorem upg_facts {M : Mat} {i k : Nat} (hk : upg M i = some k) :
    ∃ m, par M 1 i = some m ∧ par M 0 k = some m ∧ entry M 1 k = entry M 1 i ∧
      (k = i + 1 ∨ (Anc0 M k i ∧ k < i)) := by
  obtain ⟨m, hm1, hm2, hcol, hcase⟩ := upg_spec hk
  refine ⟨m, hm1, par0_of_upgshape hm2 ?_, ?_, hcase⟩
  · have : entry M 0 k = (col M k).1 := rfl; rw [this, hcol]
  · have : entry M 1 k = (col M k).2.1 := rfl; rw [this, hcol]

theorem bump_e1 {M : Mat} {i j : Nat} (h : col M j = bump M i) : entry M 1 j = entry M 1 i := by
  have : entry M 1 j = (col M j).2.1 := rfl
  rw [this]; exact (bump_eq h).2.1

/-- A column of a branch not containing `c` and left of `c` has all its descendants left of `c`. -/
theorem left_desc {M : Mat} {m i c : Nat} (hmi : Anc0 M m i) (hmc : ¬ Anc0 M m c) (hm : m < c) : i < c := by
  by_contra h
  apply hmc
  exact anc_between hmi c (by omega) (by omega)

/-- A child `k` of `j` left of `c` comes before the child `s` of `j` toward `c`. -/
theorem left_child_lt {M : Mat} {j k s c : Nat} (hk : par M 0 k = some j) (hs : par M 0 s = some j)
    (hsc : Anc0 M s c) (hks : k ≠ s) (hkc : k < c) : k < s := by
  by_contra h
  have hsk : s < k := by omega
  have hA : Anc0 M s k := anc_between hsc k (by omega) (by omega)
  have hsj : Anc0 M s j := anc0_par hA (by omega) hk
  have := hsj.le
  have := par_lt M 0 s j hs
  omega

/-! ## 前向きに閉じた集合 -/

/-- The spine condition at `a` below `c`: the spine columns strictly between have row 1 at least `e1(a)`. -/
def InvC (M : Mat) (c a : Nat) : Prop :=
  ∀ w, Anc0 M a w → Anc0 M w c → w ≠ a → w ≠ c → entry M 1 a ≤ entry M 1 w

/-- A side column `i` with branch point `bp`. -/
def SideW (M : Mat) (c i bp : Nat) : Prop :=
  Anc0 M bp c ∧ bp ≠ c ∧ Anc0 M bp i ∧ InvC M c bp ∧ (∀ z, Anc0 M z c → Anc0 M z i → Anc0 M z bp) ∧
    (i < c → ∃ y, Anc0 M bp y ∧ y ≠ bp ∧ Anc0 M y i ∧ entry M 1 y ≤ entry M 1 bp)

/-- **The forward-closed set of calls** (relative to `c`). -/
def SpG (M : Mat) (c : Nat) (b : Bool) (i : Nat) : Prop :=
  (Anc0 M i c → i ≠ c → b = false ∧ InvC M c i) ∧
    (¬ Anc0 M i c → ¬ Anc0 M c i → ∃ bp, SideW M c i bp)

/-- A side column's descendants are side columns with the same branch point. -/
theorem sideW_down {M : Mat} {c i d bp : Nat} (hS : SideW M c i bp) (hic : ¬ Anc0 M i c)
    (hid : Anc0 M i d) : ¬ Anc0 M d c ∧ ¬ Anc0 M c d ∧ SideW M c d bp := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  have hdc : ¬ Anc0 M d c := fun h => hic (Anc0.trans hid h)
  have hcd : ¬ Anc0 M c d := by
    intro h
    rcases anc0_total h hid with h' | h'
    · exact h2 (anc0_antisymm h1 (h5 c (Anc0.refl c) h'))
    · exact hic h'
  refine ⟨hdc, hcd, h1, h2, Anc0.trans h3 hid, h4, fun z hz1 hz2 => ?_, fun hlt => ?_⟩
  · rcases anc0_total hz2 hid with h | h
    · exact h5 z hz1 h
    · exact absurd (Anc0.trans h hz1) hic
  · have hi : i < c := by have := hid.le; omega
    obtain ⟨y, hy1, hy2, hy3, hy4⟩ := h6 hi
    exact ⟨y, hy1, hy2, Anc0.trans hy3 hid, hy4⟩

/-- An upward step `t` of `i` (the target of `P_1` or of an upgrade to an ancestor). -/
def UpS (M : Mat) (t i : Nat) : Prop :=
  Anc0 M t i ∧ t ≠ i ∧ entry M 1 t ≤ entry M 1 i ∧
    ∀ w, Anc0 M t w → Anc0 M w i → w ≠ t → w ≠ i → entry M 1 t ≤ entry M 1 w

theorem upS_par1 {M : Mat} {i m : Nat} (hm : par M 1 i = some m) : UpS M m i := by
  obtain ⟨h1, h2, h3, h4⟩ := par1_facts hm
  exact ⟨h1, by omega, by omega, fun w a b c d => by have := h4 w a b c d; omega⟩

theorem upS_upg {M : Mat} {i k m : Nat} (hm : par M 1 i = some m) (hkm : par M 0 k = some m)
    (he : entry M 1 k = entry M 1 i) (hA : Anc0 M k i) (hki : k < i) : UpS M k i := by
  obtain ⟨_, _, _, h4⟩ := par1_facts hm
  have hmk := par_lt M 0 k m hkm
  refine ⟨hA, by omega, by omega, fun w hw1 hw2 hw3 hw4 => ?_⟩
  have := h4 w (Anc0.trans (Anc0.step hkm (Anc0.refl m)) hw1) hw2 (by have := hw1.le; omega) hw4
  omega

/-- **An upward step stays in the set.** -/
theorem spG_up {M : Mat} {c i t : Nat} (hG : SpG M c false i) (hU : UpS M t i) : SpG M c false t := by
  obtain ⟨hti, hne, hle, hbw⟩ := hU
  refine ⟨fun htc htc' => ⟨rfl, ?_⟩, fun htc hct => ?_⟩
  · -- `t` on the spine
    by_cases hic : Anc0 M i c
    · by_cases hic' : i = c
      · subst hic'
        intro w hw1 hw2 hw3 hw4
        exact hbw w hw1 hw2 hw3 hw4
      · have hI := (hG.1 hic hic').2
        intro w hw1 hw2 hw3 hw4
        rcases anc0_total hw2 hic with h | h
        · by_cases hwi : w = i
          · subst hwi; exact hle
          · exact hbw w hw1 h hw3 hwi
        · by_cases hwi : w = i
          · subst hwi; exact hle
          · exact le_trans hle (hI w h hw2 (Ne.symm hwi |> fun h' => fun h'' => h' h''.symm) hw4)
    · by_cases hci : Anc0 M c i
      · intro w hw1 hw2 hw3 hw4
        have hwi : w ≠ i := by
          intro h; subst h; exact hw4 (anc0_antisymm hw2 hci)
        exact hbw w hw1 (Anc0.trans hw2 hci) hw3 hwi
      · -- `i` on a side branch: `t` is at or above the branch point
        obtain ⟨bp, h1, h2, h3, h4, h5, h6⟩ := hG.2 hic hci
        have htbp : Anc0 M t bp := h5 t htc hti
        intro w hw1 hw2 hw3 hw4
        rcases anc0_total hw2 h1 with h | h
        · -- `w` at or above `bp`
          by_cases hwbp : w = bp
          · subst hwbp
            exact hbw w hw1 h3 hw3 (by intro h'; subst h'; exact hic hw2)
          · exact hbw w hw1 (Anc0.trans h h3) hw3 (by intro h'; subst h'; exact hic hw2)
        · -- `w` strictly below `bp`
          by_cases hwbp : w = bp
          · subst hwbp
            exact hbw w hw1 h3 hw3 (by intro h'; subst h'; exact hic hw2)
          · have hbpt : t ≠ bp ∨ t = bp := by tauto
            rcases hbpt with htb | htb
            · have hb := hbw bp htbp h3 (Ne.symm htb) (by intro h'; subst h'; exact hic h1)
              exact le_trans hb (h4 w h hw2 hwbp hw4)
            · subst htb; exact h4 w h hw2 hw3 hw4
  · -- `t` on a side branch: so is `i`, with the same branch point
    have hic : ¬ Anc0 M i c := fun h => htc (Anc0.trans hti h)
    have hci : ¬ Anc0 M c i := by
      intro h
      rcases anc0_total h hti with h' | h'
      · exact hct h'
      · exact htc h'
    obtain ⟨bp, h1, h2, h3, h4, h5, h6⟩ := hG.2 hic hci
    have hbpt : Anc0 M bp t := by
      rcases anc0_total h3 hti with h | h
      · exact h
      · exact absurd (Anc0.trans h h1) htc
    refine ⟨bp, h1, h2, hbpt, h4, fun z hz1 hz2 => h5 z hz1 (Anc0.trans hz2 hti), fun htlt => ?_⟩
    have hilt : i < c := left_desc hti htc htlt
    obtain ⟨y, hy1, hy2, hy3, hy4⟩ := h6 hilt
    rcases anc0_total hy3 hti with h | h
    · exact ⟨y, hy1, hy2, h, hy4⟩
    · -- `y` strictly below `t`: then `t` is a witness
      have htbp : t ≠ bp := by intro h'; subst h'; exact htc h1
      refine ⟨t, hbpt, htbp, Anc0.refl t, ?_⟩
      by_cases hyt : y = t
      · subst hyt; exact hy4
      · by_cases hyi : y = i
        · subst hyi; exact le_trans hle hy4
        · exact le_trans (hbw y h hy3 hyt hyi) hy4

/-- **An `o` call moves to a counted child, and a `v` call is reached from an `o` call.** -/
theorem spG_child {M : Mat} {c i d : Nat} (hG : SpG M c true i) (hd : Anc0 M i d) : SpG M c true d := by
  refine ⟨fun hdc hdc' => ?_, fun hdc hcd => ?_⟩
  · have hic : Anc0 M i c := Anc0.trans hd hdc
    have hic' : i ≠ c := by intro h; subst h; exact hdc' (anc0_antisymm hdc hd)
    exact absurd (hG.1 hic hic').1 (by simp)
  · have hic : ¬ Anc0 M i c := by
      intro h
      by_cases hic' : i = c
      · subst hic'; exact hcd hd
      · exact absurd (hG.1 h hic').1 (by simp)
    have hci : ¬ Anc0 M c i := fun h => hcd (Anc0.trans h hd)
    obtain ⟨bp, hS⟩ := hG.2 hic hci
    exact ⟨bp, (sideW_down hS hic hd).2.2⟩

theorem spG_ov {M : Mat} {c i : Nat} (hG : SpG M c true i) : SpG M c false i :=
  ⟨fun h h' => absurd (hG.1 h h').1 (by simp), hG.2⟩

/-- **The upgrade to the next column stays in the set.** -/
theorem spG_next {M : Mat} {c i m : Nat} (hG : SpG M c false i) (hm : par M 1 i = some m)
    (hpm : par M 0 (i + 1) = some m) : SpG M c false (i + 1) := by
  have hU := upS_par1 hm
  obtain ⟨hmi, hmi', _, _⟩ := hU
  have hmlt : m < i := by have := hmi.le; omega
  have hmc1 : Anc0 M m (i + 1) := Anc0.step hpm (Anc0.refl m)
  -- the child `i + 1` of `m` with `m` on the spine, right of `c`: a side column with branch point `m`
  have hside : ∀ (hmc : Anc0 M m c) (hmc' : m ≠ c) (hic : c < i + 1), SpG M c false m →
      SpG M c false (i + 1) := by
    intro hmc hmc' hic hGm
    refine ⟨fun h _ => absurd h.le (by omega), fun h1 h2 => ⟨m, hmc, hmc', hmc1, (hGm.1 hmc hmc').2,
      fun z hz1 hz2 => ?_, fun h => absurd h (by omega)⟩⟩
    by_cases hz : z = i + 1
    · subst hz; exact absurd hz1 h1
    · exact anc0_par hz2 hz hpm
  have hl : i + 1 < M.length := by
    by_contra h; rw [par0_out' (by omega)] at hpm; cases hpm
  by_cases hic : Anc0 M i c
  · by_cases hic' : i = c
    · subst hic'
      exact hside hmi (by omega) (by omega) (spG_up hG (upS_par1 hm))
    · exfalso
      have hii : Anc0 M i (i + 1) := anc_between hic (i + 1) (by omega) (by
        have := hic.le; omega)
      have := anc0_par hii (by omega) hpm
      have := anc0_antisymm this hmi
      omega
  · by_cases hci : Anc0 M c i
    · rcases anc0_total hmi hci with h | h
      · by_cases hmc : m = c
        · subst hmc
          exact ⟨fun h1 h2 => absurd (anc0_antisymm h1 hmc1) h2, fun _ h2 => absurd hmc1 h2⟩
        · exact hside h hmc (by have := hci.le; omega) (spG_up hG (upS_par1 hm))
      · exact ⟨fun h1 h2 => absurd (anc0_antisymm h1 (Anc0.trans h hmc1)) h2,
          fun _ h2 => absurd (Anc0.trans h hmc1) h2⟩
    · obtain ⟨bp, h1, h2, h3, h4, h5, h6⟩ := hG.2 hic hci
      have hine : i ≠ c := fun e => hic (by rw [e]; exact Anc0.refl c)
      by_cases hmb : Anc0 M m bp
      · -- `m` at or above `bp`
        have hil : c < i := by
          by_contra hlt
          have hic2 : i < c := by omega
          by_cases hmbp : m = bp
          · subst hmbp
            obtain ⟨y, hy1, hy2, hy3, hy4⟩ := h6 hic2
            obtain ⟨_, _, hlt, hbw⟩ := par1_facts hm
            by_cases hyi : y = i
            · subst hyi; omega
            · have := hbw y hy1 hy3 hy2 hyi; omega
          · -- the child `s` of `m` toward `bp` contains `i` and `c` but not `i + 1`
            obtain ⟨s, hs1, hs2⟩ := anc0_child hmb hmbp
            have hsc : Anc0 M s c := Anc0.trans hs2 h1
            have hsi : Anc0 M s i := Anc0.trans hs2 h3
            have hsi1 : Anc0 M s (i + 1) := anc_between hsc (i + 1) (by have := hsi.le; omega) (by omega)
            have hsm := anc0_par hsi1 (by have := hsi.le; omega) hpm
            have := hsm.le
            have := par_lt M 0 s m hs1
            omega
        have hGm := spG_up hG (upS_par1 hm)
        have hmc : Anc0 M m c := Anc0.trans hmb h1
        have hmc' : m ≠ c := by intro h'; subst h'; exact h2 (anc0_antisymm h1 hmb)
        exact hside hmc hmc' (by omega) hGm
      · -- `m` strictly below `bp`: a side column, and so is its child `i + 1`
        have hbm : Anc0 M bp m := (anc0_total hmi h3).resolve_left hmb
        have hmc : ¬ Anc0 M m c := fun h' => hmb (h5 m h' hmi)
        have hcm : ¬ Anc0 M c m := fun h' => hci (Anc0.trans h' hmi)
        have hGm := spG_up hG (upS_par1 hm)
        obtain ⟨bp', hS'⟩ := hGm.2 hmc hcm
        obtain ⟨h1', h2', h3'⟩ := sideW_down hS' hmc hmc1
        exact ⟨fun h'' => absurd h'' h1', fun _ _ => ⟨bp', h3'⟩⟩

/-- **The bump edge stays in the set** (BumpLeaf: a bump grandchild with row 1 at least that of the
grandparent is a leaf and the last child). -/
theorem spG_bump {M : Mat} (hBL : BumpLeaf M) {c i j k : Nat} (hG : SpG M c false i)
    (hj : j ∈ children M i) (hjb : col M j = bump M i) (hk : k ∈ children M j) : SpG M c true k := by
  have hij : Anc0 M i j := anc0_of_child hj
  have hjk : Anc0 M j k := anc0_of_child hk
  have hik : Anc0 M i k := Anc0.trans hij hjk
  have hpj := (mem_children_iff.mp hj).2
  have hpk := (mem_children_iff.mp hk).2
  have hjlt := par_lt M 0 j i hpj
  have hklt := par_lt M 0 k j hpk
  have he1j := bump_e1 hjb
  by_cases hic : Anc0 M i c
  · by_cases hic' : i = c
    · subst hic'
      exact ⟨fun h1 h2 => absurd (anc0_antisymm h1 hik) h2, fun _ h2 => absurd hik h2⟩
    · have hI := (hG.1 hic hic').2
      -- `k` is not on the spine
      have hkc : ¬ (Anc0 M k c ∧ k ≠ c) := by
        rintro ⟨h1, h2⟩
        have hle := hI k hik h1 (by omega) h2
        obtain ⟨_, hnil, _, _⟩ := hBL i j k hj hjb hk hle
        exact h2 (anc0_leaf hnil h1).symm
      refine ⟨fun h1 h2 => absurd ⟨h1, h2⟩ hkc, fun hkc' hck => ?_⟩
      by_cases hjc : Anc0 M j c
      · have hjc' : j ≠ c := by intro h; subst h; exact hck hjk
        refine ⟨j, hjc, hjc', hjk, fun w hw1 hw2 hw3 hw4 => ?_, fun z hz1 hz2 => ?_, fun hkl => ?_⟩
        · rw [he1j]
          exact hI w (Anc0.trans hij hw1) hw2 (by have := hw1.le; omega) hw4
        · by_cases hz : z = k
          · subst hz; exact absurd hz1 hkc'
          · exact anc0_par hz2 hz hpk
        · -- a left bump grandchild is not the last child of `j`: its row 1 is below
          refine ⟨k, hjk, by omega, Anc0.refl k, ?_⟩
          by_contra hlt
          have hle : entry M 1 i ≤ entry M 1 k := by omega
          obtain ⟨_, _, hlast, _⟩ := hBL i j k hj hjb hk hle
          obtain ⟨s, hs1, hs2⟩ := anc0_child hjc hjc'
          have hks : k ≠ s := by intro h; subst h; exact hkc' hs2
          have hksl := left_child_lt hpk hs1 hs2 hks hkl
          have hsl : s < M.length := by
            by_contra h; rw [par0_out' (by omega)] at hs1; cases hs1
          have hsj : s ∈ children M j := mem_children_iff.mpr ⟨hsl, hs1⟩
          have := last_le (children_sorted M j) hlast s hsj
          omega
      · refine ⟨i, hic, hic', hik, hI, fun z hz1 hz2 => ?_, fun _ => ⟨j, hij, by omega, hjk, by omega⟩⟩
        by_cases hz : z = k
        · subst hz; exact absurd hz1 hkc'
        · have hzj := anc0_par hz2 hz hpk
          by_cases hzj' : z = j
          · subst hzj'; exact absurd hz1 hjc
          · exact anc0_par hzj hzj' hpj
  · by_cases hci : Anc0 M c i
    · have hck : Anc0 M c k := Anc0.trans hci hik
      exact ⟨fun h1 h2 => absurd (anc0_antisymm h1 hck) h2, fun _ h2 => absurd hck h2⟩
    · obtain ⟨bp, hS⟩ := hG.2 hic hci
      obtain ⟨h1, h2, h3⟩ := sideW_down hS hic hik
      exact ⟨fun h => absurd h h1, fun _ _ => ⟨bp, h3⟩⟩

/-- **The calls depending on `o(y)` (`y` a proper ancestor of `c`) are outside the set.** -/
theorem spG_noreach {M : Mat} (hBL : BumpLeaf M) {c y : Nat} (hy : Anc0 M y c) (hyc : y ≠ c) :
    ∀ {b i}, DepS M (SR y) b i → SpG M c b i → False := by
  intro b i h
  induction h with
  | @seed b i hs =>
    intro hG
    rcases hs with ⟨hb, hi⟩
    subst hb; subst hi
    exact absurd (hG.1 hy hyc).1 (by simp)
  | ochild hc _ _ _ ih => intro hG; exact ih (spG_child hG (anc0_of_child hc))
  | ov _ ih => intro hG; exact ih (spG_ov hG)
  | vpar _ hm _ ih => intro hG; exact ih (spG_up hG (upS_par1 hm))
  | @vupg i k _ _ hk _ ih =>
    intro hG
    obtain ⟨m, hm, hkm, he, hcase⟩ := upg_facts hk
    rcases hcase with hk1 | ⟨hA, hki⟩
    · subst hk1; exact ih (spG_next hG hm hkm)
    · exact ih (spG_up hG (upS_upg hm hkm he hA hki))
  | vbump _ _ hj hjb hk _ ih => intro hG; exact ih (spG_bump hBL hG hj hjb hk)

/-- **The spine lemma**: if every spine column strictly between `a` and `c` has row 1 at least `e1(a)`,
then `v(a)` depends on no `o(y)` with `y` a proper ancestor of `c`. -/
theorem not_depS_spine {M : Mat} (hBL : BumpLeaf M) {a c y : Nat} (hac : Anc0 M a c) (hI : InvC M c a)
    (hy : Anc0 M y c) (hyc : y ≠ c) : ¬ DepS M (SR y) false a := by
  intro h
  apply spG_noreach hBL hy hyc h
  refine ⟨fun _ _ => ⟨rfl, hI⟩, fun h1 _ => absurd hac h1⟩

/-- **ANC**: `v(a)` depends on no `o` of a proper ancestor of `a`. -/
theorem not_depS_anc {M : Mat} (hBL : BumpLeaf M) {a y : Nat} (hy : Anc0 M y a) (hya : y ≠ a) :
    ¬ DepS M (SR y) false a :=
  not_depS_spine hBL (Anc0.refl a) (fun _ h1 h2 h3 _ => absurd (anc0_antisymm h1 h2) (Ne.symm h3)) hy hya

end Ytosk
