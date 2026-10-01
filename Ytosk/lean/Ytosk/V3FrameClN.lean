/-
**3 行・t = 1: 展開 N = M[n] の貼り合わせの評価も FrameClosed（書き換える枠の頭は閉じている）。**

枠の頭（v(i) と頭の値）は x より前で M と同じ、x 以後で M[n − 1] の写し（`frameHead_lt`・`frameHead_copy`、
FrameOT の証明と同じ）。枠の子 c の値が変わるのは D の列だけ:
- c の値 ψ_s(y)（y ≠ 0）は fsD で ψ_s(y′)（y′ ≤ y）になる（`fsD_psi_shape`）。引き金は M の枠でも立つ（`trig_back_fsD`）。
- c の値が Ω_{t+1}（x、または D の葉）なら新しい値は Ω_{t+1} 以下で、引き金が立つなら v(i) ≤ t（`trig_back_succ`）。
  このとき頭が閉じているのは新しい不変条件 FrameClosedHi（高い子 o(c) ≥ Ω_{v(i)+1} の前の頭は閉じている）から
  （その特別な場合 FrameClosedOm）。FrameClosedHi は到達可能な行列の高い枠 41 万で例外 0、崩れるのは低くて引き金の
  ない枠だけ。値は下がるだけなので、FrameClosedHi は M[n] と M.take x に渡る（`frameClosedHi_N_t1`・`frameClosedHi_take`）。
-/
import Ytosk.V3FrameOTN
import Ytosk.V3MainT1D
import Ytosk.V3DropPres

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **New invariant**: the head before a counted child of value `Ω_{t+1}` with `v(i) ≤ t` is closed. -/
def FrameClosedOm (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL M i = L ++ c :: R → ∀ t,
    ρ.o c = psi (succ t) z z → ¬ lt t (ρ.v i) = true →
    Closed (ρ.v i) (spArg (ρ.v i) z (sumN (L.map ρ.o)))

/-! ## 順序数の補題: 値が下がっても引き金は戻る -/

/-- `fsD` of `ψ_s(y)` with `y ≠ 0`, when single, keeps the subscript. -/
theorem fsD_psi_shape {s y η s' y' : T} (hy : y ≠ z) (h : fsD (psi s y z) η = psi s' y' z) : s' = s := by
  unfold fsD at h
  rw [if_neg hy] at h
  split at h
  · cases hk : count η with
    | zero => rw [hk] at h; simp [mulT] at h
    | succ k =>
      rw [hk] at h
      simp only [mulT, app] at h
      exact (T.psi.inj h).1.symm
  · split at h <;> exact (T.psi.inj h).1.symm

/-- A trigger at a value below `Ω_{t+1}` forces `v(i) ≤ t`. -/
theorem trig_back_succ {a B t o' s' y' : T} (hle : o' ≤ psi (succ t) z z) (ho : o' = psi s' y' z)
    (ht : lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) : ¬ lt t a = true := by
  subst ho
  have h1 : B < y' := ht.1
  have h2 : psi a z z < psi s' y' z := ht.2
  have hs : s' ≤ t := by
    rcases (le_iff _ _).mp hle with hlt | heq
    · rcases psi_lt_psi_z_iff.mp hlt with h | ⟨_, h⟩
      · exact lt_succ_iff.mp h
      · exact absurd h (not_lt_z _)
    · obtain ⟨_, hy, _⟩ := T.psi.inj heq; subst hy; exact absurd h1 (not_lt_z _)
  have ha : a ≤ s' := by
    rcases psi_lt_psi_z_iff.mp h2 with h | ⟨h, _⟩
    · exact le_of_lt h
    · rw [h]
  intro hta
  exact absurd (lt_of_lt_of_le (show t < a from hta) (le_trans ha hs)) (lt_irrefl _)

/-- **The trigger at the lowered value `fsD(ψ_s(y), ζ)` goes back** to the trigger at `ψ_s(y)`, or the old
value is `Ω_{t+1}` with `v(i) ≤ t`. -/
theorem trig_back_fsD {a B s y ζ s' y' : T} (hle : fsD (psi s y z) ζ ≤ psi s y z)
    (ho : fsD (psi s y z) ζ = psi s' y' z) (ht : lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) :
    (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) ∨
      (∃ t, s = succ t ∧ y = z ∧ ¬ lt t a = true) := by
  by_cases hy : y = z
  · subst hy
    by_cases hs0 : s = z
    · subst hs0; unfold fsD at ho; simp at ho
    by_cases hss : isSucc s = true
    · right
      have hs' : s = succ (init s) := (init_app_one hss).symm
      refine ⟨init s, hs', rfl, ?_⟩
      rw [fsD_leaf hss hs0] at hle ho
      rw [hs'] at hle
      exact trig_back_succ hle ho ht
    · rw [fsD_sub hs0 (by simpa using hss)] at ho
      obtain ⟨_, hy', _⟩ := T.psi.inj ho
      subst hy'
      exact absurd ht.1 (not_lt_z B)
  · left
    have hs := fsD_psi_shape hy ho
    subst hs
    rw [ho] at hle
    have hyy : y' ≤ y := by
      rcases (le_iff _ _).mp hle with hlt | heq
      · rcases psi_lt_psi_z_iff.mp hlt with h | ⟨_, h⟩
        · exact absurd h (lt_irrefl _)
        · exact le_of_lt h
      · obtain ⟨_, h, _⟩ := T.psi.inj heq; rw [h]
    have hpp : psi s' y' z ≤ psi s' y z := by
      rcases (le_iff _ _).mp hyy with h | h
      · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h⟩))
      · rw [h]
    exact ⟨lt_of_lt_of_le (show B < y' from ht.1) hyy,
      lt_of_lt_of_le (show psi a z z < psi s' y' z from ht.2) hpp⟩

/-- **New invariant** (stronger, carried by monotonicity): the head before a high counted child
(`o(c) ≥ Ω_{v(i)+1}`) is closed. 到達可能な行列の高い枠 41 万で例外 0（崩れるのは低くて引き金のない枠だけ）。 -/
def FrameClosedHi (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL M i = L ++ c :: R →
    psi (succ (ρ.v i)) z z ≤ ρ.o c → Closed (ρ.v i) (spArg (ρ.v i) z (sumN (L.map ρ.o)))

theorem frameClosedOm_of_hi {M : Mat} {ρ : Valn} (h : FrameClosedHi M ρ) : FrameClosedOm M ρ := by
  intro i hi L c R hCL t hc hnt
  apply h i hi L c R hCL
  rw [hc]
  have hvt : ρ.v i ≤ t := not_lt.mp hnt
  have hs : succ (ρ.v i) ≤ succ t := succ_le_of_lt (lt_succ_iff.mpr hvt)
  rcases (le_iff _ _).mp hs with h' | h'
  · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h'))
  · rw [h']

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- The frame head of `M[n]` before `x` is that of `M`. -/
theorem frameHead_lt (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {Z : Nat → T} (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i) {i : Nat} (h : i < r + L) {Lc : List Nat} {c : Nat} {R : List Nat}
    (hCL : CL (TRIO.gexp M r L d0 0 n) i = Lc ++ c :: R) :
    CL M i = Lc ++ c :: R ∧ (glueZ M (r + L) ρ (shiftV ρP L) Z).v i = ρ.v i ∧
      Lc.map (glueZ M (r + L) ρ (shiftV ρP L) Z).o = Lc.map ρ.o := by
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
  have hS := hSA i h
  have hCLe : CL (TRIO.gexp M r L d0 0 n) i = CL M i := by
    unfold CL; rw [hS.ch]
    apply List.filter_congr
    intro c hc
    exact decide_eq_decide.mpr (counted_iff_of_cnt (hS.cnt c hc))
  rw [hCLe] at hCL
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcch : c ∈ children M i := (List.mem_filter.mp hcCL).1
  have hccnt : Counted M i c := by simpa using (List.mem_filter.mp hcCL).2
  -- `v(i)` does not change: otherwise `i` has no counted child
  have hvd : ¬ DepX M (r + L) false i := by
    intro hv
    rcases hOS i h (DepX.ov hv) with ⟨_, hnc⟩ | ⟨hnv, _⟩
    · rcases hnc c hcch with h' | h'
      · exact hccnt.1 h'
      · exact hccnt.2 h'
    · exact hnv hv
  -- the head of the frame avoids `D`
  have hLd : ∀ d ∈ Lc, ¬ DepX M (r + L) true d := by
    intro d hd hdD
    have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
    have hdch : d ∈ children M i := (List.mem_filter.mp hdCL).1
    have hdcnt : Counted M i d := by simpa using (List.mem_filter.mp hdCL).2
    have hdc : d < c := by
      have hs : (CL M i).Pairwise (· < ·) := (children_sorted M i).filter _
      rw [hCL] at hs
      exact (List.pairwise_append.mp hs).2.2 d hd c List.mem_cons_self
    have hiD : DepX M (r + L) true i := DepX.ochild hdch hdcnt.1 hdcnt.2 hdD
    rcases hOS i h hiD with ⟨hv, _⟩ | ⟨_, L', c', R', hch, _, _, hR', hL'⟩
    · exact hvd hv
    · have hdc' : d = c' := by
        rw [hch] at hdch
        rcases List.mem_append.mp hdch with h' | h'
        · exact absurd hdD (hL' d h' hdcnt)
        · rcases List.mem_cons.mp h' with h' | h'
          · exact h'
          · rcases hR' d h' with h'' | h''
            · exact absurd h'' hdcnt.1
            · exact absurd h'' hdcnt.2
      subst hdc'
      have hsort := children_sorted M i
      rw [hch] at hsort hcch
      rcases List.mem_append.mp hcch with h' | h'
      · have := (List.pairwise_append.mp hsort).2.2 c h' d List.mem_cons_self
        omega
      · rcases List.mem_cons.mp h' with h' | h'
        · omega
        · rcases hR' c h' with h'' | h''
          · exact hccnt.1 h''
          · exact hccnt.2 h''
  have hLo : Lc.map σ.o = Lc.map ρ.o := by
    apply List.map_congr_left
    intro d hd
    have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
    have hdM := (mem_children (List.mem_filter.mp hdCL).1).2
    have hdx : d < r + L := by
      rcases Nat.lt_or_ge d (r + L) with h' | h'
      · exact h'
      · exfalso
        have : d = r + L := by omega
        exact hLd d hd (this ▸ DepX.leaf)
    rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hdx (hLd d hd)]
  exact ⟨hCL, by rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z h hvd], hLo⟩


/-- The frame head of a copy column of `M[n]` is that of `M[n − 1]`. -/
theorem frameHead_copy (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {Z : Nat → T} (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i) {a : Nat} (ha : a < (n - 1) * L) {Lc : List Nat} {c : Nat} {R : List Nat}
    (hCL : CL (TRIO.gexp M r L d0 0 n) (r + L + a) = Lc ++ c :: R) :
    ∃ Lc' c' R', CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = Lc' ++ c' :: R' ∧
      (glueZ M (r + L) ρ (shiftV ρP L) Z).v (r + L + a) = ρP.v (r + a) ∧
      Lc.map (glueZ M (r + L) ρ (shiftV ρP L) Z).o = Lc'.map ρP.o ∧
      (glueZ M (r + L) ρ (shiftV ρP L) Z).o c = ρP.o c' := by
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
  have hCLs : CL (TRIO.gexp M r L d0 0 n) (r + L + a) =
      (CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a)).map (· + L) := by
    unfold CL
    rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha, List.filter_map]
    congr 1
    apply List.filter_congr
    intro d hd
    have hdc := mem_children hd
    rw [hlP] at hdc
    show decide (Counted (TRIO.gexp M r L d0 0 n) (r + L + a) (d + L)) =
      decide (Counted (TRIO.gexp M r L d0 0 (n - 1)) (r + a) d)
    apply decide_eq_decide.mpr
    apply counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath hz2 (ρ := ρ) (Z := Z) ha hd)
    · have := hσo (d - r); rw [show r + L + (d - r) = d + L by omega,
        show r + (d - r) = d by omega] at this
      exact this
    · obtain ⟨s, y, he⟩ := o_psi_form hCP (i := d) (by rw [hlP]; omega)
      rw [he]; simp
  rw [hCLs] at hCL
  obtain ⟨Lc', T', hsplit, hLc, hT⟩ := List.map_eq_append_iff.mp hCL
  obtain ⟨c', R', hT', hc', hR⟩ := List.map_eq_cons_iff.mp hT
  subst hLc hc' hR
  rw [hT'] at hsplit
  have hLo : (Lc'.map (· + L)).map σ.o = Lc'.map ρP.o := by
    rw [List.map_map]
    apply List.map_congr_left
    intro d hd
    have hdCL : d ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp [hd]
    have hdc := mem_children (List.mem_filter.mp hdCL).1
    have := hσo (d - r)
    rw [show r + L + (d - r) = d + L by omega, show r + (d - r) = d by omega] at this
    exact this
  refine ⟨Lc', c', R', hsplit, hσv a, hLo, ?_⟩
  have hcCL : c' ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp
  have hcc := mem_children (List.mem_filter.mp hcCL).1
  have := hσo (c' - r)
  rw [show r + L + (c' - r) = c' + L by omega, show r + (c' - r) = c' by omega] at this
  exact this



/-- **FrameClosed passes to the glued valuation of `M[n]`** (`t = 1`), given FrameClosedOm of `M`. -/
theorem frameClosed_N_t1 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {Z : Nat → T} (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (hC : Cons M ρ) (hFC : FrameClosed M ρ) (hFCO : FrameClosedOm M ρ)
    (hFCP : FrameClosed (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hle : ∀ c, c < r + L → DepX M (r + L) true c → fsD (ρ.o c) (Z c) ≤ ρ.o c)
    (hlex : ρP.o r ≤ ρ.o (r + L)) (hox : ∃ t, ρ.o (r + L) = psi (succ t) z z) :
    FrameClosed (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) := by
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  intro i hi Lc c R hCL s y hc ht
  rcases Nat.lt_or_ge i (r + L) with h | h
  · obtain ⟨hCLM, hv, hLo⟩ := frameHead_lt hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hCP hOS h hCL
    rw [hv, hLo] at ht ⊢
    have hcCL : c ∈ CL M i := by rw [hCLM]; simp
    have hcM := mem_children (List.mem_filter.mp hcCL).1
    have hiM : i < M.length := by omega
    obtain ⟨s0, y0, h0⟩ := o_psi_form hC hcM.2
    by_cases hcx : c = r + L
    · rw [hcx] at hc hCLM
      rw [glueZ_o_ge ρ (shiftV ρP L) Z (le_refl _)] at hc
      have hc' : ρP.o r = psi s y z := by
        have : (shiftV ρP L).o (r + L) = ρP.o r := by show ρP.o (r + L - L) = _; rw [Nat.add_sub_cancel]
        rw [← this]; exact hc
      obtain ⟨t, hto⟩ := hox
      have hnt := trig_back_succ (by rw [← hto]; exact hlex) hc' ht
      exact hFCO i hiM Lc (r + L) R hCLM t hto hnt
    · have hcx' : c < r + L := by omega
      by_cases hd : DepX M (r + L) true c
      · rw [glueZ_o_dep ρ (shiftV ρP L) Z hcx' hd, h0] at hc
        have hl := hle c hcx' hd
        rw [h0] at hl
        rcases trig_back_fsD hl hc ht with htM | ⟨t, hst, hy0, hnt⟩
        · exact hFC i hiM Lc c R hCLM s0 y0 h0 htM
        · exact hFCO i hiM Lc c R hCLM t (by rw [h0, hst, hy0]) hnt
      · rw [glueZ_o_lt ρ (shiftV ρP L) Z hcx' hd] at hc
        exact hFC i hiM Lc c R hCLM s y hc ht
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    obtain ⟨Lc', c', R', hsp, hv, hLo, hco⟩ :=
      frameHead_copy hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hCP hOS ha hCL
    rw [hv, hLo] at ht ⊢
    rw [hco] at hc
    exact hFCP (r + a) (by rw [hlP]; omega) Lc' c' R' hsp s y hc ht


/-- **FrameClosedHi passes to the glued valuation of `M[n]`** (`t = 1`): every value up to `x` only drops, so
a high frame of `M[n]` is high in `M`. -/
theorem frameClosedHi_N_t1 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {Z : Nat → T} (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (hFH : FrameClosedHi M ρ) (hFHP : FrameClosedHi (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hle : ∀ c, c < r + L → DepX M (r + L) true c → fsD (ρ.o c) (Z c) ≤ ρ.o c)
    (hlex : ρP.o r ≤ ρ.o (r + L)) :
    FrameClosedHi (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) := by
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  intro i hi Lc c R hCL hhi
  rcases Nat.lt_or_ge i (r + L) with h | h
  · obtain ⟨hCLM, hv, hLo⟩ := frameHead_lt hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hCP hOS h hCL
    rw [hv, hLo] at ⊢
    rw [hv] at hhi
    have hcCL : c ∈ CL M i := by rw [hCLM]; simp
    have hcM := mem_children (List.mem_filter.mp hcCL).1
    have hiM : i < M.length := by omega
    have hcle : (glueZ M (r + L) ρ (shiftV ρP L) Z).o c ≤ ρ.o c := by
      rcases Nat.lt_or_ge c (r + L) with hc | hc
      · by_cases hd : DepX M (r + L) true c
        · rw [glueZ_o_dep ρ (shiftV ρP L) Z hc hd]; exact hle c hc hd
        · rw [glueZ_o_lt ρ (shiftV ρP L) Z hc hd]
      · have : c = r + L := by omega
        subst this
        rw [glueZ_o_ge ρ (shiftV ρP L) Z (le_refl _)]
        show ρP.o (r + L - L) ≤ _
        rw [Nat.add_sub_cancel]; exact hlex
    exact hFH i hiM Lc c R hCLM (le_trans hhi hcle)
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    obtain ⟨Lc', c', R', hsp, hv, hLo, hco⟩ :=
      frameHead_copy hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hCP hOS ha hCL
    rw [hv, hLo] at ⊢
    rw [hv, hco] at hhi
    exact hFHP (r + a) (by rw [hlP]; omega) Lc' c' R' hsp hhi

end

end Ytosk

namespace Ytosk

open T

/-- **FrameClosed and FrameClosedHi are carried together** (`t = 1`). -/
theorem expStep_frameClosed_t1 {M : Mat} {r L d0 q : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some q)
    {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (hFC : FrameClosed M ρ) (hFH : FrameClosedHi M ρ) :
    ExpStepT1 (fun N σ => FrameClosed N σ ∧ FrameClosedHi N σ) M r L d0 ρ := by
  have hFCO := frameClosedOm_of_hi hFH
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP Z hCP _ hFCP _ _ _ _ hle hlex _
  have hxnb := hxnb_t1 hlen hL hA hd0e hZ2 hZ1 h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn
  have hOS := hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq
  exact ⟨frameClosed_N_t1 hlen hL hA hd0e hn hpath hx2 hxnb (hZ2 r) hiu hiux hCP hOS hC hFC hFCO hFCP.1
      (fun c hc hd => (hle c hc hd).1) hlex.1 hox,
    frameClosedHi_N_t1 hlen hL hA hd0e hn hpath hx2 hxnb (hZ2 r) hiu hiux hCP hOS hFH hFCP.2
      (fun c hc hd => (hle c hc hd).1) hlex.1⟩

end Ytosk

namespace Ytosk

open T

/-- **FrameClosedHi passes to `M.take x`** with any valuation that lowers the values (the drop):
the frames of `M.take x` extend those of `M` with the same head (`frame_take`). -/
theorem frameClosedHi_take {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk) (hle : ∀ i, i < x → ρ'.o i ≤ ρ.o i)
    (hFH : FrameClosedHi M ρ) : FrameClosedHi (M.take x) ρ' := by
  intro i hi L c R h hhi
  have hlT : (M.take x).length = x := by rw [List.length_take]; omega
  rw [hlT] at hi
  obtain ⟨hv, hL, Tl, hM⟩ := frame_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi h
  rw [hv, hL]
  rw [hv] at hhi
  have hcT : c ∈ CL (M.take x) i := by rw [h]; simp
  have hcx : c < x := by
    have := (mem_children (List.mem_filter.mp hcT).1).2; rw [hlT] at this; exact this
  exact hFH i (by omega) L c (R ++ Tl) hM (le_trans hhi (hle c hcx))

end Ytosk

