/-
**WfExQ4 (2026-11-01): PH3cG and FC3 through the DQ copy (part of `CarryV3`, WfExQ2).**

The old carry `G.frameQR_N_t1` (glueZ, `D` values `fsD(old, Z)`) uses the `D` values only through
`trig_back_fsD`: a triggered frame of the new value is either triggered in `M` with the same subscript and a
smaller argument, or comes from a leaf `Ω_{t+1}`.  `trig_back_DQ` is the same statement for any `DQ` value:
- `base` is `fsD` (old lemma); `sub` gives argument `0` (never triggered); `arg` keeps the subscript and lowers the
  argument (`DQ.lt`).
`frameQR_N_t1Q` is the copy of `frameQR_N_t1` for `glueQ` with `DQ` values; `expStepQR_ph3c` / `expStepQR_fc3`
carry PH3cG / FC3 along the q = r chain, given the leaf residual `hOm` (frames of `M` whose child is a leaf
`Ω_{t+1}` with `v(i) ≤ t`, at the new value; for `glueZ` this was `frameQROmN_t1S`).
-/
import Ytosk.WfExQ2
import Ytosk.V3PT1G

namespace Ytosk.WfExQ4
open T Ytosk Ytosk.G Ytosk.WfExQ1 Ytosk.WfExQ2 Ytosk.WfQrL1 Ytosk.WfQrL7

set_option linter.unusedSectionVars false

/-- **The trigger goes back through `DQ`.** -/
theorem trig_back_DQ {η a B s y s' y' : T} :
    ∀ {k : Bool} {t tN : T}, DQ η k t tN → k = false → t = psi s y z → tN = psi s' y' z →
    (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) →
    (s' = s ∧ y' ≤ y ∧ (lt B y = true ∧ lt (psi a z z) (psi s y z) = true)) ∨
      (∃ t, s = succ t ∧ y = z ∧ ¬ lt t a = true) := by
  intro k t tN h
  cases h with
  | mk _ _ _ => intro hk; cases hk
  | @base l hlt =>
    intro _ hl hN ht
    subst hl
    rcases trig_back_fsD (le_of_lt hlt) hN ht with htM | hr
    · left
      have hy : y ≠ z := ne_z_of_lt htM.1
      have hs := fsD_psi_shape hy hN
      subst hs
      refine ⟨rfl, ?_, htM⟩
      have hlt' : psi s' y' z < psi s' y z := by rw [← hN]; exact hlt
      rcases psi_lt_psi_z_iff.mp hlt' with h' | ⟨_, h'⟩
      · exact absurd h' (lt_irrefl' _)
      · exact le_of_lt h'
    · exact Or.inr hr
  | @sub a0 aN _ =>
    intro _ _ hN ht
    obtain ⟨_, hy', _⟩ := T.psi.inj hN
    subst hy'
    exact absurd ht.1 (not_lt_z B)
  | @arg a0 b bN hD =>
    intro _ hl hN ht
    obtain ⟨h1, h2, _⟩ := T.psi.inj hl
    obtain ⟨h3, h4, _⟩ := T.psi.inj hN
    subst h1 h2 h3 h4
    have hb : bN < b := hD.lt
    left
    refine ⟨rfl, le_of_lt hb, ?_, ?_⟩
    · exact lt_trans (show B < bN from ht.1) hb
    · exact lt_trans (show psi a z z < psi a0 bN z from ht.2) (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hb⟩))

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- The frame head of `M[n]` before `x` is that of `M`. -/
theorem frameHead_ltQ (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {oq vq : Nat → T} (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i) {i : Nat} (h : i < r + L) {Lc : List Nat} {c : Nat} {R : List Nat}
    (hCL : CL (TRIO.gexp M r L d0 0 n) i = Lc ++ c :: R) :
    CL M i = Lc ++ c :: R ∧ (glueQ M (r + L) ρ (shiftV ρP L) oq vq).v i = ρ.v i ∧
      Lc.map (glueQ M (r + L) ρ (shiftV ρP L) oq vq).o = Lc.map ρ.o := by
  set σ := glueQ M (r + L) ρ (shiftV ρP L) oq vq with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueQ_o_ge (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueQ_v_ge (by omega)]
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
    rw [hσ, glueQ_o_lt hdx (hLd d hd)]
  exact ⟨hCL, by rw [hσ, glueQ_v_lt h hvd], hLo⟩


/-- The frame head of a copy column of `M[n]` is that of `M[n − 1]`. -/
theorem frameHead_copyQ (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {oq vq : Nat → T} (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i) {a : Nat} (ha : a < (n - 1) * L) {Lc : List Nat} {c : Nat} {R : List Nat}
    (hCL : CL (TRIO.gexp M r L d0 0 n) (r + L + a) = Lc ++ c :: R) :
    ∃ Lc' c' R', CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = Lc' ++ c' :: R' ∧
      (glueQ M (r + L) ρ (shiftV ρP L) oq vq).v (r + L + a) = ρP.v (r + a) ∧
      Lc.map (glueQ M (r + L) ρ (shiftV ρP L) oq vq).o = Lc'.map ρP.o ∧
      (glueQ M (r + L) ρ (shiftV ρP L) oq vq).o c = ρP.o c' := by
  set σ := glueQ M (r + L) ρ (shiftV ρP L) oq vq with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueQ_o_ge (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσoZ : ∀ a, (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => z)).o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [glueZ_o_ge ρ (shiftV ρP L) (fun _ => z) (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueQ_v_ge (by omega)]
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
    apply counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath hz2 (ρ := ρ) (Z := fun _ => z) ha hd)
    · have := hσoZ (d - r); rw [show r + L + (d - r) = d + L by omega,
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

/-- **`frameQR_N_t1` with `DQ` values on `D`** (`glueQ`). -/
theorem frameQR_N_t1Q (Q' : T → List T → T → T → Prop)
    (hQd : ∀ a Lv s y y', y' ≤ y →
      lt (spArg a z (sumN Lv)) y' = true ∧ lt (psi a z z) (psi s y' z) = true → Q' a Lv s y → Q' a Lv s y')
    (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {oq vq : Nat → T} (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (hC : Cons M ρ)
    (hFQ : ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      QR Q' (ρ.v i) (Lc.map ρ.o) (ρ.o c))
    (hOmQ : ∀ i, i < r + L → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → ∀ t,
      ρ.o c = psi (succ t) z z → ¬ lt t (ρ.v i) = true →
      QR Q' (ρ.v i) (Lc.map ρ.o) ((glueQ M (r + L) ρ (shiftV ρP L) oq vq).o c))
    (hFQP : ∀ i, i < (TRIO.gexp M r L d0 0 (n - 1)).length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
      CL (TRIO.gexp M r L d0 0 (n - 1)) i = Lc ++ c :: R → QR Q' (ρP.v i) (Lc.map ρP.o) (ρP.o c))
    (hDQ : ∀ c, c < r + L → DepX M (r + L) true c → ∃ η, DQ η false (ρ.o c) (oq c))
    (hlex : ρP.o r ≤ ρ.o (r + L)) (hox : ∃ t, ρ.o (r + L) = psi (succ t) z z) :
    ∀ i, i < (TRIO.gexp M r L d0 0 n).length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
      CL (TRIO.gexp M r L d0 0 n) i = Lc ++ c :: R →
      QR Q' ((glueQ M (r + L) ρ (shiftV ρP L) oq vq).v i) (Lc.map (glueQ M (r + L) ρ (shiftV ρP L) oq vq).o)
        ((glueQ M (r + L) ρ (shiftV ρP L) oq vq).o c) := by
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  intro i hi Lc c R hCL s y hc ht
  rcases Nat.lt_or_ge i (r + L) with h | h
  · obtain ⟨hCLM, hv, hLo⟩ := frameHead_ltQ hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hCP hOS h hCL
    rw [hv, hLo] at ht ⊢
    have hcCL : c ∈ CL M i := by rw [hCLM]; simp
    have hcM := mem_children (List.mem_filter.mp hcCL).1
    have hiM : i < M.length := by omega
    obtain ⟨s0, y0, h0⟩ := o_psi_form hC hcM.2
    have hc0 := hc
    by_cases hcx : c = r + L
    · rw [hcx] at hc hCLM hc0
      rw [glueQ_o_ge (le_refl _)] at hc
      have hc' : ρP.o r = psi s y z := by
        have : (shiftV ρP L).o (r + L) = ρP.o r := by show ρP.o (r + L - L) = _; rw [Nat.add_sub_cancel]
        rw [← this]; exact hc
      obtain ⟨t, hto⟩ := hox
      have hnt := trig_back_succ (by rw [← hto]; exact hlex) hc' ht
      exact hOmQ i h Lc (r + L) R hCLM t hto hnt s y hc0 ht
    · have hcx' : c < r + L := by omega
      by_cases hd : DepX M (r + L) true c
      · rw [glueQ_o_dep hcx' hd] at hc
        obtain ⟨η, hD⟩ := hDQ c hcx' hd
        rcases trig_back_DQ hD rfl h0 hc ht with ⟨hss, hyy, htM⟩ | ⟨t, hst, hy0, hnt⟩
        · subst hss
          exact hQd _ _ _ _ _ hyy ht (hFQ i hiM Lc c R hCLM s y0 h0 htM)
        · exact hOmQ i h Lc c R hCLM t (by rw [h0, hst, hy0]) hnt s y hc0 ht
      · rw [glueQ_o_lt hcx' hd] at hc
        exact hFQ i hiM Lc c R hCLM s y hc ht
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    obtain ⟨Lc', c', R', hsp, hv, hLo, hco⟩ :=
      frameHead_copyQ hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hCP hOS ha hCL
    rw [hv, hLo] at ht ⊢
    rw [hco] at hc
    exact hFQP (r + a) (by rw [hlP]; omega) Lc' c' R' hsp s y hc ht

end

/-- The extra facts with the chain bound `ρP.o r ≤ o(x)` (supplied by `hLocH`'s premise `ρP.o r < o(x)`). -/
def ExDQX (M : Mat) (r L : Nat) (ρ : Valn) (n : Nat) (ρP : Valn) (oq vq : Nat → T) : Prop :=
  ExDQ M r L ρ n ρP oq vq ∧ ρP.o r ≤ ρ.o (r + L)

/-- **The leaf residual** of a frame property `Q'` at the new values. -/
def OmQRes (Q' : T → List T → T → T → Prop) (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (oq vq : Nat → T),
    Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP → Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    Cons (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) →
    Good3 (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) →
    ExDQX M r L ρ n ρP oq vq →
    ∀ i, i < r + L → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → ∀ t,
      ρ.o c = psi (succ t) z z → ¬ lt t (ρ.v i) = true →
      QR Q' (ρ.v i) (Lc.map ρ.o) ((glueQ M (r + L) ρ (shiftV ρP L) oq vq).o c)

/-- **A frame property is carried through the DQ copy** (generic form of `expStep_ph3c_t1S`). -/
theorem expStepQR_frame (Q' : T → List T → T → T → Prop)
    (hQd : ∀ a Lv s y y', y' ≤ y →
      lt (spArg a z (sumN Lv)) y' = true ∧ lt (psi a z z) (psi s y' z) = true → Q' a Lv s y → Q' a Lv s y')
    {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hFQ : ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      QR Q' (ρ.v i) (Lc.map ρ.o) (ρ.o c))
    (P : Mat → Valn → Prop)
    (hPQ : ∀ N σ, P N σ → ∀ i, i < N.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N i = Lc ++ c :: R →
      QR Q' (σ.v i) (Lc.map σ.o) (σ.o c))
    (hOm : OmQRes Q' M r L d0 ρ) :
    ExpStepQR P (fun N σ => ∀ i, i < N.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
      CL N i = Lc ++ c :: R → QR Q' (σ.v i) (Lc.map σ.o) (σ.o c)) (ExDQX M r L ρ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  have hxnb := hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
  exact frameQR_N_t1Q hlen hL hA hd0e hn Q' hQd hpath hx2 hxnb (S.z2 r) hiu hiux hCP hOS hC hFQ
    (hOm n hn ρP oq vq hCP hGP hCN hGN hEx) (hPQ _ _ hPP) hEx.1.1 hEx.2 hox

/-- **PH3cG is carried through the DQ copy**, given its leaf residual. -/
theorem expStepQR_ph3c {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hOm : OmQRes PH' M r L d0 ρ) :
    ExpStepQR PnV3 (fun N σ => PH3cG N σ) (ExDQX M r L ρ) M r L d0 ρ := by
  intro n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  exact ph3c_iff.mpr (expStepQR_frame PH' (fun _ _ _ _ _ hyy ht h => ph'_drop hyy ht h) S I.cons I.good
    hlen hL hd0e h1 hx2 (ph3c_iff.mp I.ph) PnV3 (fun N σ ⟨_, J⟩ => ph3c_iff.mp J.ph) hOm
    n hn ρP oq vq hCP hGP hPP hCN hGN hEx)

/-- **FC3 is carried through the DQ copy**, given its leaf residual. -/
theorem expStepQR_fc3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hOm : OmQRes F3' M r L d0 ρ) :
    ExpStepQR PnV3 (fun N σ => FC3 N σ) (ExDQX M r L ρ) M r L d0 ρ := by
  intro n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  exact fc3_iff.mpr (expStepQR_frame F3' (fun _ _ _ _ _ hyy ht h => f3'_drop hyy ht h) S I.cons I.good
    hlen hL hd0e h1 hx2 (fc3_iff.mp I.fc3) PnV3 (fun N σ ⟨_, J⟩ => fc3_iff.mp J.fc3) hOm
    n hn ρP oq vq hCP hGP hPP hCN hGN hEx)

end Ytosk.WfExQ4
