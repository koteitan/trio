/-
GxH.lean: シート行 464〜475, 478〜483, 485〜488。

先頭にタイの中身の字が m 個ある語 `(0,v,0) :: rword 0 v (pre v m ++ l)`（GxG.BwP）を使い、
段 0 でも Wg の世界で組んで `Wg0_sub_W0` で W 0 に移す。

- `BwP_pre_succ`: 先頭の字を 1 個増やす（末尾 `(2,v+1,0)` は根が生き返らせる孤児。塔の中身を GOKWP で継ぐ）。
- `W0_hang`: 段 0 の語の後ろに `Wg` の元を `hang_Wg` で継ぐ。
-/
import GxG
import GxB

namespace TRIO
namespace GxH

open Wset
open Small
open GwS
open Gw
open GwU
open GwV
open GwZ
open GxD
open GxG

/-! ## 部品 -/

theorem BwP_nil (v0 : ℕ) : BwP v0 0 [] := by
  intro v _ _ a ha
  show (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (pre v 0 ++ [])) ∈ Wg a
  simp only [pre, List.replicate, List.nil_append, rword_nil]
  exact Wg_mono ha (Om_mem_Wg v)

theorem Wg_of_BwP {v0 m : ℕ} {l : List TrioSeq} (h : BwP v0 m l) {v : ℕ} (hv : v0 ≤ v) :
    (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v (pre v m ++ l)) ∈ Wg (2 * v) :=
  h v hv (argOK_rword v _) (2 * v) le_rfl

theorem W0_of_BwP {m : ℕ} {l : List TrioSeq} (h : BwP 0 m l) :
    (((0, 0, 0) : ℕ × ℕ × ℕ) :: rword 0 0 (pre 0 m ++ l)) ∈ W 0 :=
  GxB.Wg0_sub_W0 (h 0 le_rfl (argOK_rword 0 _) 0 le_rfl)

theorem W0_hang {m : ℕ} {l : List TrioSeq} (h : BwP 0 m l) {u : ℕ} {R : TrioSeq}
    (hR : R ∈ Wg u) (hRge : ∀ x ∈ R, 1 ≤ x.1) (hhd : entry R 0 0 ≤ 1) :
    (((0, 0, 0) : ℕ × ℕ × ℕ) :: (rword 0 0 (pre 0 m ++ l) ++ R)) ∈ W 0 :=
  GxB.Wg0_sub_W0 (hangv (h 0 le_rfl) (fun x hx => rword_ge 0 0 _ x hx) hR hRge hhd 0 le_rfl)

theorem star_of_BwP {v0 m : ℕ} {l : List TrioSeq} (h : BwP v0 m l) {v : ℕ} (hv : v0 ≤ v) :
    rword 0 v (pre v m ++ l) ∈ Wstarv v := h v hv

theorem BwP_pre_succ {v0 m : ℕ} (hB : BwP v0 m []) : BwP v0 (m + 1) [] := by
  intro v hv _ a ha
  set X := rword 0 v (pre v m) with hX
  set c1 : ℕ × ℕ × ℕ := (1, v + 1, 1) with hc1
  set c2 : ℕ × ℕ × ℕ := (2, v + 1, 0) with hc2
  have eR : rword 0 v (pre v (m + 1) ++ []) = X ++ [c1, c2] := by
    rw [List.append_nil, pre, List.replicate_succ', ← pre, rword_append, rword_singleton]
    simp [rcol, shiftr01, hc1, hc2] <;> rfl
  rw [eR]
  set R : TrioSeq := X ++ [c1, c2] with hRdef
  have hRne : R ≠ [] := by simp [hRdef]
  have hRlen : R.length = X.length + 2 := by simp [hRdef]
  have hXge : ∀ x ∈ X, 1 ≤ x.1 := fun x hx => rword_ge 0 v _ x hx
  have hX1 : ∀ x ∈ X, x.2.1 = v + 1 := pre_row1 v m
  have hR : argOK R := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hXge p hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [hc1, hc2]
  have eX : ∀ r j, j < X.length → entry R r j = entry X r j := by
    intro r j hj; rw [hRdef, Small.entry_append_left hj]
  have e_last : ∀ r, entry R r (R.length - 1) = entry [c1, c2] r 1 := by
    intro r
    rw [show R.length - 1 = X.length + 1 by omega, hRdef, entry_append_right]
  have e_head : ∀ r, entry R r X.length = entry [c1, c2] r 0 := by
    intro r
    rw [show X.length = X.length + 0 from rfl, hRdef, entry_append_right]
  have e0 : entry R 0 (R.length - 1) = 2 := by rw [e_last]; simp [entry, hc2]
  have e1 : entry R 1 (R.length - 1) = v + 1 := by rw [e_last]; simp [entry, hc2]
  have e2 : entry R 2 (R.length - 1) = 0 := by rw [e_last]; simp [entry, hc2]
  have hRrow1 : ∀ j, j < R.length → entry R 1 j = v + 1 := by
    intro j hj
    rcases Nat.lt_or_ge j X.length with hjX | hjX
    · rw [eX 1 j hjX]
      exact GxF.getD_mem_P hjX (P := fun x => x.2.1 = v + 1) hX1
    · rcases (by omega : j = X.length ∨ j = X.length + 1) with rfl | rfl
      · rw [e_head]; simp [entry, hc1]
      · rw [show X.length + 1 = R.length - 1 by omega, e1]
  have hsr : srow R (R.length - 1) = 1 := by
    unfold srow; rw [e2, e1]; simp
  have hd : domT R (2 * v + 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2]; omega
    · rw [hsr]
      rintro ⟨k, hk, -⟩
      have hk' : nextrel1 R k (R.length - 1) := by
        unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
      obtain ⟨-, -, hkl, hk1, -⟩ := hk'
      rw [hRrow1 k (by omega), e1] at hk1
      omega
  have hpM : hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
    rw [hsr]
    have n1 : nextrel0 (((0, v, 0) : ℕ × ℕ × ℕ) :: R) 0 (X.length + 1) := by
      refine ⟨by simp, by rw [List.length_cons, hRlen]; omega, by omega, ?_, ?_⟩
      · rw [entry_cons, e_head]; simp [entry, hc1]
      · intro j hj
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [entry_cons, entry_cons, e_head, eX 0 j' (by omega)]
        have := GxF.getD_mem_P (by omega : j' < X.length) (P := fun x => 1 ≤ x.1) hXge
        simp only [entry, hc1]
        exact this
    have n2 : nextrel0 (((0, v, 0) : ℕ × ℕ × ℕ) :: R) (X.length + 1) R.length := by
      refine ⟨by simp; omega, by simp, by omega, ?_, fun j hj => by omega⟩
      rw [entry_cons, show R.length = (R.length - 1) + 1 by omega, entry_cons, e_head, e0]
      simp [entry, hc1]
    refine hasParent_one_of (b := R.length) (k := 0) (by simp) (by omega)
      ⟨by simp, by simp, Relation.ReflTransGen.tail (Relation.ReflTransGen.single n1) n2⟩ ?_
    rw [entry_cons_last hRne 1, e1]; simp [entry]
  have hnat : natDom (((0, v, 0) : ℕ × ℕ × ℕ) :: R) := by
    refine natDom_iff.mpr (Or.inr ?_)
    have hl : ((((0, v, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]
    exact hpM
  have hdl : R.dropLast = X ++ [c1] := by
    rw [hRdef, show X ++ [c1, c2] = (X ++ [c1]) ++ [c2] by simp, List.dropLast_concat]
  have htow : ∀ k, tow v 0 R k ∈ Wg (2 * v) := by
    intro k
    induction k with
    | zero => simpa [tow] using Wg_nil (2 * v)
    | succ k ih =>
        have e : tow v 0 R (k + 1) = ((0, v, 0) : ℕ × ℕ × ℕ) ::
            rword 0 v (pre v m ++ [shiftr01 1 0 (tow v 0 R k)]) := by
          rw [tow, graft_eq_shift, e0, hdl, rword_append, rword_singleton, rcol, shiftr01_add0]
          simp [hc1, List.append_assoc] <;> rfl
        rw [e]
        have hT : shiftr01 1 0 (tow v 0 R k) ∈ Wg (2 * v) := Wg_shift ih 1
        have hB' : BwP v m [shiftr01 1 0 (tow v 0 R k)] := by
          have h := GOKWP_of_Wg (v0 := v) m _ hT (GxD.shift1_ge _) []
            (by intro U hU; simp at hU) (fun u hu => hB u (le_trans hv hu))
          simpa using h
        exact hB' v le_rfl (argOK_rword v _) (2 * v) le_rfl
  refine A1g_intro (Or.inr (Or.inl ⟨hnat, fun n _ => ?_⟩))
  rw [oper_cons_tower1 hR hRne hd hsr hpM]
  exact Wg_mono ha (htow n)

theorem B1 : BwP 0 1 [] := BwP_pre_succ (BwP_nil 0)
theorem B2 : BwP 0 2 [] := BwP_pre_succ B1

theorem W100 : [((1, 0, 0) : ℕ × ℕ × ℕ)] ∈ Wg 0 :=
  A1g_intro (Or.inl ⟨by simp, by simp [lev, entry]⟩)

theorem WOk_nil (v0 : ℕ) : WOkWv v0 [] := by intro U hU; simp at hU

theorem raw0 {T : TrioSeq} (hT : T ∈ Wg 0) (hge : ∀ x ∈ T, 1 ≤ x.1) : RawWv 0 T :=
  ⟨hge, Wg_RiseOkv (v0 := 0) hT⟩

/-! ## 段 0: 行 464〜468（先頭 1 字 + ψ_0 の中身） -/

theorem BwC {v0 m : ℕ} {T : TrioSeq} (hT : T ∈ Wg (2 * v0)) (hge : ∀ x ∈ T, 1 ≤ x.1)
    {l : List TrioSeq} (hw : WOkWv v0 l) (hB : BwP v0 m l) : BwP v0 m (l ++ [T]) :=
  GOKWP_of_Wg m T hT hge l hw hB

/-- ★ シート行 464 `(0,0,0)(1,1,1)(2,1,0)(1,1,1)(2,0,0)(1,1,1)`。 -/
theorem R464_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hC : BwP 0 1 [[((1, 0, 0) : ℕ × ℕ × ℕ)]] := by
    simpa using BwC (v0 := 0) W100 (by decide) (WOk_nil 0) B1
  have hD := Bw_snoczP (WOkWv_singleton (raw0 W100 (by decide))) hC
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP hD

theorem W1010 : [((1, 0, 0) : ℕ × ℕ × ℕ), ((1, 0, 0) : ℕ × ℕ × ℕ)] ∈ Wg 0 := by
  have h := Wg_add W100 W100 (by
    intro p hp
    simp only [List.mem_append, List.mem_singleton, or_self] at hp
    subst hp; simp [entry])
  simpa using h

/-- ★ シート行 465 `… (1,1,1)(2,0,0)(2,0,0)`。 -/
theorem R465_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hC := BwC (v0 := 0) W1010 (by decide) (WOk_nil 0) B1
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP hC

theorem W0_0011 : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ Wg 0 := by
  have h := A2g' (Y := Wstarg) (fun M hM => Wstarg_closed 2 M hM) Wg2_110
  exact h (by intro p hp; simp at hp; subst hp; simp) 0 0 le_rfl

/-- ★ シート行 466 `… (1,1,1)(2,0,0)(3,1,0)`。 -/
theorem R466_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hT : shiftr01 1 0 [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ Wg (2 * 0) :=
    Wg_shift W0_0011 1
  have hC := BwC (v0 := 0) hT (GxD.shift1_ge _) (WOk_nil 0) B1
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP hC

theorem Gz0 : BwP 0 0 [[]] := by
  simpa using Bw_snoczP (WOk_nil 0) (BwP_nil 0)

theorem Gz1 : BwP 0 1 [[]] := by
  simpa using Bw_snoczP (WOk_nil 0) B1

/-- ★ シート行 467 `… (1,1,1)(2,0,0)(3,1,1)`。 -/
theorem R467_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ), ((3, 1, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hT : shiftr01 1 0 (((0, 0, 0) : ℕ × ℕ × ℕ) :: rword 0 0 (pre 0 0 ++ [[]])) ∈ Wg (2 * 0) :=
    Wg_shift (Wg_of_BwP Gz0 le_rfl) 1
  have hC := BwC (v0 := 0) hT (GxD.shift1_ge _) (WOk_nil 0) B1
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP hC

/-- ★ シート行 468 `… (1,1,1)(2,0,0)(3,1,1)(4,1,0)(3,1,1)`。 -/
theorem R468_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ), ((3, 1, 1) : ℕ × ℕ × ℕ),
    ((4, 1, 0) : ℕ × ℕ × ℕ), ((3, 1, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hT : shiftr01 1 0 (((0, 0, 0) : ℕ × ℕ × ℕ) :: rword 0 0 (pre 0 1 ++ [[]])) ∈ Wg (2 * 0) :=
    Wg_shift (Wg_of_BwP Gz1 le_rfl) 1
  have hC := BwC (v0 := 0) hT (GxD.shift1_ge _) (WOk_nil 0) B1
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP hC

/-! ## 段 0: 行 469〜（先頭 2 字） -/

/-- ★ シート行 469 `(0,0,0)(1,1,1)(2,1,0)(1,1,1)(2,1,0)`。 -/
theorem R469_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_of_BwP B2

/-- ★ シート行 470 `… (2,1,0)(1,1,0)`。 -/
theorem R470_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using W0_hang B2 Wg2_110 (by decide) (by simp [entry])

/-- ★ シート行 471 `… (2,1,0)(1,1,0)(2,2,1)`。 -/
theorem R471_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01, GwT.T21] using
    W0_hang B2 GwT.T21_Wg GwT.T21_ge (by simp [entry, GwT.T21])

/-- ★ シート行 472 `… (2,1,0)(1,1,0)(2,2,1)(3,2,0)(2,2,1)`。 -/
theorem R472_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01, GxC.L4] using
    W0_hang B2 L4_Wg L4_ge (by simp [entry, GxC.L4])

/-! ## 段 1 の部品と行 473〜488 -/

theorem W2_100 : [((1, 0, 0) : ℕ × ℕ × ℕ)] ∈ Wg (2 * 1) := Wg_mono (by omega) W100

theorem C1 : BwP 1 1 [] := BwP_pre_succ (BwP_nil 1)
theorem C2 : BwP 1 2 [] := BwP_pre_succ C1

theorem C_110 : BwP 1 1 [[((1, 1, 0) : ℕ × ℕ × ℕ)]] := by
  simpa using BwC (v0 := 1) Wg2_110 (by decide) (WOk_nil 1) C1

theorem raw1_110 : RawWv 1 [((1, 1, 0) : ℕ × ℕ × ℕ)] :=
  ⟨by decide, Wg_RiseOkv (v0 := 1) Wg2_110⟩

/-- 段 1 の根の列を 1 段上げて、段 0 の先頭 2 字の語の後ろに継ぐ。 -/
theorem row1 {Z : TrioSeq} (hZ : (((0, 1, 0) : ℕ × ℕ × ℕ) :: Z) ∈ Wg 2) :
    (((0, 0, 0) : ℕ × ℕ × ℕ) :: (rword 0 0 (pre 0 2 ++ []) ++
      shiftr01 1 0 (((0, 1, 0) : ℕ × ℕ × ℕ) :: Z))) ∈ W 0 :=
  W0_hang B2 (Wg_shift hZ 1) (GxD.shift1_ge _) (by simp [shiftr01, entry])

theorem rowB {m : ℕ} {l : List TrioSeq} (h : BwP 1 m l) :
    (((0, 0, 0) : ℕ × ℕ × ℕ) :: (rword 0 0 (pre 0 2 ++ []) ++
      shiftr01 1 0 (((0, 1, 0) : ℕ × ℕ × ℕ) :: rword 0 1 (pre 1 m ++ l)))) ∈ W 0 :=
  row1 (Wg_of_BwP h le_rfl)

/-- ★ シート行 473 `… (2,2,1)(3,2,0)(2,2,1)(3,0,0)`。 -/
theorem R473_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := BwC (v0 := 1) W2_100 (by decide) (WOk_nil 1) C1
  simpa [pre, rword, rcol, shiftr01] using rowB h

/-- ★ シート行 474 `… (2,2,1)(3,2,0)(2,2,1)(3,1,0)`。 -/
theorem R474_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using rowB C_110

/-- ★ シート行 475 `… (2,2,1)(3,1,0)(2,2,0)`。 -/
theorem R475_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hZ := tower_snoc 1 (star_of_BwP C_110 le_rfl) (fun x hx => rword_ge 0 1 _ x hx) 2 le_rfl
  simpa [pre, rword, rcol, shiftr01] using row1 hZ

theorem C_110_z : BwP 1 1 [[((1, 1, 0) : ℕ × ℕ × ℕ)], []] := by
  simpa using Bw_snoczP (WOkWv_singleton raw1_110) C_110

/-- ★ シート行 478 `… (3,1,0)(2,2,1)`。 -/
theorem R478_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using rowB C_110_z

/-- ★ シート行 479 `… (3,1,0)(2,2,1)(2,2,1)`。 -/
theorem R479_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hw : WOkWv 1 [[((1, 1, 0) : ℕ × ℕ × ℕ)], []] :=
    WOkWv_append (WOkWv_singleton raw1_110) (WOkWv_singleton (RawWv_nil 1))
  have h := Bw_snoczP hw C_110_z
  simpa [pre, rword, rcol, shiftr01] using rowB h

/-- ★ シート行 480 `… (3,1,0)(2,2,1)(3,0,0)`。 -/
theorem R480_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := BwC (v0 := 1) W2_100 (by decide) (WOkWv_singleton raw1_110) C_110
  simpa [pre, rword, rcol, shiftr01] using rowB h

/-- ★ シート行 481 `… (3,1,0)(2,2,1)(3,1,0)`。 -/
theorem R481_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := BwC (v0 := 1) Wg2_110 (by decide) (WOkWv_singleton raw1_110) C_110
  simpa [pre, rword, rcol, shiftr01] using rowB h

theorem W2_110_100 : [((1, 1, 0) : ℕ × ℕ × ℕ), ((1, 0, 0) : ℕ × ℕ × ℕ)] ∈ Wg (2 * 1) := by
  have h := Wg_add Wg2_110 W2_100 (by
    intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [entry])
  simpa using h

/-- ★ シート行 482 `… (2,2,1)(3,1,0)(3,0,0)`。 -/
theorem R482_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ), ((3, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := BwC (v0 := 1) W2_110_100 (by decide) (WOk_nil 1) C1
  simpa [pre, rword, rcol, shiftr01] using rowB h

/-- ★ シート行 483 `… (2,2,1)(3,1,0)(3,1,0)`。 -/
theorem R483_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := BwC (v0 := 1) Wg2_110_110 (by decide) (WOk_nil 1) C1
  simpa [pre, rword, rcol, shiftr01] using rowB h

/-- ★ シート行 485 `… (2,2,1)(3,1,0)(4,2,1)`。 -/
theorem R485_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := BwC (v0 := 1) GwT.T21_Wg GwT.T21_ge (WOk_nil 1) C1
  simpa [pre, rword, rcol, shiftr01, GwT.T21] using rowB h

/-- ★ シート行 486 `… (2,2,1)(3,1,0)(4,2,1)(5,2,0)(4,2,1)`。 -/
theorem R486_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ), ((5, 2, 0) : ℕ × ℕ × ℕ),
    ((4, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := BwC (v0 := 1) L4_Wg L4_ge (WOk_nil 1) C1
  simpa [pre, rword, rcol, shiftr01, GxC.L4] using rowB h

/-- ★ シート行 487 `… (2,2,1)(3,2,0)(2,2,1)(3,2,0)`。 -/
theorem R487_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa [pre, rword, rcol, shiftr01] using rowB C2

/-- ★ シート行 488 `… (2,2,1)(3,2,0)(2,2,0)`。 -/
theorem R488_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hZ := tower_snoc 1 (star_of_BwP C2 le_rfl) (fun x hx => rword_ge 0 1 _ x hx) 2 le_rfl
  simpa [pre, rword, rcol, shiftr01] using row1 hZ

#print axioms R464_mem
#print axioms R469_mem
#print axioms R488_mem

end GxH
end TRIO
