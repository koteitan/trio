/-
**B2Step は偽（2026-10-31, WfB2S）。** 28 列の標準形（SRO から 116 歩の `Std.exp` の道）で Bad2。
n = x − 1 = 26 が祖先 k = 19 = (4,3,1) へ上げ、m = P₀ k = 15。k の子は 20・22・23 で、20 と 22 が bump 子、
最後の bump 子 22 は葉（子がない）。bumpW(19) = ψ_{ω+1}(1) の段は 0 でない。
B2Step の結論（段 0 か、最後の bump 子 j に最初の子 c がある）はどちらも成り立たない。
- `not_B2NoUB`: 構造の残り `WfH7W2.B2NoUB` は無条件に偽。
- `not_B2StepCore`: B2Step の Inv3V2 を Cons・Rk・Good3 に替えたものは偽。
- `not_B2Step_of`: `hInvV2_all` の仮定（Inv3V2 の存在）のもとで B2Step は偽。
HUACB2 自身はここで成り立つ（子を持つ最後の bump 子 20 の最初の子 21 が m の段に戻る、a = m）。
直し方は `WfB2S.B2StepAb`（j = 子を持つ最後の bump 子）。
-/
import Ytosk.WfB2S
import Ytosk.WfHUACShapeFalse
import Ytosk.V3MainV2

namespace Ytosk.WfB2SFalse
open T
open WfHUACDeep
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def M : Mat := [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (6, 3, 0), (4, 3, 1), (5, 3, 1), (6, 2, 0), (5, 3, 1), (5, 3, 0), (6, 4, 1), (7, 4, 1), (8, 3, 0), (8, 2, 0)]

def trace : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1]

private def t0 : T := psi z z z
private def t1 : T := psi z t0 t0
private def t2 : T := psi t1 t0 z
private def t3 : T := psi t1 z z
private def t4 : T := psi t2 t3 z
private def t5 : T := psi t2 t4 z
private def t6 : T := psi t5 z z
private def t7 : T := psi z t6 z
private def t8 : T := psi z t0 z
private def t9 : T := psi t8 z z
private def t10 : T := psi t9 z z
private def t11 : T := psi t10 z z
private def t12 : T := psi t8 t10 z
private def t13 : T := psi t8 t9 z
private def t14 : T := psi t8 t6 z
private def t15 : T := psi t3 z z
private def t16 : T := psi t15 z z
private def t17 : T := psi z t0 t8
private def t18 : T := psi t17 t15 z
private def t19 : T := psi t17 t3 z
private def t20 : T := psi t1 t6 z
private def t21 : T := psi t2 z z
private def t22 : T := psi t21 z z
private def t23 : T := psi t17 t21 z
private def t24 : T := psi t2 t6 z
private def t25 : T := psi t17 z z
private def t26 : T := psi t1 t0 t8
private def t27 : T := psi t2 z t3
private def t28 : T := psi t26 t27 z

def oT : List T := [t7, t11, t12, t10, t10, t13, t9, t14, t14, t16, t18, t15, t15, t19, t3, t20, t22, t23, t21, t24, t19, t3, t25, t24, t6, t28, t21, t3]
def vT : List T := [z, t10, t8, t9, t9, t8, t8, t8, t8, t15, t17, t3, t3, t17, t1, t1, t21, t17, t2, t2, t17, t1, t17, t2, t5, t26, t2, t1]
def rkO : List Nat := [16, 9, 8, 7, 6, 5, 4, 15, 14, 10, 9, 8, 7, 6, 5, 13, 10, 9, 8, 12, 6, 5, 6, 11, 10, 9, 8, 5]
def rkV : List Nat := [1, 8, 2, 6, 5, 2, 3, 2, 3, 9, 4, 7, 6, 4, 4, 4, 9, 5, 7, 6, 5, 4, 5, 7, 9, 8, 7, 4]
def Wt : T := t2

private theorem std_fold : ∀ (ns : List Nat) (N : Mat), Std N → Std (ns.foldl expand N)
  | [], _, h => h
  | n :: ns, N, h => std_fold ns (expand N n) (Std.exp n h)

theorem standard : Std M := by
  have h : trace.foldl expand SRO = M := by decide
  rw [← h]
  exact std_fold trace SRO Std.sro

theorem ne_sro : M ≠ SRO := by decide

def σ : Valn := ⟨fun i => oT.getD i z, fun i => vT.getD i z⟩
def rk : Bool → Nat → Nat := fun b i => if b then rkO.getD i 0 else rkV.getD i 0

theorem cons : Cons M σ := by unfold Cons; decide

theorem rank : Rk M rk := WfHUACShapeFalse.rk_of_rkB (by decide)

theorem good : Good3 M σ := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · unfold cvals nzs
    decide

theorem upg26 : upg M 26 = some 19 := by decide
theorem par19 : par M 0 19 = some 15 := by decide
theorem children19 : children M 19 = [20, 22, 23] := by decide
theorem children22 : children M 22 = [] := by decide
theorem col22 : col M 22 = bump M 19 := by decide
theorem col23 : col M 23 ≠ bump M 19 := by decide
theorem e1_21 : entry M 1 21 ≠ 0 := by decide

theorem not_upgAbsX : ¬ UpgAbsX M 27 σ := by
  intro h
  have hl := h 26 19 Wt rfl upg26 (by decide) (by decide) (psi z one z) (by decide) (by decide)
  have h2 := hl.2 z (psi one z z) (by decide) (by decide)
  obtain ⟨y, hy, hle⟩ := h2 one (by decide)
  revert hle
  revert y
  decide

theorem anc : Anc0 M 24 27 :=
  Anc0.step (b := 25) (by decide) (Anc0.step (b := 24) (by decide) (Anc0.refl 24))

theorem bad2 : Bad2 M :=
  ⟨⟨19, by decide⟩, 25, 24, by decide, by decide, by decide, Or.inl ⟨Or.inl anc, σ, cons, not_upgAbsX⟩⟩

theorem lev_ne : lev (bumpW M σ 19) ≠ z := by decide

/-- Every valuation of `M` has the same `bumpW` at `19`. -/
theorem bumpW_eq {ρ : Valn} (hρ : Cons M ρ) : bumpW M ρ 19 = bumpW M σ 19 := by
  have hu := cons_unique hρ cons rank
  unfold bumpW
  congr 2
  congr 1
  apply List.map_congr_left
  intro j hj
  unfold bumpTerm
  split
  · congr 2
    apply List.map_congr_left
    intro c hc
    exact (hu c (mem_children hc).2).1
  · rfl

/-- No decomposition with the last bump child having a first child. -/
theorem no_canon (P : Nat → Prop) : ¬ ∃ L j R c C, children M 19 = L ++ j :: R ∧ col M j = bump M 19 ∧
    (∀ d ∈ R, col M d ≠ bump M 19) ∧ children M j = c :: C ∧ P c := by
  rintro ⟨L, j, R, c, C, hL, hjb, hR, hC, _⟩
  rw [children19] at hL
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨d, L⟩⟩⟩
  · simp only [List.nil_append, List.cons.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    exact hR 22 (by simp) col22
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hL
    obtain ⟨_, rfl, rfl⟩ := hL
    rw [children22] at hC
    cases hC
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hL
    obtain ⟨_, _, rfl, rfl⟩ := hL
    exact col23 hjb
  · simp only [List.cons_append, List.cons.injEq] at hL
    obtain ⟨_, _, _, h⟩ := hL
    have := congrArg List.length h
    simp at this

/-- **The structural residual `B2NoUB` is false.** -/
theorem not_B2NoUB : ¬ WfH7W2.B2NoUB := by
  intro h
  rcases h M standard ne_sro bad2 26 rfl 19 15 upg26 (by decide) par19 with h0 | ⟨L, j, R, c, C, hL, hjb, hR, hC, _⟩
  · exact e1_21 (h0 20 (by rw [children19]; simp) (by decide) 21 (by decide))
  · exact no_canon (fun _ => True) ⟨L, j, R, c, C, hL, hjb, hR, hC, trivial⟩

/-- `B2Step` with `Cons`, `Rk`, `Good3` in place of `Inv3V2`. -/
def B2StepCore : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Cons M ρ → Rk M rk → Good3 M ρ → ∀ n, n + 2 = M.length →
    ∀ k m, upg M n = some k → k < n → par M 0 k = some m →
    lev (bumpW M ρ k) = z ∨
    ∃ L j R c C, children M k = L ++ j :: R ∧ col M j = bump M k ∧ (∀ d ∈ R, col M d ≠ bump M k) ∧
      children M j = c :: C ∧
      ∀ a, WfHUACDeep.Up1 M a m → entry M 1 a = entry M 1 c → WfHUACDeep.StepDom M ρ a m

theorem not_B2StepCore : ¬ B2StepCore := by
  intro h
  rcases h M σ rk standard ne_sro bad2 cons rank good 26 rfl 19 15 upg26 (by decide) par19 with h0 | ⟨L, j, R, c, C, hL, hjb, hR, hC, hst⟩
  · exact lev_ne h0
  · exact no_canon (fun c => ∀ a, Up1 M a 15 → entry M 1 a = entry M 1 c → StepDom M σ a 15)
      ⟨L, j, R, c, C, hL, hjb, hR, hC, hst⟩

/-- **`B2Step` is false whenever every standard matrix has an `Inv3V2` valuation** (the conclusion of
`hInvV2_all`). -/
theorem not_B2Step_of_inv (hI : ∃ ρ rk, Inv3V2 M ρ rk) : ¬ WfH7W2.B2Step := by
  intro h
  obtain ⟨ρ, rk', I⟩ := hI
  rcases h M ρ rk' standard ne_sro bad2 I 26 rfl 19 15 upg26 (by decide) par19 with h0 | ⟨L, j, R, c, C, hL, hjb, hR, hC, hst⟩
  · rw [bumpW_eq I.cons] at h0
    exact lev_ne h0
  · exact no_canon (fun c => ∀ a, Up1 M a 15 → entry M 1 a = entry M 1 c → StepDom M ρ a 15)
      ⟨L, j, R, c, C, hL, hjb, hR, hC, hst⟩

theorem not_B2Step_of (hU : HDropU) (hD : HDropV2) (hT : HTakeV2) (hTB : TakeBadV2) (hBO : BadOutV2)
    (h0 : ExpT0OutV2) (h1 : ExpT1OutV2) (h2 : ExpT2V2) (hCB : T2CBadOut) : ¬ WfH7W2.B2Step :=
  not_B2Step_of_inv (hInvV2_all hU hD hT hTB hBO h0 h1 h2 hCB M standard ne_sro (by decide))

#print axioms not_B2NoUB
#print axioms not_B2StepCore
#print axioms not_B2Step_of

end Ytosk.WfB2SFalse
