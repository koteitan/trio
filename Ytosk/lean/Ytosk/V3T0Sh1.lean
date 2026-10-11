/-
**3 行・t = 0: T0Shape の (i) のうち状態 B = 0 の枠。**

(i): r より前の枠 i で最後の数える子 c の引数の組 (y′, y) が型 B0（どちらも低い部分 0）、古い枠が書き換える
（B < y）なら新しい枠も書き換える（B < y′）。B = 0 のときは y′ ≠ 0 を示せばよい。

- 古い枠が書き換えるので y ≠ 0、よって c は M で数える子を持つ（持たなければ o(c) = ψ_v(0)）。
- c は N でも数える子を持つ（c ≠ g なら数える子は同じ。c = g なら r より前の数える子か、最後の写しの根）。
- 数える子の o は ψ の形で 0 でないので、和も 0 でなく、`spArg` の結果も 0 でない（`spArg_ne_z`）。

残りの (i) は B ≠ 0 の枠だけ（PH3c の pre・cut 型）。
-/
import Ytosk.V3T0Sh3

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## (i) で B = 0 の枠 -/

/-- **`T0Shape` (i) when the state is `0`**: the new argument is nonzero. -/
theorem t0_shape1_z {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (I : Inv3 M ρ rk) (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0) :
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z →
      spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true := by
  intro n hn2 σ hCN i c Lc hi hc hCL s y y' hy hy' hB htr
  have hn : 1 ≤ n := by omega
  have he2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  rw [hB] at htr ⊢
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hcM : c < M.length := by omega
  have hcN : c < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  -- `y ≠ 0`, so `c` has a counted child in `M`
  have hyz : y ≠ z := by rintro rfl; exact T.not_lt_z _ htr.1
  obtain ⟨d, hd, hdc⟩ : ∃ d, d ∈ children M c ∧ Counted M c d := by
    by_contra hno
    push Not at hno
    have := o_of_no_counted I.cons hcM (I.good.ot_v c hcM) hno
    rw [hy] at this; simp only [psi.injEq] at this
    exact hyz this.2.1
  -- a counted child of `c` in `N`
  obtain ⟨d', hd', hdc'⟩ : ∃ d', d' ∈ children (TRIO.gexp M r L 0 0 n) c ∧
      Counted (TRIO.gexp M r L 0 0 n) c d' := by
    have hdl := (mem_children hd).1
    by_cases hcg : par M 0 r = some c
    · have hchN := children_g0 hlen hL hp hn hcg
      by_cases hdr : d < r
      · refine ⟨d, by rw [hchN]; exact List.mem_append_left _ hd, ?_⟩
        exact (counted_lt0 hlen hL hp hn I.r0p I.z2 he2 hn2 hc hdr).mpr hdc
      · have hle := children_g_le hlen hL hp hcg hd
        have hdr' : d = r := by omega
        subst hdr'
        refine ⟨d + (n - 1) * L, ?_, counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn2 hcg hdc⟩
        rw [hchN]
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨n - 2, List.mem_range.mpr (by omega), by
          congr 1; congr 1; omega⟩
    · have hdr : d < r := children_lt_r hlen hL hp hc hcg hd
      refine ⟨d, by rw [children_pre0 hlen hL hp hn hc hcg]; exact hd, ?_⟩
      exact (counted_lt0 hlen hL hp hn I.r0p I.z2 he2 hn2 hc hdr).mpr hdc
  obtain ⟨y0, hy0, hy0z⟩ := o_arg_ne_z hCN hcN hd' hdc'
  rw [hy'] at hy0; simp only [psi.injEq] at hy0
  rw [hy0.2.1]
  show z < y0
  exact lt_of_le_of_ne (z_le y0) (Ne.symm hy0z)

/-- **`T0ShapeR` with (i) only at frames with a nonzero state** (`B ≠ 0`, the kinds `pre`・`cut` of PH3c). -/
def T0ShapeR2 : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → Lhd z y' y →
      (split y' (psi (succ s) z z)).2 = z → (split y (psi (succ s) z z)).2 = z →
      spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ≠ z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true) ∧
    (∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      σ.v c ≠ ρ.v c → par M 1 c ≠ some i → ¬ psi (ρ.v c) z z < psi (succ (ρ.v i)) z z →
      ¬ psi (σ.v c) z z < psi (succ (ρ.v i)) z z) ∧
    (∀ n, 2 ≤ n → ∀ g, par M 0 r = some g →
      Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      (drop1 M (r + L) rk).o r = omid M r L ρ)

theorem t0ShapeR_of (h : T0ShapeR2) : T0ShapeR := by
  intro M ρ rk r L hM hS I R hlen hL hp he1
  obtain ⟨h1, h2, h4⟩ := h M ρ rk r L hM hS I R hlen hL hp he1
  refine ⟨?_, h2, h4⟩
  intro n hn σ hCN i c Lc hi hc hCL hD s y y' hy hy' hl hlo' hlo htr
  by_cases hB : spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = z
  · exact t0_shape1_z I hlen hL hp he1 n hn σ hCN i c Lc hi hc hCL s y y' hy hy' hB htr
  · exact h1 n hn σ hCN i c Lc hi hc hCL hD s y y' hy hy' hl hlo' hlo hB htr

/-- **`hExp` for `t = 0`** with `T0Shape` (iii) proved and (i) narrowed to nonzero states. -/
theorem hExp_t0_mainR2
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hS : T0ShapeR2) (hRest : T0Rest) (hC1 : T0RWResC PTP1) (hC1W : T0RWResC PTP1W)
    (hCT : T0RWResC PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN :=
  hExp_t0_mainR hLast (t0ShapeR_of hS) hRest hC1 hC1W hCT

end Ytosk
