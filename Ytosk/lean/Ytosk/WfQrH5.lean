/-
**WfQrH5 (2026-11-01): the `M`-side facts `hOx`, `hrx` of `qr_chainF` are theorems.**
For the last column `x` (`x + 1 = |M|`, rows 1 nonzero, row 2 zero, `P₁ x = r`): `x` has no children and no upgrade,
so `v(x) = v(r) + 1` and `o(x) = Ω_{v(r)+1}` (`ox_eq`); `o(r) = ψ_{v(r)}(Y) < Ω_{v(r)+1}` (`or_lt_ox`).
-/
import Ytosk.WfQrH1
import Ytosk.WfSrcC1

namespace Ytosk.WfQrH5
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL5 Ytosk.WfQrL6 Ytosk.WfQrL7 Ytosk.WfQrL8 Ytosk.WfQrL9 Ytosk.WfQrL10
  Ytosk.WfQrL16 Ytosk.WfQrL18

section
variable {M : Mat} {ρ : Valn} {x r : Nat}

theorem vx_eq (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length) (h1 : entry M 1 x ≠ 0)
    (h2 : entry M 2 x = 0) (hp : par M 1 x = some r) (hrM : r < M.length) : ρ.v x = succ (ρ.v r) := by
  have hu : upg M x = none := by unfold upg; rw [if_pos (Or.inr (Or.inr hx))]
  rw [(hC x (by omega)).2]
  unfold vRhs
  rw [if_neg h1, if_pos h2, hu, hp]
  simp only [vOpt]
  rw [add_one_eq_succ (hG.ot_v r hrM), sf_ot (isOT_succ (hG.ot_v r hrM))]

theorem ox_eq (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length) (h1 : entry M 1 x ≠ 0)
    (h2 : entry M 2 x = 0) (hp : par M 1 x = some r) (hrM : r < M.length) :
    ρ.o x = psi (succ (ρ.v r)) z z := by
  have hxM : x < M.length := by omega
  rw [(hC x hxM).1, WfQrL10.oRhs_sub (by rw [children_last hx]; simp),
    sf_ot (WfQrL10.isOT_om (hG.ot_v x hxM)), vx_eq hC hG hx h1 h2 hp hrM]

theorem or_lt_ox (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length) (h1 : entry M 1 x ≠ 0)
    (h2 : entry M 2 x = 0) (hp : par M 1 x = some r) (hrM : r < M.length) :
    ρ.o r < ρ.o x := by
  obtain ⟨Y, hY⟩ := WfSrcC.o_psi_form hC hrM (hG.ot_v r hrM)
  rw [ox_eq hC hG hx h1 h2 hp hrM, hY, psi_lt_psi_z_iff]
  exact Or.inl (lt_succ_self _)

end

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

/-- **`qr_chainF` with `hOx`, `hrx` proved** (`ox_eq`, `or_lt_ox`). -/
theorem qr_chainG (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ n, 2 ≤ n → ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ n, 2 ≤ n → ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : ∀ n, 2 ≤ n → isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    (hnd : ∀ n, 2 ≤ n → ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (h1x : entry M 1 (r + L) ≠ 0) (hp1 : par M 1 (r + L) = some r)
    (hrD : DepX M (r + L) true r)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (Ex : Nat → Valn → (Nat → T) → (Nat → T) → Prop)
    (hOSD : ∀ i, i < r + L → DepX M (r + L) true i → OShapeD M (r + L) i)
    (hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i)
    (hPre : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      isOT (preState M ρ i L') = true)
    (hLocE : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r < ρ.o (r + L) → ρP.o r ≠ z → Cons (TRIO.gexp M r L d0 0 n) σ →
        Single (σ.o Rt) ∧
        (∀ i, i < r + L → DepX M (r + L) true i → isOT (σ.o i) = true) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → isOT (σ.v i) = true) ∧
        (∀ c, c < r + L → DepX M (r + L) true c → σ.o c ≠ z) ∧
        Ex n ρP σ.o σ.v ∧
        (∀ c, c ≤ r + L → DepX M (r + L) true c → Single (σ.o c) ∧ isOT (σ.o c) = true) ∧
        (∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → DepX M (r + L) true c →
          (∃ η, DQ η false (ρ.o c) (σ.o c)) →
          ∃ η', DQ η' false (psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L') (ρ.o c)) z)
            (psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L') (σ.o c)) z)) ∧
        (∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k → entry M 2 i = 0 →
          Single (last (ρ.v k)) ∧ Single (last (σ.v k)) ∧
          ∀ η, DQ η true (ρ.v k) (σ.v k) → DQ η false (last (ρ.v k)) (last (σ.v k))) ∧
        (∀ i L' K j k, i < r + L → DepX M (r + L) false i → children M i = L' ++ [j] → col M j = bump M i →
          children M j = K ++ [k] → DepX M (r + L) true k →
          Single (bumpW M ρ i) ∧ Single (bumpWQ M ρ i L' K (σ.o k)) ∧
          ((∃ η, DQ η false (ρ.o k) (σ.o k)) →
            ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L' K (σ.o k)))))
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    (hr1 : ρ1.o r < ρ.o (r + L)) (hr1z : ρ1.o r ≠ z)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (TRIO.gexp M r L d0 0 1) ρ1) (hPs : ExpStepQ Pn Ex M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      ρN.o r < ρ.o r ∧ ρN.o r < ρ.o (r + L) ∧ ρN.o r ≠ z ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hrM : r < M.length := by omega
  exact WfQrH1.qr_chainF hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hC hG hRM hOS
    (ox_eq hC hG hlen h1x hx2 hp1 hrM) (le_of_lt (or_lt_ox hC hG hlen h1x hx2 hp1 hrM)) hrD hRA hR0 hRlast hRd
    hsM hpM Ex hOSD hVS hPre hLocE hC1 hR1 hG1 hr1 hr1z hPv1 Pn hP1 hPs

end

end Ytosk.WfQrH5
