/-
**WfQrH7 (2026-11-01): `qr_chainH`, the q = r chain with `hLocE` replaced by named fields.**
`qr_chainG` (WfQrH5: no `γ`, `hX`, `hOx`, `hrx` proved) where the standard-form conjuncts come from C_strip
(`DQC`, WfQrH6.std_of_DQC), `σ.o c ≠ 0` from `Cons` (WfQrH5.o_ne_z_of_cons), `Single (σ.o Rt)` from the standard
form, and the `o`-frame steps from the frame fields `OFields` (WfQrH3.hOF_of_fields).  Remaining: C_strip, `Ex`,
`OFields`, `hUpgL`, the bump step (WfQrH4.bump_step3 from `LayerF`), the base `ρ1.o r < o(x)`.
-/
import Ytosk.WfQrH5
import Ytosk.WfQrH6
import Ytosk.WfQrH3
import Ytosk.WfQrH4

namespace Ytosk.WfQrH7
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL5 Ytosk.WfQrL6 Ytosk.WfQrL7 Ytosk.WfQrL8 Ytosk.WfQrL9 Ytosk.WfQrL10
  Ytosk.WfQrL16 Ytosk.WfQrL18 Ytosk.WfQrH5 Ytosk.WfQrH6 Ytosk.WfQrH3 Ytosk.WfQrH2

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

/-- **The q = r chain from the named fields** (see the file header). -/
theorem qr_chainH (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
    (hLocH : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r < ρ.o (r + L) → ρP.o r ≠ z → Cons (TRIO.gexp M r L d0 0 n) σ →
        -- C_strip (standard form of the new values)
        (∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) ∧
        Ex n ρP σ.o σ.v ∧
        -- the `o` frame fields
        (∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → DepX M (r + L) true c →
          ∀ η, DQ η false (ρ.o c) (σ.o c) → OFields (ρ.v i) (preState M ρ i L') (ρ.o c) (σ.o c) η) ∧
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
  refine qr_chainG hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hC hG hRM hOS h1x hp1 hrD hRA hR0 hRlast hRd
    hsM hpM Ex hOSD hVS hPre ?_ hC1 hR1 hG1 hr1 hr1z hPv1 Pn hP1 hPs
  intro n hn ρP σ hCP hPr hPrz hCσ
  obtain ⟨hDo, hDv, hEx, hFr, hUpgL, hBW2⟩ := hLocH n hn ρP σ hCP hPr hPrz hCσ
  have hlN := len_N (d0 := d0) (n := n) hlen hn
  have hpos : 0 < (n - 1) * L := Nat.mul_pos (by omega) hL
  have hxN : r + L < (TRIO.gexp M r L d0 0 n).length := by omega
  obtain ⟨hSo, hSv⟩ := std_of_DQC hG hlen hCσ hxN hDo hDv
  have hRx : Rt < r + L := by
    rcases Nat.eq_or_lt_of_le hRA.le with h | h
    · exfalso
      have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hR0; rw [hR0]; rfl
      have h1 : entry M 0 (r + L) ≠ 0 := by
        have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
      rw [h] at hR0e; exact h1 hR0e
    · exact h
  refine ⟨(hSo Rt (by omega) hRd).1, fun i hi hd => (hSo i (by omega) hd).2, hSv,
    fun c hc _ => o_ne_z_of_cons hCσ (by omega), hEx, hSo, ?_, hUpgL, hBW2⟩
  exact hOF_of_fields hlen hPre (fun c hc _ => single_o hC hG (by omega)) (fun c hc hd => (hSo c hc hd).1) hFr


/-- `qr_chainH` with `ρ1.o r ≠ 0` proved (`o_ne_z_of_cons` on `M[1]`). -/
theorem qr_chainH2 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
    (hLocH : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r < ρ.o (r + L) → ρP.o r ≠ z → Cons (TRIO.gexp M r L d0 0 n) σ →
        -- C_strip (standard form of the new values)
        (∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) ∧
        Ex n ρP σ.o σ.v ∧
        -- the `o` frame fields
        (∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → DepX M (r + L) true c →
          ∀ η, DQ η false (ρ.o c) (σ.o c) → OFields (ρ.v i) (preState M ρ i L') (ρ.o c) (σ.o c) η) ∧
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
    (hr1 : ρ1.o r < ρ.o (r + L))
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (TRIO.gexp M r L d0 0 1) ρ1) (hPs : ExpStepQ Pn Ex M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      ρN.o r < ρ.o r ∧ ρN.o r < ρ.o (r + L) ∧ ρN.o r ≠ z ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have h1 : (TRIO.gexp M r L d0 0 1).length = r + 1 * L := TRIO.gexp_length hlen
  refine qr_chainH hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hC hG hRM hOS h1x hp1 hrD hRA hR0 hRlast hRd
    hsM hpM Ex hOSD hVS hPre hLocH hC1 hR1 hG1 hr1 (o_ne_z_of_cons hC1 (by omega)) hPv1 Pn hP1 hPs


/-- `qr_chainH2` with the base bound from `v_{M[1]}(r) ≤ v(r)` (measured: g36_2 + std_a, 17,382 frames, 0 failures;
equality in 16,786). -/
theorem qr_chainH3 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
    (hLocH : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r < ρ.o (r + L) → ρP.o r ≠ z → Cons (TRIO.gexp M r L d0 0 n) σ →
        -- C_strip (standard form of the new values)
        (∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) ∧
        Ex n ρP σ.o σ.v ∧
        -- the `o` frame fields
        (∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → DepX M (r + L) true c →
          ∀ η, DQ η false (ρ.o c) (σ.o c) → OFields (ρ.v i) (preState M ρ i L') (ρ.o c) (σ.o c) η) ∧
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
    (hv1 : ρ1.v r ≤ ρ.v r)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (TRIO.gexp M r L d0 0 1) ρ1) (hPs : ExpStepQ Pn Ex M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      ρN.o r < ρ.o r ∧ ρN.o r < ρ.o (r + L) ∧ ρN.o r ≠ z ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have h1 : (TRIO.gexp M r L d0 0 1).length = r + 1 * L := TRIO.gexp_length hlen
  have hr1M : r < (TRIO.gexp M r L d0 0 1).length := by omega
  have hrM : r < M.length := by omega
  have hr1 : ρ1.o r < ρ.o (r + L) := by
    obtain ⟨Y, hY⟩ := WfSrcC.o_psi_form hC1 hr1M (hG1.ot_v r hr1M)
    rw [ox_eq hC hG hlen h1x hx2 hp1 hrM, hY, psi_lt_psi_z_iff]
    exact Or.inl (lt_of_le_of_lt hv1 (lt_succ_self _))
  exact qr_chainH2 hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hC hG hRM hOS h1x hp1 hrD hRA hR0 hRlast hRd
    hsM hpM Ex hOSD hVS hPre hLocH hC1 hR1 hG1 hr1 hPv1 Pn hP1 hPs

end

end Ytosk.WfQrH7
