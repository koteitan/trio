/-
**WfExQ9 (2026-11-01): the carried property with the chain bound, `PnV3r = PnV3 ∧ σ.o r < o(r)`.**
`expStepQ_V3Y` (WfExQ8) needs `ρP.o r < ρ.o r`, which `hLocH` of WfQrH7.qr_chainH3 does not give; it is carried in
`Pn` instead: on `M[n]` it follows from the `DQ` value at `r ∈ D` (`DQ.lt`).  So `qr_chainH3` runs with
`Pn = PnV3r ρ r`, `Ex = ExDQX M r L ρ` (supplied by `exDQX_of_loc` from the C_strip conjuncts of `hLocH`), and the
base `hP1` is `Inv3V3` of `M[1] = M.take x` with the seed below `o(r)`.
-/
import Ytosk.WfExQ8

namespace Ytosk.WfExQ9
open T Ytosk Ytosk.WfExQ1 Ytosk.WfExQ2 Ytosk.WfExQ4 Ytosk.WfExQ8 Ytosk.WfQrL1 Ytosk.WfQrL7

/-- The carried property with the chain bound at `r`. -/
def PnV3r (ρ : Valn) (r : Nat) (N : Mat) (σ : Valn) : Prop := PnV3 N σ ∧ σ.o r < ρ.o r

/-- **`ExpStepQ` of `PnV3r` with `ExDQX`**, from the three remaining residuals. -/
theorem expStepQ_V3r {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    (hVSF : ExpStepQR PnV3 (fun N σ => VSmallF N σ) (ExDQY M r L ρ) M r L d0 ρ)
    (hVRA : ExpStepQR PnV3 (fun N σ => VSmallRAll N σ) (ExDQY M r L ρ) M r L d0 ρ)
    (hFr : FrameAtN M r L d0) :
    ExpStepQ (PnV3r ρ r) (ExDQX M r L ρ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrD : DepX M (r + L) true r := dep_anc_x S.uat S.z2 S.r12 S.bumpE2 hlen hx2 hA
  have hrx : r < r + L := by omega
  have hY := expStepQ_V3Y S I hlen hL hd0e h1 hx2 hq hVSF hVRA hFr
  intro n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  refine ⟨hY n hn ρP oq vq hCP hGP hPP.1 hCN hGN ⟨hEx, hPP.2⟩, ?_⟩
  rw [glueQ_o_dep hrx hrD]
  obtain ⟨η, hD⟩ := hEx.1.1 r hrx hrD
  exact hD.lt

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

open Ytosk.WfQrL5 Ytosk.WfQrL6 Ytosk.WfQrL8 Ytosk.WfQrL9 Ytosk.WfQrL10 Ytosk.WfQrL16 Ytosk.WfQrL18 Ytosk.WfQrH5
  Ytosk.WfQrH6 Ytosk.WfQrH3 Ytosk.WfQrH2 in
/-- **The q = r chain carrying `Inv3V3`** (`qr_chainH3` with `Pn = PnV3r ρ r`, `Ex = ExDQX`; the `Ex` conjunct of
`hLocH` is gone: it follows from the C_strip conjuncts).  Remaining value residuals: `hVSF`, `hVRA`, `hFr`. -/
theorem qr_chainV3 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
    (hOSD : ∀ i, i < r + L → DepX M (r + L) true i → OShapeD M (r + L) i)
    (hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i)
    (hPre : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      isOT (preState M ρ i L') = true)
    (hLocH : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r < ρ.o (r + L) → ρP.o r ≠ z → Cons (TRIO.gexp M r L d0 0 n) σ →
        -- C_strip (standard form of the new values)
        (∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) ∧
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
    (S : SInv M) (I : Inv3V3 M ρ rkM) (hq : par M 0 (r + L) = some r)
    (hVSF : ExpStepQR PnV3 (fun N σ => VSmallF N σ) (ExDQY M r L ρ) M r L d0 ρ)
    (hVRA : ExpStepQR PnV3 (fun N σ => VSmallRAll N σ) (ExDQY M r L ρ) M r L d0 ρ)
    (hFr : FrameAtN M r L d0)
    (hP1 : PnV3 (TRIO.gexp M r L d0 0 1) ρ1) (hs1 : ρ1.o r < ρ.o r) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ PnV3r ρ r (TRIO.gexp M r L d0 0 n) ρN ∧
      ρN.o r < ρ.o r ∧ ρN.o r < ρ.o (r + L) ∧ ρN.o r ≠ z ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ :=
  WfQrH7.qr_chainH3 hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hC hG hRM hOS h1x hp1 hrD hRA hR0 hRlast hRd
    hsM hpM (ExDQX M r L ρ) hOSD hVS hPre
    (fun n hn ρP σ hCP hlt hne hCN => by
      obtain ⟨ho, hv, hOF, hU, hB⟩ := hLocH n hn ρP σ hCP hlt hne hCN
      exact ⟨ho, hv, WfExQ7.exDQX_of_loc n ρP hlt ho hv, hOF, hU, hB⟩)
    hC1 hR1 hG1 hv1 hPv1 (PnV3r ρ r) ⟨hP1, hs1⟩
    (expStepQ_V3r S I hlen hL hd0e hp1 hx2 hq hVSF hVRA hFr)

end

end Ytosk.WfExQ9
