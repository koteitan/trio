/-
**WfSdP5: the `q = r` chain over `ExpStepT1D` (2026-11-01).**

Copies (suffix `D`) of `qr_chainW`, `qr_mainW` (WfSdH1), `qr_finalW` … `qr_final4SGW` (WfSdH3) and `qr_final4SGW2`
(WfSdP1) with the carried property over `ExpStepT1D` (WfSdP3): the chain also hands `OkD`, and the index-0 condition
in the form "`SeedOK` at every diagonal point of the column" (at `q = r` the only point is `v(r)`:
`qr_only_mu_col`, then `SeedOK v(r)`). `OkD` is made from `SeedC2` (`okD_of_seedC2W`).
`qr_final4SGD2`: the `q = r` chain from the `PV2` drop conclusion, `UAwR`, and the live producers of WfSdP4.
-/
import Ytosk.WfSdP4

namespace Ytosk

open T

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e
/-- **All `n ≥ 2`** (`t = 1`, `q = r`), given the local equations with per-column indices. -/
theorem qr_chainD (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
    {μ br seed : T} (hbr : br ≠ z) (hcb : cof br = .big μ)
    (hgam : ∀ m, gamS μ br seed m ≤ ρ.o (r + L) ∧ gamS μ br seed m ≠ z)
    (hro : ρ.o r = psi μ br z) (hrD : DepX M (r + L) true r)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- the local equations at each level, with per-column indices
    (hLoc : ∀ n, 2 ≤ n → ∀ ρP : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r = gamS μ br seed (n - 2) → ∃ Zf : Nat → T, Zf r = gamS μ br seed (n - 2) ∧
        (∀ i, i < r + L →
          (DepX M (r + L) true i →
            oRhs M (glueZ M (r + L) ρ (shiftV ρP L) Zf) i = fsD (ρ.o i) (Zf i)) ∧
          (DepX M (r + L) false i →
            vRhs M (glueZ M (r + L) ρ (shiftV ρP L) Zf) i = fsD (ρ.v i) (Zf i))) ∧
        Single (fsD (ρ.o Rt) (Zf Rt)) ∧ fsD (ρ.o Rt) (Zf Rt) < ρ.o Rt ∧
        (∀ i, i < r + L → DepX M (r + L) true i → isOT (fsD (ρ.o i) (Zf i)) = true) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → isOT (fsD (ρ.v i) (Zf i)) = true) ∧
        (∀ c, c < r + L → DepX M (r + L) true c → fsD (ρ.o c) (Zf c) ≤ ρ.o c ∧ fsD (ρ.o c) (Zf c) ≠ z) ∧
        (∀ i, ∃ k, n - 2 ≤ k ∧ Zf i = gamS μ br seed k ∧
          (k = 0 → ∀ bb, DepX M (r + L) bb i → i < r + L → ∀ a', ¬ lt μ a' = true → isOT (psi a' br z) = true → DiagAt a' br μ (valB ρ bb i) → SeedOK a' br μ seed)))
    (hHD : HoleDataW M (r + L) ρ μ br μ seed) (hokD : OkD μ br μ seed)
    -- the base `M[1] = M.take x`
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    (hr1 : ρ1.o r = seed)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (TRIO.gexp M r L d0 0 1) ρ1) (hPs : ExpStepT1D Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧ ρN.o r = gamS μ br seed (n - 1) ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have step : ∀ n, 2 ≤ n → ∀ ρP rkP, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Rk (TRIO.gexp M r L d0 0 (n - 1)) rkP → Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Pn (TRIO.gexp M r L d0 0 (n - 1)) ρP → ρP.o r = gamS μ br seed (n - 2) →
      (∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
        (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
          upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ρ.v g = ρP.v g) →
      ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
        Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧ ρN.o r = gamS μ br seed (n - 1) ∧
        (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
        isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧
        root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
    intro n hn ρP rkP hCP hRP hGP hPP hPr hPv
    obtain ⟨Zf, hZr, hF, hsR, hlt, hoto, hotv, hle, hZg⟩ := hLoc n hn ρP hCP hPr
    have hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
        (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
          upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
        (glueZ M (r + L) ρ (shiftV ρP L) Zf).v g = ρP.v g := by
      intro g hg a ha hr
      rw [glueZ_v_lt ρ _ _ (by omega) (hnd n hn g hg a ha hr)]
      exact hPv g hg a ha hr
    have hCN := cons_N_t1 hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) hC hCP
      hagree hF
    have hRN := rk_N_t1 hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) (hnd n hn)
      hRM hRP
    have hlex : ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z := by rw [hPr]; exact hgam (n - 2)
    have hGN := good3_N_t1 hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) hC hG hGP hOS
      hoto hotv hle hlex
    refine ⟨_, _, hCN, hRN, hGN, hPs n hn ρP Zf hCP hGP hPP hCN hGN hoto hotv hle hlex
      ⟨μ, br, μ, seed, n - 2, hHD, hokD, hZg, hPr, rfl, rfl, hro⟩, ?_, ?_, ?_⟩
    · rw [glueZ_o_dep ρ _ Zf (by omega) hrD, hro, fsD_here hbr hcb, hZr]
      rw [show n - 1 = (n - 2) + 1 by omega]; rfl
    · intro g hg hd
      exact glueZ_v_lt ρ _ _ hg hd
    · exact root_N_t1 hlen hL hA hd0e hn (ρN := shiftV ρP L) (Z := Zf)
        hRA hR0 hRlast hRd hsM hpM hsR hlt
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    exact step 2 (le_refl _) ρ1 rk1 hC1 hR1 hG1 hP1 hr1 (fun g hg a ha hr => hPv1 g hg a (by omega) hr)
  | succ n hn ih =>
    obtain ⟨ρP, rkP, hCP, hRP, hGP, hPP, hPr, hPd, _⟩ := ih
    apply step (n + 1) (by omega) ρP rkP (by simpa using hCP) (by simpa using hRP) (by simpa using hGP)
      (by simpa using hPP)
      (by rw [show n + 1 - 2 = n - 1 by omega]; exact hPr)
    intro g hg a ha hr
    exact (hPd g (by omega) (hnd (n + 1) (by omega) g hg a ha hr)).symm
end

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e
/-- **All `n ≥ 2`** (`t = 1`, `q = r`), given the local conditions with the per-column indices. -/
theorem qr_mainD (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
    {μ br seed : T} (hbr : br ≠ z) (hcb : cof br = .big μ)
    (hro : ρ.o r = psi μ br z) (hrD : DepX M (r + L) true r)
    (hox : ∀ ζ, fsD (ρ.o (r + L)) ζ = ζ)
    (hgam : ∀ m, gamS μ br seed m ≤ ρ.o (r + L) ∧ gamS μ br seed m ≠ z)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- the lifts
    {lo : Nat → Nat → Nat} {lb : Nat → Nat → Nat → Nat}
    (hxv : ¬ DepX M (r + L) false (r + L))
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i)
    (hdr : dOf M (r + L) lo lb r = 0)
    -- the local conditions and the root at every level
    (hO : ∀ m i, i < r + L → DepX M (r + L) true i →
      OLocZ M (r + L) ρ (zfQ M (r + L) lo lb μ br seed m) i)
    (hV : ∀ m i, i < r + L → DepX M (r + L) false i →
      VLocZ M (r + L) ρ (zfQ M (r + L) lo lb μ br seed m) i)
    (hRt : ∀ m, Single (fsD (ρ.o Rt) (zfQ M (r + L) lo lb μ br seed m Rt)) ∧
      fsD (ρ.o Rt) (zfQ M (r + L) lo lb μ br seed m Rt) < ρ.o Rt)
    (hOT : ∀ m, (∀ i, i < r + L → DepX M (r + L) true i →
        isOT (fsD (ρ.o i) (zfQ M (r + L) lo lb μ br seed m i)) = true) ∧
      (∀ i, i < r + L → DepX M (r + L) false i →
        isOT (fsD (ρ.v i) (zfQ M (r + L) lo lb μ br seed m i)) = true) ∧
      (∀ c, c < r + L → DepX M (r + L) true c →
        fsD (ρ.o c) (zfQ M (r + L) lo lb μ br seed m c) ≤ ρ.o c ∧
        fsD (ρ.o c) (zfQ M (r + L) lo lb μ br seed m c) ≠ z))
    (hHD : HoleDataW M (r + L) ρ μ br μ seed) (hokD : OkD μ br μ seed)
    (hdiag0 : ∀ bb i, DepX M (r + L) bb i → i < r + L → dOf M (r + L) lo lb i = 0 →
      ∀ a', ¬ lt μ a' = true → isOT (psi a' br z) = true → DiagAt a' br μ (valB ρ bb i) → SeedOK a' br μ seed)
    -- the base `M[1] = M.take x`
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    (hr1 : ρ1.o r = seed)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (TRIO.gexp M r L d0 0 1) ρ1) (hPs : ExpStepT1D Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧ ρN.o r = gamS μ br seed (n - 1) ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have hdx : dOf M (r + L) lo lb (r + L) = 0 := dOf_x hx hxv hOS hVS
  refine qr_chainD hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hC hG hRM hOS hbr hcb hgam hro hrD hRA
    hR0 hRlast hRd hsM hpM ?_ hHD hokD hC1 hR1 hG1 hr1 hPv1 Pn hP1 hPs
  intro n _ ρP _ hPr
  refine ⟨zfQ M (r + L) lo lb μ br seed (n - 2), ?_, ?_, (hRt (n - 2)).1, (hRt (n - 2)).2, (hOT (n - 2)).1,
    (hOT (n - 2)).2.1, (hOT (n - 2)).2.2, fun i => ⟨_, Nat.le_add_right _ _, rfl,
      fun hk bb hd hi => hdiag0 bb i hd hi (by omega)⟩⟩
  · unfold zfQ; rw [hdr, Nat.add_zero]
  · apply qr_path hC hG hx ?_ (hO (n - 2)) (hV (n - 2))
    show ρP.o (r + L - L) = _
    rw [show r + L - L = r by omega, hox, hPr]
    unfold zfQ; rw [hdx, Nat.add_zero]
end


section

/-- **`qr_final` with `SeedOK μ` and `HokQ`** in place of `SeedOK` at every diagonal point, and the chain over
`HoleDataW` / `ExpStepT1D`. -/
theorem qr_finalD {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
    (hTP : TP1WC M ρ) (hTPL : TPLoWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r)) (hAU' : AbsUWL M ρ) (hAD' : AbsDWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r))
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- `A = o(r) = ψ_μ(b + Ω_{μ+1})`
    {b : T} (hro : ρ.o r = psi (ρ.v r) (app b (psi (succ (ρ.v r)) z z)) z)
    (hb : AllGeT (psi (succ (ρ.v r)) z z) b)
    (hpre : preState M ρ r ((children M r).filter (fun d => decide (d < r + L))) = b)
    -- the frames with the child `ψ_s(b_r)`
    (hYB : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → Counted M i c →
      DepX M (r + L) true c → ∀ s, ρ.o c = psi s (app b (psi (succ (ρ.v r)) z z)) z →
      lt (preState M ρ i L') (app b (psi (succ (ρ.v r)) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app b (psi (succ (ρ.v r)) z z)) z) = true →
      ∀ m', lt (preState M ρ i L')
        (app b (gamS (ρ.v r) (app b (psi (succ (ρ.v r)) z z)) ((drop1 M (r + L) rkM).o r)
          (m' + dOf M (r + L) (loQ M ρ (ρ.v r) b) (lbQ M ρ (ρ.v r) b) c))) = true)
    -- the seed `o_{M[1]}(r)`
    (hSr : SeedOK (ρ.v r) (app b (psi (succ (ρ.v r)) z z)) (ρ.v r) ((drop1 M (r + L) rkM).o r))
    (hok0 : HokQ (ρ.v r) (app b (psi (succ (ρ.v r)) z z)) (ρ.v r) ((drop1 M (r + L) rkM).o r))
    (hokD : OkD (ρ.v r) (app b (psi (succ (ρ.v r)) z z)) (ρ.v r) ((drop1 M (r + L) rkM).o r))
    (hsp0 : spArg (ρ.v r) b ((drop1 M (r + L) rkM).o r) = app b ((drop1 M (r + L) rkM).o r))
    (hADs0 : ∀ i, i < r + L →
      DepX M (r + L) false i → entry M 2 i ≠ 0 →
      dOf M (r + L) (loQ M ρ (ρ.v r) b) (lbQ M ρ (ρ.v r) b) i = 0 →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
        q < fsD (bumpW M ρ i) ((drop1 M (r + L) rkM).o r))
    (hAUs0 : ∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k →
      dOf M (r + L) (loQ M ρ (ρ.v r) b) (lbQ M ρ (ρ.v r) b) i = 0 →
      OHole (last (ρ.v k)) → cof (last (ρ.v k)) = .omega →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) →
        q < fsD (last (ρ.v k)) ((drop1 M (r + L) rkM).o r))
    (hLs : ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) b) (lbQ M ρ (ρ.v r) b) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ (ρ.v r)) z z) →
      (split y (psi (succ s) z z)).2 = z →
      (split (fsD y ((drop1 M (r + L) rkM).o r)) (psi (succ s) z z)).2 = z)
    (hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rkM))
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1D Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r < r + L := by omega
  have hrM : r < M.length := by omega
  have hpath := hpath_of_par1 h1 hA (by omega)
  set μ := ρ.v r with hμ
  set seed := (drop1 M (r + L) rkM).o r with hseed
  have hox : ρ.o (r + L) = psi (succ μ) z z :=
    o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2
  have hdep := qr_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq
  have hOS := hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq
  have hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i :=
    fun i hi hv => dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hv
  have hS3 := hS3_t1 h1 hA (by omega) hlen hR0 hZ2 hSD hZ1
  have hBk : ∀ i j k, i < r + L → DepX M (r + L) false i → j ∈ children M i → col M j = bump M i →
      k ∈ children M j → DepX M (r + L) true k → k < r + L := by
    intro i j k hi hv hj hjb hk hdk
    have hir : i ≤ r := by
      by_contra h
      exact hdep.2.2 false i (by omega) hi hv
    have := hS3 i j k hir hj hjb hk hdk
    omega
  have hxv : ¬ DepX M (r + L) false (r + L) := by
    intro h
    cases h with
    | vpar _ hp hdm =>
      rw [h1] at hp; cases hp
      exact hdep.2.1 hdm
    | vupg _ _ hu _ => have := upg_succ_lt hu; omega
    | vbump _ h2 _ _ _ _ => exact h2 hx2
  -- the base `M[1] = M.take x`
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hseedS : ∃ a X, seed = psi a X z := by
    obtain ⟨σ, hσ⟩ := o_psi_sub hC1 hrT
    exact ⟨_, σ, hσ⟩
  -- the lifts
  have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  obtain ⟨hxcb, hxcu⟩ := qr_x_counted hx h1 hx2 hq
  have hdr : dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) r = 0 := by
    rw [dOf_ochild hx hxv hOS hVS hxr hxcb hxcu DepX.leaf, dOf_x hx hxv hOS hVS]
    unfold loQ
    rw [if_neg]
    rintro ⟨h, _⟩
    rw [hox] at h
    exact absurd (T.psi.inj h).2.1.symm (fun he => absurd (app_eq_z he).2 (by simp))
  -- the root
  obtain ⟨Rt, hRA, hRt0, hRlast⟩ := root_t1 hR01 hR12 h00 (r + L)
  have hRd := dep_anc_x hUAT hZ2 hR12 hBE hlen hx2 hRA
  have hRx : Rt < r + L := by
    rcases Nat.lt_or_ge Rt (r + L) with h | h
    · exact h
    · exfalso
      have : Rt = r + L := by have := hRA.le; omega
      rw [this] at hRt0
      have h2 := congrArg (fun p : Nat × Nat × Nat => p.2.1) hRt0
      have he : entry M 1 (r + L) = 0 := by
        unfold entry; unfold col at h2; simpa using h2
      have := par1_entry_lt h1; omega
  have hrot : isOT (psi μ (app b (psi (succ μ) z z)) z) = true := by rw [← hro]; exact hG.ot_o r hrM
  have hseedz : seed ≠ z := by obtain ⟨a, X, he⟩ := hseedS; rw [he]; simp
  have hgS : ∀ k, ∃ a X, gamS μ (app b (psi (succ μ) z z)) seed k = psi a X z := by
    intro k; cases k with
    | zero => exact hseedS
    | succ k => exact ⟨μ, _, rfl⟩
  -- the holes of the `D` values give standard, smaller, nonzero values
  have hHok : ∀ bb i, DepX M (r + L) bb i → i < r + L → ∀ m,
      isOT (fsD (valB ρ bb i) (zfQ M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) μ
        (app b (psi (succ μ) z z)) seed m i)) = true ∧
      fsD (valB ρ bb i) (zfQ M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) μ
        (app b (psi (succ μ) z z)) seed m i) < valB ρ bb i := by
    intro bb i hd hi m
    obtain ⟨hH, _⟩ := qr_holeD hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hro hox hOS bb i hd hi
    have hot : isOT (valB ρ bb i) = true := by
      cases bb
      · exact hG.ot_v i (by omega)
      · exact hG.ot_o i (by omega)
    exact hok0 _ (m + dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) i) hot hH
      (fun h0 => qr_only_mu_col hx hC hG hKD hTD hq hro hOS hVS hBk hxv hd hi (by omega))
  have hOT : ∀ m, (∀ i, i < r + L → DepX M (r + L) true i →
        isOT (fsD (ρ.o i) (zfQ M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) μ
          (app b (psi (succ μ) z z)) seed m i)) = true) ∧
      (∀ i, i < r + L → DepX M (r + L) false i →
        isOT (fsD (ρ.v i) (zfQ M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) μ
          (app b (psi (succ μ) z z)) seed m i)) = true) ∧
      (∀ c, c < r + L → DepX M (r + L) true c →
        fsD (ρ.o c) (zfQ M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) μ (app b (psi (succ μ) z z)) seed m c)
          ≤ ρ.o c ∧
        fsD (ρ.o c) (zfQ M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) μ (app b (psi (succ μ) z z)) seed m c)
          ≠ z) := by
    intro m
    refine ⟨fun i hi hd => (hHok true i hd hi m).1, fun i hi hd => (hHok false i hd hi m).1,
      fun c hc hd => ⟨(hHok true c hd hc m).2.le, ?_⟩⟩
    have hcM : c < M.length := by omega
    obtain ⟨hH, _⟩ := qr_holeD hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hro hox hOS true c hd hc
    simp only [valB, cond_true] at hH
    exact single_ne_z (single_fsD (o_psi_form hC hcM) (holeT_not_succ hH)
      (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hH)) (hgS _)
      (hok0 _ (m + dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c) (hG.ot_o c hcM) hH
        (fun h0 => qr_only_mu_col hx hC hG hKD hTD hq hro hOS hVS hBk hxv hd hc (by omega))).1)
  have hRt : ∀ m, Single (fsD (ρ.o Rt) (zfQ M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) μ
        (app b (psi (succ μ) z z)) seed m Rt)) ∧
      fsD (ρ.o Rt) (zfQ M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) μ (app b (psi (succ μ) z z)) seed m Rt)
        < ρ.o Rt := by
    intro m
    obtain ⟨hHR, _⟩ := qr_holeD hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hro hox hOS
      true Rt hRd hRx
    simp only [valB, cond_true] at hHR
    have hRM' : Rt < M.length := by omega
    have hok := hok0 _ (m + dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) Rt) (hG.ot_o Rt hRM') hHR
      (fun h0 => qr_only_mu_col hx hC hG hKD hTD hq hro hOS hVS hBk hxv hRd hRx (by omega))
    refine ⟨?_, hok.2⟩
    exact single_fsD (o_psi_form hC hRM') (holeT_not_succ hHR)
      (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHR)) (hgS _) hok.1
  intro n hn
  obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, _, _, hot, hlt⟩ :=
    qr_mainD hlen hL hA hd0e hpath hx2 (hxnb_t1 hlen hL hA hd0e hZ2 hZ1 h1) (hZ2 r)
      (fun n hn => hiu_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn)
      (fun n hn => hiux_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn)
      (hnd_t1 hlen hL hA hd0e hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2) hC hG hRM
      (fun h => absurd (app_eq_z h).2 (by simp)) cof_br hro hdep.1 (fun ζ => by
        rw [hox]; exact fsD_leaf (isSucc_succ μ) (succ_ne_z μ))
      (fun m => ⟨by rw [hox]; exact (gamS_lt_om hrot cof_br (lt_irrefl' μ) hSr m).le,
        gamS_ne_z_q hseedz m⟩)
      hRA hRt0 hRlast hRd hsM hpM hxv hOS hVS hdr
      (fun m => qr_olocW hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hro rfl hb hpre hox
        hOS hVS hBk hxv hSr hok0 hseedS hsp0 hTP hTPL hYB hLs m)
      (fun m => qr_vlocW hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hro hox hOS hb hVS
        hBk hxv hseedS hTPL hLs hSr hok0 hAU' hAUs0 hAD' hADs0 m)
      hRt hOT ⟨hrot, cof_br, lt_irrefl' μ, hSr, hok0, hseedS, fun bb i hd hi =>
        (qr_holeD hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hro hox hOS bb i hd hi).1⟩
      hokD (fun bb i hd hi h0 a' _ _ hD => by
        rw [qr_only_mu_col hx hC hG hKD hTD hq hro hOS hVS hBk hxv hd hi h0 a' hD]; exact hSr)
      (ρ1 := drop1 M (r + L) rkM) (rk1 := rkM) (by rw [gexp_one_eq hlen]; exact hC1)
      (by rw [gexp_one_eq hlen]; exact hRk1) (by rw [gexp_one_eq hlen]; exact hG1) rfl
      (fun g hg a ha h => by
        rw [gexp_one_eq hlen] at h
        exact base_v_read hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hg ha h)
      Pn (by rw [gexp_one_eq hlen]; exact hP1) hPs n hn
  exact ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩
end

section

/-- **`qr_final2` with `SeedOK μ` and `HokQ`** (`b = qrB`). -/
theorem qr_final2D {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
    (hTP : TP1WC M ρ) (hTPL : TPLoWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r)) (hAU' : AbsUWL M ρ) (hAD' : AbsDWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r))
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hYB : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → Counted M i c →
      DepX M (r + L) true c → ∀ s,
      ρ.o c = psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z) = true →
      ∀ m', lt (preState M ρ i L') (app (qrB M ρ r (r + L))
        (gamS (ρ.v r) (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) ((drop1 M (r + L) rkM).o r)
          (m' + dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L)))
            (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) c)))
        = true)
    (hSr : SeedOK (ρ.v r) (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) (ρ.v r)
      ((drop1 M (r + L) rkM).o r))
    (hok0 : HokQ (ρ.v r) (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) (ρ.v r)
      ((drop1 M (r + L) rkM).o r))
    (hokD : OkD (ρ.v r) (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) (ρ.v r)
      ((drop1 M (r + L) rkM).o r))
    (hsp0 : spArg (ρ.v r) (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r) =
      app (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r))
    (hADs0 : ∀ i, i < r + L →
      DepX M (r + L) false i → entry M 2 i ≠ 0 →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L))) (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) i = 0 →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
        q < fsD (bumpW M ρ i) ((drop1 M (r + L) rkM).o r))
    (hAUs0 : ∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L))) (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) i = 0 →
      OHole (last (ρ.v k)) → cof (last (ρ.v k)) = .omega →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) →
        q < fsD (last (ρ.v k)) ((drop1 M (r + L) rkM).o r))
    (hLs : ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L))) (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z) →
      (split y (psi (succ s) z z)).2 = z →
      (split (fsD y ((drop1 M (r + L) rkM).o r)) (psi (succ s) z z)).2 = z)
    (hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rkM))
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1D Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  obtain ⟨b, hro, hbe, hb⟩ := qr_o_r hlen hR0 hSD h1 hx2 hq hC hG hRM
  have hbq : b = qrB M ρ r (r + L) := hbe
  subst hbq
  exact qr_finalD hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hq hC hG hRM hKD hTD
    hTP hTPL hAU' hAD' hsM hpM hro hb rfl hYB hSr hok0 hokD hsp0 hADs0 hAUs0 hLs hG1 Pn hP1 hPs
end

section

/-- **`qr_final3G2` with the seed condition `SeedC2`** (no `SmallSelf`): the strong branch gives `SeedOK` at every
diagonal point as before, the weak branch `SeedOK μ` and `HokQ` (`hok_of_seedC2`). -/
theorem qr_final3GD {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    -- the conclusion of the drop lemma and the seed condition
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
    (hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rkM) i ∧ PV2 M ρ (drop1 M (r + L) rkM) i)
    (hseedC : SeedC2 (ρ.v r) (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r))
    -- value invariants
    (hTP : TP1WC M ρ) (hTPL : TPLoWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r)) (hAU' : AbsUWL M ρ) (hAD' : AbsDWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r))
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- `q = r`
    (hTP1 : TP1C M ρ)
    (hYBs : (drop1 M (r + L) rkM).o r < psi (ρ.v r) one z →
      ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      Counted M i c → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L)))
        (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) c = 0 → ∀ s,
      ρ.o c = psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z) = true →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r)) = true)
    (hADs0 : ∀ i, i < r + L →
      DepX M (r + L) false i → entry M 2 i ≠ 0 →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L))) (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) i = 0 →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
        q < fsD (bumpW M ρ i) ((drop1 M (r + L) rkM).o r))
    (hAUs0 : ∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L))) (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) i = 0 →
      OHole (last (ρ.v k)) → cof (last (ρ.v k)) = .omega →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) →
        q < fsD (last (ρ.v k)) ((drop1 M (r + L) rkM).o r))
    (hLs0 : ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L))) (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z) →
      (split y (psi (succ s) z z)).2 = z →
      (split (fsD y ((drop1 M (r + L) rkM).o r)) (psi (succ s) z z)).2 = z)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1D Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have hr : r < r + L := by omega
  have hrM : r < M.length := by omega
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  set μ := ρ.v r with hμ
  set b := qrB M ρ r (r + L) with hbdef
  set seed := (drop1 M (r + L) rkM).o r with hseed
  -- `o(r) = A`
  obtain ⟨b0, hro, hbe, hb⟩ := qr_o_r hlen hR0 hSD h1 hx2 hq hC hG hRM
  have hbb : b0 = b := hbe
  rw [hbb] at hro hb
  have hrot : isOT (psi μ (app b (psi (succ μ) z z)) z) = true := by rw [← hro]; exact hG.ot_o r hrM
  have hdep := qr_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq
  have hxv : ¬ DepX M (r + L) false (r + L) := by
    intro h
    cases h with
    | vpar _ hp hdm =>
      rw [h1] at hp; cases hp
      exact hdep.2.1 hdm
    | vupg _ _ hu _ => have := upg_succ_lt hu; omega
    | vbump _ h2 _ _ _ _ => exact h2 hx2
  -- the drop lemma
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hlt : seed < ρ.o r := dep_strict02 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hx2 hq hxv
    true r hdep.1 hr
  have hsing := (hdrop r hr).1.2
  -- the form of the seed
  obtain ⟨σ1, hs1⟩ := o_psi_sub hC1 hrT
  set s1 := sf ((drop1 M (r + L) rkM).v r) with hs1def
  have hs1' : seed = psi s1 σ1 z := hs1
  have hsot : isOT (psi s1 σ1 z) = true := by rw [← hs1]; exact hsing.1
  have hlt' : psi s1 σ1 z < psi μ (app b (psi (succ μ) z z)) z := by rw [← hs1, ← hro]; exact hlt
  have hseedz : seed ≠ z := by rw [hs1']; simp
  -- `spArg(μ, b, seed) = b + seed`
  have hsp0 : spArg μ b seed = app b seed := by rw [hs1']; exact spArg_seed hb hsot hlt'
  -- `SeedOK`
  have hbot : isOT b = true := isOT_app_left (isOT_arg hrot)
  have hS_strong : Lhd z seed (psi μ (app b (psi (succ μ) z z)) z) →
      ∀ a', ¬ lt μ a' = true → isOT (psi a' (app b (psi (succ μ) z z)) z) = true →
      SeedOK a' (app b (psi (succ μ) z z)) μ seed := by
    intro hlhd' a' ha' hot'
    have hlhd : Lhd z seed (ρ.o r) := by rw [hro]; exact hlhd'
    rw [hs1']
    have hsub := hlt'
    rw [psi_lt_psi_z_iff] at hsub
    rcases hsub with hsμ | ⟨hsμ, hσb⟩
    · -- the subscript is below `μ`
      apply seedOK_of_lhd_below ha' hsot hsμ
      · rw [← hro, ← hs1']; exact hlhd
      · have hl2 : Lhd z (psi s1 σ1 z) (psi μ (app b (psi (succ μ) z z)) z) := by
          rw [← hro, ← hs1']; exact hlhd
        exact SeedComps.seed_comps_lt hl2 hsμ ha' hot'
    · -- the subscript is `μ`
      rw [hsμ] at hsot ⊢
      have hl' : Lhd z (psi μ σ1 z) (psi μ (app b (psi (succ μ) z z)) z) := by
        rw [← hro]; rw [hs1', hsμ] at hlhd; exact hlhd
      exact seedOK_of_lhd_top hot' cof_br ha' hsot hσb hl'
  -- `SeedC2`: the strong branch gives the old `hS`; the weak branch `SeedOK μ` and `HokQ` (`hok_of_seedC2`)
  obtain ⟨hSr, hok0⟩ : SeedOK μ (app b (psi (succ μ) z z)) μ seed ∧ HokQ μ (app b (psi (succ μ) z z)) μ seed := by
    rcases hseedC with hl | ⟨_, _, _, hSr, hl⟩
    · exact ⟨hS_strong hl μ (lt_irrefl' μ) hrot, hokQ_of_S hrot cof_br (lt_irrefl' μ) (hS_strong hl)⟩
    · exact ⟨hSr, hokQ_of_seedC2 hrot hSr hl⟩
  have hokD : OkD μ (app b (psi (succ μ) z z)) μ seed := okD_of_seedC2W hrot hS_strong hseedC
  -- the (L)(ii) at the seed
  have hLs : ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ μ) z z) →
      (split y (psi (succ s) z z)).2 = z → (split (fsD y seed) (psi (succ s) z z)).2 = z := by
    exact hLs0
  -- The seed bound is used only when the child's lift count is zero.
  have hYB : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      Counted M i c → DepX M (r + L) true c → ∀ s, ρ.o c = psi s (app b (psi (succ μ) z z)) z →
      lt (preState M ρ i L') (app b (psi (succ μ) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app b (psi (succ μ) z z)) z) = true →
      ∀ m', lt (preState M ρ i L') (app b (gamS μ (app b (psi (succ μ) z z)) seed
        (m' + dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c))) = true := by
    intro i L' c R hi hd hch hcnt hdc s hcv htr1 htr2 m'
    have h0 := hTP1 i L' c R hch hcnt s _ hcv htr1 htr2 (ohole_of_cof_big cof_br)
    rw [holeLev_cof cof_br, fsD_eq_fs cof_br, fs_br] at h0
    set d := dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c
    by_cases h1s : psi μ one z ≤ gamS μ (app b (psi (succ μ) z z)) seed (m' + d)
    · refine lt_of_lt_of_le (show preState M ρ i L' < app b (psi μ one z) from h0) ?_
      rcases (le_iff _ _).mp h1s with h | h
      · exact le_of_lt (app_lt_app_left b h)
      · rw [h]
    · have hz : m' + d = 0 := by
        by_contra hn
        obtain ⟨k, hk⟩ : ∃ k, m' + d = k + 1 := ⟨m' + d - 1, by omega⟩
        rw [hk] at h1s
        exact h1s (gamS_ge_psi1 hseedz k)
      have hd0 : d = 0 := by omega
      rw [hz]
      have hlt1 : seed < psi μ one z := by
        rcases lt_trichotomy' seed (psi μ one z) with h | h | h
        · exact h
        · exact (h1s (by rw [hz]; change psi μ one z ≤ seed; rw [h])).elim
        · exact (h1s (by rw [hz]; exact le_of_lt h)).elim
      exact hYBs hlt1 i L' c R hi hd hch hcnt hdc hd0 s hcv htr1 htr2
  exact qr_final2D hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hq hC hG hRM hKD hTD
    hTP hTPL hAU' hAD' hsM hpM hYB hSr hok0 hokD hsp0 hADs0 hAUs0 hLs
    (good3_take2 (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop) Pn hP1 hPs
end

section

/-- Shared final assembly with the trigger restricted to zero-lift children. -/
theorem qr_final4_seedGD {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    -- the conclusion of the drop lemma and the seed condition
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
    (hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rkM) i ∧ PV2 M ρ (drop1 M (r + L) rkM) i)
    (hseedC : SeedC2 (ρ.v r) (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r))
    -- value invariants
    (hTP : TP1WC M ρ) (hTPL : TPLoWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r)) (hAU' : AbsUWL M ρ) (hAU0 : AbsUW0 M ρ rkM) (hAD' : AbsDWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r))
    (hTP1 : TP1C M ρ) (hYBs : (drop1 M (r + L) rkM).o r < psi (ρ.v r) one z →
      ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      Counted M i c → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L)))
        (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) c = 0 →
      ∀ s, ρ.o c = psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z) = true →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r)) = true) (hTPN : TPLoN M ρ) (hADN : AbsDN M ρ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- the seed
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1D Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have hrx : r < r + L := by omega
  have hrM : r < M.length := by omega
  set μ := ρ.v r with hμ
  set b := qrB M ρ r (r + L) with hbdef
  set seed := (drop1 M (r + L) rkM).o r with hseed
  obtain ⟨b0, hro, hbe, hb⟩ := qr_o_r hlen hR0 hSD h1 hx2 hq hC hG hRM
  have hbb : b0 = b := hbe
  rw [hbb] at hro hb
  have hdep := qr_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq
  have hOS := hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq
  have hVS' : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i :=
    fun i hi hv => dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hv
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hS3 := hS3_t1 h1 hA (by omega) hlen hR0 hZ2 hSD hZ1
  have hBk : ∀ i j k, i < r + L → DepX M (r + L) false i → j ∈ children M i → col M j = bump M i →
      k ∈ children M j → DepX M (r + L) true k → k < r + L := by
    intro i j k hi hv hj hjb hk hdk
    have hir : i ≤ r := by
      by_contra h
      exact hdep.2.2 false i (by omega) hi hv
    have := hS3 i j k hir hj hjb hk hdk
    omega
  have hxv : ¬ DepX M (r + L) false (r + L) := by
    intro h
    cases h with
    | vpar _ hp hdm =>
      rw [h1] at hp; cases hp
      exact hdep.2.1 hdm
    | vupg _ _ hu _ => have := upg_succ_lt hu; omega
    | vbump _ h2 _ _ _ _ => exact h2 hx2
  have hox : ρ.o (r + L) = psi (succ μ) z z :=
    o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2
  -- the base
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hseedz : seed ≠ z := by
    obtain ⟨σ1, hs1⟩ := o_psi_sub hC1 hrT
    show (drop1 M (r + L) rkM).o r ≠ z
    rw [hs1]; simp
  have h1s : one ≤ seed := one_le_of_ne_z hseedz
  -- the DiagAt and the `A`-freeness of lift-free columns
  have hdiag : ∀ bb c, c < r + L → DepX M (r + L) bb c →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
      DiagAt μ (app b (psi (succ μ) z z)) μ (valB ρ bb c) ∧
      (bb = true → (∀ s y, ρ.o c = psi s y z → ∀ a, last y = psi a z z →
          a ≠ psi μ (app b (psi (succ μ) z z)) z)) ∧
      (bb = false → last (ρ.v c) ≠ psi μ (app b (psi (succ μ) z z)) z) := by
    intro bb c hc hdc hd0
    obtain ⟨d, hd⟩ := depL_of_depX (lo := loQ M ρ μ b) (lb := lbQ M ρ μ b) hdc
    have hdd : d = 0 := by
      cases bb with
      | true => rw [← dOf_o hx hxv hOS hVS' (by omega) hd]; exact hd0
      | false => rw [← dOf_v hx hxv hOS hVS' (by omega) hd]; exact hd0
    have hNA := qr_lastNA hx hC hG hKD hTD hq hro hOS hVS' hBk hb hd hc hdd
    refine ⟨qr_diag0 hx hC hG hKD hTD hq hro hOS hVS' hBk hd hc hdd, fun h => (hNA.1 h).1, hNA.2⟩
  -- hLs0
  have hLs0 : ∀ c, c < r + L → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
      ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ μ) z z) →
      (split y (psi (succ s) z z)).2 = z → (split (fsD y seed) (psi (succ s) z z)).2 = z := by
    intro c hc hdc hd0 s y hcv hyb hl
    by_cases hyz : y = z
    · subst hyz; simp [fsD, split]
    obtain ⟨hD, hNA, _⟩ := hdiag true c hc hdc hd0
    simp only [valB, cond_true] at hD
    rw [hcv] at hD
    refine lo_keep_Q hD hyz hyb ?_ (le_refl _) hl
    intro hl' a hla hns hOa hca
    have hDy : DiagAt μ _ μ y := DiagAt.arg_inv hD hyz (fun h => hyb h.2)
    have hDl := hDy.last_g
    rw [hla] at hDl
    have hDa : DiagAt μ (app b (psi (succ μ) z z)) μ a := by
      generalize hBB : app b (psi (succ μ) z z) = BB at hDl ⊢
      cases hDl with
      | here hb' _ _ => exact absurd rfl hb'
      | arg hb' _ _ => exact absurd rfl hb'
      | sub _ _ h => exact h
    have hxl : M.length - 1 = r + L := by omega
    have hTPN' := hTPN (drop1 M (r + L) rkM) rkM (by rw [hxl]; exact hC1) (by rw [hxl]; exact hRk1)
    exact hTPN' r μ b (by rw [hxl]; exact h1) (by rw [hxl]; exact hq) (by rw [hxl]; exact hx2) hro c
      (by rw [hxl]; exact hc) (by rw [hxl]; exact hdc) (by rw [hxl]; exact hd0) s y hcv hyb hl' a hla hns hOa hca
      (notNode_of_diag hDa (hNA rfl s y hcv a hla))
  -- hADs0
  have hADs0 : ∀ i, i < r + L → DepX M (r + L) false i → entry M 2 i ≠ 0 →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) i = 0 →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i → q < fsD (bumpW M ρ i) seed := by
    intro i hi hv h2 hd0 q hq hlt
    have hiM : i < M.length := by omega
    obtain ⟨h1', _, hcase⟩ := hVS' i hi hv
    rcases hcase with ⟨h2', _⟩ | ⟨_, L', K, j, k, hch, hjb, hchj, hdk, _, _⟩
    · exact absurd h2' h2
    have hj : j ∈ children M i := by rw [hch]; simp
    have hkj : k ∈ children M j := by rw [hchj]; simp
    have hkx : k < r + L := hBk i j k hi hv hj hjb hkj hdk
    have hdb := dOf_bump hx hxv hOS hVS' (lo := loQ M ρ μ b) (lb := lbQ M ρ μ b) hi h1' h2 hj hjb hkj hdk
    have hdk0 : dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) k = 0 := by omega
    obtain ⟨hDk, _, _⟩ := hdiag true k hkx hdk hdk0
    simp only [valB, cond_true] at hDk
    obtain ⟨_, _, hNAi⟩ := hdiag false i hi hv hd0
    have hNA := hNAi rfl
    have hBD : BumpData M ρ μ i L' K j k := bump_data hC hG hKD hTD h1' h2 hch hjb hchj
    set P := nzs (L'.map (bumpTerm M ρ i)) with hPdef
    set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
    have hGot : isOT G = true := (sumN_dec _ hBD.sK hBD.pK).1
    have hkS : Single (ρ.o k) := hBD.sK _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hGe : G = app (sumN (K.map ρ.o)) (ρ.o k) := sumN_snoc_dec hBD.sK hBD.pK
    have hDG : DiagAt μ (app b (psi (succ μ) z z)) μ G := by
      rw [hGe]; exact DiagAt.append _ (single_ne_z hkS) hDk
    have hωGz : omega G ≠ z := single_ne_z (single_omega hGot)
    have hDW : DiagAt μ (app b (psi (succ μ) z z)) μ (bumpW M ρ i) := by
      rw [hBD.W]
      exact diag_omega hBD.potW (DiagAt.append _ hωGz (diag_omega hGot hDG))
    -- `W` is the last summand of `v(i)`
    have hvi := v_bump_valueG hC hiM h1' h2 hch hjb hchj hBD.sK hBD.pK hBD.sL hBD.pp hBD.gt
      (vOpt_ot hG (by omega))
    have hsW := single_omega hBD.potW
    have hWz : omega (app (sumN P) (omega G)) ≠ z := single_ne_z hsW
    obtain ⟨_, s0, y0, hW0⟩ := hsW
    obtain ⟨B, X, _, _, hadd⟩ := add_prefix s0 y0 (vOpt ρ (par M 1 i))
    have hlast : last (ρ.v i) = bumpW M ρ i := by
      rw [hvi, hW0, hadd, last_app B (by simp), hBD.W, hW0]; rfl
    have hWne : bumpW M ρ i ≠ psi μ (app b (psi (succ μ) z z)) z := by rw [← hlast]; exact hNA
    have h0 := hADN i hiM h1' h2 (ohole_of_diag hDW) (DiagAt.cof_omega hDW)
      (notNode_of_diag hDW hWne) q hq hlt
    exact lt_of_lt_of_le h0 (fsD_mono_eta (ohole_of_diag hDW) h1s)
  have hAUL : AbsUWL M ρ := hAU'
  have hAUs0 : ∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k →
      dOf M (r + L) (loQ M ρ μ b) (lbQ M ρ μ b) i = 0 →
      OHole (last (ρ.v k)) → cof (last (ρ.v k)) = .omega →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) → q < fsD (last (ρ.v k)) seed :=
    fun i k hi hv hu hd hO hc qq hqq hlt => by
      have h := hAU0
      unfold AbsUW0 at h
      rw [show M.length - 1 = r + L by omega] at h
      exact h r μ b h1 hq hx2 hro i k hi hv hu hd hO hc qq hqq hlt
  exact qr_final3GD hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hq hC hG hRM
    hKD hTD hdrop hseedC hTP hTPL hAUL hAD' hsM hpM hTP1 hYBs hADs0 hAUs0 hLs0 Pn hP1 hPs
end

section

/-- The seed trigger of Inv3V2, without the false global TrigOmC. -/
theorem qr_final4SGD {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    -- the conclusion of the drop lemma and the seed condition
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
    (hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rkM) i ∧ PV2 M ρ (drop1 M (r + L) rkM) i)
    (hseedC : SeedC2 (ρ.v r) (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r))
    -- value invariants
    (hTP : TP1WC M ρ) (hTPL : TPLoWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r)) (hAU' : AbsUWL M ρ) (hAU0 : AbsUW0 M ρ rkM) (hAD' : AbsDWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r))
    (hTP1 : TP1C M ρ) (hTS : TrigS0 M ρ rkM) (hTPN : TPLoN M ρ) (hADN : AbsDN M ρ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    -- the seed
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1D Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hlast : M.length - 1 = r + L := by omega
  have hro : ρ.o r = psi (ρ.v r)
      (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z := by
    obtain ⟨b0, hro, hbe, _⟩ := qr_o_r hlen hR0 hSD h1 hx2 hq hC hG hRM
    have hbb : b0 = qrB M ρ r (r + L) := hbe
    rw [hbb] at hro
    exact hro
  have hYBs : (drop1 M (r + L) rkM).o r < psi (ρ.v r) one z →
      ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      Counted M i c → DepX M (r + L) true c →
      dOf M (r + L) (loQ M ρ (ρ.v r) (qrB M ρ r (r + L)))
        (lbQ M ρ (ρ.v r) (qrB M ρ r (r + L))) c = 0 →
      ∀ s, ρ.o c = psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app (qrB M ρ r (r + L)) (psi (succ (ρ.v r)) z z)) z) = true →
      lt (preState M ρ i L') (app (qrB M ρ r (r + L)) ((drop1 M (r + L) rkM).o r)) = true := by
    have h := hTS r (ρ.v r) (qrB M ρ r (r + L))
      (by simpa only [hlast] using h1) (by simpa only [hlast] using hq)
      (by simpa only [hlast] using hx2) hro
    simpa only [hlast] using h
  exact qr_final4_seedGD hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00
    h1 hx2 hq hC hG hRM hKD hTD hdrop hseedC
    hTP hTPL hAU' hAU0 hAD' hTP1 hYBs hTPN hADN hsM hpM Pn hP1 hPs
end


section

/-- **`qr_final4SGD` without `hseedC`**: the seed condition from `qr_seedC2_of` and `UAwR`. -/
theorem qr_final4SGD2 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
    (hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rkM) i ∧ PV2 M ρ (drop1 M (r + L) rkM) i)
    (hUAR : UAwR M ρ (r + L)) (h3 : NoBad3 M ρ ∨ r + 2 = M.length)
    (hTP : TP1WC M ρ) (hTPL : TPLoWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r)) (hAU' : AbsUWL M ρ)
    (hAU0 : AbsUW0 M ρ rkM) (hAD' : AbsDWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r))
    (hTP1 : TP1C M ρ) (hTS : TrigS0 M ρ rkM) (hTPN : TPLoN M ρ) (hADN : AbsDN M ρ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1D Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  obtain ⟨b0, hro, hbe, hb⟩ := qr_o_r hlen hR0 hSD h1 hx2 hq hC hG hRM
  have hbb : b0 = qrB M ρ r (r + L) := hbe
  rw [hbb] at hro hb
  have hlt := qr_seed_lt2 hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq hC hG hRM hdrop
  have hseedC := qr_seedC2_of hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hRM hdrop (par_lt M 1 (r + L) r h1) hro hb
    hlt (fun k W hi hu hvk hWz => hUAR r k W hi hu hvk hWz) h3
  exact qr_final4SGD hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hq hC hG hRM hKD hTD hdrop
    hseedC hTP hTPL hAU' hAU0 hAD' hTP1 hTS hTPN hADN hsM hpM Pn hP1 hPs
end


end Ytosk
