/-
**WfSdH1: the hole data of the `q = r` chain without `SeedOK` at every diagonal point (2026-11-01).**

`HoleData.S` asks `SeedOK a′ b_r μ seed` at every `a′ ≤ μ`; for a weak seed `Ω_{w′}` (the weak branch of
`WfDrE2.SeedC2`) it is false at `a′ = 0`. `HoleDataW` keeps only `SeedOK μ` (`Sr`) and the descent of `fsD` along the
chain, asked at index `0` only on terms whose diagonal points are all `μ` (`ok`; this is what `hok_of_seedC2` gives).
`ExpStepT1W` is `ExpStepT1` over `HoleDataW`, and its index witness also says that at index `0` every `D` value has
`μ` as a diagonal point (what `qr_diag0` gives at lift count `0`), so a producer can supply the index-0 condition.
- `HoleData.toW`: the old hole data gives the new one.
- `omega_fsD_hole_QW`: `omega_fsD_hole_Q` with the descent asked only on terms whose diagonal points are those of `Y`.
- `qr_chainW` / `qr_mainW`: copies of `qr_chain` / `qr_main` over `HoleDataW` / `ExpStepT1W`.
- `qr_diag_col`, `qr_only_mu_col`: at lift count `dOf = 0` every `D` value has `μ` as its only diagonal point.
-/
import Ytosk.WfDrL3

namespace Ytosk

open T

/-- **The descent of `fsD` along the chain**, asked at index `0` only on terms whose diagonal points are all `vr`
(the form `hok_of_seedC2` gives for the weak seeds of `SeedC2`). -/
abbrev HokQ (μ br vr seed : T) : Prop :=
  ∀ t k, isOT t = true → HoleT μ br vr t → (k = 0 → ∀ a', DiagAt a' br μ t → a' = vr) →
    isOT (fsD t (gamS μ br seed k)) = true ∧ fsD t (gamS μ br seed k) < t

/-- `HokQ` from the old seed condition at every diagonal point. -/
theorem hokQ_of_S {μ br vr seed : T} (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ)
    (hμ : ¬ lt μ vr = true)
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed) : HokQ μ br vr seed :=
  fun _ k hot hH _ => hok_of_holeT hrot hcb hμ hS hot hH k

/-- `HokQ` from the weak branch of `SeedC2` (`hok_of_seedC2`). -/
theorem hokQ_of_seedC2 {μ b seed : T}
    (hrot : isOT (psi μ (app b (psi (succ μ) z z)) z) = true)
    (hSr : SeedOK μ (app b (psi (succ μ) z z)) μ seed)
    (hl : Lhd z (psi μ (app b seed) z) (psi μ (app b (psi (succ μ) z z)) z)) :
    HokQ μ (app b (psi (succ μ) z z)) μ seed :=
  fun _ k hot hH h0 => hok_of_seedC2 hrot hSr hl hot hH k h0

/-- **The hole data of the chain without `SeedOK` below `v(r)`.** -/
structure HoleDataW (M : Mat) (x : Nat) (ρ : Valn) (μ br vr seed : T) : Prop where
  rot : isOT (psi vr br z) = true
  cb : cof br = .big μ
  hμ : ¬ lt μ vr = true
  Sr : SeedOK vr br μ seed
  ok : HokQ μ br vr seed
  seedS : ∃ a X, seed = psi a X z
  hole : ∀ bb i, DepX M x bb i → i < x → HoleT μ br vr (valB ρ bb i)

/-- The old hole data gives the new one. -/
theorem HoleData.toW {M : Mat} {x : Nat} {ρ : Valn} {μ br vr seed : T} (h : HoleData M x ρ μ br vr seed) :
    HoleDataW M x ρ μ br vr seed :=
  ⟨h.rot, h.cb, h.hμ, h.S vr (lt_irrefl' vr) h.rot,
    hokQ_of_S h.rot h.cb h.hμ h.S, h.seedS, h.hole⟩

/-- **`ExpStepT1At` over `HoleDataW`**, with the index-0 diagonal points of the `D` values. -/
def ExpStepT1AtW (Pn : Mat → Valn → Prop) (M : Mat) (r L d0 : Nat) (ρ : Valn) (n : Nat) : Prop :=
  ∀ (ρP : Valn) (Z : Nat → T),
    Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP → Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    Pn (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    Good3 (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    (∀ i, i < r + L → DepX M (r + L) true i → isOT (fsD (ρ.o i) (Z i)) = true) →
    (∀ i, i < r + L → DepX M (r + L) false i → isOT (fsD (ρ.v i) (Z i)) = true) →
    (∀ c, c < r + L → DepX M (r + L) true c → fsD (ρ.o c) (Z c) ≤ ρ.o c ∧ fsD (ρ.o c) (Z c) ≠ z) →
    (ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z) →
    (∃ μ br vr seed k0, HoleDataW M (r + L) ρ μ br vr seed ∧
      (∀ i, ∃ k, k0 ≤ k ∧ Z i = gamS μ br seed k ∧
        (k = 0 → ∀ bb, DepX M (r + L) bb i → i < r + L → DiagAt vr br μ (valB ρ bb i))) ∧
      ρP.o r = gamS μ br seed k0 ∧ k0 = n - 2 ∧ μ = vr ∧ ρ.o r = psi vr br z) →
    Pn (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z)

/-- `ExpStepT1AtW` at every `n ≥ 2`. -/
def ExpStepT1W (Pn : Mat → Valn → Prop) (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ExpStepT1AtW Pn M r L d0 ρ n

/-- **`omega_fsD_hole_Q` with the descent asked only on terms whose diagonal points are diagonal points of `Y`**
(the index-0 condition of `hok_of_seedC2` is then read off `Y`). -/
theorem omega_fsD_hole_QW {a' μ br vr Y ζ : T} (hY : isOT Y = true) (hH : HoleT μ br vr Y)
    (hD : DiagAt a' br μ Y) (hcb : cof br = .big μ) (hζz : ζ ≠ z)
    (hok : ∀ t, isOT t = true → HoleT μ br vr t → (∀ a'', DiagAt a'' br μ t → DiagAt a'' br μ Y) →
      isOT (fsD t ζ) = true ∧ fsD t ζ < t)
    (hLY : ∀ s b, Y = psi s b z → b ≠ z → (split b (psi (succ s) z z)).2 = z →
      (split (fsD b ζ) (psi (succ s) z z)).2 = z) :
    fsD (omega Y) ζ = omega (fsD Y ζ) := by
  have hYz := holeT_ne_z hH
  have hYs := holeT_not_succ hH
  obtain ⟨hYot', hYlt⟩ := hok Y hY hH (fun _ h => h)
  by_cases hE : Y < E0
  · rw [omega_small hE, fsD_psi hYz hYs, omega_small (lt_trans hYlt hE)]
  cases Y with
  | z => exact absurd rfl hYz
  | psi s b c =>
    by_cases hc : c = z
    · subst hc
      have hθ : psi (succ s) z z = psi (succ s) z z := rfl
      by_cases hlo : loOf s b = z
      · rw [omega_fix_nolo hY hE hlo]
        symm
        by_cases hb : b = z
        · subst hb
          have hsz : s ≠ z := by
            intro he; subst he; rw [show isSucc (psi z z z) = true from rfl] at hYs; cases hYs
          by_cases hs : isSucc s = true
          · exact absurd (DiagAt.not_omega_succ hD) (by rw [hs]; simp)
          · have hns : isSucc s = false := by simpa using hs
            have hHs := holeT_sub_inv hns hH
            rw [fsD_sub hsz hns] at hYot' ⊢
            apply omega_fix_nolo hYot'
            · intro hE'; exact fsD_ne_z_of_holeT hζz hHs (below_E0 hE').1
            · rfl
        · have hHb := holeT_arg hb hH hcb
          have hbs := not_succ_arg_of_holeT hb hH
          rw [fsD_psi hb hbs] at hYot' ⊢
          have hlo' := hLY s b rfl hb hlo
          apply omega_fix_nolo hYot'
          · intro hE'
            obtain ⟨hsz, hlt⟩ := below_E0 hE'
            subst hsz
            exact not_lt_of_lo_z (fsD_ne_z_of_holeT hζz hHb) hlo' hlt
          · exact hlo'
      · -- the low part survives
        have hb : b ≠ z := by intro he; subst he; exact hlo rfl
        have hHb := holeT_arg hb hH hcb
        have hbs := not_succ_arg_of_holeT hb hH
        have hfx : fsD (psi s b z) ζ = psi s (fsD b ζ) z := fsD_psi hb hbs ζ
        have e := split_app (psi (succ s) z z) b
        set hi := (split b (psi (succ s) z z)).1 with hhi
        set lo := (split b (psi (succ s) z z)).2 with hlodef
        have hlo0 : lo ≠ z := hlo
        have hbot : isOT b = true := isOT_arg hY
        have hloot : isOT lo = true := isOT_app_right (by rw [e]; exact hbot)
        have hHlo : HoleT μ br vr lo := holeT_app_inv hlo0 (by rw [e]; exact hHb)
        have hfb : fsD b ζ = app hi (fsD lo ζ) := by
          conv => lhs; rw [← e]
          exact fsD_app hi hlo0 ζ
        have hflt : head (fsD lo ζ) < psi (succ s) z z := by
          have h1 := (hok lo hloot hHlo (fun a'' h => DiagAt.arg hb hbs (by
            have h' := DiagAt.append hi hlo0 h
            rw [e] at h'; exact h'))).2
          have h2 : head lo < psi (succ s) z z := split_snd_head_lt hlo0
          have h3 : lo < psi (succ s) z z := by
            cases hlc : lo with
            | z => exact absurd hlc hlo0
            | psi a' b' c' =>
              rw [hlc] at h2
              exact lt_of_head_lt h2
          exact lt_of_le_of_lt (head_le_self _) (lt_trans h1 h3)
        have hsplit : split (fsD b ζ) (psi (succ s) z z) = (hi, fsD lo ζ) := by
          rw [hfb]; exact split_app_of (split_fst_ge _ b) (Or.inr hflt)
        apply omega_fsD_lo hY hE hlo hfx (by rw [← hfx]; exact hYot')
        · intro hE'
          obtain ⟨hsz, hlt⟩ := below_E0 hE'
          subst hsz
          apply hE
          -- `Y ≥ E0` forces a summand of `b` at least `Ω_1`, which `fsD b ζ` keeps
          exfalso
          have hhiz : hi ≠ z := by
            intro hz
            rw [hz] at e
            simp only [app] at e
            have h3 : b < psi (succ z) z z := by
              rw [← e]
              cases hlc : lo with
              | z => exact absurd hlc hlo0
              | psi a' b' c' =>
                have h2 : head lo < psi (succ z) z z := split_snd_head_lt hlo0
                rw [hlc] at h2
                exact lt_of_head_lt h2
            apply hE
            unfold E0; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h3⟩
          have hhi1 : ¬ hi < psi (succ z) z z := not_lt_of_lo_z hhiz (by
            rw [hhi]
            have := split_app_of (t := psi (succ z) z z) (B := hi) (X := z) (split_fst_ge _ b)
              (Or.inl rfl)
            rw [app_z_right] at this
            rw [this])
          apply hhi1
          exact lt_of_le_of_lt (le_app_self hi _) (by rw [← hfb]; exact hlt)
        · unfold hiOf; rw [hsplit]
        · unfold loOf; rw [hsplit]; exact fsD_ne_z_of_holeT hζz hHlo
        · exact hYs
    · have hHc := holeT_rest hc hH
      have hfx : fsD (psi s b c) ζ = psi s b (fsD c ζ) := by
        cases c with
        | z => exact absurd rfl hc
        | psi => rfl
      rw [hfx] at hYot'
      exact omega_fsD_rest hY hE hc (holeT_not_succ hHc) hYot' (fsD_ne_z_of_holeT hζz hHc)
        (DiagAt.fsD_not_succ hζz (DiagAt.rest_inv hc hD))


section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

/-- **All `n ≥ 2`** (`t = 1`, `q = r`), given the local equations with per-column indices. -/
theorem qr_chainW (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
          (k = 0 → ∀ bb, DepX M (r + L) bb i → i < r + L → DiagAt μ br μ (valB ρ bb i))))
    (hHD : HoleDataW M (r + L) ρ μ br μ seed)
    -- the base `M[1] = M.take x`
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    (hr1 : ρ1.o r = seed)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (TRIO.gexp M r L d0 0 1) ρ1) (hPs : ExpStepT1W Pn M r L d0 ρ) :
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
      ⟨μ, br, μ, seed, n - 2, hHD, hZg, hPr, rfl, rfl, hro⟩, ?_, ?_, ?_⟩
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
theorem qr_mainW (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
    (hHD : HoleDataW M (r + L) ρ μ br μ seed)
    (hdiag0 : ∀ bb i, DepX M (r + L) bb i → i < r + L → dOf M (r + L) lo lb i = 0 →
      DiagAt μ br μ (valB ρ bb i))
    -- the base `M[1] = M.take x`
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    (hr1 : ρ1.o r = seed)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (TRIO.gexp M r L d0 0 1) ρ1) (hPs : ExpStepT1W Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧ ρN.o r = gamS μ br seed (n - 1) ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have hdx : dOf M (r + L) lo lb (r + L) = 0 := dOf_x hx hxv hOS hVS
  refine qr_chainW hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hC hG hRM hOS hbr hcb hgam hro hrD hRA
    hR0 hRlast hRd hsM hpM ?_ hHD hC1 hR1 hG1 hr1 hPv1 Pn hP1 hPs
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
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ b : T} (hx : x + 1 = M.length)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
  (hq : par M 0 x = some r) (hro : ρ.o r = psi μ (app b (psi (succ μ) z z)) z)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
  (hBk : ∀ i j k, i < x → DepX M x false i → j ∈ children M i → col M j = bump M i →
    k ∈ children M j → DepX M x true k → k < x)
  (hxv : ¬ DepX M x false x)
include hx hC hG hKD hTD hq hro hOS hVS hBk hxv

/-- **At lift count `dOf = 0`, `μ` is a diagonal point of the `D` value** (`qr_diag0` read through `dOf`). -/
theorem qr_diag_col {bb : Bool} {i : Nat} (hd : DepX M x bb i) (hi : i < x)
    (h0 : dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) i = 0) :
    DiagAt μ (app b (psi (succ μ) z z)) μ (valB ρ bb i) := by
  obtain ⟨d, hD⟩ := depL_of_depX (lo := loQ M ρ μ b) (lb := lbQ M ρ μ b) hd
  have hdd : dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) i = d := by
    cases bb
    · exact dOf_v hx hxv hOS hVS (by omega) hD
    · exact dOf_o hx hxv hOS hVS (by omega) hD
  rw [hdd] at h0
  exact qr_diag0 hx hC hG hKD hTD hq hro hOS hVS hBk hD hi h0

/-- **At lift count `dOf = 0`, `μ` is the only diagonal point of the `D` value.** -/
theorem qr_only_mu_col {bb : Bool} {i : Nat} (hd : DepX M x bb i) (hi : i < x)
    (h0 : dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) i = 0) :
    ∀ a', DiagAt a' (app b (psi (succ μ) z z)) μ (valB ρ bb i) → a' = μ :=
  diag_only_mu (qr_diag_col hx hC hG hKD hTD hq hro hOS hVS hBk hxv hd hi h0)

end

end Ytosk
