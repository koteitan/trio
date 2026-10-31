/-
**WfDrL3: the index-0 obligation of `hok_of_seedC2` (2026-10-31).**

`hok_of_seedC2` (WfDrE2) needs, at index `k = 0`, that every diagonal point of the column's term is `μ`.
`DiagAt a b μ t` follows a fixed path in `t` (the last summand, then the argument when it is not `0` / a successor,
else the subscript) and stops at the first node `ψ_a(b)`. When `b` has no diagonal point itself (`not_diag_br` for
`b_r = b + Ω_{μ+1}`), the point is unique (`DiagAt.unique`). `qr_diag0` (V3QRDiag) gives `DiagAt μ b_r μ t` for every
column with lift count `0`; so every diagonal point there is `μ` (`qr_diag_only_mu`), and `hok_of_seedC2` holds at
every index `m + d` of a column with lift count `d` (`hok_col_of_seedC2`).
Measured first (tmp/wf/WfDrL/probe_dp0.py): at `d = 0` no diagonal point other than `μ`; at `d > 0` the root's `0`
and others do occur.
-/
import Ytosk.WfDrE2
import Ytosk.V3QRDiag

namespace Ytosk

open T

/-- **The diagonal point is unique** when `b` has none. -/
theorem DiagAt.unique {a a' b μ : T} (hnb : ∀ a'', ¬ DiagAt a'' b μ b) :
    ∀ {t : T}, DiagAt a b μ t → DiagAt a' b μ t → a = a' := by
  intro t h1 h2
  induction h1 with
  | here hb _ _ =>
    cases h2 with
    | here _ _ _ => rfl
    | arg _ _ hD => exact absurd hD (hnb _)
    | sub _ _ _ => exact absurd rfl hb
  | rest _ ih =>
    cases h2 with
    | rest hD => exact ih hD
  | arg hb' _ hD ih =>
    cases h2 with
    | here _ _ _ => exact absurd hD (hnb _)
    | arg _ _ hD' => exact ih hD'
    | sub _ _ _ => exact absurd rfl hb'
  | sub ha _ _ ih =>
    cases h2 with
    | here hb _ _ => exact absurd rfl hb
    | arg hb _ _ => exact absurd rfl hb
    | sub _ _ hD' => exact ih hD'

/-- With `b_r = b + Ω_{μ+1}` the diagonal point is unique. -/
theorem DiagAt.unique_br {a a' μ b t : T} (h1 : DiagAt a (app b (psi (succ μ) z z)) μ t)
    (h2 : DiagAt a' (app b (psi (succ μ) z z)) μ t) : a = a' :=
  DiagAt.unique (fun _ h => not_diag_br h) h1 h2

/-- If `μ` is a diagonal point of `t` (for `b_r`), it is the only one. -/
theorem diag_only_mu {μ b t : T} (h : DiagAt μ (app b (psi (succ μ) z z)) μ t) :
    ∀ a', DiagAt a' (app b (psi (succ μ) z z)) μ t → a' = μ :=
  fun _ h' => (DiagAt.unique_br h h').symm

/-- **`hok_of_seedC2` with the index-0 condition as "`μ` is a diagonal point"** (the form the `q = r` chain can supply:
`qr_diag0` and the inversions `DiagAt.rest_inv` / `arg_inv` / `last'` along the path). -/
theorem hok_of_seedC2_diag {μ b seed t : T}
    (hrot : isOT (psi μ (app b (psi (succ μ) z z)) z) = true)
    (hSr : SeedOK μ (app b (psi (succ μ) z z)) μ seed)
    (hl : Lhd z (psi μ (app b seed) z) (psi μ (app b (psi (succ μ) z z)) z))
    (hot : isOT t = true) (hH : HoleT μ (app b (psi (succ μ) z z)) μ t) (k : Nat)
    (h0 : k = 0 → DiagAt μ (app b (psi (succ μ) z z)) μ t) :
    isOT (fsD t (gamS μ (app b (psi (succ μ) z z)) seed k)) = true ∧
      fsD t (gamS μ (app b (psi (succ μ) z z)) seed k) < t :=
  hok_of_seedC2 hrot hSr hl hot hH k (fun hk => diag_only_mu (h0 hk))

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ b : T} (hx : x + 1 = M.length)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
  (hq : par M 0 x = some r) (hro : ρ.o r = psi μ (app b (psi (succ μ) z z)) z)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
  (hBk : ∀ i j k, i < x → DepX M x false i → j ∈ children M i → col M j = bump M i →
    k ∈ children M j → DepX M x true k → k < x)
include hx hC hG hKD hTD hq hro hOS hVS hBk

/-- **The index-0 obligation**: a column with lift count `0` has only `μ` as a diagonal point. -/
theorem qr_diag_only_mu {bb : Bool} {i : Nat} (hD : DepL M x (loQ M ρ μ b) (lbQ M ρ μ b) bb i 0)
    (hi : i < x) : ∀ a', DiagAt a' (app b (psi (succ μ) z z)) μ (valB ρ bb i) → a' = μ :=
  diag_only_mu (qr_diag0 hx hC hG hKD hTD hq hro hOS hVS hBk hD hi rfl)

/-- **`hok_of_seedC2` at a column**: with lift count `d`, every index `m + d` works (the weak branch of `SeedC2`). -/
theorem hok_col_of_seedC2 {bb : Bool} {i d : Nat} (hD : DepL M x (loQ M ρ μ b) (lbQ M ρ μ b) bb i d)
    (hi : i < x) {seed : T}
    (hrot : isOT (psi μ (app b (psi (succ μ) z z)) z) = true)
    (hSr : SeedOK μ (app b (psi (succ μ) z z)) μ seed)
    (hl : Lhd z (psi μ (app b seed) z) (psi μ (app b (psi (succ μ) z z)) z))
    (hot : isOT (valB ρ bb i) = true) (hH : HoleT μ (app b (psi (succ μ) z z)) μ (valB ρ bb i)) (m : Nat) :
    isOT (fsD (valB ρ bb i) (gamS μ (app b (psi (succ μ) z z)) seed (m + d))) = true ∧
      fsD (valB ρ bb i) (gamS μ (app b (psi (succ μ) z z)) seed (m + d)) < valB ρ bb i := by
  apply hok_of_seedC2 hrot hSr hl hot hH (m + d)
  intro h0
  have hd0 : d = 0 := by omega
  subst hd0
  exact qr_diag_only_mu hx hC hG hKD hTD hq hro hOS hVS hBk hD hi

end

end Ytosk
