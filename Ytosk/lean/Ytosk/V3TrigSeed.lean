/-
**t = 1・q = r の、子の持ち上げ回数が 0 のときだけ要る始点の条件。**
V3Inv2 と展開のエンジンの両方から使うため、低い層に置く。
-/
import Ytosk.V3QRKeep

namespace Ytosk

open T

/-- The trigger is needed at the seed only when the child's lift count is zero.
`qr_oloc` uses chain index `m + dOf c`; a positive lift count is handled by TP1C.
The unrestricted `TrigS` is false on T2Ext. -/
def TrigS0 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z →
    (drop1 M (M.length - 1) rk).o r < psi μ one z →
    ∀ i L' c R, i < M.length - 1 → DepX M (M.length - 1) true i → children M i = L' ++ c :: R →
    Counted M i c → DepX M (M.length - 1) true c →
    dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
    ∀ s, ρ.o c = psi s (app b (psi (succ μ) z z)) z →
    lt (preState M ρ i L') (app b (psi (succ μ) z z)) = true →
    lt (psi (ρ.v i) z z) (psi s (app b (psi (succ μ) z z)) z) = true →
    lt (preState M ρ i L') (app b ((drop1 M (M.length - 1) rk).o r)) = true

/-- The actual trigger bound consumed by `qr_oloc`, at `m + dOf c`.
This proves that restricting the seed field to lift count zero is sufficient. -/
theorem hYB_of_trigS0 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (h : TrigS0 M ρ rk) (hTP : TP1C M ρ) {r : Nat} {μ b : T}
    (h1 : par M 1 (M.length - 1) = some r)
    (h0 : par M 0 (M.length - 1) = some r)
    (h2 : entry M 2 (M.length - 1) = 0)
    (hro : ρ.o r = psi μ (app b (psi (succ μ) z z)) z)
    (hseedz : (drop1 M (M.length - 1) rk).o r ≠ z) :
    ∀ i L' c R, i < M.length - 1 → DepX M (M.length - 1) true i →
      children M i = L' ++ c :: R → Counted M i c → DepX M (M.length - 1) true c →
      ∀ s, ρ.o c = psi s (app b (psi (succ μ) z z)) z →
      lt (preState M ρ i L') (app b (psi (succ μ) z z)) = true →
      lt (psi (ρ.v i) z z) (psi s (app b (psi (succ μ) z z)) z) = true →
      ∀ m, lt (preState M ρ i L')
        (app b (gamS μ (app b (psi (succ μ) z z)) ((drop1 M (M.length - 1) rk).o r)
          (m + dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c))) = true := by
  intro i L' c R hi hd hch hcnt hdc s hcv ht1 ht2 m
  have hTPb := hTP i L' c R hch hcnt s _ hcv ht1 ht2 (ohole_of_cof_big cof_br)
  rw [holeLev_cof cof_br, fsD_eq_fs cof_br, fs_br] at hTPb
  set seed := (drop1 M (M.length - 1) rk).o r
  set d := dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c
  by_cases hbound : psi μ one z ≤ gamS μ (app b (psi (succ μ) z z)) seed (m + d)
  · show preState M ρ i L' < app b (gamS μ (app b (psi (succ μ) z z)) seed (m + d))
    apply lt_of_lt_of_le (show preState M ρ i L' < app b (psi μ one z) from hTPb)
    rcases (le_iff _ _).mp hbound with hlt | he
    · exact le_of_lt (app_lt_app_left b hlt)
    · rw [he]
  · have hzero : m + d = 0 := by
      by_contra hn
      obtain ⟨k, hk⟩ : ∃ k, m + d = k + 1 := ⟨m + d - 1, by omega⟩
      rw [hk] at hbound
      exact hbound (gamS_ge_psi1 hseedz k)
    have hd0 : d = 0 := by omega
    rw [hzero]
    have hslt : seed < psi μ one z := by
      rcases lt_trichotomy' seed (psi μ one z) with hlt | he | hgt
      · exact hlt
      · exact (hbound (by rw [hzero]; change psi μ one z ≤ seed; rw [he])).elim
      · exact (hbound (by rw [hzero]; exact le_of_lt hgt)).elim
    exact h r μ b h1 h0 h2 hro hslt i L' c R hi hd hch hcnt hdc hd0 s hcv ht1 ht2

end Ytosk
