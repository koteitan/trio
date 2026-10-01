/-
**3 行・t = 1・q ≠ r: M[n]（n ≥ 2）の値の降下。**

N = M[n]、P = M[n − 1] の評価（ρP, rkP）があり、D の局所条件が鎖の項 ζ = gamS μ b_r seed m で成り立てば、
N にも評価があり、値は標準形で M の値より小さい（`val_N_t1`）。
等式は `cons_N_t1`、順位は `rk_N_t1`、経路は `t1_path`、根は `root_N_t1`。
-/
import Ytosk.V3PathT
import Ytosk.V3T1
import Ytosk.V3Root

namespace Ytosk

open T

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **The value of `M[n]` drops** (`t = 1`, `q ≠ r`, `n ≥ 2`). -/
theorem val_N_t1 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    (hnd : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    {ρ ρP : Valn} {rkM rkP : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP) (hRP : Rk (TRIO.gexp M r L d0 0 (n - 1)) rkP)
    (hPv : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ρ.v g = ρP.v g)
    {μ br vr seed : T} {m : Nat}
    (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed)
    (hHx : HoleT μ br vr (ρ.o (r + L)))
    (hPr : ρP.o r = fsD (ρ.o (r + L)) (gamS μ br seed m))
    (hO : ∀ i, i < r + L → DepX M (r + L) true i → OLocal M (r + L) ρ (gamS μ br seed m) μ vr br i)
    (hV : ∀ i, i < r + L → DepX M (r + L) false i → VLocal M (r + L) ρ (gamS μ br seed m) μ i)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hsR : Single (fsD (ρ.o Rt) (gamS μ br seed m))) :
    ∃ t', Val (TRIO.gexp M r L d0 0 n) t' ∧ isOT t' = true ∧ t' < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  set ζ := gamS μ br seed m with hζ
  set ρN := shiftV ρP L with hρN
  have hxN : ρN.o (r + L) = fsD (ρ.o (r + L)) ζ := by
    show ρP.o (r + L - L) = _
    rw [show r + L - L = r by omega]; exact hPr
  have hpt := t1_path (ρN := ρN) hC hG hx hrot hcb hμr hbr hS hHx hxN hO hV
  -- the equations
  have hF : ∀ i, i < r + L →
      (DepX M (r + L) true i →
        oRhs M (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => ζ)) i = fsD (ρ.o i) ζ) ∧
      (DepX M (r + L) false i →
        vRhs M (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => ζ)) i = fsD (ρ.v i) ζ) := by
    intro i hi
    exact ⟨fun hd => (hpt true i hd (Or.inl hi)).2 hi, fun hd => (hpt false i hd (Or.inl hi)).2 hi⟩
  have hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => ζ)).v g = ρP.v g := by
    intro g hg a ha hr
    rw [glueZ_v_lt ρ _ _ (by omega) (hnd g hg a ha hr)]
    exact hPv g hg a ha hr
  have hCN := cons_N_t1 hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hC hCP hagree hF
  have hRN := rk_N_t1 hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hnd hRM hRP
  -- the root
  have hRx : Rt < r + L := by
    rcases Nat.eq_or_lt_of_le hRA.le with h | h
    · exfalso
      have h1 : entry M 0 (r + L) ≠ 0 := by
        have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
      have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hR0; rw [hR0]; rfl
      rw [h] at hR0e; exact h1 hR0e
    · exact h
  have hRt := hpt true Rt hRd (Or.inl hRx)
  have hRot : isOT (ρ.o Rt) = true := hG.ot_o Rt (by omega)
  have hlt := (hok_of_holeT hrot hcb (by rw [hμr]; exact lt_irrefl' _) hS hRot hRt.1 m).2
  obtain ⟨hot, hroot⟩ := root_N_t1 hlen hL hA hd0e hn (ρN := shiftV ρP L) (Z := fun _ => ζ)
    hRA hR0 hRlast hRd hsM hpM hsR hlt
  exact ⟨_, ⟨_, _, hCN, hRN, rfl⟩, hot, hroot⟩

end

end Ytosk
