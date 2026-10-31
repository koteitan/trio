/-
**WfQnH5 (2026-11-01): root decrease of the q ≠ r engine with the bad closure (assembly, step 4).**
`t1_rootB`: the path theorem off the closure (`WfQnL3.t1_pathB`, fed by `WfQnH2.vlocal_t1_atXB` and
`WfQnH3.olocal_t1B`), (E1) off the closure (`WfQnL5.E1_M`) and the root step (`WfQnL7.root_N_E3`) give the descent
of the value for any solution `σ` of `N = M[n]`.  Left open: (E3) at the root when the root lies in the closure
(`hE3`; `WfQnH4.leaf_E3` is the leaf case).
-/
import Ytosk.WfQnH4

namespace Ytosk.WfQnH5
open T Ytosk Ytosk.WfQnE3 Ytosk.WfBad

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L → entry M 1 r < entry M 1 s)
  (hx2 : entry M 2 (r + L) = 0)
  (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
  (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
  (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
  {rkM : Bool → Nat → Nat} (hRM : Rk M rkM) {B : Nat → Prop} (hB : ∀ i, B i → DepX M (r + L) false i)
  (hndN : ∀ a, a < (n - 1) * L → ∀ g, g < r + L →
      (par (TRIO.gexp M r L d0 0 n) 1 (r + L + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 n) (r + L + a) = some g) → ¬ DepX M (r + L) false g)
include hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux hRM hB hndN

/-- **(E1) off the closure from the local conditions off the closure.** -/
theorem t1_E1B (hz2 : entry M 2 r ≤ 1) {ρ ρP σ : Valn} {rkN : Bool → Nat → Nat} {μ br vr seed : T} {m : Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ)
    (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => gamS μ br seed m)).v g = ρP.v g)
    (hCN : Cons (TRIO.gexp M r L d0 0 n) σ) (hRN : Rk (TRIO.gexp M r L d0 0 n) rkN)
    (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed)
    (hHx : HoleT μ br vr (ρ.o (r + L)))
    (hxN : (shiftV ρP L).o (r + L) = fsD (ρ.o (r + L)) (gamS μ br seed m))
    (hO : ∀ i, i < r + L → DepX M (r + L) true i → ¬ DepXB M B true i →
      OLocal M (r + L) ρ (gamS μ br seed m) μ vr br i)
    (hV : ∀ i, i < r + L → DepX M (r + L) false i → ¬ DepXB M B false i →
      VLocal M (r + L) ρ (gamS μ br seed m) μ i) :
    (∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M B true i) →
      σ.o i = (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => gamS μ br seed m)).o i) ∧
    (∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M B false i) →
      σ.v i = (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => gamS μ br seed m)).v i) := by
  have hP := WfQnL3.t1_pathB (B := B) hC hG hlen hrot hcb hμr hbr hS hHx hxN hO hV
  have hF := WfQnH4.hF_of_pathB hP
  exact WfQnL5.E1_M hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux hRM hB hndN hz2 hC hCP hagree hF hCN hRN

/-- **Root decrease off the closure, with (E3) at the root.** -/
theorem t1_rootB (hz2 : entry M 2 r ≤ 1) {ρ ρP σ : Valn} {rkN : Bool → Nat → Nat} {μ br vr seed : T} {m : Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ)
    (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => gamS μ br seed m)).v g = ρP.v g)
    (hCN : Cons (TRIO.gexp M r L d0 0 n) σ) (hRN : Rk (TRIO.gexp M r L d0 0 n) rkN)
    (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed)
    (hHx : HoleT μ br vr (ρ.o (r + L)))
    (hxN : (shiftV ρP L).o (r + L) = fsD (ρ.o (r + L)) (gamS μ br seed m))
    (hO : ∀ i, i < r + L → DepX M (r + L) true i → ¬ DepXB M B true i →
      OLocal M (r + L) ρ (gamS μ br seed m) μ vr br i)
    (hV : ∀ i, i < r + L → DepX M (r + L) false i → ¬ DepXB M B false i →
      VLocal M (r + L) ρ (gamS μ br seed m) μ i)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hsR : Single (fsD (ρ.o Rt) (gamS μ br seed m))) (hlt : fsD (ρ.o Rt) (gamS μ br seed m) < ρ.o Rt)
    (hE3 : DepXB M B true Rt → Single (σ.o Rt) ∧ σ.o Rt < ρ.o Rt) :
    isOT (root (TRIO.gexp M r L d0 0 n) σ) = true ∧ root (TRIO.gexp M r L d0 0 n) σ < root M ρ := by
  have hE := t1_E1B hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux hRM hB hndN hz2 hC hG hCP hagree hCN hRN
    hrot hcb hμr hbr hS hHx hxN hO hV
  exact WfQnL7.root_N_E3 (Z := fun _ => gamS μ br seed m) hlen hL hA hd0e hn hRA hR0 hRlast hRd hsM hpM hB
    hE.1 hsR hlt hE3

end

end Ytosk.WfQnH5
