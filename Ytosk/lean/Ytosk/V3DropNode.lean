/-
**落とす補題: 枠 1 段の合成。**

子の値どうしの ◁ と枠の場合から、親の引数どうし・値どうしの ◁:
- `ArgRoute`（書き換えなし同士 / 書き換えあり同士で変化が低い部分 / M だけ書き換えで低い部分あり）なら
  親の引数どうしの ◁（`node_arg`）と値どうしの ◁。
- それ以外は「引数の成分が引数以下」の道で値どうしの ◁ だけ（`lhdE_psi_small`）。
-/
import Ytosk.V3DropLhd

namespace Ytosk

open T

/-- The routes through one frame that relate the arguments. -/
inductive ArgRoute (a B s' y' s y : T) : Prop
  | nn : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) →
      ¬ (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → ArgRoute a B s' y' s y
  | tt (P R R' : T) : s' = s → y = app P R → y' = app P R' → R ≠ z → LhdE y' y →
      lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true →
      lt B y = true ∧ lt (psi a z z) (psi s y z) = true →
      ((split y' (psi (succ s) z z)).2 ≠ z →
        head R < psi (succ s) z z ∧ (R' = z ∨ head R' < psi (succ s) z z)) →
      ArgRoute a B s' y' s y
  | tn : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) →
      lt B y = true ∧ lt (psi a z z) (psi s y z) = true →
      (split y (psi (succ s) z z)).2 ≠ z → (split y (psi (succ s) z z)).1 ≤ B →
      ArgRoute a B s' y' s y

/-- **One frame of the drop, on an argument route.** -/
theorem node_arg {a B s' y' s y : T} (hc' : isOT (psi s' y' z) = true) (hc : isOT (psi s y z) = true)
    (hrel : LhdE (psi s' y' z) (psi s y z)) (hB : ∀ q ∈ summands B, psi s y z ≤ q)
    (hroute : ArgRoute a B s' y' s y) :
    LhdE (step a B s' y' z) (step a B s y z) := by
  cases hroute with
  | nn hn' hn => exact lhdE_step_nn' hrel hn' hn hB
  | tt P R R' hs hy hy' hRz hyy ht' ht hshape =>
    subst hs; subst hy; subst hy'
    exact lhdE_step_tt_shape hc' hc ht' ht hyy hRz hshape
  | tn hn' ht hlo hge =>
    have hlt : B < y := ht.1
    exact lhdE_step_tn hc hrel hn' ht hlo (B_eq_hi hc hlo hge hlt hB) hB

/-- **One frame of the drop, values**: either an argument route or the small route. -/
theorem node_val {a B s' y' s y : T} (hc' : isOT (psi s' y' z) = true) (hc : isOT (psi s y z) = true)
    (hrel : LhdE (psi s' y' z) (psi s y z)) (hB : ∀ q ∈ summands B, psi s y z ≤ q)
    (hroute : ArgRoute a B s' y' s y ∨
      (step a B s' y' z ≤ step a B s y z ∧
        ∀ u, ¬ lt a u = true → ∀ g ∈ comps u (step a B s' y' z), g ≤ step a B s' y' z)) :
    LhdE (psi a (step a B s' y' z) z) (psi a (step a B s y z) z) := by
  rcases hroute with h | ⟨hle, hsm⟩
  · exact lhdE_psi a (node_arg hc' hc hrel hB h)
  · exact lhdE_psi_small a hle hsm

end Ytosk
