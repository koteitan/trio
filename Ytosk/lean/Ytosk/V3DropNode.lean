/-
**落とす補題: 枠 1 段の合成。**

子の値どうしの ◁ と枠の場合から、親の引数どうし・値どうしの ◁:
- `ArgRoute`（書き換えなし同士 / 書き換えあり同士で変化が低い部分 / M だけ書き換えで低い部分あり）なら
  親の引数どうしの ◁（`node_arg`）と値どうしの ◁。
- それ以外は「引数の成分が引数以下」の道で値どうしの ◁ だけ（`lhdE_psi_small`）。
-/
import Ytosk.V3DropFrame

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

/-- **One `o` frame of the drop at the evaluator level**, through `node_val`. -/
theorem drop_oframe_val {M M' : Mat} {ρ ρ' : Valn} {i : Nat}
    (hC : Cons M ρ) (hC' : Cons M' ρ') (hi : i < M.length) (hi' : i < M'.length)
    (hvot : isOT (ρ.v i) = true) (hv : ρ'.v i = ρ.v i)
    (hs : ∀ t ∈ (children M i).map (cnt M ρ i), t = z ∨ Single t)
    (hdec : (cvals M ρ i).Pairwise (fun a b => b ≤ a))
    (hs' : ∀ t ∈ (children M' i).map (cnt M' ρ' i), t = z ∨ Single t)
    (hdec' : (cvals M' ρ' i).Pairwise (fun a b => b ≤ a))
    {L R : List Nat} {c : Nat} (hch : children M i = L ++ c :: R) (hch' : children M' i = L ++ c :: R)
    (hcb : col M c ≠ bump M i) (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
    (hcb' : col M' c ≠ bump M' i) (hcu' : ¬ (isUpg M' c = true ∧ topped M' c = true))
    (hR : ∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hR' : ∀ d ∈ R, col M' d = bump M' i ∨ (isUpg M' d = true ∧ topped M' d = true))
    (hL : ∀ d ∈ L, cnt M' ρ' i d = cnt M ρ i d)
    {s y s' y' : T} (hc : ρ.o c = psi s y z) (hc' : ρ'.o c = psi s' y' z)
    (hcS : Single (ρ.o c)) (hcS' : Single (ρ'.o c))
    (hrel : LhdE (ρ'.o c) (ρ.o c)) (hB : ∀ q ∈ summands (preState M ρ i L), psi s y z ≤ q)
    (hroute : ArgRoute (ρ.v i) (preState M ρ i L) s' y' s y ∨
      (step (ρ.v i) (preState M ρ i L) s' y' z ≤ step (ρ.v i) (preState M ρ i L) s y z ∧
        ∀ u, ¬ lt (ρ.v i) u = true → ∀ g ∈ comps u (step (ρ.v i) (preState M ρ i L) s' y' z),
          g ≤ step (ρ.v i) (preState M ρ i L) s' y' z)) :
    LhdE (ρ'.o i) (ρ.o i) := by
  have hpre : preState M' ρ' i L = preState M ρ i L := by
    unfold preState
    rw [hv]
    congr 3
    exact List.map_congr_left hL
  have hvot' : isOT (ρ'.v i) = true := by rw [hv]; exact hvot
  rw [o_frame_loc hC' hi' hvot' hs' hdec' hch' hcb' hcu' hR' hcS',
    o_frame_loc hC hi hvot hs hdec hch hcb hcu hR hcS, hpre, hv, hc, hc', spArg_single, spArg_single]
  rw [hc, hc'] at hrel
  exact node_val (by rw [← hc']; exact hcS'.1) (by rw [← hc]; exact hcS.1) hrel hB hroute

/-- **The step result is standard.** -/
theorem isOT_step {a B s y : T} (hBot : isOT B = true) (hc : isOT (psi s y z) = true) :
    isOT (step a B s y z) = true := by
  unfold step
  split
  · rw [H_eq hc]
    have hyot := isOT_arg hc
    have e := split_app (psi (succ s) z z) y
    have hhiot : isOT (split y (psi (succ s) z z)).1 = true := by
      rw [← e] at hyot; exact isOT_app_left hyot
    split
    · rw [app_z_right]; exact hhiot
    · apply isOT_app_of hhiot hc
      intro q hq
      have hq' := split_fst_ge (psi (succ s) z z) y q hq
      simp only [head]
      rcases lt_trichotomy' q (psi s y z) with h | h | h
      · exfalso; apply hq'
        exact lt_trans h (by rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self s))
      · rw [h]
      · exact le_of_lt h
  · exact isOT_add hBot hc

/-- The parent value is standard on an argument route. -/
theorem ot_parent_lhd {a X' X : T} (hot : isOT (psi a X z) = true) (hX' : isOT X' = true)
    (hl : LhdE X' X) : isOT (psi a X' z) = true := by
  rcases hl with rfl | hl
  · exact hot
  · exact psi_ot_of_lhd (isOT_sub hot) hX' hl (comps_lt hot) (fun _ g hg => by simp [comps] at hg)

/-- The parent value is standard on the small route. -/
theorem ot_parent_small {a X' : T} (ha : isOT a = true) (hX' : isOT X' = true)
    (hsm : ∀ g ∈ comps a X', g ≤ X') : isOT (psi a X' z) = true := by
  rw [isOT_psi_iff]
  refine ⟨ha, hX', rfl, z_le _, ?_⟩
  intro g hg
  rcases (le_iff _ _).mp (hsm g hg) with h | h
  · exact h
  · exfalso; have := size_comps hg; rw [h] at this; exact Nat.lt_irrefl _ this

end Ytosk
