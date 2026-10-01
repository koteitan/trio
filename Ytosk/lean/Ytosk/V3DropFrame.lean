/-
**落とす補題: o の枠（評価器の段）。**

`o_frame_loc`: Good3 の代わりに局所の仮定（その列の数える子の値が項 1 つで降順、v が標準形）で o の枠の分解。
`drop_oframe`: M と M′（= M.take x）で、列 i の子・数える子・前の寄与・v が同じで、最後の数える子 c だけ値が違うとき、
o(i) の関係は 1 段 step の関係（`LhdE`）から ψ で出る。
-/
import Ytosk.V3DropLhd

namespace Ytosk

open T

section
variable {M : Mat} {ρ : Valn} {i : Nat}

theorem cvals_single_loc (hs : ∀ t ∈ (children M i).map (cnt M ρ i), t = z ∨ Single t) :
    ∀ t ∈ cvals M ρ i, Single t := by
  intro t ht
  unfold cvals nzs at ht
  rw [List.mem_filter] at ht
  rcases hs t ht.1 with h | h
  · exact absurd h (by simpa using ht.2)
  · exact h

theorem o_spArg_loc (hC : Cons M ρ) (hi : i < M.length) (hvot : isOT (ρ.v i) = true)
    (hs : ∀ t ∈ (children M i).map (cnt M ρ i), t = z ∨ Single t)
    (hdec : (cvals M ρ i).Pairwise (fun a b => b ≤ a)) :
    ρ.o i = psi (ρ.v i) (spArg (ρ.v i) z (sumN (cvals M ρ i))) z := by
  rw [(hC i hi).1]
  unfold oRhs
  rw [sumN_skip_z hs hdec]
  have hS := (sumN_dec _ (cvals_single_loc hs) hdec).1
  exact sf_psi_spArg hvot hS

/-- **The frame decomposition with local hypotheses.** -/
theorem o_frame_loc (hC : Cons M ρ) (hi : i < M.length) (hvot : isOT (ρ.v i) = true)
    (hs : ∀ t ∈ (children M i).map (cnt M ρ i), t = z ∨ Single t)
    (hdec : (cvals M ρ i).Pairwise (fun a b => b ≤ a))
    {L R : List Nat} {c : Nat} (hch : children M i = L ++ c :: R) (hcb : col M c ≠ bump M i)
    (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
    (hR : ∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hcS : Single (ρ.o c)) :
    ρ.o i = psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (ρ.o c)) z := by
  have hsplit := cvals_split hch hcb hcu hR (single_ne_z hcS)
  have hdec' := hdec
  have hsing := cvals_single_loc hs
  rw [hsplit] at hdec' hsing
  rw [o_spArg_loc hC hi hvot hs hdec, hsplit, sumN_snoc_dec hsing hdec', spArg_app]
  rfl

end

/-- **One `o` frame of the drop.** -/
theorem drop_oframe {M M' : Mat} {ρ ρ' : Valn} {i : Nat}
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
    (hstep : LhdE (step (ρ.v i) (preState M ρ i L) s' y' z) (step (ρ.v i) (preState M ρ i L) s y z)) :
    LhdE (ρ'.o i) (ρ.o i) := by
  have hpre : preState M' ρ' i L = preState M ρ i L := by
    unfold preState
    rw [hv]
    congr 3
    exact List.map_congr_left hL
  have hvot' : isOT (ρ'.v i) = true := by rw [hv]; exact hvot
  rw [o_frame_loc hC' hi' hvot' hs' hdec' hch' hcb' hcu' hR' hcS',
    o_frame_loc hC hi hvot hs hdec hch hcb hcu hR hcS, hpre, hv, hc, hc', spArg_single, spArg_single]
  exact lhdE_psi _ hstep

end Ytosk
