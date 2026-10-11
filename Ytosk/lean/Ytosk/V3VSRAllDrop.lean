/-
**VSmallRAll は 1 列落としで保たれる（2026-10-12、drop-fix）。**

`M.take x` の枠 (k, c)（c は k の数える子、新しい c が書き換え）は M の枠と同じ: v(k) と前の子の o は変わらず
（`frame_take`）、古い c も書き換え（`rewrite_take`）、添字は同じで引数は下がる（`new_rewrite_same_v`・PO）。
引数の高い部分が 0 でないことは引数が上がると保たれる（`split_mono`）。段の道 `PathLvAll` も枠ごとに M の道へ写る。
-/
import Ytosk.V3VSRAll
import Ytosk.V3DropPres

namespace Ytosk

open T

/-- A nonzero high part survives a larger argument. -/
theorem split_hi_ne_z_of_le {θ y' y : T} (hyy : y' ≤ y) (h : (split y' θ).1 ≠ z) : (split y θ).1 ≠ z := by
  rcases (le_iff _ _).mp hyy with hlt | rfl
  · rcases split_mono θ hlt with h1 | ⟨h1, _⟩
    · intro h0; rw [h0] at h1; exact T.not_lt_z _ h1
    · rw [← h1]; exact h
  · exact h

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop

/-- **A rewriting frame of `M.take x` is a rewriting frame of `M`** with the same parent value, the same
earlier children, the same subscript and a larger argument. -/
theorem frame_take_rw {k c : Nat} {Lc R : List Nat} {s' y' : T} (hcl : CL (M.take x) k = Lc ++ c :: R)
    (hc' : ρ'.o c = psi s' y' z)
    (ht' : lt (spArg (ρ'.v k) z (sumN (Lc.map ρ'.o))) y' = true ∧ lt (psi (ρ'.v k) z z) (psi s' y' z) = true) :
    ρ'.v k = ρ.v k ∧ Lc.map ρ'.o = Lc.map ρ.o ∧ (∃ Tl, CL M k = Lc ++ c :: (R ++ Tl)) ∧
      ∃ y, ρ.o c = psi s' y z ∧ y' ≤ y ∧
        (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v k) z z) (psi s' y z) = true) := by
  have hcT : c ∈ CL (M.take x) k := by rw [hcl]; simp
  have hcc := cl_mem_children hcT
  have hcx : c < x := by have := (mem_children hcc).2; rw [lenT hx] at this; exact this
  have hkc : k < c := (mem_children hcc).1
  have hk : k < x := by omega
  have hkM : k < M.length := by omega
  obtain ⟨hv, hL, Tl, hM⟩ := frame_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hk hcl
  rw [hv, hL] at ht'
  obtain ⟨hsM, _⟩ := cl_vals hC hG hkM
  rw [hM] at hsM
  obtain ⟨s, y, hsy⟩ := (hsM (ρ.o c) (by simp)).2
  have ht := rewrite_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hk hcl hc' ht' hsy
  have hvs := new_rewrite_same_v hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hcx hc'
    (ne_z_of_lt ht'.1)
  obtain ⟨y0, hy0⟩ := o_psi_sub hC' (show c < (M.take x).length by rw [lenT hx]; exact hcx)
  rw [hc'] at hy0; simp only [psi.injEq] at hy0
  obtain ⟨y1, hy1⟩ := o_psi_sub hC (show c < M.length by omega)
  rw [hsy] at hy1; simp only [psi.injEq] at hy1
  have hss : s' = s := by rw [hy0.1, hy1.1, hvs]
  subst hss
  have hle : psi s' y' z ≤ psi s' y z := by
    rw [← hc', ← hsy]
    exact DRelOA.le ((hdrop c hcx).1.1.elim (fun h => Or.inl h) (fun h => Or.inr h.1))
  have hyy : y' ≤ y := by
    rcases (le_iff _ _).mp hle with h | h
    · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact le_of_lt h
    · simp only [psi.injEq] at h; rw [h.2.1]
  exact ⟨hv, hL, ⟨Tl, hM⟩, y, hsy, hyy, ht⟩

/-- **The levels of `M.take x` are levels of `M`.** -/
theorem pathLvAll_take {i : Nat} {u : T} (h : PathLvAll (M.take x) ρ' i u) : PathLvAll M ρ i u := by
  induction h with
  | top hcl hc' ht' =>
    obtain ⟨hv, -, ⟨Tl, hM⟩, y, hsy, -, ht⟩ :=
      frame_take_rw hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hcl hc' ht'
    rw [hv]; exact PathLvAll.top hM hsy ht
  | step hcl hc' ht' _ ih =>
    obtain ⟨-, -, ⟨Tl, hM⟩, y, hsy, -, ht⟩ :=
      frame_take_rw hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hcl hc' ht'
    exact PathLvAll.step hM hsy ht ih

/-- **`VSmallRAll` passes to `M.take x`** (no residual: the frames of `M.take x` are frames of `M`). -/
theorem vsmallRAll_take (hVA : VSmallRAll M ρ) : VSmallRAll (M.take x) ρ' := by
  intro k c Lc R s' y' hcl hc' ht' hhz u hu hku g hg
  obtain ⟨hv, hL, ⟨Tl, hM⟩, y, hsy, hyy, ht⟩ :=
    frame_take_rw hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hcl hc' ht'
  rw [hv] at hku; rw [hv, hL]
  have hu' : u = ρ.v k ∨ PathLvAll M ρ k u := by
    rcases hu with hu | hu
    · exact Or.inl (hv ▸ hu)
    · exact Or.inr (pathLvAll_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hu)
  exact hVA k c Lc (R ++ Tl) s' y hM hsy ht (split_hi_ne_z_of_le hyy hhz) u hu' hku g hg

end

end Ytosk
