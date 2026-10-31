/-
**WfT2R9: `NotBumpKidX` is structural (2026-11-01, t = 2 Bad2 route).**

`notBumpKidX_of`: if `m = P₀ i` were a bump child of `p = P₀ m`, then `e₁ p = e₁ m < e₁ i` (`P₁ i = m` from
`BadAbsShape`), so `BumpLeaf` (a field of `LocInv`, true on every standard matrix) gives `e₂ i = 0`, against
`e₂ i ≠ 0` in `BdX`. So `NotBumpKidX` holds on every standard `M` with no value condition.
`T2BelowRV2Y`: `T2BelowRV2X` without the field `NotBumpKidX`; `T2BelowRV2Y.toX`.
`trio_terminates_main_V2_curYR`: the top theorem of WfT2R8 with `T2BelowRV2Y`.
-/
import Ytosk.WfT2R8
import Ytosk.V3Spine

namespace Ytosk.WfT2X

open T Ytosk.WfAbsW

/-- **`NotBumpKidX` from `BumpLeaf`.** -/
theorem notBumpKidX_of {M N : Mat} {bnd : Nat} {ρ σ : Valn} (hBL : BumpLeaf M) :
    NotBumpKidX M N bnd ρ σ := by
  intro i m p hb hm hp hbump
  obtain ⟨_, h1, h2, _, hsh⟩ := hb
  obtain ⟨m', Lc, hp0, hp1, _⟩ := hsh
  rw [hm] at hp0
  cases hp0
  have hlt : entry M 1 m < entry M 1 i := (par1_facts hp1).2.2.1
  have he1 := e1_of_col (show col M m = (entry M 0 p + 1, entry M 1 p, 1) from hbump)
  have hiM : i < M.length := by
    by_contra h
    exact h1 (entry_out (by omega) 1)
  have hmM : m < M.length := by have := par_lt M 0 i m hm; omega
  have hjk : m ∈ children M p := mem_children_iff.mpr ⟨hmM, hp⟩
  have hci : i ∈ children M m := mem_children_iff.mpr ⟨hiM, hm⟩
  exact h2 (hBL p m i hjk hbump hci (by omega)).1

/-- **`T2BelowRV2X` without `NotBumpKidX`.** -/
def T2BelowRV2Y : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      (∀ b j, r + L ≤ j → j < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n).length → isOT (valB σ b j) = true) →
      isOT (σ.o r) = true → (∀ q, par M 0 (r + L) = some q → q ≠ r → isOT (σ.o q) = true) →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
      (∀ p, T2Seed M r L p → T2SeedRR M ρ σ p) ∧
      AbsWNx M (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) (r + L) ρ σ

theorem T2BelowRV2Y.toX (h : T2BelowRV2Y) : T2BelowRV2X := by
  intro M ρ rk C hz h2 r L hlen hr n hn hG σ hCN hOTx hor hoq hdec
  obtain ⟨h1, h3⟩ := h M ρ rk C hz h2 r L hlen hr n hn hG σ hCN hOTx hor hoq hdec
  exact ⟨h1, h3, notBumpKidX_of (sInvXJ_std C.std C.ne).1.loc.2.2.2⟩

end Ytosk.WfT2X

namespace Ytosk

/-- **The top theorem with `T2BelowRV2Y`** (no `NotBumpKidX`). -/
theorem trio_terminates_main_V2_curYR (hDU : HDropU) (hQD : T2QNDomBad2) (hRY : WfT2X.T2BelowRV2Y)
    (hStep : WfB2S.B2StepAb) (hSib : WfH7W.H7WSib)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hBE : HBumpExt) (hCB : T2CBadOut)
    (hVU : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → FDCopyRoot.T2VAncUse M)
    (hClR : WfScout.T2SeedClV2R) (hPRE : T2SeedPResRCV2E) (hCan : HCanonV2)
    (hDomQ : T2SeedDomV2Q)
    (hVCp : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRACopyEsc M)
    (hAG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAK KAG M) : WellFounded Step' :=
  trio_terminates_main_V2_curXR hDU hQD hRY.toX hStep hSib hF hLf hBE hCB hVU hClR hPRE hCan hDomQ hVCp hAG

end Ytosk

#print axioms Ytosk.trio_terminates_main_V2_curYR
