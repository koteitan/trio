/-
**3 行・t = 1・q = r: 枠の 1 段（引き上げつき）。**

- `oRhs_frame_gen`: 任意の割り当て ρ′ で、前の数える子が変わらず最後の数える子の値が c′ なら
  oRhs(ρ′, i) = ψ_{v(i)}(spArg(v(i), B, c′))。
- `o_lift`: 最後の数える子の値が A = ψ_μ(b + Ω_{μ+1}) で書き換えが起きる枠では、子が next(ζ) に変わると
  親は fsD(o(i), next(ζ))（ζ が鎖の 1 つ先へずれる、`frame_fsD_shift`）。
-/
import Ytosk.V3QRChain

namespace Ytosk

open T

/-- **The value of an `o` frame** for any valuation `ρ′` that keeps the earlier counted children. -/
theorem oRhs_frame_gen {M : Mat} {i : Nat} {ρ ρ' : Valn} {L R : List Nat} {c : Nat} {c' : T}
    (hiM : i < M.length) (hch : children M i = L ++ c :: R)
    (hcb : col M c ≠ bump M i) (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
    (hR : ∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hv' : ρ'.v i = ρ.v i) (hL : ∀ d ∈ L, cnt M ρ' i d = cnt M ρ i d) (hcz : ρ'.o c = c')
    (hvot : isOT (ρ.v i) = true) (hs : ∀ t ∈ L.map (cnt M ρ i), t = z ∨ Single t)
    (hcS' : Single c') (hp' : (nzs (L.map (cnt M ρ i)) ++ [c']).Pairwise (fun a b => b ≤ a)) :
    oRhs M ρ' i = psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) c') z := by
  have hlist : (children M i).map (cnt M ρ' i) = L.map (cnt M ρ i) ++ [c'] ++ R.map (cnt M ρ' i) := by
    rw [hch, List.map_append, List.map_cons, List.map_congr_left hL, cnt_cnt ρ' hcb hcu, hcz]
    simp
  have hRz : ∀ t ∈ R.map (cnt M ρ' i), t = z := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact cnt_unc ρ' (hR d hd)
  have hcne' := single_ne_z hcS'
  have hnz' : nzs ((children M i).map (cnt M ρ' i)) = nzs (L.map (cnt M ρ i)) ++ [c'] := by
    rw [hlist, nzs_append, nzs_append, nzs_single hcne', nzs_zeros _ hRz, List.append_nil]
  have hsL : ∀ t ∈ nzs (L.map (cnt M ρ i)), Single t := by
    intro t ht
    simp only [nzs, List.mem_filter] at ht
    rcases hs t ht.1 with h | h
    · exact absurd h (by simpa using ht.2)
    · exact h
  have hsl : ∀ t ∈ nzs (L.map (cnt M ρ i)) ++ [c'], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsL t ht
    · rw [List.mem_singleton] at ht; rw [ht]; exact hcS'
  have hsz' : ∀ t ∈ (children M i).map (cnt M ρ' i), t = z ∨ Single t := by
    intro t ht
    rw [hlist] at ht
    rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_append.mp ht with ht | ht
      · exact hs t ht
      · rw [List.mem_singleton] at ht; rw [ht]; exact Or.inr hcS'
    · exact Or.inl (hRz t ht)
  have hS := sumN_dec _ hsl hp'
  unfold oRhs
  rw [hv', sumN_skip_z hsz' (by rw [hnz']; exact hp'), hnz', sf_psi_spArg hvot hS.1,
    sumN_snoc_dec hsl hp', spArg_app]
  rfl

/-- **The lifted `o` frame**: the last counted child has the value `A`, the frame rewrites, and the child
moves to `next(ζ)`; then the parent is `fsD(o(i), next ζ)`. -/
theorem o_lift {a B μ b ζ : T} (hb : AllGeT (psi (succ μ) z z) b)
    (hA : isOT (psi μ (app b (psi (succ μ) z z)) z) = true) (hAζ : isOT (qnext μ b ζ) = true)
    (htr : lt B (app b (psi (succ μ) z z)) = true ∧
      lt (psi a z z) (psi μ (app b (psi (succ μ) z z)) z) = true)
    (hζ : ζ < psi (succ μ) z z) (hζz : ζ ≠ z) (hBζ : lt B (app b ζ) = true)
    (hX : spArg a B (psi μ (app b (psi (succ μ) z z)) z) ≠ z)
    (hXs : isSucc (spArg a B (psi μ (app b (psi (succ μ) z z)) z)) = false) :
    fsD (psi a (spArg a B (psi μ (app b (psi (succ μ) z z)) z)) z) (qnext μ b ζ) =
      psi a (spArg a B (qnext μ b ζ)) z := by
  rw [fsD_psi hX hXs]
  unfold qnext
  rw [frame_fsD_shift hA hAζ htr hb (lt_irrefl' μ) hζ hζz hBζ]

end Ytosk
