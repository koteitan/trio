/-
**道に沿った添字の付け替え**: fsD_transfer の仮定を、比較が実際に降りる部分項だけに狭めた形。

s と fsD(X, ξ) の比較は、X の穴への道（残り・添字・引数）に沿って s の部分項を降り、穴の位置で
s の部分項 u と ξ の比較になる。その u の集合が `Al X s`（X の穴に並ぶ s の部分項）。
`fsD_transfer_al`: Al X s のどの u についても「u < ξ₁ かつ u < ξ₀ なら u < ξ₂」なら、
「s < fsD(X, ξ₁) かつ s < fsD(X, ξ₀) なら s < fsD(X, ξ₂)」。
fsD_transfer は s の部分項すべてに条件を課すが、比べられない深い部分項は外せる（t1-exp の SeedCond の偽はこの形）。
-/
import Ytosk.V3GroupA

namespace Ytosk

open T

/-- `u` is the subterm of `s` aligned with the hole of `X` (the one compared with the index). -/
inductive Al : T → T → T → Prop
  | leaf {a s : T} : a ≠ z → isSucc a = true → Al (psi a z z) s s
  | rest {a b c d e c' u : T} : Al (psi c d e) c' u → Al (psi a b (psi c d e)) (psi a b c') u
  | sub {a a' b' c' u : T} : isSucc a = false → Al a a' u → Al (psi a z z) (psi a' b' c') u
  | arg {a b b' c' u : T} : b ≠ z → isSucc b = false → Al b b' u → Al (psi a b z) (psi a b' c') u

/-- **Transfer along the hole path.** -/
theorem fsD_transfer_al {ξ₀ ξ₁ ξ₂ : T} :
    ∀ {X : T}, OHole X → ∀ s, (∀ u, Al X s u → u < ξ₁ → u < ξ₀ → u < ξ₂) →
      s < fsD X ξ₁ → s < fsD X ξ₀ → s < fsD X ξ₂
  | z, hO, _, _, _, _ => absurd hO (by simp [OHole])
  | psi a b (psi c d e), hO, s, h, h1, h0 => by
    have hO' : OHole (psi c d e) := hO
    have hf : ∀ ξ, fsD (psi a b (psi c d e)) ξ = psi a b (fsD (psi c d e) ξ) := fun _ => rfl
    rw [hf] at h1 h0 ⊢
    cases s with
    | z => exact T.z_lt_psi _ _ _
    | psi a' b' c' =>
      rw [T.psi_lt_psi] at h1 h0 ⊢
      rcases h1 with h1 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h3⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · rcases h0 with h0 | ⟨_, h0⟩ | ⟨_, _, h0⟩
        · exact absurd h0 (lt_irrefl' _)
        · exact absurd h0 (lt_irrefl' _)
        · exact Or.inr (Or.inr ⟨rfl, rfl,
            fsD_transfer_al hO' c' (fun u hu => h u (.rest hu)) h3 h0⟩)
  | psi a b z, hO, s, h, h1, h0 => by
    by_cases hb : b = z
    · subst hb
      have h2 : a ≠ z ∧ (isSucc a = true ∨ OHole a) := by simpa [OHole] using hO
      by_cases hs : isSucc a = true
      · rw [fsD_leaf hs h2.1] at h1 h0 ⊢; exact h s (.leaf h2.1 hs) h1 h0
      · have hs' : isSucc a = false := by simpa using hs
        have hOa : OHole a := by simpa [hs] using h2.2
        rw [fsD_sub h2.1 hs'] at h1 h0 ⊢
        cases s with
        | z => exact T.z_lt_psi _ _ _
        | psi a' b' c' =>
          rw [T.psi_lt_psi] at h1 h0 ⊢
          rcases h1 with h1 | ⟨_, h1⟩ | ⟨_, _, h1⟩
          · rcases h0 with h0 | ⟨_, h0⟩ | ⟨_, _, h0⟩
            · exact Or.inl (fsD_transfer_al hOa a' (fun u hu => h u (.sub hs' hu)) h1 h0)
            · exact absurd h0 (T.not_lt_z _)
            · exact absurd h0 (T.not_lt_z _)
          · exact absurd h1 (T.not_lt_z _)
          · exact absurd h1 (T.not_lt_z _)
    · have hs : isSucc b = false := by
        by_contra hc
        have : isSucc b = true := by simpa using hc
        simp [OHole, hb, this] at hO
      have hOb : OHole b := by
        cases hcb : cof b with
        | big μ => exact ohole_of_cof_big hcb
        | zero => simpa [OHole, hb, hs, hcb] using hO
        | succ => simpa [OHole, hb, hs, hcb] using hO
        | omega => simpa [OHole, hb, hs, hcb] using hO
      rw [fsD_psi hb hs] at h1 h0 ⊢
      cases s with
      | z => exact T.z_lt_psi _ _ _
      | psi a' b' c' =>
        rw [T.psi_lt_psi] at h1 h0 ⊢
        rcases h1 with h1 | ⟨rfl, h2⟩ | ⟨rfl, _, h3⟩
        · exact Or.inl h1
        · rcases h0 with h0 | ⟨_, h0⟩ | ⟨_, _, h0⟩
          · exact absurd h0 (lt_irrefl' _)
          · exact Or.inr (Or.inl ⟨rfl,
              fsD_transfer_al hOb b' (fun u hu => h u (.arg hb hs hu)) h2 h0⟩)
          · exact absurd h0 (T.not_lt_z _)
        · exact absurd h3 (T.not_lt_z _)

/-- The aligned subterms are subterms. -/
theorem Al.subT : ∀ {X s u : T}, Al X s u → SubT u s
  | _, _, _, .leaf _ _ => .refl _
  | _, _, _, .rest h => .rest h.subT
  | _, _, _, .sub _ h => .sub h.subT
  | _, _, _, .arg _ _ h => .arg h.subT

/-- **fsD_transfer from the aligned form** (the old statement is a special case). -/
theorem fsD_transfer_of_al {S : T → Prop} (hS : SubClosed S) {ξ₀ ξ₁ ξ₂ : T}
    (h : ∀ u, S u → u < ξ₁ → u < ξ₀ → u < ξ₂) {X : T} (hO : OHole X) (s : T) (hs : S s) :
    s < fsD X ξ₁ → s < fsD X ξ₀ → s < fsD X ξ₂ :=
  fsD_transfer_al hO s (fun u hu => h u (hS s hs u hu.subT))

end Ytosk
