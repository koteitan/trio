/-
**WfQnL3 (2026-11-01): the path theorem off the closure of the bad calls (toward (E1)).**
`t1_pathB`: `t1_path` (V3PathT) with `OLocal` / `VLocal` asked only at calls outside `DepXB M B`; the conclusion
(hole and glue equation `rhs(glue) = fsD(old, ζ)`) holds at every call of `D` outside `DepXB M B`.
With `B = WfBad.BadSet` and `WfQnL1.vlocal_t1_atX`, `VLocal` holds off the closure (`vlocal_offB`).
-/
import Ytosk.V3PathT
import Ytosk.WfQnL1

namespace Ytosk.WfQnL3
open T Ytosk Ytosk.WfQnE3

section
variable {M : Mat} {x : Nat} {ρ ρN : Valn} {μ br vr seed : T} {m : Nat}

/-- **The path theorem off the closure of the bad calls** (`t1_path` with `VLocal` / `OLocal` asked only
off `DepXB M B`). -/
theorem t1_pathB {B : Nat → Prop} (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed)
    (hHx : HoleT μ br vr (ρ.o x)) (hxN : ρN.o x = fsD (ρ.o x) (gamS μ br seed m))
    (hO : ∀ i, i < x → DepX M x true i → ¬ DepXB M B true i → OLocal M x ρ (gamS μ br seed m) μ vr br i)
    (hV : ∀ i, i < x → DepX M x false i → ¬ DepXB M B false i → VLocal M x ρ (gamS μ br seed m) μ i) :
    ∀ b i, DepX M x b i → ¬ DepXB M B b i → (i < x ∨ (i = x ∧ b = true)) →
      HoleT μ br vr (valB ρ b i) ∧
      (i < x → rhsB M (glue M x ρ ρN (gamS μ br seed m)) b i = fsD (valB ρ b i) (gamS μ br seed m)) := by
  set ζ := gamS μ br seed m with hζ
  have hμ : ¬ lt μ vr = true := by rw [hμr]; exact lt_irrefl' _
  have hok : ∀ t, isOT t = true → HoleT μ br vr t → isOT (fsD t ζ) = true ∧ fsD t ζ < t :=
    fun t hot hH => hok_of_holeT hrot hcb hμ hS hot hH m
  -- the glued `o` value of a `D` column at or below `x`
  have hgo : ∀ c, c ≤ x → DepX M x true c → (glue M x ρ ρN ζ).o c = fsD (ρ.o c) ζ := by
    intro c hc hd
    rcases Nat.lt_or_ge c x with h | h
    · exact glue_o_dep ρ ρN ζ h hd
    · have : c = x := by omega
      subst this; rw [glue_o_ge ρ ρN ζ (le_refl _)]; exact hxN
  intro b i hD
  induction hD with
  | leaf =>
    intro _ _
    exact ⟨hHx, fun h => absurd h (lt_irrefl _)⟩
  | @ochild i c hc hcb' hcu hdc ih =>
    intro hnb hix
    have hcM := (mem_children hc).2
    have hic := (mem_children hc).1
    have hi : i < x := by
      rcases hix with h | ⟨h, _⟩
      · exact h
      · omega
    have hcx : c ≤ x := by omega
    replace ih := ih (fun hd => hnb (DepXB.ochild hc hcb' hcu hd))
    have ihc := (ih (by rcases Nat.lt_or_ge c x with h | h
                        · exact Or.inl h
                        · exact Or.inr ⟨by omega, rfl⟩)).1
    simp only [valB, cond_true] at ihc
    rcases hO i hi (DepX.ochild hc hcb' hcu hdc) hnb with ⟨_, hnc⟩ | ⟨hv, L, c', R, hch, hcb2, hcu2, hR, hLnd,
        hcS', hleaf, hW, hL, hpass⟩
    · exact absurd (hnc c hc) (by
        rintro (h | h)
        · exact hcb' h
        · exact hcu h)
    · -- `c` is the last counted child
      have hcc : c = c' := by
        rw [hch] at hc
        rcases List.mem_append.mp hc with h | h
        · exact absurd hdc (hLnd c h ⟨hcb', hcu⟩)
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · rcases hR c h with h' | h'
            · exact absurd h' hcb'
            · exact absurd h' hcu
      subst hcc
      have hst := stepO_last (ρN := ρN) (ζ := ζ) hC hG hx hi hch hcb2 hcu2 hR hLnd hv hcM
        (hgo c hcx hdc) ihc (hok _ (hG.ot_o c hcM) ihc) hcS' hleaf hW hL hpass hμr hbr hcb
      exact ⟨hst.2, fun _ => hst.1⟩
  | @ov i hv ih =>
    intro hnb hix
    rcases hix with hi | ⟨rfl, _⟩
    · have ihv := (ih (fun hd => hnb (DepXB.ov hd)) (Or.inl hi)).1
      simp only [valB, cond_false] at ihv
      rcases hO i hi (DepX.ov hv) hnb with ⟨_, hnc⟩ | ⟨hv', _⟩
      · have hst := stepO_sub (ρN := ρN) (ζ := ζ) hC hG hx hi hnc hv ihv
          (hok _ (hG.ot_v i (by omega)) ihv)
        exact ⟨hst.2, fun _ => hst.1⟩
      · exact absurd hv hv'
    · exact ⟨hHx, fun h => absurd h (lt_irrefl _)⟩
  | @vpar i m' h1 hp hdm _ =>
    intro hnb hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    exact absurd hdm ((hV i hi (DepX.vpar h1 hp hdm) hnb).2.1 m' hp)
  | @vupg i k h1 h2 hu hdk ih =>
    intro hnb hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    obtain ⟨_, hpd, hcase⟩ := hV i hi (DepX.vupg h1 h2 hu hdk) hnb
    rcases hcase with ⟨k', _, hu', hk, hVs, hVs', hAV⟩ | ⟨_, _, _, _, h2', _⟩
    · have hkk : k = k' := by rw [hu] at hu'; exact Option.some.inj hu'
      subst hkk
      have ihk := (ih (fun hd => hnb (DepXB.vupg h1 h2 hu hd)) (Or.inl hk)).1
      simp only [valB, cond_false] at ihk
      have hst := stepV_upgL (ρN := ρN) (ζ := ζ) hC hx hi hk h1 h2 hu hpd hdk hVs hVs'
        (le_of_lt (hok _ hVs.1 (holeT_last_g ihk)).2) (vOpt_ot hG (by omega)) hAV ihk
      exact ⟨hst.2, fun _ => hst.1⟩
    · exact absurd h2 h2'
  | @vbump i j k h1 h2 hj hjb hk hdk ih =>
    intro hnb hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    obtain ⟨_, hpd, hcase⟩ := hV i hi (DepX.vbump h1 h2 hj hjb hk hdk) hnb
    rcases hcase with ⟨_, h2', _⟩ | ⟨L, K, j', k', _, hch, hjb', hchj, hKnd, hLnd, hsk', hsK, hpK, hsL,
        hpp, hpp', hgt, hgt', hωp, hAbs, hpassG, hpassP⟩
    · exact absurd h2' h2
    · have hjj : j = j' := by
        rw [hch] at hj
        rcases List.mem_append.mp hj with h | h
        · exact absurd hdk (hLnd j h k hk).2
        · exact List.mem_singleton.mp h
      subst hjj
      have hkk : k = k' := by
        rw [hchj] at hk
        rcases List.mem_append.mp hk with h | h
        · exact absurd hdk (hKnd k h)
        · exact List.mem_singleton.mp h
      subst hkk
      have hkM := (mem_children hk).2
      have hkx : k ≤ x := by omega
      replace ih := ih (fun hd => hnb (DepXB.vbump h1 h2 hj hjb hk hd))
      have ihk := (ih (by rcases Nat.lt_or_ge k x with h | h
                          · exact Or.inl h
                          · exact Or.inr ⟨by omega, rfl⟩)).1
      simp only [valB, cond_true] at ihk
      have hK : ∀ d ∈ K, (glue M x ρ ρN ζ).o d = ρ.o d := by
        intro d hd
        have hsort := children_sorted M j
        rw [hchj] at hsort
        have hdk' : d < k := (List.pairwise_append.mp hsort).2.2 d hd k (List.mem_singleton_self _)
        exact glue_o_lt ρ ρN ζ (by omega) (hKnd d hd)
      have hL : ∀ d ∈ L, bumpTerm M (glue M x ρ ρN ζ) i d = bumpTerm M ρ i d := by
        intro d hd
        unfold bumpTerm
        split
        · congr 2
          apply List.map_congr_left
          intro e he
          exact glue_o_lt ρ ρN ζ (hLnd d hd e he).1 (hLnd d hd e he).2
        · rfl
      have hst := stepV_bumpG (ρN := ρN) (ζ := ζ) hC hx hi h1 h2 hch hjb hchj (hgo k hkx hdk) hK hL
        (vOpt_glue hx hi hpd) hsK hpK hsk' (le_of_lt (hok _ (hG.ot_o k hkM) ihk).2) hsL hpp hpp'
        hgt hgt' hωp (vOpt_ot hG (by omega)) hAbs ihk hpassG hpassP
      exact ⟨hst.2, fun _ => hst.1⟩


end

/-- **Off the closure of the bad calls, `VLocal or bad` is `VLocal`.** -/
theorem vlocal_offB {M : Mat} {x r : Nat} {ρ : Valn} {ζ μ : T}
    (hVX : ∀ i, i < x → DepX M x false i → VLocal M x ρ ζ μ i ∨ WfBad.BadSet M x ρ r ζ i) :
    ∀ i, i < x → DepX M x false i → ¬ DepXB M (WfBad.BadSet M x ρ r ζ) false i → VLocal M x ρ ζ μ i := by
  intro i hi hv hnb
  rcases hVX i hi hv with h | h
  · exact h
  · exact absurd (DepXB.leaf h) hnb

end Ytosk.WfQnL3
