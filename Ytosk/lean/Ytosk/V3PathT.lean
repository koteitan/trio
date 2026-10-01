/-
**3 行・t = 1・q ≠ r: 経路の定理。**

D の各列の局所条件（`OLocal`・`VLocal`: 列の形と枠の条件）から、D のすべての呼び出しで
- 穴 `HoleT`（x の値 Ω_{μ+1} の穴が下にある）、
- 貼り合わせの値の等式（右辺 = fsD(M の値, ζ)）
が成り立つ（`t1_path`）。ζ は始点つきの鎖の項 gamS μ b_r seed m。
-/
import Ytosk.V3StepV

namespace Ytosk

open T

/-- Local conditions at an `o` call of `D`: either only the subscript changes (no counted children),
or the last counted child is the only counted child in `D` and the frame conditions hold. -/
def OLocal (M : Mat) (x : Nat) (ρ : Valn) (ζ μ vr br : T) (i : Nat) : Prop :=
  (DepX M x false i ∧
    ∀ d ∈ children M i, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) ∨
  (¬ DepX M x false i ∧ ∃ L c R, children M i = L ++ c :: R ∧ col M c ≠ bump M i ∧
    ¬ (isUpg M c = true ∧ topped M c = true) ∧
    (∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) ∧
    (∀ d ∈ L, Counted M i d → ¬ DepX M x true d) ∧
    Single (fsD (ρ.o c) ζ) ∧
    (∀ s y, ρ.o c = psi s y z → y = z → ∀ s' y', psi s' y' z ∈ summands (fsD (psi s y z) ζ) →
      y' ≤ preState M ρ i L ∨ s' < ρ.v i) ∧
    (∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L) y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true → lt (preState M ρ i L) (fsD y ζ) = true) ∧
    (∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L) y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 ζ ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z → (split (fsD y ζ) (psi (succ s) z z)).2 = z)) ∧
    (∀ s y, ρ.o c = psi s y z → cof (psi s y z) = .big μ →
      lt μ (ρ.v i) = true ∨ (ρ.v i = vr ∧ step (ρ.v i) (preState M ρ i L) s y z = br)))

/-- Local conditions at a `v` call of `D`: the row-1 parent is outside `D`, and either an upgrade
frame or a bump frame (the last child is the bump child, its last child is the only one in `D`). -/
def VLocal (M : Mat) (x : Nat) (ρ : Valn) (ζ μ : T) (i : Nat) : Prop :=
  entry M 1 i ≠ 0 ∧ (∀ m, par M 1 i = some m → ¬ DepX M x false m) ∧
  ((∃ k, entry M 2 i = 0 ∧ upg M i = some k ∧ k < x ∧ Single (ρ.v k) ∧ Single (fsD (ρ.v k) ζ) ∧
      (∀ q ∈ summands (vOpt ρ (par M 1 i)), q < ρ.v k → q < fsD (ρ.v k) ζ)) ∨
   (∃ L K j k, entry M 2 i ≠ 0 ∧ children M i = L ++ [j] ∧ col M j = bump M i ∧
      children M j = K ++ [k] ∧ (∀ d ∈ K, ¬ DepX M x true d) ∧
      (∀ d ∈ L, ∀ e ∈ children M d, e < x ∧ ¬ DepX M x true e) ∧
      Single (fsD (ρ.o k) ζ) ∧
      (∀ t ∈ K.map ρ.o ++ [ρ.o k], Single t) ∧
      (K.map ρ.o ++ [ρ.o k]).Pairwise (fun a b => b ≤ a) ∧
      (∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t) ∧
      (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))]).Pairwise
        (fun a b => b ≤ a) ∧
      (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]))]).Pairwise
        (fun a b => b ≤ a) ∧
      (∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))], one < t) ∧
      (∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]))],
        one < t) ∧
      fsD (omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
          (omega (sumN (K.map ρ.o ++ [ρ.o k]))))) ζ =
        omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
          (omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ])))) ∧
      (∀ X ∈ [omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
            (omega (sumN (K.map ρ.o ++ [ρ.o k])))),
          omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
            (omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]))))],
        add (vOpt ρ (par M 1 i)) X = X) ∧
      (∀ s b c, sumN (K.map ρ.o ++ [ρ.o k]) = psi s b c →
        cof (sumN (K.map ρ.o ++ [ρ.o k])) = .big μ → lt μ s = true) ∧
      (∀ s b c, app (sumN (nzs (L.map (bumpTerm M ρ i))))
          (omega (sumN (K.map ρ.o ++ [ρ.o k]))) = psi s b c →
        cof (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [ρ.o k])))) =
          .big μ → lt μ s = true)))

/-- The value of a call. -/
def valB (ρ : Valn) (b : Bool) (i : Nat) : T := cond b (ρ.o i) (ρ.v i)

/-- The right side of a call. -/
def rhsB (M : Mat) (ρ : Valn) (b : Bool) (i : Nat) : T := cond b (oRhs M ρ i) (vRhs M ρ i)

section
variable {M : Mat} {x : Nat} {ρ ρN : Valn} {μ br vr seed : T} {m : Nat}

theorem vOpt_glue {i : Nat} {ζ : T} (hx : x + 1 = M.length) (hi : i < x)
    (hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m) :
    vOpt (glue M x ρ ρN ζ) (par M 1 i) = vOpt ρ (par M 1 i) := by
  cases hp : par M 1 i with
  | none => rfl
  | some m =>
    have hm : m < i := par_lt M 1 i m hp
    exact glue_v_lt ρ ρN ζ (by omega) (hpd m hp)

theorem vOpt_ot (hG : Good3 M ρ) {i : Nat} (hiM : i < M.length) : isOT (vOpt ρ (par M 1 i)) = true := by
  cases hp : par M 1 i with
  | none => rfl
  | some m =>
    have hm : m < i := par_lt M 1 i m hp
    exact hG.ot_v m (by omega)

/-- **The path theorem** (`t = 1`, `q ≠ r`). -/
theorem t1_path (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed)
    (hHx : HoleT μ br vr (ρ.o x)) (hxN : ρN.o x = fsD (ρ.o x) (gamS μ br seed m))
    (hO : ∀ i, i < x → DepX M x true i → OLocal M x ρ (gamS μ br seed m) μ vr br i)
    (hV : ∀ i, i < x → DepX M x false i → VLocal M x ρ (gamS μ br seed m) μ i) :
    ∀ b i, DepX M x b i → (i < x ∨ (i = x ∧ b = true)) →
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
    intro _
    exact ⟨hHx, fun h => absurd h (lt_irrefl _)⟩
  | @ochild i c hc hcb' hcu hdc ih =>
    intro hix
    have hcM := (mem_children hc).2
    have hic := (mem_children hc).1
    have hi : i < x := by
      rcases hix with h | ⟨h, _⟩
      · exact h
      · omega
    have hcx : c ≤ x := by omega
    have ihc := (ih (by rcases Nat.lt_or_ge c x with h | h
                        · exact Or.inl h
                        · exact Or.inr ⟨by omega, rfl⟩)).1
    simp only [valB, cond_true] at ihc
    rcases hO i hi (DepX.ochild hc hcb' hcu hdc) with ⟨_, hnc⟩ | ⟨hv, L, c', R, hch, hcb2, hcu2, hR, hLnd,
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
    intro hix
    rcases hix with hi | ⟨rfl, _⟩
    · have ihv := (ih (Or.inl hi)).1
      simp only [valB, cond_false] at ihv
      rcases hO i hi (DepX.ov hv) with ⟨_, hnc⟩ | ⟨hv', _⟩
      · have hst := stepO_sub (ρN := ρN) (ζ := ζ) hC hG hx hi hnc hv ihv
          (hok _ (hG.ot_v i (by omega)) ihv)
        exact ⟨hst.2, fun _ => hst.1⟩
      · exact absurd hv hv'
    · exact ⟨hHx, fun h => absurd h (lt_irrefl _)⟩
  | @vpar i m' h1 hp hdm _ =>
    intro hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    exact absurd hdm ((hV i hi (DepX.vpar h1 hp hdm)).2.1 m' hp)
  | @vupg i k h1 h2 hu hdk ih =>
    intro hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    obtain ⟨_, hpd, hcase⟩ := hV i hi (DepX.vupg h1 h2 hu hdk)
    rcases hcase with ⟨k', _, hu', hk, hVs, hVs', hAV⟩ | ⟨_, _, _, _, h2', _⟩
    · have hkk : k = k' := by rw [hu] at hu'; exact Option.some.inj hu'
      subst hkk
      have ihk := (ih (Or.inl hk)).1
      simp only [valB, cond_false] at ihk
      have hst := stepV_upgA (ρN := ρN) (ζ := ζ) hC hx hi hk h1 h2 hu hpd hdk hVs hVs'
        (le_of_lt (hok _ (hG.ot_v k (by omega)) ihk).2) (vOpt_ot hG (by omega)) hAV ihk
      exact ⟨hst.2, fun _ => hst.1⟩
    · exact absurd h2 h2'
  | @vbump i j k h1 h2 hj hjb hk hdk ih =>
    intro hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    obtain ⟨_, hpd, hcase⟩ := hV i hi (DepX.vbump h1 h2 hj hjb hk hdk)
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
      have hst := stepV_bump (ρN := ρN) (ζ := ζ) hC hx hi h1 h2 hch hjb hchj (hgo k hkx hdk) hK hL
        (vOpt_glue hx hi hpd) hsK hpK hsk' (le_of_lt (hok _ (hG.ot_o k hkM) ihk).2) hsL hpp hpp'
        hgt hgt' hωp hAbs ihk hpassG hpassP
      exact ⟨hst.2, fun _ => hst.1⟩

end

end Ytosk
