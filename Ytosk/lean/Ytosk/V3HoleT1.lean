/-
**3 行・t = 1・q ≠ r: 穴と位置の帰納法。**

D の呼び出しの値について、穴 `HoleT` と「r 以下なら対角化の点の下」を同時に示す（`t1_hole`）。
o の枠の通過条件は位置から出す: 子 c の値の共終数が Ω_{μ+1} なら c は r より後ろ、親 i は r 以後で、
i = r なら o(r) = ψ_{v(r)}(b_r) の形、i > r なら F1（μ < v(i)）。
-/
import Ytosk.V3Pos

namespace Ytosk

open T

/-- The shape at an `o` call of `D` (without the frame conditions). -/
def OShape (M : Mat) (x i : Nat) : Prop :=
  (DepX M x false i ∧
    ∀ d ∈ children M i, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) ∨
  (¬ DepX M x false i ∧ ∃ L c R, children M i = L ++ c :: R ∧ col M c ≠ bump M i ∧
    ¬ (isUpg M c = true ∧ topped M c = true) ∧
    (∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) ∧
    (∀ d ∈ L, Counted M i d → ¬ DepX M x true d))

/-- The position part: at or before `r`, a diagonal point. -/
def DiagLe (μ br vr : T) (r i : Nat) (t : T) : Prop :=
  i ≤ r → ∃ a', ¬ lt vr a' = true ∧ DiagAt a' br μ t

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ br vr ζ : T}

/-- **Hole and position** (`t = 1`, `q ≠ r`). -/
theorem t1_hole (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hrx : r < x) (hAr : Anc0 M r x) (hro : ρ.o r = psi vr br z)
    (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hHx : HoleT μ br vr (ρ.o x))
    (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
    (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
    (hV : ∀ i, i < x → DepX M x false i → VLocal M x ρ ζ μ i)
    (hS2 : ∀ i k, i ≤ r → DepX M x false i → entry M 2 i = 0 → upg M i = some k → k ≤ r)
    (hS3 : ∀ i j k, i ≤ r → j ∈ children M i → col M j = bump M i → k ∈ children M j →
      DepX M x true k → k ≤ r) :
    ∀ b i, DepX M x b i → (i < x ∨ (i = x ∧ b = true)) →
      HoleT μ br vr (valB ρ b i) ∧ DiagLe μ br vr r i (valB ρ b i) := by
  have hμ : ¬ lt μ vr = true := by rw [hμr]; exact lt_irrefl' _
  intro b i hD
  induction hD with
  | leaf =>
    intro _
    exact ⟨hHx, fun h => absurd h (by omega)⟩
  | @ochild i c hc hcb' hcu hdc ih =>
    intro hix
    have hcM := (mem_children hc).2
    have hic := (mem_children hc).1
    have hi : i < x := by
      rcases hix with h | ⟨h, _⟩
      · exact h
      · omega
    have hcx : c ≤ x := by omega
    have hcpos : c < x ∨ (c = x ∧ true = true) := by
      rcases Nat.lt_or_ge c x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, rfl⟩
    obtain ⟨ihH, ihD⟩ := ih hcpos
    simp only [valB, cond_true] at ihH ihD
    rcases hOS i hi (DepX.ochild hc hcb' hcu hdc) with ⟨_, hnc⟩ | ⟨hv, L, c', R, hch, hcb2, hcu2, hR, hLnd⟩
    · exact absurd (hnc c hc) (by
        rintro (h | h)
        · exact hcb' h
        · exact hcu h)
    · have hcc : c = c' := by
        rw [hch] at hc
        rcases List.mem_append.mp hc with h | h
        · exact absurd hdc (hLnd c h ⟨hcb', hcu⟩)
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · rcases hR c h with h' | h'
            · exact absurd h' hcb'
            · exact absurd h' hcu
      subst hcc
      have hiM : i < M.length := by omega
      obtain ⟨s, y, hcv⟩ := o_psi_form hC hcM
      have hcot : isOT (psi s y z) = true := by rw [← hcv]; exact hG.ot_o c hcM
      have hframe := o_frame hC hG hiM hch hcb2 hcu2 hR hcM
      rw [hcv, spArg_single] at hframe
      rw [hcv] at ihH ihD
      -- a child after `r` has its parent at or after `r`
      have hpar : r < c → r ≤ i := fun h =>
        par0_ge_of_anc hAr h hcx (mem_children_iff.mp hc).2
      -- the value at `r`
      have hatr : i = r → ρ.v i = vr ∧ step (ρ.v i) (preState M ρ i L) s y z = br := by
        intro hir
        have h := hframe
        rw [hir, hro] at h
        rw [hir]
        exact ⟨(T.psi.inj h).1.symm, (T.psi.inj h).2.1.symm⟩
      have hpass : cof (psi s y z) = .big μ →
          lt μ (ρ.v i) = true ∨ (ρ.v i = vr ∧ step (ρ.v i) (preState M ρ i L) s y z = br) := by
        intro hcof
        have hrc : r < c := by
          by_contra h
          obtain ⟨a', _, hDc⟩ := ihD (by omega)
          exact DiagAt.cof_ne hDc hcof
        rcases Nat.eq_or_lt_of_le (hpar hrc) with h | h
        · exact Or.inr (hatr h.symm)
        · exact Or.inl (hF1 i h hi (DepX.ochild hc hcb' hcu hdc) hv)
      refine ⟨?_, ?_⟩
      · show HoleT μ br vr (ρ.o i)
        rw [hframe]
        exact holeT_oframe hcot ihH hμr hbr hcb hpass
      · intro hir
        show ∃ a', ¬ lt vr a' = true ∧ DiagAt a' br μ (ρ.o i)
        by_cases hcr : c ≤ r
        · rw [hframe]
          exact diag_oframe hcot (ihD hcr) hμr hbr hcb
        · have hir' : i = r := le_antisymm hir (hpar (by omega))
          rw [hir', hro]
          exact ⟨vr, lt_irrefl' _, DiagAt.here hbr hcb hμ⟩
  | @ov i hv ih =>
    intro hix
    rcases hix with hi | ⟨rfl, _⟩
    · obtain ⟨ihH, ihD⟩ := ih (Or.inl hi)
      simp only [valB, cond_false] at ihH ihD
      rcases hOS i hi (DepX.ov hv) with ⟨_, hnc⟩ | ⟨hv', _⟩
      · have hoi := o_nocnt hC hG (by omega) hnc
        have hvz := holeT_ne_z ihH
        have hvs := holeT_not_succ ihH
        refine ⟨?_, ?_⟩
        · show HoleT μ br vr (ρ.o i)
          rw [hoi]; exact holeT_sub hvz hvs ihH
        · intro hir
          show ∃ a', ¬ lt vr a' = true ∧ DiagAt a' br μ (ρ.o i)
          obtain ⟨a', ha', hDv⟩ := ihD hir
          rw [hoi]; exact ⟨a', ha', DiagAt.sub (DiagAt.ne_z hDv) (DiagAt.not_succ hDv) hDv⟩
      · exact absurd hv hv'
    · exact ⟨hHx, fun h => absurd h (by omega)⟩
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
    obtain ⟨_, _, hcase⟩ := hV i hi (DepX.vupg h1 h2 hu hdk)
    rcases hcase with ⟨k', _, hu', hk, hVs, _, _⟩ | ⟨_, _, _, _, h2', _⟩
    · have hkk : k = k' := by rw [hu] at hu'; exact Option.some.inj hu'
      subst hkk
      obtain ⟨ihH, ihD⟩ := ih (Or.inl hk)
      simp only [valB, cond_false] at ihH ihD
      obtain ⟨B, hvi⟩ := upg_val hC (by omega) h1 h2 hu hVs (vOpt_ot hG (by omega))
      have hkz := holeT_ne_z ihH
      refine ⟨?_, ?_⟩
      · show HoleT μ br vr (ρ.v i)
        rw [hvi]; exact holeT_app B hkz ihH
      · intro hir
        show ∃ a', ¬ lt vr a' = true ∧ DiagAt a' br μ (ρ.v i)
        obtain ⟨a', ha', hDk⟩ := ihD (hS2 i k hir (DepX.vupg h1 h2 hu hdk) h2 hu)
        rw [hvi]; exact ⟨a', ha', DiagAt.append B hkz hDk⟩
    · exact absurd h2 h2'
  | @vbump i j k h1 h2 hj hjb hk hdk ih =>
    intro hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    have hiM : i < M.length := by omega
    obtain ⟨_, _, hcase⟩ := hV i hi (DepX.vbump h1 h2 hj hjb hk hdk)
    rcases hcase with ⟨_, h2', _⟩ | ⟨L, K, j', k', _, hch, hjb', hchj, hKnd, hLnd, _, hsK, hpK, hsL,
        hpp, _, hgt, _, _, hAbs, hpassG, hpassP⟩
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
      have hkpos : k < x ∨ (k = x ∧ true = true) := by
        rcases Nat.lt_or_ge k x with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, rfl⟩
      obtain ⟨ihH, ihD⟩ := ih hkpos
      simp only [valB, cond_true] at ihH ihD
      have hvi := v_bump_value hC hiM h1 h2 hch hjb hchj hsK hpK hsL hpp hgt
        (hAbs _ List.mem_cons_self)
      set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
      set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
      have hGot : isOT G = true := (sumN_dec _ hsK hpK).1
      have hkS : Single (ρ.o k) := hsK _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hG : G = app (sumN (K.map ρ.o)) (ρ.o k) := sumN_snoc_dec hsK hpK
      have hsP : ∀ t ∈ P ++ [omega G], Single t := by
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · simp only [hPdef, nzs, List.mem_filter] at ht
          rcases hsL t ht.1 with h | h
          · exact absurd h (by simpa using ht.2)
          · exact h
        · rw [List.mem_singleton] at ht; subst ht; exact single_omega hGot
      have hpot : isOT (app (sumN P) (omega G)) = true := by
        rw [← sumN_snoc_dec hsP hpp]; exact (sumN_dec _ hsP hpp).1
      have hωGz : omega G ≠ z := single_ne_z (single_omega hGot)
      refine ⟨?_, ?_⟩
      · show HoleT μ br vr (ρ.v i)
        rw [hvi]
        have hHG : HoleT μ br vr G := by rw [hG]; exact holeT_app _ (single_ne_z hkS) ihH
        exact holeT_omega hpot (holeT_app _ hωGz (holeT_omega hGot hHG hpassG)) hpassP
      · intro hir
        show ∃ a', ¬ lt vr a' = true ∧ DiagAt a' br μ (ρ.v i)
        obtain ⟨a', ha', hDk⟩ := ihD (hS3 i j k hir hj hjb hk hdk)
        rw [hvi]
        have hDG : DiagAt a' br μ G := by rw [hG]; exact DiagAt.append _ (single_ne_z hkS) hDk
        exact ⟨a', ha', diag_omega hpot (DiagAt.append _ hωGz (diag_omega hGot hDG))⟩

end

end Ytosk
