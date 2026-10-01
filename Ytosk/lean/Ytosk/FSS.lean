/-
**始点つきの対角化（補題 3.3 の一般化）。**

対角化の点 ψ_a(b)（cof b = Ω_{μ+1}、μ ≥ a）で、Denis 氏の列 γ_0 = 0 の代わりに始点 γ′_0 = 始点から
γ′_{k+1} = ψ_μ(b[γ′_k]) とする。展開 M[n] では始点は M[1] での r の値（最後のコピーには上げ役がないので 0 にならない）。
始点の条件（`SeedOK`）のもとで、列の各項 ψ_a(b[γ′_m]) は標準形で、◁ 関係を `Gc` が自明な形で満たす
（したがって上の ω の段の標準形も添字の成分の条件なしで出る）。
-/
import Ytosk.SPFSD

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The seeded diagonal chain at `μ`: `γ′_0 = seed`, `γ′_{k+1} = ψ_μ(b[γ′_k])`. -/
def gamS (μ b seed : T) : Nat → T
  | 0 => seed
  | k + 1 => psi μ (fs b (gamS μ b seed k)) z

/-- The conditions on the seed at the diagonal node `ψ_a(b)`. -/
structure SeedOK (a b μ seed : T) : Prop where
  ot : isOT seed = true
  lt_om : seed < psi (succ μ) z z
  lt_next : seed < psi μ (fs b seed) z
  comps_a : ∀ g ∈ comps a seed, g < fs b seed
  dom : ∀ u c0 c1, fs b seed < c0 → c0 ≤ b → ¬ lt a u = true →
    ∀ g ∈ comps u seed, ∃ y ∈ comps u (psi a c0 c1) ++ Gc u z, g ≤ y

section chain
variable {a b μ seed : T} (hot : isOT (psi a b z) = true) (hcb : cof b = .big μ)
  (hμ : ¬ lt μ a = true) (hS : SeedOK a b μ seed)
include hot hcb hμ hS

theorem gamS_lt_om : ∀ k, gamS μ b seed k < psi (succ μ) z z
  | 0 => hS.lt_om
  | k + 1 => by
    show psi μ _ z < _
    rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ)

theorem gamS_valid : ∀ k, ValidLt b (gamS μ b seed k) := fun k => by
  unfold ValidLt; rw [hcb]; exact gamS_lt_om hot hcb hμ hS k

theorem gamS_mono : ∀ k, gamS μ b seed k < gamS μ b seed (k + 1)
  | 0 => hS.lt_next
  | k + 1 => by
    show psi μ (fs b (gamS μ b seed k)) z < psi μ (fs b (gamS μ b seed (k + 1))) z
    rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, fs_mono hcb (gamS_mono k)⟩

theorem gamS_ge : ∀ k, psi μ z z ≤ gamS μ b seed (k + 1) := by
  intro k
  show psi μ z z ≤ psi μ (fs b (gamS μ b seed k)) z
  rw [le_iff]
  rcases (le_iff _ _).mp (z_le (fs b (gamS μ b seed k))) with h4 | h4
  · left; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h4⟩
  · right; rw [← h4]

theorem gamS_ot : ∀ k, isOT (gamS μ b seed k) = true := by
  have hbot : isOT b = true := isOT_arg hot
  have hcomp := comps_lt hot
  have hμot : isOT μ = true := isOT_cof_mu hbot hcb
  have haμ : a ≤ μ := le_of_not_gt hμ
  have hcompμ : ∀ g ∈ comps μ b, g < b := fun g hg => hcomp g (comps_mono haμ hg)
  intro k
  induction k with
  | zero => exact hS.ot
  | succ k ih =>
    show isOT (psi μ (fs b (gamS μ b seed k)) z) = true
    apply psi_ot_of_lhd hμot (isOT_fs hbot ⟨ih, by rw [hcb]; exact gamS_lt_om hot hcb hμ hS k⟩)
      (lhd_fs hbot (gamS_valid hot hcb hμ hS k)) hcompμ
    intro _ g hg
    cases k with
    | zero => exact hS.comps_a g (comps_mono haμ hg)
    | succ j =>
      have hss : lt μ μ = false := Bool.eq_false_iff.mpr (lt_irrefl' μ)
      have ih' := ih
      simp only [gamS] at hg ih'
      simp only [comps, hss, Bool.false_eq_true, if_false, List.mem_append,
        List.mem_cons] at hg
      have hmono : fs b (gamS μ b seed j) < fs b (gamS μ b seed (j + 1)) :=
        fs_mono hcb (gamS_mono hot hcb hμ hS j)
      rcases hg with (rfl | hg | hg) | hg
      · exact hmono
      · exact lt_trans (comps_lt ih' g hg) hmono
      · rw [comps_self_nil hμot] at hg; simp at hg
      · simp at hg

/-- The component condition along the chain (`Q` in Lemma 3.3). -/
theorem gamS_comps : ∀ k, ∀ g ∈ comps a (gamS μ b seed k), g < fs b (gamS μ b seed k) := by
  have hbot : isOT b = true := isOT_arg hot
  have hcomp := comps_lt hot
  intro k
  induction k with
  | zero => exact hS.comps_a
  | succ j ih =>
    intro g hg
    simp only [gamS] at hg
    simp only [comps, hμ, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    have hmono : fs b (gamS μ b seed j) < fs b (gamS μ b seed (j + 1)) :=
      fs_mono hcb (gamS_mono hot hcb hμ hS j)
    have hV : Valid b (gamS μ b seed j) :=
      ⟨gamS_ot hot hcb hμ hS j, by rw [hcb]; exact gamS_lt_om hot hcb hμ hS j⟩
    rcases hg with (rfl | hg | hg) | hg
    · exact hmono
    · have hR := psi_ot_of_lhd (isOT_sub hot) (isOT_fs hbot hV)
        (lhd_fs hbot (gamS_valid hot hcb hμ hS j)) hcomp (fun _ => ih)
      exact lt_trans (comps_lt hR g hg) hmono
    · have hF5 := gamS_ge hot hcb hμ hS j
      have hF1 := gamS_lt_om hot hcb hμ hS (j + 1)
      have hgb : g ∈ comps a b := comps_mu hbot hcb hF5 hF1
        (le_of_lt (fs_lt (gamS_valid hot hcb hμ hS (j + 1)))) (le_refl b) hμ g hg
      have hgb' := hcomp g hgb
      by_contra hcon
      have hgy : g ∈ comps a g := comps_mu hbot hcb hF5 hF1
        (le_of_not_gt hcon) (le_of_lt hgb') hμ g hg
      exact Nat.lt_irrefl _ (size_comps hgy)
    · simp at hg

/-- **The diagonal node with a seeded index is standard.** -/
theorem isOT_diag_seed (m : Nat) : isOT (psi a (fs b (gamS μ b seed m)) z) = true := by
  have hbot : isOT b = true := isOT_arg hot
  have hV : Valid b (gamS μ b seed m) :=
    ⟨gamS_ot hot hcb hμ hS m, by rw [hcb]; exact gamS_lt_om hot hcb hμ hS m⟩
  exact psi_ot_of_lhd (isOT_sub hot) (isOT_fs hbot hV) (lhd_fs hbot (gamS_valid hot hcb hμ hS m))
    (comps_lt hot) (fun _ => gamS_comps hot hcb hμ hS m)

theorem gamS_fs_le : ∀ j k, j ≤ k → fs b (gamS μ b seed j) ≤ fs b (gamS μ b seed k) := by
  intro j k hjk
  induction hjk with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (le_of_lt (fs_mono hcb (gamS_mono hot hcb hμ hS _)))

/-- **The diagonal node with a seeded index is below the node** in Buchholz's sense, with no index
components. -/
theorem lhd_diag_seed (m : Nat) : Lhd z (psi a (fs b (gamS μ b seed m)) z) (psi a b z) := by
  have hbot : isOT b = true := isOT_arg hot
  have F2 := gamS_valid hot hcb hμ hS
  have IH : ∀ k, Lhd (gamS μ b seed k) (fs b (gamS μ b seed k)) b := fun k => lhd_fs hbot (F2 k)
  refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, fs_lt (F2 _)⟩, fun u c h1 h2 => ?_⟩
  obtain ⟨c0, c1, rfl, hc1, hc2⟩ := between_psi h1 h2
  intro x hx
  simp only [comps, List.mem_append] at hx
  rcases hx with hx | hx
  · split at hx
    · simp at hx
    · rename_i hau
      have hin : ∀ w ∈ comps u c0, w ∈ comps u (psi a c0 c1) := fun w hw =>
        mem_comps_psi_arg hau hw
      have hc0in : c0 ∈ comps u (psi a c0 c1) := by simp [comps, hau]
      simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact ⟨c0, List.mem_append_left _ hc0in, hc1⟩
      · rcases (le_iff _ _).mp hc1 with hlt | heq
        · have D : ∀ k, k ≤ m → ∀ x ∈ comps u (fs b (gamS μ b seed k)),
              ∃ y ∈ comps u (psi a c0 c1) ++ Gc u z, x ≤ y := by
            intro k
            induction k with
            | zero =>
              intro _ x hx
              have hk : fs b (gamS μ b seed 0) < c0 :=
                lt_of_le_of_lt (gamS_fs_le hot hcb hμ hS _ _ (Nat.zero_le _)) hlt
              obtain ⟨y, hy, hxy⟩ := (IH 0).2 u c0 hk hc2 x hx
              rcases List.mem_append.mp hy with hy | hy
              · exact ⟨y, List.mem_append_left _ (hin y hy), hxy⟩
              · simp only [Gc, List.mem_cons] at hy
                rcases hy with rfl | hy
                · exact ⟨z, List.mem_append_right _ (by simp [Gc]), hxy⟩
                · obtain ⟨y', hy', hyy'⟩ := hS.dom u c0 c1 hk hc2 hau y hy
                  exact ⟨y', hy', le_trans hxy hyy'⟩
            | succ j ihj =>
              intro hj x hx
              have hk : fs b (gamS μ b seed (j + 1)) < c0 :=
                lt_of_le_of_lt (gamS_fs_le hot hcb hμ hS _ _ hj) hlt
              obtain ⟨y, hy, hxy⟩ := (IH (j + 1)).2 u c0 hk hc2 x hx
              rcases List.mem_append.mp hy with hy | hy
              · exact ⟨y, List.mem_append_left _ (hin y hy), hxy⟩
              · simp only [Gc, List.mem_cons] at hy
                rcases hy with rfl | hy
                · exact ⟨z, List.mem_append_right _ (by simp [Gc]), hxy⟩
                · simp only [gamS] at hy
                  simp only [comps, List.mem_append] at hy
                  rcases hy with hy | hy
                  · split at hy
                    · simp at hy
                    · rename_i hμu
                      simp only [List.mem_cons, List.mem_append] at hy
                      rcases hy with rfl | hy | hy
                      · have : fs b (gamS μ b seed j) < c0 :=
                          lt_of_le_of_lt (gamS_fs_le hot hcb hμ hS _ _ (by omega)) hlt
                        exact ⟨c0, List.mem_append_left _ hc0in, le_trans hxy (le_of_lt this)⟩
                      · obtain ⟨y', hy', hyy'⟩ := ihj (by omega) y hy
                        exact ⟨y', hy', le_trans hxy hyy'⟩
                      · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                        have hg1 : psi μ z z ≤ gamS μ b seed m := by
                          rw [hm']; exact gamS_ge hot hcb hμ hS m'
                        have := comps_mu hbot hcb hg1 (gamS_lt_om hot hcb hμ hS m) hc1 hc2 hμu y hy
                        exact ⟨y, List.mem_append_left _ (hin y this), hxy⟩
                  · simp at hy
          exact D m (Nat.le_refl _) x hx
        · rw [heq] at hx
          exact ⟨x, List.mem_append_left _ (hin x hx), le_refl _⟩
      · exact ⟨x, List.mem_append_left _ (by simp [comps, hau, hx]), le_refl _⟩
  · simp at hx

end chain

/-! ## 対角化の点から上へ -/

/-- `t` has its diagonal point at `ψ_a(b)`: above it only `ω`-cofinal layers. -/
inductive DiagAt (a b μ : T) : T → Prop
  | here : b ≠ z → cof b = .big μ → ¬ lt μ a = true → DiagAt a b μ (psi a b z)
  | rest {a' b' c d e : T} : DiagAt a b μ (psi c d e) → DiagAt a b μ (psi a' b' (psi c d e))
  | arg {a' b' : T} : b' ≠ z → isSucc b' = false → DiagAt a b μ b' → DiagAt a b μ (psi a' b' z)
  | sub {a' : T} : a' ≠ z → isSucc a' = false → DiagAt a b μ a' → DiagAt a b μ (psi a' z z)

theorem fsD_here {a b μ ζ : T} (hb : b ≠ z) (hc : cof b = .big μ) :
    fsD (psi a b z) ζ = psi a (fs b ζ) z := by
  rw [fsD_psi hb (not_succ_of_cof_big hc), fsD_eq_fs hc]

theorem fsD_sub {a' ζ : T} (ha : a' ≠ z) (hs : isSucc a' = false) :
    fsD (psi a' z z) ζ = psi (fsD a' ζ) z z := by
  conv => lhs; unfold fsD
  rw [if_pos rfl, if_neg ha, if_neg (by rw [hs]; simp)]

/-- **Seeded Lemma 3.3.** With the diagonal point at `ψ_a(b)` and a good seed, every member of the
seeded chain gives a standard term below `t`, with no index components in the `◁` relation. -/
theorem fsD_seed {a b μ seed : T} (hS : SeedOK a b μ seed) :
    ∀ {t : T}, DiagAt a b μ t → isOT t = true → ∀ m,
      isOT (fsD t (gamS μ b seed m)) = true ∧ Lhd z (fsD t (gamS μ b seed m)) t := by
  intro t hD
  induction hD with
  | here hb hc hμ =>
    intro hot m
    rw [fsD_here hb hc]
    exact ⟨isOT_diag_seed hot hc hμ hS m, lhd_diag_seed hot hc hμ hS m⟩
  | @rest a' b' c d e _ ih =>
    intro hot m
    obtain ⟨hot', hl⟩ := ih (isOT_rest hot) m
    show isOT (psi a' b' (fsD (psi c d e) _)) = true ∧ Lhd z (psi a' b' (fsD (psi c d e) _)) _
    refine ⟨?_, by simpa using lhd_app (psi a' b' z) hl⟩
    obtain ⟨h1, h2, _, h4, h5⟩ := isOT_psi_iff.mp hot
    rw [isOT_psi_iff]
    exact ⟨h1, h2, hot', le_trans (head_le_of_lt hl.1) h4, h5⟩
  | @arg a' b' hb hs _ ih =>
    intro hot m
    obtain ⟨hot', hl⟩ := ih (isOT_arg hot) m
    rw [fsD_psi hb hs]
    refine ⟨?_, lhd_psi a' hl⟩
    apply psi_ot_of_lhd (isOT_sub hot) hot' hl (comps_lt hot)
    intro _ g hg; simp [comps] at hg
  | @sub a' ha hs _ ih =>
    intro hot m
    obtain ⟨hot', hl⟩ := ih (isOT_sub hot) m
    rw [fsD_sub ha hs]
    refine ⟨by rw [isOT_psi_iff]; exact ⟨hot', rfl, rfl, z_le _, by simp [comps]⟩, ?_⟩
    refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inl hl.1, fun u c h1 h2 => ?_⟩
    obtain ⟨v, c0, c1, rfl, hv1, hv2⟩ := between_sub h1 h2
    intro x hx
    simp only [comps, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · simp at hx
      · rename_i hau
        have hvu : ¬ lt v u = true := fun h => hau (lt_of_le_of_lt hv1 h)
        simp only [List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · exact ⟨z, List.mem_append_right _ (List.mem_cons_self), le_refl _⟩
        · simp at hx
        · rcases (le_iff _ _).mp hv1 with hv1 | rfl
          · obtain ⟨y, hy, hxy⟩ := hl.2 u v hv1 hv2 x hx
            refine ⟨y, ?_, hxy⟩
            rcases List.mem_append.mp hy with hy | hy
            · exact List.mem_append_left _ (by simp [comps, hvu, hy])
            · exact List.mem_append_right _ hy
          · exact ⟨x, List.mem_append_left _ (by simp [comps, hvu, hx]), le_refl _⟩
    · simp at hx

/-! ## 枠を上る DiagAt -/

theorem DiagAt.append {a b μ : T} : ∀ (B : T) {c : T}, c ≠ z → DiagAt a b μ c → DiagAt a b μ (app B c)
  | z, _, _, h => by simpa using h
  | psi a' b' B', c, hc, h => by
    simp only [app_psi]
    cases hB : app B' c with
    | z => exact absurd (app_eq_z hB).2 hc
    | psi d e f =>
      have := DiagAt.append B' hc h
      rw [hB] at this
      exact DiagAt.rest this

/-- The diagonal point stays below the node after one frame (any of the three cases). -/
theorem DiagAt.frame {a b μ a' b' s y : T} (hc : isOT (psi s y z) = true)
    (hD : DiagAt a b μ (psi s y z))
    (hcase : ((y ≤ b' ∨ s < a') ∧ isOT (app b' (psi s y z)) = true) ∨
      ((lt b' y = true ∧ lt (psi a' z z) (psi s y z) = true) ∧ (split y (psi (succ s) z z)).2 ≠ z) ∨
      ((lt b' y = true ∧ lt (psi a' z z) (psi s y z) = true) ∧ (split y (psi (succ s) z z)).2 = z ∧
        DiagAt a b μ y)) :
    DiagAt a b μ (spArg a' b' (psi s y z)) := by
  have hcz : psi s y z ≠ z := by simp
  rcases hcase with ⟨hno, hbc⟩ | ⟨htr, hlo⟩ | ⟨htr, hlo, hy⟩
  · have h1 : spArg a' b' (psi s y z) = app b' (psi s y z) := by
      apply spArg_eq_app hbc
      intro s' y' hq
      simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hq
      obtain ⟨rfl, rfl, _⟩ := hq; exact hno
    rw [h1]; exact DiagAt.append b' hcz hD
  · have hH : spArg a' b' (psi s y z) = app (split y (psi (succ s) z z)).1 (psi s y z) := by
      rw [spArg_cons]; show step a' b' s y z = _
      unfold step; rw [if_pos htr, H_eq hc]; simp [hlo]
    rw [hH]; exact DiagAt.append _ hcz hD
  · have hH : spArg a' b' (psi s y z) = y := by
      rw [spArg_cons]; show step a' b' s y z = _
      unfold step; rw [if_pos htr, H_eq hc, if_pos hlo, app_z_right]
      have := split_app (psi (succ s) z z) y; rw [hlo, app_z_right] at this; exact this
    rw [hH]; exact hy

theorem DiagAt.ne_z {a b μ : T} {t : T} (h : DiagAt a b μ t) : t ≠ z := by
  cases h <;> simp

/-- The argument of a node over the diagonal point. -/
theorem DiagAt.arg_inv {a b μ a' y : T} (h : DiagAt a b μ (psi a' y z)) (hy : y ≠ z)
    (hne : ¬ (a' = a ∧ y = b)) : DiagAt a b μ y := by
  cases h with
  | here => exact absurd ⟨rfl, rfl⟩ hne
  | arg _ _ h' => exact h'
  | sub => exact absurd rfl hy

/-! ## 正規化の 1 段の形 -/

/-- One step of `sp` either ends with the summand (no rewrite, or a rewrite with a lower part), or is
`y` itself (a rewrite with no lower part). -/
theorem step_cases {a b s y : T} (hc : isOT (psi s y z) = true) :
    (∃ B, step a b s y z = app B (psi s y z)) ∨
      (step a b s y z = y ∧ (split y (psi (succ s) z z)).2 = z ∧ y ≠ z ∧
        lt b y = true ∧ lt (psi a z z) (psi s y z) = true) := by
  unfold step
  by_cases htr : lt b y = true ∧ lt (psi a z z) (psi s y z) = true
  · rw [if_pos htr, H_eq hc]
    by_cases hlo : (split y (psi (succ s) z z)).2 = z
    · right
      rw [if_pos hlo, app_z_right]
      have := split_app (psi (succ s) z z) y; rw [hlo, app_z_right] at this
      refine ⟨this, hlo, ?_, htr⟩
      rintro rfl; simp [lt] at htr
    · left; rw [if_neg hlo]; exact ⟨_, rfl⟩
  · rw [if_neg htr]
    left
    obtain ⟨B, _, _, _, he⟩ := add_prefix s y b
    exact ⟨B, he⟩

/-- **The cofinality `Ω_{μ+1}` survives one step** (when it passes `ψ_s`). -/
theorem cof_step {a b s y μ : T} (hc : isOT (psi s y z) = true) (hcof : cof (psi s y z) = .big μ) :
    cof (step a b s y z) = .big μ := by
  rcases step_cases (a := a) (b := b) hc with ⟨B, hB⟩ | ⟨hy, _, hyz, _⟩
  · rw [hB, cof_app B (by simp), hcof]
  · rw [hy]; exact (cof_psi_inv hyz hcof).1

/-- **The diagonal point stays below after one step**, unless the step rewrites the diagonal node
itself away (then the argument of the diagonal node is the result). -/
theorem DiagAt.step {a0 b0 μ a b s y : T} (hc : isOT (psi s y z) = true)
    (hD : DiagAt a0 b0 μ (psi s y z)) :
    DiagAt a0 b0 μ (step a b s y z) ∨ (s = a0 ∧ y = b0 ∧ step a b s y z = b0) := by
  rcases step_cases (a := a) (b := b) hc with ⟨B, hB⟩ | ⟨hy, _, hyz, _⟩
  · left; rw [hB]; exact DiagAt.append B (by simp) hD
  · by_cases hne : s = a0 ∧ y = b0
    · right; exact ⟨hne.1, hne.2, by rw [hy, hne.2]⟩
    · left; rw [hy]; exact DiagAt.arg_inv hD hyz hne

/-- **`fsD` is increasing in the index above a diagonal point.** -/
theorem DiagAt.fsD_mono {a b μ : T} {t : T} (h : DiagAt a b μ t) {η η' : T} (hlt : η < η') :
    fsD t η < fsD t η' := by
  induction h with
  | here hb hc _ =>
    rw [fsD_here hb hc, fsD_here hb hc, psi_lt_psi_z_iff]
    exact Or.inr ⟨rfl, fs_mono hc hlt⟩
  | @rest a' b' c d e _ ih =>
    show psi a' b' (fsD (psi c d e) η) < psi a' b' (fsD (psi c d e) η')
    rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, ih⟩)
  | arg hb hs _ ih =>
    rw [fsD_psi hb hs, fsD_psi hb hs, psi_lt_psi_z_iff]
    exact Or.inr ⟨rfl, ih⟩
  | sub ha hs _ ih =>
    rw [fsD_sub ha hs, fsD_sub ha hs, psi_lt_psi_z_iff]
    exact Or.inl ih

/-- With a big cofinality, `fsD` is increasing in the index. -/
theorem fsD_mono_big {t μ : T} (hc : cof t = .big μ) {η η' : T} (hlt : η < η') :
    fsD t η < fsD t η' := by
  rw [fsD_eq_fs hc, fsD_eq_fs hc]; exact fs_mono hc hlt

/-- The diagonal node is standard when the term is. -/
theorem DiagAt.ot_node {a b μ : T} {t : T} (h : DiagAt a b μ t) (hot : isOT t = true) :
    isOT (psi a b z) = true := by
  induction h with
  | here => exact hot
  | rest _ ih => exact ih (isOT_rest hot)
  | arg _ _ _ ih => exact ih (isOT_arg hot)
  | sub _ _ _ ih => exact ih (isOT_sub hot)

/-- The seed `0` is always good. -/
theorem seedOK_z (a b μ : T) : SeedOK a b μ z where
  ot := rfl
  lt_om := T.z_lt_psi _ _ _
  lt_next := T.z_lt_psi _ _ _
  comps_a := by intro g hg; simp [comps] at hg
  dom := by intro u c0 c1 _ _ _ g hg; simp [comps] at hg

/-- **Denis's `γ_1 = ψ_μ(b[0])` is a good seed.** -/
theorem seedOK_gam1 {a b μ : T} (hot : isOT (psi a b z) = true) (hcb : cof b = .big μ)
    (hμ : ¬ lt μ a = true) : SeedOK a b μ (psi μ (fs b z) z) := by
  have hS0 := seedOK_z a b μ
  have hbot : isOT b = true := isOT_arg hot
  refine ⟨gamS_ot hot hcb hμ hS0 1, gamS_lt_om hot hcb hμ hS0 1, gamS_mono hot hcb hμ hS0 1,
    gamS_comps hot hcb hμ hS0 1, ?_⟩
  intro u c0 c1 h1 h2 hau g hg
  have hμu : ¬ lt μ u = true := fun h => hau (show a < u from lt_of_le_of_lt (le_of_not_gt hμ) h)
  have hin : ∀ w ∈ comps u c0, w ∈ comps u (psi a c0 c1) := fun w hw => mem_comps_psi_arg hau hw
  have hc0in : c0 ∈ comps u (psi a c0 c1) := by simp [comps, hau]
  have hg1 : fs b z < fs b (psi μ (fs b z) z) := fs_mono hcb (T.z_lt_psi _ _ _)
  simp only [comps, hμu, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
  rcases hg with (rfl | hg | hg) | hg
  · exact ⟨c0, List.mem_append_left _ hc0in, le_of_lt (lt_trans hg1 h1)⟩
  · have hl := lhd_fs hbot (show ValidLt b z by unfold ValidLt; rw [hcb]; exact T.z_lt_psi _ _ _)
    obtain ⟨y, hy, hgy⟩ := hl.2 u c0 (lt_trans hg1 h1) h2 g hg
    rcases List.mem_append.mp hy with hy | hy
    · exact ⟨y, List.mem_append_left _ (hin y hy), hgy⟩
    · exact ⟨y, List.mem_append_right _ (by simpa [Gc, comps] using hy), hgy⟩
  · have hge : psi μ z z ≤ psi μ (fs b z) z := gamS_ge hot hcb hμ hS0 0
    have hlt : psi μ (fs b z) z < psi (succ μ) z z := gamS_lt_om hot hcb hμ hS0 1
    have := comps_mu hbot hcb hge hlt (le_of_lt h1) h2 hμu g hg
    exact ⟨g, List.mem_append_left _ (hin g this), le_refl _⟩
  · simp at hg

/-- **A seed below Denis's `γ_1` and `◁`-below `b` is good.** -/
theorem seedOK_of_lhd {a b μ σ : T} (hot : isOT (psi a b z) = true) (hcb : cof b = .big μ)
    (hμ : ¬ lt μ a = true) (hsot : isOT (psi μ σ z) = true) (hσ : σ ≤ fs b z) (hl : Lhd z σ b) :
    SeedOK a b μ (psi μ σ z) := by
  have hbot : isOT b = true := isOT_arg hot
  have hcomp := comps_lt hot
  have hS0 := seedOK_z a b μ
  have hsz : z < psi μ σ z := T.z_lt_psi _ _ _
  have hmono : fs b z < fs b (psi μ σ z) := fs_mono hcb hsz
  have hσlt : σ < fs b (psi μ σ z) := lt_of_le_of_lt hσ hmono
  have hslt : psi μ σ z < psi (succ μ) z z := by
    rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ)
  have hval : ValidLt b (psi μ σ z) := by unfold ValidLt; rw [hcb]; exact hslt
  have hfsle : fs b (psi μ σ z) ≤ b := le_of_lt (fs_lt hval)
  have hge : psi μ z z ≤ psi μ σ z := by
    rw [le_iff]
    rcases (le_iff _ _).mp (z_le σ) with h4 | h4
    · left; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h4⟩
    · right; rw [← h4]
  -- the Denis node `ψ_a(b[0])` is standard
  have hd0 : isOT (psi a (fs b z) z) = true := isOT_diag_seed hot hcb hμ hS0 0
  have hcd0 := comps_lt hd0
  refine ⟨hsot, hslt, ?_, ?_, ?_⟩
  · rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hσlt⟩
  · intro g hg
    simp only [comps, hμ, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    rcases hg with (rfl | hg | hg) | hg
    · exact hσlt
    · -- a component of `σ`: dominated by components of `b[0]`
      rcases (le_iff _ _).mp hσ with hlt | heq
      · obtain ⟨y, hy, hgy⟩ := hl.2 a (fs b z) hlt (le_of_lt (fs_lt (by
          unfold ValidLt; rw [hcb]; exact T.z_lt_psi _ _ _))) g hg
        rcases List.mem_append.mp hy with hy | hy
        · exact lt_of_le_of_lt hgy (lt_trans (hcd0 y hy) hmono)
        · simp [Gc, comps] at hy; subst hy
          exact lt_of_le_of_lt hgy (lt_of_le_of_lt (z_le _) hmono)
      · rw [heq] at hg; exact lt_trans (hcd0 g hg) hmono
    · have hgb : g ∈ comps a b := comps_mu hbot hcb hge hslt hfsle (le_refl b) hμ g hg
      have hgb' := hcomp g hgb
      by_contra hcon
      have hgy : g ∈ comps a g := comps_mu hbot hcb hge hslt (le_of_not_gt hcon) (le_of_lt hgb') hμ g hg
      exact Nat.lt_irrefl _ (size_comps hgy)
    · simp at hg
  · intro u c0 c1 h1 h2 hau g hg
    have hμu : ¬ lt μ u = true := fun h => hau (show a < u from lt_of_le_of_lt (le_of_not_gt hμ) h)
    have hin : ∀ w ∈ comps u c0, w ∈ comps u (psi a c0 c1) := fun w hw => mem_comps_psi_arg hau hw
    have hc0in : c0 ∈ comps u (psi a c0 c1) := by simp [comps, hau]
    simp only [comps, hμu, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    rcases hg with (rfl | hg | hg) | hg
    · exact ⟨c0, List.mem_append_left _ hc0in, le_of_lt (lt_trans hσlt h1)⟩
    · obtain ⟨y, hy, hgy⟩ := hl.2 u c0 (lt_trans hσlt h1) h2 g hg
      rcases List.mem_append.mp hy with hy | hy
      · exact ⟨y, List.mem_append_left _ (hin y hy), hgy⟩
      · exact ⟨y, List.mem_append_right _ (by simpa [Gc, comps] using hy), hgy⟩
    · have := comps_mu hbot hcb hge hslt (le_of_lt h1) h2 hμu g hg
      exact ⟨g, List.mem_append_left _ (hin g this), le_refl _⟩
    · simp at hg

/-- **A seed `ψ_μ(σ)` with `σ ≤ b[0]` whose components (below `a`) are at most `b[0]` is good.** -/
theorem seedOK_of_comps {a b μ σ : T} (hot : isOT (psi a b z) = true) (hcb : cof b = .big μ)
    (hμ : ¬ lt μ a = true) (hsot : isOT (psi μ σ z) = true) (hσ : σ ≤ fs b z)
    (hcs : ∀ u, ¬ lt a u = true → ∀ g ∈ comps u σ, g ≤ fs b z) :
    SeedOK a b μ (psi μ σ z) := by
  have hbot : isOT b = true := isOT_arg hot
  have hcomp := comps_lt hot
  have hsz : z < psi μ σ z := T.z_lt_psi _ _ _
  have hmono : fs b z < fs b (psi μ σ z) := fs_mono hcb hsz
  have hσlt : σ < fs b (psi μ σ z) := lt_of_le_of_lt hσ hmono
  have hslt : psi μ σ z < psi (succ μ) z z := by
    rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ)
  have hval : ValidLt b (psi μ σ z) := by unfold ValidLt; rw [hcb]; exact hslt
  have hfsle : fs b (psi μ σ z) ≤ b := le_of_lt (fs_lt hval)
  have hge : psi μ z z ≤ psi μ σ z := by
    rw [le_iff]
    rcases (le_iff _ _).mp (z_le σ) with h4 | h4
    · left; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h4⟩
    · right; rw [← h4]
  have haa : ¬ lt a a = true := by simp [Bool.eq_false_iff.mpr (lt_irrefl' _)]
  refine ⟨hsot, hslt, ?_, ?_, ?_⟩
  · rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hσlt⟩
  · intro g hg
    simp only [comps, hμ, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    rcases hg with (rfl | hg | hg) | hg
    · exact hσlt
    · exact lt_of_le_of_lt (hcs a haa g hg) hmono
    · have hgb : g ∈ comps a b := comps_mu hbot hcb hge hslt hfsle (le_refl b) hμ g hg
      have hgb' := hcomp g hgb
      by_contra hcon
      have hgy : g ∈ comps a g := comps_mu hbot hcb hge hslt (le_of_not_gt hcon) (le_of_lt hgb') hμ g hg
      exact Nat.lt_irrefl _ (size_comps hgy)
    · simp at hg
  · intro u c0 c1 h1 h2 hau g hg
    have hμu : ¬ lt μ u = true := fun h => hau (show a < u from lt_of_le_of_lt (le_of_not_gt hμ) h)
    have hin : ∀ w ∈ comps u c0, w ∈ comps u (psi a c0 c1) := fun w hw => mem_comps_psi_arg hau hw
    have hc0in : c0 ∈ comps u (psi a c0 c1) := by simp [comps, hau]
    simp only [comps, hμu, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    rcases hg with (rfl | hg | hg) | hg
    · exact ⟨c0, List.mem_append_left _ hc0in, le_of_lt (lt_trans hσlt h1)⟩
    · exact ⟨c0, List.mem_append_left _ hc0in,
        le_of_lt (lt_of_le_of_lt (hcs u hau g hg) (lt_trans hmono h1))⟩
    · have := comps_mu hbot hcb hge hslt (le_of_lt h1) h2 hμu g hg
      exact ⟨g, List.mem_append_left _ (hin g this), le_refl _⟩
    · simp at hg

/-! ## 自然数型の項（一番深い位置が後続） -/

theorem last_mem_of : ∀ {t : T}, t ≠ z → last t ∈ summands t
  | z, h => absurd rfl h
  | psi a b z, _ => by simp [last, summands]
  | psi a b (psi c d e), _ => by
    show last (psi c d e) ∈ psi a b z :: summands (psi c d e)
    exact List.mem_cons_of_mem _ (last_mem_of (by simp))

/-- The deepest position of `t` is a successor argument. -/
inductive SuccPath : T → Prop
  | base {v b : T} : b ≠ z → isSucc b = true → SuccPath (psi v b z)
  | rest {a b c d e : T} : SuccPath (psi c d e) → SuccPath (psi a b (psi c d e))
  | arg {a b : T} : b ≠ z → isSucc b = false → SuccPath b → SuccPath (psi a b z)

theorem SuccPath.cof {t : T} (h : SuccPath t) : cof t = .omega := by
  induction h with
  | base hb hs => simp [_root_.Ytosk.cof, hb, hs]
  | rest _ ih => simp [_root_.Ytosk.cof] at *; exact ih
  | arg hb hs _ ih => simp [_root_.Ytosk.cof, hb, hs, ih]

/-- **On a successor-type term, `fsD` is `fs`.** -/
theorem SuccPath.fsD_eq {t : T} (h : SuccPath t) (η : T) : fsD t η = fs t η := by
  induction h with
  | base hb hs =>
    conv => lhs; unfold fsD
    conv => rhs; unfold fs
    rw [if_neg hb, if_neg hb, if_pos hs, if_pos hs]
  | @rest a b c d e _ ih =>
    show psi a b (fsD (psi c d e) η) = psi a b (fs (psi c d e) η)
    rw [ih]
  | @arg a b hb hs hp ih =>
    rw [fsD_psi hb hs]
    conv => rhs; unfold fs
    rw [if_neg hb, if_neg (by rw [hs]; simp), hp.cof]
    simp only
    rw [ih]

theorem SuccPath.append {t : T} : ∀ (B : T), SuccPath t → SuccPath (app B t)
  | z, h => by simpa using h
  | psi a1 b1 B', h => by
    simp only [app_psi]
    have hne : t ≠ z := by cases h <;> simp
    cases hB : app B' t with
    | z => exact absurd (app_eq_z hB).2 hne
    | psi d e f =>
      have := SuccPath.append B' h
      rw [hB] at this
      exact SuccPath.rest this

theorem SuccPath.not_succ {t : T} (h : SuccPath t) : isSucc t = false := by
  induction h with
  | base hb _ =>
    simp only [isSucc, last, beq_eq_false_iff_ne]
    intro h; simp [one] at h; exact hb h.2
  | rest _ ih => rw [isSucc_psi_rest _ _ _ (by simp)]; exact ih
  | arg hb _ _ _ =>
    simp only [isSucc, last, beq_eq_false_iff_ne]
    intro h; simp [one] at h; exact hb h.2

/-- **A successor-type child keeps the node successor-type after one step.** -/
theorem SuccPath.step {a b s y : T} (hc : isOT (psi s y z) = true) (hp : SuccPath (psi s y z)) :
    SuccPath (step a b s y z) := by
  rcases step_cases (a := a) (b := b) hc with ⟨B, hB⟩ | ⟨h1, hlo, h3, _⟩
  · rw [hB]; exact SuccPath.append B hp
  · rw [h1]
    cases hp with
    | base _ hs =>
      exfalso
      -- a successor argument has a lower part (the final `1`)
      have hge := split_fst_ge (psi (succ s) z z) y
      have hbpl := split_app (psi (succ s) z z) y
      rw [hlo, app_z_right] at hbpl
      have h1y : last y = one := by unfold isSucc at hs; simpa using hs
      have hmem : one ∈ summands y := by rw [← h1y]; exact last_mem_of h3
      rw [← hbpl] at hmem
      apply hge _ hmem
      show psi z z z < _; rw [psi_lt_psi_z_iff]; left
      exact lt_of_le_of_lt (z_le s) (lt_succ_self s)
    | arg _ _ hy => exact hy

theorem mulT_lt_succ {x : T} (hx : ∃ s y, x = psi s y z) : ∀ k, mulT x k < mulT x (k + 1)
  | 0 => by obtain ⟨s, y, rfl⟩ := hx; exact T.z_lt_psi _ _ _
  | k + 1 => by
    show app x (mulT x k) < app x (mulT x (k + 1))
    exact (app_lt_app_left_iff x).mpr (mulT_lt_succ hx k)

/-- **On a successor-type term, the fundamental sequence is increasing.** -/
theorem SuccPath.fs_mono_nat {t : T} (h : SuccPath t) (k : Nat) :
    fs t (natT k) < fs t (natT (k + 1)) := by
  induction h with
  | @base v b hb hs =>
    conv => lhs; unfold fs
    conv => rhs; unfold fs
    rw [if_neg hb, if_neg hb, if_pos hs, if_pos hs, count_natT, count_natT]
    exact mulT_lt_succ ⟨_, _, rfl⟩ k
  | @rest a b c d e _ ih =>
    show psi a b (fs (psi c d e) (natT k)) < psi a b (fs (psi c d e) (natT (k + 1)))
    rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, ih⟩)
  | @arg a b hb hs hp ih =>
    conv => lhs; unfold fs
    conv => rhs; unfold fs
    rw [if_neg hb, if_neg hb, if_neg (by rw [hs]; simp), if_neg (by rw [hs]; simp), hp.cof]
    simp only
    rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, ih⟩

theorem SuccPath.fs_mono_nat' {t : T} (h : SuccPath t) : ∀ {k m : Nat}, k < m →
    fs t (natT k) < fs t (natT m)
  | k, 0, hkm => absurd hkm (Nat.not_lt_zero _)
  | k, m + 1, hkm => by
    rcases Nat.lt_or_ge k m with h1 | h1
    · exact lt_trans (h.fs_mono_nat' h1) (h.fs_mono_nat m)
    · have : k = m := by omega
      subst this; exact h.fs_mono_nat k

end Ytosk
