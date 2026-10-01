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

end Ytosk
