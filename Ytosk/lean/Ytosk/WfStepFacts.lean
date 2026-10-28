/-
HUACStep from danger-free chain facts.

Frame: `n` upgrades to the ancestor `k` (`k < n`), `m = P0 k = P1 n`, `W = bumpW k`,
`j` = last bump child of `k`, `c` = first child of `j`, `a` = the row-1 ancestor of `m`
at the row-1 level of `c`.  Along the row-1 chain from `a` (exclusive) to `m`
(inclusive) every column `y` adds the increment `1` (no upgrade), `ω` (upgrade to a
target without bump child, a *w-step*) or `last v(t)` (upgrade to a target with a bump
child, a *B-step*).

`StepFacts` (no `Danger` in it) asks, when `lev W ≠ 0`:
  (LK) the last bump child `j` has a child `c`;
  (A)  a B-step increment is `≥ W`;
  (B)  no w-step lies row-1 below a B-step;
  (II) if some chain column in `(a, m]` upgrades, `v(a)` has a level-0 component `≥ 1`.

Proved here: (A) ∧ (B) and a B-step leave no dangerous summand in `v(m)`
(`noDanger_of_B`), so under `Danger` every upgrade target in `(a, m]` has no bump child,
and with (II) `stepDom_of_noBump` gives `StepDom`.  Hence `StepFacts → HUACStep`.
-/
import Ytosk.WfHUAC2Canon

namespace Ytosk.WfStepFacts
open T
open WfHUACDeep

/-- Summands of `V + X`: those of `X`, and those of `V` not below the head of `X`. -/
theorem summands_add_gen : ∀ (V X : T), ∀ q ∈ summands (add V X),
    q ∈ summands X ∨ (q ∈ summands V ∧ ¬ q < head X)
  | z, X, q, hq => Or.inl (by simpa [add] using hq)
  | psi a b c, z, q, hq => by
    refine Or.inr ⟨by simpa [add] using hq, ?_⟩
    intro h
    change lt q (head z) = true at h
    cases q <;> simp [head, lt] at h
  | psi a b c, psi d e f, q, hq => by
    rw [add_psi_psi] at hq
    split at hq
    · exact Or.inl hq
    · rename_i hn
      simp only [summands, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact Or.inr ⟨by simp [summands], by simpa [head] using hn⟩
      · rcases summands_add_gen c (psi d e f) q hq with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨by simp [summands, h1], h2⟩

theorem summands_last : ∀ {t q : T}, q ∈ summands (last t) → q = last t
  | z, q, h => by simp [last, summands] at h
  | psi a b z, q, h => by simpa [last, summands] using h
  | psi a b (psi d e f), q, h => by
    have : last (psi a b (psi d e f)) = last (psi d e f) := rfl
    rw [this] at h ⊢
    exact summands_last h

theorem head_last : ∀ t : T, head (last t) = last t
  | z => rfl
  | psi a b z => rfl
  | psi a b (psi d e f) => by
    have : last (psi a b (psi d e f)) = last (psi d e f) := rfl
    rw [this]; exact head_last _

/-- `t` has a bump child. -/
def HasBump (M : Mat) (t : Nat) : Prop := ∃ d ∈ children M t, col M d = bump M t

theorem up1_cases {M : Mat} {b x : Nat} (h : Up1 M b x) :
    b = x ∨ ∃ y, par M 1 x = some y ∧ Up1 M b y := by
  cases h with
  | refl => exact Or.inl rfl
  | step hp hA => exact Or.inr ⟨_, hp, hA⟩

theorem up1_antisymm {M : Mat} {a y : Nat} (h1 : Up1 M a y) (h2 : Up1 M y a) : y = a := by
  have := up1_le h1; have := up1_le h2; omega

/-- **No dangerous summand above a B-step.**  If (A) and (B) hold on the chain from `a`
to `x` and some column of `(a, x]` is a B-step, no summand of `v(x)` below `W` has a
nonzero level-0 component. -/
theorem noDanger_of_B {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {W : T} {a x : Nat} (hA : Up1 M a x) (hxN : x < M.length) (hx2 : entry M 2 x = 0)
    (hAst : ∀ y t, Up1 M a y → Up1 M y x → y ≠ a → upg M y = some t → HasBump M t →
      W ≤ last (ρ.v t))
    (hBst : ∀ y1 y2 t1 t2, Up1 M a y1 → Up1 M y1 y2 → Up1 M y2 x → y1 ≠ a → y2 ≠ y1 →
      upg M y1 = some t1 → HasBump M t1 → upg M y2 = some t2 → ¬ HasBump M t2 → False)
    (hB : ∃ y t, Up1 M a y ∧ Up1 M y x ∧ y ≠ a ∧ upg M y = some t ∧ HasBump M t) :
    ∀ q ∈ summands (ρ.v x), q < W → ∀ g ∈ comps z q, g = z := by
  induction hA with
  | refl =>
    obtain ⟨y, t, h1, h2, hne, _, _⟩ := hB
    exact absurd (up1_antisymm h1 h2) hne
  | @step x y hp hA ih =>
    have hyx := par_lt M 1 x y hp
    have hy2 : entry M 2 y = 0 := by
      have := par1_e2_ne_one S.z1c hp
      have := S.z2 y
      omega
    have hay := up1_le hA
    have hxa : x ≠ a := by omega
    have h1 : entry M 1 x ≠ 0 := by have := par1_entry_lt hp; omega
    have hpOT := vOpt_ot hG hxN
    rw [hp] at hpOT
    simp only [vOpt] at hpOT
    -- restrictions of the chain facts to `y`
    have hAst' : ∀ y' t, Up1 M a y' → Up1 M y' y → y' ≠ a → upg M y' = some t →
        HasBump M t → W ≤ last (ρ.v t) :=
      fun y' t h1 h2 hne hu hb => hAst y' t h1 (Up1.step hp h2) hne hu hb
    have hBst' : ∀ y1 y2 t1 t2, Up1 M a y1 → Up1 M y1 y2 → Up1 M y2 y → y1 ≠ a → y2 ≠ y1 →
        upg M y1 = some t1 → HasBump M t1 → upg M y2 = some t2 → ¬ HasBump M t2 → False :=
      fun y1 y2 t1 t2 h1 h2 h3 => hBst y1 y2 t1 t2 h1 h2 (Up1.step hp h3)
    -- a B-step strictly above `x` lies in `(a, y]`
    have hBy : ∀ y0 t0, Up1 M a y0 → Up1 M y0 x → y0 ≠ a → upg M y0 = some t0 →
        HasBump M t0 → y0 ≠ x → Up1 M y0 y := by
      intro y0 t0 _ h2 _ _ _ hne
      rcases up1_cases h2 with h | ⟨y', hp', hA'⟩
      · exact absurd h hne
      · rw [hp] at hp'; cases hp'; exact hA'
    have ihy := fun hB' => ih (by omega) hy2 hAst' hBst' hB'
    rw [(hC x hxN).2]
    unfold vRhs
    rw [if_neg h1, if_pos hx2, hp]
    simp only [vOpt]
    obtain ⟨y0, t0, hy0a, hy0x, hy0ne, hu0, hb0⟩ := hB
    cases hu : upg M x with
    | none =>
      rw [sf_ot (isOT_add hpOT isOT_one)]
      have hy0 : y0 ≠ x := by intro h; subst h; rw [hu] at hu0; cases hu0
      have ihy' := ihy ⟨y0, t0, hy0a, hBy y0 t0 hy0a hy0x hy0ne hu0 hb0 hy0, hy0ne, hu0, hb0⟩
      intro q hq hqW g hg
      rcases summands_add_gen _ _ q hq with hq | ⟨hq, _⟩
      · have : q = one := by simpa [one, summands] using hq
        subst this
        exact comps_one_eq hg
      · exact ihy' q hq hqW g hg
    | some t =>
      rw [sf_ot (isOT_add hpOT (isOT_last (hG.ot_v t (upg_lt hxN hu))))]
      by_cases hbt : HasBump M t
      · have hWL : W ≤ last (ρ.v t) := hAst x t (Up1.step hp hA) (Up1.refl x) hxa hu hbt
        intro q hq hqW
        exfalso
        rcases summands_add_gen _ _ q hq with hq | ⟨_, hq⟩
        · rw [summands_last hq] at hqW
          exact absurd (lt_of_lt_of_le hqW hWL) (lt_irrefl _)
        · rw [head_last] at hq
          exact hq (lt_of_lt_of_le hqW hWL)
      · exfalso
        have hy0 : y0 ≠ x := by
          intro h; subst h; rw [hu] at hu0; cases hu0; exact hbt hb0
        exact hBst y0 x t0 t hy0a hy0x (Up1.refl x) hy0ne (Ne.symm hy0) hu0 hb0 hu hbt

/-- **Residual (danger-free chain facts).** -/
def StepFacts : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ →
    ∀ n k m, upg N n = some k → k < n → par N 0 k = some m →
      lev (bumpW N σ k) ≠ z →
      ∃ L j R c C, children N k = L ++ j :: R ∧ col N j = bump N k ∧
        (∀ d ∈ R, col N d ≠ bump N k) ∧ children N j = c :: C ∧
        ∀ a, Up1 N a m → entry N 1 a = entry N 1 c →
          -- (A) a B-step increment is at least `W`
          (∀ y t, Up1 N a y → Up1 N y m → y ≠ a → upg N y = some t → HasBump N t →
            bumpW N σ k ≤ last (σ.v t)) ∧
          -- (B) no w-step row-1 below a B-step
          (∀ y1 y2 t1 t2, Up1 N a y1 → Up1 N y1 y2 → Up1 N y2 m → y1 ≠ a → y2 ≠ y1 →
            upg N y1 = some t1 → HasBump N t1 → upg N y2 = some t2 → ¬ HasBump N t2 → False) ∧
          -- (II) an upgrade in `(a, m]` gives `v(a)` a level-0 component `≥ 1`
          ((∃ y t, Up1 N a y ∧ Up1 N y m ∧ y ≠ a ∧ upg N y = some t) →
            ∃ g ∈ comps z (σ.v a), one ≤ g)

/-- **Bridge**: `StepFacts → HUACStep`. -/
theorem hUACStep_of_facts (hF : StepFacts) : WfHUAC2Canon.HUACStep := by
  intro N σ rk hN hNe hC hR hG n k m hu hkn hkm hdg
  by_cases hlev : lev (bumpW N σ k) = z
  · exact Or.inl hlev
  right
  obtain ⟨L, j, R, c, C, hL, hjb, hR', hCc, hfa⟩ := hF N σ rk hN hNe hC hR hG n k m hu hkn hkm hlev
  refine ⟨L, j, R, c, C, hL, hjb, hR', hCc, ?_⟩
  intro a ha hae
  obtain ⟨hAst, hBst, hII⟩ := hfa a ha hae
  have S := sInv_std hN hNe
  have hn : n < N.length := by have := upg_succ_lt hu; omega
  obtain ⟨m', hm', _, hcol, _⟩ := upg_spec hu
  obtain ⟨m'', hm'', hk0⟩ := upg_target_par0 S.r0p hu
  rw [hkm] at hk0; cases hk0
  rw [hm'] at hm''; cases hm''
  have hmN : m < N.length := by
    have := par_lt N 0 k m hkm
    have := upg_lt hn hu
    omega
  have hm2 : entry N 2 m = 0 := by have := e2_of_col hcol; have := S.z2 k; omega
  -- under danger there is no B-step in `(a, m]`
  have hnoB : ∀ y, Up1 N a y → Up1 N y m → y ≠ a → ∀ t, upg N y = some t →
      ∀ d ∈ children N t, col N d ≠ bump N t := by
    intro y h1 h2 hne t ht d hd hdb
    obtain ⟨q, hq, hqW, g, hg, hgz⟩ := hdg
    rw [hm'] at hq
    simp only [vOpt] at hq
    exact hgz (noDanger_of_B S hC hG ha hmN hm2 hAst hBst ⟨y, t, h1, h2, hne, ht, d, hd, hdb⟩
      q hq hqW g hg)
  by_cases hU : ∃ y t, Up1 N a y ∧ Up1 N y m ∧ y ≠ a ∧ upg N y = some t
  · exact stepDom_of_noBump S hC hG hmN hnoB (hII hU)
  · intro y h1 h2 hne t ht
    exact absurd ⟨y, t, h1, h2, hne, ht⟩ hU

/-- HUAC from the danger-free chain facts. -/
theorem hUAC_of_facts (hF : StepFacts) : HUAC :=
  WfHUAC2Canon.hUAC_of_step (hUACStep_of_facts hF)

end Ytosk.WfStepFacts
