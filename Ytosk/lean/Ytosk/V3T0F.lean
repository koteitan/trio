/-
**3 行・t = 0: g の o の枠（種 S1）。**

r が g で数えられるとき、N での g の子の値は M の子の値 Lc のあとに ψ_v(Y0)（中間のコピーの根）が m 個、
最後に ρ′.o(r)（M.take x での r の値）が並ぶ。M では Lc のあとに ψ_v(Y0 + 1)（= o_M(r)）。
- m ≥ 1: 最初の ψ_v(Y0) のあとは書き換えが起きない（`no_rw_after`）ので、最後の子 ρ′.o(r) ⊴ ψ_v(Y0)
  の枠（`node_lhd`）で ψ_v(Y0) を m + 1 個並べた値以下。それは o_M(g) の基本列の項 o_M(g)[k]
  （2 行の `t0_frame_notrig`・`t0_frame_trig`・`t0_frame_swallow`）で、Buchholz 氏の ◁ で o_M(g) より下。
- m = 0: 最後の子 ρ′.o(r) ◁ o_M(r) の 1 枠。
-/
import Ytosk.V3T0D

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem app_assoc' : ∀ (x y w : T), app (app x y) w = app x (app y w)
  | z, _, _ => rfl
  | psi a b c, y, w => by simp only [app_psi]; rw [app_assoc' c y w]

theorem mulT_succ' (t : T) : ∀ n, mulT t (n + 1) = app (mulT t n) t
  | 0 => by simp [mulT]
  | n + 1 => by
    show app t (mulT t (n + 1)) = app (app t (mulT t n)) t
    rw [mulT_succ' t n, app_assoc']

/-- `cof` is `0` only at `0`, and a successor only for a successor. -/
theorem cof_props : ∀ t : T, (cof t = .zero → t = z) ∧ (cof t = .succ → isSucc t = true)
  | z => ⟨fun _ => rfl, fun h => by simp [cof] at h⟩
  | psi a b (psi c d e) => by
    have ih := cof_props (psi c d e)
    refine ⟨fun h => absurd (ih.1 (by simpa [cof] using h)) (by simp), fun h => ?_⟩
    have := ih.2 (by simpa [cof] using h)
    simpa [isSucc, last] using this
  | psi a b z => by
    have iha := cof_props a
    have ihb := cof_props b
    by_cases hb : b = z
    · subst hb
      by_cases ha : a = z
      · subst ha
        refine ⟨fun h => by simp [cof] at h, fun _ => ?_⟩
        simp [isSucc, last, one]
      · by_cases hs : isSucc a = true
        · refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp [cof, ha, hs] at h
        · refine ⟨fun h => ?_, fun h => ?_⟩
          · simp only [cof, if_pos, if_neg ha, if_neg hs] at h
            exact absurd (iha.1 h) ha
          · simp only [cof, if_pos, if_neg ha, if_neg hs] at h
            exact absurd (iha.2 h) hs
    · by_cases hs : isSucc b = true
      · refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp [cof, hb, hs] at h
      · refine ⟨fun h => ?_, fun h => ?_⟩
        · cases hc : cof b with
          | zero => exact absurd (ihb.1 hc) hb
          | big μ =>
            simp only [cof, if_neg hb, if_neg hs, hc] at h
            split at h <;> cases h
          | succ => simp [cof, hb, hs, hc] at h
          | omega => simp [cof, hb, hs, hc] at h
        · cases hc : cof b with
          | succ => exact absurd (ihb.2 hc) hs
          | big μ =>
            simp only [cof, if_neg hb, if_neg hs, hc] at h
            split at h <;> cases h
          | zero => simp [cof, hb, hs, hc] at h
          | omega => simp [cof, hb, hs, hc] at h

theorem natT_lt_om (μ : T) : ∀ k, natT k < psi (succ μ) z z
  | 0 => T.z_lt_psi _ _ _
  | k + 1 => by
    show psi z z (natT k) < psi (succ μ) z z
    rw [psi_lt_psi]
    exact Or.inl (lt_of_le_of_ne (z_le _) (Ne.symm (succ_ne_z μ)))

/-- **Every natural index is valid** for a `ψ` with a nonzero argument. -/
theorem validLt_natT {a b : T} (hb : b ≠ z) (k : Nat) : ValidLt (psi a b z) (natT k) := by
  have h := cof_props (psi a b z)
  unfold ValidLt
  cases hc : cof (psi a b z) with
  | zero => exact absurd (h.1 hc) (by simp)
  | succ =>
    exfalso
    have := h.2 hc
    simp only [isSucc, last, beq_iff_eq, one, psi.injEq] at this
    exact hb this.2.1
  | omega => trivial
  | big μ => exact natT_lt_om μ k

/-- `◁` with a natural index is `◁` with index `0`. -/
theorem lhd_natT_z {k : Nat} {b a : T} (h : Lhd (natT k) b a) : Lhd z b a := by
  refine ⟨h.1, fun u c h1 h2 x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := h.2 u c h1 h2 x hx
  rcases List.mem_append.mp hy with hy | hy
  · exact ⟨y, List.mem_append_left _ hy, hxy⟩
  · have hyz : y = z := by
      simp only [Gc, List.mem_cons] at hy
      rcases hy with hy | hy
      · exact hy
      · exact comps_natT k y hy
    exact ⟨y, List.mem_append_right _ (by simp [Gc, hyz]), hxy⟩

theorem lt_app_one (Y : T) : Y < app Y one := by
  have := app_lt_app_left Y (show z < one from T.z_lt_psi _ _ _)
  rwa [app_z_right] at this

/-- **No rewrite after the first copy**: once `ψ_v(Y0)` has been appended, `Y0` is at most the state. -/
theorem no_rw_after {a B v Y0 : T} (hO : isOT (psi v Y0 z) = true) {m : Nat} (hm : 1 ≤ m) :
    ¬ (lt (spArg a B (mulT (psi v Y0 z) m)) Y0 = true ∧ lt (psi a z z) (psi v Y0 z) = true) := by
  rintro ⟨h1, h2⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have e : spArg a B (mulT (psi v Y0 z) (m' + 1)) =
      spArg a (step a B v Y0 z) (mulT (psi v Y0 z) m') := by
    show spArg a B (app (psi v Y0 z) (mulT (psi v Y0 z) m')) = _
    rw [app_psi, app_z, spArg_cons, step_rest a B v Y0 _ z]
  rw [e] at h1
  have hle1 : Y0 ≤ step a B v Y0 z := by
    unfold step
    split_ifs with ht
    · exact le_H hO
    · have hB : ¬ lt B Y0 = true := fun h => ht ⟨h, h2⟩
      have hBY : Y0 ≤ B := by
        rcases lt_or_ge B Y0 with h | h
        · exact absurd h hB
        · exact h
      exact le_trans hBY (le_of_lt (by
        have := add_lt_add_left B (T.z_lt_psi v Y0 z); rwa [add_z_right] at this))
  have hle2 := le_spArg a (mulT (psi v Y0 z) m') (step a B v Y0 z) (isOT_mulT hO ⟨_, _, rfl⟩ m')
  exact absurd (lt_of_lt_of_le (show _ < Y0 from h1) (le_trans hle1 hle2)) (lt_irrefl' _)

/-- **The core of the `g` frame** (`t = 0`): the children `ψ_v(Y0)` × m and then `X′ ◁ ψ_v(Y0 + 1)`
against the single child `ψ_v(Y0 + 1)`. -/
theorem s1_core {a B v Y0 X' : T} {m : Nat}
    (hOld : isOT (psi a (spArg a B (psi v (app Y0 one) z)) z) = true)
    (hX : isOT (psi v (app Y0 one) z) = true) (hO : isOT (psi v Y0 z) = true)
    (hBX : ∀ q ∈ summands B, psi v (app Y0 one) z ≤ q)
    (hX' : Single X') (hl : Lhd z X' (psi v (app Y0 one) z))
    (hX'O : 1 ≤ m → X' ≤ psi v Y0 z)
    (hy' : ∀ s' y', X' = psi s' y' z → s' ≠ v → y' = z)
    (hsub : lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true → SubSmall a v)
    (hsub0 : ∀ s' y', X' = psi s' y' z → s' ≠ v →
      lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true → SubSmall a s')
    (hcl : lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true → Closed a B) :
    Lhd z (psi a (spArg a (spArg a B (mulT (psi v Y0 z) m)) X') z)
      (psi a (spArg a B (psi v (app Y0 one) z)) z) := by
  obtain ⟨s', y', rfl⟩ := hX'.2
  have hc' := hX'.1
  have hOX : psi v Y0 z < psi v (app Y0 one) z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one Y0⟩)
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    simp only [mulT]
    show Lhd z (psi a (spArg a B (psi s' y' z)) z) (psi a (spArg a B (psi v (app Y0 one) z)) z)
    rw [spArg_single, spArg_single]
    have hsub' : (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) ∨
        (lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true) → SubSmall a s' := by
      intro hrw
      by_cases hs : s' = v
      · subst hs
        apply hsub
        rcases hrw with hn | ho
        · have hle : psi s' y' z ≤ psi s' (app Y0 one) z := le_of_lt hl.1
          have hyy : y' ≤ app Y0 one := by
            rcases (le_iff _ _).mp hle with h | h
            · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
              · exact absurd h (lt_irrefl' _)
              · exact le_of_lt h
            · simp only [psi.injEq] at h; rw [h.2.1]
          exact ⟨lt_of_lt_of_le hn.1 hyy, lt_of_lt_of_le hn.2 hle⟩
        · exact ho
      · have hyz := hy' s' y' rfl hs
        rcases hrw with hn | ho
        · exfalso; have := hn.1; rw [hyz] at this; exact T.not_lt_z _ this
        · exact hsub0 s' y' rfl hs ho
    have hE := node_lhd hX hc' (Or.inr hl) hBX hsub hsub' (fun _ hr => hcl hr)
    apply lhd_of_lhdE_lt hE
    apply psi_lt_psi_z_iff.mpr; right; refine ⟨rfl, ?_⟩
    apply step_lt hX hc' (Or.inl hl) hBX
    · intro ht' hss
      exfalso
      have hyz := hy' s' y' rfl (ne_of_lt hss)
      have := ht'.1; rw [hyz] at this; exact T.not_lt_z _ this
    · intro h; exfalso; have := lt_app_one Y0; rw [h] at this; exact T.not_lt_z _ this
  · -- `m ≥ 1`
    set O := psi v Y0 z with hOdef
    set B' := spArg a B (mulT O m) with hB'
    have hnr := no_rw_after (a := a) (B := B) hO hm
    rw [← hOdef, ← hB'] at hnr
    have hB'O : ∀ q ∈ summands B', O ≤ q :=
      spArg_summands_ge ⟨v, Y0, rfl⟩ (mulT O m) B (isOT_mulT hO ⟨_, _, rfl⟩ m)
        (fun q hq => by rw [summands_mulT ⟨_, _, rfl⟩ m q hq])
        (fun q hq => le_trans (le_of_lt hOX) (hBX q hq))
    -- the middle value: `m + 1` copies
    have hMid : spArg a B (mulT O (m + 1)) = step a B' v Y0 z := by
      rw [mulT_succ', spArg_app, hOdef, spArg_single]
    -- (i) the last child against `ψ_v(Y0)`
    have hNM : LhdE (psi a (step a B' s' y' z) z) (psi a (step a B' v Y0 z) z) := by
      by_cases heq : psi s' y' z = O
      · rw [hOdef] at heq; simp only [psi.injEq] at heq; rw [heq.1, heq.2.1]; exact Or.inl rfl
      · have hlt' : psi s' y' z < O := lt_of_le_of_ne (hX'O hm) heq
        have hlO : Lhd z (psi s' y' z) O := lhd_restrict hl hlt' (le_of_lt hOX)
        have hnew : ¬ (lt B' y' = true ∧ lt (psi a z z) (psi s' y' z) = true) := by
          rintro ⟨h1, h2⟩
          by_cases hs : s' = v
          · subst hs
            have hyy : y' ≤ Y0 := by
              rcases psi_lt_psi_z_iff.mp hlt' with h | ⟨_, h⟩
              · exact absurd h (lt_irrefl' _)
              · exact le_of_lt h
            exact hnr ⟨lt_of_lt_of_le h1 hyy, lt_trans h2 hlt'⟩
          · have := hy' s' y' rfl hs
            rw [this] at h1; exact T.not_lt_z _ h1
        exact node_lhd hO hc' (Or.inr hlO) hB'O (fun h => absurd h hnr)
          (fun h => by rcases h with h | h
                       · exact absurd h hnew
                       · exact absurd h hnr)
          (fun _ h => absurd h hnr)
    -- (ii) the middle value is a term of the fundamental sequence of the old value
    have hArg : spArg a B (psi v (app Y0 one) z) ≠ z := by
      intro h
      have := lt_spArg a (b := B) hX (by simp)
      rw [h] at this; exact T.not_lt_z _ this
    have hfsM : ∃ k, psi a (spArg a B (mulT O (m + 1))) z =
        fs (psi a (spArg a B (psi v (app Y0 one) z)) z) (natT k) := by
      by_cases htr : lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true
      · by_cases hbad : lt B Y0 = true ∧ (split Y0 (psi (succ v) z z)).2 = z
        · refine ⟨m, ?_⟩
          have := t0_frame_swallow (n := m + 1) (by omega) hX hO htr hbad.1 hbad.2
          rw [show m + 1 - 1 = m by omega] at this
          exact this.symm
        · exact ⟨m + 1, (t0_frame_trig (n := m + 1) (by omega) hOld hX hO htr hbad).symm⟩
      · have hXapp : isOT (app B (psi v (app Y0 one) z)) = true := by
          have h1 := isOT_arg hOld
          rw [spArg_single] at h1; unfold step at h1
          rw [if_neg htr, add_eq_app_of_ge ⟨_, _, rfl⟩ _ hBX] at h1
          exact h1
        exact ⟨m + 1, (t0_frame_notrig (m + 1) hXapp htr hBX).symm⟩
    obtain ⟨k, hk⟩ := hfsM
    have hlM : Lhd z (psi a (spArg a B (mulT O (m + 1))) z)
        (psi a (spArg a B (psi v (app Y0 one) z)) z) := by
      rw [hk]; exact lhd_natT_z (lhd_fs hOld (validLt_natT hArg k))
    rw [hMid] at hlM
    have hnew : spArg a B' (psi s' y' z) = step a B' s' y' z := spArg_single _ _ _ _
    rw [hnew]
    exact lhd_of_lhdE_lt (LhdE.trans hNM (Or.inr hlM)) (lt_of_le_of_lt hNM.le hlM.1)

theorem sumN_replicate {O : T} (hO : Single O) : ∀ m, sumN (List.replicate m O) = mulT O m
  | 0 => rfl
  | m + 1 => by
    rw [List.replicate_succ, sumN_cons_dec (fun u hu => by
        rcases List.mem_cons.mp hu with h | h
        · rw [h]; exact hO
        · rw [(List.mem_replicate.mp h).2]; exact hO)
      (List.pairwise_cons.mpr ⟨fun b hb => by rw [(List.mem_replicate.mp hb).2],
        List.pairwise_replicate.mpr (Or.inr (le_refl _))⟩), sumN_replicate hO m]
    rfl

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : Good3 (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

/-- **`o(x) = 1`** and `x` counts at `r`. -/
theorem o_x_one : ρ.o (r + L) = one := by
  have hxl : r + L < M.length := by omega
  rw [o_of_no_counted hC hxl (hG.ot_v _ hxl) (fun c hc => by have := mem_children hc; omega),
    v_z_of_e1 hC hxl he1]
  rfl

/-- **`o_M(r) = ψ_v(Y0 + 1)` and `omid = ψ_v(Y0)`** with `Y0` the state of `r` without `x`. -/
theorem o_r_omid :
    ρ.o r = psi (ρ.v r) (app (spArg (ρ.v r) z
      (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r)))) one) z ∧
    omid M r L ρ = psi (ρ.v r) (spArg (ρ.v r) z
      (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r)))) z := by
  have hrM : r < M.length := by omega
  have hvot := hG.ot_v r hrM
  set F := (children M r).filter (fun c => decide (c < r + L)) with hF
  have hFot : ∀ t ∈ F.map (cnt M ρ r), isOT t = true := by
    intro t ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    exact isOT_cnt hG (mem_children (List.mem_filter.mp hc).1).2
  have hS := isOT_sumN _ hFot
  set S := sumN (F.map (cnt M ρ r)) with hSdef
  refine ⟨?_, sf_psi_spArg hvot hS⟩
  have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
  have hcx : cnt M ρ r (r + L) = one := by
    unfold cnt
    rw [if_neg (by
      intro h
      have : entry M 2 (r + L) = (col M (r + L)).2.2 := rfl
      rw [this, h] at he2; simp [bump] at he2), if_neg (by rw [isUpg_x0 hlen hL hp he2]; simp)]
    exact o_x_one hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN
  rw [(hC r hrM).1]
  unfold oRhs
  rw [children_split_x (x := r + L) hlen hxr, List.map_append, List.map_singleton, hcx, ← hF,
    sumN_snoc, ← hSdef, sf_ot (isOT_add hS rfl), add_one_eq_app,
    sf_psi_spArg hvot (show isOT (app S one) = true from isOT_succ hS), spArg_app]
  congr 2
  show spArg (ρ.v r) (spArg (ρ.v r) z S) (psi z z z) = _
  rw [spArg_single, step_leaf]
  exact add_one_eq_app _

/-- **Seed S1**: when `r` counts at its parent `g`, `o(g)` drops by `◁` in `N`. -/
theorem t0_S1 {g : Nat} (hg : par M 0 r = some g) {ρ' : Valn} (hcnt : Counted M g r)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ)
    (hσG : ∀ c, c < r → ¬ DepX M (r + L) true c → σ.o c = ρ.o c)
    (hσvg : σ.v g = ρ.v g)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hl : Lhd z (ρ'.o r) (ρ.o r))
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hVr : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → ∀ Lc, CL M g = Lc ++ [r] → ∀ s y,
      ρ.o r = psi s y z →
      lt (spArg (ρ.v g) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true →
      VSmallV s') :
    Lhd z (σ.o g) (ρ.o g) := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hgr : g < r := par_lt M 0 r g hg
  have hgM : g < M.length := by omega
  have hgN : g < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hrg : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
  -- the counted children in `M`
  set F := (children M g).filter (fun d => decide (d < r)) with hFdef
  have hchM : children M g = F ++ [r] := children_g_last hlen hL hp hg
  set Lc := F.filter (fun d => decide (Counted M g d)) with hLcdef
  have hclM : CL M g = Lc ++ [r] := by
    unfold CL; rw [hchM, List.filter_append]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hcnt]
    rfl
  -- the counted children in `N`
  set f : Nat → Nat := fun k => r + k * L with hfdef
  have hroots : [r] ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) =
      (List.range (n - 1)).map f ++ [r + (n - 1) * L] := by
    have e1 : (List.range n).map f = [r] ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp [hfdef, Nat.add_sub_cancel]
    have e2 : (List.range n).map f = (List.range (n - 1)).map f ++ [r + (n - 1) * L] := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range_succ, List.map_append]; simp [hfdef]
    rw [← e1, e2]
  set Cm := ((List.range (n - 1)).map f).filter
    (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) g d)) with hCmdef
  have hclN : CL (TRIO.gexp M r L 0 0 n) g = Lc ++ Cm ++ [r + (n - 1) * L] := by
    unfold CL
    rw [children_g0 hlen hL hp hn hg, hchM, List.append_assoc, hroots, List.filter_append,
      List.filter_append]
    have hF' : F.filter (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) g d)) = Lc := by
      apply List.filter_congr
      intro d hd
      have hdr : d < r := by simpa using (List.mem_filter.mp hd).2
      simp only [counted_lt0 hlen hL hp hn hR0 hZ2 he2 hn2 hgr hdr]
    rw [hF', List.append_assoc]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hLast]
    rfl
  have hCmv : Cm.map σ.o = List.replicate Cm.length (omid M r L ρ) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hd).1
    exact hσmid k (by have := List.mem_range.mp hk; omega)
  have hLcv : Lc.map σ.o = Lc.map ρ.o := by
    apply List.map_congr_left
    intro d hd
    have hdF := (List.mem_filter.mp hd).1
    have hdr : d < r := by simpa using (List.mem_filter.mp hdF).2
    have hdM := (List.mem_filter.mp hdF).1
    apply hσG d hdr
    intro hD
    exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hdM hrg hdr hD hcnt
  -- the values
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hgM
  obtain ⟨hsN, hpN⟩ := cl_vals hCN hGN hgN
  rw [hclM] at hsM hpM
  rw [hclN] at hsN hpN
  simp only [List.map_append, List.map_singleton] at hsM hpM hsN hpN
  rw [hLcv, hCmv, hσlast] at hsN hpN
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN
  set Y0 := spArg (ρ.v r) z (sumN (((children M r).filter (fun c => decide (c < r + L))).map
    (cnt M ρ r))) with hY0
  set v := ρ.v r with hv
  set a := ρ.v g with ha
  set Lv := Lc.map ρ.o with hLv
  set m := Cm.length with hm
  have hOv : omid M r L ρ = psi v Y0 z := hom
  -- the sums
  have hsO : Single (omid M r L ρ) := by
    rw [← hσmid 0 (by omega)]; simpa using single_o hCN hGN (show r + 0 * L < _ by rw [hlN]; omega)
  have hsumN : sumN (Lv ++ List.replicate m (omid M r L ρ) ++ [ρ'.o r]) =
      app (app (sumN Lv) (mulT (omid M r L ρ) m)) (ρ'.o r) := by
    have hp1 := List.pairwise_append.mp hpN
    rw [sumN_append_dec hsN hpN, sumN_append_dec (fun t ht => hsN t (List.mem_append_left _ ht)) hp1.1,
      sumN_replicate hsO m, sumN_singleton (hsN _ (by simp))]
  have hsumM : sumN (Lv ++ [ρ.o r]) = app (sumN Lv) (ρ.o r) := by
    rw [sumN_append_dec hsM hpM, sumN_singleton (hsM _ (by simp))]
  have hoN : σ.o g = psi a (spArg a (spArg a (spArg a z (sumN Lv)) (mulT (omid M r L ρ) m))
      (ρ'.o r)) z := by
    rw [o_cl_eq hCN hGN hgN, hclN]
    simp only [List.map_append, List.map_singleton]
    rw [hLcv, hCmv, hσlast, hsumN, spArg_app, spArg_app, hσvg]
  have hoM : ρ.o g = psi a (spArg a (spArg a z (sumN Lv)) (ρ.o r)) z := by
    rw [o_cl_eq hC hG hgM, hclM]
    simp only [List.map_append, List.map_singleton]
    rw [hsumM, spArg_app]
  have hLs := sumN_dec Lv (fun t ht => hsM t (List.mem_append_left _ ht)) (List.pairwise_append.mp hpM).1
  have hfr := hVS g hgM Lc r [] (by rw [hclM])
  rw [hoN, hoM, hOv]
  have hXot : isOT (ρ.o r) = true := hG.ot_o r (by omega)
  rw [hor] at hoM hl hfr hXot ⊢
  have hOld : isOT (psi a (spArg a (spArg a z (sumN Lv)) (psi v (app Y0 one) z)) z) = true := by
    rw [← hoM]; exact hG.ot_o g hgM
  apply s1_core hOld hXot (by rw [← hOv]; exact hsO.1)
  · apply spArg_summands_ge ⟨v, _, rfl⟩ (sumN Lv) z hLs.1
    · rw [hLs.2]; intro q hq
      have := (List.pairwise_append.mp hpM).2.2 q hq (ρ.o r) (by simp)
      rwa [hor] at this
    · simp [summands]
  · have hnl : (n - 1) * L + L = n * L := by
      rw [← Nat.succ_mul]; congr 1; omega
    rw [← hσlast]; exact single_o hCN hGN (by rw [hlN]; omega)
  · exact hl
  · intro hm1
    have hp1 := List.pairwise_append.mp hpN
    rw [← hOv]
    exact hp1.2.2 (omid M r L ρ) (List.mem_append_right _ (List.mem_replicate.mpr ⟨by omega, rfl⟩))
      (ρ'.o r) (by simp)
  · exact hy'
  · intro hrw
    have := (hfr.2 v (app Y0 one) rfl hrw).subSmall a
    exact this
  · intro s' y' hs' hsv hrw
    exact (hVr s' y' hs' hsv Lc hclM v (app Y0 one) hor hrw).subSmall a
  · intro hrw
    exact hF g hgM Lc r [] (by rw [hclM]) v (app Y0 one) hor hrw

end

end Ytosk
