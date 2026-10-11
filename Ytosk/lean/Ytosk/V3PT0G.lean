/-
**PH3cG・FC3 は t = 0 の展開 N = M[n] に渡る（closure、2026-10-11）。**

`frameClosed_N_t0`（V3T0Frm）と同じ組み立て。枠の性質 Q が
- (d) 子の値が添字を保って下がっても保たれる（`hQd`）、
- (nr) 書き換えない枠では成り立つ（`hQnr`）
なら、M と M.take x の枠の Q から N の枠の Q が出る（`frameQd_N_t0`）。PH3cG・FC3 は (d)・(nr) を満たす
（V3PKind の挟み込み）。実測（deepA の t = 0 の行列、n = 2, 3）: N の B ≠ 0 の書き換えの枠は、x より前では M の枠の
y が下がったもの、写しは M[n − 1] と同じ（例外 0）。
-/
import Ytosk.V3T0Frm
import Ytosk.V3PKind
import Ytosk.V3PKindG

namespace Ytosk.G

open T

set_option linter.unusedSectionVars false

/-! ## 枠の性質としての PH3cG・FC3 -/

/-- The frame property of `PH3cG`. -/
abbrev QPH (a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true →
    spArg a z (sumN Lv) ≠ z →
    PH3cKindG (spArg a z (sumN Lv)) (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s

/-- The frame property of `FC3`. -/
abbrev QF3 (a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true →
    Lv = [] → (split y (psi (succ s) z z)).1 ≠ z → FC3c a s y

theorem ph3c_iff {M : Mat} {ρ : Valn} : PH3cG M ρ ↔ ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat)
    (R : List Nat), CL M i = Lc ++ c :: R → QPH (ρ.v i) (Lc.map ρ.o) (ρ.o c) := by
  constructor
  · intro h i hi Lc c R hCL s y hsy ht hB
    exact h i hi Lc c R hCL s y hsy hB ht
  · intro h i hi Lc c R hCL s y hsy hB ht
    exact h i hi Lc c R hCL s y hsy ht hB

theorem lt_z_of_ne {y : T} (h : y ≠ z) : lt z y = true := by
  cases y with
  | z => exact absurd rfl h
  | psi => rfl

theorem fc3_iff {M : Mat} {ρ : Valn} : FC3 M ρ ↔ ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat)
    (R : List Nat), CL M i = Lc ++ c :: R → QF3 (ρ.v i) (Lc.map ρ.o) (ρ.o c) := by
  constructor
  · intro h i hi Lc c R hCL s y hsy ht hL hhi
    have hLc : Lc = [] := List.map_eq_nil_iff.mp hL
    subst hLc
    have hy : y ≠ z := ne_z_of_lt ht.1
    exact h i hi c R (by simpa using hCL) s y hsy hy ht.2 hhi
  · intro h i hi c R hCL s y hsy hy ht hhi
    exact h i hi [] c R (by simpa using hCL) s y hsy ⟨lt_z_of_ne hy, ht⟩ rfl hhi

/-- (d) for `QPH`. -/
theorem qph_drop {a : T} {Lv : List T} {s s' y y' : T} (hle : psi s' y' z ≤ psi s y z)
    (hss : y' ≠ z → s' = s) (hM : QPH a Lv (psi s y z)) : QPH a Lv (psi s' y' z) := by
  intro s1 y1 h ht hB
  obtain ⟨h1, h2, -⟩ := T.psi.inj h
  subst h1; subst h2
  have hy0 : y' ≠ z := ne_z_of_lt ht.1
  have hs := hss hy0
  subst hs
  have hyy : y' ≤ y := by
    rcases (le_iff _ _).mp hle with h | h
    · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact le_of_lt h
    · simp only [psi.injEq] at h; rw [h.2.1]
  have hMt : lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s' y z) = true :=
    ⟨lt_of_lt_of_le (show _ < y' from ht.1) hyy, lt_of_lt_of_le (show _ < psi s' y' z from ht.2) hle⟩
  exact ph3cKindG_squeeze (hM s' y rfl hMt hB) ht.1 hyy

/-- (d) for `QF3`. -/
theorem qf3_drop {a : T} {Lv : List T} {s s' y y' : T} (hle : psi s' y' z ≤ psi s y z)
    (hss : y' ≠ z → s' = s) (hM : QF3 a Lv (psi s y z)) : QF3 a Lv (psi s' y' z) := by
  intro s1 y1 h ht hL hhi
  obtain ⟨h1, h2, -⟩ := T.psi.inj h
  subst h1; subst h2
  have hy0 : y' ≠ z := ne_z_of_lt ht.1
  have hs := hss hy0
  subst hs
  have hyy : y' ≤ y := by
    rcases (le_iff _ _).mp hle with h | h
    · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact le_of_lt h
    · simp only [psi.injEq] at h; rw [h.2.1]
  subst hL
  exact fc3_squeeze (fun hy hrw hhiM => hM s' y rfl ⟨lt_z_of_ne hy, hrw⟩ rfl hhiM) hyy ht.2 hhi

theorem qph_nr {a : T} {Lv : List T} {s y : T}
    (h : ¬ (lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true)) :
    QPH a Lv (psi s y z) := by
  intro s1 y1 e ht
  simp only [psi.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e
  exact absurd ht h

theorem qf3_nr {a : T} {Lv : List T} {s y : T}
    (h : ¬ (lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true)) :
    QF3 a Lv (psi s y z) := by
  intro s1 y1 e ht
  simp only [psi.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e
  exact absurd ht h

/-! ## t = 0 -/

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : GoodOT (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

/-- **A frame property that survives drops of the child and holds at non-rewriting frames passes to
`N = M[n]`** (`t = 0`), from the frames of `M` and `M.take x`. -/
theorem frameQd_N_t0 (Q : T → List T → T → Prop)
    (hQd : ∀ a Lv s s' y y', psi s' y' z ≤ psi s y z → (y' ≠ z → s' = s) →
      Q a Lv (psi s y z) → Q a Lv (psi s' y' z))
    (hQnr : ∀ a Lv s y, ¬ (lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true) →
      Q a Lv (psi s y z))
    {ρ' : Valn}
    (hF : ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      Q (ρ.v i) (Lc.map ρ.o) (ρ.o c))
    (hFT : ∀ i, i < (M.take (r + L)).length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
      CL (M.take (r + L)) i = Lc ++ c :: R → Q (ρ'.v i) (Lc.map ρ'.o) (ρ'.o c))
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧ σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i)
    (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : ∀ g, par M 0 r = some g → Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hC1 : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hlr : ρ'.o r ≤ ρ.o r) (hO'le : ρ'.o r ≤ omid M r L ρ)
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d)
    (hss : ∀ d, d < r → σ.v d ≠ ρ.v d → σ.o d = psi (σ.v d) z z) :
    ∀ i, i < (TRIO.gexp M r L 0 0 n).length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
      CL (TRIO.gexp M r L 0 0 n) i = Lc ++ c :: R → Q (σ.v i) (Lc.map σ.o) (σ.o c) := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hsub : ∀ d, d < r → ∀ s y s' y', ρ.o d = psi s y z → σ.o d = psi s' y' z → y' ≠ z → s' = s := by
    intro d hd s y s' y' h h' hy
    obtain ⟨y0, hy0⟩ := o_psi_sub hCN (show d < (TRIO.gexp M r L 0 0 n).length by rw [hlN]; omega)
    rw [h'] at hy0; simp only [psi.injEq] at hy0
    obtain ⟨y1, hy1⟩ := o_psi_sub hC (show d < M.length by omega)
    rw [h] at hy1; simp only [psi.injEq] at hy1
    rw [hy0.1, hy1.1, sf_ot (hGN.ot_v d (by rw [hlN]; omega)), sf_ot (hG.ot_v d (by omega))]
    by_contra hne
    have := hss d hd hne
    rw [h'] at this; simp only [psi.injEq] at this; exact hy this.2.1
  intro i hi Lc c R hCL
  apply frameQ_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN
    Q (ρ' := ρ') hF hFT hσB hoffD
  · -- the frames of `g` when `r` counts there
    intro g hg hcnt
    have hgr : g < r := par_lt M 0 r g hg
    have hrc : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
    have hσvg : σ.v g = ρ.v g := (hoffD g hgr).2 (fun hd =>
      uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hd hrc hcnt)
    apply g_frames_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN Q hg hcnt
      (fun c hc hd => (hoffD c hc).1 hd) hσvg hσmid hσlast (hLast g hg hcnt)
      (fun Lc c R h => hF g (by omega) Lc c R h)
    intro Lc j cv hclM hcv
    obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG
    set v := ρ.v r with hv
    set a := ρ.v g with ha
    set Y0 := spArg v z (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r)))
      with hY0
    have hOot : isOT (psi v Y0 z) = true := by
      rw [← hom]; exact isOT_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN
    -- the psi form of `cv`
    obtain ⟨s, y, hsy⟩ : ∃ s y, cv = psi s y z := by
      rcases hcv with rfl | rfl
      · exact ⟨v, Y0, hom⟩
      · exact (single_o hC1 hGT (show r < (M.take (r + L)).length by rw [List.length_take]; omega)).2
    subst hsy
    have hcvle : psi s y z ≤ psi v Y0 z := by
      rcases hcv with h | h
      · rw [h, hom]
      · rw [h, ← hom]; exact hO'le
    have hcvss : y ≠ z → s = v := by
      intro hy
      rcases hcv with h | h
      · rw [hom] at h; simp only [psi.injEq] at h; exact h.1
      · by_contra hne; exact hy (hy' s y h.symm hne)
    obtain ⟨hsM, hpM⟩ := cl_vals hC hG (show g < M.length by omega)
    rw [hclM] at hsM hpM
    simp only [List.map_append, List.map_singleton] at hsM hpM
    have hOr : psi v Y0 z < ρ.o r := by
      rw [hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one Y0⟩)
    rcases Nat.eq_zero_or_pos j with hj | hj
    · -- the first copy root: below `o(r)`
      subst hj
      simp only [List.replicate, List.append_nil]
      have hle : psi s y z ≤ psi v (app Y0 one) z := by rw [← hor]; exact le_trans hcvle (le_of_lt hOr)
      have hQr := hF g (by omega) Lc r [] (by rw [hclM])
      rw [hor] at hQr
      exact hQd _ _ _ _ _ _ hle hcvss hQr
    · -- a later one does not rewrite
      apply hQnr
      intro ht
      have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht))
        (List.pairwise_append.mp hpM).1
      have hLge : ∀ q ∈ Lc.map ρ.o, ρ.o r ≤ q := fun q hq => (List.pairwise_append.mp hpM).2.2 q hq _ (by simp)
      have hOs : Single (psi v Y0 z) := ⟨hOot, _, _, rfl⟩
      have hsum : sumN (Lc.map ρ.o ++ List.replicate j (omid M r L ρ)) =
          app (sumN (Lc.map ρ.o)) (mulT (psi v Y0 z) j) := by
        rw [hom, sumN_append_dec, sumN_replicate hOs]
        · intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact hsM t (List.mem_append_left _ ht)
          · rw [(List.mem_replicate.mp ht).2]; exact hOs
        · refine List.pairwise_append.mpr ⟨(List.pairwise_append.mp hpM).1,
            List.pairwise_replicate.mpr (Or.inr (le_refl _)), fun q hq b hb => ?_⟩
          rw [(List.mem_replicate.mp hb).2]; exact le_trans (le_of_lt hOr) (hLge q hq)
      rw [hsum, spArg_app] at ht
      have hnr := no_rw_after (a := a) (B := spArg a z (sumN (Lc.map ρ.o))) hOot hj
      apply hnr
      have hy0 : y ≠ z := fun h => by rw [h] at ht; exact T.not_lt_z _ ht.1
      obtain rfl := hcvss hy0
      have hyy : y ≤ Y0 := by
        rcases (le_iff _ _).mp hcvle with h | h
        · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact le_of_lt h
        · simp only [psi.injEq] at h; rw [h.2.1]
      exact ⟨lt_of_lt_of_le (show _ < y from ht.1) hyy, lt_of_lt_of_le (show _ < psi v y z from ht.2) hcvle⟩
  · -- a frame before `r` whose child is in `D`
    intro i' hi' hng Lc' c' R' hCL' hD
    have hcM : c' ∈ children M i' := cl_mem_children (show c' ∈ CL M i' by rw [hCL']; simp)
    have hccnt : Counted M i' c' := by
      have : c' ∈ CL M i' := by rw [hCL']; simp
      unfold CL at this; simpa using (List.mem_filter.mp this).2
    have hcr : c' < r := by
      by_cases hig : par M 0 r = some i'
      · have hle := children_g_le hlen hL hp hig hcM
        rcases Nat.lt_or_ge c' r with h | h
        · exact h
        · exfalso; have : c' = r := by omega
          rw [this] at hccnt; exact hng ⟨hig, hccnt⟩
      · exact children_lt_r hlen hL hp hi' hig hcM
    have hcMl : c' < M.length := by omega
    obtain ⟨s0, y0, hs0⟩ := (single_o hC hG hcMl).2
    obtain ⟨y1, hy1⟩ := o_psi_sub hCN (show c' < (TRIO.gexp M r L 0 0 n).length by rw [hlN]; omega)
    rw [hy1]
    have hle : psi (sf (σ.v c')) y1 z ≤ psi s0 y0 z := by rw [← hy1, ← hs0]; exact hdl c' hcr hD
    have hQ := hF i' (by omega) Lc' c' R' hCL'
    rw [hs0] at hQ
    exact hQd _ _ _ _ _ _ hle (hsub c' hcr s0 y0 _ y1 hs0 hy1) hQ
  · exact hi
  · exact hCL

/-- **PH3cG of `N = M[n]`** (`t = 0`). -/
theorem ph3c_N_t0 {ρ' : Valn} (hF : PH3cG M ρ) (hFT : PH3cG (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧ σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i)
    (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : ∀ g, par M 0 r = some g → Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hC1 : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hlr : ρ'.o r ≤ ρ.o r) (hO'le : ρ'.o r ≤ omid M r L ρ)
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d)
    (hss : ∀ d, d < r → σ.v d ≠ ρ.v d → σ.o d = psi (σ.v d) z z) :
    PH3cG (TRIO.gexp M r L 0 0 n) σ :=
  ph3c_iff.mpr (frameQd_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN QPH
    (fun _ _ _ _ _ _ hle hss h => qph_drop hle hss h) (fun _ _ _ _ h => qph_nr h)
    (ph3c_iff.mp hF) (ph3c_iff.mp hFT) hσB hoffD hσmid hσlast hLast hC1 hGT hlr hO'le hy' hdl hss)

/-- **FC3 of `N = M[n]`** (`t = 0`). -/
theorem fc3_N_t0 {ρ' : Valn} (hF : FC3 M ρ) (hFT : FC3 (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧ σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i)
    (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : ∀ g, par M 0 r = some g → Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hC1 : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hlr : ρ'.o r ≤ ρ.o r) (hO'le : ρ'.o r ≤ omid M r L ρ)
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d)
    (hss : ∀ d, d < r → σ.v d ≠ ρ.v d → σ.o d = psi (σ.v d) z z) :
    FC3 (TRIO.gexp M r L 0 0 n) σ :=
  fc3_iff.mpr (frameQd_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN QF3
    (fun _ _ _ _ _ _ hle hss h => qf3_drop hle hss h) (fun _ _ _ _ h => qf3_nr h)
    (fc3_iff.mp hF) (fc3_iff.mp hFT) hσB hoffD hσmid hσlast hLast hC1 hGT hlr hO'le hy' hdl hss)

end

end Ytosk.G
