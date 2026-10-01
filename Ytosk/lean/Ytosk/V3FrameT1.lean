/-
**3 行・t = 1・q ≠ r: 枠の条件 (W) を値の不変条件 TP1 から。**

- 穴の段 `holeLev`: 共終数 Ω_{μ+1} の項と、対角化の点 ψ_{a'}(b)（cof b = Ω_{μ+1}）の下の項で μ（`holeLev_holeT`）。
- 値の不変条件 **TP1**: 書き換えの枠（B < y、ψ_{v(i)}(0) < ψ_s(y)）で穴のある y について B < fsD(y, ψ_{holeLev y}(1))。
- 始点 seed = o_{M.take x}(r) の引数は 0 でない（M.take x で r の最初の子 r+1 は数える子、`seed_arg_ne_z`）。
  よって ψ_μ(1) ≤ seed、鎖のすべての項も ψ_μ(1) 以上。
- (W)（`hW_of_TP1`）: TP1 と穴と fsD の単調性から。
-/
import Ytosk.V3ValT1R
import Ytosk.V3TP1

namespace Ytosk

open T

/-! ## 穴の段 -/

/-- The level `μ` of the `Ω_{μ+1}` hole that `fsD` acts on. -/
def holeLev : T → T
  | z => z
  | psi _ _ (psi c d e) => holeLev (psi c d e)
  | psi a b z =>
    if b = z then (if isSucc a then init a else holeLev a)
    else match cof b with
      | .big μ => μ
      | _ => holeLev b

theorem holeLev_cof : ∀ {t μ : T}, cof t = .big μ → holeLev t = μ
  | z, _, h => by simp [cof] at h
  | psi _ _ (psi c d e), μ, h => by
    show holeLev (psi c d e) = μ
    exact holeLev_cof (t := psi c d e) (by simpa [cof] using h)
  | psi a b z, μ, h => by
    unfold holeLev
    unfold cof at h
    by_cases hb : b = z
    · rw [if_pos hb] at h ⊢
      by_cases ha : a = z
      · rw [if_pos ha] at h; cases h
      · rw [if_neg ha] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs] at h ⊢; cases h; rfl
        · rw [if_neg hs] at h ⊢; exact holeLev_cof h
    · rw [if_neg hb] at h ⊢
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h
        cases hcb : cof b with
        | big μ' =>
          rw [hcb] at h; simp only at h
          split at h
          · cases h; rfl
          · cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- Below a diagonal point the cofinality is `ω`. -/
theorem DiagAt.cof_omega {a b μ t : T} (h : DiagAt a b μ t) : cof t = .omega := by
  induction h with
  | here hb hc hμ =>
    have hs := not_succ_of_cof_big hc
    unfold cof
    rw [if_neg hb, if_neg (by rw [hs]; simp), hc]
    simp only
    rw [if_neg hμ]
  | rest _ ih => simpa [cof] using ih
  | @arg a' b' hb hs _ ih =>
    unfold cof
    rw [if_neg hb, if_neg (by rw [hs]; simp), ih]
  | @sub a' ha hs _ ih =>
    unfold cof
    rw [if_pos rfl, if_neg ha, if_neg (by rw [hs]; simp)]
    exact ih

theorem DiagAt.holeLev_eq {a b μ t : T} (h : DiagAt a b μ t) : Ytosk.holeLev t = μ := by
  induction h with
  | here hb hc _ =>
    unfold holeLev
    rw [if_neg hb, hc]
  | rest _ ih => exact ih
  | @arg a' b' hb _ hD ih =>
    unfold holeLev
    rw [if_neg hb, hD.cof_omega]
    exact ih
  | @sub a' _ hs _ ih =>
    unfold holeLev
    rw [if_pos rfl, if_neg (by rw [hs]; simp)]
    exact ih

/-- **The level of a hole.** -/
theorem holeLev_holeT {μ br vr t : T} (h : HoleT μ br vr t) : holeLev t = μ := by
  rcases h with h | ⟨_, _, hD⟩
  · exact holeLev_cof h
  · exact hD.holeLev_eq

/-! ## 値の不変条件 TP1 -/

/-- **Value invariant TP1** (persistence of the rewriting): at a rewriting frame with a hole in the
argument `y`, the state `B` stays below `fsD(y, ψ_μ(1))`, `μ` the level of the hole
(SRO より下の L8 網羅で 3.9 万枠、例外 0; 数えない子では引き金は起きない). -/
def TP1 (M : Mat) (ρ : Valn) : Prop :=
  ∀ i L c R, children M i = L ++ c :: R → ∀ s y, ρ.o c = psi s y z →
    lt (preState M ρ i L) y = true → lt (psi (ρ.v i) z z) (psi s y z) = true → OHole y →
    lt (preState M ρ i L) (fsD y (psi (holeLev y) one z)) = true

/-! ## 始点の引数は 0 でない -/

theorem add_ne_z_left : ∀ {x : T} (y : T), x ≠ z → add x y ≠ z
  | z, _, h => absurd rfl h
  | psi a b c, z, _ => by simp [add]
  | psi a b c, psi d e f, _ => by
    simp only [add]
    split <;> simp

theorem H_ne_z {s y : T} (hy : y ≠ z) : H s y ≠ z := by
  unfold H
  by_cases ht : cut (add s one) y = z
  · rw [ht, add_z_left]
    have hlt : lt (psi s z z) (psi s y z) = true := by
      show psi s z z < psi s y z
      rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, lt_of_le_of_ne (z_le y) (Ne.symm hy)⟩
    simp only [sub, hlt, if_true]
    simp
  · exact add_ne_z_left _ ht

theorem step_ne_z' (a b s y c : T) : step a b s y c ≠ z := by
  unfold step
  split
  · rename_i h
    apply H_ne_z
    intro hy; rw [hy] at h; exact T.not_lt_z _ h.1
  · exact add_ne_z_right _ (by simp)

theorem spArg_ne_z (a : T) : ∀ (c b : T), (b ≠ z ∨ c ≠ z) → spArg a b c ≠ z
  | z, b, h => by
    rcases h with h | h
    · exact h
    · exact absurd rfl h
  | psi s y c, b, _ => by
    rw [spArg_cons]
    exact spArg_ne_z a c _ (Or.inl (step_ne_z' a b s y c))

theorem foldl_sf_ne_z : ∀ (l : List T) (acc : T), (acc ≠ z ∨ ∃ t ∈ l, t ≠ z) →
    l.foldl (fun a b => sf (add a b)) acc ≠ z
  | [], acc, h => by
    rcases h with h | ⟨t, ht, _⟩
    · exact h
    · simp at ht
  | t :: l, acc, h => by
    simp only [List.foldl_cons]
    apply foldl_sf_ne_z l
    by_cases hacc : acc ≠ z
    · exact Or.inl (sf_ne_z (add_ne_z_left _ hacc))
    · rcases h with h | ⟨t', ht', hne⟩
      · exact absurd h hacc
      · rcases List.mem_cons.mp ht' with rfl | ht'
        · exact Or.inl (sf_ne_z (add_ne_z_right _ hne))
        · exact Or.inr ⟨t', ht', hne⟩

/-- **The argument of `o(i)` is nonzero when `i` has a counted child.** -/
theorem o_arg_ne_z {N : Mat} {ρ : Valn} {i c : Nat} (hC : Cons N ρ) (hi : i < N.length)
    (hc : c ∈ children N i) (hcnt : Counted N i c) :
    ∃ σ, ρ.o i = psi (sf (ρ.v i)) σ z ∧ σ ≠ z := by
  have hcl := (mem_children hc).2
  have hoc : ρ.o c ≠ z := by
    rw [(hC c hcl).1]; unfold oRhs; exact sf_ne_z (by simp)
  have hmem : ρ.o c ∈ (children N i).map (cnt N ρ i) := by
    refine List.mem_map.mpr ⟨c, hc, ?_⟩
    rw [cnt_eq_ite, if_pos hcnt]
  have hS : sumN ((children N i).map (cnt N ρ i)) ≠ z :=
    foldl_sf_ne_z _ z (Or.inr ⟨_, hmem, hoc⟩)
  refine ⟨spArg (sf (ρ.v i)) z (sf (sumN ((children N i).map (cnt N ρ i)))), ?_,
    spArg_ne_z _ _ _ (Or.inr (sf_ne_z hS))⟩
  rw [(hC i hi).1]
  unfold oRhs
  show add (sp (sf (ρ.v i)) z (sf _)) (sf z) = _
  rw [sp_eq_spArg]
  rfl

/-! ## M.take x で r の最初の子は数える子 -/

section
variable {M : Mat} {x r : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (h1 : par M 1 x = some r) (hqr : par M 0 x ≠ some r)
include hx hR0 hSD h1

/-- **`r` has no bump child.** -/
theorem no_bump_child_r : ∀ j ∈ children M r, col M j ≠ bump M r := by
  intro j hj hjb
  have hA := anc0_of_par M 1 r x h1
  have hrx : r ≠ x := by have := par_lt M 1 x r h1; omega
  obtain ⟨p, hpr, hpx⟩ := anc0_child hA hrx
  have hpl : p < M.length := by have := hpx.le; omega
  have hpM : p ∈ children M r := mem_children_iff.mpr ⟨hpl, hpr⟩
  have hp1 := e1_path_child h1 hA hrx hpr hpx
  have hpj : par M 0 j = some r := (mem_children_iff.mp hj).2
  have hrp := par_lt M 0 p r hpr
  have hjl := (mem_children hj).2
  rcases Nat.lt_trichotomy j p with hjp | rfl | hpj'
  · obtain ⟨L, R, hLR⟩ := List.append_of_mem hj
    obtain ⟨hL, _⟩ := sib_order (children_sorted M r) hLR
    have hpR : p ∈ R := by
      have : p ∈ L ++ j :: R := hLR ▸ hpM
      rcases List.mem_append.mp this with h | h
      · have := hL p h; omega
      · rcases List.mem_cons.mp h with h | h
        · omega
        · exact h
    have hle := sib_le hSD R L j hLR p hpR
    rw [hjb] at hle
    unfold colLe bump at hle
    have e0 : (col M p).1 = entry M 0 p := rfl
    have e1 : (col M p).2.1 = entry M 1 p := rfl
    simp only at hle
    rw [e0, e1] at hle
    have := hR0 p r hpr
    omega
  · have := e1_of_col (show col M j = (entry M 0 r + 1, entry M 1 r, 1) from hjb); omega
  · have hA' := anc_between hpx j (by omega) (by omega)
    have := (anc0_par hA' (by omega) hpj).le
    omega

include hZ2 hZ1 hUAB hqr in
/-- **In `M.take x`, the first child `r + 1` of `r` is counted.** -/
theorem first_child_counted_take :
    r + 1 ∈ children (M.take x) r ∧ Counted (M.take x) r (r + 1) := by
  have hA := anc0_of_par M 1 r x h1
  have hrx : r < x := par_lt M 1 x r h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hrq : r ≤ q := par0_ge_of_anc hA hrx (Nat.le_refl _) hq
  have hqr' : q ≠ r := fun e => hqr (e ▸ hq)
  have hqx := par_lt M 0 x q hq
  have hr1x : r + 1 < x := by omega
  have hpar : par M 0 (r + 1) = some r := child_succ hA (by omega)
  have hmemM : r + 1 ∈ children M r := mem_children_iff.mpr ⟨by omega, hpar⟩
  have hmemT : r + 1 ∈ children (M.take x) r := by
    rw [children_take, List.mem_filter]; exact ⟨hmemM, by simpa using hr1x⟩
  refine ⟨hmemT, ?_, ?_⟩
  · rw [col_take M hr1x, bump_take M hrx]
    exact no_bump_child_r hx hR0 hSD h1 (r + 1) hmemM
  · rintro ⟨hiu, htop⟩
    obtain ⟨k, hk, hu⟩ := (isUpg_take M (by omega) (r + 1)).mp hiu
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    rcases hcase with h | ⟨hAk, hlt⟩
    · have hkr : k = r := by omega
      rw [hkr] at hu
      have := leaf_of_upg_next hR0 hu x hA
      omega
    · have he2 : entry M 2 (r + 1) = 1 := by have := upg_target_e2 hu; have := hZ2 (r + 1); omega
      obtain ⟨p', hp', hp'k⟩ := anc0_child hAk (by omega)
      have hp'k' := hp'k.le
      have hp'x : p' < x := by omega
      have hp'M : p' ∈ children M (r + 1) := mem_children_iff.mpr ⟨by omega, hp'⟩
      have hp'T : p' ∈ children (M.take x) (r + 1) := by
        rw [children_take, List.mem_filter]; exact ⟨hp'M, by simpa using hp'x⟩
      unfold topped at htop
      cases hl : (children (M.take x) (r + 1)).getLast? with
      | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hp'T; simp at hp'T
      | some ℓ =>
        rw [hl] at htop
        simp only [decide_eq_true_eq] at htop
        have hlast : children (M.take x) (r + 1) = (children (M.take x) (r + 1)).dropLast ++ [ℓ] := by
          rw [List.dropLast_append_getLast? _ hl]
        have hall := all_bump_of_last (R0P_take hR0 x) (Z2_take hZ2 x) (SibDec_take hSD x)
          (Z1C_take hZ1 x) (by rw [entry_take M 2 hr1x]; exact he2) hlast htop p' hp'T
        rw [col_take M hp'x, bump_take M hr1x] at hall
        exact hUAB k (r + 1) hu (by omega) p' hp'M hall hp'k

end

/-- **The seed is at least `ψ_μ(1)`.** -/
theorem seed_ge_one {M : Mat} {x r : Nat} {ρ1 : Valn} {μ : T} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAB : UAB M)
    (h1 : par M 1 x = some r) (hqr : par M 0 x ≠ some r)
    (hC1 : Cons (M.take x) ρ1) (hv : ρ1.v r = μ) (hμot : isOT μ = true) :
    psi μ one z ≤ ρ1.o r := by
  obtain ⟨hmem, hcnt⟩ := first_child_counted_take hx hR0 hZ2 hSD hZ1 hUAB h1 hqr
  have hrx : r < x := par_lt M 1 x r h1
  obtain ⟨σ, hσ, hσz⟩ := o_arg_ne_z hC1 (by rw [List.length_take]; omega) hmem hcnt
  rw [hσ, hv, sf_ot hμot]
  exact le_psi_arg (one_le_of_ne_z hσz)

/-! ## (W) -/

/-- **(W) from TP1**: the state stays below `fsD(y, ζ)` for every term `ζ` of the chain. -/
theorem hW_of_TP1 {M : Mat} {x r : Nat} {ρ : Valn} {μ br vr seed ζ0 : T} (hx : x + 1 = M.length)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hrx : r < x) (hAr : Anc0 M r x) (hro : ρ.o r = psi vr br z)
    (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z) (hox : ρ.o x = psi (succ μ) z z)
    (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
    (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
    (hV : ∀ i, i < x → DepX M x false i → VLocal M x ρ ζ0 μ i)
    (hS2 : ∀ i k, i ≤ r → DepX M x false i → entry M 2 i = 0 → upg M i = some k → k ≤ r)
    (hS3 : ∀ i j k, i ≤ r → j ∈ children M i → col M j = bump M i → k ∈ children M j →
      DepX M x true k → k ≤ r)
    (hTP : TP1 M ρ) (hseed : psi μ one z ≤ seed) :
    ∀ m i L' c R, i < x → DepX M x true i → children M i = L' ++ c :: R →
      DepX M x true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      lt (preState M ρ i L') (fsD y (gamS μ br seed m)) = true := by
  have hH := t1_hole hC hG hx hrx hAr hro hcb hμr hbr (Or.inl (by rw [hox]; exact cof_omega_succ μ))
    hF1 hOS hV hS2 hS3
  intro m i L' c R hi _ hch hdc s y hcv hlt1 hlt2
  have hcM : c ∈ children M i := by rw [hch]; simp
  have hcl := (mem_children hcM).2
  obtain ⟨hHc, _⟩ := hH true c hdc (by
    rcases Nat.lt_or_ge c x with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, rfl⟩)
  simp only [valB, cond_true] at hHc
  rw [hcv] at hHc
  have hy : y ≠ z := by
    intro h; rw [h] at hlt1; exact T.not_lt_z _ hlt1
  have hHy := holeT_arg hy hHc hcb
  have hOy := ohole_of_holeT hHy
  have h0 := hTP i L' c R hch s y hcv hlt1 hlt2 hOy
  rw [holeLev_holeT hHy] at h0
  exact persist_of_tp1 hOy (gamS_ge_one hcb hseed m) h0

/-! ## まとめ: (W) を TP1 から -/

/-- **`t = 1`, `q ≠ r`, all `n ≥ 2`**: `t1_main_val` with (W) replaced by the value invariant TP1. -/
theorem t1_main_tp1 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmall M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hTP : TP1 M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbs M ρ) (hWS : BumpWeakShape M ρ)
    (hVSt : BumpVSmallTake M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbs M ρ)
    (hne : (drop1 M (r + L) rkM).o r ≠ ρ.o r)
    {μ br vr : T} (hμr : μ = vr) (hro : ρ.o r = psi vr br z)
    (hV : ∀ m i, i < r + L → DepX M (r + L) false i →
      VLocal M (r + L) ρ (gamS μ br ((drop1 M (r + L) rkM).o r) m) μ i)
    (hLo : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z →
        fsD (split y (psi (succ s) z z)).2 (gamS μ br ((drop1 M (r + L) rkM).o r) m) ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z →
        (split (fsD y (gamS μ br ((drop1 M (r + L) rkM).o r) m)) (psi (succ s) z z)).2 = z))
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r < r + L := by omega
  have hrM : r < M.length := by omega
  have hvr : ρ.v r = vr := by
    obtain ⟨y0, hy0⟩ := o_psi_sub hC hrM
    rw [hro] at hy0; simp only [psi.injEq] at hy0
    rw [hy0.1, sf_ot (hG.ot_v r hrM)]
  have hF1 : ∀ i, r < i → i < r + L → DepX M (r + L) true i → ¬ DepX M (r + L) false i →
      lt μ (ρ.v i) = true := by
    intro i h2 h3 h4 h5
    rw [hμr, ← hvr]
    exact hF1_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hC hG hRM i h2 h3 h4 h5
  have hox : ρ.o (r + L) = psi (succ μ) z z := by
    rw [o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2, hvr, hμr]
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq
  obtain ⟨hcb, hbr⟩ := hcb_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hox hF1 hOS (hV 0) h1 hx2 hqr
    hR12 hBE hro
  -- the seed
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hv1 : (drop1 M (r + L) rkM).v r = μ := by
    rw [base_v_r hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hA (by omega) hqr hpath, hvr, hμr]
  have hseed := seed_ge_one hlen hR0 hZ2 hSD hZ1 hUAB h1 hqr hC1 hv1
    (by rw [hμr, ← hvr]; exact hG.ot_v r hrM)
  have hW := hW_of_TP1 hlen hC hG hrx hA hro hcb hμr hbr hox hF1 hOS (hV 0)
    (hS2_t1 hR0 hA (by omega)) (hS3_t1 h1 hA (by omega) hlen hR0 hZ2 hSD hZ1) hTP hseed
  exact t1_main_val hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hqr hC hG hRM
    hVS hF hFO hArgT hKD hTD hAbs hWS hVSt hUA hne hμr hro hV hW hLo hsM hpM

/-! ## (L) -/

/-- **Value invariant TPL** (the low part stays empty): at a rewriting frame whose argument `y` has no
part below `Ω_{s+1}` and ends with `Ω_a` (`a` a limit with a hole), `Ω_{fsD(a, ψ_μ(Ω_{μ+1}))} ≥ Ω_{s+1}`
(`μ` the level of the hole; SRO より下の L8 網羅と乱択で 406 枠、例外 0。下限 ψ_μ(1) では 3 件崩れる). -/
def TPL (M : Mat) (ρ : Valn) : Prop :=
  ∀ i L c R, children M i = L ++ c :: R → ∀ s y, ρ.o c = psi s y z →
    lt (preState M ρ i L) y = true → lt (psi (ρ.v i) z z) (psi s y z) = true →
    (split y (psi (succ s) z z)).2 = z → ∀ a, last y = psi a z z → isSucc a = false → OHole a →
    ¬ psi (fsD a (psi (holeLev y) (psi (succ (holeLev y)) z z) z)) z z < psi (succ s) z z

theorem summands_fsD_psi {a b ζ : T} (hb : b ≠ z) :
    ∀ q ∈ summands (fsD (psi a b z) ζ), ∃ b', q = psi a b' z := by
  intro q hq
  by_cases hs : isSucc b = true
  · have h : fsD (psi a b z) ζ = mulT (psi a (init b) z) (count ζ) := by
      conv => lhs; unfold fsD
      rw [if_neg hb, if_pos hs]
    rw [h] at hq
    exact ⟨init b, summands_mulT ⟨_, _, rfl⟩ _ q hq⟩
  · rw [fsD_psi hb (by simpa using hs)] at hq
    simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
    exact ⟨_, hq⟩

theorem DiagAt.last' {a b μ : T} : ∀ {t : T}, DiagAt a b μ t → DiagAt a b μ (last t)
  | z, h => by cases h
  | psi _ _ z, h => h
  | psi _ _ (psi c d e), h => by
    show DiagAt a b μ (last (psi c d e))
    cases h with
    | rest h' => exact DiagAt.last' h'

theorem DiagAt.not_omega_succ {a b μ a' : T} (h : DiagAt a b μ (psi a' z z)) : isSucc a' = false := by
  cases h with
  | here hb _ _ => exact absurd rfl hb
  | arg hb _ _ => exact absurd rfl hb
  | sub _ hs _ => exact hs

/-- **(L)(ii) at a frame of `D`**: no low part stays no low part. -/
theorem lo_keep_of_TPL {μ br vr s y ζ : T} (hTPLf : (split y (psi (succ s) z z)).2 = z →
      ∀ a, last y = psi a z z → isSucc a = false → OHole a →
      ¬ psi (fsD a (psi μ (psi (succ μ) z z) z)) z z < psi (succ s) z z)
    (hy : y ≠ z) (hH : HoleT μ br vr (psi s y z)) (hcb : cof br = .big μ)
    (hbrl : last br ≠ psi (succ μ) z z) (hζΩ : psi μ (psi (succ μ) z z) z ≤ ζ)
    (hl : (split y (psi (succ s) z z)).2 = z) :
    (split (fsD y ζ) (psi (succ s) z z)).2 = z := by
  have hHy := holeT_arg hy hH hcb
  apply lo_z_keep hy hl
  have hyall : ∀ q ∈ summands y, ¬ q < psi (succ s) z z := by
    intro q hq
    have e := split_app (psi (succ s) z z) y
    rw [hl, app_z_right] at e
    rw [← e] at hq
    exact split_fst_ge _ y q hq
  have hHl := holeT_last hHy
  have hlh := hyall _ (last_mem hy)
  obtain ⟨a, b, hlc⟩ := last_psi_form hy
  rw [hlc] at hlh hHl ⊢
  by_cases hb : b = z
  · subst hb
    by_cases ha : isSucc a = true
    · -- the last summand is `Ω_{μ+1}`
      exfalso
      have haz : a ≠ z := by
        intro h; subst h
        have h1 : isSucc (z : T) = false := rfl
        rw [h1] at ha; cases ha
      have hcf : cof (psi a z z) = .big (init a) := by
        unfold cof; rw [if_pos rfl, if_neg haz, if_pos ha]
      have hia : init a = μ := by
        rcases hHl with h | ⟨_, _, hD⟩
        · rw [hcf] at h; cases h; rfl
        · rw [hD.not_omega_succ] at ha; cases ha
      have hsa : succ μ = a := by rw [← hia]; unfold succ; exact init_app_one ha
      rcases hH with hcof | ⟨a', _, hD⟩
      · have hμs := (cof_psi_inv hy hcof).2
        apply hlh
        rw [← hsa, psi_lt_psi_z_iff]
        left
        exact lt_of_le_of_lt (le_refl _) (show succ μ < succ s from by
          rw [lt_succ_iff]; exact succ_le_of_lt (show μ < s from hμs))
      · cases hD with
        | here _ _ _ => exact hbrl (by rw [hlc, ← hsa])
        | arg _ _ hDy =>
          have := hDy.last'
          rw [hlc] at this
          rw [this.not_omega_succ] at ha; cases ha
        | sub _ _ _ => exact hy rfl
    · have haz : a ≠ z := by
        intro h; subst h
        have := holeT_not_succ hHl
        have h1 : isSucc (psi z z z) = true := rfl
        rw [h1] at this; cases this
      have hns : isSucc a = false := by simpa using ha
      have hOa : OHole a := by
        have h := ohole_of_holeT hHl
        unfold OHole at h
        rw [if_pos rfl] at h
        rcases h.2 with h' | h'
        · rw [hns] at h'; cases h'
        · exact h'
      rw [fsD_sub haz hns]
      intro q hq
      simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
      subst hq
      intro hlt
      apply hTPLf hl a hlc hns hOa
      exact lt_of_le_of_lt (le_psi_sub (fsD_mono_eta hOa hζΩ)) hlt
  · intro q hq
    obtain ⟨b', rfl⟩ := summands_fsD_psi hb q hq
    intro hlt
    apply hlh
    rw [psi_lt_psi_z_iff] at hlt ⊢
    rcases hlt with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact absurd h' (T.not_lt_z _)

/-- **(L) from TPL** on the whole chain, given the lower bound `ψ_μ(Ω_{μ+1}) ≤ ζ` of the chain. -/
theorem hLo_of_TPL {M : Mat} {x r : Nat} {ρ : Valn} {μ br vr seed ζ0 : T} (hx : x + 1 = M.length)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hrx : r < x) (hAr : Anc0 M r x) (hro : ρ.o r = psi vr br z)
    (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z) (hox : ρ.o x = psi (succ μ) z z)
    (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
    (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
    (hV : ∀ i, i < x → DepX M x false i → VLocal M x ρ ζ0 μ i)
    (hS2 : ∀ i k, i ≤ r → DepX M x false i → entry M 2 i = 0 → upg M i = some k → k ≤ r)
    (hS3 : ∀ i j k, i ≤ r → j ∈ children M i → col M j = bump M i → k ∈ children M j →
      DepX M x true k → k ≤ r)
    (hTPL : TPL M ρ) (hbrl : last br ≠ psi (succ μ) z z)
    (hζΩ : ∀ m, psi μ (psi (succ μ) z z) z ≤ gamS μ br seed m) :
    ∀ m i L' c R, i < x → DepX M x true i → children M i = L' ++ c :: R →
      DepX M x true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z →
        fsD (split y (psi (succ s) z z)).2 (gamS μ br seed m) ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z →
        (split (fsD y (gamS μ br seed m)) (psi (succ s) z z)).2 = z) := by
  have hH := t1_hole hC hG hx hrx hAr hro hcb hμr hbr (Or.inl (by rw [hox]; exact cof_omega_succ μ))
    hF1 hOS hV hS2 hS3
  intro m i L' c R _ _ hch hdc s y hcv hlt1 hlt2
  have hcM : c ∈ children M i := by rw [hch]; simp
  have hcl := (mem_children hcM).2
  obtain ⟨hHc, _⟩ := hH true c hdc (by
    rcases Nat.lt_or_ge c x with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, rfl⟩)
  simp only [valB, cond_true] at hHc
  rw [hcv] at hHc
  have hy : y ≠ z := by
    intro h; rw [h] at hlt1; exact T.not_lt_z _ hlt1
  have hHy := holeT_arg hy hHc hcb
  have hζz : gamS μ br seed m ≠ z := by
    intro h; have := hζΩ m; rw [h] at this
    exact T.not_lt_z _ (lt_of_lt_of_le (T.z_lt_psi _ _ _) this)
  refine ⟨fun hl => lo_ne_z_of_holeT hζz hHy hl, fun hl => ?_⟩
  have hlev := holeLev_holeT hHy
  have hTf := hTPL i L' c R hch s y hcv hlt1 hlt2
  rw [hlev] at hTf
  exact lo_keep_of_TPL hTf hy hHc hcb hbrl (hζΩ m) hl

/-! ## b_r の最後の項は Ω_{μ+1} でない -/

theorem cof_of_isSucc : ∀ {t : T}, isSucc t = true → cof t = .succ
  | z, h => by simp [isSucc, last, one] at h
  | psi a b (psi c d e), h => by
    show cof (psi c d e) = .succ
    exact cof_of_isSucc (t := psi c d e) h
  | psi a b z, h => by
    have h' : psi a b z = one := by simpa [isSucc, last] using h
    cases h'
    rfl

/-- **The last summand of `H s y`**: `ψ_s(y)`, or the last summand of `y` when `y` has no part below
`Ω_{s+1}`. -/
theorem last_H {s y : T} (hy : y ≠ z) (hot : isOT y = true) (hs : isOT s = true) :
    last (H s y) = psi s y z ∨
      (last (H s y) = last y ∧ (split y (psi (succ s) z z)).2 = z) := by
  unfold H
  have hcut : cut (add s one) y = (split y (psi (succ s) z z)).1 := by
    rw [cut_eq_split _ hot, add_one_eq_succ hs]
  rw [hcut]
  have e := split_app (psi (succ s) z z) y
  by_cases hlo : (split y (psi (succ s) z z)).2 = z
  · right
    rw [hlo, app_z_right] at e
    rw [e]
    have hsub : sub (psi s y z) (psi s y z) = z := by
      simp only [sub]
      rw [if_neg (show ¬ (lt (psi s y z) (psi s y z) = true) from lt_irrefl' _)]
    rw [hsub, add_z_right]
    exact ⟨rfl, hlo⟩
  · left
    have hlt : (split y (psi (succ s) z z)).1 < y := by
      conv => rhs; rw [← e]
      exact lt_app_of hlo
    have hlt' : lt (psi s (split y (psi (succ s) z z)).1 z) (psi s y z) = true := by
      show psi s _ z < psi s y z
      rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hlt⟩
    have hsub : sub (psi s y z) (psi s (split y (psi (succ s) z z)).1 z) = psi s y z := by
      simp only [sub, hlt', if_true]
    rw [hsub]
    exact last_add_single _

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ ζ : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hC : Cons M ρ) (hG : Good3 M ρ)
  (hox : ρ.o x = psi (succ μ) z z)
  (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hV : ∀ i, i < x → DepX M x false i → VLocal M x ρ ζ μ i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hox hF1 hOS hV

/-- **The argument of `o(r)` does not end with `Ω_{μ+1}`.** -/
theorem last_br_t1 (h1 : par M 1 x = some r) (hx2 : entry M 2 x = 0) (hqr : par M 0 x ≠ some r)
    (hR12 : R12 M) (hBE : BumpE2 M) {vr br : T} (hro : ρ.o r = psi vr br z) :
    last br ≠ psi (succ μ) z z := by
  have hAr := anc0_of_par M 1 r x h1
  have hrx : r < x := par_lt M 1 x r h1
  have hpath := hpath_of_par1 h1 hAr (by omega)
  have hDr : DepX M x true r := dep_anc_x hUAT hZ2 hR12 hBE hx hx2 hAr
  have hnv : ¬ DepX M x false r := fun h =>
    v_r_not_chg hx hR0 hZ2 hSD hZ1 hUAT hUAB hAr (by omega) hqr hpath (depX_chgX h)
  have hcof := t1_cof hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hox hF1 hOS hV
  rcases hOS r hrx hDr with ⟨hv, _⟩ | ⟨_, L, c, R, hch, hcb2, hcu2, hR, hLnd⟩
  · exact absurd hv hnv
  · have hc : c ∈ children M r := by rw [hch]; simp
    have hcD : DepX M x true c := by
      cases hDr with
      | leaf => omega
      | @ochild _ c0 hc0 hcb0 hcu0 hdc0 =>
        have : c0 = c := by
          rw [hch] at hc0
          rcases List.mem_append.mp hc0 with h | h
          · exact absurd hdc0 (hLnd c0 h ⟨hcb0, hcu0⟩)
          · rcases List.mem_cons.mp h with h | h
            · exact h
            · rcases hR c0 h with h' | h'
              · exact absurd h' hcb0
              · exact absurd h' hcu0
        rw [← this]; exact hdc0
      | ov h => exact absurd h hnv
    have hcM := (mem_children hc).2
    have hrc := (mem_children hc).1
    have hpc : par M 0 c = some r := (mem_children_iff.mp hc).2
    obtain ⟨s, y, hcv⟩ := o_psi_form hC hcM
    have hcot : isOT (psi s y z) = true := by rw [← hcv]; exact hG.ot_o c hcM
    have hframe := o_frame hC hG (by omega) hch hcb2 hcu2 hR hcM
    rw [hcv, spArg_single] at hframe
    have hcx : c < x := by
      rcases Nat.lt_or_ge c x with h | h
      · exact h
      · exfalso
        have : c = x := by omega
        subst this; exact hqr hpc
    have hcc := hcof true c hcD hrc (Or.inl hcx)
    simp only [valB, cond_true] at hcc
    rw [hcv] at hcc
    rw [hro] at hframe
    obtain ⟨_, hb, _⟩ := T.psi.inj hframe
    rw [hb]
    by_cases hy : y = z
    · -- `o(c) = Ω_{μ+1}` is impossible
      subst hy
      unfold step
      rw [if_neg (by intro h; exact T.not_lt_z _ h.1), last_add_single]
      intro he
      have hs : s = succ μ := (T.psi.inj he).1
      cases hcD with
      | leaf => omega
      | @ochild _ d hd hdb hdu _ =>
        obtain ⟨σ, hσ, hσz⟩ := o_arg_ne_z hC hcM hd ⟨hdb, hdu⟩
        rw [hcv] at hσ; exact hσz (T.psi.inj hσ).2.1.symm
      | ov hvc =>
        have hvv := hcof false c hvc hrc (Or.inl hcx)
        simp only [valB, cond_false] at hvv
        obtain ⟨σ, hσ⟩ := o_psi_sub hC hcM
        rw [hcv, sf_ot (hG.ot_v c hcM)] at hσ
        have hsv : s = ρ.v c := (T.psi.inj hσ).1
        rw [← hsv, hs, cof_of_isSucc (isSucc_succ μ)] at hvv
        cases hvv
    · have hμs := (cof_psi_inv hy hcc).2
      have hyot : isOT y = true := isOT_arg hcot
      unfold step
      split
      · rcases last_H (s := s) hy hyot (isOT_sub hcot) with h | ⟨h, hlo⟩
        · rw [h]; intro he; exact hy (T.psi.inj he).2.1
        · rw [h]
          intro he
          have hyall : ∀ q ∈ summands y, ¬ q < psi (succ s) z z := by
            intro q hq
            have e := split_app (psi (succ s) z z) y
            rw [hlo, app_z_right] at e
            rw [← e] at hq
            exact split_fst_ge _ y q hq
          apply hyall _ (last_mem hy)
          rw [he, psi_lt_psi_z_iff]
          left
          rw [lt_succ_iff]; exact succ_le_of_lt (show μ < s from hμs)
      · rw [last_add_single]; intro he; exact hy (T.psi.inj he).2.1

end

/-! ## 鎖の下限 ψ_μ(Ω_{μ+1}) -/

/-- **A standard term with cofinality `Ω_{μ+1}` has its head at least `Ω_{μ+1}`.** -/
theorem om_le_head_of_cof : ∀ {t μ : T}, isOT t = true → cof t = .big μ → psi (succ μ) z z ≤ head t
  | z, _, _, h => by simp [cof] at h
  | psi a b (psi c d e), μ, hot, h => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    have ih := om_le_head_of_cof (isOT_rest hot) h'
    have h4 := (isOT_psi_iff.mp hot).2.2.2.1
    exact le_trans ih h4
  | psi a b z, μ, hot, h => by
    show psi (succ μ) z z ≤ psi a b z
    unfold cof at h
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h
      by_cases ha : a = z
      · rw [if_pos ha] at h; cases h
      · rw [if_neg ha] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs] at h; cases h
          have : succ (init a) = a := by unfold succ; exact init_app_one hs
          rw [this]
        · rw [if_neg hs] at h
          have ih := om_le_head_of_cof (isOT_sub hot) h
          have hμa : μ < a := lt_of_lt_of_le (lt_trans' (lt_succ_self μ) (sub_lt _ z z))
            (le_trans ih (head_le_self a))
          exact le_psi_sub (succ_le_of_lt hμa)
    · rw [if_neg hb] at h
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h
        cases hcb : cof b with
        | big μ' =>
          rw [hcb] at h; simp only at h
          split at h
          · rename_i hlt
            cases h
            exact le_trans (le_psi_sub (succ_le_of_lt hlt)) (le_psi_arg (z_le b))
          · cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- **`fs` stays above the level.** -/
theorem lt_fs_of_cof : ∀ {t μ η : T}, isOT t = true → cof t = .big μ → μ < η → μ < fs t η
  | z, _, _, _, h, _ => by simp [cof] at h
  | psi a b (psi c d e), μ, η, hot, h, _ => by
    show μ < psi a b (fs (psi c d e) η)
    have hh := om_le_head_of_cof hot h
    exact lt_of_lt_of_le (lt_trans' (lt_succ_self μ) (sub_lt _ z z))
      (le_trans hh (le_psi_rest (z_le _)))
  | psi a b z, μ, η, hot, h, hη => by
    unfold cof at h
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h
      by_cases ha : a = z
      · rw [if_pos ha] at h; cases h
      · rw [if_neg ha] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs] at h; cases h
          unfold fs; rw [if_pos rfl, if_neg ha, if_pos hs]; exact hη
        · rw [if_neg hs] at h
          unfold fs; rw [if_pos rfl, if_neg ha, if_neg hs]
          exact lt_trans' (lt_fs_of_cof (isOT_sub hot) h hη) (lt_Om_self _)
    · rw [if_neg hb] at h
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h
        cases hcb : cof b with
        | big μ' =>
          rw [hcb] at h; simp only at h
          split at h
          · rename_i hlt
            cases h
            unfold fs; rw [if_neg hb, if_neg hs, hcb]; simp only; rw [if_pos hlt]
            exact lt_trans' hlt (sub_lt _ _ _)
          · cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- **`fs` stays at least `Ω_{μ+1}`** unless the term ends with `Ω_{μ+1}`. -/
theorem om_le_fs : ∀ {t μ η : T}, isOT t = true → cof t = .big μ → last t ≠ psi (succ μ) z z →
    μ < η → psi (succ μ) z z ≤ fs t η
  | z, _, _, _, h, _, _ => by simp [cof] at h
  | psi a b (psi c d e), μ, η, hot, h, _, _ => by
    show psi (succ μ) z z ≤ psi a b (fs (psi c d e) η)
    exact le_trans (om_le_head_of_cof hot h) (le_psi_rest (z_le _))
  | psi a b z, μ, η, hot, h, hl, hη => by
    unfold cof at h
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h
      by_cases ha : a = z
      · rw [if_pos ha] at h; cases h
      · rw [if_neg ha] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs] at h; cases h
          exfalso; apply hl
          show psi a z z = _
          have : succ (init a) = a := by unfold succ; exact init_app_one hs
          rw [this]
        · rw [if_neg hs] at h
          unfold fs; rw [if_pos rfl, if_neg ha, if_neg hs]
          exact le_psi_sub (succ_le_of_lt (lt_fs_of_cof (isOT_sub hot) h hη))
    · rw [if_neg hb] at h
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h
        cases hcb : cof b with
        | big μ' =>
          rw [hcb] at h; simp only at h
          split at h
          · rename_i hlt
            cases h
            unfold fs; rw [if_neg hb, if_neg hs, hcb]; simp only; rw [if_pos hlt]
            exact le_trans (le_psi_sub (succ_le_of_lt hlt)) (le_psi_arg (z_le _))
          · cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- **The chain stays at least `ψ_μ(Ω_{μ+1})`** (given the seed does). -/
theorem gamS_ge_omfix {μ br seed : T} (hot : isOT br = true) (hcb : cof br = .big μ)
    (hbrl : last br ≠ psi (succ μ) z z) (hseed : psi μ (psi (succ μ) z z) z ≤ seed) :
    ∀ m, psi μ (psi (succ μ) z z) z ≤ gamS μ br seed m
  | 0 => hseed
  | m + 1 => by
    show psi μ (psi (succ μ) z z) z ≤ psi μ (fs br (gamS μ br seed m)) z
    apply le_psi_arg
    apply om_le_fs hot hcb hbrl
    exact lt_of_lt_of_le (sub_lt μ _ z) (gamS_ge_omfix hot hcb hbrl hseed m)

/-! ## まとめ: (W)・(L) を TP1・TPL から -/

/-- **`t = 1`, `q ≠ r`, all `n ≥ 2`**: `t1_main_val` with (W) and (L) replaced by the value invariants
TP1 and TPL and the lower bound `ψ_μ(Ω_{μ+1}) ≤ seed` of the seed. -/
theorem t1_main_tpl {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmall M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hTP : TP1 M ρ) (hTPL : TPL M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbs M ρ) (hWS : BumpWeakShape M ρ)
    (hVSt : BumpVSmallTake M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbs M ρ)
    (hne : (drop1 M (r + L) rkM).o r ≠ ρ.o r)
    {μ br vr : T} (hμr : μ = vr) (hro : ρ.o r = psi vr br z)
    (hseedΩ : psi μ (psi (succ μ) z z) z ≤ (drop1 M (r + L) rkM).o r)
    (hV : ∀ m i, i < r + L → DepX M (r + L) false i →
      VLocal M (r + L) ρ (gamS μ br ((drop1 M (r + L) rkM).o r) m) μ i)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r < r + L := by omega
  have hrM : r < M.length := by omega
  have hvr : ρ.v r = vr := by
    obtain ⟨y0, hy0⟩ := o_psi_sub hC hrM
    rw [hro] at hy0; simp only [psi.injEq] at hy0
    rw [hy0.1, sf_ot (hG.ot_v r hrM)]
  have hF1 : ∀ i, r < i → i < r + L → DepX M (r + L) true i → ¬ DepX M (r + L) false i →
      lt μ (ρ.v i) = true := by
    intro i h2 h3 h4 h5
    rw [hμr, ← hvr]
    exact hF1_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hC hG hRM i h2 h3 h4 h5
  have hox : ρ.o (r + L) = psi (succ μ) z z := by
    rw [o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2, hvr, hμr]
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq
  obtain ⟨hcb, hbr⟩ := hcb_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hox hF1 hOS (hV 0) h1 hx2 hqr
    hR12 hBE hro
  have hbrl := last_br_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hox hF1 hOS (hV 0) h1 hx2 hqr
    hR12 hBE hro
  have hrot : isOT (psi vr br z) = true := by rw [← hro]; exact hG.ot_o r hrM
  have hζΩ := gamS_ge_omfix (isOT_arg hrot) hcb hbrl hseedΩ
  have hLo := hLo_of_TPL hlen hC hG hrx hA hro hcb hμr hbr hox hF1 hOS (hV 0)
    (hS2_t1 hR0 hA (by omega)) (hS3_t1 h1 hA (by omega) hlen hR0 hZ2 hSD hZ1) hTPL hbrl hζΩ
  exact t1_main_tp1 hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hqr hC hG hRM
    hVS hF hFO hTP hArgT hKD hTD hAbs hWS hVSt hUA hne hμr hro hV hLo hsM hpM

end Ytosk
