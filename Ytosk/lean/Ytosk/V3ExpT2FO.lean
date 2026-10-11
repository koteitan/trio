/-
**3 行・t = 2: 数える子の枠の性質を M[n] へ運ぶ骨組み（`clField_expand_t2`）と FrameOT。**

枠の性質 Q a Lv cv（a = v(i)、Lv = 前の数える子の値、cv = その子の値）について、
- 写しの枠: P の枠から σ で（`hQσ`: Q は σ で保たれる）。
- x より前の種でない列: `FrameShape` で M の枠と同じか、最後の子だけ ◁ で下がる（`hQlow`）。
- 種の列（`T2SeedCol`）の枠: 残り。
- M[1] = M.take x の枠: 接頭辞の不変条件から。
-/
import Ytosk.V3ExpT2CG
import Ytosk.V3ExpT2BA

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- A property of all counted frames of a matrix. -/
def CLField (Q : T → List T → T → Prop) (N : Mat) (σ : Valn) : Prop :=
  ∀ i, i < N.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N i = Lc ++ c :: R →
    Q (σ.v i) (Lc.map σ.o) (σ.o c)

theorem clField_congr {Q : T → List T → T → Prop} {N : Mat} {σ τ : Valn} (h : CLField Q N σ)
    (hA : Agree N σ τ) : CLField Q N τ := by
  intro i hi Lc c R hCL
  have hcN : ∀ d ∈ CL N i, d < N.length := fun d hd => (mem_children (cl_mem_children hd)).2
  have hcl : c < N.length := hcN c (by rw [hCL]; simp)
  have hLc : Lc.map τ.o = Lc.map σ.o := List.map_congr_left (fun d hd =>
    ((hA d (hcN d (by rw [hCL]; exact List.mem_append_left _ hd))).1).symm)
  rw [← (hA i hi).2, hLc, ← (hA c hcl).1]
  exact h i hi Lc c R hCL

/-- **The copy frames** from those of `P`, for a `σ`-invariant property. -/
theorem clField_copy {Q : T → List T → T → Prop}
    (hQσ : ∀ (V V' a : T) (Lv : List T) (cv : T), isOT V = true → isOT V' = true → V < V' →
      isOT a = true → V ≤ a → (∀ t ∈ Lv ++ [cv], Single t) →
      (Lv ++ [cv]).Pairwise (fun a b => b ≤ a) → (V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) →
      Q a Lv cv → Q (shf V V' a) (Lv.map (sh V V')) (sh V V' cv))
    {N P : Mat} {σ ρ : Valn} {r L : Nat} {V' : T} {g : Nat → Prop}
    (hF : CopyFacts N P σ ρ r L V' g) (hCP : Cons P ρ) (hGP : Good3 P ρ) (hrP : r < P.length)
    (hV' : isOT V' = true) (hVV : ρ.v r < V') (hQP : CLField Q P ρ) :
    ∀ i, r ≤ i → i < P.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N (i + L) = Lc ++ c :: R →
      Q (σ.v (i + L)) (Lc.map σ.o) (σ.o c) := by
  set V := ρ.v r with hVdef
  have hVo : isOT V = true := hGP.ot_v r hrP
  intro i hri hi Lc c R h
  obtain ⟨hcl, hgc, hngc⟩ := hF i hri hi
  rw [hcl] at h
  obtain ⟨Lc0, rest, hsplit, hLc, hrest⟩ := List.map_eq_append_iff.mp h
  obtain ⟨c0, R0, hrest0, hc, _⟩ := List.map_eq_cons_iff.mp hrest
  rw [hrest0] at hsplit
  have hQ := hQP i hi Lc0 c0 R0 hsplit
  subst hLc; subst hc
  obtain ⟨hsM, hpM⟩ := cl_vals hCP hGP hi
  rw [hsplit] at hsM hpM
  have hmem : ∀ d ∈ Lc0 ++ [c0], d ∈ CL P i := fun d hd => by
    rw [hsplit]
    rcases List.mem_append.mp hd with h | h
    · exact List.mem_append_left _ h
    · simp at h; rw [h]; simp
  have hS' : ∀ t ∈ Lc0.map ρ.o ++ [ρ.o c0], Single t := fun t ht => by
    apply hsM
    rw [List.map_append, List.map_cons]
    rcases List.mem_append.mp ht with h | h
    · exact List.mem_append_left _ h
    · simp at h; rw [h]; simp
  have hP' : (Lc0.map ρ.o ++ [ρ.o c0]).Pairwise (fun a b => b ≤ a) := by
    rw [List.map_append, List.map_cons] at hpM
    have h1 := List.pairwise_append.mp hpM
    refine List.pairwise_append.mpr ⟨h1.1, by simp, fun a ha b hb => ?_⟩
    simp at hb; rw [hb]; exact h1.2.2 a ha _ (by simp)
  rw [List.map_map]
  by_cases hg : g i
  · obtain ⟨hv, hVi, hlt, hd⟩ := hgc hg
    have hmap : Lc0.map (σ.o ∘ (· + L)) = (Lc0.map ρ.o).map (sh V V') := by
      rw [List.map_map]; apply List.map_congr_left; intro d hd'
      exact (hd d (hmem d (List.mem_append_left _ hd'))).1
    rw [hv, hmap, (hd c0 (hmem c0 (by simp))).1]
    apply hQσ V V' (ρ.v i) (Lc0.map ρ.o) (ρ.o c0) hVo hV' hVV (hGP.ot_v i hi) hVi hS' hP' _ hQ
    rcases Nat.lt_or_ge r i with h1 | h1
    · exact Or.inl (hlt h1)
    · have hir : i = r := by omega
      right
      intro t ht
      have hdl : ∀ d ∈ Lc0 ++ [c0], V < lev (ρ.o d) := by
        intro d hd'
        have hdC := hmem d hd'
        obtain ⟨y', hy'⟩ := o_form hCP hGP (mem_children (cl_mem_children hdC)).2
        rw [hy']; exact (hd d hdC).2 hir
      rcases List.mem_append.mp ht with h | h
      · obtain ⟨d, hd', rfl⟩ := List.mem_map.mp h
        exact hdl d (List.mem_append_left _ hd')
      · simp at h; rw [h]; exact hdl c0 (by simp)
  · obtain ⟨hv, hd⟩ := hngc hg
    have hmap : Lc0.map (σ.o ∘ (· + L)) = Lc0.map ρ.o := by
      apply List.map_congr_left; intro d hd'; exact hd d (hmem d (List.mem_append_left _ hd'))
    rw [hv, hmap, hd c0 (hmem c0 (by simp))]
    exact hQ

/-- **A frame of `N` before `x` from its shape against `M`.** -/
theorem clField_of_shape {Q : T → List T → T → Prop}
    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → Q a Lv cv')
    {M N : Mat} {ρ σ : Valn} {i : Nat} (hS : FrameShape M N ρ σ i)
    (hQ : ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → Q (ρ.v i) (Lc.map ρ.o) (ρ.o c)) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N i = Lc ++ c :: R → Q (σ.v i) (Lc.map σ.o) (σ.o c) := by
  intro Lc c R hCL
  rcases hS with ⟨hv, hcl, hsame⟩ | ⟨hv, Lc0, c0, hclM, hclN, hsame, hl, hot, _⟩ | ⟨hN, _⟩
  · rw [hcl] at hCL
    have hmem : ∀ d ∈ Lc ++ [c], d ∈ CL M i := fun d hd => by
      rw [hCL]
      rcases List.mem_append.mp hd with h | h
      · exact List.mem_append_left _ h
      · simp at h; rw [h]; simp
    rw [hv, List.map_congr_left (fun d hd => hsame d (hmem d (List.mem_append_left _ hd))),
      hsame c (hmem c (by simp))]
    exact hQ Lc c R hCL
  · rw [hclN] at hCL
    by_cases hR : R = []
    · rw [hR] at hCL
      obtain ⟨h1, h2⟩ := List.append_inj' hCL rfl
      simp only [List.cons.injEq, and_true] at h2
      subst h1; subst h2
      rw [hv, List.map_congr_left hsame]
      exact hQlow _ _ _ _ (hQ Lc0 c0 [] hclM) hl hot
    · have hdl : (Lc ++ c :: R).dropLast = Lc0 := by rw [← hCL]; simp
      rw [List.dropLast_append_of_ne_nil (by simp)] at hdl
      have hLs : ∀ d ∈ Lc, d ∈ Lc0 := fun d hd => by rw [← hdl]; exact List.mem_append_left _ hd
      have hcs : c ∈ Lc0 := by
        rw [← hdl]
        apply List.mem_append_right
        obtain ⟨r0, rs, rfl⟩ := List.exists_cons_of_ne_nil hR
        simp
      have hclM' : CL M i = Lc ++ c :: R := by rw [hclM, hCL]
      rw [hv, List.map_congr_left (fun d hd => hsame d (hLs d hd)), hsame c hcs]
      exact hQ Lc c R hclM'
  · rw [hN] at hCL; simp at hCL

end Ytosk

namespace Ytosk

open T Classical

/-- The residual of a frame property at the seed columns of `M[n]`. -/
def T2SeedFrames (Q : T → List T → T → Prop) (M : Mat) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n) σ →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ∀ i, T2SeedCol M r L i → ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
        CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) i =
          Lc ++ c :: R → Q (σ.v i) (Lc.map σ.o) (σ.o c)

/-- **A counted-frame property of every `M[n]`** (`t = 2`, `n ≥ 1`), from its `σ`-invariance, its stability
under lowering the last child by `◁`, the frames of `M` and `M.take x`, and the seed frames. -/
theorem clField_expand_t2 {Q : T → List T → T → Prop}
    (hQσ : ∀ (V V' a : T) (Lv : List T) (cv : T), isOT V = true → isOT V' = true → V < V' →
      isOT a = true → V ≤ a → (∀ t ∈ Lv ++ [cv], Single t) →
      (Lv ++ [cv]).Pairwise (fun a b => b ≤ a) → (V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) →
      Q a Lv cv → Q (shf V V' a) (Lv.map (sh V V')) (sh V V' cv))
    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → Q a Lv cv')
    (hB : T2BelowXRes) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3 M ρ rk) (R : Res3A M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hQM : CLField Q M ρ)
    (hQT : ∀ τ, Cons (M.take (M.length - 1)) τ → CLField Q (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames Q M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → CLField Q (expand M n) σ := by
  have hGall := good3_expand_t2 hM hS I R hz h2 (t2BelowXAll_of hB M ρ rk hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  rw [hL] at hr hQT
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  have hd1 : 0 < d1 := by omega
  have hexp : ∀ n, expand M n = TRIO.gexp M r L d0 d1 n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hG : ∀ m, 1 ≤ m → ∀ σ, Cons (TRIO.gexp M r L d0 d1 m) σ → Good3 (TRIO.gexp M r L d0 d1 m) σ :=
    fun m hm σ hσ => by rw [← hexp m] at hσ ⊢; exact hGall m hm σ hσ
  have hRk : ∀ m, 1 ≤ m → ∃ rk, Rk (TRIO.gexp M r L d0 d1 m) rk := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hBE : ∀ m, 1 ≤ m → BumpE2 (TRIO.gexp M r L d0 d1 m) := fun m _ => by
    rw [← hexp m]; exact (sInvX_expand hX m).loc.2.2.1
  have hCR := t2CopyResAll_holds M ρ rk hM hS I R hz h2 r L hlen hr
  have hBS := t2BelowXS_of hB hM hS I R hz h2 hlen hr
  have hSD := hX.loc.1
  have key : ∀ n, 1 ≤ n → ∀ σ, Cons (TRIO.gexp M r L d0 d1 n) σ → CLField Q (TRIO.gexp M r L d0 d1 n) σ := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        intro σ hσ
        rw [gexp_one_gen hlen] at hσ ⊢
        exact hQT σ hσ
      · intro σ hCN
        have hn2 : 2 ≤ m + 1 := by omega
        obtain ⟨rkP, hRP⟩ := hRk m hm0
        have hCP : Cons (TRIO.gexp M r L d0 d1 m) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
        have hGP := hG m hm0 _ hCP
        have hQP := ih hm0 _ hCP
        have hm : m + 1 - 1 = m := by omega
        obtain ⟨hKV, hB', hV', hVV⟩ := hCR (m + 1) hn2 σ _ hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP)
        have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
        have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r hX.r0p hSD
        have hF := copy_facts_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
          hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP) (by rw [hm]; exact hRP) hK hKV hRK hB' hV' hVV
        rw [hm] at hF
        have hlN : (TRIO.gexp M r L d0 d1 (m + 1)).length = r + (m + 1) * L := TRIO.gexp_length hlen
        have hlP : (TRIO.gexp M r L d0 d1 m).length = r + m * L := TRIO.gexp_length hlen
        have hmL : (m + 1) * L = m * L + L := Nat.succ_mul m L
        have hrP : r < (TRIO.gexp M r L d0 d1 m).length := by
          have : L ≤ m * L := Nat.le_mul_of_pos_left L hm0
          omega
        have hcopy := clField_copy hQσ hF hCP hGP hrP hV' hVV hQP
        have hGN := hG (m + 1) (by omega) σ hCN
        intro i hi Lc c R hCL
        rcases Nat.lt_or_ge i (r + L) with hix | hix
        · by_cases hsc : T2SeedCol M r L i
          · exact hSeed r L hlen hr (m + 1) hn2 σ hCN hGN i hsc Lc c R hCL
          · have hsh := (hBS (m + 1) hn2 (by rw [hm]; exact hG m hm0) σ hCN (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) i hix).2.2.2.1 hsc
            exact clField_of_shape hQlow hsh (fun Lc c R h => hQM i (by omega) Lc c R h) Lc c R hCL
        · obtain ⟨a, rfl⟩ : ∃ a, i = r + a + L := ⟨i - L - r, by omega⟩
          exact hcopy (r + a) (by omega) (by omega) Lc c R hCL
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact key n hn σ hσ

end Ytosk

namespace Ytosk

open T Classical

/-- The frame property of `FrameOT`. -/
abbrev QFO (a : T) (Lv : List T) (_cv : T) : Prop := isOT (psi a (spArg a z (sumN Lv)) z) = true

theorem frameOT_iff {N : Mat} {σ : Valn} : FrameOT N σ ↔ CLField QFO N σ := Iff.rfl

/-- `FrameOT`'s frame property moves with `σ`. -/
theorem qFO_sh (V V' a : T) (Lv : List T) (cv : T) (hV : isOT V = true) (hV' : isOT V' = true)
    (hVV : V < V') (ha : isOT a = true) (hVa : V ≤ a) (hs : ∀ t ∈ Lv ++ [cv], Single t)
    (hp : (Lv ++ [cv]).Pairwise (fun a b => b ≤ a)) (hlev : V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t)
    (hQ : QFO a Lv cv) : QFO (shf V V' a) (Lv.map (sh V V')) (sh V V' cv) := by
  have hLs : ∀ t ∈ Lv, Single t := fun t ht => hs t (List.mem_append_left _ ht)
  have hLp : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp).1
  obtain ⟨hSot, hSsum⟩ := sumN_dec Lv hLs hLp
  have hlev' : V < a ∨ ∀ q ∈ summands (sumN Lv), lev q ≠ V := by
    rcases hlev with h | h
    · exact Or.inl h
    · right; rw [hSsum]; intro q hq; exact ne_of_gt (h q (List.mem_append_left _ hq))
  show isOT (psi (shf V V' a) (spArg (shf V V' a) z (sumN (Lv.map (sh V V')))) z) = true
  rw [← sh_sumN hV hV' hVV (fun t ht => (hLs t ht).1)]
  have hsp := sh_spArg hV hV' hVV ha hVa (b := z) rfl hSot hlev'
  rw [sh_z] at hsp
  rw [hsp]
  exact isOT_shTop hV hV' hVV hQ hVa

/-- **`FrameOT` of every `M[n]`** (`t = 2`), from `FrameOT` of `M` and `M.take x` and the seed frames. -/
theorem frameOT_expand_t2 (hB : T2BelowXRes) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → FrameOT (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QFO M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → FrameOT (expand M n) σ :=
  clField_expand_t2 qFO_sh (fun _ _ _ _ h _ _ => h) hB hM hS I R hz h2 I.fo hT hSeed

end Ytosk
