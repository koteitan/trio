/-
**RwClosed の写しの枠を ClSh なしで（2026-10-17、t0）。**

ClSh は項の主張として偽（V3RwClSh の冒頭）。写しの枠で前提（書き換えて B < hi(y)、B が hi(y) の先頭部分でない）が
立つときに、V・V′・a の支配の条件 `SubstDom` を残りにする。a = V なら f(a) = V′ で、要るのは `VDom V V′` だけ
（`substDom_of_vDom`）。
- `CopyCutK V V′ a Lv cv`: 前提が立てば SubstDom V V′ a。
- t2 の骨組み clField_copy・clField_expand_t2S を、枠ごとの条件 K を受け取る形に写した
  （`clField_copyK`・`clField_expand_t2SK`、残り `T2CopyK K M`）。
- `qRCo_shK`: qRCo_sh の ClSh を CopyCutK に替えたもの（closedA_sh・substDom_self）。
-/
import Ytosk.V3RwClSh
import Ytosk.V3RwClSeed

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- **The relation of `V` and `V′`** used at the copy frames: the nonzero components of `V` at a level `u′ ≤ V`,
moved by `σ`, are below components of `V′` at `u′`. -/
def VDom (V V' : T) : Prop :=
  ∀ u', ¬ lt V' u' = true → ∀ d ∈ comps (if u' ≤ V then u' else V) V,
    d = z ∨ ∃ d' ∈ comps u' V', sh V V' d ≤ d'

/-- **The condition at a copy frame**: if the premise of `QRC` holds, then `SubstDom V V′ a`. -/
def CopyCutK (V V' a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true →
    spArg a z (sumN Lv) < (split y (psi (succ s) z z)).1 →
    (¬ ∃ R', (split y (psi (succ s) z z)).1 = app (spArg a z (sumN Lv)) R') → SubstDom V V' a

/-- `a = V` and `VDom V V′` give `SubstDom V V′ a`. -/
theorem substDom_of_vDom {V V' a : T} (ha : a = V) (h : VDom V V') : SubstDom V V' a := by
  subst ha; exact substDom_self h

/-- **Residual: the condition `K` at the guarded copy frames** of every `M[n]` (`t = 2`), with
`V = v_P(r)` and `V′ = v_N(r + L)` (`P = M[n − 1]`, `N = M[n]`). -/
def T2CopyK (K : T → T → T → List T → T → Prop) (M : Mat) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ n, 2 ≤ n → ∀ σ ρ,
    Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
    Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρ →
    Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρ →
    ∀ i, r ≤ i → i < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r)
      (n - 1)).length →
    TRIO.le1 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) r i →
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
      CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) i =
        Lc ++ c :: R →
      K (ρ.v r) (σ.v (r + L)) (ρ.v i) (Lc.map ρ.o) (ρ.o c)

theorem clField_copyK {Q : T → List T → T → Prop} {K : T → T → T → List T → T → Prop}
    (hQσ : ∀ (V V' a : T) (Lv : List T) (cv : T), isOT V = true → isOT V' = true → V < V' →
      isOT a = true → V ≤ a → (∀ t ∈ Lv ++ [cv], Single t) →
      (Lv ++ [cv]).Pairwise (fun a b => b ≤ a) → (V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) →
      K V V' a Lv cv → Q a Lv cv → Q (shf V V' a) (Lv.map (sh V V')) (sh V V' cv))
    {N P : Mat} {σ ρ : Valn} {r L : Nat} {V' : T} {g : Nat → Prop}
    (hF : CopyFacts N P σ ρ r L V' g) (hCP : Cons P ρ) (hGP : Good3 P ρ) (hrP : r < P.length)
    (hV' : isOT V' = true) (hVV : ρ.v r < V') (hQP : CLField Q P ρ)
    (hK : ∀ i, r ≤ i → i < P.length → g i → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL P i = Lc ++ c :: R →
      K (ρ.v r) V' (ρ.v i) (Lc.map ρ.o) (ρ.o c)) :
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
    apply hQσ V V' (ρ.v i) (Lc0.map ρ.o) (ρ.o c0) hVo hV' hVV (hGP.ot_v i hi) hVi hS' hP' _
      (hK i hri hi hg Lc0 c0 R0 hsplit) hQ
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


theorem clField_expand_t2SK {Q : T → List T → T → Prop} {K : T → T → T → List T → T → Prop}
    (hQσ : ∀ (V V' a : T) (Lv : List T) (cv : T), isOT V = true → isOT V' = true → V < V' →
      isOT a = true → V ≤ a → (∀ t ∈ Lv ++ [cv], Single t) →
      (Lv ++ [cv]).Pairwise (fun a b => b ≤ a) → (V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) →
      K V V' a Lv cv → Q a Lv cv → Q (shf V V' a) (Lv.map (sh V V')) (sh V V' cv))
    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → (∃ s y, cv = psi s y z) →
      (∀ s y s' y', cv = psi s y z → cv' = psi s' y' z → s' ≠ s → y' = z) → Q a Lv cv')
    (hB : T2BelowXRes) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hQM : CLField Q M ρ)
    (hQT : ∀ τ, Cons (M.take (M.length - 1)) τ → CLField Q (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames Q M) (hKM : T2CopyK K M) :
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
        have hcopy := clField_copyK hQσ hF hCP hGP hrP hV' hVV hQP (by
          intro i hri hi hg Lc c R hCL
          have := hKM r L hlen hr (m + 1) hn2 σ _ hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP) i hri
            (by rw [hm]; exact hi) (by rw [hm]; exact hg) Lc c R (by rw [hm]; exact hCL)
          exact this)
        have hGN := hG (m + 1) (by omega) σ hCN
        intro i hi Lc c R hCL
        rcases Nat.lt_or_ge i (r + L) with hix | hix
        · by_cases hsc : T2SeedCol M r L i
          · exact hSeed r L hlen hr (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN hGN i hsc Lc c R hCL
          · have hsh := (hBS (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) i hix).2.2.2.1 hsc
            exact clField_of_shapeS hQlow I.cons I.good hCN hGN hsh (fun Lc c R h => hQM i (by omega) Lc c R h)
              Lc c R hCL
        · obtain ⟨a, rfl⟩ : ∃ a, i = r + a + L := ⟨i - L - r, by omega⟩
          exact hcopy (r + a) (by omega) (by omega) Lc c R hCL
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact key n hn σ hσ

theorem qRCo_shK (V V' a : T) (Lv : List T) (cv : T) (hV : isOT V = true)
    (hV' : isOT V' = true) (hVV : V < V') (ha : isOT a = true) (hVa : V ≤ a)
    (hs : ∀ t ∈ Lv ++ [cv], Single t) (hp : (Lv ++ [cv]).Pairwise (fun a b => b ≤ a))
    (hlev : V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) (hK : CopyCutK V V' a Lv cv) (hQ : QRCo a Lv cv) :
    QRCo (shf V V' a) (Lv.map (sh V V')) (sh V V' cv) := by
  have hLs : ∀ t ∈ Lv, Single t := fun t ht => hs t (List.mem_append_left _ ht)
  have hLp : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp).1
  obtain ⟨hSot, hSsum⟩ := sumN_dec Lv hLs hLp
  have hlev' : V < a ∨ ∀ q ∈ summands (sumN Lv), lev q ≠ V := by
    rcases hlev with h | h
    · exact Or.inl h
    · right; rw [hSsum]; intro q hq; exact ne_of_gt (h q (List.mem_append_left _ hq))
  have hBot : isOT (spArg a z (sumN Lv)) = true := isOT_spArg a (sumN Lv) z rfl hSot
  have hB : spArg (shf V V' a) z (sumN (Lv.map (sh V V'))) = sh V V' (spArg a z (sumN Lv)) := by
    rw [← sh_sumN hV hV' hVV (fun t ht => (hLs t ht).1)]
    have hsp := sh_spArg hV hV' hVV ha hVa (b := z) rfl hSot hlev'
    rw [sh_z] at hsp
    exact hsp
  obtain ⟨hcvot, s, y, hcv⟩ := hs cv (by simp)
  subst hcv
  refine ⟨isOT_sh hV hV' hVV hcvot, ?_⟩
  intro s' y' hcv' ht' hhi' hnp'
  rw [hB] at ht' hhi' hnp' ⊢
  have hVV' : V ≤ V' := le_of_lt hVV
  have hsot : isOT s = true := isOT_sub hcvot
  have hyot : isOT y = true := isOT_arg hcvot
  by_cases hVs : V < s
  · rw [sh_psi_gt hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    have h1 : lt (spArg a z (sumN Lv)) y = true :=
      (sh_lt_iff hV hV' hVV' hBot hyot).mp ht'.1
    have hfa : shf V V' a ≤ shf V V' s := le_of_trig ht'.2
    have has : a ≤ s := by
      rcases (le_iff _ _).mp hfa with h | h
      · exact le_of_lt ((shf_lt_iff hV hV' hVV' ha hsot hVa (le_of_lt hVs)).mp h)
      · rcases lt_trichotomy' a s with h' | h' | h'
        · exact le_of_lt h'
        · rw [h']
        · exact absurd h (ne_of_gt (shf_lt_shf hV hV' hVV' hsot ha (le_of_lt hVs) h'))
    have hyz : y ≠ z := fun h => by rw [h] at h1; exact T.not_lt_z _ h1
    have h2 : lt (psi a z z) (psi s y z) = true := by
      show psi a z z < psi s y z
      rcases (le_iff _ _).mp has with h | h
      · exact psi_lt_psi_z_iff.mpr (Or.inl h)
      · subst h
        exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hyz)⟩)
    -- the premise `B < hi(y)` moves back
    have hsplit := sh_split hV hV' hVV (sh_lt_om_succ hV hV' hVV hsot hVs) hyot
    rw [hsplit] at hhi' hnp'
    have hhiot : isOT (split y (psi (succ s) z z)).1 = true :=
      isOT_app_left (by rw [split_app]; exact hyot)
    have hhi : spArg a z (sumN Lv) < (split y (psi (succ s) z z)).1 :=
      (sh_lt_iff hV hV' hVV' hBot hhiot).mp hhi'
    have hBc : ∀ q ∈ summands (spArg a z (sumN Lv)), psi s y z ≤ q := by
      apply spArg_summands_ge ⟨s, y, rfl⟩ (sumN Lv) z hSot
      · rw [hSsum]; intro q hq
        exact (List.pairwise_append.mp hp).2.2 q hq _ (by simp)
      · simp [summands]
    have hBV : ∀ q ∈ summands (spArg a z (sumN Lv)), V < lev q := by
      intro q hq
      exact lt_of_lt_of_le hVs (lev_le_of_le (hBc q hq))
    have hnp : ¬ ∃ R', (split y (psi (succ s) z z)).1 = app (spArg a z (sumN Lv)) R' := by
      rintro ⟨R', hR'⟩
      exact hnp' ⟨sh V V' R', by simp only; rw [hR', sh_app]⟩
    have hBa : ∀ q ∈ summands (spArg a z (sumN Lv)), a ≤ lev q := fun q hq =>
      le_trans has (lev_le_of_le (hBc q hq))
    have hD : SubstDom V V' a := hK s y rfl ⟨h1, h2⟩ hhi hnp
    exact closedA_sh hV hV' hVV' ha hVa hBot hD (hQ.2 s y rfl ⟨h1, h2⟩ hhi hnp)
  · rw [sh_psi_le hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    exfalso
    have hlt : s < shf V V' a :=
      lt_of_le_of_lt (le_of_not_gt hVs) (lt_of_lt_of_le hVV (le_shf hV hV' hVV' ha hVa))
    have := le_of_trig ht'.2
    exact lt_irrefl' _ (lt_of_lt_of_le hlt this)

/-- **RwClosed of every `M[n]`** (`t = 2`, `n ≥ 1`) without `ClSh`: the copy frames by `T2CopyK CopyCutK`. -/
theorem rwClosed_expand_t2K (hB : T2BelowXRes) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hRM : RwClosed M ρ)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → RwClosed (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QRC M) (hK : T2CopyK CopyCutK M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → RwClosed (expand M n) σ := by
  have hl : 1 ≤ M.length := by
    rcases Nat.eq_zero_or_pos M.length with h | h
    · exfalso; apply hz; rw [h]
      have : M = [] := List.eq_nil_of_length_eq_zero h
      subst this; rfl
    · exact h
  have hSeed' : T2SeedFrames QRCo M := by
    intro r L hlen hr n hn hGm σ hCN hGN i hsc Lc c R hCL
    have hcN := (mem_children (cl_mem_children (show c ∈ CL _ i by rw [hCL]; simp))).2
    exact ⟨hGN.ot_o c hcN, hSeed r L hlen hr n hn hGm σ hCN hGN i hsc Lc c R hCL⟩
  have key := clField_expand_t2SK (K := CopyCutK) (fun V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hK hQ =>
      qRCo_shK V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hK hQ) qRCo_low hB hM hS I R hz h2
    (clField_QRCo I.good hRM) (fun τ hτ => clField_QRCo (good3_take_any I R hl hτ) (hT τ hτ))
    hSeed' hK
  exact fun n hn σ hσ => rwClosed_of_QRCo (key n hn σ hσ)

/-- **RwClosed of every `M[n]`** (`t = 2`) with the residuals `T2CopyK CopyCutK` (copy frames), `T2X1Cl` and
`T2SeedPRes` (seed frames), `T2BelowXRes`. -/
theorem rwClosed_expand_t2SK (hB : T2BelowXRes) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hRM : RwClosed M ρ)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → RwClosed (M.take (M.length - 1)) τ)
    (hX1 : G.T2X1Cl M ρ) (hRes : G.T2SeedPRes M ρ) (hK : T2CopyK CopyCutK M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → RwClosed (expand M n) σ :=
  rwClosed_expand_t2K hB hM hS I R hz h2 hRM hT (G.seed_frames_RC hM hS I R hRM hz h2 hT hX1 hRes) hK


/-! ## 閉じた枠と V′ の支配に分けた形（共有の値の条件 VDomF） -/

/-- **The copy-frame condition, split**: at the premise, the state is closed at all levels `≤ a`, and `VDomF`. -/
def CopyCutL (V V' a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true →
    spArg a z (sumN Lv) < (split y (psi (succ s) z z)).1 →
    (¬ ∃ R', (split y (psi (succ s) z z)).1 = app (spArg a z (sumN Lv)) R') →
    ClosedLow a (spArg a z (sumN Lv)) ∧ VDomF V V' a

/-- The `P`-side part: at the premise, the state is closed at all levels `≤ a`. -/
def CopyLowK (_V _V' a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true →
    spArg a z (sumN Lv) < (split y (psi (succ s) z z)).1 →
    (¬ ∃ R', (split y (psi (succ s) z z)).1 = app (spArg a z (sumN Lv)) R') →
    ClosedLow a (spArg a z (sumN Lv))

/-- The value part: `VDomF` (shared with VSmallRAll and FrameDom). -/
def CopyVDomK (V V' a : T) (_Lv : List T) (_cv : T) : Prop := VDomF V V' a

theorem t2CopyK_mono {K K' : T → T → T → List T → T → Prop} (h : ∀ V V' a Lv cv, K V V' a Lv cv → K' V V' a Lv cv)
    {M : Mat} (hK : T2CopyK K M) : T2CopyK K' M :=
  fun r L hlen hr n hn σ ρ hσ hρ hG i hri hi hg Lc c R hCL =>
    h _ _ _ _ _ (hK r L hlen hr n hn σ ρ hσ hρ hG i hri hi hg Lc c R hCL)

theorem t2CopyK_and {M : Mat} (h1 : T2CopyK CopyLowK M) (h2 : T2CopyK CopyVDomK M) : T2CopyK CopyCutL M :=
  fun r L hlen hr n hn σ ρ hσ hρ hG i hri hi hg Lc c R hCL s y hcv ht hhi hnp =>
    ⟨h1 r L hlen hr n hn σ ρ hσ hρ hG i hri hi hg Lc c R hCL s y hcv ht hhi hnp,
     h2 r L hlen hr n hn σ ρ hσ hρ hG i hri hi hg Lc c R hCL⟩

theorem qRCo_shL (V V' a : T) (Lv : List T) (cv : T) (hV : isOT V = true)
    (hV' : isOT V' = true) (hVV : V < V') (ha : isOT a = true) (hVa : V ≤ a)
    (hs : ∀ t ∈ Lv ++ [cv], Single t) (hp : (Lv ++ [cv]).Pairwise (fun a b => b ≤ a))
    (hlev : V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) (hK : CopyCutL V V' a Lv cv) (hQ : QRCo a Lv cv) :
    QRCo (shf V V' a) (Lv.map (sh V V')) (sh V V' cv) := by
  have hLs : ∀ t ∈ Lv, Single t := fun t ht => hs t (List.mem_append_left _ ht)
  have hLp : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp).1
  obtain ⟨hSot, hSsum⟩ := sumN_dec Lv hLs hLp
  have hlev' : V < a ∨ ∀ q ∈ summands (sumN Lv), lev q ≠ V := by
    rcases hlev with h | h
    · exact Or.inl h
    · right; rw [hSsum]; intro q hq; exact ne_of_gt (h q (List.mem_append_left _ hq))
  have hBot : isOT (spArg a z (sumN Lv)) = true := isOT_spArg a (sumN Lv) z rfl hSot
  have hB : spArg (shf V V' a) z (sumN (Lv.map (sh V V'))) = sh V V' (spArg a z (sumN Lv)) := by
    rw [← sh_sumN hV hV' hVV (fun t ht => (hLs t ht).1)]
    have hsp := sh_spArg hV hV' hVV ha hVa (b := z) rfl hSot hlev'
    rw [sh_z] at hsp
    exact hsp
  obtain ⟨hcvot, s, y, hcv⟩ := hs cv (by simp)
  subst hcv
  refine ⟨isOT_sh hV hV' hVV hcvot, ?_⟩
  intro s' y' hcv' ht' hhi' hnp'
  rw [hB] at ht' hhi' hnp' ⊢
  have hVV' : V ≤ V' := le_of_lt hVV
  have hsot : isOT s = true := isOT_sub hcvot
  have hyot : isOT y = true := isOT_arg hcvot
  by_cases hVs : V < s
  · rw [sh_psi_gt hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    have h1 : lt (spArg a z (sumN Lv)) y = true :=
      (sh_lt_iff hV hV' hVV' hBot hyot).mp ht'.1
    have hfa : shf V V' a ≤ shf V V' s := le_of_trig ht'.2
    have has : a ≤ s := by
      rcases (le_iff _ _).mp hfa with h | h
      · exact le_of_lt ((shf_lt_iff hV hV' hVV' ha hsot hVa (le_of_lt hVs)).mp h)
      · rcases lt_trichotomy' a s with h' | h' | h'
        · exact le_of_lt h'
        · rw [h']
        · exact absurd h (ne_of_gt (shf_lt_shf hV hV' hVV' hsot ha (le_of_lt hVs) h'))
    have hyz : y ≠ z := fun h => by rw [h] at h1; exact T.not_lt_z _ h1
    have h2 : lt (psi a z z) (psi s y z) = true := by
      show psi a z z < psi s y z
      rcases (le_iff _ _).mp has with h | h
      · exact psi_lt_psi_z_iff.mpr (Or.inl h)
      · subst h
        exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hyz)⟩)
    -- the premise `B < hi(y)` moves back
    have hsplit := sh_split hV hV' hVV (sh_lt_om_succ hV hV' hVV hsot hVs) hyot
    rw [hsplit] at hhi' hnp'
    have hhiot : isOT (split y (psi (succ s) z z)).1 = true :=
      isOT_app_left (by rw [split_app]; exact hyot)
    have hhi : spArg a z (sumN Lv) < (split y (psi (succ s) z z)).1 :=
      (sh_lt_iff hV hV' hVV' hBot hhiot).mp hhi'
    have hBc : ∀ q ∈ summands (spArg a z (sumN Lv)), psi s y z ≤ q := by
      apply spArg_summands_ge ⟨s, y, rfl⟩ (sumN Lv) z hSot
      · rw [hSsum]; intro q hq
        exact (List.pairwise_append.mp hp).2.2 q hq _ (by simp)
      · simp [summands]
    have hBV : ∀ q ∈ summands (spArg a z (sumN Lv)), V < lev q := by
      intro q hq
      exact lt_of_lt_of_le hVs (lev_le_of_le (hBc q hq))
    have hnp : ¬ ∃ R', (split y (psi (succ s) z z)).1 = app (spArg a z (sumN Lv)) R' := by
      rintro ⟨R', hR'⟩
      exact hnp' ⟨sh V V' R', by simp only; rw [hR', sh_app]⟩
    have hBa : ∀ q ∈ summands (spArg a z (sumN Lv)), a ≤ lev q := fun q hq =>
      le_trans has (lev_le_of_le (hBc q hq))
    obtain ⟨hL, hD⟩ := hK s y rfl ⟨h1, h2⟩ hhi hnp
    exact closedA_sh_low hV hV' hVV' ha hVa hBot hBV hBa hL hD
  · rw [sh_psi_le hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    exfalso
    have hlt : s < shf V V' a :=
      lt_of_le_of_lt (le_of_not_gt hVs) (lt_of_lt_of_le hVV (le_shf hV hV' hVV' ha hVa))
    have := le_of_trig ht'.2
    exact lt_irrefl' _ (lt_of_lt_of_le hlt this)

/-- **RwClosed of every `M[n]`** (`t = 2`, `n ≥ 1`) without `ClSh`: the copy frames by `T2CopyK CopyCutL`. -/
theorem rwClosed_expand_t2L (hB : T2BelowXRes) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hRM : RwClosed M ρ)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → RwClosed (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QRC M) (hK : T2CopyK CopyCutL M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → RwClosed (expand M n) σ := by
  have hl : 1 ≤ M.length := by
    rcases Nat.eq_zero_or_pos M.length with h | h
    · exfalso; apply hz; rw [h]
      have : M = [] := List.eq_nil_of_length_eq_zero h
      subst this; rfl
    · exact h
  have hSeed' : T2SeedFrames QRCo M := by
    intro r L hlen hr n hn hGm σ hCN hGN i hsc Lc c R hCL
    have hcN := (mem_children (cl_mem_children (show c ∈ CL _ i by rw [hCL]; simp))).2
    exact ⟨hGN.ot_o c hcN, hSeed r L hlen hr n hn hGm σ hCN hGN i hsc Lc c R hCL⟩
  have key := clField_expand_t2SK (K := CopyCutL) (fun V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hK hQ =>
      qRCo_shL V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hK hQ) qRCo_low hB hM hS I R hz h2
    (clField_QRCo I.good hRM) (fun τ hτ => clField_QRCo (good3_take_any I R hl hτ) (hT τ hτ))
    hSeed' hK
  exact fun n hn σ hσ => rwClosed_of_QRCo (key n hn σ hσ)

/-- **RwClosed of every `M[n]`** (`t = 2`) with the residuals `T2CopyK CopyLowK` (copy frames of `P`: closed at the premise) and `T2CopyK CopyVDomK` (`VDomF`), `T2X1Cl` and
`T2SeedPRes` (seed frames), `T2BelowXRes`. -/
theorem rwClosed_expand_t2SL (hB : T2BelowXRes) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hRM : RwClosed M ρ)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → RwClosed (M.take (M.length - 1)) τ)
    (hX1 : G.T2X1Cl M ρ) (hRes : G.T2SeedPRes M ρ) (hLow : T2CopyK CopyLowK M) (hVD : T2CopyK CopyVDomK M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → RwClosed (expand M n) σ :=
  rwClosed_expand_t2L hB hM hS I R hz h2 hRM hT (G.seed_frames_RC hM hS I R hRM hz h2 hT hX1 hRes)
    (t2CopyK_and hLow hVD)

end Ytosk
