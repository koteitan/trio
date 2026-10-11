/-
**t = 2・sv（q = r で x − 1 が x へ上げる）の種 r の枠の PH3cG・FC3（closure、2026-10-12）。**

N = M[n] での r の数える子は CL_N(r) = CL_{M.take x}(r) ++ [x′]（t2 の `o_r_level_sv`）。
- x′ より前の枠は M.take x の枠（値は M.take x と同じ）。
- 最後の枠: 状態 X₁（M.take x での r の引数）、子 ψ_{V+1}(σ^{n−1} X₁)。t2 の残り `T2SeedSVRes.rw` で
  どの段でも書き換えて状態が σ X に替わる。PH3cG の種類は前任の `seed_kind`・`seed_ext`（V3PSeedO）から。
  ここで要るのが Fix(X₁): σ X₁ = X₁ か X₁ ∈ cutsNSG (V + 1) (σ X₁)。これが「右端の 1 か所の置き換え」の結論で、
  名前つきの残り `T2SeedSVFix` にした（実測: 5 集合で X₁ はいつも SpotN、加数はすべて Ω_{V+2} 以上、例外 0）。
- FC3: 最後の枠が最初の枠なら X₁ = 0 で、σ(0) = 0 なので書き換えない。
-/
import Ytosk.V3PSeedOG
import Ytosk.V3PSeedQRG
import Ytosk.V3T2SeedSV
import Ytosk.V3PSeedOG

namespace Ytosk.G

open T

set_option linter.unusedSectionVars false

open Classical in
/-- **The data of the seed frames of `r` in `N = M[n]`** (sv): `CL N r = CL (M.take x) r ++ [x]`, the values
before `x` are those of `M.take x`, and `o_N(x) = ψ_{V+1}(σ_{V_P, V+1}(arg of o_P(r)))`. -/
theorem seed_frame_data_sv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (htP : topped (M.take (r + L)) r = false)
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hG0 : Good3 (M.take (r + L)) τ0)
    (hR0 : Rk (M.take (r + L)) rk0) :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r =
        CL (M.take (r + L)) r ++ [r + L] ∧
      σ.v r = τ0.v r ∧ (∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d) ∧
      σ.o (r + L) = psi (succ (ρ.v r)) (sh (ρP.v r) (succ (ρ.v r)) (spArg (ρP.v r) z
        (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1))
          r).map ρP.o)))) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨hcntN, hcntP⟩ := sv_cnt hM hS I hz h2 hlen hr hq hux htP hn
  have hag := sv_agree hM hS I hz h2 hlen hr hq hux htP hn hCN hC0 hR0
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hrM : r < M.length := by omega
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hrT : r < (M.take (r + L)).length := by omega
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  -- the counted children of `r` in `N`
  have hxcN : Counted N r (r + L) := by
    have hx2 := (entry_xprime (d1 := d1) hlen hL0 hq hd0e (by omega) hn).1
    rw [← hN] at hx2
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col _ (r + L) = (_, _, 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hxrc : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have hCLN : CL N r = CL (M.take (r + L)) r ++ [r + L] := by
    unfold CL
    rw [children_N2 hlen hL0 hq hd0e (by omega) hn hrx, children_take]
    conv_lhs => rw [children_split_x hlen hxrc, List.filter_append]
    rw [show List.filter (fun c => decide (Counted N r c)) [r + L] = [r + L] by simp [hxcN]]
    congr 1
    apply List.filter_congr
    intro c hc
    have hcx : c < r + L := by simpa using (List.mem_filter.mp hc).2
    simp only [decide_eq_decide]
    exact (hcntN r c hrx hcx).trans (hcntP r c hrx hcx).symm
  -- the values of the earlier children are those of `M.take x`
  have hval : ∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d := by
    intro d hd
    have hdc := cl_mem_children hd
    have hcnt : Counted (M.take (r + L)) r d := by simpa using (List.mem_filter.mp hd).2
    exact ((hag d (by have := (mem_children hdc).2; omega)).1
      ((hR0 r hrT).2.1 d hdc hcnt.1 hcnt.2)).symm
  have hvr : σ.v r = τ0.v r := ((hag r hrx).2 (hR0 r hrT).1).symm
  -- the copy root `x′`
  have hCR := t2CopyResAll_holds M ρ rk hM hS I R hz h2 r L hlen hr
  have hBEP : BumpE2 P := by rw [hP, ← hexp (n - 1)]; exact (sInvX_expand hX (n - 1)).loc.2.2.1
  obtain ⟨hKV, hB', hV', hVV⟩ := hCR n hn σ ρP hCN hCP hGP
  have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP
  have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hX.r0p hX.loc.1
  have hF := copy_facts_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP hCN hCP hGP hRP hK hKV hRK hB' hV' hVV
  have hox := o_copy_root hCN hCP hGP hF hrP hxN hV' hVV rfl
  have hvx : σ.v (r + L) = succ (ρ.v r) := by
    have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
    rcases vx_eq hlen hL0 hA hq hd0e hn hd1e he2r h1lt hrb hr1 (fun h => absurd rfl h) I.be hJ hX.r0p I.uat hUN
      I.cons I.good hCN hRN with h | ⟨h, _⟩
    · rw [h, add_one_eq_succ (I.good.ot_v r hrM)]
    · exact absurd rfl h
  rw [hvx] at hox
  exact ⟨hCLN, hvr, hval, hox⟩

/-- **The residual of the sv seed state** (`T2SeedSVFix`): the argument `X₁` of `r` in `M.take x` is fixed by
`σ = σ_{V, V+1}` or a `PH3cG` cut of its image at level `V + 1`, and its summands are at least `Ω_{V+2}`.
実測: 5 集合で X₁ はいつも SpotN（`fix_of_spotN` でこの形）、加数の条件も例外 0。 -/
structure T2SeedSVFix (M : Mat) (ρ : Valn) (r L : Nat) : Prop where
  fix : ∀ τ, Cons (M.take (r + L)) τ →
    sh (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) = t2X1 M r L τ ∨
      t2X1 M r L τ ∈ cutsNSG (succ (ρ.v r)) (sh (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ))
  hi : ∀ τ, Cons (M.take (r + L)) τ → AllGeT (psi (succ (succ (ρ.v r))) z z) (t2X1 M r L τ)

theorem isOT_shIt {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V') {X : T}
    (hX : isOT X = true) : ∀ k, isOT (shIt V V' X k) = true
  | 0 => hX
  | k + 1 => isOT_sh hV hV' hVV (isOT_shIt hV hV' hVV hX k)

/-- **Frames of `r` in `N` from the frames of a source `G`** where `CL G r = Lc ++ E`. -/
theorem seed_frames_liftE {Q : T → List T → T → Prop} {G N : Mat} {ρ σ : Valn} {r x' : Nat} {Lc E : List Nat}
    (hCLG : CL G r = Lc ++ E) (hCLN : CL N r = Lc ++ [x']) (hvr : σ.v r = ρ.v r)
    (hLc : ∀ d ∈ Lc, σ.o d = ρ.o d)
    (hQG : ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat), CL G r = Lc' ++ c :: R' →
      Q (ρ.v r) (Lc'.map ρ.o) (ρ.o c))
    (hlast : Q (ρ.v r) (Lc.map ρ.o) (σ.o x')) :
    ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat), CL N r = Lc' ++ c :: R' → Q (σ.v r) (Lc'.map σ.o) (σ.o c) := by
  intro Lc' c R' h
  rw [hCLN] at h
  rw [hvr]
  by_cases hR : R' = []
  · subst hR
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at h2
    subst h1; subst h2
    rw [List.map_congr_left hLc]; exact hlast
  · have hdl : (Lc' ++ c :: R').dropLast = Lc := by rw [← h]; simp
    rw [List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hR] at hdl
    have hLs : ∀ d ∈ Lc', d ∈ Lc := fun d hd => by rw [← hdl]; exact List.mem_append_left _ hd
    have hcs : c ∈ Lc := by rw [← hdl]; simp
    have hclG : CL G r = Lc' ++ c :: (R'.dropLast ++ E) := by rw [hCLG, ← hdl]; simp
    rw [List.map_congr_left (fun d hd => hLc d (hLs d hd)), hLc c hcs]
    exact hQG Lc' c _ hclG

theorem shIt_z {V V' : T} : ∀ k, shIt V V' z k = z
  | 0 => rfl
  | k + 1 => by simp [shIt, shIt_z k]

open Classical in
/-- **PH3cG and FC3 at the frames of the seed `r` of `M[n]`** (sv), from PH3cG・FC3・FrameOT of `M.take x`,
t2 の残り `T2SeedSVRes`, and the residual `T2SeedSVFix`. -/
theorem seed_frames_sv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (hRes : T2SeedSVRes M ρ r L) (hFix : T2SeedSVFix M ρ r L)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : Rk (M.take (r + L)) rk0)
    (hT : FrameOT (M.take (r + L)) τ0 ∧ PH3cG (M.take (r + L)) τ0 ∧ FC3 (M.take (r + L)) τ0) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
      ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat),
        CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r =
          Lc' ++ c :: R' →
        QPHs (σ.v r) (Lc'.map σ.o) (σ.o c) ∧ QF3s (σ.v r) (Lc'.map σ.o) (σ.o c) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set V := ρ.v r with hVdef
  set X1 := t2X1 M r L τ0 with hX1def
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hRk : ∀ m, 1 ≤ m → ∃ rk', Rk (TRIO.gexp M r L d0 d1 m) rk' := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hVot : isOT V = true := I.good.ot_v r hrM
  have hV' : isOT (succ V) = true := isOT_succ hVot
  have hVV : V < succ V := lt_succ_self V
  have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hrT : r < (M.take (r + L)).length := by omega
  have hvP : τ0.v r = V := v_take_of_untopped I hlen (par_lt M 0 _ _ hq) (topP_sv hlen I.z2 I.z1 hr hq hux) hC0
  have hQT1 := clField_qT2P hC0 hT.1 hT.2.1 r hrT
  have hQT2 := clField_qT2F hC0 hT.1 hT.2.2 r hrT
  have hX1e : X1 = spArg V z (sumN ((CL (M.take (r + L)) r).map τ0.o)) := by
    rw [hX1def]; unfold t2X1; rw [hvP]
  intro n hn hGlow σ hCN hdecN Lc' c R' hCL
  have hG0 : Good3 (M.take (r + L)) τ0 := by
    have := hGlow 1 (le_refl 1) (by omega) τ0 (by rw [hP1]; exact hC0)
    rw [hP1] at this; exact this
  have hX1ot : isOT X1 = true := by
    have := hG0.ot_o r hrT
    rw [o_cl_eq hC0 hG0 hrT] at this
    rw [hX1def]; exact isOT_arg this
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  -- the child of the last frame: `σ^{n−1} X₁`
  obtain ⟨hox, hCLN, hvr, hval⟩ : σ.o (r + L) = psi (succ V) (sh V (succ V) (shIt V (succ V) X1 (n - 2))) z ∧
      CL (TRIO.gexp M r L d0 d1 n) r = CL (M.take (r + L)) r ++ [r + L] ∧ σ.v r = τ0.v r ∧
      ∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn2 : n = 2 := by omega
      subst hn2
      have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hC0
      have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := hGlow 1 (le_refl 1) (by omega) τ0 hCP
      have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hR0
      obtain ⟨hCLN, hvr, hval, hox⟩ :=
        seed_frame_data_sv hM hS I R hz h2 hlen hr hq hux (topP_sv hlen I.z2 I.z1 hr hq hux) (le_refl 2) hCN hRN hCP hGP hRP hC0 hG0 hR0
      rw [← hd0def, ← hd1def] at hCLN hox
      rw [show (2 - 1 : Nat) = 1 from rfl, hP1, hvP, ← hX1e] at hox
      exact ⟨hox, hCLN, hvr, hval⟩
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      obtain ⟨hCLN, hvr, hval, hox⟩ :=
        seed_frame_data_sv hM hS I R hz h2 hlen hr hq hux (topP_sv hlen I.z2 I.z1 hr hq hux) hn hCN hRN hCP hGP hRP hC0 hG0 hR0
      rw [← hd0def, ← hd1def] at hCLN hox
      have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
      have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hval' := seed_r_value_sv hM hS I R hz h2 hlen hr hq hux hRes hC0 hR0 (n - 1) (by omega)
        (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP (cl_vals hCP hGP hrP).2
      have hform := o_cl_eq hCP hGP hrP
      rw [hval'] at hform
      simp only [psi.injEq] at hform
      have h21 := hform.2.1
      rw [← hform.1] at h21
      rw [← hform.1, ← h21, show n - 1 - 1 = n - 2 by omega] at hox
      exact ⟨hox, hCLN, hvr, hval⟩
  -- the levels below `n` are standard
  have hOT : ∀ j, j + 1 < n → isOT (psi V (shIt V (succ V) X1 j) z) = true := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have := hG0.ot_o r hrT
      rw [o_cl_eq hC0 hG0 hrT] at this
      show isOT (psi V X1 z) = true
      rw [hX1e]; rw [hvP] at this; exact this
    · obtain ⟨rkj, hRj⟩ := hRk (j + 1) (by omega)
      have hCj : Cons (TRIO.gexp M r L d0 d1 (j + 1)) (rhsIt _ (rkBound _ rkj)) := cons_of_rk hRj
      have hGj := hGlow (j + 1) (by omega) hj _ hCj
      have hlj : (TRIO.gexp M r L d0 d1 (j + 1)).length = r + (j + 1) * L := TRIO.gexp_length hlen
      have hrj : r < (TRIO.gexp M r L d0 d1 (j + 1)).length := by
        have : L ≤ (j + 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hv := seed_r_value_sv hM hS I R hz h2 hlen hr hq hux hRes hC0 hR0 (j + 1) (by omega)
        (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCj (cl_vals hCj hGj hrj).2
      have := hGj.ot_o r hrj
      rw [hv, show j + 1 - 1 = j by omega] at this
      exact this
  have hBhi := hFix.hi τ0 hC0
  have hFx := hFix.fix τ0 hC0
  have hE : ∀ k, k + 1 < n → SeedExt (succ V) X1 (shIt V (succ V) X1 k) := by
    intro k
    induction k with
    | zero => intro _; exact Or.inl rfl
    | succ k ih =>
      intro hk
      have hcv : isOT (psi (succ V) (sh V (succ V) (shIt V (succ V) X1 k)) z) = true := by
        have := isOT_shTop (V' := succ V) hVot hV' hVV (hOT k (by omega)) (le_refl _)
        rwa [shf_self] at this
      have h := seed_ext (a := V) hVot hV' hVV hX1ot (isOT_shIt hVot hV' hVV hX1ot k) hBhi hFx (ih (by omega)) hcv
      rw [hRes.rw τ0 hC0 k] at h
      exact h
  refine ⟨seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr hval
      (fun Lc' c R' h => (hQT1 Lc' c R' h).2) ?_ Lc' c R' hCL,
    seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr hval
      (fun Lc' c R' h => (hQT2 Lc' c R' h).2) ?_ Lc' c R' hCL⟩
  · -- PH3cG at the last frame
    rw [hox]
    intro s y c0 hc ht _
    simp only [psi.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    have hst : spArg (τ0.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o)) = X1 := rfl
    rw [hst] at ht ⊢
    exact seed_kind hVot hV' hVV hX1ot (isOT_shIt hVot hV' hVV hX1ot (n - 2)) hBhi hFx (hE (n - 2) (by omega)) ht.1
  · -- FC3 at the last frame: the state is `0` and nothing rewrites
    rw [hox]
    intro s y c0 hc ht hL _
    simp only [psi.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    have hLc0 : CL (M.take (r + L)) r = [] := List.map_eq_nil_iff.mp hL
    have hX0 : X1 = z := by rw [hX1e, hLc0]; rfl
    have hst : spArg (τ0.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o)) = X1 := rfl
    rw [hst, hX0, shIt_z, sh_z] at ht
    exact absurd ht.1 (lt_irrefl' _)

end Ytosk.G
