/-
**t = 2・q = r（x への上げなし）の種 r の枠の PH3c・FC3（closure、2026-10-12）。**

N = M[n] での r の数える子は CL_N(r) = Lc ++ [x′]（x′ = r + L は写しの根）。
- x′ より前の子の枠は M の枠そのもの（値が同じ）。
- 最後の枠: 状態 B（M と同じ）、子 x′ の値 ψ_{V+1}(y)、y = σ_{V_P, V+1}(M[n − 1] での r の引数)。
  - n = 2: t2 の残り `T2SeedQRRes.w1`（¬ B < y）で書き換えない。
  - n ≥ 3: M[n − 1] での r の引数は seqZ(n − 3) = B + ψ_{V+n−2}(…)（t2 の `seed_r_value_qr`・`seqZ_form`）。
    σ(B) = B（`tame_sigmaB_std`）なので y = B + ψ_{V+n−1}(…)。加数はすべて Ω_{V+2} 以上なので
    hi = y・lo = 0 で、種類は pre（hi = B + R、R ≠ 0）。FC3 は B = 0 のときで、lev(hi) = V + n − 1 = (V + 1) + (n − 2)。
-/
import Ytosk.V3Tame
import Ytosk.V3T2SeedQRL
import Ytosk.V3PT2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## 項の補題 -/

theorem app_eq_self_iff : ∀ {B R : T}, app B R = B → R = z
  | z, _, h => by simpa using h
  | psi _ _ c, R, h => by
    simp only [app_psi, psi.injEq] at h
    exact app_eq_self_iff h.2.2

theorem natT_succ_ne_z (k : Nat) : natT (k + 1) ≠ z := by
  rw [← app_one_natT]; simp [one]

/-- `V + (k + 2) = (V + 1) + (k + 1)`. -/
theorem addN_succ_split (V : T) (k : Nat) : addN V (k + 2) = app (succ V) (natT (k + 1)) := by
  unfold addN succ
  rw [app_assoc, app_one_natT]

theorem succ_succ_le_addN (V : T) {k : Nat} (hk : 2 ≤ k) : succ (succ V) ≤ addN V k := by
  have : succ (succ V) = addN V 2 := by
    unfold addN succ; rw [app_assoc]; rfl
  rw [this]; exact addN_le hk

/-! ## 最後の枠: n ≥ 3 -/

section
variable {V B W1 s : T} (hV : isOT V = true)
  (hσB : sh V (succ V) B = B)
  (hBc : ∀ q ∈ summands B, psi s z z ≤ q) (hks : ∀ k, addN V k < s)
include hV hσB hBc hks

/-- **The child of the last seed frame**: `σ(seqZ k) = B + ψ_{V+k+2}(σ^{k+1} W₁)`. -/
theorem sh_seqZ (k : Nat) :
    sh V (succ V) (seqZ V B W1 k) = app B (psi (addN V (k + 2)) (shN V (k + 1) W1) z) := by
  rw [seqZ_form hV hσB hBc hks k, sh_app, hσB, sh_psi_addN hV (by omega)]
  rfl

theorem sh_seqZ_allGe (k : Nat) :
    ∀ q ∈ summands (sh V (succ V) (seqZ V B W1 k)), ¬ q < psi (succ (succ V)) z z := by
  rw [sh_seqZ hV hσB hBc hks k, summands_app]
  intro q hq hlt
  rcases List.mem_append.mp hq with hq | hq
  · have h1 := hBc q hq
    have h2 : psi (succ (succ V)) z z ≤ psi s z z :=
      psi_le_psi_z (le_of_lt (lt_of_le_of_lt (succ_succ_le_addN V (le_refl 2)) (hks 2)))
    exact absurd (lt_of_lt_of_le hlt (le_trans h2 h1)) (lt_irrefl' _)
  · simp only [summands, List.mem_singleton] at hq
    subst hq
    rw [psi_lt_psi_z_iff] at hlt
    rcases hlt with h | ⟨_, h⟩
    · exact absurd (lt_of_lt_of_le h (succ_succ_le_addN V (by omega))) (lt_irrefl' _)
    · exact T.not_lt_z _ h

/-- **PH3c at the last seed frame** (`n ≥ 3`): the kind is `pre`. -/
theorem seed_last_kind (k : Nat) :
    PH3cKind B (split (sh V (succ V) (seqZ V B W1 k)) (psi (succ (succ V)) z z)).1
      (split (sh V (succ V) (seqZ V B W1 k)) (psi (succ (succ V)) z z)).2 (succ V) := by
  rw [split_all_ge (sh_seqZ_allGe hV hσB hBc hks k), sh_seqZ hV hσB hBc hks k]
  refine Or.inr ⟨fun h => ?_, Or.inl ⟨_, by simp, rfl⟩⟩
  have := app_eq_self_iff h; simp at this

/-- **FC3 at the last seed frame** when it is the first frame (`B = 0`). -/
theorem seed_last_fc3 (k : Nat) (hB0 : B = z) : FC3c V (succ V) (sh V (succ V) (seqZ V B W1 k)) := by
  refine ⟨fun h => absurd h (ne_of_gt (lt_succ_self V)), fun _ => ⟨natT (k + 1), natT_succ_ne_z k, ?_⟩⟩
  rw [split_all_ge (sh_seqZ_allGe hV hσB hBc hks k), sh_seqZ hV hσB hBc hks k, hB0, app_z, lev_psi]
  exact addN_succ_split V k

end

/-! ## N での r の枠のデータ（t2 の `o_r_level_qr` の前半を写したもの） -/

open Classical in
/-- **The data of the seed frames of `r` in `N = M[n]`** (`t = 2`, `q = r`, no upgrade into `x`):
`CL N r = Lc ++ [x]`, `v_N(r) = v(r)`, the children before `x` keep their values, and
`o_N(x) = ψ_{V+1}(σ_{V_P, V+1}(arg of o_P(r)))` with `P = M[n − 1]`. -/
theorem seed_frame_data_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L])
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP) :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = Lc ++ [r + L] ∧
      σ.v r = ρ.v r ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧
      σ.o (r + L) = psi (succ (ρ.v r)) (sh (ρP.v r) (succ (ρ.v r)) (spArg (ρP.v r) z
        (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1))
          r).map ρP.o)))) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
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
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hxbr : col M (r + L) ≠ bump M r := fun h => by
    have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hIU : ∀ c, c < r + L → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_N2 (d1 := d1) hlen hL0 hq hd0e hn hXu hxbr he2r hc]
    exact htM
  have hxcN : Counted N r (r + L) := by
    have hx2 := (entry_xprime (d1 := d1) hlen hL0 hq hd0e (by omega) hn).1
    rw [← hN] at hx2
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col _ (r + L) = (_, _, 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hCLN : CL N r = Lc ++ [r + L] := by
    rw [CL_N2 hlen hL0 hq hd0e hn hXu hxbr he2r hIU hxcN hrx, hCLM]
  -- `D = DepS M {o(r)}` misses the counted children of `r` and `v(r)`
  have hoff := t2_off hlen hL0 hq hd0e hn hXu hxbr hrb he2r hIU I.cons hCN hRN
  have hnoD : ∀ b i, DepS M (fun b i => b = true ∧ i = r) b i → i < M.length → rk true r ≤ rk b i := by
    intro b i hD hi
    obtain ⟨b', i', ⟨rfl, rfl⟩, hle⟩ := depS_rk_ex I.rank hD hi
    exact hle
  have hrM : r < M.length := by omega
  have hvr : σ.v r = ρ.v r := (hoff r hrx).2 (fun hD => by
    have h1 := hnoD false r hD hrM
    have h2' := (I.rank r hrM).1
    omega)
  have hLc : ∀ d ∈ Lc, d < r + L ∧ σ.o d = ρ.o d := by
    intro d hd
    have hdCL : d ∈ CL M r := by rw [hCLM]; simp [hd]
    have hdc := cl_mem_children hdCL
    have hcnt : Counted M r d := by simpa using (List.mem_filter.mp hdCL).2
    have hdx : d < r + L := by
      have hsort := cl_sorted M r
      rw [hCLM] at hsort
      exact (List.pairwise_append.mp hsort).2.2 d hd (r + L) (by simp)
    refine ⟨hdx, (hoff d hdx).1 (fun hD => ?_)⟩
    have h1 := hnoD true d hD (by omega)
    have h2' := (I.rank r hrM).2.1 d hdc hcnt.1 hcnt.2
    omega
  -- the copy root `x′`
  have hCR := t2CopyResAll_holds M ρ rk hM hS I R hz h2 r L hlen hr
  have hm : n - 1 + 1 = n := by omega
  have hBEP : BumpE2 P := by rw [hP, ← hexp (n - 1)]; exact (sInvX_expand hX (n - 1)).loc.2.2.1
  obtain ⟨hKV, hB', hV', hVV⟩ := hCR n hn σ ρP hCN hCP hGP
  have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP
  have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hX.r0p hX.loc.1
  have hF := copy_facts_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP hCN hCP hGP hRP hK hKV hRK hB' hV' hVV
  have hox := o_copy_root hCN hCP hGP hF hrP hxN hV' hVV rfl
  -- `v(x′) = V + 1`
  have hvx : σ.v (r + L) = succ (ρ.v r) := by
    have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
    rcases vx_eq hlen hL0 hA hq hd0e hn hd1e he2r h1lt hrb hr1 (fun h => absurd rfl h) I.be hJ hX.r0p I.uat hUN
      I.cons I.good hCN hRN with h | ⟨h, _⟩
    · rw [h, add_one_eq_succ (I.good.ot_v r hrM)]
    · exact absurd rfl h
  rw [hvx] at hox
  exact ⟨hCLN, hvr, fun d hd => (hLc d hd).2, hox⟩

/-! ## 枠の持ち上げ -/

/-- **The frames of `r` in `N`** from the frames of `M` and the last frame: `CL N r = Lc ++ [x′]`, the same
`v(r)` and the same values before `x′`. -/
theorem seed_frames_lift {Q : T → List T → T → Prop} {M N : Mat} {ρ σ : Valn} {r x x' : Nat} {Lc : List Nat}
    (hCLM : CL M r = Lc ++ [x]) (hCLN : CL N r = Lc ++ [x']) (hvr : σ.v r = ρ.v r)
    (hLc : ∀ d ∈ Lc, σ.o d = ρ.o d)
    (hQM : ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat), CL M r = Lc' ++ c :: R' →
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
    have hclM : CL M r = Lc' ++ c :: (R'.dropLast ++ [x]) := by rw [hCLM, ← hdl]; simp
    rw [List.map_congr_left (fun d hd => hLc d (hLs d hd)), hLc c hcs]
    exact hQM Lc' c _ hclM

/-! ## 組み立て: q = r・x への上げなし -/

open Classical in
/-- **PH3c and FC3 at the frames of the seed `r` of `M[n]`** (`t = 2`, `q = r`, no upgrade into `x`), from
PH3c・FC3 of `M` and t2 の残り `T2SeedQRRes` (σB is `tame_sigmaB_std`). -/
theorem seed_frames_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) (hRes : T2SeedQRRes M ρ r L Lc)
    {τ0 : Valn} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : ∃ rk0, Rk (M.take (r + L)) rk0)
    (hP : PH3c M ρ) (hF : FC3 M ρ) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat),
        CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r =
          Lc' ++ c :: R' →
        QPHs (σ.v r) (Lc'.map σ.o) (σ.o c) ∧ QF3s (σ.v r) (Lc'.map σ.o) (σ.o c) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set V := ρ.v r with hVdef
  set B := t2B V ρ Lc with hBdef
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
  obtain ⟨hBc, hBot, _⟩ := qr_M_side I hlen hrx hCLM
  have hQM1 := clField_qT2P I.cons I.fo hP r hrM
  have hQM2 := clField_qT2F I.cons I.fo hF r hrM
  intro n hn hGlow σ hCN Lc' c R' hCL
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  -- the valuation of `P = M[n − 1]` and the child of the last frame
  obtain ⟨Y, hYl⟩ : ∃ Y, σ.o (r + L) = psi (succ V) Y z ∧
      ((n = 2 ∧ ¬ B < Y) ∨ (3 ≤ n ∧ Y = sh V (succ V) (seqZ V B (t2W1 (M.take (r + L)) V τ0 r) (n - 3)))) ∧
      CL (TRIO.gexp M r L d0 d1 n) r = Lc ++ [r + L] ∧ σ.v r = V ∧ ∀ d ∈ Lc, σ.o d = ρ.o d := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn2 : n = 2 := by omega
      subst hn2
      have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
      have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hC0
      have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := hGlow 1 (le_refl 1) (by omega) τ0 hCP
      obtain ⟨rk0, hRk0⟩ := hR0
      have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hRk0
      obtain ⟨hCLN, hvr, hLc, hox⟩ :=
        seed_frame_data_qr hM hS I R hz h2 hlen hr hq hXu hCLM (le_refl 2) hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hox
      rw [show (2 - 1 : Nat) = 1 from rfl, hP1] at hox
      exact ⟨_, hox, Or.inl ⟨rfl, hRes.w1 τ0 hC0⟩, hCLN, hvr, hLc⟩
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      obtain ⟨hCLN, hvr, hLc, hox⟩ :=
        seed_frame_data_qr hM hS I R hz h2 hlen hr hq hXu hCLM hn hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hox
      have hval := seed_r_value_qr hM hS I R hz h2 hlen hr hq hXu hCLM hRes hC0 ⟨_, hR0.choose_spec⟩ (n - 1)
        (by omega) (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP
      have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
      have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hform := o_cl_eq hCP hGP hrP
      rw [hval] at hform
      simp only [psi.injEq] at hform
      have h21 := hform.2.1
      rw [← hform.1] at h21
      rw [← hform.1, ← h21, show n - 1 - 2 = n - 3 by omega] at hox
      exact ⟨_, hox, Or.inr ⟨hn3, rfl⟩, hCLN, hvr, hLc⟩
  obtain ⟨hox, hcase, hCLN, hvr, hLc⟩ := hYl
  have hσB := hRes.σB
  refine ⟨seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => (hQM1 Lc' c R' h).2) ?_ Lc' c R' hCL,
    seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => (hQM2 Lc' c R' h).2) ?_ Lc' c R' hCL⟩
  · -- PH3c at the last frame
    rw [hox]
    intro s y c0 hc ht hBz
    simp only [psi.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    rcases hcase with ⟨_, hnr⟩ | ⟨hn3, hY⟩
    · exact absurd ht.1 hnr
    · rw [hY]
      exact seed_last_kind hVot hσB hBc hRes.ks (n - 3)
  · -- FC3 at the last frame
    rw [hox]
    intro s y c0 hc ht hL _
    simp only [psi.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    rcases hcase with ⟨_, hnr⟩ | ⟨hn3, hY⟩
    · exact absurd ht.1 hnr
    · rw [hY]
      have hLc0 : Lc = [] := List.map_eq_nil_iff.mp hL
      exact seed_last_fc3 hVot hσB hBc hRes.ks (n - 3) (by rw [hLc0]; rfl)

end Ytosk
