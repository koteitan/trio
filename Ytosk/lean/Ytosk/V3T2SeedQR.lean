/-
**3 行・t = 2・q = r: M[n] の種 r の値を M[n − 1] の r の値で書く（漸化式の N の側）。**

- `o_copy_root`: 写しの根 x′ = r + L の値は ψ_{V′}(σ(M[n − 1] での r の引数))（CopyFacts・o_cl_loc・sh_spArg）。
- `o_r_level_qr`: q = r で x への上げがないとき、N = M[n] の r の値は
  ψ_V(step_V(B, V + 1, σ_{V_P, V+1}(M[n − 1] での r の引数)))（B は x より前の r の数える子の状態、M と同じ）。
-/
import Ytosk.V3T2SeedRec
import Ytosk.V3ExpT2FO
import Ytosk.V3T2M

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- **The root of the copy**: `σ.o (r + L) = ψ_{V′}(σ(arg of ρ.o r))`. -/
theorem o_copy_root {N P : Mat} {σ ρ : Valn} {r L : Nat} {V' : T} {g : Nat → Prop}
    (hCN : Cons N σ) (hCP : Cons P ρ) (hGP : Good3 P ρ) (hF : CopyFacts N P σ ρ r L V' g)
    (hrP : r < P.length) (hxN : r + L < N.length) (hV' : isOT V' = true) (hVV : ρ.v r < V')
    (hVx : σ.v (r + L) = V') :
    σ.o (r + L) = psi V' (sh (ρ.v r) V' (spArg (ρ.v r) z (sumN ((CL P r).map ρ.o)))) z := by
  obtain ⟨hCL, hg, hng⟩ := hF r (le_refl r) hrP
  have hgr : g r := by
    by_contra hn
    obtain ⟨hv, _⟩ := hng hn
    rw [hVx] at hv; rw [hv] at hVV; exact lt_irrefl' _ hVV
  obtain ⟨hv, _, _, hod⟩ := hg hgr
  have hV := hGP.ot_v r hrP
  have hvx : σ.v (r + L) = V' := by rw [hv, shf_self]
  obtain ⟨hsP, hpP⟩ := cl_vals hCP hGP hrP
  have hmap : (CL N (r + L)).map σ.o = ((CL P r).map ρ.o).map (sh (ρ.v r) V') := by
    rw [hCL, List.map_map, List.map_map]
    apply List.map_congr_left
    intro d hd
    exact (hod d hd).1
  have hsN : ∀ c ∈ CL N (r + L), Single (σ.o c) := by
    intro c hc
    rw [hCL] at hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    rw [(hod d hd).1]
    obtain ⟨hot, s, y, hsy⟩ := hsP _ (List.mem_map_of_mem hd)
    refine ⟨isOT_sh hV hV' hVV hot, ?_⟩
    rw [hsy]; exact sh_single s y
  have hpN : ((CL N (r + L)).map σ.o).Pairwise (fun a b => b ≤ a) := by
    rw [hmap, List.pairwise_map]
    exact hpP.imp_of_mem (fun ha hb hab => sh_le_sh hV hV' (le_of_lt hVV) (hsP _ hb).1 (hsP _ ha).1 hab)
  rw [o_cl_loc hCN hxN (by rw [hvx]; exact hV') hsN hpN, hvx, hmap]
  rw [← sh_sumN hV hV' hVV (fun t ht => (hsP t ht).1)]
  have hS := sumN_dec _ hsP hpP
  have hlev : ρ.v r < ρ.v r ∨ ∀ q ∈ summands (sumN ((CL P r).map ρ.o)), lev q ≠ ρ.v r := by
    right; rw [hS.2]; intro q hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
    have hdP : d < P.length := (mem_children (cl_mem_children hd)).2
    obtain ⟨y0, hy0⟩ := o_psi_sub hCP hdP
    rw [hy0, lev_psi, sf_ot (hGP.ot_v d hdP)]
    exact ne_of_gt ((hod d hd).2 rfl)
  have hsp := sh_spArg hV hV' hVV hV (le_refl _) (b := z) rfl hS.1 hlev
  rw [sh_z, shf_self] at hsp
  rw [hsp]

/-- **The seed column `r` of `M[n]`** (`t = 2`, `q = r`, no upgrade into `x`): with `CL M r = Lc ++ [x]`,
`o_N(r) = ψ_V(step_V(B, V + 1, σ_{V_P, V+1}(arg of o_P(r))))`, `P = M[n − 1]`. -/
theorem o_r_level_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
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
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    (hks1 : succ (ρ.v r) < ρ.v (r + L)) :
    σ.o r = psi (ρ.v r) (step (ρ.v r) (spArg (ρ.v r) z (sumN (Lc.map ρ.o))) (succ (ρ.v r))
      (sh (ρP.v r) (succ (ρ.v r)) (spArg (ρP.v r) z (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) (n - 1)) r).map ρP.o)))) z) z := by
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
  -- the frame of `r` in `N`
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hrM
  rw [hCLM] at hsM hpM
  simp only [List.map_append, List.map_singleton] at hsM hpM
  have hxM : r + L < M.length := by omega
  have hoxM : ρ.o (r + L) = psi (ρ.v (r + L)) z z := by
    rw [o_cl_eq I.cons I.good hxM]
    have : CL M (r + L) = [] := by
      unfold CL; rw [children_last_nil hlen]; rfl
    rw [this]; rfl
  have hVot := I.good.ot_v r hrM
  have hshOT : isOT (psi (succ (ρ.v r)) (sh (ρP.v r) (succ (ρ.v r))
      (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o)))) z) = true := by
    have hPo : isOT (psi (ρP.v r) (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o))) z) = true := by
      rw [← o_cl_eq hCP hGP hrP]; exact hGP.ot_o r hrP
    have := isOT_shTop (V' := succ (ρ.v r)) (hGP.ot_v r hrP) (by rw [← hvx]; exact hV') (by rw [← hvx]; exact hVV)
      hPo (le_refl _)
    rwa [shf_self] at this
  have hsN : ∀ c ∈ CL N r, Single (σ.o c) := by
    intro c hc
    rw [hCLN] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [(hLc c hc).2]; exact hsM _ (List.mem_append_left _ (List.mem_map_of_mem hc))
    · simp at hc; rw [hc, hox]; exact ⟨hshOT, _, _, rfl⟩
  have hpN : ((CL N r).map σ.o).Pairwise (fun a b => b ≤ a) := by
    rw [hCLN, List.map_append, List.map_singleton, List.map_congr_left (fun d hd => (hLc d hd).2)]
    have hp1 := List.pairwise_append.mp hpM
    refine List.pairwise_append.mpr ⟨hp1.1, by simp, fun t ht b hb => ?_⟩
    simp at hb; rw [hb, hox]
    refine le_trans (le_of_lt ?_) (hp1.2.2 t ht (ρ.o (r + L)) (by simp))
    rw [hoxM, psi_lt_psi_z_iff]; left; exact hks1
  have hform := o_last_form hCN hrN (by rw [hvr]; exact hVot) hCLN hsN hpN hox
  rw [hform, hvr, List.map_congr_left (fun d hd => (hLc d hd).2)]


/-- **The counted children of the seed `r` in `M[n]` decrease** (`q = r`, no upgrade into `x`). -/
theorem seed_dec_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
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
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    (hks1 : succ (ρ.v r) < ρ.v (r + L)) :
    ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
      σ.o).Pairwise (fun a b => b ≤ a) := by
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
  -- the frame of `r` in `N`
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hrM
  rw [hCLM] at hsM hpM
  simp only [List.map_append, List.map_singleton] at hsM hpM
  have hxM : r + L < M.length := by omega
  have hoxM : ρ.o (r + L) = psi (ρ.v (r + L)) z z := by
    rw [o_cl_eq I.cons I.good hxM]
    have : CL M (r + L) = [] := by
      unfold CL; rw [children_last_nil hlen]; rfl
    rw [this]; rfl
  have hVot := I.good.ot_v r hrM
  have hshOT : isOT (psi (succ (ρ.v r)) (sh (ρP.v r) (succ (ρ.v r))
      (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o)))) z) = true := by
    have hPo : isOT (psi (ρP.v r) (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o))) z) = true := by
      rw [← o_cl_eq hCP hGP hrP]; exact hGP.ot_o r hrP
    have := isOT_shTop (V' := succ (ρ.v r)) (hGP.ot_v r hrP) (by rw [← hvx]; exact hV') (by rw [← hvx]; exact hVV)
      hPo (le_refl _)
    rwa [shf_self] at this
  have hsN : ∀ c ∈ CL N r, Single (σ.o c) := by
    intro c hc
    rw [hCLN] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [(hLc c hc).2]; exact hsM _ (List.mem_append_left _ (List.mem_map_of_mem hc))
    · simp at hc; rw [hc, hox]; exact ⟨hshOT, _, _, rfl⟩
  have hpN : ((CL N r).map σ.o).Pairwise (fun a b => b ≤ a) := by
    rw [hCLN, List.map_append, List.map_singleton, List.map_congr_left (fun d hd => (hLc d hd).2)]
    have hp1 := List.pairwise_append.mp hpM
    refine List.pairwise_append.mpr ⟨hp1.1, by simp, fun t ht b hb => ?_⟩
    simp at hb; rw [hb, hox]
    refine le_trans (le_of_lt ?_) (hp1.2.2 t ht (ρ.o (r + L)) (by simp))
    rw [hoxM, psi_lt_psi_z_iff]; left; exact hks1
  exact hpN

end Ytosk
