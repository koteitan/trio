/-
**3 行・t = 0: VSmallRAll は展開 N = M[n] に渡る（2026-10-16、t0）。**

N の書き換える枠 (i, c) は、M の書き換える枠 (φ i, φ c)（φ = phi0、写した元の列）に写る（`frameMap_N_t0`）:
v(i) と添字 s は同じ、引数は M の方が大きい、状態は同じ。
- r より前: 枠は M と同じ列。c が D なら子は下がる（hdl）、添字は同じ（hss）。
- g の枠: 写しの根 r_j の子は omid か o′(r) で o_M(r) = ψ_v(Y0 + 1) より下、2 個目以降は書き換えない（no_rw_after）。
- 中間の写し: M の枠そのもの。最後の写し: M.take x の枠で、これは M の枠に写る（frame_take_rw）。
旧い試み（M.take x の段の道へ写す）は、段の鎖が g の上を通る所で「N で書き換えるなら M.take x でも書き換える」が
偽だった。最後の写しの枠も M の枠へ写せば、段の道は M の道に入る（`pathLvAll_N_t0`）ので、この穴は要らない。
-/
import Ytosk.V3T0Frm
import Ytosk.V3VSRAllDrop

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- A frame that rewrites keeps rewriting at a larger argument. -/
theorem rw_up {a B s y y0 : T} (h : y ≤ y0)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true) :
    lt B y0 = true ∧ lt (psi a z z) (psi s y0 z) = true :=
  ⟨lt_of_lt_of_le (show B < y from ht.1) h, lt_of_lt_of_le (show _ < psi s y z from ht.2) (psi_le_psi_arg h)⟩

/-- The arguments of two `ψ` terms with the same subscript compare as the terms. -/
theorem arg_le_of_psi_le {s y y0 : T} (h : psi s y z ≤ psi s y0 z) : y ≤ y0 := by
  rcases (le_iff _ _).mp h with h | h
  · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
    · exact absurd h (lt_irrefl' _)
    · exact le_of_lt h
  · simp only [psi.injEq] at h; rw [h.2.1]

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ ρ' : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : GoodOT (TRIO.gexp M r L 0 0 n) σ)
  (hC1 : Cons (M.take (r + L)) ρ') (hRk1 : Rk (M.take (r + L)) rk) (hGT : Good3 (M.take (r + L)) ρ')
  (hdrop : ∀ i, i < r + L → PO ρ ρ' i ∧ PV M ρ ρ' i)
  (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
    σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧ σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i)
  (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
    (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
  (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
  (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
  (hLast : ∀ g, par M 0 r = some g → Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
  (hO'le : ρ'.o r ≤ omid M r L ρ)
  (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
  (hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d)
  (hss : ∀ d, d < r → σ.v d ≠ ρ.v d → σ.o d = psi (σ.v d) z z)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hC1 hRk1 hGT hdrop hσB hoffD
  hσmid hσlast hLast hO'le hy' hdl hss

/-- **A rewriting frame of `N = M[n]` is a rewriting frame of `M`** at the copied columns: the same parent
value and subscript, the same state, and a larger argument. -/
theorem frameMap_N_t0 :
    ∀ i (Lc : List Nat) (c : Nat) (R : List Nat), CL (TRIO.gexp M r L 0 0 n) i = Lc ++ c :: R →
    ∀ s y, σ.o c = psi s y z →
    lt (spArg (σ.v i) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v i) z z) (psi s y z) = true →
    ∃ (Lc' R' : List Nat) (yM : T), CL M (phi0 r L i) = Lc' ++ phi0 r L c :: R' ∧
      ρ.v (phi0 r L i) = σ.v i ∧ Lc'.map ρ.o = Lc.map σ.o ∧
      ρ.o (phi0 r L c) = psi s yM z ∧ y ≤ yM ∧
      (lt (spArg (σ.v i) z (sumN (Lc'.map ρ.o))) yM = true ∧ lt (psi (σ.v i) z z) (psi s yM z) = true) := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  -- `σ.o d = ψ_{s′}(y′)` with `y′ ≠ 0` keeps the subscript of `ρ.o d`
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
  intro i Lc c R hCL s y hsy ht
  have hy0 : y ≠ z := ne_z_of_lt ht.1
  rcases Nat.lt_or_ge i r with hir | hir
  · rw [phi0_lt hir]
    by_cases hgc : par M 0 r = some i ∧ Counted M i r
    · -- the frames of `g`
      obtain ⟨hg, hcnt⟩ := hgc
      have hx : r + L + 1 = M.length := hlen
      have hgM : i < M.length := by omega
      have hrg : r ∈ children M i := mem_children_iff.mpr ⟨by omega, hg⟩
      set F := (children M i).filter (fun d => decide (d < r)) with hFdef
      have hchM : children M i = F ++ [r] := children_g_last hlen hL hp hg
      set Lg := F.filter (fun d => decide (Counted M i d)) with hLgdef
      have hclM : CL M i = Lg ++ [r] := by
        unfold CL; rw [hchM, List.filter_append]
        simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hcnt]
        rfl
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
        (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) i d)) with hCmdef
      have hclN : CL (TRIO.gexp M r L 0 0 n) i = Lg ++ Cm ++ [r + (n - 1) * L] := by
        unfold CL
        rw [children_g0 hlen hL hp hn hg, hchM, List.append_assoc, hroots, List.filter_append,
          List.filter_append]
        have hF' : F.filter (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) i d)) = Lg := by
          apply List.filter_congr
          intro d hd
          have hdr : d < r := by simpa using (List.mem_filter.mp hd).2
          simp only [counted_lt0 hlen hL hp hn hR0 hZ2 he2 hn2 hir hdr]
        rw [hF', List.append_assoc]
        simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos (hLast i hg hcnt)]
        rfl
      have hCmv : Cm.map σ.o = List.replicate Cm.length (omid M r L ρ) := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp, fun b hb => ?_⟩
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hd).1
        exact hσmid k (by have := List.mem_range.mp hk; omega)
      have hLcv : Lg.map σ.o = Lg.map ρ.o := by
        apply List.map_congr_left
        intro d hd
        have hdF := (List.mem_filter.mp hd).1
        have hdr : d < r := by simpa using (List.mem_filter.mp hdF).2
        have hdM := (List.mem_filter.mp hdF).1
        apply (hoffD d hdr).1
        intro hD
        exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hdM hrg hdr hD hcnt
      have hσvg : σ.v i = ρ.v i := (hoffD i hir).2 (fun hd =>
        uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hd hrg hcnt)
      rw [hclN] at hCL
      obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG
      set Y0 := spArg (ρ.v r) z (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r)))
        with hY0
      have hOot : isOT (psi (ρ.v r) Y0 z) = true := by
        rw [← hom]; exact isOT_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN
      -- a copy root `c = r + k L` with `o(c)` the middle value or `o′(r)`, after `P2` middle roots
      have hroot : ∀ (P2 : List Nat) (k : Nat), k < n → c = r + k * L →
          (σ.o c = omid M r L ρ ∨ σ.o c = ρ'.o r) → Lc = Lg ++ P2 →
          P2.map σ.o = List.replicate P2.length (omid M r L ρ) →
          ∃ (Lc' R' : List Nat) (yM : T), CL M i = Lc' ++ phi0 r L c :: R' ∧
            ρ.v i = σ.v i ∧ Lc'.map ρ.o = Lc.map σ.o ∧
            ρ.o (phi0 r L c) = psi s yM z ∧ y ≤ yM ∧
            (lt (spArg (σ.v i) z (sumN (Lc'.map ρ.o))) yM = true ∧
              lt (psi (σ.v i) z z) (psi s yM z) = true) := by
        intro P2 k hk hck hcv hLc hP2v
        have hss : s = ρ.v r := by
          rcases hcv with h | h
          · rw [hsy, hom] at h; simp only [psi.injEq] at h; exact h.1
          · rw [hsy] at h; by_contra hne; exact hy0 (hy' s y h.symm hne)
        subst hss
        have hyY : y ≤ Y0 := by
          apply arg_le_of_psi_le
          rw [← hsy, ← hom]
          rcases hcv with h | h
          · rw [h]
          · rw [h]; exact hO'le
        have hφ : phi0 r L c = r := by
          rw [hck, show r + k * L = r + (k * L + 0) by omega, phi0_copy hL]; omega
        rw [hφ]
        cases P2 with
        | nil =>
          rw [List.append_nil] at hLc
          subst hLc
          have hyy : y ≤ app Y0 one := le_trans hyY (le_of_lt (lt_app_one Y0))
          refine ⟨Lg, [], app Y0 one, hclM, hσvg.symm, hLcv.symm, hor, hyy, ?_⟩
          rw [← hLcv]; exact rw_up hyy ht
        | cons d P2' =>
          exfalso
          have hj : 1 ≤ (d :: P2').length := by simp
          apply no_rw_after (a := σ.v i) (B := spArg (σ.v i) z (sumN (Lg.map ρ.o))) hOot hj
          obtain ⟨hsM, hpM⟩ := cl_vals hC hG hgM
          rw [hclM] at hsM hpM
          simp only [List.map_append, List.map_singleton] at hsM hpM
          have hOr : psi (ρ.v r) Y0 z < ρ.o r := by
            rw [hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one Y0⟩)
          have hLge : ∀ q ∈ Lg.map ρ.o, ρ.o r ≤ q := fun q hq =>
            (List.pairwise_append.mp hpM).2.2 q hq _ (by simp)
          have hOs : Single (psi (ρ.v r) Y0 z) := ⟨hOot, _, _, rfl⟩
          have hsum : sumN (Lg.map ρ.o ++ List.replicate (d :: P2').length (omid M r L ρ)) =
              app (sumN (Lg.map ρ.o)) (mulT (psi (ρ.v r) Y0 z) (d :: P2').length) := by
            rw [hom, sumN_append_dec, sumN_replicate hOs]
            · intro t ht
              rcases List.mem_append.mp ht with ht | ht
              · exact hsM t (List.mem_append_left _ ht)
              · rw [(List.mem_replicate.mp ht).2]; exact hOs
            · refine List.pairwise_append.mpr ⟨(List.pairwise_append.mp hpM).1,
                List.pairwise_replicate.mpr (Or.inr (le_refl _)), fun q hq b hb => ?_⟩
              rw [(List.mem_replicate.mp hb).2]; exact le_trans (le_of_lt hOr) (hLge q hq)
          have ht' := ht
          rw [hLc, List.map_append, hLcv, hP2v, hsum, spArg_app] at ht'
          exact ⟨lt_of_lt_of_le (show _ < y from ht'.1) hyY,
            lt_of_lt_of_le (show _ < psi (ρ.v r) y z from ht'.2) (psi_le_psi_arg hyY)⟩
      rcases append_split_cons Lg (Cm ++ [r + (n - 1) * L]) Lc R c (by rw [← List.append_assoc]; exact hCL) with
        ⟨R0, hR0⟩ | ⟨P2, hP, hD⟩
      · -- a child before the copy roots: a frame of `M`
        have hσL : Lc.map σ.o = Lc.map ρ.o := by
          have := hLcv; rw [hR0, List.map_append, List.map_append] at this
          exact List.append_inj_left this (by simp)
        have hcσ : σ.o c = ρ.o c := by
          have := hLcv; rw [hR0, List.map_append, List.map_append] at this
          have h2 := List.append_inj_right this (by simp)
          simp only [List.map_cons, List.cons.injEq] at h2; exact h2.1
        have hcr : c < r := by
          have hcF : c ∈ Lg := by rw [hR0]; simp
          simpa using (List.mem_filter.mp (List.mem_filter.mp hcF).1).2
        rw [phi0_lt hcr]
        refine ⟨Lc, R0 ++ [r], y, by rw [hclM, hR0]; simp, hσvg.symm, hσL.symm, hcσ ▸ hsy, le_refl _, ?_⟩
        rw [hσL] at ht; exact ht
      · rcases append_split_cons Cm [r + (n - 1) * L] P2 R c hD with ⟨R1, hR1⟩ | ⟨P3, hP3, hD3⟩
        · -- a middle copy root
          have hcm : c ∈ Cm := by rw [hR1]; simp
          obtain ⟨k, hk, hkc⟩ := List.mem_map.mp (List.mem_filter.mp hcm).1
          have hkn := List.mem_range.mp hk
          have hcv : σ.o c = omid M r L ρ := by
            rw [← hkc]; exact hσmid k (by omega)
          have hP2v : P2.map σ.o = List.replicate P2.length (omid M r L ρ) := by
            rw [List.eq_replicate_iff]; refine ⟨by simp, fun b hb => ?_⟩
            have : b ∈ Cm.map σ.o := by
              rw [hR1]; simp only [List.map_append]; exact List.mem_append_left _ hb
            rw [hCmv] at this; exact (List.mem_replicate.mp this).2
          exact hroot P2 k (by omega) hkc.symm (Or.inl hcv) hP hP2v
        · -- the last copy root
          have hP3n : P3 = [] := by
            cases P3 with
            | nil => rfl
            | cons a P3' => simp at hD3
          subst hP3n
          have hcl : c = r + (n - 1) * L := by simp at hD3; exact hD3.1.symm
          rw [List.append_nil] at hP3
          rw [hP3] at hP
          have hcv : σ.o c = ρ'.o r := by rw [hcl]; exact hσlast
          exact hroot Cm (n - 1) (by omega) hcl (Or.inr hcv) hP hCmv
    have hb : par M 0 r = some i → col M r = bump M i := by
      intro hig
      by_contra hb
      exact hgc ⟨hig, hb, by rw [not_topped_r hlen hL hp he2]; simp⟩
    rw [cl_N_eq hlen hL hp hn hR0 hZ2 he2 hn2 hir hb] at hCL
    have hcCL : c ∈ CL M i := by rw [hCL]; simp
    have hccnt : Counted M i c := by
      have := hcCL; unfold CL at this; simpa using (List.mem_filter.mp this).2
    have hsort : (CL M i).Pairwise (· < ·) := List.Pairwise.filter _ (children_sorted M i)
    rw [hCL] at hsort
    have hLc : ∀ d ∈ Lc, σ.o d = ρ.o d := by
      intro d hd
      have hdc : d < c := (List.pairwise_append.mp hsort).2.2 d hd c (by simp)
      have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
      have hdr : d < r := by
        have hdch := cl_mem_children hdCL
        by_cases hig : par M 0 r = some i
        · have hle := children_g_le hlen hL hp hig hdch
          have hcle := children_g_le hlen hL hp hig (cl_mem_children hcCL)
          omega
        · exact children_lt_r hlen hL hp hir hig hdch
      apply (hoffD d hdr).1
      intro hD
      exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) (cl_mem_children hdCL)
        (cl_mem_children hcCL) hdc hD hccnt
    have hv : σ.v i = ρ.v i := by
      apply (hoffD i hir).2
      intro hD
      exact uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hD (cl_mem_children hcCL) hccnt
    have hcr : c < r := by
      have hcch := cl_mem_children hcCL
      by_cases hig : par M 0 r = some i
      · have hle := children_g_le hlen hL hp hig hcch
        rcases Nat.lt_or_ge c r with h | h
        · exact h
        · exfalso; have hcr' : c = r := by omega
          rw [hcr'] at hccnt; exact hgc ⟨hig, hccnt⟩
      · exact children_lt_r hlen hL hp hir hig hcch
    rw [phi0_lt hcr]
    have hLm : Lc.map ρ.o = Lc.map σ.o := (List.map_congr_left hLc).symm
    by_cases hDc : DepX M (r + L) true c
    · have hcM : c < M.length := by omega
      obtain ⟨s0, y1, hs0⟩ := (single_o hC hG hcM).2
      have hss0 : s = s0 := hsub c hcr s0 y1 s y hs0 hsy hy0
      subst hss0
      have hle : psi s y z ≤ psi s y1 z := by rw [← hsy, ← hs0]; exact hdl c hcr hDc
      have hyy := arg_le_of_psi_le hle
      refine ⟨Lc, R, y1, hCL, hv.symm, hLm, hs0, hyy, ?_⟩
      rw [hLm]; exact rw_up hyy ht
    · have hcσ := (hoffD c hcr).1 hDc
      refine ⟨Lc, R, y, hCL, hv.symm, hLm, hcσ ▸ hsy, le_refl _, ?_⟩
      rw [hLm]; exact ht
  · -- a copy column
    have hiN : i < (TRIO.gexp M r L 0 0 n).length := by
      have hcT : c ∈ CL (TRIO.gexp M r L 0 0 n) i := by rw [hCL]; simp
      have := mem_children (cl_mem_children hcT); omega
    have hk0 : (i - r) / L < n := by
      rw [hlN] at hiN
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hq0 : (i - r) % L < L := Nat.mod_lt _ hL
    have hi' : i = r + ((i - r) / L * L + (i - r) % L) := by
      have := Nat.div_add_mod (i - r) L
      rw [Nat.mul_comm] at this; omega
    obtain ⟨k, q, hk, hq, rfl⟩ : ∃ k q, k < n ∧ q < L ∧ i = r + (k * L + q) :=
      ⟨_, _, hk0, hq0, hi'⟩
    rw [phi0_copy hq]
    rw [cl_copy0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hk hq] at hCL
    obtain ⟨G, hGdef⟩ : ∃ G, G = ((children M (r + q)).filter (fun c => decide (c < r + L))).filter
      (fun d => decide (Counted M (r + q) d)) := ⟨_, rfl⟩
    rw [← hGdef] at hCL
    obtain ⟨Lc', T', hGs, hLc', hT'⟩ := List.map_eq_append_iff.mp hCL
    obtain ⟨c', R', rfl, hc', hR'⟩ := List.map_eq_cons_iff.mp hT'
    have hGm : ∀ d ∈ G, r + q < d ∧ d < r + L := fun d hd => by
      rw [hGdef] at hd
      have h := List.mem_filter.mp (List.mem_filter.mp hd).1
      exact ⟨(mem_children h.1).1, by simpa using h.2⟩
    have hkL : k * L + L ≤ n * L := by
      have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
    have hval : ∀ d ∈ G, σ.o (shk r (k * L) d) = if k + 1 < n then ρ.o d else ρ'.o d := by
      intro d hd
      obtain ⟨h1, h2⟩ := hGm d hd
      obtain ⟨q', rfl⟩ : ∃ q', d = r + q' := ⟨d - r, by omega⟩
      simp only [shk, if_pos (show r ≤ r + q' by omega)]
      rw [show r + q' + k * L = r + (k * L + q') by omega, (hσB _ (by omega) (by rw [hlN]; omega)).1]
      split
      · rename_i hkn; exact tau_o_mid hkn (by omega) (by omega)
      · have hk' : k = n - 1 := by omega
        rw [hk']
        exact tau_o_last (by omega)
    have hc'G : c' ∈ G := by rw [hGs]; simp
    obtain ⟨hc1, hc2⟩ := hGm c' hc'G
    have hφc : phi0 r L (shk r (k * L) c') = c' := by
      obtain ⟨q', rfl⟩ : ∃ q', c' = r + q' := ⟨c' - r, by omega⟩
      simp only [shk, if_pos (show r ≤ r + q' by omega)]
      rw [show r + q' + k * L = r + (k * L + q') by omega, phi0_copy (by omega)]
    rw [← hc', hφc]
    have hcval := hval c' hc'G
    have hLcval : Lc.map σ.o = Lc'.map (if k + 1 < n then ρ.o else ρ'.o) := by
      rw [← hLc', List.map_map]
      apply List.map_congr_left
      intro d hd
      simp only [Function.comp]
      rw [hval d (by rw [hGs]; exact List.mem_append_left _ hd)]
      split <;> rfl
    rw [← hc'] at hsy
    rw [(hσB _ (by omega) hiN).2] at ht ⊢
    by_cases hkn : k + 1 < n
    · rw [if_pos hkn] at hcval hLcval
      rw [tau_v_mid hkn hq] at ht ⊢
      rw [hLcval] at ht ⊢
      rw [hcval] at hsy
      -- the frame of `M` at `r + q`
      have hCLM : ∃ X, CL M (r + q) = G ++ X := by
        by_cases hxq : r + L ∈ children M (r + q)
        · refine ⟨((([r + L] : List Nat)).filter (fun d => decide (Counted M (r + q) d))), ?_⟩
          unfold CL
          rw [hGdef]
          conv_lhs => rw [children_split_x (x := r + L) hlen hxq]
          rw [List.filter_append]
        · refine ⟨[], ?_⟩
          unfold CL
          rw [hGdef, children_filter_x (x := r + L) hlen hxq, List.append_nil]
      obtain ⟨X, hX⟩ := hCLM
      exact ⟨Lc', R' ++ X, y, by rw [hX, hGs]; simp, rfl, rfl, hsy, le_refl _, ht⟩
    · rw [if_neg hkn] at hcval hLcval
      have hk' : k = n - 1 := by omega
      subst hk'
      rw [tau_v_last hq] at ht ⊢
      rw [hLcval] at ht ⊢
      rw [hcval] at hsy
      have hCLT : CL (M.take (r + L)) (r + q) = Lc' ++ c' :: R' := by
        rw [cl_take_B hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hq, ← hGdef, hGs]
      obtain ⟨hvv, hLL, ⟨Tl, hM⟩, yM, hsyM, hyy, htM⟩ :=
        frame_take_rw hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hCLT hsy ht
      rw [hvv]
      exact ⟨Lc', R' ++ Tl, yM, hM, rfl, hLL.symm, hsyM, hyy, htM⟩

/-- **The levels of `N` are levels of `M`** at the copied column. -/
theorem pathLvAll_N_t0 {c : Nat} {u : T} (h : PathLvAll (TRIO.gexp M r L 0 0 n) σ c u) :
    PathLvAll M ρ (phi0 r L c) u := by
  induction h with
  | top hcl hsy ht =>
    obtain ⟨Lc', R', yM, hM, hv, -, hsyM, -, htM⟩ :=
      frameMap_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hC1 hRk1 hGT hdrop hσB hoffD hσmid hσlast hLast hO'le hy' hdl hss _ _ _ _ hcl _ _ hsy ht
    rw [← hv] at htM ⊢
    exact PathLvAll.top hM hsyM htM
  | step hcl hsy ht _ ih =>
    obtain ⟨Lc', R', yM, hM, hv, -, hsyM, -, htM⟩ :=
      frameMap_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hC1 hRk1 hGT hdrop hσB hoffD hσmid hσlast hLast hO'le hy' hdl hss _ _ _ _ hcl _ _ hsy ht
    rw [← hv] at htM
    exact PathLvAll.step hM hsyM htM ih

/-- **`VSmallRAll` passes to `N = M[n]`** (`t = 0`): every rewriting frame of `N` and every level of `N` above
it are a rewriting frame and a level of `M` with the same subscript, parent value and state. -/
theorem vsmallRAll_N_t0 (hVA : VSmallRAll M ρ) : VSmallRAll (TRIO.gexp M r L 0 0 n) σ := by
  intro k c Lc R s y hcl hc ht hhz u hu hku g hg
  obtain ⟨Lc', R', yM, hM, hv, hLm, hsyM, hyy, htM⟩ :=
    frameMap_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hC1 hRk1 hGT hdrop hσB hoffD hσmid hσlast hLast hO'le hy' hdl hss k Lc c R hcl s y hc ht
  have hu' : u = ρ.v (phi0 r L k) ∨ PathLvAll M ρ (phi0 r L k) u :=
    hu.imp (fun h => h.trans hv.symm) (fun h => pathLvAll_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN hC1 hRk1 hGT hdrop hσB hoffD hσmid hσlast hLast hO'le hy' hdl hss h)
  rw [← hv] at hku htM
  have := hVA (phi0 r L k) (phi0 r L c) Lc' R' s yM hM hsyM htM (split_hi_ne_z_of_le hyy hhz) u hu' hku g hg
  rw [hv, hLm] at this
  exact this

end

end Ytosk
