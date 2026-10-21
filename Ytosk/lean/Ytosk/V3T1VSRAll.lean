/-
**t = 1 の展開での VSmallRAll（2026-10-17、t1）。**

N = M[n]（t = 1、x = r + L）の書き換える枠 (k, c) は、M の枠 (φ k, φ c) に写る（φ は写しのブロックを
ブロック 0 に戻す写像 `phiT1`）。v(k)・添字・前の子の o（状態）は同じで、引数は M の方が大きい。
ただし写しの根 c（ブロックの根）の枠は例外で、そのとき φ k = φ c = r、v(k) = v(r)、
添字の成分は v(r) の成分で押さえられる（`FrameMapT1` の第 2 の場合）。
- 段の道 `PathLvAll` も枠ごとに M の道へ写る（`pathLvAll_mapT1`）。写しの根の枠を通るときは、
  段は v(r) か M の r での段。
- よって VSmallRAll N は VSmallRAll M だけから出る（`vsmallRAll_of_mapT1`）。P = M[n − 1] の VSmallRAll は要らない。
- `FrameMapT1` は 1 コピーごとに保たれる（`expStep_frameMapT1`）:
  - 接頭辞（k < x）: CL は M と同じ。書き換える子 c は v が D でない（D なら c は数える子を持たず引数 0）。
    前の子は D でない（p1_dep）。o は fsD で下がるので引数は M の方が大きい。
    c = x（写しの根）の枠は q = r のときだけ書き換える（q ≠ r なら v(q) > v(r) で Ω_{v(q)} ≥ o(x)）。
  - 写し（k ≥ x）: P の枠 (k − L, c − L) そのもの。φ は L ずらしで変わらない。
- 始点 M.take x（drop1）では `frame_take_rw`、v(r) の成分は PV の ◁ から。
-/
import Ytosk.V3ExpT1Inv2
import Ytosk.V3VSRAllDrop
import Ytosk.V3T0VSRAllN
import Ytosk.V3S1Std
import Ytosk.V3QRWeak

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The column of block 0 that a column of `M[n]` copies (`t = 1`). -/
def phiT1 (r L k : Nat) : Nat := if k < r then k else r + (k - r) % L

theorem phiT1_lt {r L k : Nat} (hk : k < r + L) : phiT1 r L k = k := by
  unfold phiT1; split_ifs with h
  · rfl
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem phiT1_shift {r L k : Nat} (hk : r ≤ k) : phiT1 r L (k + L) = phiT1 r L k := by
  unfold phiT1
  rw [if_neg (by omega), if_neg (by omega), show k + L - r = (k - r) + L by omega, Nat.add_mod_right]

theorem phiT1_x {r L : Nat} (hL : 0 < L) : phiT1 r L (r + L) = r := by
  unfold phiT1; rw [if_neg (by omega), show r + L - r = L by omega, Nat.mod_self]; rfl

/-- **The frames of `N` and those of `M`** (`t = 1`). -/
def FrameMapT1 (M : Mat) (ρ : Valn) (r L : Nat) (N : Mat) (σ : Valn) : Prop :=
  ∀ k c (Lc R : List Nat) s y, CL N k = Lc ++ c :: R → σ.o c = psi s y z →
    (lt (spArg (σ.v k) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v k) z z) (psi s y z) = true) →
    (∃ (Lc' R' : List Nat) (yM : T), CL M (phiT1 r L k) = Lc' ++ phiT1 r L c :: R' ∧
      σ.v k = ρ.v (phiT1 r L k) ∧ Lc'.map ρ.o = Lc.map σ.o ∧ ρ.o (phiT1 r L c) = psi s yM z ∧ y ≤ yM ∧
      (lt (spArg (ρ.v (phiT1 r L k)) z (sumN (Lc'.map ρ.o))) yM = true ∧
        lt (psi (ρ.v (phiT1 r L k)) z z) (psi s yM z) = true)) ∨
    (phiT1 r L k = r ∧ phiT1 r L c = r ∧ σ.v k = ρ.v r ∧
      ∀ u, ∀ g ∈ comps u s, g ≤ psi s z z ∨ ∃ d ∈ comps u (ρ.v r), g ≤ d)

/-- The components of `v(r)` in `N` are dominated by those in `M` (when `q = r`). -/
def VrDomQ (M : Mat) (ρ : Valn) (r L : Nat) (_N : Mat) (σ : Valn) : Prop :=
  par M 0 (r + L) = some r → ∀ u, ∀ g ∈ comps u (σ.v r), g ≤ psi (σ.v r) z z ∨ ∃ d ∈ comps u (ρ.v r), g ≤ d

section
variable {M : Mat} {ρ : Valn} {r L : Nat} {N : Mat} {σ : Valn}

/-- **The levels of `N` are levels of `M`** (through the copy roots: `v(r)` or the levels at `r`). -/
theorem pathLvAll_mapT1 (hF : FrameMapT1 M ρ r L N σ) {i : Nat} {u : T} (h : PathLvAll N σ i u) :
    PathLvAll M ρ (phiT1 r L i) u ∨ (phiT1 r L i = r ∧ (u = ρ.v r ∨ PathLvAll M ρ r u)) := by
  induction h with
  | @top k c Lc R s y hcl hsy ht =>
    rcases hF k c Lc R s y hcl hsy ht with ⟨Lc', R', yM, hM, hv, _, hsyM, _, htM⟩ | ⟨_, hφc, hv, _⟩
    · left; rw [hv]; exact PathLvAll.top hM hsyM htM
    · right; exact ⟨hφc, Or.inl hv⟩
  | @step k c Lc R s y u hcl hsy ht _ ih =>
    rcases hF k c Lc R s y hcl hsy ht with ⟨Lc', R', yM, hM, hv, _, hsyM, _, htM⟩ | ⟨hφk, hφc, _, _⟩
    · left
      rcases ih with ih | ⟨hφk, ih | ih⟩
      · exact PathLvAll.step hM hsyM htM ih
      · have := PathLvAll.top hM hsyM htM
        rw [hφk] at this; rw [ih]; exact this
      · rw [← hφk] at ih; exact PathLvAll.step hM hsyM htM ih
    · right
      refine ⟨hφc, ?_⟩
      rcases ih with ih | ⟨_, ih⟩
      · rw [hφk] at ih; exact Or.inr ih
      · exact ih

/-- **`VSmallRAll N` from `VSmallRAll M`** through the frame map. -/
theorem vsmallRAll_of_mapT1 (hF : FrameMapT1 M ρ r L N σ) (hVA : VSmallRAll M ρ) : VSmallRAll N σ := by
  intro k c Lc R s y hcl hsy ht hhz u hu hku g hg
  rcases hF k c Lc R s y hcl hsy ht with ⟨Lc', R', yM, hM, hv, hL, hsyM, hyy, htM⟩ | ⟨_, _, hv, hdom⟩
  · rw [hv] at hku ⊢
    rw [← hL]
    have hu' : u = ρ.v (phiT1 r L k) ∨ PathLvAll M ρ (phiT1 r L k) u := by
      rcases hu with hu | hu
      · exact Or.inl (hv ▸ hu)
      · rcases pathLvAll_mapT1 hF hu with h | ⟨hφ, h | h⟩
        · exact Or.inr h
        · exact Or.inl (by rw [hφ]; exact h)
        · exact Or.inr (by rw [hφ]; exact h)
    exact hVA _ _ Lc' R' s yM hM hsyM htM (split_hi_ne_z_of_le hyy hhz) u hu' hku g hg
  · rcases hdom u g hg with h | ⟨d, hd, hgd⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨d, hv ▸ hd, hgd⟩)

end

/-- `ψ_a(0) ≤ ψ_b(0)` from `a ≤ b`. -/
theorem psi_z_le {a b : T} (h : a ≤ b) : psi a z z ≤ psi b z z := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h))
  · exact le_refl _

section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
  (hR : Rk M rk) {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
  (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
include S hC hG hR hlen hL hd0e h1 hx2

/-- **The frame map survives each `t = 1` copy.** -/
theorem expStep_frameMapT1 :
    ExpStepT1 (fun N σ => FrameMapT1 M ρ r L N σ ∧ VrDomQ M ρ r L N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r < r + L := par_lt M 1 _ r h1
  obtain ⟨q0, hq0⟩ := par0_of_anc hA (by omega)
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hvr : ¬ DepX M (r + L) false r := not_depX_v_r1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2
  intro n hn ρP Z hCP hGP hPP hCN hGN _ _ hle hlex _
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
    (hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1 n hn)
    (hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn)
  have hCLeq : ∀ j, j < r + L → CL (TRIO.gexp M r L d0 0 n) j = CL M j := by
    intro j hj
    have hS := hSA j hj
    unfold CL; rw [hS.ch]
    apply List.filter_congr
    intro d hd
    exact decide_eq_decide.mpr (counted_iff_of_cnt (hS.cnt d hd))
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
  have hσvr : σ.v r = ρ.v r := by rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z hrx hvr]
  refine ⟨?_, fun _ u g hg => Or.inr ⟨g, hσvr ▸ hg, le_refl g⟩⟩
  intro k c Lc R s y hCL hsy hrw
  have hy0 : y ≠ z := ne_z_of_lt hrw.1
  rcases Nat.lt_or_ge k (r + L) with hk | hk
  · -- the frames before `x`
    rw [hCLeq k hk] at hCL
    have hcCL : c ∈ CL M k := by rw [hCL]; simp
    have hcch : c ∈ children M k := (List.mem_filter.mp hcCL).1
    have hccnt : Counted M k c := by simpa using (List.mem_filter.mp hcCL).2
    have hcM := (mem_children hcch).2
    have hkc := (mem_children hcch).1
    have h0 : par M 0 c = some k := (mem_children_iff.mp hcch).2
    have hvk : ¬ DepX M (r + L) false k := fun hv =>
      uncnt_of_depv hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq0 hk hv hcch hccnt
    have hσvk : σ.v k = ρ.v k := by rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z hk hvk]
    have hφk := phiT1_lt (r := r) (L := L) hk
    rcases Nat.lt_or_ge c (r + L) with hcx | hcx
    · -- an ordinary child
      left
      have hφc := phiT1_lt (r := r) (L := L) hcx
      rw [hφk, hφc]
      have hcN : c < (TRIO.gexp M r L d0 0 n).length := by rw [hlN]; omega
      have hcv : ¬ DepX M (r + L) false c := by
        intro hcd
        have hCLc : CL M c = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro d hd
          exact uncnt_of_depv hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq0 hcx hcd
            (List.mem_filter.mp hd).1 (by simpa using (List.mem_filter.mp hd).2)
        have hoc : σ.o c = psi (σ.v c) z z := by
          rw [o_cl_eq hCN hGN hcN, hCLeq c hcx, hCLc]; rfl
        rw [hoc] at hsy
        simp only [psi.injEq] at hsy
        exact hy0 hsy.2.1.symm
      have hσvc : σ.v c = ρ.v c := by rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z hcx hcv]
      obtain ⟨y1, hy1⟩ := o_psi_sub hCN hcN
      rw [hsy, sf_ot (hGN.ot_v c hcN), hσvc] at hy1
      simp only [psi.injEq] at hy1
      obtain ⟨hs, -⟩ := hy1
      obtain ⟨yM, hyM⟩ := o_psi_sub hC hcM
      rw [sf_ot (hG.ot_v c hcM), ← hs] at hyM
      have hole : σ.o c ≤ ρ.o c := by
        by_cases hD : DepX M (r + L) true c
        · rw [hσ, glueZ_o_dep ρ (shiftV ρP L) Z hcx hD]; exact (hle c hcx hD).1
        · rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hcx hD]
      rw [hsy, hyM] at hole
      have hyy := arg_le_of_psi_le hole
      have hLo : Lc.map ρ.o = Lc.map σ.o := by
        apply List.map_congr_left
        intro d hd
        have hdCL : d ∈ CL M k := by rw [hCL]; simp [hd]
        have hdch : d ∈ children M k := (List.mem_filter.mp hdCL).1
        have hdc : d < c := by
          have hs' : (CL M k).Pairwise (· < ·) := (children_sorted M k).filter _
          rw [hCL] at hs'
          exact (List.pairwise_append.mp hs').2.2 d hd c (by simp)
        have hdD : ¬ DepX M (r + L) true d := fun hD =>
          p1_dep hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq0 hk hdch hcch hdc hD hccnt
        rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z (by omega) hdD]
      refine ⟨Lc, R, yM, hCL, hσvk, hLo, hyM, hyy, ?_⟩
      rw [hLo, ← hσvk]
      exact rw_up hyy hrw
    · -- the copy root `x`
      right
      have hcxe : c = r + L := by omega
      subst hcxe
      have hkq : k = q0 := by rw [h0] at hq0; exact Option.some.inj hq0
      subst hkq
      have hkr : k = r := by
        by_contra hkr
        have hAk : Anc0 M r k := anc0_par hA (by omega) h0
        have hrk : r < k := lt_of_le_of_ne hAk.le (Ne.symm hkr)
        have hHi : HiR M r k := fun s hs1 hs2 hs3 =>
          hpath s hs1 (hs2.trans (Anc0.step h0 (Anc0.refl k))) hs3 (by have := hs2.le; omega)
        have hlt := v_chain_lt hC hG hR k hrk (by omega) hAk hHi
        have hox : ρ.o (r + L) = psi (succ (ρ.v r)) z z :=
          o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2
        have hσx : σ.o (r + L) = ρP.o r := by have := hσo 0; simpa using this
        have h2 := hrw.2
        rw [hσvk, ← hsy, hσx] at h2
        have h3 : ρP.o r ≤ psi (ρ.v k) z z :=
          le_trans hlex.1 (by rw [hox]; exact psi_z_le (succ_le_of_lt hlt))
        exact lt_irrefl' _ (lt_of_lt_of_le h2 h3)
      rw [hkr] at h0 hσvk hk ⊢
      refine ⟨phiT1_lt hk, phiT1_x hL, hσvk, ?_⟩
      have hxN : r + L < (TRIO.gexp M r L d0 0 n).length := by
        rw [hlN]; have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega
      obtain ⟨y1, hy1⟩ := o_psi_sub hCN hxN
      rw [hsy, sf_ot (hGN.ot_v _ hxN)] at hy1
      simp only [psi.injEq] at hy1
      have hsv : s = ρP.v r := by rw [hy1.1]; have := hσv 0; simpa using this
      rw [hsv]
      exact hPP.2 h0
  · -- the copies
    obtain ⟨a, rfl⟩ : ∃ a, k = r + L + a := ⟨k - (r + L), by omega⟩
    have hkN : r + L + a < (TRIO.gexp M r L d0 0 n).length := by
      have hcch : c ∈ children (TRIO.gexp M r L d0 0 n) (r + L + a) :=
        (List.mem_filter.mp (show c ∈ CL _ (r + L + a) by rw [hCL]; simp)).1
      have := mem_children hcch; omega
    have ha : a < (n - 1) * L := by rw [hlN] at hkN; omega
    have hCLs : CL (TRIO.gexp M r L d0 0 n) (r + L + a) =
        (CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a)).map (· + L) := by
      unfold CL
      rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha, List.filter_map]
      congr 1
      apply List.filter_congr
      intro d hd
      have hdc := mem_children hd
      rw [hlP] at hdc
      show decide (Counted (TRIO.gexp M r L d0 0 n) (r + L + a) (d + L)) =
        decide (Counted (TRIO.gexp M r L d0 0 (n - 1)) (r + a) d)
      apply decide_eq_decide.mpr
      apply counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath (S.z2 r) (ρ := ρ) (Z := Z) ha hd)
      · have := hσo (d - r); rw [show r + L + (d - r) = d + L by omega,
          show r + (d - r) = d by omega] at this
        exact this
      · obtain ⟨s, y, he⟩ := o_psi_form hCP (i := d) (by rw [hlP]; omega)
        rw [he]; simp
    rw [hCLs] at hCL
    obtain ⟨Lc', T', hsplit, hLc, hT⟩ := List.map_eq_append_iff.mp hCL
    obtain ⟨c', R', hT', hc', hR'⟩ := List.map_eq_cons_iff.mp hT
    subst hLc hc' hR'
    rw [hT'] at hsplit
    have hc'CL : c' ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp
    have hc'c := mem_children (List.mem_filter.mp hc'CL).1
    have hLo : (Lc'.map (· + L)).map σ.o = Lc'.map ρP.o := by
      rw [List.map_map]
      apply List.map_congr_left
      intro d hd
      have hdCL : d ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp [hd]
      have hdc := mem_children (List.mem_filter.mp hdCL).1
      have := hσo (d - r)
      rw [show r + L + (d - r) = d + L by omega, show r + (d - r) = d by omega] at this
      exact this
    have hoc : σ.o (c' + L) = ρP.o c' := by
      have := hσo (c' - r)
      rw [show r + L + (c' - r) = c' + L by omega, show r + (c' - r) = c' by omega] at this
      exact this
    rw [hoc] at hsy
    rw [hσv, hLo] at hrw
    have hφk : phiT1 r L (r + L + a) = phiT1 r L (r + a) := by
      rw [show r + L + a = (r + a) + L by omega]; exact phiT1_shift (by omega)
    have hφc : phiT1 r L (c' + L) = phiT1 r L c' := phiT1_shift (by omega)
    rw [hφk, hφc, hσv, hLo]
    exact hPP.1 (r + a) c' Lc' R' s y hsplit hsy hrw

end

/-- **The base**: `M.take x` with the drop valuation. -/
theorem frameMapT1_take {M : Mat} {ρ ρ' : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take (r + L)) ρ') (hRk' : Rk (M.take (r + L)) rk)
    (hlen : r + L + 1 = M.length) (hx2 : entry M 2 (r + L) = 0)
    (hdrop : ∀ i, i < r + L → PO ρ ρ' i ∧ PV M ρ ρ' i) (hUA : UpgAbsXW M (r + L) ρ) :
    FrameMapT1 M ρ r L (M.take (r + L)) ρ' ∧ VrDomQ M ρ r L (M.take (r + L)) ρ' := by
  constructor
  · intro k c Lc R s y hcl hsy ht
    left
    have hcT : c ∈ CL (M.take (r + L)) k := by rw [hcl]; simp
    have hcc := cl_mem_children hcT
    have hcx : c < r + L := by have := (mem_children hcc).2; rw [lenT hlen] at this; exact this
    have hkc : k < c := (mem_children hcc).1
    obtain ⟨hv, hL, ⟨Tl, hM⟩, yM, hsyM, hyy, htM⟩ :=
      frame_take_rw hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hC hG hC' hRk' hdrop hcl hsy ht
    rw [phiT1_lt (show k < r + L by omega), phiT1_lt hcx]
    exact ⟨Lc, R ++ Tl, yM, hM, hv, hL.symm, hsyM, hyy, htM⟩
  · intro hq u g hg
    have hrx : r < r + L := par_lt M 0 _ r hq
    rcases (hdrop r hrx).2.1 with h | ⟨_, _, hnc⟩
    · rcases h with h | h
      · exact Or.inr ⟨g, h ▸ hg, le_refl g⟩
      · obtain ⟨d, hd, hgd⟩ := h.2 u (ρ.v r) h.1 (le_refl _) g hg
        rcases List.mem_append.mp hd with hd | hd
        · exact Or.inr ⟨d, hd, hgd⟩
        · simp [Gc, comps] at hd; subst hd; exact Or.inl (le_trans hgd (z_le _))
    · rcases hnc with hn | ⟨_, _, k, W, hi2, hu, hvk, hWz, hbad⟩
      · exfalso
        have hxch : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
        apply hn (r + L) hxch
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have : entry M 2 (r + L) = (bump M r).2.2 := by rw [← h]; rfl
          rw [hx2] at this; simp [bump] at this
        · rw [not_isUpg_e2z hx2] at h; cases h.1
      · -- `r = x − 1` lost its upgrade: `v′(r) = v(P_1 r) + 1`, whose components are below `Ω_{v′(r)}`
        rcases hUA r k W (by omega) hu hvk hWz with h | ⟨_, hSm, _⟩
        · exact absurd h hbad
        · have h12 := upg_e12 hu
          have h2r : entry M 2 r = 0 := by have := S.z2 r; omega
          have hvr := v_last_take (x := r + L) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hC hG hC' hRk'
            (r := r) (by omega) h12.1 h2r
          have hVot : isOT (add (vOpt ρ (par M 1 r)) one) = true :=
            isOT_add (vOpt_ot hG (by omega)) isOT_one
          rw [hvr, sf_ot hVot] at hg ⊢
          exact Or.inl (le_of_lt (hSm g (comps_mono (z_le u) hg)))

/-- **`ExpT1OutV2` from the frame and leaf residuals and `S1`** (VSmallRAll is proved, `expStep_frameMapT1`). -/
theorem expT1Out_V2 (hF : HFrameV2) (hLf : HLeafV2) (hS1 : S1Std) : ExpT1OutV2 := by
  intro M ρ rk C hz h1t n hn
  have I := C.I
  have S := C.S
  obtain ⟨r, hr⟩ := parLast_of S.e00 S.r01 S.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h1t] at hr
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  have hx2 : entry M 2 (M.length - 1) = 0 := by
    unfold TRIO.srow at h1t
    by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
    · rw [if_pos ha] at h1t; cases h1t
    · show TRIO.entry M 2 (M.length - 1) = 0; omega
  have hexp := expand_eq_gexp_t1 M n hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hStdN : Std (expand M n) := Std.exp n C.std
  have hdr := C.R.drop
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hI1 := (C.pre (r + L) (by omega) (by omega)).1
  rw [hL] at hexp hr hx2 hdr
  simp only [Nat.add_sub_cancel_left] at hexp
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  have hPR : PassRootRes M r L ρ := passRootRes_of_S1 (sInvXJ_std C.std C.ne).1 (hS1 M C.std C.ne) hlen hr hx2
  have hstep : ExpStepT1 (fun N σ => T1Core r ρ N σ ∧ (FrameMapT1 M ρ r L N σ ∧ VrDomQ M ρ r L N σ)) M r L
      (entry M 0 (r + L) - entry M 0 r) ρ :=
    expStep_and (expStep_core_vsmallF_pass_inv3V2 S I hlen hL0 hd0e hr hx2 hPR)
      (expStep_frameMapT1 S I.cons I.good I.rank hlen hL0 hd0e hr hx2)
  have hdrop := drop_all hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hI1.cons hI1.rank
    I.vs hdr.vst I.fc I.fo hdr.argT
    (bump_drop hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hI1.cons hI1.rank
      I.kd I.td hdr.ab hdr.ws) hdr.ua
  have hbase : T1Core r ρ (M.take (r + L)) (drop1 M (r + L) rk) ∧
      (FrameMapT1 M ρ r L (M.take (r + L)) (drop1 M (r + L) rk) ∧
        VrDomQ M ρ r L (M.take (r + L)) (drop1 M (r + L) rk)) :=
    ⟨(t1_base S I hlen hr hdr hI1).1,
      frameMapT1_take S I.cons I.good hI1.cons hI1.rank hlen hx2 hdrop hdr.ua⟩
  rw [hexp] at hStdN ⊢
  have hfin : ∃ ρN rkN, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) rkN ∧
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      (T1Core r ρ (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
        (FrameMapT1 M ρ r L (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
          VrDomQ M ρ r L (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN)) ∧
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN < root M ρ := by
    by_cases hq : par M 0 (r + L) = some r
    · exact qr_final4S hlen hL0 hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
        hr hx2 hq I.cons I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
        I.tp1w I.tplow I.auwl I.auw0 I.adw I.tp1 I.trigs I.tplon I.adn I.rootS I.rootP
        _ hbase hstep n hn
    · have hrM : r < M.length := by omega
      obtain ⟨br, hro⟩ := o_psi_sub I.cons hrM
      rw [sf_ot (I.good.ot_v r hrM)] at hro
      have hne : (drop1 M (r + L) rk).o r ≠ ρ.o r :=
        ne_of_lt (o_r_strict0 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2
          hr hx2 hq I.cons I.good hI1.cons hI1.rank hdrop)
      exact t1_main_vlocS hlen hL0 hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
        hr hx2 hq I.cons I.good I.rank I.vs I.fc I.fo I.tp1 I.tplos I.ads I.aus hdr.argT
        I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua hne rfl hro I.rootS I.rootP hI1.good
        _ hbase hstep n hn
  obtain ⟨ρN, rkN, hCN, hRN, hGN, ⟨hcore, hmap, _⟩, hot, hlt⟩ := hfin
  have hNE : TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [len_N (d0 := entry M 0 (r + L) - entry M 0 r) hlen (show 2 ≤ n from hn)]
    omega
  have hNS := ne_SRO_of_rk hRN
  obtain ⟨hTP, hTPW⟩ := hLf _ ρN rkN hStdN hNS hNE hCN hRN hGN
  exact ⟨ρN, rkN, inv3V2_of_core hRN hcore (vsmallRAll_of_mapT1 hmap I.vra)
    (hF _ ρN rkN hStdN hNS hNE hCN hRN hGN) hTP hTPW, hot, hlt⟩

/-- `S1Std` holds (`S1_std`, V3S1Std). -/
theorem s1Std : S1Std := fun _ hM _ => S1_std hM

/-- **`ExpT1OutV2` from the shared frame and leaf residuals only.** -/
theorem expT1Out_V2_glob (hF : HFrameV2) (hLf : HLeafV2) : ExpT1OutV2 :=
  expT1Out_V2 hF hLf s1Std

end Ytosk
