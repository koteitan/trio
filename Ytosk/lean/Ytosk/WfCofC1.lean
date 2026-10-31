/-
**WfCofC1 (2026-11-01): the `t = 0` core, and `HCountS` for `t = 0`.**

For a standard `A ≠ SRO` whose last column `x = r + L` has type `t = 0` (`lastTy A = 0`, bad root `r = P_0(x)`),
`A[n] = gexp A r L 0 0 n` (`expand_eq_gexp_t0`, `d0 = d1 = 0`): the copies `r + kL` are row-0 siblings of `r`.
`t0_core` (from `t0_vals` of V3T0V, `HGood3` and the structural invariants `sInv_std`): for `n ≥ 2` the true
valuation `σ` of `A[n]` satisfies

- `σ.o c = o_A(c)` for `c < r`, `c ∉ DepX A x true`,
- `σ.o (r + kL) = omid = ψ_{v(r)}(Y0)` for `k + 1 < n` (the middle copy roots),
- `σ.o (r + (n−1)L) = o_{A[1]}(r)` (`A[1] = A.take x`, valuation `drop1`),
- `o_A(r) = ψ_{v(r)}(Y0 + 1)` (`o_r_omid`).

`HCountS` for `t = 0` (`hCountS0_of`):
- `r` a root: the roots of `A[k+2]` are the roots before `r` (values kept) and the copy roots `r + jL`;
  `fsD(tA, k) = S + omid·k ≤ S + omid·(k+1) + o_{A[1]}(r) = val(A[k+2])`. **Proved** (from `HGood3`, `HRootSP`).
- `r` not a root: the last root `Rt < r` is a strict ancestor of `r`; the roots before `Rt` keep their values and
  `fsD(tA, k) = S + fsD(o(Rt), k)`. The remaining fact is the count bound at `Rt` (`HCntPath0`).
-/
import Ytosk.WfCofH3
import Ytosk.V3T0VS
import Ytosk.V3T0Root
import Ytosk.V3DropRel

namespace Ytosk.WfCofC1

open T Ytosk Ytosk.WfCofH2 Ytosk.WfCofH3

set_option linter.unusedSectionVars false

theorem e12_zero_of_lastTy0 {A : Mat} (h : lastTy A = 0) :
    entry A 1 (A.length - 1) = 0 ∧ entry A 2 (A.length - 1) = 0 := by
  unfold lastTy at h
  by_cases h2 : entry A 2 (A.length - 1) > 0
  · rw [if_pos h2] at h; cases h
  · rw [if_neg h2] at h
    by_cases h1 : entry A 1 (A.length - 1) > 0
    · rw [if_pos h1] at h; cases h
    · omega

/-- **The `t = 0` core.** -/
theorem t0_core (hG : HGood3) (A : Mat) (hAs : Std A) (hS : A ≠ SRO) (hE : A ≠ [])
    (hz : col A (A.length - 1) ≠ (0, 0, 0)) (ht : lastTy A = 0) (r : Nat) (hr : BRoot A r)
    (ρ : Valn) (rkA : Bool → Nat → Nat) (hC : Cons A ρ) (hRA : Rk A rkA)
    (n : Nat) (hn2 : 2 ≤ n) (σ : Valn) (rkN : Bool → Nat → Nat)
    (hCN : Cons (expand A n) σ) (hRN : Rk (expand A n) rkN) :
    let L := A.length - 1 - r
    r < A.length - 1 ∧ expand A n = TRIO.gexp A r L 0 0 n ∧
    (∀ c, c < r → ¬ DepX A (A.length - 1) true c → σ.o c = ρ.o c) ∧
    (∀ k, k + 1 < n → σ.o (r + k * L) = omid A r L ρ) ∧
    σ.o (r + (n - 1) * L) = (drop1 A (r + L) rkA).o r ∧
    ρ.o r = psi (ρ.v r) (app (spArg (ρ.v r) z
      (sumN (((children A r).filter (fun c => decide (c < r + L))).map (cnt A ρ r)))) one) z ∧
    omid A r L ρ = psi (ρ.v r) (spArg (ρ.v r) z
      (sumN (((children A r).filter (fun c => decide (c < r + L))).map (cnt A ρ r)))) z ∧
    (∀ g, par A 0 r = some g → ∀ k, k < n → par (expand A n) 0 (r + k * L) = some g) := by
  intro L
  have I := sInv_std hAs hS
  have hpos : 0 < A.length := List.length_pos_of_ne_nil hE
  have hr0 : par A 0 (A.length - 1) = some r := by
    have := hr; unfold BRoot at this; rw [ht] at this; exact this
  have hrx : r < A.length - 1 := par_lt A 0 _ r hr0
  have hlen : r + L + 1 = A.length := by omega
  have hL : 0 < L := by omega
  have hxe : A.length - 1 = r + L := by omega
  have hp : par A 0 (r + L) = some r := by rw [← hxe]; exact hr0
  have hn : 1 ≤ n := by omega
  obtain ⟨he1, he2⟩ := e12_zero_of_lastTy0 ht
  rw [hxe] at he1 he2
  have hsrow : TRIO.srow A (A.length - 1) = 0 := by rw [← WfCofH1.lastTy_eq]; exact ht
  have hzT : ¬ (TRIO.entry A 0 (A.length - 1) = 0 ∧ TRIO.entry A 1 (A.length - 1) = 0 ∧
      TRIO.entry A 2 (A.length - 1) = 0) := fun h => hz ((col_zero_iff A _).mpr h)
  have hpar : par A (TRIO.srow A (A.length - 1)) (A.length - 1) = some r := by rw [hsrow]; exact hr0
  have hexp : expand A n = TRIO.gexp A r L 0 0 n := expand_eq_gexp_t0 A n (by omega) hzT hpar hsrow
  have hGA := hG A ρ rkA hAs hS hE hC hRA
  rw [hexp] at hCN hRN
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sibDec I.z1c I.uat
  have hRk1 : Rk (A.take (r + L)) rkA := rk_take (by omega) hRA hcnt
  set ρ' := drop1 A (r + L) rkA with hρ'
  have hC1 : Cons (A.take (r + L)) ρ' := cons_of_rk hRk1
  have hoff := chg_off hlen hC hGA hC1 hRk1
  have hvD := t0_vals hlen hL hp hn I.r0p I.z2 I.sibDec I.z1c I.uat I.uab he2 hn2 (depLike_depX A (r + L))
    (read_not_dep hlen hL hp I.r0p I.z2 I.sibDec I.z1c I.uat I.uab) hC hGA hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hlN : (TRIO.gexp A r L 0 0 n).length = r + n * L := lenN0 hlen hn
  have hσB : ∀ i, r ≤ i → i < r + n * L → σ.o i = (tauN r L n ρ ρ' (omid A r L ρ)).o i :=
    fun i hri hiN => (hvD i (by rw [hlN]; exact hiN)).1 (fun h => by omega)
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn I.r0p I.z2 I.sibDec I.z1c I.uat I.uab he1 he2 hn2 hC hGA
  refine ⟨hrx, hexp, ?_, ?_, ?_, hor, hom, ?_⟩
  · intro c hc hd
    rw [hxe] at hd
    rw [(hvD c (by rw [hlN]; omega)).1 (fun h => hd h.2), tau_o_lt hc]
  · intro k hk
    have : k * L + L ≤ n * L := by
      have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
    rw [hσB _ (by omega) (by omega)]
    exact tau_o_root hk hL
  · have hnl : (n - 1) * L + L = n * L := by rw [← Nat.succ_mul]; congr 1; omega
    rw [hσB _ (by omega) (by omega)]
    have := tau_o_last (r := r) (L := L) (n := n) (ρ := ρ) (ρ' := ρ') (oMid := omid A r L ρ) hL
    rwa [Nat.add_zero, Nat.add_zero] at this
  · intro g hg k hk
    rw [hexp]
    have := par0_gexp_root_t0 (d1 := 0) hlen hL hk (anc0_of_par A 0 r (r + L) hp) hg
    rwa [Nat.add_zero] at this

/-! ## `HCountS` for `t = 0` -/

/-- `HCountS` restricted to `t = 0`. -/
def HCountS0 : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) → lastTy A = 0 →
    ∀ tA, Val A tA → ∀ a b, SuccAt a b tA → ∀ k tN, Val (expand A (k + 2)) tN → fsD tA (natT k) ≤ tN

/-- **The count bound at the last root** (`t = 0`, `r` not a root): for a root `c` that is a strict row-0
ancestor of `r`, `fsD(o_A(c), k) ≤ o_{A[k+2]}(c)`. -/
def HCntPath0 : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) → lastTy A = 0 →
    ∀ tA, Val A tA → ∀ a b, SuccAt a b tA → ∀ r, BRoot A r → ∀ ρA rkA, Cons A ρA → Rk A rkA →
    ∀ k σ rk, Cons (expand A (k + 2)) σ → Rk (expand A (k + 2)) rk →
    ∀ c, Anc0 A c (A.length - 1) → c < r → col A c = (0, 0, 0) → fsD (ρA.o c) (natT k) ≤ σ.o c

theorem fsD_succArg (v Y : T) (k : Nat) : fsD (psi v (app Y one) z) (natT k) = mulT (psi v Y z) k := by
  have hne : app Y one ≠ z := fun h => by simp [one] at h; exact absurd (app_eq_z h).2 (by simp)
  have hs : isSucc (app Y one) = true := isSucc_succ Y
  rw [← (SuccAt.here hne hs (a := v)).fs_eq_fsD, fs_succ_arg]

theorem hCountS0_of (hG : HGood3) (hRS : HRootSP) (hP : HCntPath0) : HCountS0 := by
  intro A hAs hS hNE hz ht tA hv a b hSA k tN hvN
  have I := sInv_std hAs hS
  obtain ⟨r, hr0⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hr : BRoot A r := by rw [BRoot, WfCofH1.lastTy_eq]; exact hr0
  obtain ⟨ρA, rkA, hCA, hRA, rfl⟩ := hv
  obtain ⟨σ, rkN, hCN, hRN, rfl⟩ := hvN
  have hpos : 0 < A.length := List.length_pos_of_ne_nil hNE
  have hx : A.length - 1 + 1 = A.length := by omega
  obtain ⟨hrx, hexp, hcore, hmid, hlast, hor, hom, _⟩ :=
    t0_core hG A hAs hS hNE hz ht r hr ρA rkA hCA hRA (k + 2) (by omega) σ rkN hCN hRN
  set L := A.length - 1 - r with hLd
  have hlen : r + L + 1 = A.length := by omega
  have hL : 0 < L := by omega
  have hxe : A.length - 1 = r + L := by omega
  have hr0' : par A 0 (A.length - 1) = some r := by
    have := hr; unfold BRoot at this; rw [ht] at this; exact this
  have hp : par A 0 (r + L) = some r := by rw [← hxe]; exact hr0'
  have hA0 : Anc0 A r (A.length - 1) := anc0_of_par A 0 r _ hr0'
  obtain ⟨hsA, hpA⟩ := hRS A ρA rkA hAs hCA hRA
  obtain ⟨hsN, hpN⟩ := hRS _ σ rkN (Std.exp _ hAs) hCN hRN
  cases hgr : par A 0 r with
  | none =>
    -- `r` is a root: the copies are new roots
    have hn1 : 1 ≤ k + 2 := by omega
    have hrootsA := roots_M_root hlen hL hp hn1 I.r01 I.r12 I.e00 hgr
    have hrootsN := roots_N_root hlen hL hp hn1 I.r01 I.r12 I.e00 hgr
    rw [← hexp] at hrootsN
    set pre := (List.range r).filter (fun i => decide (col A i = (0, 0, 0))) with hpre
    have hpre_lt : ∀ c ∈ pre, c < r := by
      intro c hc; rw [hpre, List.mem_filter] at hc; exact List.mem_range.mp hc.1
    have hcr : col A r = (0, 0, 0) := col_r_root hlen hL hp hn1 I.r01 I.r12 I.e00 hgr
    have hRl : ∀ j, r < j → j ≤ A.length - 1 → entry A 0 j ≠ 0 := by
      intro j h1 h2
      have := anc0_interval hA0 j h1 h2
      have := e0_of_col hcr
      omega
    have hpre_eq : ∀ c ∈ pre, σ.o c = ρA.o c := by
      intro c hc
      have hcR := hpre_lt c hc
      apply hcore c hcR
      intro hd
      have := depX_ge hx (e0_of_col hcr) (by omega) hRl hd
      omega
    have hMl : (roots A).map ρA.o = pre.map ρA.o ++ [ρA.o r] := by
      rw [hrootsA, List.map_append, List.map_singleton]
    have hcopies : ((List.range (k + 2)).map (fun j => r + j * L)).map σ.o =
        List.replicate (k + 1) (omid A r L ρA) ++ [σ.o (r + (k + 2 - 1) * L)] := by
      rw [List.range_succ, List.map_append, List.map_append, List.map_singleton, List.map_singleton]
      congr 1
      rw [List.map_map]
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range, Function.comp, List.getElem_replicate]
        simp only [List.length_map, List.length_range] at h1
        exact hmid i (by omega)
    have hNl : (roots (expand A (k + 2))).map σ.o =
        pre.map ρA.o ++ (List.replicate (k + 1) (omid A r L ρA) ++ [σ.o (r + (k + 2 - 1) * L)]) := by
      rw [hrootsN, List.map_append, hcopies]
      congr 1
      exact List.map_congr_left hpre_eq
    have hsAl : ∀ t ∈ pre.map ρA.o ++ [ρA.o r], Single t := by
      intro t ht'
      rw [← hMl] at ht'
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht'
      exact hsA i hi
    have hsNl : ∀ t ∈ pre.map ρA.o ++ (List.replicate (k + 1) (omid A r L ρA) ++ [σ.o (r + (k + 2 - 1) * L)]),
        Single t := by
      intro t ht'
      rw [← hNl] at ht'
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht'
      exact hsN i hi
    have hrootA : root A ρA = app (sumN (pre.map ρA.o)) (ρA.o r) := by
      rw [root_eq_roots hsA hpA, hMl]
      rw [hMl] at hpA
      exact sumN_snoc_dec hsAl hpA
    have hpN' := hpN
    rw [hNl] at hpN'
    have hrootN : root (expand A (k + 2)) σ = app (sumN (pre.map ρA.o))
        (app (sumN (List.replicate (k + 1) (omid A r L ρA))) (sumN [σ.o (r + (k + 2 - 1) * L)])) := by
      rw [root_eq_roots hsN hpN, hNl, sumN_append_dec hsNl hpN']
      congr 1
      have hs2 : ∀ t ∈ List.replicate (k + 1) (omid A r L ρA) ++ [σ.o (r + (k + 2 - 1) * L)], Single t :=
        fun t ht' => hsNl t (List.mem_append_right _ ht')
      exact sumN_append_dec hs2 (List.pairwise_append.mp hpN').2.1
    have hsO : Single (omid A r L ρA) :=
      hsNl _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_replicate.mpr ⟨by omega, rfl⟩)))
    have hRne : ρA.o r ≠ z := by rw [hor]; simp
    show fsD (root A ρA) (natT k) ≤ root (expand A (k + 2)) σ
    rw [hrootA, hrootN, fsD_app _ hRne, sumN_replicate hsO]
    apply app_le_app_left
    rw [hor, fsD_succArg, ← hom]
    refine le_trans ?_ (le_app_self _ _)
    rw [hom]
    exact mulT_le_of_le _ _ (by omega)
  | some g =>
    -- `r` is not a root: the last root `Rt < r` keeps the roots before it
    have hn1 : 1 ≤ k + 2 := by omega
    have hroots : roots (expand A (k + 2)) = roots A := by
      rw [hexp]; exact roots_N_par hlen hL hp hn1 I.r0p hgr
    obtain ⟨Rt, hRA0, hR0, hRl⟩ := root_t1 I.r01 I.r12 I.e00 (A.length - 1)
    have hR0e : entry A 0 Rt = 0 := e0_of_col hR0
    have hRr : Rt < r := by
      have hr0p := I.r0p r g hgr
      rcases Nat.lt_or_ge Rt r with h | h
      · exact h
      · exfalso
        rcases Nat.eq_or_lt_of_le h with h' | h'
        · rw [h'] at hr0p; omega
        · have := anc0_interval hA0 Rt h' hRA0.le
          omega
    have hEP := hP A hAs hS hNE hz ht _ ⟨ρA, rkA, hCA, hRA, rfl⟩ a b hSA r hr ρA rkA hCA hRA k σ rkN hCN hRN
      Rt hRA0 hRr hR0
    have hsplit := roots_split hx hRA0 hR0
    set pre := (roots A).filter (fun c => decide (c < Rt)) with hpre
    have hpre_lt : ∀ c ∈ pre, c < Rt := by
      intro c hc; rw [hpre, List.mem_filter] at hc; simpa using hc.2
    have hpre_eq : ∀ c ∈ pre, σ.o c = ρA.o c := by
      intro c hc
      have hcR := hpre_lt c hc
      apply hcore c (by omega)
      intro hd
      have := depX_ge hx hR0e hRA0.le hRl hd
      omega
    have hMl : (roots A).map ρA.o = pre.map ρA.o ++ [ρA.o Rt] := by
      rw [hsplit, List.map_append, List.map_singleton]
    have hNl : (roots (expand A (k + 2))).map σ.o = pre.map ρA.o ++ [σ.o Rt] := by
      rw [hroots, hsplit, List.map_append, List.map_singleton]
      congr 1
      exact List.map_congr_left hpre_eq
    have hsAl : ∀ t ∈ pre.map ρA.o ++ [ρA.o Rt], Single t := by
      intro t ht'
      rw [← hMl] at ht'
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht'
      exact hsA i hi
    have hsNl : ∀ t ∈ pre.map ρA.o ++ [σ.o Rt], Single t := by
      intro t ht'
      rw [← hNl] at ht'
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht'
      exact hsN i hi
    have hrootA : root A ρA = app (sumN (pre.map ρA.o)) (ρA.o Rt) := by
      rw [root_eq_roots hsA hpA, hMl]
      rw [hMl] at hpA
      exact sumN_snoc_dec hsAl hpA
    have hrootN : root (expand A (k + 2)) σ = app (sumN (pre.map ρA.o)) (σ.o Rt) := by
      rw [root_eq_roots hsN hpN, hNl]
      rw [hNl] at hpN
      exact sumN_snoc_dec hsNl hpN
    have hRne : ρA.o Rt ≠ z := by
      obtain ⟨s, y, hsy⟩ := o_psi_form hCA (i := Rt) (by omega)
      rw [hsy]; simp
    show fsD (root A ρA) (natT k) ≤ root (expand A (k + 2)) σ
    rw [hrootA, hrootN, fsD_app _ hRne]
    exact app_le_app_left _ hEP

/-- `HCountS` restricted to `t ≠ 0` (measured: `t = 1` never has the successor-argument type). -/
def HCountS12 : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) → lastTy A ≠ 0 →
    ∀ tA, Val A tA → ∀ a b, SuccAt a b tA → ∀ k tN, Val (expand A (k + 2)) tN → fsD tA (natT k) ≤ tN

theorem hCountS_of (h0 : HCountS0) (h12 : HCountS12) : HCountS := by
  intro A hA hS hE hz tA hv a b hSA k tN hvN
  by_cases ht : lastTy A = 0
  · exact h0 A hA hS hE hz ht tA hv a b hSA k tN hvN
  · exact h12 A hA hS hE hz ht tA hv a b hSA k tN hvN

/-- **`EvalFSNZ 2`** with `HCountS` for `t = 0` replaced by the count bound at the last root. -/
theorem evalFSNZ2_of_C (hD : Desc3) (hG : HGood3) (hT : HDiagT1) (hE : HEngPath) (hRS : HRootSP)
    (h3 : HCID) (hP : HCntPath0) (h12 : HCountS12) : EvalFSNZ 2 :=
  evalFSNZ2_of_H hD hG hT hE hRS h3 (hCountS_of (hCountS0_of hG hRS hP) h12)

end Ytosk.WfCofC1
