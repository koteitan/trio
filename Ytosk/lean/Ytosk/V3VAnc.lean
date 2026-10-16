/-
**VAnc を行 1 の 1 段から（2026-10-17、t0）。**

`VAnc σ p j`（V3RwClSh）: v(p) の成分は Ω_{v(j)} 以下か v(j) の成分以下。行 1 の 1 段（j の行 1 の親 p）で
立ち（`VAncStep`）、行 1 の親へ v が増えれば（`VMono1`）、行 1 の祖先のすべてに広がる（`vAnc_of_le1`）。
1 段の中身: v(j) = v(p) + t で、add が落とす v(p) の加数 q（q < t の先頭）の成分が t の成分か Ω_{v(j)} で
押さえられること。測定（tmp/t0/probes/vanc1.py、std_a・ext2・ext1 各 2 万、d3s 1.5 万）で 73434 件例外 0。
-/
import Ytosk.V3RwClSh
import Ytosk.V3ExpT2C

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **One row-1 step** of `VAnc`. -/
def VAncStep (N : Mat) (σ : Valn) : Prop :=
  ∀ c m, c < N.length → par N 1 c = some m → VAnc σ m c

/-- `v` does not decrease from the row-1 parent. -/
def VMono1 (N : Mat) (σ : Valn) : Prop :=
  ∀ c m, c < N.length → par N 1 c = some m → σ.v m ≤ σ.v c

/-- `v` does not decrease along row-1 descent. -/
theorem v_le_of_le1 {N : Mat} {σ : Valn} (hM : VMono1 N σ) :
    ∀ n p c, c < n → TRIO.le1 N p c → σ.v p ≤ σ.v c
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, p, c, hcn, h => by
    by_cases hcp : c = p
    · subst hcp; exact le_refl _
    · obtain ⟨m, hm, hpm⟩ := le1_par1_down h hcp
      have hmc := par_lt N 1 c m hm
      exact le_trans (v_le_of_le1 hM n p m (by omega) hpm) (hM c m h.2.1 hm)

/-- **`VAnc` along row-1 descent** from one step and the monotonicity of `v`. -/
theorem vAnc_of_le1 {N : Mat} {σ : Valn} (hS : VAncStep N σ) (hM : VMono1 N σ) :
    ∀ n p c, c < n → TRIO.le1 N p c → VAnc σ p c
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, p, c, hcn, h => by
    by_cases hcp : c = p
    · subst hcp; exact vAnc_refl σ c
    · obtain ⟨m, hm, hpm⟩ := le1_par1_down h hcp
      have hmc := par_lt N 1 c m hm
      exact vAnc_trans (hM c m h.2.1 hm) (vAnc_of_le1 hS hM n p m (by omega) hpm) (hS c m h.2.1 hm)

theorem le_sf_add {X t : T} (hX : isOT X = true) (ht : isOT t = true) (hs : t = z ∨ ∃ s y, t = psi s y z) :
    X ≤ sf (add X t) := by
  rw [sf_ot (isOT_add hX ht)]
  rcases hs with rfl | hs
  · rw [add_z_right]
  · exact le_add_of_single X hs

/-- **`VMono1` from the value equation.** -/
theorem vMono1_of {N : Mat} {σ : Valn} (hC : Cons N σ) (hG : Good3 N σ) : VMono1 N σ := by
  intro c m hc hm
  have hnr := (par1_iff N hc).mp hm
  have he1 : entry N 1 c ≠ 0 := by
    intro h0
    have h' := hnr.2.2.2.1
    rw [show TRIO.entry N 1 c = entry N 1 c from rfl, h0] at h'
    omega
  have hmc : m < c := par_lt N 1 c m hm
  have hmo : isOT (σ.v m) = true := hG.ot_v m (by omega)
  have hv := (hC c hc).2
  unfold vRhs at hv
  rw [if_neg he1, hm] at hv
  simp only [vOpt] at hv
  rw [hv]
  split_ifs with h2
  · cases hu : upg N c with
    | none => exact le_sf_add hmo rfl (Or.inr ⟨z, z, rfl⟩)
    | some k =>
      show σ.v m ≤ sf (add (σ.v m) (last (σ.v k)))
      have hko : isOT (σ.v k) = true := hG.ot_v k (upg_lt hc hu)
      refine le_sf_add hmo (isOT_last hko) ?_
      by_cases hk : σ.v k = z
      · left; rw [hk]; rfl
      · right; exact last_single' hk
  · refine le_sf_add hmo (isOT_omega (isOT_sumN _ ?_)) (Or.inr (omega_single _))
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG c d

/-- **`VAnc` along row-1 descent** in a valued matrix, from the one-step condition. -/
theorem vAnc_of_step {N : Mat} {σ : Valn} (hC : Cons N σ) (hG : Good3 N σ) (hS : VAncStep N σ)
    {p c : Nat} (h : TRIO.le1 N p c) : VAnc σ p c :=
  vAnc_of_le1 hS (vMono1_of hC hG) (c + 1) p c (Nat.lt_succ_self c) h

/-! ## 写しの列の行 1 の祖先 -/

/-- **A guarded column of `P = M[n − 1]` moves to a row-1 descendant of `r + L` in `N = M[n]`** (`t = 2`). -/
theorem le1_copy2 {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
    (hd0 : 0 < d0) (hd1 : 0 < d1) (hgx : TRIO.le1 M r (r + L)) :
    ∀ k i, i < k → r ≤ i → i < r + (n - 1) * L → TRIO.le1 (TRIO.gexp M r L d0 d1 (n - 1)) r i →
      TRIO.le1 (TRIO.gexp M r L d0 d1 n) (r + L) (i + L)
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, i, hik, hri, hi, hg => by
    have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
    have hnL : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
    by_cases hir : i = r
    · subst hir; exact le1_self (by rw [hlN]; omega)
    · obtain ⟨m, hm, hgm⟩ := le1_par1_down hg hir
      have hmi : m < i := par_lt _ 1 i m hm
      have hrm : r ≤ m := le1_ge hgm
      have ih := le1_copy2 hlen hL hA hd0e hn hd0 hd1 hgx k m (by omega) hrm (by omega) hgm
      have hp := par1_copy2 hlen hL hA hd0e hn hd0 hd1 hgx (j := i - r) (by omega) (by omega)
      rw [show r + (i - r) = i by omega, hm] at hp
      simp only [Option.map_some, if_pos hrm] at hp
      rw [show r + L + (i - r) = i + L by omega] at hp
      exact le1_par1_up ih hp (by rw [hlN]; omega)

end Ytosk
