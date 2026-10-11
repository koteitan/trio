/-
**3 行・t = 2: 1 列落としで種の o が実際に変わる（Res3T2 の seed1）、数える子でつながる場合。**

x = M.length − 1、M′ = M.take x、ρ′ = drop1 M x rk。
- q = r で x が r の数える子（upg(x − 1) ≠ x の場合、C′ 2 万行列で例外 0）: o′(r) < o(r) は
  o_strict_frame（c = x、x は M′ にないので帰納法の仮定は要らない）。
- q ≠ r: x は q の bump 子で、M′ では q は bump 子を失う。v(q) の ω の和の最後の項 1 が消えるので
  v′(q) < v(q)（`v_strict_bump_x`）、CL q = [] なので o′(q) = ψ_{v′(q)}(0) < o(q)。
  q が pq の数える子なら（C′ で 4221/4436 件）、q は pq の最後の子なので o_strict_frame で o′(pq) < o(pq)。
-/
import Ytosk.V3StrictR
import Ytosk.V3InvT2
import Ytosk.V3T2Top

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop

/-- **A counted child `x` is lost**: `o′(i) < o(i)`. -/
theorem o_strict_cl_x {i : Nat} (hi : i < x) (hxi : x ∈ CL M i) : ρ'.o i < ρ.o i :=
  o_strict_frame hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hi hxi
    (fun d hd => by have := (mem_children (cl_mem_children hd)).2; omega)
    (fun h => absurd h (Nat.lt_irrefl _))

/-- **The bump child `x` is lost**: `v′(i) < v(i)`. -/
theorem v_strict_bump_x {i : Nat} (hi : i < x) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    {L : List Nat} (hch : children M i = L ++ [x]) (hxb : col M x = bump M i) :
    ρ'.v i < ρ.v i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : i < (M.take x).length := by omega
  have hiM : i < M.length := by omega
  have hoff := chg_off hx hC hG hC' hRk'
  have hxM : x ∈ children M i := by rw [hch]; simp
  have hpx : par M 0 x = some i := (mem_children_iff.mp hxM).2
  -- the row-1 parent does not change
  have hV : vOpt ρ' (par (M.take x) 1 i) = vOpt ρ (par M 1 i) := by
    rw [par_take M 1 i hi]
    cases hp : par M 1 i with
    | none => rfl
    | some m =>
      show ρ'.v m = ρ.v m
      have hm := par_lt M 1 i m hp
      apply (hoff m (by omega)).2
      intro hCm
      exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCm).1 rfl (by omega) |>.2.2 i hi hp
  have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  -- the children of `i` in `M.take x`
  have hLx : ∀ d ∈ L, d < x := (sib_order (children_sorted M i) (R := []) (by rw [hch])).1
  have hchT : children (M.take x) i = L := by
    rw [children_take, hch, List.filter_append, List.filter_eq_self.mpr
      (fun d hd => by simp only [decide_eq_true_eq]; exact hLx d hd)]
    simp
  -- the earlier bump terms do not grow
  have hbtL : ∀ d ∈ L, bumpTerm (M.take x) ρ' i d ≤ bumpTerm M ρ i d := by
    intro d hd
    have hdx : d < x := hLx d hd
    unfold bumpTerm
    rw [col_take M hdx, bump_take M hi]
    split
    · have hex : ∀ e ∈ children M d, e < x := by
        intro e he
        have hel := (mem_children he).2
        rcases Nat.lt_or_ge e x with h | h
        · exact h
        · exfalso
          have hex : e = x := by omega
          rw [hex] at he
          have hdi : d = i := Option.some.inj ((mem_children_iff.mp he).2.symm.trans hpx)
          have hdM : d ∈ children M i := by rw [hch]; simp [hd]
          have := (mem_children hdM).1; omega
      have hchd : children (M.take x) d = children M d := by
        rw [children_take, List.filter_eq_self]
        intro e he; simp only [decide_eq_true_eq]; exact hex e he
      rw [hchd]
      have hot' : ∀ t ∈ (children M d).map ρ'.o, isOT t = true := by
        intro t ht; obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht; exact (hdrop e (hex e he)).1.2.1
      have hot : ∀ t ∈ (children M d).map ρ.o, isOT t = true := by
        intro t ht; obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o e (mem_children he).2
      exact omega_le_omega (isOT_sumN _ hot') (isOT_sumN _ hot)
        (sumN_le2 (forall2_map_le (fun e he => (hdrop e (hex e he)).1.le)) hot' hot)
    · exact le_refl _
  set Pl := one :: L.map (bumpTerm M ρ i) with hPl
  set Pl' := one :: L.map (bumpTerm (M.take x) ρ' i) with hPl'
  have hPlot : ∀ t ∈ Pl, isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i d
  have hPlot' : ∀ t ∈ Pl', isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm_of (fun e he => by
        rw [List.length_take] at he; exact (hdrop e (by omega)).1.2.1) i d
  have hbtx : bumpTerm M ρ i x = one := by
    unfold bumpTerm; rw [if_pos hxb, children_last_nil hx]; simp [omega_z]
  have hvM : ρ.v i = sf (add (vOpt ρ (par M 1 i)) (omega (sumN (Pl ++ [one])))) := by
    rw [(hC i hiM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, hch, List.map_append, List.map_singleton, hbtx, ← List.cons_append]
  have hvT : ρ'.v i = sf (add (vOpt ρ (par M 1 i)) (omega (sumN Pl'))) := by
    rw [(hC' i hiT).2]; unfold vRhs
    rw [entry_take M 1 hi, entry_take M 2 hi, if_neg h1, if_neg h2, hV, hchT]
  have hP'ot : isOT (sumN Pl') = true := isOT_sumN _ hPlot'
  have hPot : isOT (sumN (Pl ++ [one])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPlot t h
    · simp at h; rw [h]; rfl)
  have hle : sumN Pl' ≤ sumN Pl :=
    sumN_le2 (List.Forall₂.cons (le_refl _) (forall2_map_le hbtL)) hPlot' hPlot
  have hP : sumN Pl' < sumN (Pl ++ [one]) := sumN_lt_snoc hPlot rfl hle (T.z_lt_psi _ _ _)
  rw [hvM, hvT, sf_ot (isOT_add hVot (isOT_omega hP'ot)), sf_ot (isOT_add hVot (isOT_omega hPot))]
  exact add_lt_add_left _ (omega_lt_omega hP'ot hPot hP)

/-- **`q ≠ r`, `q` a counted child of `pq`**: `o′(pq) < o(pq)`. `x` is the bump child of `q` and `q` has no
counted child, so `v(q)` and then `o(q)` drop; `q` is the last child of `pq`. -/
theorem o_strict_qn {q pq : Nat} (hq : par M 0 x = some q) (hpq : par M 0 q = some pq)
    (hxb : col M x = bump M q) (h1q : entry M 1 q ≠ 0) (h2q : entry M 2 q ≠ 0) (hclq : CL M q = [])
    (hqcl : q ∈ CL M pq) : ρ'.o pq < ρ.o pq := by
  have hqx : q < x := par_lt M 0 x q hq
  have hpqq : pq < q := par_lt M 0 q pq hpq
  have hxq : x ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hqT : q < (M.take x).length := by omega
  have hqM : q < M.length := by omega
  -- `v(q)` and `o(q)` drop
  have hv : ρ'.v q < ρ.v q :=
    v_strict_bump_x hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hqx h1q h2q
      (children_split_x hx hxq) hxb
  have hCh : ChgX M x false q := by
    by_contra hn
    have := (chg_off hx hC hG hC' hRk' q hqx).2 hn
    rw [this] at hv; exact lt_irrefl _ hv
  have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCh).1 rfl hqx
  have ho : ρ'.o q < ρ.o q := by
    rw [o_of_no_counted hC' hqT (hdrop q hqx).2.2 hT.2.1, o_cl_eq hC hG hqM, hclq]
    exact psi_lt_psi_z_iff.mpr (Or.inl hv)
  -- `q` is the last counted child of `pq`
  have hAqx : Anc0 M q x := anc0_of_par M 0 q x hq
  apply o_strict_frame hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop (by omega) hqcl
  · intro d hd
    have hdc := cl_mem_children hd
    have hpd : par M 0 d = some pq := (mem_children_iff.mp hdc).2
    have hdl := (mem_children hdc).2
    by_contra hlt
    have hqd : q < d := by omega
    have hdx : d ≠ x := fun h => by rw [h, hq] at hpd; cases hpd; omega
    have hAqd : Anc0 M q d := anc_between hAqx d (by omega) (by omega)
    have := par0_ge_of_anc hAqd hqd (le_refl d) hpd
    omega
  · exact fun _ => ho

end

end Ytosk
