/-
**3 行・t = 0: 展開 N の値（1）目標の割り当て τ と列ごとの等式。**

N = M[n] = gexp M r L 0 0 n（n ≥ 2）の値を、目標の割り当て `tauN` と比べる。
- r より前: M の値。中間のコピー（k < n − 1）: M の値（根の o だけ `omid` = x を除いた r の子の状態）。
  最後のコピー: M′ = M.take x の値。
- `cons_agree`: τ が N の等式を、依存で閉じた呼び出しの集合の上で満たせば、N の値はそこで τ に等しい。
- 列ごとの等式: 中間のコピー（`eqo_mid`・`eqv_mid`）、中間の根（`eqo_root`・`eqv_root`）、最後のコピー
  （`eqo_last`・`eqv_last`）。x − 1 の上げの先は r 以前（`upg_xm1_le`）、B の中の数え方は M′ と M で同じ
  （`counted_take_B`）。
-/
import Ytosk.V3T0S

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Partial uniqueness.** If `τ` satisfies the equations of `N` at every call outside `E`, and these
calls read only calls outside `E`, then the valuation `σ` of `N` equals `τ` there. -/
theorem cons_agree {N : Mat} {σ τ : Valn} {rk : Bool → Nat → Nat} (E : Bool → Nat → Prop)
    (hCN : Cons N σ) (hR : Rk N rk)
    (ho : ∀ i, i < N.length → ¬ E true i → τ.o i = oRhs N τ i)
    (hv : ∀ i, i < N.length → ¬ E false i → τ.v i = vRhs N τ i)
    (hdo : ∀ i, i < N.length → ¬ E true i →
      ¬ E false i ∧ ∀ c ∈ children N i, Counted N i c → ¬ E true c)
    (hdv : ∀ i, i < N.length → ¬ E false i → entry N 1 i ≠ 0 →
      (∀ m, par N 1 i = some m → ¬ E false m) ∧
      (entry N 2 i = 0 → ∀ k, upg N i = some k → ¬ E false k) ∧
      (entry N 2 i ≠ 0 → ∀ j ∈ children N i, col N j = bump N i → ∀ k ∈ children N j,
        ¬ E true k)) :
    ∀ i, i < N.length → (¬ E true i → σ.o i = τ.o i) ∧ (¬ E false i → σ.v i = τ.v i) := by
  have key : ∀ K, ∀ i, i < N.length → (rk true i ≤ K → ¬ E true i → σ.o i = τ.o i) ∧
      (rk false i ≤ K → ¬ E false i → σ.v i = τ.v i) := by
    intro K
    induction K using Nat.strongRecOn with
    | _ K ih =>
      have hvv : ∀ i, i < N.length → rk false i ≤ K → ¬ E false i → σ.v i = τ.v i := by
        intro i hi hK hE
        obtain ⟨_, _, hRi⟩ := hR i hi
        rw [(hCN i hi).2, hv i hi hE]
        apply vRhs_congr
        · intro m h1 hm
          have hlt' := (hRi h1).1 m hm
          exact (ih _ (by omega) m (by have := par_lt N 1 i m hm; omega)).2 (Nat.le_refl _)
            ((hdv i hi hE h1).1 m hm)
        · intro k h1 h2 hk
          have hlt' := (hRi h1).2.1 h2 k hk
          exact (ih _ (by omega) k (upg_lt hi hk)).2 (Nat.le_refl _) ((hdv i hi hE h1).2.1 h2 k hk)
        · intro j hj h1 h2 hb k hk
          have hlt' := (hRi h1).2.2 h2 j hj hb k hk
          exact (ih _ (by omega) k (mem_children hk).2).1 (Nat.le_refl _)
            ((hdv i hi hE h1).2.2 h2 j hj hb k hk)
      refine fun i hi => ⟨fun hK hE => ?_, hvv i hi⟩
      obtain ⟨hvo, hc, _⟩ := hR i hi
      obtain ⟨hEv, hEc⟩ := hdo i hi hE
      rw [(hCN i hi).1, ho i hi hE]
      apply oRhs_congr
      · exact hvv i hi (by omega) hEv
      · intro c hcm hbc huc
        have hlt' := hc c hcm hbc huc
        exact (ih _ (by omega) c (mem_children hcm).2).1 (Nat.le_refl _) (hEc c hcm ⟨hbc, huc⟩)
  intro i hi
  exact ⟨fun hE => (key _ i hi).1 (Nat.le_refl _) hE, fun hE => (key _ i hi).2 (Nat.le_refl _) hE⟩

/-- **The target valuation of `N`**: `M` before `r` and on the middle copies (the roots' `o` is `oMid`),
`M.take x` on the last copy. -/
def tauN (r L n : Nat) (ρ ρ' : Valn) (oMid : T) : Valn :=
  ⟨fun i => if i < r then ρ.o i else if i < r + (n - 1) * L then
      (if (i - r) % L = 0 then oMid else ρ.o (phi0 r L i)) else ρ'.o (phi0 r L i),
   fun i => if i < r then ρ.v i else if i < r + (n - 1) * L then ρ.v (phi0 r L i)
      else ρ'.v (phi0 r L i)⟩

section tau
variable {r L n : Nat} {ρ ρ' : Valn} {oMid : T}

theorem tau_o_lt {i : Nat} (hi : i < r) : (tauN r L n ρ ρ' oMid).o i = ρ.o i := by
  simp only [tauN, if_pos hi]

theorem tau_v_lt {i : Nat} (hi : i < r) : (tauN r L n ρ ρ' oMid).v i = ρ.v i := by
  simp only [tauN, if_pos hi]

theorem tau_v_mid {k q : Nat} (hk : k + 1 < n) (hq : q < L) :
    (tauN r L n ρ ρ' oMid).v (r + (k * L + q)) = ρ.v (r + q) := by
  have : k * L + L ≤ (n - 1) * L := by
    have := Nat.mul_le_mul_right L (show k + 1 ≤ n - 1 by omega); rw [Nat.succ_mul] at this; exact this
  simp only [tauN, if_neg (show ¬ r + (k * L + q) < r by omega),
    if_pos (show r + (k * L + q) < r + (n - 1) * L by omega), phi0_copy hq]

theorem tau_o_mid {k q : Nat} (hk : k + 1 < n) (hq : q < L) (hq0 : 0 < q) :
    (tauN r L n ρ ρ' oMid).o (r + (k * L + q)) = ρ.o (r + q) := by
  have : k * L + L ≤ (n - 1) * L := by
    have := Nat.mul_le_mul_right L (show k + 1 ≤ n - 1 by omega); rw [Nat.succ_mul] at this; exact this
  have hmod : (r + (k * L + q) - r) % L = q := by
    rw [show r + (k * L + q) - r = q + L * k by rw [Nat.mul_comm]; omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hq]
  simp only [tauN, if_neg (show ¬ r + (k * L + q) < r by omega),
    if_pos (show r + (k * L + q) < r + (n - 1) * L by omega), hmod, if_neg (show q ≠ 0 by omega),
    phi0_copy hq]

theorem tau_o_root {k : Nat} (hk : k + 1 < n) (hL : 0 < L) :
    (tauN r L n ρ ρ' oMid).o (r + k * L) = oMid := by
  have : k * L + L ≤ (n - 1) * L := by
    have := Nat.mul_le_mul_right L (show k + 1 ≤ n - 1 by omega); rw [Nat.succ_mul] at this; exact this
  have hmod : (r + k * L - r) % L = 0 := by
    rw [show r + k * L - r = L * k by rw [Nat.mul_comm]; omega, Nat.mul_mod_right]
  simp only [tauN, if_neg (show ¬ r + k * L < r by omega),
    if_pos (show r + k * L < r + (n - 1) * L by omega), hmod, if_true]

theorem tau_o_last {q : Nat} (hq : q < L) :
    (tauN r L n ρ ρ' oMid).o (r + ((n - 1) * L + q)) = ρ'.o (r + q) := by
  simp only [tauN, if_neg (show ¬ r + ((n - 1) * L + q) < r by omega),
    if_neg (show ¬ r + ((n - 1) * L + q) < r + (n - 1) * L by omega), phi0_copy hq]

theorem tau_v_last {q : Nat} (hq : q < L) :
    (tauN r L n ρ ρ' oMid).v (r + ((n - 1) * L + q)) = ρ'.v (r + q) := by
  simp only [tauN, if_neg (show ¬ r + ((n - 1) * L + q) < r by omega),
    if_neg (show ¬ r + ((n - 1) * L + q) < r + (n - 1) * L by omega), phi0_copy hq]

/-- `v` of `τ` on `M.take x` with `n ≥ 2` (the first copy is a middle copy). -/
theorem tau_v_x {t : Nat} (hn2 : 2 ≤ n) (ht : t < r + L) :
    (tauN r L n ρ ρ' oMid).v t = ρ.v t := by
  rcases Nat.lt_or_ge t r with h | h
  · exact tau_v_lt h
  · have := tau_v_mid (r := r) (L := L) (n := n) (ρ := ρ) (ρ' := ρ') (oMid := oMid) (k := 0) (q := t - r)
      (by omega) (by omega)
    rwa [show r + (0 * L + (t - r)) = t by simp; omega, show r + (t - r) = t by omega] at this

end tau

theorem foldl_zeros : ∀ (l2 : List T) (acc : T), isOT acc = true → (∀ t ∈ l2, t = z) →
    l2.foldl (fun a b => sf (add a b)) acc = acc
  | [], _, _, _ => rfl
  | t :: l2, acc, hacc, h => by
    have ht : t = z := h t (by simp)
    simp only [List.foldl_cons]
    rw [ht, add_z_right, sf_ot hacc]
    exact foldl_zeros l2 acc hacc (fun u hu => h u (by simp [hu]))

/-- Appending zeros does not change `sumN`. -/
theorem sumN_append_zeros {l : List T} (hl : ∀ t ∈ l, isOT t = true) (l2 : List T)
    (h : ∀ t ∈ l2, t = z) : sumN (l ++ l2) = sumN l := by
  unfold sumN
  rw [List.foldl_append]
  exact foldl_zeros l2 _ (isOT_sumN l hl) h

/-! ## 右辺の比較の一般形 -/

theorem cnt_eq_of {N M0 : Mat} {τ ρ0 : Valn} {i c i0 c0 : Nat}
    (hiff : Counted N i c ↔ Counted M0 i0 c0) (ho : τ.o c = ρ0.o c0) : cnt N τ i c = cnt M0 ρ0 i0 c0 := by
  classical
  rw [cnt_eq_ite, cnt_eq_ite]
  by_cases h : Counted M0 i0 c0
  · rw [if_pos (hiff.mpr h), if_pos h, ho]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

theorem bumpTerm_eq_of {N M0 : Mat} {τ ρ0 : Valn} {i j i0 j0 : Nat}
    (hcol : col N j = bump N i ↔ col M0 j0 = bump M0 i0)
    (hch : col M0 j0 = bump M0 i0 → (children N j).map τ.o = (children M0 j0).map ρ0.o) :
    bumpTerm N τ i j = bumpTerm M0 ρ0 i0 j0 := by
  unfold bumpTerm
  by_cases h : col M0 j0 = bump M0 i0
  · rw [if_pos (hcol.mpr h), if_pos h, hch h]
  · rw [if_neg (fun h' => h (hcol.mp h')), if_neg h]

theorem vRhs_eq_of {N M0 : Mat} {τ ρ0 : Valn} {i i0 : Nat}
    (h1 : entry N 1 i = entry M0 1 i0) (h2 : entry N 2 i = entry M0 2 i0)
    (hp : entry M0 1 i0 ≠ 0 → vOpt τ (par N 1 i) = vOpt ρ0 (par M0 1 i0))
    (hu : entry M0 1 i0 ≠ 0 → entry M0 2 i0 = 0 →
      (upg N i).map (fun k => last (τ.v k)) = (upg M0 i0).map (fun k => last (ρ0.v k)))
    (hb : entry M0 1 i0 ≠ 0 → entry M0 2 i0 ≠ 0 →
      sumN (one :: (children N i).map (bumpTerm N τ i)) =
        sumN (one :: (children M0 i0).map (bumpTerm M0 ρ0 i0))) :
    vRhs N τ i = vRhs M0 ρ0 i0 := by
  unfold vRhs
  rw [h1, h2]
  by_cases e1 : entry M0 1 i0 = 0
  · rw [if_pos e1, if_pos e1]
  · rw [if_neg e1, if_neg e1, hp e1]
    by_cases e2 : entry M0 2 i0 = 0
    · rw [if_pos e2, if_pos e2]
      have h := hu e1 e2
      cases hN : upg N i with
      | none =>
        cases hM : upg M0 i0 with
        | none => rfl
        | some k => rw [hN, hM] at h; cases h
      | some k =>
        cases hM : upg M0 i0 with
        | none => rw [hN, hM] at h; cases h
        | some k' =>
          rw [hN, hM] at h
          simp only [Option.map_some, Option.some.injEq] at h
          simp only [h]
    · rw [if_neg e2, if_neg e2, hb e1 e2]

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
include hlen hL hp hn

omit hn in
/-- `x` is not upgraded to (its row 2 is `0`). -/
theorem isUpg_x0 (he2 : entry M 2 (r + L) = 0) : isUpg M (r + L) = false := by
  unfold isUpg
  rw [List.any_eq_false]
  intro k _ hk
  exact upg_ne_e2z (of_decide_eq_true hk) he2

omit hn in
/-- **`o(r)` is in `ChgX`** (through the counted child `x`). -/
theorem chgX_r (he2 : entry M 2 (r + L) = 0) : ChgX M (r + L) true r := by
  have hx : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
  refine ChgX.ochild hx ?_ ?_ ChgX.leaf
  · intro h
    have : entry M 2 (r + L) = (col M (r + L)).2.2 := rfl
    rw [this, h] at he2; simp [bump] at he2
  · rw [isUpg_x0 hlen hL hp he2]; simp

/-- A child at or after `r` of a column before `r` in `N`: the column is `g` and the child is a copy root. -/
theorem child_ge_r {i c : Nat} (hi : i < r) (hc : c ∈ children (TRIO.gexp M r L 0 0 n) i) (hcr : r ≤ c) :
    par M 0 r = some i ∧ ∃ k, k < n ∧ c = r + k * L := by
  by_cases hig : par M 0 r = some i
  · refine ⟨hig, ?_⟩
    rw [children_g0 hlen hL hp hn hig] at hc
    rcases List.mem_append.mp hc with hc | hc
    · have := children_g_le hlen hL hp hig hc
      exact ⟨0, by omega, by omega⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
      exact ⟨k + 1, by have := List.mem_range.mp hk; omega, rfl⟩
  · rw [children_pre0 hlen hL hp hn hi hig] at hc
    have := children_lt_r hlen hL hp hi hig hc
    omega

/-- A child before `r` of a column before `r` in `N` is a child in `M`. -/
theorem child_lt_r {i c : Nat} (hi : i < r) (hc : c ∈ children (TRIO.gexp M r L 0 0 n) i) (hcr : c < r) :
    c ∈ children M i := by
  by_cases hig : par M 0 r = some i
  · rw [children_g0 hlen hL hp hn hig] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hc
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc; omega
  · rwa [children_pre0 hlen hL hp hn hi hig] at hc

/-- A child of a column before `r` in `N` has its parent before `r` or is a copy root. -/
theorem col_root0 {k : Nat} (hk : k < n) : col (TRIO.gexp M r L 0 0 n) (r + k * L) = col M r := by
  have h1 := col_copy0 hlen hk hL (M := M) (n := n) (k := k) (q := 0)
  rw [Nat.add_zero, Nat.add_zero] at h1
  exact h1

omit hlen hL hp hn in
theorem shk_B {k q : Nat} : shk r (k * L) (r + q) = r + (k * L + q) := by
  unfold shk; rw [if_pos (by omega)]; omega

omit hn in
/-- The children of a non-root column of `B` are before `x`. -/
theorem children_B_lt {q : Nat} (hq0 : 0 < q) :
    (children M (r + q)).filter (fun c => decide (c < r + L)) = children M (r + q) := by
  rw [List.filter_eq_self]
  intro c hc
  have h := mem_children_iff.mp hc
  simp only [decide_eq_true_eq]
  by_contra hc'
  have : c = r + L := by omega
  rw [this, hp] at h
  have := h.2; simp at this; omega

omit hn in
/-- **An upgrade from `x − 1` lands at `r` or before.** -/
theorem upg_xm1_le (hR0 : R0P M) (he2 : entry M 2 (r + L) = 0) {t : Nat}
    (hu : upg M (r + (L - 1)) = some t) : t ≤ r := by
  obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
  rcases hcase with h | ⟨hA, hlt⟩
  · exfalso
    have := upg_target_e2 hu
    rw [h, show r + (L - 1) + 1 = r + L by omega] at this; omega
  · by_contra htr
    have he0 := upg_climb_e0 hu (by omega)
    rw [show r + (L - 1) + 1 = r + L by omega] at he0
    have := e0_B_gt hlen hL hp (q := t - r) (by omega) (by omega)
    rw [show r + (t - r) = t by omega] at this
    have hR := hR0 _ _ hp
    omega

omit hn in
/-- **Upgrades into the non-root columns of `B`** are the same in `M.take x`. -/
theorem isUpg_take_B (hR0 : R0P M) (he2 : entry M 2 (r + L) = 0) {q : Nat} (hq : q < L) (hq0 : 0 < q) :
    isUpg (M.take (r + L)) (r + q) = isUpg M (r + q) := by
  apply Bool.eq_iff_iff.mpr
  rw [isUpg_take M (by omega)]
  unfold isUpg
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hu⟩
    exact ⟨j, List.mem_range.mpr (by omega), by simpa using hu⟩
  · rintro ⟨j, hj, hu⟩
    have hu' : upg M j = some (r + q) := by simpa using hu
    refine ⟨j, ?_, hu'⟩
    have hj' := List.mem_range.mp hj
    by_contra hjx
    rcases Nat.lt_or_ge j (r + L) with h | h
    · have : j = r + (L - 1) := by omega
      rw [this] at hu'
      have := upg_xm1_le hlen hL hp hR0 he2 hu'
      omega
    · have : j + 1 = M.length := by omega
      unfold upg at hu'; rw [if_pos (Or.inr (Or.inr this))] at hu'; cases hu'

omit hn in
/-- **Counting inside `B`** is the same in `M.take x`. -/
theorem counted_take_B (hR0 : R0P M) (he2 : entry M 2 (r + L) = 0) {q q' : Nat} (hq : q < L)
    (hq' : q' < L) (hq'0 : 0 < q') :
    Counted (M.take (r + L)) (r + q) (r + q') ↔ Counted M (r + q) (r + q') := by
  unfold Counted
  rw [col_take M (show r + q' < r + L by omega), bump_take M (show r + q < r + L by omega),
    isUpg_take_B hlen hL hp hR0 he2 hq' hq'0, topped_take_B hlen hL hp hq' hq'0]

omit hlen hL hp hn in
theorem tau_v_shk {ρ ρ' : Valn} {oMid : T} {k t : Nat} (hk : k + 1 < n) (ht : t < r + L) :
    (tauN r L n ρ ρ' oMid).v (shk r (k * L) t) = ρ.v t := by
  unfold shk
  split
  · rename_i h
    rw [show t + k * L = r + (k * L + (t - r)) by omega, tau_v_mid hk (by omega),
      show r + (t - r) = t by omega]
  · exact tau_v_lt (by omega)

omit hL hp in
theorem bump_copy0 {k q : Nat} (hk : k < n) (hq : q < L) :
    bump (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) = bump M (r + q) := by
  unfold bump; rw [entry_copy0 hlen hk hq 0, entry_copy0 hlen hk hq 1]

omit hn in
theorem lt_x_of_child_B {q c : Nat} (hq0 : 0 < q) (hc : c ∈ children M (r + q)) : c < r + L := by
  have h := mem_children_iff.mp hc
  by_contra hc'
  have : c = r + L := by omega
  rw [this, hp] at h
  have := h.2; simp at this; omega

/-- The value read by an upgrade of a middle copy. -/
theorem hu_mid (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) {ρ ρ' : Valn} {oMid : T}
    {k q : Nat} (hk : k + 1 < n) (hq : q < L)
    (hvr : upg M (r + (L - 1)) = some r → ρ'.v r = ρ.v r) :
    (upg (TRIO.gexp M r L 0 0 n) (r + (k * L + q))).map (fun t => last ((tauN r L n ρ ρ' oMid).v t)) =
      (upg M (r + q)).map (fun t => last (ρ.v t)) := by
  by_cases hq1 : q + 1 < L
  · rw [upg_copy0 hlen hL hp hn (by omega) hq1, Option.map_map]
    cases hU : upg M (r + q) with
    | none => rfl
    | some t =>
      simp only [Option.map_some, Function.comp, Option.some.injEq]
      have ht : t < M.length := upg_lt (by omega) hU
      have htx : t ≠ r + L := fun h => upg_ne_e2z hU (by rw [h]; exact he2)
      rw [tau_v_shk (oMid := oMid) (ρ' := ρ') hk (by omega)]
  · have hqL : q = L - 1 := by omega
    subst hqL
    rw [upg_copy_last0 hlen hL hp hn hR0 hZ2 he2 hk, Option.map_map]
    cases hU : upg M (r + (L - 1)) with
    | none => rfl
    | some t =>
      simp only [Option.map_some, Function.comp, Option.some.injEq]
      split
      · rename_i htr
        subst htr
        rcases Nat.lt_or_ge (k + 2) n with hk2 | hk2
        · have := tau_v_mid (r := t) (L := L) (n := n) (ρ := ρ) (ρ' := ρ') (oMid := oMid) (k := k + 1)
            (q := 0) hk2 hL
          rw [Nat.add_zero, Nat.add_zero] at this
          rw [this, Nat.add_zero]
        · have hkn : k + 1 = n - 1 := by omega
          have := tau_v_last (r := t) (L := L) (n := n) (ρ := ρ) (ρ' := ρ') (oMid := oMid) (q := 0) hL
          rw [Nat.add_zero, Nat.add_zero, ← hkn] at this
          rw [this, hvr hU]
      · rename_i htr
        have := upg_xm1_le hlen hL hp hR0 he2 hU
        rw [tau_v_lt (by omega)]

theorem eqo_mid (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) {ρ ρ' : Valn} {oMid : T}
    (hC : Cons M ρ) {k q : Nat} (hk : k + 1 < n) (hq : q < L) (hq0 : 0 < q) :
    oRhs (TRIO.gexp M r L 0 0 n) (tauN r L n ρ ρ' oMid) (r + (k * L + q)) = ρ.o (r + q) := by
  rw [(hC (r + q) (by omega)).1]
  unfold oRhs
  rw [children_copy0 hlen hL hp hn (by omega) hq, children_B_lt hlen hL hp hq0, List.map_map,
    tau_v_mid hk hq]
  congr 3
  apply List.map_congr_left
  intro c hc
  have hcgt := (mem_children hc).1
  have hcx := lt_x_of_child_B hlen hL hp hq0 hc
  obtain ⟨q', rfl⟩ : ∃ q', c = r + q' := ⟨c - r, by omega⟩
  simp only [Function.comp]
  rw [shk_B]
  exact cnt_eq_of (counted_copy0 hlen hL hp hn hR0 hZ2 he2 (by omega) hq (by omega) (by omega))
    (tau_o_mid hk (by omega) (by omega))

/-- A bump term of a middle copy. -/
theorem bt_mid {ρ ρ' : Valn} {oMid : T} {k q q' : Nat} (hk : k + 1 < n) (hq : q < L) (hq' : q' < L)
    (hq'0 : 0 < q') :
    bumpTerm (TRIO.gexp M r L 0 0 n) (tauN r L n ρ ρ' oMid) (r + (k * L + q)) (r + (k * L + q')) =
      bumpTerm M ρ (r + q) (r + q') := by
  apply bumpTerm_eq_of
  · rw [col_copy0 hlen (by omega) hq', bump_copy0 hlen hn (by omega) hq]
  · intro _
    rw [children_copy0 hlen hL hp hn (by omega) hq', children_B_lt hlen hL hp hq'0, List.map_map]
    apply List.map_congr_left
    intro d hd
    have hdgt := (mem_children hd).1
    have hdx := lt_x_of_child_B hlen hL hp hq'0 hd
    obtain ⟨q'', rfl⟩ : ∃ q'', d = r + q'' := ⟨d - r, by omega⟩
    simp only [Function.comp]
    rw [shk_B, tau_o_mid hk (by omega) (by omega)]

theorem eqv_mid (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) {ρ ρ' : Valn} {oMid : T}
    (hC : Cons M ρ) (hvr : upg M (r + (L - 1)) = some r → ρ'.v r = ρ.v r)
    {k q : Nat} (hk : k + 1 < n) (hq : q < L) (hq0 : 0 < q) :
    vRhs (TRIO.gexp M r L 0 0 n) (tauN r L n ρ ρ' oMid) (r + (k * L + q)) = ρ.v (r + q) := by
  rw [(hC (r + q) (by omega)).2]
  apply vRhs_eq_of (entry_copy0 hlen (by omega) hq 1) (entry_copy0 hlen (by omega) hq 2)
  · intro _
    rw [par1_copy0 hlen hL hp hn (by omega) hq]
    cases hP : par M 1 (r + q) with
    | none => rfl
    | some m =>
      have := par_lt M 1 _ _ hP
      exact tau_v_shk hk (by omega)
  · intro _ _; exact hu_mid hlen hL hp hn hR0 hZ2 he2 hk hq hvr
  · intro _ _
    rw [children_copy0 hlen hL hp hn (by omega) hq, children_B_lt hlen hL hp hq0, List.map_map]
    congr 2
    apply List.map_congr_left
    intro c hc
    have hcgt := (mem_children hc).1
    have hcx := lt_x_of_child_B hlen hL hp hq0 hc
    obtain ⟨q', rfl⟩ : ∃ q', c = r + q' := ⟨c - r, by omega⟩
    simp only [Function.comp]
    rw [shk_B]
    exact bt_mid hlen hL hp hn hk hq (by omega) (by omega)

/-- **`o` of a middle copy root.** -/
noncomputable def omid (M : Mat) (r L : Nat) (ρ : Valn) : T :=
  sf (psi (ρ.v r) (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r))) z)

theorem eqo_root (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) {ρ ρ' : Valn} {oMid : T}
    {k : Nat} (hk : k + 1 < n) :
    oRhs (TRIO.gexp M r L 0 0 n) (tauN r L n ρ ρ' oMid) (r + (k * L + 0)) = omid M r L ρ := by
  unfold oRhs omid
  rw [children_copy0 hlen hL hp hn (by omega) hL, List.map_map, tau_v_mid hk hL, Nat.add_zero]
  congr 3
  apply List.map_congr_left
  intro c hc
  rw [List.mem_filter] at hc
  have hcgt := (mem_children hc.1).1
  have hcx : c < r + L := by simpa using hc.2
  obtain ⟨q', rfl⟩ : ∃ q', c = r + q' := ⟨c - r, by omega⟩
  simp only [Function.comp]
  rw [shk_B]
  have := counted_copy0 hlen hL hp hn hR0 hZ2 he2 (k := k) (q := 0) (q' := q') (by omega) hL (by omega)
    (by omega)
  rw [Nat.add_zero, Nat.add_zero] at this
  exact cnt_eq_of this (tau_o_mid hk (by omega) (by omega))

theorem eqv_root (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) {ρ ρ' : Valn} {oMid : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hvr : upg M (r + (L - 1)) = some r → ρ'.v r = ρ.v r)
    {k : Nat} (hk : k + 1 < n) :
    vRhs (TRIO.gexp M r L 0 0 n) (tauN r L n ρ ρ' oMid) (r + (k * L + 0)) = ρ.v r := by
  have hr0 : r + 0 = r := Nat.add_zero r
  have e := (hC r (by omega)).2
  rw [e]
  apply vRhs_eq_of (by rw [entry_copy0 hlen (by omega) hL 1, hr0])
    (by rw [entry_copy0 hlen (by omega) hL 2, hr0])
  · intro _
    rw [par1_copy0 hlen hL hp hn (by omega) hL, hr0]
    cases hP : par M 1 r with
    | none => rfl
    | some m =>
      have := par_lt M 1 _ _ hP
      exact tau_v_shk hk (by omega)
  · intro _ _
    have := hu_mid hlen hL hp hn hR0 hZ2 he2 (ρ := ρ) (ρ' := ρ') (oMid := oMid) hk hL hvr
    rwa [hr0] at this
  · intro _ _
    have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
    rw [children_copy0 hlen hL hp hn (by omega) hL, hr0, List.map_map]
    conv_rhs => rw [children_split_x (x := r + L) hlen hxr]
    rw [List.map_append, ← List.cons_append]
    have hbx : bumpTerm M ρ r (r + L) = z := by
      unfold bumpTerm
      rw [if_neg]
      intro h
      have : entry M 2 (r + L) = (col M (r + L)).2.2 := rfl
      rw [this, h] at he2; simp [bump] at he2
    rw [List.map_singleton, hbx, sumN_append_zeros (by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG r j) [z] (by simp)]
    congr 2
    apply List.map_congr_left
    intro c hc
    rw [List.mem_filter] at hc
    have hcgt := (mem_children hc.1).1
    have hcx : c < r + L := by simpa using hc.2
    obtain ⟨q', rfl⟩ : ∃ q', c = r + q' := ⟨c - r, by omega⟩
    simp only [Function.comp]
    rw [shk_B]
    have := bt_mid hlen hL hp hn (ρ := ρ) (ρ' := ρ') (oMid := oMid) (k := k) (q := 0) (q' := q') hk hL
      (by omega) (by omega)
    rwa [Nat.add_zero] at this

omit hlen hL hp hn in
theorem tau_v_shk_last {ρ ρ' : Valn} {oMid : T} {t : Nat} (hrt : r ≤ t) (ht : t < r + L) :
    (tauN r L n ρ ρ' oMid).v (shk r ((n - 1) * L) t) = ρ'.v t := by
  unfold shk
  rw [if_pos hrt, show t + (n - 1) * L = r + ((n - 1) * L + (t - r)) by omega, tau_v_last (by omega),
    show r + (t - r) = t by omega]

omit hlen hL hp hn in
theorem shk_lt {s t : Nat} (ht : t < r) : shk r s t = t := by unfold shk; rw [if_neg (by omega)]

theorem eqo_last (hR0 : R0P M) (hZ2 : Z2 M) (he2 : entry M 2 (r + L) = 0) {ρ ρ' : Valn} {oMid : T}
    (hC' : Cons (M.take (r + L)) ρ') {q : Nat} (hq : q < L) :
    oRhs (TRIO.gexp M r L 0 0 n) (tauN r L n ρ ρ' oMid) (r + ((n - 1) * L + q)) = ρ'.o (r + q) := by
  rw [(hC' (r + q) (by rw [List.length_take]; omega)).1]
  unfold oRhs
  rw [children_copy0 hlen hL hp hn (by omega) hq, children_take, List.map_map, tau_v_last hq]
  congr 3
  apply List.map_congr_left
  intro c hc
  rw [List.mem_filter] at hc
  have hcgt := (mem_children hc.1).1
  have hcx : c < r + L := by simpa using hc.2
  obtain ⟨q', rfl⟩ : ∃ q', c = r + q' := ⟨c - r, by omega⟩
  simp only [Function.comp]
  rw [shk_B]
  exact cnt_eq_of ((counted_copy0 hlen hL hp hn hR0 hZ2 he2 (by omega) hq (by omega) (by omega)).trans
    (counted_take_B hlen hL hp hR0 he2 hq (by omega) (by omega)).symm) (tau_o_last (by omega))

theorem eqv_last {ρ ρ' : Valn} {oMid : T} (hC' : Cons (M.take (r + L)) ρ') {q : Nat} (hq : q < L)
    (hread : ∀ m, m < r → (par M 1 (r + q) = some m ∨ upg M (r + q) = some m) → ρ'.v m = ρ.v m)
    (he2 : entry M 2 (r + L) = 0) :
    vRhs (TRIO.gexp M r L 0 0 n) (tauN r L n ρ ρ' oMid) (r + ((n - 1) * L + q)) = ρ'.v (r + q) := by
  have hqx : r + q < r + L := by omega
  rw [(hC' (r + q) (by rw [List.length_take]; omega)).2]
  have hv : ∀ t, t < r + L → (t < r → ρ'.v t = ρ.v t) →
      (tauN r L n ρ ρ' oMid).v (shk r ((n - 1) * L) t) = ρ'.v t := by
    intro t ht hlt
    rcases Nat.lt_or_ge t r with h | h
    · rw [shk_lt h, tau_v_lt h, hlt h]
    · exact tau_v_shk_last h ht
  apply vRhs_eq_of (by rw [entry_copy0 hlen (by omega) hq 1, entry_take M 1 hqx])
    (by rw [entry_copy0 hlen (by omega) hq 2, entry_take M 2 hqx])
  · intro _
    rw [par1_copy0 hlen hL hp hn (by omega) hq, par_take M 1 (r + q) hqx]
    cases hP : par M 1 (r + q) with
    | none => rfl
    | some m =>
      have := par_lt M 1 _ _ hP
      exact hv m (by omega) (fun h => hread m h (Or.inl hP))
  · intro _ _
    by_cases hq1 : q + 1 < L
    · rw [upg_copy0 hlen hL hp hn (by omega) hq1, upg_take M (show r + q + 1 < r + L by omega),
        Option.map_map]
      cases hU : upg M (r + q) with
      | none => rfl
      | some t =>
        simp only [Option.map_some, Function.comp, Option.some.injEq]
        have ht : t < M.length := upg_lt (by omega) hU
        have htx : t ≠ r + L := fun h => upg_ne_e2z hU (by rw [h]; exact he2)
        rw [hv t (by omega) (fun h => hread t h (Or.inr hU))]
    · have hqL : q = L - 1 := by omega
      subst hqL
      rw [upg_none_last0 hlen hL hp hn, show r + (L - 1) = r + L - 1 by omega,
        upg_take_last M (by omega) (by omega)]
      rfl
  · intro _ _
    rw [children_copy0 hlen hL hp hn (by omega) hq, children_take, List.map_map]
    congr 2
    apply List.map_congr_left
    intro c hc
    rw [List.mem_filter] at hc
    have hcgt := (mem_children hc.1).1
    have hcx : c < r + L := by simpa using hc.2
    obtain ⟨q', rfl⟩ : ∃ q', c = r + q' := ⟨c - r, by omega⟩
    simp only [Function.comp]
    rw [shk_B]
    apply bumpTerm_eq_of
    · rw [col_copy0 hlen (by omega) (by omega), bump_copy0 hlen hn (by omega) hq, col_take M hcx,
        bump_take M hqx]
    · intro _
      rw [children_copy0 hlen hL hp hn (by omega) (show q' < L by omega), children_take, List.map_map]
      apply List.map_congr_left
      intro d hd
      rw [List.mem_filter] at hd
      have hdgt := (mem_children hd.1).1
      have hdx : d < r + L := by simpa using hd.2
      obtain ⟨q'', rfl⟩ : ∃ q'', d = r + q'' := ⟨d - r, by omega⟩
      simp only [Function.comp]
      rw [shk_B, tau_o_last (by omega)]

end

end Ytosk
