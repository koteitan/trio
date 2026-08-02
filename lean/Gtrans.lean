/-
Gtrans.lean: ガード輸送（guard transport）。

t=2 展開 `gexp = take j0 ++ gcopies` の鏡像位置で `le1`-ガードが保存
される: `le1 (gexp …) j0 (j0 + (k*Lb + q)) ↔ le1 M j0 (j0 + q)`。
probe: 77460 実展開ケース 0 違反。srow=2 の剥離（peel2）の心臓部。

構造: 位置算術層 → A1/A3（親計算の転送）→ 鎖逆転（DC）→ B-pos/B-neg。
コピールートは局所床（copy root = local floor）として働き、境界降下は
lp の親鎖（np2 の le1 成分から行 1 が狭義に w1 を超える）を通る。
-/
import Invariant

namespace TRIO

open Classical

/-- The guarded expansion body: take-part plus the guarded copies. -/
noncomputable def gexp (M : TrioSeq) (j0 Lb d0 d1 n : ℕ) : TrioSeq :=
  M.take j0 ++ gcopies M j0 Lb d0 d1 n

section Gtrans

variable {M : TrioSeq} {j0 Lb d0 d1 n : ℕ}

theorem gexp_length (hlen : j0 + Lb + 1 = M.length) :
    (gexp M j0 Lb d0 d1 n).length = j0 + n * Lb := by
  unfold gexp
  rw [List.length_append, List.length_take, gcopies_length]
  omega

theorem gexp_getD_low {p : ℕ} (hlen : j0 + Lb + 1 = M.length) (hp : p < j0) :
    (gexp M j0 Lb d0 d1 n).getD p (0, 0, 0) = M.getD p (0, 0, 0) := by
  unfold gexp
  rw [getD_append_left (by rw [List.length_take]; omega), getD_take (by omega)]

theorem gexp_getD_mir {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hq : q < Lb) :
    (gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + q)) (0, 0, 0)
      = (entry M 0 (j0 + q) + k * d0,
         entry M 1 (j0 + q) + (if le1 M j0 (j0 + q) then k * d1 else 0),
         entry M 2 (j0 + q)) := by
  unfold gexp
  rw [getD_app_right _ _ (by rw [List.length_take]; omega),
    show j0 + (k * Lb + q) - (M.take j0).length = k * Lb + q from by
      rw [List.length_take]; omega,
    gcopies_getD hk hq]

/-- Positions in the copies region decompose as `j0 + (k*Lb + q)`. -/
theorem gexp_pos_decomp {p : ℕ} (hLb : 0 < Lb) (hp0 : j0 ≤ p)
    (hp1 : p < j0 + n * Lb) :
    ∃ k q, k < n ∧ q < Lb ∧ p = j0 + (k * Lb + q) := by
  refine ⟨(p - j0) / Lb, (p - j0) % Lb, ?_, Nat.mod_lt _ hLb, ?_⟩
  · exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  · have h := Nat.div_add_mod (p - j0) Lb
    rw [Nat.mul_comm Lb ((p - j0) / Lb)] at h
    omega

/-! ## 窓層 -/

theorem gexp_entry_root {y : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hn : 0 < n) (hLb : 0 < Lb) :
    entry (gexp M j0 Lb d0 d1 n) y j0 = entry M y j0 := by
  have h := gexp_getD_mir (M := M) (d0 := d0) (d1 := d1)
    (k := 0) (q := 0) hlen hn hLb
  simp only [Nat.zero_mul, ite_self, Nat.add_zero] at h
  unfold entry
  rw [h]
  dsimp only
  split_ifs with h1 h2
  · rfl
  · rfl
  · rfl

theorem gexp_entry0_gt (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) :
    ∀ p, j0 < p → p < j0 + n * Lb →
      entry M 0 j0 < entry (gexp M j0 Lb d0 d1 n) 0 p := by
  intro p hp0 hp1
  obtain ⟨k, q, hk, hq, rfl⟩ := gexp_pos_decomp hLb (by omega) hp1
  show entry M 0 j0 < ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + q)) (0, 0, 0)).1
  rw [gexp_getD_mir hlen hk hq]
  dsimp only
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · omega
      · exact h
    have : 0 < k * d0 := Nat.mul_pos hkpos hd0pos
    simp only [Nat.add_zero]
    omega
  · have := hup (j0 + q) (by omega) (by omega)
    omega

theorem gexp_rtg0_root (hlen : j0 + Lb + 1 = M.length) (hn : 0 < n)
    (hLb : 0 < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) :
    ∀ p, j0 ≤ p → p < j0 + n * Lb →
      Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) j0 p := by
  intro p hp0 hp1
  refine rtg0_of_window (by rw [gexp_length hlen]; omega) hp0 ?_
  intro l hl0 hl1
  rw [gexp_entry_root hlen hn hLb]
  exact gexp_entry0_gt hlen hLb hup hd0pos l hl0 (by omega)

/-! ## 親計算の転送（A1: コピー内 / A3: ルート降下） -/

/-- **A1**: an interior (or floor) parent step transports into copy `k`. -/
theorem gexp_nextrel0_mir {k qa qb : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hqb : qb < Lb)
    (h : nextrel0 M (j0 + qa) (j0 + qb)) :
    nextrel0 (gexp M j0 Lb d0 d1 n)
      (j0 + (k * Lb + qa)) (j0 + (k * Lb + qb)) := by
  have hab : qa < qb := by
    have := nextrel0_index_less h
    omega
  have hbnd : j0 + (k * Lb + qb) < j0 + n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  refine ⟨by rw [gexp_length hlen]; omega, by rw [gexp_length hlen]; omega,
    by omega, ?_, ?_⟩
  · show ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + qa)) (0, 0, 0)).1
      < ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + qb)) (0, 0, 0)).1
    rw [gexp_getD_mir hlen hk (by omega), gexp_getD_mir hlen hk hqb]
    have := h.2.2.2.1
    have e1 : entry M 0 (j0 + qa) = (M.getD (j0 + qa) (0, 0, 0)).1 := rfl
    have e2 : entry M 0 (j0 + qb) = (M.getD (j0 + qb) (0, 0, 0)).1 := rfl
    dsimp only
    show (M.getD (j0 + qa) (0, 0, 0)).1 + k * d0
      < (M.getD (j0 + qb) (0, 0, 0)).1 + k * d0
    omega
  · intro l ⟨hl0, hl1⟩
    have hql : ∃ ql, qa < ql ∧ ql < qb ∧ l = j0 + (k * Lb + ql) :=
      ⟨l - j0 - k * Lb, by omega, by omega, by omega⟩
    obtain ⟨ql, hql0, hql1, rfl⟩ := hql
    show ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + qb)) (0, 0, 0)).1
      ≤ ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + ql)) (0, 0, 0)).1
    rw [gexp_getD_mir hlen hk hqb, gexp_getD_mir hlen hk (by omega)]
    have := h.2.2.2.2 (j0 + ql) ⟨by omega, by omega⟩
    dsimp only
    show (M.getD (j0 + qb) (0, 0, 0)).1 + k * d0
      ≤ (M.getD (j0 + ql) (0, 0, 0)).1 + k * d0
    have e1 : entry M 0 (j0 + qb) = (M.getD (j0 + qb) (0, 0, 0)).1 := rfl
    have e2 : entry M 0 (j0 + ql) = (M.getD (j0 + ql) (0, 0, 0)).1 := rfl
    omega

/-- **A3**: the root of copy `k` descends to the `lp`-parent's image in
copy `k-1`. -/
theorem gexp_nextrel0_root {k qp : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hk1 : 1 ≤ k) (hqp : qp < Lb)
    (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (h : nextrel0 M (j0 + qp) (j0 + Lb)) :
    nextrel0 (gexp M j0 Lb d0 d1 n)
      (j0 + ((k - 1) * Lb + qp)) (j0 + (k * Lb + 0)) := by
  have hLb : 0 < Lb := by omega
  have hsm : k * Lb = (k - 1) * Lb + Lb := by
    have h2 : (k - 1 + 1) * Lb = (k - 1) * Lb + Lb := Nat.succ_mul (k - 1) Lb
    have h3 : k - 1 + 1 = k := by omega
    rw [h3] at h2
    exact h2
  have hsd : k * d0 = (k - 1) * d0 + d0 := by
    have h2 : (k - 1 + 1) * d0 = (k - 1) * d0 + d0 := Nat.succ_mul (k - 1) d0
    have h3 : k - 1 + 1 = k := by omega
    rw [h3] at h2
    exact h2
  have hbnd : j0 + (k * Lb + 0) < j0 + n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  refine ⟨by rw [gexp_length hlen]; omega, by rw [gexp_length hlen]; omega,
    by omega, ?_, ?_⟩
  · show ((gexp M j0 Lb d0 d1 n).getD (j0 + ((k - 1) * Lb + qp)) (0, 0, 0)).1
      < ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + 0)) (0, 0, 0)).1
    rw [gexp_getD_mir hlen (by omega) hqp, gexp_getD_mir hlen hk hLb]
    have h4 := h.2.2.2.1
    have e1 : entry M 0 (j0 + qp) = (M.getD (j0 + qp) (0, 0, 0)).1 := rfl
    have e2 : entry M 0 (j0 + Lb) = (M.getD (j0 + Lb) (0, 0, 0)).1 := rfl
    have e3 : entry M 0 j0 = (M.getD j0 (0, 0, 0)).1 := rfl
    dsimp only
    show (M.getD (j0 + qp) (0, 0, 0)).1 + (k - 1) * d0
      < (M.getD (j0 + 0) (0, 0, 0)).1 + k * d0
    rw [Nat.add_zero]
    omega
  · intro l ⟨hl0, hl1⟩
    have hql : ∃ ql, qp < ql ∧ ql < Lb ∧ l = j0 + ((k - 1) * Lb + ql) :=
      ⟨l - j0 - (k - 1) * Lb, by omega, by omega, by omega⟩
    obtain ⟨ql, hql0, hql1, rfl⟩ := hql
    show ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + 0)) (0, 0, 0)).1
      ≤ ((gexp M j0 Lb d0 d1 n).getD (j0 + ((k - 1) * Lb + ql)) (0, 0, 0)).1
    rw [gexp_getD_mir hlen hk hLb, gexp_getD_mir hlen (by omega) (by omega)]
    have h5 := h.2.2.2.2 (j0 + ql) ⟨by omega, by omega⟩
    have e1 : entry M 0 (j0 + Lb) = (M.getD (j0 + Lb) (0, 0, 0)).1 := rfl
    have e2 : entry M 0 (j0 + ql) = (M.getD (j0 + ql) (0, 0, 0)).1 := rfl
    have e3 : entry M 0 j0 = (M.getD j0 (0, 0, 0)).1 := rfl
    dsimp only
    show (M.getD (j0 + 0) (0, 0, 0)).1 + k * d0
      ≤ (M.getD (j0 + ql) (0, 0, 0)).1 + (k - 1) * d0
    rw [Nat.add_zero]
    omega

/-- Chains transport into copy `k` (A1 iterated). -/
theorem gexp_rtg0_mir {k : ℕ} (hlen : j0 + Lb + 1 = M.length) (hk : k < n) :
    ∀ {c : ℕ} {qa : ℕ}, Relation.ReflTransGen (nextrel0 M) (j0 + qa) c →
      ∀ qc, c = j0 + qc → qc < Lb →
      Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n))
        (j0 + (k * Lb + qa)) (j0 + (k * Lb + qc)) := by
  intro c qa h
  induction h with
  | refl =>
    intro qc hc _
    have : qa = qc := by omega
    rw [this]
  | @tail y z hay hyz ih =>
    intro qc hc hqc
    have hy0 : j0 + qa ≤ y := nextrel0_rtrancl_index_le hay
    have hyz' : y < z := nextrel0_index_less hyz
    have hqy : y = j0 + (y - j0) := by omega
    rw [hc] at hyz
    refine (ih (y - j0) hqy (by omega)).tail ?_
    exact gexp_nextrel0_mir hlen hk hqc (by rw [← hqy]; exact hyz)

/-! ## 鎖逆転（DC inversion） -/

/-- **Chain inversion**: any chain ancestor (≥ `j0`) of a mirror position is
itself a mirror position, either in the same copy over an `M`-chain to the
target offset, or in an earlier copy over an `M`-chain to `lp`. -/
theorem gexp_chain_inversion {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0) :
    ∀ x, Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) x
        (j0 + (k * Lb + q)) →
      j0 ≤ x →
      ∃ k' q', k' ≤ k ∧ q' < Lb ∧ x = j0 + (k' * Lb + q') ∧
        ((k' = k ∧ Relation.ReflTransGen (nextrel0 M) (j0 + q') (j0 + q)) ∨
         (k' < k ∧ Relation.ReflTransGen (nextrel0 M) (j0 + q') (j0 + Lb))) := by
  intro x hx
  induction hx using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _
    exact ⟨k, q, le_rfl, hq, rfl, Or.inl ⟨rfl, .refl⟩⟩
  | @head x' y' hxy hyt ih =>
    intro hx0
    have hxy' : x' < y' := nextrel0_index_less hxy
    obtain ⟨k', q', hk', hq', rfl, hcase⟩ := ih (by omega)
    rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
    · -- the target is a copy root
      rcases Nat.eq_zero_or_pos k' with rfl | hk'pos
      · -- copy 0 root = `j0` itself: no ancestor at or above `j0`
        exact absurd hxy' (by omega)
      · -- A3: the parent is the `lp`-parent's image in copy `k'-1`
        have hrtg : Relation.ReflTransGen (nextrel0 M) j0 (j0 + Lb) := by
          refine rtg0_of_window (by omega) (by omega) ?_
          intro l hl0 hl1
          exact hup l hl0 hl1
        rcases hrtg.cases_tail with heq | ⟨pa, hpa1, hpa2⟩
        · exact absurd heq (by omega)
        · have hpa0 : j0 ≤ pa := nextrel0_rtrancl_index_le hpa1
          have hpaL : pa < j0 + Lb := nextrel0_index_less hpa2
          set qp := pa - j0 with hqp
          have hpae : pa = j0 + qp := by omega
          rw [hpae] at hpa2
          have hstep := gexp_nextrel0_root (n := n) (d1 := d1) (k := k') hlen
            (by omega) (by omega) (by omega) hd0e hpa2
          have hxe : x' = j0 + ((k' - 1) * Lb + qp) :=
            nextrel0_src_unique hxy hstep
          refine ⟨k' - 1, qp, by omega, by omega, hxe, Or.inr ⟨?_, ?_⟩⟩
          · omega
          · exact Relation.ReflTransGen.single hpa2
    · -- interior target: A1 with the `M`-side parent
      have hrtg : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q') := by
        refine rtg0_of_window (by omega) (by omega) ?_
        intro l hl0 hl1
        exact hup l hl0 (by omega)
      rcases hrtg.cases_tail with heq | ⟨pa, hpa1, hpa2⟩
      · exact absurd heq (by omega)
      · have hpa0 : j0 ≤ pa := nextrel0_rtrancl_index_le hpa1
        have hpaq : pa < j0 + q' := nextrel0_index_less hpa2
        set qa := pa - j0 with hqa
        have hpae : pa = j0 + qa := by omega
        rw [hpae] at hpa2
        have hstep := gexp_nextrel0_mir (n := n) (d0 := d0) (d1 := d1)
          (k := k') hlen (by omega) hq' hpa2
        have hxe : x' = j0 + (k' * Lb + qa) :=
          nextrel0_src_unique hxy hstep
        refine ⟨k', qa, hk', by omega, hxe, ?_⟩
        rcases hcase with ⟨rfl, hM⟩ | ⟨hlt, hM⟩
        · exact Or.inl ⟨rfl, hM.head hpa2⟩
        · exact Or.inr ⟨hlt, hM.head hpa2⟩

/-! ## ガード輸送 -/

/-- **B-pos**: a guarded (`le1`) column stays guarded at every mirror. -/
theorem gexp_le1_mir {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hd1pos : 0 < d1) (hle1lp : le1 M j0 (j0 + Lb))
    (hg : le1 M j0 (j0 + q)) :
    le1 (gexp M j0 Lb d0 d1 n) j0 (j0 + (k * Lb + q)) := by
  have hLb : 0 < Lb := by omega
  have hn : 0 < n := by omega
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hch : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) j0
      (j0 + (k * Lb + q)) :=
    gexp_rtg0_root hlen hn hLb hup hd0pos _ (by omega) (by omega)
  refine (le1_iff_chain_window (by rw [gexp_length hlen]; omega) hch).2 ?_
  intro x hrx hxt hne
  have hx0 : j0 ≤ x := nextrel0_rtrancl_index_le hrx
  obtain ⟨k', q', hk', hq', rfl, hcase⟩ :=
    gexp_chain_inversion hlen hk hq hup hd0e x hxt hx0
  rw [gexp_entry_root hlen hn hLb]
  show entry M 1 j0
    < ((gexp M j0 Lb d0 d1 n).getD (j0 + (k' * Lb + q')) (0, 0, 0)).2.1
  rw [gexp_getD_mir hlen (by omega) hq']
  dsimp only
  rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
  · -- copy root: lifted by `k' * d1 > 0`
    have hk'pos : 0 < k' := by
      rcases Nat.eq_zero_or_pos k' with rfl | h
      · exact absurd (by simp) hne
      · exact h
    simp only [Nat.add_zero]
    rw [if_pos (le1_refl (by omega))]
    have : 0 < k' * d1 := Nat.mul_pos hk'pos hd1pos
    omega
  · -- interior: the `M`-side chain node is strictly above `w1`
    have hMrtg : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q') := by
      refine rtg0_of_window (by omega) (by omega) ?_
      intro l hl0 hl1
      exact hup l hl0 (by omega)
    have hMwin : entry M 1 j0 < entry M 1 (j0 + q') := by
      rcases hcase with ⟨_, hM⟩ | ⟨_, hM⟩
      · exact le1_chain_window hg.2.2 (j0 + q') hMrtg hM (by omega)
      · exact le1_chain_window hle1lp.2.2 (j0 + q') hMrtg hM (by omega)
    have e1 : entry M 1 (j0 + q') = (M.getD (j0 + q') (0, 0, 0)).2.1 := rfl
    split_ifs with hcond
    · omega
    · omega

/-- **B-neg**: an unguarded column stays unguarded at every mirror (the
`M`-side blocker mirrors with an unlifted row 1). -/
theorem gexp_not_le1_mir {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0)
    (hg : ¬ le1 M j0 (j0 + q)) :
    ¬ le1 (gexp M j0 Lb d0 d1 n) j0 (j0 + (k * Lb + q)) := by
  have hLb : 0 < Lb := by omega
  have hn : 0 < n := by omega
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · exact absurd (by
        show le1 M j0 (j0 + 0)
        rw [Nat.add_zero]
        exact le1_refl (by omega)) hg
    · exact h
  have hMrtg : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q) := by
    refine rtg0_of_window (by omega) (by omega) ?_
    intro l hl0 hl1
    exact hup l hl0 (by omega)
  obtain ⟨b, hj0b, hbq, hbne, hb1⟩ :=
    blocker_of_not_le1 hMrtg (by omega) hg
  have hb0 : j0 ≤ b := nextrel0_rtrancl_index_le hj0b
  have hbq' : b ≤ j0 + q := nextrel0_rtrancl_index_le hbq
  set qb := b - j0 with hqb
  have hbe : b = j0 + qb := by omega
  have hqbpos : 0 < qb := by omega
  have hgb : ¬ le1 M j0 b := by
    intro hcon
    exact absurd (le1_chain_window hcon.2.2 b hj0b .refl hbne) (by omega)
  intro hcon
  have hXb : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n))
      (j0 + (k * Lb + qb)) (j0 + (k * Lb + q)) := by
    refine gexp_rtg0_mir hlen hk ?_ q rfl hq
    rw [← hbe]
    exact hbq
  have hXroot : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) j0
      (j0 + (k * Lb + qb)) := by
    refine gexp_rtg0_root hlen hn hLb hup hd0pos _ (by omega) ?_
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hwin := le1_chain_window hcon.2.2 (j0 + (k * Lb + qb)) hXroot hXb
    (by omega)
  rw [gexp_entry_root hlen hn hLb] at hwin
  have hval : entry (gexp M j0 Lb d0 d1 n) 1 (j0 + (k * Lb + qb))
      = entry M 1 (j0 + qb) := by
    show ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + qb)) (0, 0, 0)).2.1 = _
    rw [gexp_getD_mir hlen hk (by omega)]
    dsimp only
    rw [if_neg (by rw [← hbe]; exact hgb), Nat.add_zero]
  rw [hval] at hwin
  have e1 : entry M 1 (j0 + qb) = (M.getD (j0 + qb) (0, 0, 0)).2.1 := rfl
  have e2 : entry M 1 b = (M.getD b (0, 0, 0)).2.1 := rfl
  rw [hbe] at hb1
  have e3 : entry M 1 j0 = (M.getD j0 (0, 0, 0)).2.1 := rfl
  omega

/-- **Guard transport** (probe: 77460 cases, 0 violations): the `le1` guard
at any mirror position equals the host guard. -/
theorem gexp_guard_transport {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hd1pos : 0 < d1) (hle1lp : le1 M j0 (j0 + Lb)) :
    le1 (gexp M j0 Lb d0 d1 n) j0 (j0 + (k * Lb + q)) ↔ le1 M j0 (j0 + q) := by
  constructor
  · intro h
    by_contra hg
    exact gexp_not_le1_mir hlen hk hq hup hd0pos hg h
  · intro hg
    exact gexp_le1_mir hlen hk hq hup hd0pos hd0e hd1pos hle1lp hg

end Gtrans

end TRIO
