/-
Croot.lean: 展開の**ブロック根**における行 1 錐の輸送（`Lcone.gexp_cone_mir` の
`j0 = 0` 版）と、そこから従うガード付きコピー塊の**根リフト漸化式**。

`Lcone.gexp_cone_mir` は宿主の根 `0`（`j0 > 0` の下の前置ブロックの根）の錐を
運ぶ。ここで要るのはそれとは別の

    le1 (gexp M 0 Lb d0 d1 n) 0 (k * Lb + q)  ↔  le1 M 0 q

すなわち**コピー塊自身の根**の錐。前置ブロックが無いので鎖分解の「接頭辞側」が
消えて素直になるが、代わりに 2 つの仮定が要る（tools/probe_coneroot.py）:

* `hd1pos : 0 < d1` — コピーの根 `k*Lb`（`q = 0`）が錐に入るのは行 1 が
  `k*d1` だけ上昇するからで、`d1 = 0` では偽（1700/3362 反例）。
* `hlp : le1 M 0 Lb` — ブロックされた列が根の行 1 錐に入ること。前のコピーへ
  降りる鎖（`gexp_chain_inversion` の第 2 分岐）を押さえるのに要る。
  `hlp` を落とすと反例が出る（970/17823）。行 2 ブロッカーでは
  `p = parent R 2 x` から `le2 R p x` ⟹ `le1 R p x` で自動的に成立する。

計測（probe_coneroot.py, 120000 サンプル）:

    T2/hlp/d1>0    9726     0        ← 本定理の仮定
    T2/hlp/d1=0    3362  1700
    T2/nolp/d1>0  17823   970
-/
import Aexp

namespace TRIO

open Wset

/-! ## ブロック根の錐輸送 -/

section Root

variable {M : TrioSeq} {Lb d0 d1 n : ℕ}

/-- The expansion's own root is strictly the shallowest column: inside copy `0`
by `hup`, and every later copy root is `k * d0` deeper. -/
theorem gexp_root_shallow_root (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb)
    (hn : 0 < n) (hup : ∀ l, 0 < l → l ≤ 0 + Lb → entry M 0 0 < entry M 0 l)
    (hd0pos : 0 < d0) :
    ∀ l, 0 < l → l < (gexp M 0 Lb d0 d1 n).length →
      entry (gexp M 0 Lb d0 d1 n) 0 0 < entry (gexp M 0 Lb d0 d1 n) 0 l := by
  intro l hl0 hl1
  have hXlen : (gexp M 0 Lb d0 d1 n).length = 0 + n * Lb := gexp_length hlen
  rw [hXlen] at hl1
  have hzero : entry (gexp M 0 Lb d0 d1 n) 0 0 = entry M 0 0 := by
    have h := gexp_entry0_mir (M := M) (j0 := 0) (Lb := Lb) (d0 := d0)
      (d1 := d1) (n := n) (k := 0) (q := 0) hlen hn hLb
    simpa using h
  -- Euclidean decomposition of `l`
  have hq' : l % Lb < Lb := Nat.mod_lt _ hLb
  have hk' : l / Lb < n := by
    rw [Nat.div_lt_iff_lt_mul hLb]
    omega
  have hle : (l / Lb) * Lb + l % Lb = l := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod l Lb
  have hmir := gexp_entry0_mir (M := M) (j0 := 0) (Lb := Lb) (d0 := d0)
    (d1 := d1) (n := n) (k := l / Lb) (q := l % Lb) hlen hk' hq'
  rw [hle] at hmir
  have hval : entry (gexp M 0 Lb d0 d1 n) 0 l
      = entry M 0 (l % Lb) + (l / Lb) * d0 := by
    have h0 : (0 : ℕ) + l = l := by omega
    rw [← h0, hmir]
    simp
  rw [hzero, hval]
  rcases Nat.eq_zero_or_pos (l % Lb) with hq0 | hqpos
  · -- a copy root: `l / Lb` copies deep
    have hkpos : 0 < l / Lb := by
      rcases Nat.eq_zero_or_pos (l / Lb) with hk0 | hkpos
      · exfalso
        rw [hk0, Nat.zero_mul, Nat.zero_add, hq0] at hle
        omega
      · exact hkpos
    have : 0 < (l / Lb) * d0 := Nat.mul_pos hkpos hd0pos
    rw [hq0]
    omega
  · have := hup (l % Lb) hqpos (by omega)
    omega

/-- **Root-cone transport at the block root** (`Lcone.gexp_cone_mir` with
`j0 = 0`): a mirror position is in the copies block's own root cone exactly
when its source offset is in the host's root cone. -/
theorem gexp_cone_mir_root {k q : ℕ} (hlen : 0 + Lb + 1 = M.length)
    (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, 0 < l → l ≤ 0 + Lb → entry M 0 0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (0 + Lb) = entry M 0 0 + d0)
    (hd1pos : 0 < d1) (hlp : le1 M 0 (0 + Lb)) :
    le1 (gexp M 0 Lb d0 d1 n) 0 (0 + (k * Lb + q)) ↔ le1 M 0 (0 + q) := by
  classical
  have hn : 0 < n := by omega
  have hXlen : (gexp M 0 Lb d0 d1 n).length = 0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hplt : 0 + (k * Lb + q) < (gexp M 0 Lb d0 d1 n).length := by
    rw [hXlen]; omega
  have hqlt : 0 + q < M.length := by omega
  have hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l :=
    fun l hl0 hl1 => hup l hl0 (by omega)
  have hrX := gexp_root_shallow_root (d1 := d1) (n := n) hlen hLb hn hup hd0pos
  have h10 : entry (gexp M 0 Lb d0 d1 n) 1 0 = entry M 1 0 := by
    have h := gexp_entry1_mir (M := M) (j0 := 0) (Lb := Lb) (d0 := d0)
      (d1 := d1) (n := n) (k := 0) (q := 0) hlen hn hLb
    simpa using h
  rw [le1_zero_iff hrX hplt, le1_zero_iff hr0 hqlt, h10]
  constructor
  · -- the expansion's window forces the host's window
    intro hXw y hyq hy0
    have hyle : y ≤ 0 + q := nextrel0_rtrancl_index_le hyq
    have hylt : y < Lb := by omega
    have hyq' : Relation.ReflTransGen (nextrel0 M) (0 + y) (0 + q) := by
      simpa using hyq
    have hmir : Relation.ReflTransGen (nextrel0 (gexp M 0 Lb d0 d1 n))
        (0 + (k * Lb + y)) (0 + (k * Lb + q)) :=
      gexp_rtg0_mir (d0 := d0) (d1 := d1) (n := n) hlen hk hyq' q rfl hq
    have h := hXw (0 + (k * Lb + y)) hmir (by omega)
    rw [gexp_entry1_mir hlen hk hylt] at h
    by_cases hg : le1 M 0 (0 + y)
    · have := le1_entry1_lt hg (by omega)
      simpa using this
    · rw [if_neg hg] at h
      simp only [Nat.zero_add] at h ⊢
      omega
  · -- the host's window forces the expansion's window
    intro hMw y hyp hy0
    obtain ⟨k', q', hk', hq', hye, hcase⟩ :=
      gexp_chain_inversion hlen hk hq hup hd0e y hyp (by omega)
    subst hye
    rw [gexp_entry1_mir hlen (by omega) hq']
    rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
    · -- a copy root: it ascends by `k' * d1`
      have hk'pos : 0 < k' := by
        by_contra hc
        have : k' = 0 := by omega
        subst this
        simp at hy0
      have hrefl : le1 M 0 (0 + 0) := ⟨by omega, by omega, .refl⟩
      rw [if_pos hrefl]
      have : 0 < k' * d1 := Nat.mul_pos hk'pos hd1pos
      simp only [Nat.zero_add]
      omega
    · have hbase : entry M 1 0 < entry M 1 (0 + q') := by
        rcases hcase with ⟨-, hM⟩ | ⟨-, hM⟩
        · exact hMw (0 + q') hM (by omega)
        · have hchain : Relation.ReflTransGen (nextrel0 M) 0 (0 + q') :=
            rtg0_of_window (by omega) (by omega)
              (fun l hl0 hl1 => hup l hl0 (by omega))
          exact le1_chain_window hlp.2.2 (0 + q') hchain hM (by omega)
      split_ifs <;> omega

end Root

/-! ## セグメントへの再基底化

`gexp_cone_mir_root` を使うには、ブロックを**単独の列**として切り出す必要が
ある。切り出し `seg R p (L+1)` は接頭辞との連結なので、既存の
`le1_take` / `le1_append_right`（どちらも無条件）で錐がそのまま移る。 -/

section Rebase

/-- **Segment restriction preserves the block root's cone.**  `R.take (p+L+1)`
splits as `R.take p ++ seg R p (L+1)`, and both `le1_take` and
`le1_append_right` are unconditional. -/
theorem le1_seg_root {R : TrioSeq} {p L q : ℕ} (hlen : p + (L + 1) ≤ R.length)
    (hq : q < L + 1) :
    le1 (seg R p (L + 1)) 0 q ↔ le1 R p (p + q) := by
  have hsplit : R.take (p + (L + 1)) = R.take p ++ seg R p (L + 1) := by
    rw [← seg_zero_eq_take R (by omega), ← seg_zero_eq_take R (by omega),
      seg_append]
    simp
  have hplen : (R.take p).length = p := by rw [List.length_take]; omega
  have happ := le1_append_right (R.take p) (seg R p (L + 1)) 0 q
  rw [hplen] at happ
  have htk : le1 (R.take (p + (L + 1))) p (p + q) ↔ le1 R p (p + q) :=
    le1_take (by omega) (by omega)
  rw [← htk, hsplit]
  exact (by simpa using happ : le1 (R.take p ++ seg R p (L + 1)) (p + 0) (p + q)
    ↔ le1 (seg R p (L + 1)) 0 q).symm

/-- Re-basing row 0 does not move the row-1 ancestry (`le1_shiftr01` backwards,
via `shiftr01_shiftl0`). -/
theorem le1_shiftl0 {c : ℕ} {Z : TrioSeq} (h : ∀ x ∈ Z, c ≤ x.1) {a b : ℕ} :
    le1 (shiftl0 c Z) a b ↔ le1 Z a b := by
  have hz : shiftr01 c 0 (shiftl0 c Z) = Z := shiftr01_shiftl0 h
  have := le1_shiftr01 (d0 := c) (W := shiftl0 c Z) (a := a) (b := b)
  rw [hz] at this
  exact this.symm

/-- `map` over a shifted range' is the shifted map over the base range'. -/
theorem range_map_shift (f : ℕ → ℕ × ℕ × ℕ) (a : ℕ) :
    ∀ L b, (List.range' (a + b) L).map f
      = (List.range' b L).map (fun j => f (a + j)) := by
  intro L
  induction L with
  | zero => intro b; simp
  | succ L ih =>
      intro b
      rw [List.range'_succ, List.range'_succ, List.map_cons, List.map_cons]
      have hab : a + b + 1 = a + (b + 1) := by omega
      rw [hab, ih (b + 1)]

theorem range_map_shift0 (f : ℕ → ℕ × ℕ × ℕ) (a L : ℕ) :
    (List.range' a L).map f = (List.range' 0 L).map (fun j => f (a + j)) :=
  range_map_shift f a L 0

/-- **The copies block re-bases to the segment**: with the block root's cone
transported (`le1_seg_root`), the guarded copies of `R` at `p` are literally
the guarded copies of the cut-out segment at `0`. -/
theorem entry_seg {N : TrioSeq} {a l i j : ℕ} (hj : j < l) :
    entry (seg N a l) i j = entry N i (a + j) := by
  unfold entry
  rw [seg_getD hj]
  split_ifs <;> rfl

/-- **The copies block re-bases to the segment**: with the block root's cone
transported (`le1_seg_root`), the guarded copies of `R` at `p` are literally
the guarded copies of the cut-out segment at `0`. -/
theorem gcopies_seg (R : TrioSeq) {p L d0 d1 : ℕ} (n : ℕ)
    (hlen : p + (L + 1) ≤ R.length) :
    gcopies R p L d0 d1 n = gcopies (seg R p (L + 1)) 0 L d0 d1 n := by
  classical
  unfold gcopies gcopy
  refine List.flatMap_congr ?_
  intro k _
  rw [range_map_shift0]
  refine List.map_congr_left ?_
  intro j hj
  have hjl : j < L := by
    rw [List.mem_range'_1] at hj
    omega
  have hjl1 : j < L + 1 := by omega
  rw [entry_seg hjl1, entry_seg hjl1, entry_seg hjl1]
  have hguard : le1 (seg R p (L + 1)) 0 j ↔ le1 R p (p + j) :=
    le1_seg_root hlen hjl1
  by_cases hg : le1 R p (p + j)
  · rw [if_pos hg, if_pos (hguard.mpr hg)]
  · rw [if_neg hg, if_neg (fun hc => hg (hguard.mp hc))]

theorem gexp_zero_eq_gcopies (B : TrioSeq) (L d0 d1 n : ℕ) :
    gexp B 0 L d0 d1 n = gcopies B 0 L d0 d1 n := by
  unfold gexp
  simp

/-- **The block root's cone, copies form** — `gexp_cone_mir_root` transported
across `gexp B 0 … = gcopies B 0 …`. -/
theorem le1_gcopies_root {B : TrioSeq} {L d0 d1 n k q : ℕ}
    (hlen : L + 1 = B.length) (hLb : 0 < L) (hk : k < n) (hq : q < L)
    (hup : ∀ l, 0 < l → l ≤ L → entry B 0 0 < entry B 0 l)
    (hd0pos : 0 < d0) (hd0e : entry B 0 L = entry B 0 0 + d0)
    (hd1pos : 0 < d1) (hlp : le1 B 0 L) :
    le1 (gcopies B 0 L d0 d1 n) 0 (k * L + q) ↔ le1 B 0 q := by
  have h := gexp_cone_mir_root (M := B) (Lb := L) (d0 := d0) (d1 := d1)
    (n := n) (k := k) (q := q) (by omega) hLb hk hq
    (fun l hl0 hl1 => hup l hl0 (by omega)) hd0pos (by simpa using hd0e)
    hd1pos (by simpa using hlp)
  rw [gexp_zero_eq_gcopies] at h
  simpa using h

/-! ## ガード付きコピー塊の根リフト漸化式

`d1 = 0` の `shiftl0_gcopies_succ`（Gamma）はコピー塊を「窓への反復接ぎ木」に
落とす。`d1 > 0` ではコピーごとに行 1 が `d1` 上昇するが、`le1_gcopies_root`
により**その上昇はブロック全体の根リフト `Lift1 · d1` と一致する**ので、
漸化式は「窓への接ぎ木 + 根リフト」になる。 -/

/-- **The guarded copies block is iterated grafting with a root lift**: the
`d1 > 0` analogue of `shiftl0_gcopies_succ`. -/
theorem gcopies_succ_graft_lift {B : TrioSeq} {L d0 d1 n : ℕ}
    (hlen : L + 1 = B.length) (hLb : 0 < L)
    (hup : ∀ l, 0 < l → l ≤ L → entry B 0 0 < entry B 0 l)
    (hd0pos : 0 < d0) (hbase : entry B 0 0 = 0) (hd0e : entry B 0 L = d0)
    (hd1pos : 0 < d1) (hlp : le1 B 0 L) :
    gcopies B 0 L d0 d1 (n + 1)
      = graft B (Lift1 (gcopies B 0 L d0 d1 n) d1) := by
  classical
  set X : TrioSeq := gcopies B 0 L d0 d1 n with hX
  have hXlen : X.length = n * L := by rw [hX, gcopies_length]
  have hDlen : B.dropLast.length = L := by rw [List.length_dropLast]; omega
  have hgraft : graft B (Lift1 X d1)
      = B.dropLast ++ shiftr01 d0 0 (Lift1 X d1) := by
    rw [graft_eq_shift, show B.length - 1 = L from by omega, hd0e]
  have hsucc : (n + 1) * L = n * L + L := Nat.succ_mul n L
  have hZlen : (shiftr01 d0 0 (Lift1 X d1)).length = n * L := by
    rw [shiftr01_length, Lift1_length, hXlen]
  rw [hgraft]
  refine list_ext_getD ?_ ?_
  · rw [gcopies_length, List.length_append, hDlen, hZlen]
    omega
  · intro i hi
    rw [gcopies_length] at hi
    obtain ⟨k, q, hk, hq, rfl⟩ := index_decomp hLb (by omega : i < (n + 1) * L)
    rw [gcopies_getD hk hq]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hiL : 0 * L + q < B.dropLast.length := by rw [hDlen]; omega
      rw [getD_append_left hiL, getD_eq_entries]
      have he : ∀ t, entry B.dropLast t (0 * L + q) = entry B t (0 + q) := by
        intro t
        rw [List.dropLast_eq_take,
          Wset.entry_take (X := B) (l := B.length - 1) (i := t)
            (j := 0 * L + q) (by omega)]
        congr 1
        omega
      rw [he 0, he 1, he 2]
      simp
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hkk : (k' + 1) * L = k' * L + L := Nat.succ_mul k' L
      have hge : B.dropLast.length ≤ (k' + 1) * L + q := by rw [hDlen]; omega
      have hsub : (k' + 1) * L + q - B.dropLast.length = k' * L + q := by
        rw [hDlen]; omega
      have hidx : k' * L + q < X.length := by
        have h2 : (k' + 1) * L ≤ n * L := Nat.mul_le_mul_right _ (by omega)
        rw [hXlen]; omega
      have htrip : ((entry X 0 (k' * L + q), entry X 1 (k' * L + q),
            entry X 2 (k' * L + q)) : ℕ × ℕ × ℕ)
          = (entry B 0 (0 + q) + k' * d0,
             entry B 1 (0 + q) + (if le1 B 0 (0 + q) then k' * d1 else 0),
             entry B 2 (0 + q)) := by
        rw [← getD_eq_entries, hX]
        exact gcopies_getD (by omega) hq
      have e0 : entry X 0 (k' * L + q) = entry B 0 (0 + q) + k' * d0 := by
        have h := congrArg Prod.fst htrip
        simpa using h
      have e1 : entry X 1 (k' * L + q)
          = entry B 1 (0 + q) + (if le1 B 0 (0 + q) then k' * d1 else 0) := by
        have h := congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) htrip
        simpa using h
      have e2 : entry X 2 (k' * L + q) = entry B 2 (0 + q) := by
        have h := congrArg (fun x : ℕ × ℕ × ℕ => x.2.2) htrip
        simpa using h
      have hcone : le1 X 0 (k' * L + q) ↔ le1 B 0 (0 + q) := by
        have h := le1_gcopies_root (B := B) (L := L) (d0 := d0) (d1 := d1)
          (n := n) (k := k') (q := q) hlen hLb (by omega) hq hup hd0pos
          (by rw [hd0e, hbase]; omega) hd1pos hlp
        rw [← hX] at h
        simpa using h
      have hkd0 : (k' + 1) * d0 = k' * d0 + d0 := Nat.succ_mul k' d0
      have hkd1 : (k' + 1) * d1 = k' * d1 + d1 := Nat.succ_mul k' d1
      rw [getD_app_right _ _ hge, hsub,
        shiftr01_getD (by rw [Lift1_length]; exact hidx), Lift1_getD hidx]
      dsimp only
      rw [e0, e1, e2]
      by_cases hg : le1 B 0 (0 + q)
      · rw [if_pos hg, if_pos (hcone.mpr hg), if_pos hg]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega
      · rw [if_neg hg, if_neg (fun hc => hg (hcone.mp hc)), if_neg hg]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega

/-! ## 再基底化した窓ブロック `B = shiftl0 c (seg R p (L+1))`

行 0 の一様な引き下げは行 1 の祖先関係を動かさない（`le1_shiftl0`）ので、
コピー塊はそのまま再基底化したブロックのコピー塊になる。 -/

theorem getD_shiftl0 {c : ℕ} {S : TrioSeq} {j : ℕ} :
    (shiftl0 c S).getD j ((0, 0, 0) : ℕ × ℕ × ℕ)
      = (((S.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).1 - c,
          (S.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).2.1,
          (S.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).2.2) : ℕ × ℕ × ℕ) := by
  rcases Nat.lt_or_ge j S.length with hj | hj
  · unfold shiftl0
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj]
    simp
  · rw [getD_out (by rw [shiftl0_length]; omega), getD_out hj]
    simp

theorem entry0_shiftl0' {c : ℕ} {S : TrioSeq} {j : ℕ} :
    entry (shiftl0 c S) 0 j = entry S 0 j - c := by
  unfold entry
  rw [getD_shiftl0]
  simp

theorem entry1_shiftl0 {c : ℕ} {S : TrioSeq} {j : ℕ} :
    entry (shiftl0 c S) 1 j = entry S 1 j := by
  unfold entry
  rw [getD_shiftl0]
  simp

theorem entry2_shiftl0 {c : ℕ} {S : TrioSeq} {j : ℕ} :
    entry (shiftl0 c S) 2 j = entry S 2 j := by
  unfold entry
  rw [getD_shiftl0]
  simp

theorem le_of_mem_seg {R : TrioSeq} {p l c : ℕ}
    (h : ∀ j, p ≤ j → j < p + l → c ≤ entry R 0 j) :
    ∀ x ∈ seg R p l, c ≤ x.1 := by
  intro x hx
  unfold seg at hx
  rw [List.mem_map] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  rw [List.mem_range'_1] at hj
  exact h j hj.1 hj.2

theorem shiftl0_flatMap {c : ℕ} {α : Type} (l : List α) (f : α → TrioSeq) :
    shiftl0 c (l.flatMap f) = l.flatMap (fun x => shiftl0 c (f x)) := by
  unfold shiftl0
  rw [List.map_flatMap]

theorem shiftl0_map {c : ℕ} {α : Type} (l : List α) (f : α → ℕ × ℕ × ℕ) :
    shiftl0 c (l.map f)
      = l.map (fun x => (((f x).1 - c, (f x).2.1, (f x).2.2) : ℕ × ℕ × ℕ)) := by
  unfold shiftl0
  rw [List.map_map]
  rfl

/-- Re-basing row 0 commutes with taking guarded copies of a block. -/
theorem shiftl0_gcopies_block {S : TrioSeq} {L d0 d1 c n : ℕ}
    (hc : ∀ x ∈ S, c ≤ x.1) (hL : L ≤ S.length) :
    shiftl0 c (gcopies S 0 L d0 d1 n) = gcopies (shiftl0 c S) 0 L d0 d1 n := by
  classical
  have hguard : ∀ j, le1 (shiftl0 c S) 0 j ↔ le1 S 0 j :=
    fun j => le1_shiftl0 (c := c) (Z := S) hc
  unfold gcopies gcopy
  rw [shiftl0_flatMap]
  refine List.flatMap_congr ?_
  intro k _
  rw [shiftl0_map]
  refine List.map_congr_left ?_
  intro j hj
  rw [List.mem_range'_1] at hj
  have hjS : j < S.length := by omega
  have hmem : S.getD j ((0, 0, 0) : ℕ × ℕ × ℕ) ∈ S := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjS]
    exact List.getElem_mem hjS
  have hcj : c ≤ entry S 0 j := hc _ hmem
  rw [entry0_shiftl0', entry1_shiftl0, entry2_shiftl0]
  by_cases hg : le1 S 0 j
  · rw [if_pos hg, if_pos ((hguard j).mpr hg)]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega
  · rw [if_neg hg, if_neg (fun hcx => hg ((hguard j).mp hcx))]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega

/-- **The whole re-basing**: the host's guarded copies at `p`, re-based in row
0, are the guarded copies of the cut-out block `B = shiftl0 c (seg R p (L+1))`
at its own root. -/
theorem shiftl0_gcopies_seg {R : TrioSeq} {p L d0 d1 c n : ℕ}
    (hlen : p + (L + 1) ≤ R.length)
    (hc : ∀ j, p ≤ j → j < p + (L + 1) → c ≤ entry R 0 j) :
    shiftl0 c (gcopies R p L d0 d1 n)
      = gcopies (shiftl0 c (seg R p (L + 1))) 0 L d0 d1 n := by
  rw [gcopies_seg R n hlen]
  exact shiftl0_gcopies_block (le_of_mem_seg hc) (by rw [seg_length]; omega)

/-! ## リフト文脈の中間ブロック則 (IL)

装備成分 `CtxInf`（文脈の再基底化した中間ブロックが `W` の package）を機械に
通すとき、唯一機械的でないのがリフト文脈 `ltail v z R t = mlift R v t`。
素朴な「中間ブロックの**根リフト**」は**偽**（tools/probe_infltail.py:
窓条件つきでも 1911/35973 反例）。正しい形は**環境マスクリフト**:

```
seg (mlift R v t) p (k+1)
  = mlift (seg R p (k+1)) v t   （p が錐に入るとき）
  = seg R p (k+1)               （入らないとき）
```

理由は `amin` の分解: 窓の中の列 `p+q` の行 0 祖先鎖は `p` を通ってから外へ
出るので `amin R (p+q) = min (amin (seg R p (k+1)) q) (amin R p)`。 -/

section InfLift

/-- Row-0 ancestry is invariant under re-basing row 0 (all entries at least
`c`). -/
theorem nextrel0_shiftl0 {c : ℕ} {Z : TrioSeq} (h : ∀ x ∈ Z, c ≤ x.1) {a b : ℕ} :
    nextrel0 (shiftl0 c Z) a b ↔ nextrel0 Z a b := by
  have hz : shiftr01 c 0 (shiftl0 c Z) = Z := shiftr01_shiftl0 h
  have hh := nextrel0_shiftr01 (d0 := c) (W := shiftl0 c Z) (a := a) (b := b)
  rw [hz] at hh
  exact hh.symm

theorem rtg0_shiftl0 {c : ℕ} {Z : TrioSeq} (h : ∀ x ∈ Z, c ≤ x.1) {a b : ℕ} :
    Relation.ReflTransGen (nextrel0 (shiftl0 c Z)) a b
      ↔ Relation.ReflTransGen (nextrel0 Z) a b := by
  have hz : shiftr01 c 0 (shiftl0 c Z) = Z := shiftr01_shiftl0 h
  have hh := rtg0_shiftr01 (d0 := c) (W := shiftl0 c Z) (a := a) (b := b)
  rw [hz] at hh
  exact hh.symm

theorem coneV_shiftl0 {c : ℕ} {Z : TrioSeq} (h : ∀ x ∈ Z, c ≤ x.1) {v j : ℕ} :
    coneV (shiftl0 c Z) v j ↔ coneV Z v j := by
  unfold coneV
  constructor
  · intro hc y hy
    have h1 := hc y ((rtg0_shiftl0 h).mpr hy)
    rwa [entry1_shiftl0] at h1
  · intro hc y hy
    rw [entry1_shiftl0]
    exact hc y ((rtg0_shiftl0 h).mp hy)

open Classical in
theorem shiftl0_mlift {c : ℕ} {Z : TrioSeq} (h : ∀ x ∈ Z, c ≤ x.1) (v t : ℕ) :
    shiftl0 c (mlift Z v t) = mlift (shiftl0 c Z) v t := by
  classical
  refine list_ext_getD ?_ ?_
  · rw [shiftl0_length, mlift_length, mlift_length, shiftl0_length]
  · intro i hi
    rw [shiftl0_length, mlift_length] at hi
    rw [getD_shiftl0, mlift_getD hi,
      mlift_getD (by rw [shiftl0_length]; exact hi)]
    dsimp only
    rw [entry0_shiftl0', entry1_shiftl0, entry2_shiftl0]
    by_cases hg : coneV Z v i
    · rw [if_pos hg, if_pos ((coneV_shiftl0 h).mpr hg)]
    · rw [if_neg hg, if_neg (fun hc => hg ((coneV_shiftl0 h).mp hc))]

/-- Row-0 ancestry inside a segment is the host's ancestry, translated. -/
theorem le0_seg_iff {R : TrioSeq} {p k a b : ℕ} (hlen : p + (k + 1) ≤ R.length)
    (hb : b < k + 1) :
    le0 (seg R p (k + 1)) a b ↔ le0 R (p + a) (p + b) := by
  have hsplit : R.take (p + (k + 1)) = R.take p ++ seg R p (k + 1) := by
    rw [← seg_zero_eq_take R (by omega), ← seg_zero_eq_take R (by omega),
      seg_append]
    simp
  have hplen : (R.take p).length = p := by rw [List.length_take]; omega
  have happ := le0_append_right (R.take p) (seg R p (k + 1)) a b
  rw [hplen] at happ
  have htk : le0 (R.take (p + (k + 1))) (p + a) (p + b) ↔ le0 R (p + a) (p + b) :=
    le0_take (by omega) (by omega)
  rw [← htk, hsplit]
  exact happ.symm

/-- **`amin` splits at the window root**: an ancestor of `p + q` either lives in
the segment or is an ancestor of `p` itself. -/
theorem amin_seg {R : TrioSeq} {p k q : ℕ} (hlen : p + (k + 1) ≤ R.length)
    (hq : q < k + 1)
    (hchain : Relation.ReflTransGen (nextrel0 R) p (p + q)) :
    amin R (p + q) = min (amin (seg R p (k + 1)) q) (amin R p) := by
  classical
  set S : TrioSeq := seg R p (k + 1) with hS
  have hSlen : S.length = k + 1 := by rw [hS, seg_length]
  refine Nat.le_antisymm ?_ ?_
  · refine Nat.le_min.mpr ⟨?_, ?_⟩
    · obtain ⟨y, hy, hey⟩ := amin_mem S q
      have hylt : y < k + 1 := by
        have := nextrel0_rtrancl_index_le hy
        omega
      have hyR : le0 R (p + y) (p + q) := by
        rw [← le0_seg_iff hlen hq]
        exact ⟨by rw [hSlen]; omega, by rw [hSlen]; omega, hy⟩
      have hle := amin_le hyR.2.2
      have hentry : entry S 1 y = entry R 1 (p + y) := by
        rw [hS]; exact entry_seg (by omega)
      omega
    · exact amin_mono hchain
  · obtain ⟨y, hy, hey⟩ := amin_mem R (p + q)
    rcases Nat.lt_or_ge y p with hyp | hyp
    · have hle0y : le0 R y (p + q) := ⟨by omega, by omega, hy⟩
      have hle0p : le0 R p (p + q) := ⟨by omega, by omega, hchain⟩
      have := amin_le (le0_of_le0_le0 hle0y hle0p hyp).2.2
      omega
    · obtain ⟨y', rfl⟩ : ∃ y', y = p + y' := ⟨y - p, by omega⟩
      have hy'le : y' ≤ q := by
        have := nextrel0_rtrancl_index_le hy
        omega
      have hyS : le0 S y' q := by
        rw [le0_seg_iff hlen hq]
        exact ⟨by omega, by omega, hy⟩
      have hle := amin_le hyS.2.2
      have hentry : entry S 1 y' = entry R 1 (p + y') := by
        rw [hS]; exact entry_seg (by omega : y' < k + 1)
      omega

theorem coneV_seg {R : TrioSeq} {p k q v : ℕ} (hlen : p + (k + 1) ≤ R.length)
    (hq : q < k + 1)
    (hchain : Relation.ReflTransGen (nextrel0 R) p (p + q)) :
    coneV R v (p + q) ↔ (coneV (seg R p (k + 1)) v q ∧ coneV R v p) := by
  rw [coneV_iff_amin, coneV_iff_amin, coneV_iff_amin, amin_seg hlen hq hchain]
  omega

open Classical in
/-- **(IL)**: the ambient mask lift restricts to a segment as the segment's own
ambient mask lift — or not at all, when the segment root is outside the cone. -/
theorem seg_mlift {R : TrioSeq} {p k v t : ℕ} (hlen : p + (k + 1) ≤ R.length)
    (hwin : ∀ q, q < k + 1 → Relation.ReflTransGen (nextrel0 R) p (p + q)) :
    seg (mlift R v t) p (k + 1)
      = if coneV R v p then mlift (seg R p (k + 1)) v t
        else seg R p (k + 1) := by
  classical
  refine list_ext_getD ?_ ?_
  · rw [seg_length]
    split <;> [rw [mlift_length, seg_length]; rw [seg_length]]
  · intro q hq
    rw [seg_length] at hq
    have hpq : p + q < R.length := by omega
    have hcone := coneV_seg (R := R) (p := p) (k := k) (q := q) (v := v) hlen hq
      (hwin q hq)
    rw [seg_getD hq, entry0_mlift, entry2_mlift,
      entry1_mlift hpq]
    by_cases hp : coneV R v p
    · rw [if_pos hp, mlift_getD (by rw [seg_length]; exact hq),
        entry_seg hq, entry_seg hq, entry_seg hq]
      by_cases hg : coneV (seg R p (k + 1)) v q
      · rw [if_pos hg, if_pos (hcone.mpr ⟨hg, hp⟩)]
      · rw [if_neg hg, if_neg (fun hc => hg (hcone.mp hc).1)]
    · rw [if_neg hp, seg_getD hq, if_neg (fun hc => hp (hcone.mp hc).2)]
      simp

theorem amin_shiftl0 {c : ℕ} {Z : TrioSeq} (h : ∀ x ∈ Z, c ≤ x.1) (j : ℕ) :
    amin (shiftl0 c Z) j = amin Z j := by
  refine Nat.le_antisymm ?_ ?_
  · obtain ⟨y, hy, hey⟩ := amin_mem Z j
    have hle := amin_le (A := shiftl0 c Z) ((rtg0_shiftl0 h).mpr hy)
    rw [entry1_shiftl0] at hle
    omega
  · obtain ⟨y, hy, hey⟩ := amin_mem (shiftl0 c Z) j
    have hle := amin_le (A := Z) ((rtg0_shiftl0 h).mp hy)
    rw [entry1_shiftl0] at hey
    omega

theorem shiftl0_slift {c : ℕ} {Z : TrioSeq} (h : ∀ x ∈ Z, c ≤ x.1)
    (φ : ℕ → ℕ) : shiftl0 c (slift Z φ) = slift (shiftl0 c Z) φ := by
  refine list_ext_getD ?_ ?_
  · rw [shiftl0_length, slift_length, slift_length, shiftl0_length]
  · intro i hi
    rw [shiftl0_length, slift_length] at hi
    rw [getD_shiftl0, slift_getD hi, slift_getD (by rw [shiftl0_length]; exact hi)]
    dsimp only
    rw [entry0_shiftl0', entry1_shiftl0, entry2_shiftl0, amin_shiftl0 h]

/-- **(IL), general staircase form**: a staircase lift restricts to a segment as
the segment's own staircase lift, with the staircase capped at the segment
root's ancestor-minimum (`stair_cap`). -/
theorem seg_slift {R : TrioSeq} {p k : ℕ} {φ : ℕ → ℕ} (hφ : Stair φ)
    (hlen : p + (k + 1) ≤ R.length)
    (hwin : ∀ q, q < k + 1 → Relation.ReflTransGen (nextrel0 R) p (p + q)) :
    seg (slift R φ) p (k + 1)
      = slift (seg R p (k + 1))
          (fun m => m + (φ (min (amin R p) m) - min (amin R p) m)) := by
  refine list_ext_getD ?_ ?_
  · rw [seg_length, slift_length, seg_length]
  · intro q hq
    rw [seg_length] at hq
    have hpq : p + q < R.length := by omega
    have hqS : q < (seg R p (k + 1)).length := by rw [seg_length]; exact hq
    have hamin := amin_seg (R := R) (p := p) (k := k) (q := q) hlen hq (hwin q hq)
    rw [seg_getD hq, entry0_slift, entry2_slift, entry1_slift hpq,
      slift_getD hqS, entry_seg hq, entry_seg hq, entry_seg hq, hamin]
    have hmin : min (amin R p) (amin (seg R p (k + 1)) q)
        = min (amin (seg R p (k + 1)) q) (amin R p) := Nat.min_comm _ _
    rw [hmin]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    dsimp only
    have hle : min (amin (seg R p (k + 1)) q) (amin R p)
        ≤ amin (seg R p (k + 1)) q := Nat.min_le_left _ _
    have hge := hφ.ge (min (amin (seg R p (k + 1)) q) (amin R p))
    omega

/-- The re-based general form. -/
theorem shiftl0_seg_slift {R : TrioSeq} {p k c : ℕ} {φ : ℕ → ℕ} (hφ : Stair φ)
    (hlen : p + (k + 1) ≤ R.length)
    (hwin : ∀ q, q < k + 1 → Relation.ReflTransGen (nextrel0 R) p (p + q))
    (hc : ∀ x ∈ seg R p (k + 1), c ≤ x.1) :
    shiftl0 c (seg (slift R φ) p (k + 1))
      = slift (shiftl0 c (seg R p (k + 1)))
          (fun m => m + (φ (min (amin R p) m) - min (amin R p) m)) := by
  rw [seg_slift hφ hlen hwin, shiftl0_slift hc]

/-- The lifted context IS the ambient mask lift. -/
theorem ltail_eq_mlift {v z t : ℕ} {R : TrioSeq} (hR : argOK R) :
    Wset.ltail v z R t = mlift R v t := by
  have h := lift_cons_eq_mlift (v := v) (z := z) (t := t) hR
  rw [Wset.lift_cons] at h
  simpa using congrArg List.tail h

open Classical in
/-- **(IL), re-based form** — the shape the context component `CtxInf` needs:
the lifted context's re-based infix is the infix's own ambient mask lift. -/
theorem shiftl0_seg_mlift {R : TrioSeq} {p k v t c : ℕ}
    (hlen : p + (k + 1) ≤ R.length)
    (hwin : ∀ q, q < k + 1 → Relation.ReflTransGen (nextrel0 R) p (p + q))
    (hc : ∀ x ∈ seg R p (k + 1), c ≤ x.1) :
    shiftl0 c (seg (mlift R v t) p (k + 1))
      = if coneV R v p then mlift (shiftl0 c (seg R p (k + 1))) v t
        else shiftl0 c (seg R p (k + 1)) := by
  rw [seg_mlift hlen hwin]
  split
  · rw [shiftl0_mlift hc]
  · rfl

open Classical in
/-- **(IL) for the lifted context**, stated with `ltail`. -/
theorem shiftl0_seg_ltail {R : TrioSeq} {p k v z t c : ℕ} (hR : argOK R)
    (hlen : p + (k + 1) ≤ R.length)
    (hwin : ∀ q, q < k + 1 → Relation.ReflTransGen (nextrel0 R) p (p + q))
    (hc : ∀ x ∈ seg R p (k + 1), c ≤ x.1) :
    shiftl0 c (seg (Wset.ltail v z R t) p (k + 1))
      = if coneV R v p then mlift (shiftl0 c (seg R p (k + 1))) v t
        else shiftl0 c (seg R p (k + 1)) := by
  rw [ltail_eq_mlift (v := v) (z := z) (t := t) hR]
  exact shiftl0_seg_mlift hlen hwin hc

/-! ### 複合文脈の中間ブロック（低位・高位） -/

theorem seg_graft_low {E A : TrioSeq} {p k : ℕ} (hk : p + k < E.length - 1) :
    seg (graft E A) p (k + 1) = seg E p (k + 1) := by
  unfold seg
  refine List.map_congr_left ?_
  intro j hj
  rw [List.mem_range'_1] at hj
  rw [entry_graft_low (by omega), entry_graft_low (by omega),
    entry_graft_low (by omega)]

theorem shiftl0_seg_graft_high {E A : TrioSeq} {j0 k : ℕ}
    (hk : j0 + k < A.length) :
    shiftl0 (entry (graft E A) 0 (E.length - 1 + j0))
        (seg (graft E A) (E.length - 1 + j0) (k + 1))
      = shiftl0 (entry A 0 j0) (seg A j0 (k + 1)) := by
  have hc : entry (graft E A) 0 (E.length - 1 + j0)
      = entry A 0 j0 + entry E 0 (E.length - 1) :=
    entry0_graft_high (by omega)
  refine list_ext_getD ?_ ?_
  · rw [shiftl0_length, seg_length, shiftl0_length, seg_length]
  · intro q hq
    rw [shiftl0_length, seg_length] at hq
    have hidx : E.length - 1 + j0 + q = E.length - 1 + (j0 + q) := by omega
    rw [getD_shiftl0, getD_shiftl0, seg_getD hq, seg_getD hq, hc, hidx,
      entry0_graft_high (by omega : j0 + q < A.length),
      entry1_graft_high, entry2_graft_high]
    refine Prod.ext ?_ (Prod.ext rfl rfl)
    dsimp only
    omega

end InfLift

end Rebase

end TRIO
