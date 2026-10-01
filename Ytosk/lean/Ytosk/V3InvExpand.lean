/-
**Inv3 の構造の部分は展開で保たれる（すべての t・すべての n）。SRO 以外の Std の行列はみな満たす。**

- `SInv`: 依頼の 10 項目（R0P・Z2・SibDec・Z1C・UAT・UAB・R12・BumpE2・R01・行 0 の先頭が 0）。
- `SInvX`: 展開で閉じる形（UAB・UAT の代わりに BumpLeaf、R1S を足す）。`SInvX.toSInv` で SInv に戻る
  （`uab_of_bumpLeaf`・`uat_of_uab`）。
- `sInvX_expand`: SInvX M → SInvX (expand M n)。列ごとの性質は V3InvExp、局所的な性質は
  `loc_t0`・`loc_t1`・`loc_t2`（種 S を経由）、零列・親なし・n = 0 は take。
- SRO 自身は UAB を満たさない（`sro_not_uab`: upg 3 = 1、のりしろの子 2 が 3 の祖先）。SRO の展開は
  種 (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1) を `decide` で確かめて出す（`sro_expand`）。
- `sInv_std`: Std M → M ≠ SRO → SInv M。
-/
import Ytosk.V3InvSeed3

namespace Ytosk

open T

/-- The structural part of `Inv3`. -/
structure SInv (M : Mat) : Prop where
  r0p : R0P M
  z2 : Z2 M
  sibDec : SibDec M
  z1c : Z1C M
  uat : UAT M
  uab : UAB M
  r12 : R12 M
  bumpE2 : BumpE2 M
  r01 : R01 M
  e00 : entry M 0 0 = 0

/-- The form closed under expansion. -/
structure SInvX (M : Mat) : Prop where
  r0p : R0P M
  r1s : R1S M
  z2 : Z2 M
  r12 : R12 M
  r01 : R01 M
  e00 : entry M 0 0 = 0
  loc : LocInv M

theorem SInvX.toSInv {M : Mat} (h : SInvX M) : SInv M :=
  have hUAB := uab_of_bumpLeaf h.loc.2.2.2
  ⟨h.r0p, h.z2, h.loc.1, h.loc.2.1, uat_of_uab h.r0p h.z2 h.loc.1 h.loc.2.1 hUAB, hUAB, h.r12,
    h.loc.2.2.1, h.r01, h.e00⟩

theorem locInv_take {M : Mat} (h : LocInv M) (k : Nat) : LocInv (M.take k) :=
  ⟨SibDec_take h.1 k, Z1C_take h.2.1 k, BumpE2_take h.2.2.1 k, bumpLeaf_take h.2.2.2 k⟩

theorem gexp_n0 (M : Mat) (r L d0 d1 : Nat) : TRIO.gexp M r L d0 d1 0 = M.take r := by
  unfold TRIO.gexp TRIO.gcopies; simp

/-! ## 展開 -/

theorem locInv_expand {M : Mat} (h : LocInv M) (hZ2 : Z2 M) (n : Nat) : LocInv (expand M n) := by
  by_cases hM : M.length < 2
  · rw [expand_short hM]; simpa using locInv_take h 0
  rcases expand_cases M n (by omega) with he | ⟨r, hp, he⟩
  · rw [he]; exact locInv_take h _
  rw [he]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rw [gexp_n0]; exact locInv_take h r
  have hx : (M.length - 1) + 1 = M.length := by omega
  unfold TRIO.srow at hp ⊢
  by_cases h2 : 0 < TRIO.entry M 2 (M.length - 1)
  · simp only [h2, if_true] at hp ⊢
    exact loc_t2 hx h hZ2 hp hn
  · simp only [h2, if_false] at hp ⊢
    by_cases h1 : 0 < TRIO.entry M 1 (M.length - 1)
    · simp only [h1, if_true] at hp ⊢
      exact loc_t1 hx h hp hn
    · simp only [h1, if_false] at hp ⊢
      exact loc_t0 hx h hp hn

/-- **The structural invariants survive every expansion.** -/
theorem sInvX_expand {M : Mat} (h : SInvX M) (n : Nat) : SInvX (expand M n) :=
  have h01 := R0P_R1S_expand h.e00 h.r0p h.r1s n
  ⟨h01.1, h01.2, Z2_expand h.z2 n, R12_expand h.z2 h.r12 n, R01_expand h.r12 h.r01 n,
    e00_expand h.e00 n, locInv_expand h.loc h.z2 n⟩

theorem sInv_expand {M : Mat} (h : SInvX M) (n : Nat) : SInv (expand M n) :=
  (sInvX_expand h n).toSInv

/-! ## 具体的な行列（decide） -/

instance colLe_dec (a b : Nat × Nat × Nat) : Decidable (colLe a b) := by
  unfold colLe; infer_instance

/-- Bounded forms of the local properties, decidable on a concrete matrix. -/
structure LocB (M : Mat) : Prop where
  sd : ∀ p, p < M.length → ∀ a ∈ children M p, ∀ b ∈ children M p, a < b →
    (∀ e ∈ children M p, ¬ (a < e ∧ e < b)) → colLe (col M b) (col M a)
  z1 : ∀ p, p < M.length → entry M 2 p = 1 → ∀ c ∈ children M p, entry M 1 c ≤ entry M 1 p
  be : ∀ p, p < M.length → ∀ c ∈ children M p, col M c = bump M p → entry M 2 p = 1
  bl0 : ∀ k, k < M.length → ∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j,
    entry M 1 k ≤ entry M 1 c → entry M 2 c = 0
  bl1 : ∀ k, k < M.length → ∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j,
    entry M 1 k ≤ entry M 1 c → children M c = []
  bl2 : ∀ k, k < M.length → ∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j,
    entry M 1 k ≤ entry M 1 c → (children M j).getLast? = some c
  bl3 : ∀ k, k < M.length → ∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j,
    entry M 1 k ≤ entry M 1 c → (children M k).getLast? = some j

theorem LocB.toLocInv {M : Mat} (h : LocB M) : LocInv M := by
  refine ⟨fun p l1 l2 a b hch => ?_, fun p c h2 hc => ?_, fun p c hc hb => ?_,
    fun k j c hj hb hc h1 => ?_⟩
  · obtain ⟨hab, ha, hb, hno⟩ := split_consec (children_sorted M p) hch
    have := mem_children ha
    exact h.sd p (by omega) a ha b hb hab hno
  · have := mem_children hc
    exact h.z1 p (by omega) h2 c hc
  · have := mem_children hc
    exact h.be p (by omega) c hc hb
  · have := mem_children hj
    exact ⟨h.bl0 k (by omega) j hj hb c hc h1, h.bl1 k (by omega) j hj hb c hc h1,
      h.bl2 k (by omega) j hj hb c hc h1, h.bl3 k (by omega) j hj hb c hc h1⟩

/-- A property of all columns, from the columns of a concrete matrix. -/
theorem all_of_lt {M : Mat} {P : Nat → Prop} (hout : ∀ i, M.length ≤ i → P i)
    (h : ∀ i, i < M.length → P i) : ∀ i, P i := fun i => by
  rcases Nat.lt_or_ge i M.length with hi | hi
  · exact h i hi
  · exact hout i hi

/-- The row-0 parent relation of a concrete matrix. -/
theorem par0_of_lt {M : Mat} {P : Nat → Nat → Prop}
    (h : ∀ c, c < M.length → ∀ p, p < c → par M 0 c = some p → P c p) :
    ∀ c p, par M 0 c = some p → P c p := fun c p hp => by
  have hpc := par_lt M 0 c p hp
  rcases Nat.lt_or_ge c M.length with hc | hc
  · exact h c hc p hpc hp
  · exact absurd hp (par0_out hc)

/-- **SRO itself fails `UAB`**: `upg 3 = 1` and the bump child `2` of `1` is an ancestor of `3`. -/
theorem sro_not_uab : ¬ UAB SRO := fun h =>
  h 3 1 (by decide) (by decide) 2 (by decide) (by decide)
    (Anc0.step (by decide : par SRO 0 3 = some 2) (Anc0.refl 2))

theorem sro_cols : R0P SRO ∧ R1S SRO ∧ Z2 SRO ∧ R12 SRO ∧ R01 SRO ∧ entry SRO 0 0 = 0 := by
  refine ⟨par0_of_lt (by decide), par0_of_lt (by decide),
    all_of_lt (M := SRO) (fun i hi => ?_) (by decide),
    all_of_lt (M := SRO) (fun i hi _ => ?_) (by decide),
    all_of_lt (M := SRO) (fun i hi _ => ?_) (by decide), by decide⟩
  · rw [entry_out hi]; omega
  · exact entry_out hi 2
  · exact entry_out hi 1

/-- **Every expansion of SRO satisfies the invariants** (through the seed
`(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)`, checked by `decide`). -/
theorem sro_expand (n : Nat) : SInvX (expand SRO n) := by
  obtain ⟨hR0, hR1, hZ2, hR12, hR01, h00⟩ := sro_cols
  have h01 := R0P_R1S_expand h00 hR0 hR1 n
  refine ⟨h01.1, h01.2, Z2_expand hZ2 n, R12_expand hZ2 hR12 n, R01_expand hR12 hR01 n,
    e00_expand h00 n, ?_⟩
  rcases expand_cases SRO n (by decide) with he | ⟨r, hp, he⟩
  · rw [he]
    exact LocB.toLocInv ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hp1 : par SRO (TRIO.srow SRO (SRO.length - 1)) (SRO.length - 1) = some 1 := by decide
  rw [hp1] at hp
  cases hp
  have he' : expand SRO n = TRIO.gexp SRO 1 (4 - 1) 0 0 n := by rw [he]; rfl
  rw [he']
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rw [gexp_n0]
    exact LocB.toLocInv ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hx : 4 + 1 = SRO.length := rfl
  have hr : par SRO 0 4 = some 1 := by decide
  have hS := seed_seed0 hx hr
  have hlS : (seedOf SRO 1 0 0).length = 5 := rfl
  have key : ∀ K, K < 5 → ∀ J ∈ children (seedOf SRO 1 0 0) K,
      col (seedOf SRO 1 0 0) J = bump (seedOf SRO 1 0 0) K → 4 ∈ children (seedOf SRO 1 0 0) J →
      entry (seedOf SRO 1 0 0) 1 K ≤ entry (seedOf SRO 1 0 0) 1 4 → False := by decide
  exact loc_of_seed hx (by decide) hS (LocB.toLocInv ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩)
    (fun K J hJ => key K (by have := mem_children hJ; omega) J hJ)
    (fun hA _ _ _ => hS.root_excl hA rfl) hn

/-! ## Std -/

theorem sInvX_std' {M : Mat} (h : Std M) : M = SRO ∨ SInvX M := by
  induction h with
  | sro => exact Or.inl rfl
  | exp n _ ih =>
    right
    rcases ih with h | h
    · subst h; exact sro_expand n
    · exact sInvX_expand h n

/-- **Every standard matrix other than SRO satisfies the structural invariants.** -/
theorem sInv_std {M : Mat} (h : Std M) (hne : M ≠ SRO) : SInv M :=
  ((sInvX_std' h).resolve_left hne).toSInv

end Ytosk
