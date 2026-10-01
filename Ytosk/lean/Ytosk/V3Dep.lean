/-
**3 行: 最後の列への依存の閉包と、値の貼り合わせ。**

`DepX M x b i`: 呼び出し (b, i)（b = true は o、false は v）の値が、依存をたどって最後の列 x の o に届く。
展開 M[n] では、x より前の列のうち D（= DepX）に入らない呼び出しの値は変わらず、D に入る呼び出しの値は
fsD(·, ζ) になる（`desc.md`）。ここでは
- D に入らない呼び出しの右辺は、D の外で一致する 2 つの割り当てで同じ（`oRhs_nodep`・`vRhs_nodep`）、
- 列 i で M と N の構造が同じなら右辺も同じ（`SameAt`、`oRhs_same`・`vRhs_same`）、
- 貼り合わせた割り当て（x より前は M の値か fsD、x 以後は与えた値）が N の等式を満たす条件（`cons_glue`）
を示す。D の呼び出しの局所的な交換（枠の補題）は仮定 `hF` に置く。
-/
import Ytosk.V3Exist
import Ytosk.FSD

namespace Ytosk

open T

/-- The calls whose value reaches the `o` of column `x` along the dependencies. -/
inductive DepX (M : Mat) (x : Nat) : Bool → Nat → Prop
  | leaf : DepX M x true x
  | ochild {i c : Nat} : c ∈ children M i → col M c ≠ bump M i →
      ¬ (isUpg M c = true ∧ topped M c = true) → DepX M x true c → DepX M x true i
  | ov {i : Nat} : DepX M x false i → DepX M x true i
  | vpar {i m : Nat} : entry M 1 i ≠ 0 → par M 1 i = some m → DepX M x false m → DepX M x false i
  | vupg {i k : Nat} : entry M 1 i ≠ 0 → entry M 2 i = 0 → upg M i = some k → DepX M x false k →
      DepX M x false i
  | vbump {i j k : Nat} : entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → j ∈ children M i → col M j = bump M i →
      k ∈ children M j → DepX M x true k → DepX M x false i

/-! ## D の外の呼び出し -/

/-- Two valuations that agree outside `D`. -/
def AgreeOff (M : Mat) (x : Nat) (ρ₁ ρ₂ : Valn) : Prop :=
  (∀ i, ¬ DepX M x true i → ρ₁.o i = ρ₂.o i) ∧ (∀ i, ¬ DepX M x false i → ρ₁.v i = ρ₂.v i)

theorem oRhs_nodep {M : Mat} {x i : Nat} {ρ₁ ρ₂ : Valn} (h : AgreeOff M x ρ₁ ρ₂)
    (hi : ¬ DepX M x true i) : oRhs M ρ₁ i = oRhs M ρ₂ i := by
  apply oRhs_congr
  · exact h.2 i (fun hv => hi (DepX.ov hv))
  · intro c hc hb hu
    exact h.1 c (fun hd => hi (DepX.ochild hc hb hu hd))

theorem vRhs_nodep {M : Mat} {x i : Nat} {ρ₁ ρ₂ : Valn} (h : AgreeOff M x ρ₁ ρ₂)
    (hi : ¬ DepX M x false i) : vRhs M ρ₁ i = vRhs M ρ₂ i := by
  apply vRhs_congr
  · intro m h1 hm
    exact h.2 m (fun hd => hi (DepX.vpar h1 hm hd))
  · intro k h1 h2 hk
    exact h.2 k (fun hd => hi (DepX.vupg h1 h2 hk hd))
  · intro j hj h1 h2 hb k hk
    exact h.1 k (fun hd => hi (DepX.vbump h1 h2 hj hb hk hd))

/-! ## 構造が同じ列 -/

/-- Column `i` has the same local structure in `M` and `N` (everything the right sides read). -/
structure SameAt (M N : Mat) (i : Nat) : Prop where
  e1 : entry N 1 i = entry M 1 i
  e2 : entry N 2 i = entry M 2 i
  bump : bump N i = bump M i
  par1 : par N 1 i = par M 1 i
  upg : upg N i = upg M i
  ch : children N i = children M i
  chcol : ∀ c ∈ children M i, col N c = col M c
  chupg : ∀ c ∈ children M i, isUpg N c = isUpg M c
  chtop : ∀ c ∈ children M i, topped N c = topped M c
  chch : ∀ c ∈ children M i, children N c = children M c

theorem cnt_same {M N : Mat} {i : Nat} (h : SameAt M N i) (ρ : Valn) :
    ∀ c ∈ children M i, cnt N ρ i c = cnt M ρ i c := by
  intro c hc
  unfold cnt
  rw [h.chcol c hc, h.bump, h.chupg c hc, h.chtop c hc]

theorem oRhs_same {M N : Mat} {i : Nat} (h : SameAt M N i) (ρ : Valn) :
    oRhs N ρ i = oRhs M ρ i := by
  unfold oRhs
  rw [h.ch]
  congr 3
  exact List.map_congr_left (cnt_same h ρ)

theorem vRhs_same {M N : Mat} {i : Nat} (h : SameAt M N i) (ρ : Valn) :
    vRhs N ρ i = vRhs M ρ i := by
  unfold vRhs
  have hb : (children M i).map (bumpTerm N ρ i) = (children M i).map (bumpTerm M ρ i) := by
    apply List.map_congr_left
    intro j hj
    unfold bumpTerm
    rw [h.chcol j hj, h.bump, h.chch j hj]
  rw [h.e1, h.e2, h.par1, h.upg, h.ch, hb]

/-! ## 貼り合わせ -/

open Classical in
/-- Below `x`: the value in `M`, or `fsD(·, ζ)` on `D`. From `x` on: `ρN`. -/
noncomputable def glue (M : Mat) (x : Nat) (ρ ρN : Valn) (ζ : T) : Valn :=
  ⟨fun i => if i < x then (if DepX M x true i then fsD (ρ.o i) ζ else ρ.o i) else ρN.o i,
   fun i => if i < x then (if DepX M x false i then fsD (ρ.v i) ζ else ρ.v i) else ρN.v i⟩

theorem glue_o_lt {M : Mat} {x i : Nat} (ρ ρN : Valn) (ζ : T) (hi : i < x) (hd : ¬ DepX M x true i) :
    (glue M x ρ ρN ζ).o i = ρ.o i := by
  simp only [glue, if_pos hi, if_neg hd]

theorem glue_v_lt {M : Mat} {x i : Nat} (ρ ρN : Valn) (ζ : T) (hi : i < x) (hd : ¬ DepX M x false i) :
    (glue M x ρ ρN ζ).v i = ρ.v i := by
  simp only [glue, if_pos hi, if_neg hd]

theorem glue_o_dep {M : Mat} {x i : Nat} (ρ ρN : Valn) (ζ : T) (hi : i < x) (hd : DepX M x true i) :
    (glue M x ρ ρN ζ).o i = fsD (ρ.o i) ζ := by
  simp only [glue, if_pos hi, if_pos hd]

theorem glue_v_dep {M : Mat} {x i : Nat} (ρ ρN : Valn) (ζ : T) (hi : i < x) (hd : DepX M x false i) :
    (glue M x ρ ρN ζ).v i = fsD (ρ.v i) ζ := by
  simp only [glue, if_pos hi, if_pos hd]

theorem glue_o_ge {M : Mat} {x i : Nat} (ρ ρN : Valn) (ζ : T) (hi : x ≤ i) :
    (glue M x ρ ρN ζ).o i = ρN.o i := by
  simp only [glue, if_neg (Nat.not_lt.mpr hi)]

theorem glue_v_ge {M : Mat} {x i : Nat} (ρ ρN : Valn) (ζ : T) (hi : x ≤ i) :
    (glue M x ρ ρN ζ).v i = ρN.v i := by
  simp only [glue, if_neg (Nat.not_lt.mpr hi)]

/-- A dependency of a call below the last column is below the last column, except the leaf. -/
theorem nodep_lt_of_ge {M : Mat} {x i : Nat} (hx : x + 1 = M.length) (hi : i < M.length)
    (hix : x ≤ i) : i = x := by omega

/-- **Gluing.** The glued valuation satisfies the equations of `N` below `x`, given the structure and
the local exchange on `D`. (The calls outside `D` read only calls outside `D`, which keep `M`'s values;
`v(x)` is never read below `x` by an outside call, since the reads of an outside call are outside `D`.) -/
theorem cons_glue_lt {M N : Mat} {x : Nat} (hx : x + 1 = M.length) {ρ ρN : Valn} {ζ : T}
    (hC : Cons M ρ) (hS : ∀ i, i < x → SameAt M N i)
    (hvx : ∀ i, i < x → ¬ DepX M x false i → ∀ m, entry M 1 i ≠ 0 →
      (par M 1 i = some m ∨ (entry M 2 i = 0 ∧ upg M i = some m)) → m < x)
    (hF : ∀ i, i < x →
      (DepX M x true i → oRhs M (glue M x ρ ρN ζ) i = fsD (ρ.o i) ζ) ∧
      (DepX M x false i → vRhs M (glue M x ρ ρN ζ) i = fsD (ρ.v i) ζ)) :
    ∀ i, i < x → (glue M x ρ ρN ζ).o i = oRhs N (glue M x ρ ρN ζ) i ∧
      (glue M x ρ ρN ζ).v i = vRhs N (glue M x ρ ρN ζ) i := by
  intro i hi
  have hiM : i < M.length := by omega
  rw [oRhs_same (hS i hi), vRhs_same (hS i hi)]
  -- the glued valuation agrees with `ρ` on the reads of an outside call
  refine ⟨?_, ?_⟩
  · by_cases hd : DepX M x true i
    · rw [glue_o_dep ρ ρN ζ hi hd, (hF i hi).1 hd]
    · rw [glue_o_lt ρ ρN ζ hi hd, (hC i hiM).1]
      apply oRhs_congr
      · have hv : ¬ DepX M x false i := fun hv => hd (DepX.ov hv)
        rw [glue_v_lt ρ ρN ζ hi hv]
      · intro c hc hb hu
        have hcd : ¬ DepX M x true c := fun h => hd (DepX.ochild hc hb hu h)
        have hcl := (mem_children hc).2
        have hcx : c < x := by
          rcases Nat.lt_or_ge c x with h | h
          · exact h
          · have : c = x := by omega
            subst this; exact absurd DepX.leaf hcd
        rw [glue_o_lt ρ ρN ζ hcx hcd]
  · by_cases hd : DepX M x false i
    · rw [glue_v_dep ρ ρN ζ hi hd, (hF i hi).2 hd]
    · rw [glue_v_lt ρ ρN ζ hi hd, (hC i hiM).2]
      apply vRhs_congr
      · intro m h1 hm
        have hmd : ¬ DepX M x false m := fun h => hd (DepX.vpar h1 hm h)
        rw [glue_v_lt ρ ρN ζ (hvx i hi hd m h1 (Or.inl hm)) hmd]
      · intro k h1 h2 hk
        have hkd : ¬ DepX M x false k := fun h => hd (DepX.vupg h1 h2 hk h)
        rw [glue_v_lt ρ ρN ζ (hvx i hi hd k h1 (Or.inr ⟨h2, hk⟩)) hkd]
      · intro j hj h1 h2 hb k hk
        have hkd : ¬ DepX M x true k := fun h => hd (DepX.vbump h1 h2 hj hb hk h)
        have hkl := (mem_children hk).2
        have hkx : k < x := by
          rcases Nat.lt_or_ge k x with h | h
          · exact h
          · have : k = x := by omega
            subst this; exact absurd DepX.leaf hkd
        rw [glue_o_lt ρ ρN ζ hkx hkd]

end Ytosk
