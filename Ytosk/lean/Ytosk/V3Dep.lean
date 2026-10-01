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
  par1 : par N 1 i = par M 1 i
  upg : upg N i = upg M i
  ch : children N i = children M i
  cnt : ∀ c ∈ children M i, ∀ ρ : Valn, cnt N ρ i c = cnt M ρ i c
  bt : ∀ c ∈ children M i, ∀ ρ : Valn, bumpTerm N ρ i c = bumpTerm M ρ i c

theorem oRhs_same {M N : Mat} {i : Nat} (h : SameAt M N i) (ρ : Valn) :
    oRhs N ρ i = oRhs M ρ i := by
  unfold oRhs
  rw [h.ch]
  congr 3
  exact List.map_congr_left (fun c hc => h.cnt c hc ρ)

theorem vRhs_same {M N : Mat} {i : Nat} (h : SameAt M N i) (ρ : Valn) :
    vRhs N ρ i = vRhs M ρ i := by
  unfold vRhs
  have hb : (children M i).map (bumpTerm N ρ i) = (children M i).map (bumpTerm M ρ i) :=
    List.map_congr_left (fun c hc => h.bt c hc ρ)
  rw [h.e1, h.e2, h.par1, h.upg, h.ch, hb]

/-- `SameAt` from the structure of the children. -/
theorem sameAt_of {M N : Mat} {i : Nat} (e1 : entry N 1 i = entry M 1 i)
    (e2 : entry N 2 i = entry M 2 i) (hb : bump N i = bump M i) (hp : par N 1 i = par M 1 i)
    (hu : upg N i = upg M i) (hch : children N i = children M i)
    (hcol : ∀ c ∈ children M i, col N c = col M c)
    (hiu : ∀ c ∈ children M i, isUpg N c = isUpg M c)
    (htop : ∀ c ∈ children M i, topped N c = topped M c)
    (hchch : ∀ c ∈ children M i, children N c = children M c) : SameAt M N i where
  e1 := e1
  e2 := e2
  par1 := hp
  upg := hu
  ch := hch
  cnt := fun c hc ρ => by unfold cnt; rw [hcol c hc, hb, hiu c hc, htop c hc]
  bt := fun c hc ρ => by unfold bumpTerm; rw [hcol c hc, hb, hchch c hc]

/-! ## 貼り合わせ -/

open Classical in
/-- Below `x`: the value in `M`, or `fsD(·, Z i)` on `D` (the index may depend on the column).
From `x` on: `ρN`. -/
noncomputable def glueZ (M : Mat) (x : Nat) (ρ ρN : Valn) (Z : Nat → T) : Valn :=
  ⟨fun i => if i < x then (if DepX M x true i then fsD (ρ.o i) (Z i) else ρ.o i) else ρN.o i,
   fun i => if i < x then (if DepX M x false i then fsD (ρ.v i) (Z i) else ρ.v i) else ρN.v i⟩

/-- The glued valuation with one index `ζ`. -/
noncomputable def glue (M : Mat) (x : Nat) (ρ ρN : Valn) (ζ : T) : Valn :=
  glueZ M x ρ ρN (fun _ => ζ)

theorem glueZ_o_lt {M : Mat} {x i : Nat} (ρ ρN : Valn) (Z : Nat → T) (hi : i < x)
    (hd : ¬ DepX M x true i) : (glueZ M x ρ ρN Z).o i = ρ.o i := by
  simp only [glueZ, if_pos hi, if_neg hd]

theorem glueZ_v_lt {M : Mat} {x i : Nat} (ρ ρN : Valn) (Z : Nat → T) (hi : i < x)
    (hd : ¬ DepX M x false i) : (glueZ M x ρ ρN Z).v i = ρ.v i := by
  simp only [glueZ, if_pos hi, if_neg hd]

theorem glueZ_o_dep {M : Mat} {x i : Nat} (ρ ρN : Valn) (Z : Nat → T) (hi : i < x)
    (hd : DepX M x true i) : (glueZ M x ρ ρN Z).o i = fsD (ρ.o i) (Z i) := by
  simp only [glueZ, if_pos hi, if_pos hd]

theorem glueZ_v_dep {M : Mat} {x i : Nat} (ρ ρN : Valn) (Z : Nat → T) (hi : i < x)
    (hd : DepX M x false i) : (glueZ M x ρ ρN Z).v i = fsD (ρ.v i) (Z i) := by
  simp only [glueZ, if_pos hi, if_pos hd]

theorem glueZ_o_ge {M : Mat} {x i : Nat} (ρ ρN : Valn) (Z : Nat → T) (hi : x ≤ i) :
    (glueZ M x ρ ρN Z).o i = ρN.o i := by
  simp only [glueZ, if_neg (Nat.not_lt.mpr hi)]

theorem glueZ_v_ge {M : Mat} {x i : Nat} (ρ ρN : Valn) (Z : Nat → T) (hi : x ≤ i) :
    (glueZ M x ρ ρN Z).v i = ρN.v i := by
  simp only [glueZ, if_neg (Nat.not_lt.mpr hi)]

theorem glue_o_lt {M : Mat} {x i : Nat} (ρ ρN : Valn) (ζ : T) (hi : i < x) (hd : ¬ DepX M x true i) :
    (glue M x ρ ρN ζ).o i = ρ.o i := by
  simp only [glue, glueZ, if_pos hi, if_neg hd]

theorem glue_v_lt {M : Mat} {x i : Nat} (ρ ρN : Valn) (ζ : T) (hi : i < x) (hd : ¬ DepX M x false i) :
    (glue M x ρ ρN ζ).v i = ρ.v i := by
  simp only [glue, glueZ, if_pos hi, if_neg hd]

theorem glue_o_dep {M : Mat} {x i : Nat} (ρ ρN : Valn) (ζ : T) (hi : i < x) (hd : DepX M x true i) :
    (glue M x ρ ρN ζ).o i = fsD (ρ.o i) ζ := by
  simp only [glue, glueZ, if_pos hi, if_pos hd]

theorem glue_v_dep {M : Mat} {x i : Nat} (ρ ρN : Valn) (ζ : T) (hi : i < x) (hd : DepX M x false i) :
    (glue M x ρ ρN ζ).v i = fsD (ρ.v i) ζ := by
  simp only [glue, glueZ, if_pos hi, if_pos hd]

theorem glue_o_ge {M : Mat} {x i : Nat} (ρ ρN : Valn) (ζ : T) (hi : x ≤ i) :
    (glue M x ρ ρN ζ).o i = ρN.o i := by
  simp only [glue, glueZ, if_neg (Nat.not_lt.mpr hi)]

theorem glue_v_ge {M : Mat} {x i : Nat} (ρ ρN : Valn) (ζ : T) (hi : x ≤ i) :
    (glue M x ρ ρN ζ).v i = ρN.v i := by
  simp only [glue, glueZ, if_neg (Nat.not_lt.mpr hi)]

/-- A dependency of a call below the last column is below the last column, except the leaf. -/
theorem nodep_lt_of_ge {M : Mat} {x i : Nat} (hx : x + 1 = M.length) (hi : i < M.length)
    (hix : x ≤ i) : i = x := by omega

/-- **Gluing.** The glued valuation satisfies the equations of `N` below `x`, given the structure and
the local exchange on `D`. (The calls outside `D` read only calls outside `D`, which keep `M`'s values;
`v(x)` is never read below `x` by an outside call, since the reads of an outside call are outside `D`.) -/
theorem cons_glue_lt {M N : Mat} {x : Nat} (hx : x + 1 = M.length) {ρ ρN : Valn} {Z : Nat → T}
    (hC : Cons M ρ) (hS : ∀ i, i < x → SameAt M N i)
    (hvx : ∀ i, i < x → ¬ DepX M x false i → ∀ m, entry M 1 i ≠ 0 →
      (par M 1 i = some m ∨ (entry M 2 i = 0 ∧ upg M i = some m)) → m < x)
    (hF : ∀ i, i < x →
      (DepX M x true i → oRhs M (glueZ M x ρ ρN Z) i = fsD (ρ.o i) (Z i)) ∧
      (DepX M x false i → vRhs M (glueZ M x ρ ρN Z) i = fsD (ρ.v i) (Z i))) :
    ∀ i, i < x → (glueZ M x ρ ρN Z).o i = oRhs N (glueZ M x ρ ρN Z) i ∧
      (glueZ M x ρ ρN Z).v i = vRhs N (glueZ M x ρ ρN Z) i := by
  intro i hi
  have hiM : i < M.length := by omega
  rw [oRhs_same (hS i hi), vRhs_same (hS i hi)]
  -- the glued valuation agrees with `ρ` on the reads of an outside call
  refine ⟨?_, ?_⟩
  · by_cases hd : DepX M x true i
    · rw [glueZ_o_dep ρ ρN Z hi hd, (hF i hi).1 hd]
    · rw [glueZ_o_lt ρ ρN Z hi hd, (hC i hiM).1]
      apply oRhs_congr
      · have hv : ¬ DepX M x false i := fun hv => hd (DepX.ov hv)
        rw [glueZ_v_lt ρ ρN Z hi hv]
      · intro c hc hb hu
        have hcd : ¬ DepX M x true c := fun h => hd (DepX.ochild hc hb hu h)
        have hcl := (mem_children hc).2
        have hcx : c < x := by
          rcases Nat.lt_or_ge c x with h | h
          · exact h
          · have : c = x := by omega
            subst this; exact absurd DepX.leaf hcd
        rw [glueZ_o_lt ρ ρN Z hcx hcd]
  · by_cases hd : DepX M x false i
    · rw [glueZ_v_dep ρ ρN Z hi hd, (hF i hi).2 hd]
    · rw [glueZ_v_lt ρ ρN Z hi hd, (hC i hiM).2]
      apply vRhs_congr
      · intro m h1 hm
        have hmd : ¬ DepX M x false m := fun h => hd (DepX.vpar h1 hm h)
        rw [glueZ_v_lt ρ ρN Z (hvx i hi hd m h1 (Or.inl hm)) hmd]
      · intro k h1 h2 hk
        have hkd : ¬ DepX M x false k := fun h => hd (DepX.vupg h1 h2 hk h)
        rw [glueZ_v_lt ρ ρN Z (hvx i hi hd k h1 (Or.inr ⟨h2, hk⟩)) hkd]
      · intro j hj h1 h2 hb k hk
        have hkd : ¬ DepX M x true k := fun h => hd (DepX.vbump h1 h2 hj hb hk h)
        have hkl := (mem_children hk).2
        have hkx : k < x := by
          rcases Nat.lt_or_ge k x with h | h
          · exact h
          · have : k = x := by omega
            subst this; exact absurd DepX.leaf hkd
        rw [glueZ_o_lt ρ ρN Z hkx hkd]

end Ytosk
