import L105Cap
import GzD

namespace TRIO
open Wset Gw GxL GxN GzD

/-! # C4 = (0,0,0)(1,1,1)(2,1,1)(3,1,0) ∈ W 0 の grind (scratch, 複数ハートビート)
Step 1: R の基本事実(argOK / domT / hasParent)を手構成で green に。 -/

def Rc4 : TrioSeq := [((1,1,1) : ℕ×ℕ×ℕ), ((2,1,1) : ℕ×ℕ×ℕ), ((3,1,0) : ℕ×ℕ×ℕ)]

def C4f : TrioSeq := ((0,0,0) : ℕ×ℕ×ℕ) :: Rc4

theorem Rc4_argOK : argOK Rc4 := by
  intro p hp
  simp only [Rc4, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem Rc4_srow : srow Rc4 (Rc4.length - 1) = 1 := by decide

theorem Rc4_ne : Rc4 ≠ [] := by decide

theorem Rc4_domT : domT Rc4 1 := by
  refine ⟨by decide, ?_⟩
  rw [Rc4_srow]
  rintro ⟨j0, hj0, -⟩
  unfold nextR at hj0
  rw [if_neg (by decide), if_pos rfl] at hj0
  have hlt := hj0.2.2.1
  have hent := hj0.2.2.2.1
  have hlen : Rc4.length - 1 = 2 := by decide
  rw [hlen] at hlt hent
  have he2 : entry Rc4 1 2 = 1 := by decide
  rw [he2] at hent
  have hj02 : j0 = 0 ∨ j0 = 1 := by omega
  rcases hj02 with rfl | rfl
  · exact absurd hent (by decide)
  · exact absurd hent (by decide)

/-- le0 C4f 0 3 を ReflTransGen チェーン 0→1→2→3 で構成。 -/
theorem C4_le0 : le0 C4f 0 3 := by
  refine ⟨by decide, by decide, ?_⟩
  have s01 : nextrel0 C4f 0 1 := ⟨by decide, by decide, by decide, by decide, by intro j hj; omega⟩
  have s12 : nextrel0 C4f 1 2 := ⟨by decide, by decide, by decide, by decide, by intro j hj; omega⟩
  have s23 : nextrel0 C4f 2 3 := ⟨by decide, by decide, by decide, by decide, by intro j hj; omega⟩
  exact (((Relation.ReflTransGen.refl.tail s01).tail s12).tail s23)

theorem C4_hasParent :
    hasParent C4f (srow Rc4 (Rc4.length - 1)) Rc4.length := by
  rw [Rc4_srow]
  have hlen : Rc4.length = 3 := by decide
  rw [hlen]
  exact hasParent_one_of (M := C4f) (b := 3) (k := 0) (by decide) (by decide) C4_le0 (by decide)

/-! Step 2: C4⟦n⟧ = tow 0 0 Rc4 n、tow 帰納で C4 を「塔ステップ」1本に還元。 -/

theorem C4_oper (n : ℕ) : C4f⟦n⟧ = tow 0 0 Rc4 n :=
  oper_cons_tower1 (v := 0) (z := 0) (m := 1) Rc4_argOK Rc4_ne Rc4_domT Rc4_srow C4_hasParent

/-- 塔ステップ(crux, 開コア): 根 (0,0,0) の下に基底ブロック X を graft しても W 0 に残る。 -/
def TowStepC4 : Prop :=
  ∀ X : TrioSeq, X ∈ W 0 → based X →
    (((0,0,0) : ℕ×ℕ×ℕ) :: graft Rc4 X) ∈ W 0

theorem tow_mem_of_step (h : TowStepC4) : ∀ k, tow 0 0 Rc4 k ∈ W 0 := by
  intro k
  induction k with
  | zero => simpa [tow] using W_nil 0
  | succ k ih =>
      show (((0,0,0) : ℕ×ℕ×ℕ) :: graft Rc4 (tow 0 0 Rc4 k)) ∈ W 0
      exact h _ ih (based_tow 0 0 Rc4 k)

/-- **C4 ∈ W 0、塔ステップ `TowStepC4` を法として**(verified、開コアは 1 本に isolate)。 -/
theorem C4_mem_of_step (h : TowStepC4) : C4f ∈ W 0 := by
  refine mem_of_oper_mem (fun n hn => ?_)
  rw [C4_oper n]
  exact tow_mem_of_step h n

/-! Step 3: TowStepC4 が `Subst1`(原子的開コア)の具体インスタンスであることを繋ぐ。
    S = C3 = (0,0,0)(1,1,1)(2,1,1), p = 2, C = (2,1,1) :: shiftr01 3 0 X。 -/

theorem graft_Rc4_eq (X : TrioSeq) :
    (((0,0,0) : ℕ×ℕ×ℕ) :: graft Rc4 X)
      = [((0,0,0):ℕ×ℕ×ℕ), ((1,1,1):ℕ×ℕ×ℕ)] ++ (((2,1,1):ℕ×ℕ×ℕ) :: shiftr01 3 0 X) := by
  unfold graft shiftr01
  have hdl : Rc4.dropLast = [((1,1,1):ℕ×ℕ×ℕ), ((2,1,1):ℕ×ℕ×ℕ)] := by decide
  have hen : entry Rc4 0 (Rc4.length - 1) = 3 := by decide
  rw [hdl, hen]
  simp

theorem TowStepC4_of_subst1 (hs : Subst1)
    (hsub : ∀ X : TrioSeq, X ∈ W 0 → based X →
      (((2,1,1) : ℕ×ℕ×ℕ) :: shiftr01 3 0 X) ∈ W 3) :
    TowStepC4 := by
  intro X hX hbX
  rw [graft_Rc4_eq X]
  have hC3 : ([((0,0,0):ℕ×ℕ×ℕ), ((1,1,1):ℕ×ℕ×ℕ), ((2,1,1):ℕ×ℕ×ℕ)] : TrioSeq) ∈ W 0 :=
    GzD.R1317_mem
  have hlev : lev ([((0,0,0):ℕ×ℕ×ℕ), ((1,1,1):ℕ×ℕ×ℕ), ((2,1,1):ℕ×ℕ×ℕ)] : TrioSeq) 2 = 3 := by
    decide
  have hhead : ∀ i, entry (((2,1,1):ℕ×ℕ×ℕ) :: shiftr01 3 0 X) i 0
      = entry ([((0,0,0):ℕ×ℕ×ℕ), ((1,1,1):ℕ×ℕ×ℕ), ((2,1,1):ℕ×ℕ×ℕ)] : TrioSeq) i 2 := by
    intro i; rfl
  have hdeep : ∀ j, 1 ≤ j → j < (((2,1,1):ℕ×ℕ×ℕ) :: shiftr01 3 0 X).length →
      entry ([((0,0,0):ℕ×ℕ×ℕ), ((1,1,1):ℕ×ℕ×ℕ), ((2,1,1):ℕ×ℕ×ℕ)] : TrioSeq) 0 2
        < entry (((2,1,1):ℕ×ℕ×ℕ) :: shiftr01 3 0 X) 0 j := by
    intro j hj1 hj2
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have h2 : entry ([((0,0,0):ℕ×ℕ×ℕ), ((1,1,1):ℕ×ℕ×ℕ), ((2,1,1):ℕ×ℕ×ℕ)] : TrioSeq) 0 2 = 2 := by
      decide
    rw [h2, entry_cons]
    have hkX : k < X.length := by
      have := hj2
      rw [List.length_cons, shiftr01_length] at this
      omega
    rw [entry0_shiftr01 hkX]
    omega
  have hres := hs 0 2 [((0,0,0):ℕ×ℕ×ℕ), ((1,1,1):ℕ×ℕ×ℕ), ((2,1,1):ℕ×ℕ×ℕ)]
    (((2,1,1):ℕ×ℕ×ℕ) :: shiftr01 3 0 X) hC3 (by decide) (by simp)
    (by rw [hlev]; exact hsub X hX hbX) hhead hdeep
  simpa using hres

/-- **C4 ∈ W 0、`Subst1` と副条件 `hsub` を法として**(verified)。
    C4 = psi(I) の接頭辞。psi(I) の一歩手前を原子的開コア `Subst1`(+ 深い graft 副条件)
    まで検証済みで還元。 -/
theorem C4_mem_of_subst1 (hs : Subst1)
    (hsub : ∀ X : TrioSeq, X ∈ W 0 → based X →
      (((2,1,1) : ℕ×ℕ×ℕ) :: shiftr01 3 0 X) ∈ W 3) :
    C4f ∈ W 0 :=
  C4_mem_of_step (TowStepC4_of_subst1 hs hsub)

/-! Step 4: レベル v の族 famC4 と ZBr 構造条件(argOK/srow/domT)を v で一般化(族構成の第一歩)。
    co-recursive graft 閉包(ZBr case4 の残り)が frontier。 -/

def famC4 : ℕ → TrioSeq :=
  fun v => [((1,v+1,1):ℕ×ℕ×ℕ), ((2,v+1,1):ℕ×ℕ×ℕ), ((3,v+1,0):ℕ×ℕ×ℕ)]

theorem famC4_len (v : ℕ) : (famC4 v).length = 3 := rfl

theorem famC4_argOK (v : ℕ) : argOK (famC4 v) := by
  intro p hp
  simp only [famC4, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> · simp only []; omega

theorem famC4_srow (v : ℕ) : srow (famC4 v) ((famC4 v).length - 1) = 1 := by
  unfold srow
  rw [famC4_len]
  rw [show entry (famC4 v) 2 2 = 0 from rfl, if_neg (by omega)]
  rw [show entry (famC4 v) 1 2 = v + 1 from rfl, if_pos (by omega)]

theorem famC4_domT (v : ℕ) : domT (famC4 v) (2 * v + 1) := by
  refine ⟨?_, ?_⟩
  · unfold lev
    rw [famC4_len, show entry (famC4 v) 1 2 = v + 1 from rfl,
      show entry (famC4 v) 2 2 = 0 from rfl]
    omega
  · rw [famC4_srow, famC4_len]
    rintro ⟨j0, hj0, -⟩
    unfold nextR at hj0
    rw [if_neg (by decide), if_pos rfl] at hj0
    have hlt := hj0.2.2.1
    have hent := hj0.2.2.2.1
    rw [show entry (famC4 v) 1 2 = v + 1 from rfl] at hent
    have hj02 : j0 = 0 ∨ j0 = 1 := by omega
    rcases hj02 with rfl | rfl
    · rw [show entry (famC4 v) 1 0 = v + 1 from rfl] at hent; omega
    · rw [show entry (famC4 v) 1 1 = v + 1 from rfl] at hent; omega

theorem famC4_zero : famC4 0 = Rc4 := rfl

/-! Step 5: graft 閉包の底(y=[]): C3 ∈ Wg 0(R1317 の Wg 版、再利用可能)。 -/

theorem C3_Wg : ([((0,0,0):ℕ×ℕ×ℕ), ((1,1,1):ℕ×ℕ×ℕ), ((2,1,1):ℕ×ℕ×ℕ)] : TrioSeq) ∈ Wg 0 := by
  have h := Wg_of_starOK (starOK_farwords (v := 0) (WordsG_nil 0))
  simpa [GwS.rword, GwS.rcol, shiftr01] using h

end TRIO
