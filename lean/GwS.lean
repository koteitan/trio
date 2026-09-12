/-
GwS.lean: 生の列を字にした語 `rword` と、その `GoodFb` の閉包補題。

`SmallA` の `wordJ`（字は `Jk1` の木）を、字の中身が任意の列 `T`（深さ ≥ 1、Mono）
の語に置き換える。`GoodFb J` の欄は `J : ℕ → ℕ → TrioSeq` について定義されていて
`Jk1` に依存しないので、鍵の補題 `GoodFb_of_keyJ` はそのまま写せる。

    rcol a b T  := (a+1, b+1, 1) :: T↑(a+1)
    rword a b l := l.flatMap (rcol a b)

`Gw.Wg 2` の帰納で、字 `T` を語の最後に継げることを示すための部品。
-/
import Gw
import SmallA

namespace TRIO
namespace GwS

open Wset
open Small

/-! ## 生の字と語 -/

/-- 行 0 の祖先の鎖は、後ろに列を足しても変わらない。 -/
theorem rtg0_append_left {T U : TrioSeq} {k u : ℕ}
    (h : Relation.ReflTransGen (nextrel0 T) k u) (hu : u < T.length) :
    Relation.ReflTransGen (nextrel0 (T ++ U)) k u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hkb hbc ih =>
      have hbT : b < T.length := by have := hbc.2.2.1; omega
      refine Relation.ReflTransGen.tail (ih hbT) ?_
      obtain ⟨hb, hc, hbc', h0, hmin⟩ := hbc
      refine ⟨by simp; omega, by simp; omega, hbc', ?_, ?_⟩
      · rwa [Small.entry_append_left hbT, entry_append_left hu]
      · intro j hj
        rw [Small.entry_append_left hu, Small.entry_append_left (by omega)]
        exact hmin j hj

def rcol (a b : ℕ) (T : TrioSeq) : TrioSeq :=
  ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 (a + 1) 0 T

def rword (a b : ℕ) (l : List TrioSeq) : TrioSeq := l.flatMap (rcol a b)

/-- 行 1 ≥ 2 の列は、字の中に行 1 ≤ 1 の行 0 祖先を持つ（字の中身は頭の潰れで持ち上がらない）。 -/
def RiseOk (T : TrioSeq) : Prop :=
  ∀ u, u < T.length → 2 ≤ entry T 1 u →
    ∃ k, k < u ∧ Relation.ReflTransGen (nextrel0 T) k u ∧ entry T 1 k ≤ 1

/-- 字の中身の条件: 深さ ≥ 1、Mono、RiseOk。 -/
def RawOk (T : TrioSeq) : Prop := (∀ x ∈ T, 1 ≤ x.1) ∧ Mono T ∧ RiseOk T

def WOkR (l : List TrioSeq) : Prop := ∀ T ∈ l, RawOk T

theorem WOkR_append {l1 l2 : List TrioSeq} (h1 : WOkR l1) (h2 : WOkR l2) :
    WOkR (l1 ++ l2) := by
  intro T hT
  rcases List.mem_append.mp hT with h | h
  · exact h1 T h
  · exact h2 T h

theorem WOkR_singleton {T : TrioSeq} (hT : RawOk T) : WOkR [T] := by
  intro U hU
  rw [List.mem_singleton.mp hU]; exact hT

theorem rword_nil (a b : ℕ) : rword a b [] = [] := rfl

theorem rword_cons (a b : ℕ) (T : TrioSeq) (l : List TrioSeq) :
    rword a b (T :: l) = rcol a b T ++ rword a b l := by
  simp [rword]

theorem rword_append (a b : ℕ) (l1 l2 : List TrioSeq) :
    rword a b (l1 ++ l2) = rword a b l1 ++ rword a b l2 := by
  simp [rword, List.flatMap_append]

theorem rword_singleton (a b : ℕ) (T : TrioSeq) : rword a b [T] = rcol a b T := by
  simp [rword]

theorem rword_replicate (a b : ℕ) (T : TrioSeq) (n : ℕ) :
    rword a b (List.replicate n T) = (List.range n).flatMap (fun _ => rcol a b T) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ', rword_append, ih, rword_singleton, List.range_succ,
        List.flatMap_append]
      simp

theorem rcol_shift (a b s : ℕ) (T : TrioSeq) :
    shiftr01 s 0 (rcol a b T) = rcol (a + s) b T := by
  unfold rcol
  rw [show ((((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 (a + 1) 0 T))
      = [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] ++ shiftr01 (a + 1) 0 T from rfl,
    shiftr01_append0, shiftr01_add0]
  have e1 : shiftr01 s 0 [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]
      = [((a + s + 1, b + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp only [shiftr01, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    exact Prod.ext (by first | (dsimp only; omega) | dsimp only | omega | rfl) (Prod.ext (by first | (dsimp only; omega) | dsimp only | omega | rfl) rfl)
  rw [e1, show a + 1 + s = a + s + 1 by omega]
  rfl

theorem rword_shift (a b s : ℕ) (l : List TrioSeq) :
    shiftr01 s 0 (rword a b l) = rword (a + s) b l := by
  induction l with
  | nil => simp [rword, shiftr01]
  | cons T l ih =>
      rw [rword_cons, rword_cons, shiftr01_append0, rcol_shift, ih]

theorem rcol_ge (a b : ℕ) (T : TrioSeq) : ∀ x ∈ rcol a b T, a + 1 ≤ x.1 := by
  intro x hx
  simp only [rcol, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact le_rfl
  · simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, -, rfl⟩ := hx
    dsimp only; omega

theorem rword_ge (a b : ℕ) (l : List TrioSeq) : ∀ x ∈ rword a b l, a + 1 ≤ x.1 := by
  intro x hx
  simp only [rword, List.mem_flatMap] at hx
  obtain ⟨T, -, hx⟩ := hx
  exact rcol_ge a b T x hx

theorem rcol_mono {a b : ℕ} {T : TrioSeq} (hT : Mono T) : Mono (rcol a b T) := by
  intro x hx
  simp only [rcol, List.mem_cons] at hx
  rcases hx with rfl | hx
  · show (1 : ℕ) ≤ b + 1; omega
  · simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hT p hp
    dsimp only; omega

theorem rword_mono {a b : ℕ} {l : List TrioSeq} (hw : WOkR l) : Mono (rword a b l) := by
  intro x hx
  simp only [rword, List.mem_flatMap] at hx
  obtain ⟨T, hT, hx⟩ := hx
  exact rcol_mono (hw T hT).2.1 x hx

theorem rcol_ne (a b : ℕ) (T : TrioSeq) : rcol a b T ≠ [] := by simp [rcol]

theorem rcol_length (a b : ℕ) (T : TrioSeq) : (rcol a b T).length = T.length + 1 := by
  simp [rcol, shiftr01]

theorem entry_rcol_ge {a b : ℕ} {T : TrioSeq} (hT : ∀ x ∈ T, 1 ≤ x.1) :
    ∀ r, 1 ≤ r → r < (rcol a b T).length → a + 2 ≤ entry (rcol a b T) 0 r := by
  intro r hr1 hrl
  obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
  have hu : u < T.length := by rw [rcol_length] at hrl; omega
  have hmem : T.getD u (0, 0, 0) ∈ T := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]
    exact List.getElem_mem hu
  have h1 := hT _ hmem
  have hu' : u < (shiftr01 (a + 1) 0 T).length := by simpa [shiftr01] using hu
  show a + 2 ≤ ((rcol a b T).getD (u + 1) (0, 0, 0)).1
  rw [rcol, List.getD_cons_succ, shiftr01_getD hu]
  dsimp only
  omega

theorem MidD_rword (a v : ℕ) (ha : 1 ≤ a) (hv : 1 ≤ v) {l : List TrioSeq} (hw : WOkR l) :
    MidD (a + 1) (((a, v, 0) : ℕ × ℕ × ℕ) :: rword a v l) := by
  have h := MidD_append (MidD_col a v ha hv) (N := rword a v l) (rword_ge a v l)
    (rword_mono hw)
  simpa using h

/-! ## 鍵の補題（`GoodFb_of_keyJ` の写し） -/

theorem GoodFb_of_keyR {l : List TrioSeq} (hw : WOkR l)
    {new : ℕ → List TrioSeq}
    (hnew : ∀ n, 1 ≤ n → GoodFb (fun a b => rword a b (new n)))
    (key : ∀ (Z : TrioSeq) (a b : ℕ), 1 ≤ b →
      (∀ n, 1 ≤ n → Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: rword a b (new n)) ∈ W 0) →
      Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: rword a b l) ∈ W 0) :
    GoodFb (fun a b => rword a b l) where
  ge := fun a b => rword_ge a b l
  mono := fun a b => rword_mono hw
  shift := fun a b s => rword_shift a b s l
  pu := by
    intro y c hy
    refine ⟨fun x hx => by have := rword_ge (c + 1) (y + 1) l x hx; omega, rword_mono hw, ?_⟩
    intro E hE t Z hZ
    rw [rword_shift]
    have h := key Z (c + 1 + t) (y + 1) (by omega) (fun n hn => by
      have hP : PU y (c + 1 + t) (Z ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++
          rword (c + 1 + t) (y + 1) (new n))) :=
        ⟨E, c + t, Z, _, hE, by omega, hZ, by rw [show c + t + 1 = c + 1 + t from by omega],
          (hnew n hn).pu y (c + t) hy⟩
      simpa using ((BaseOk_PU y).aok _ _ hP).mem)
    simpa using h
  pk := by
    intro c E hI
    refine ⟨fun x hx => by have := rword_ge (c + 1) 2 l x hx; omega, rword_mono hw, ?_⟩
    intro j t X hX
    rw [rword_shift]
    have h := key X (c + 1 + t) 2 (by omega) (fun n hn => by
      have hP : PkGA (c + 1 + t) (X ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++
          rword (c + 1 + t) 2 (new n))) :=
        ⟨E, hI, j, c + t, X, _, by omega, hX, by rw [show c + t + 1 = c + 1 + t from by omega],
          (hnew n hn).pk (c + t)⟩
      simpa using (PkGA_Aok hP).mem)
    simpa using h
  seg := by
    intro h
    have hmid : MidD (h + 2) (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: rword (h + 1) 1 l) := by
      have h1 := MidD_rword (h + 1) 1 (by omega) (by omega) hw
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    refine ⟨hmid, by simp [entry], ?_⟩
    intro P hP s A' hA'
    rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: rword (h + 1) 1 l
        = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ rword (h + 1) 1 l from rfl,
      shiftr01_append0, shift_col, rword_shift]
    have hk := key A' (h + 1 + s) 1 (by omega) (fun n hn => by
      have hR : RunA 0 (h + s + 1) (A' ++ (((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          rword (h + s + 1) 1 (new n))) :=
        ⟨h + s, A', _, rfl, rfl, ⟨P, hP, hA'⟩, (hnew n hn).seg (h + s)⟩
      have := ((BaseOk_RunA 0).aok _ _ hR).mem
      simpa [show h + s + 1 = h + 1 + s from by omega] using this)
    simpa using hk

theorem GoodFb_rword_nil : GoodFb (fun a b => rword a b ([] : List TrioSeq)) := by
  have e : (fun a b => rword a b ([] : List TrioSeq)) = (fun a b => wordJ a b []) := by
    funext a b; rfl
  rw [e]
  exact GoodFb_wordJ_nil

/-- 良い語 `J` の上に 1 の列を継いだ行は `W 0`（`rowJ_mem_genF` の一般形）。 -/
theorem row_mem_of_GoodFb {A : TrioSeq} (hA : Aok A) {J : ℕ → ℕ → TrioSeq}
    (hG : GoodFb J) : A ++ (((1, 1, 0) : ℕ × ℕ × ℕ) :: J 1 1) ∈ W 0 := by
  have h := (hG.seg 0).reapp P0 BaseOk_zero 0 A (LwB_of_base ⟨hA, rfl⟩)
  simpa using h

/-! ## 字の繰り返し・字の中の展開・平らな最上位列 -/

theorem GoodFb_repR {l : List TrioSeq} (hw : WOkR l) {T : TrioSeq} (hT : RawOk T)
    (hstep : ∀ l' : List TrioSeq, WOkR l' → GoodFb (fun a b => rword a b l') →
      GoodFb (fun a b => rword a b (l' ++ [T])))
    (hG : GoodFb (fun a b => rword a b l)) :
    ∀ n : ℕ, GoodFb (fun a b => rword a b (l ++ List.replicate n T))
  | 0 => by simpa using hG
  | (n + 1) => by
      have hwn : WOkR (l ++ List.replicate n T) := by
        refine WOkR_append hw ?_
        intro U hU
        rw [List.eq_of_mem_replicate hU]; exact hT
      have h := hstep (l ++ List.replicate n T) hwn (GoodFb_repR hw hT hstep hG n)
      have e : l ++ List.replicate n T ++ [T] = l ++ List.replicate (n + 1) T := by
        rw [List.append_assoc, ← List.replicate_succ']
      rwa [e] at h

/-- (G1) 字の末尾の親が字の中にあれば、展開の字で閉じる。 -/
theorem GoodFb_snoc_operR {l : List TrioSeq} (hw : WOkR l) {T : TrioSeq} (hT : RawOk T)
    (hlen : 2 ≤ T.length) (hp : hasParent T (srow T (T.length - 1)) (T.length - 1))
    (hIH : ∀ n, 1 ≤ n → GoodFb (fun a b => rword a b (l ++ [T⟦n⟧]))) :
    GoodFb (fun a b => rword a b (l ++ [T])) := by
  refine GoodFb_of_keyR (WOkR_append hw (WOkR_singleton hT)) hIH ?_
  intro Z0 a b hb hn
  have e : ∀ U : TrioSeq, Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: rword a b (l ++ [U]))
      = (Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: rword a b l) ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])
        ++ shiftr01 (a + 1) 0 U := by
    intro U
    rw [rword_append, rword_singleton]
    simp [rcol, List.append_assoc]
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn'
  rw [e T, oper_shift _ T (a + 1) n hlen hp, ← e (T⟦n⟧)]
  exact hn n hn'

/-- 字の中身の最後が最上位の平らな列 `(1,0,0)` なら、字 `T` が `n` 個に複製される。 -/
theorem GoodFb_snoc_dupR {l : List TrioSeq} (hw : WOkR l) {T : TrioSeq} (hT : RawOk T)
    (hIH : ∀ n, 1 ≤ n → GoodFb (fun a b => rword a b (l ++ List.replicate n T))) :
    GoodFb (fun a b => rword a b (l ++ [T ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]])) := by
  have hT' : RawOk (T ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
    · rcases List.mem_append.mp hx with h | h
      · exact hT.1 x h
      · rw [List.mem_singleton.mp h]
    · rcases List.mem_append.mp hx with h | h
      · exact hT.2.1 x h
      · rw [List.mem_singleton.mp h]
    · intro u hu h2
      rcases Nat.lt_or_ge u T.length with huT | huT
      · rw [Small.entry_append_left huT] at h2
        obtain ⟨k, hku, hch, hk1⟩ := hT.2.2 u huT h2
        refine ⟨k, hku, rtg0_append_left hch huT, ?_⟩
        rwa [Small.entry_append_left (by omega)]
      · have hu' : u = T.length := by simp at hu; omega
        subst hu'
        rw [show T.length = T.length + 0 from rfl, entry_append_right] at h2
        simp [entry] at h2
  refine GoodFb_of_keyR (WOkR_append hw (WOkR_singleton hT')) hIH ?_
  intro Z0 a b hb hn
  have hhead : entry (rcol a b T) 0 0 < a + 2 := by simp [rcol, entry]
  have h := flat_mem'' (Y0 := Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: rword a b l))
    (M := rcol a b T) (d := a + 2) (rcol_ne a b T) hhead (entry_rcol_ge hT.1)
    (fun n => by
      match n with
      | 0 =>
          have h1 := hn 1 (le_refl 1)
          rw [rword_append, rword_replicate] at h1
          simp only [List.range_one, List.flatMap_cons, List.flatMap_nil,
            List.append_nil] at h1
          have h2 := W_take (by
            rw [show Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: (rword a b l ++ rcol a b T))
                = (Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: rword a b l)) ++ rcol a b T from by
                  simp [List.append_assoc]] at h1
            exact h1) (Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: rword a b l)).length
          rw [List.take_left] at h2
          simpa using h2
      | (n + 1) =>
          have h1 := hn (n + 1) (by omega)
          rw [rword_append, rword_replicate] at h1
          simpa [List.append_assoc] using h1)
  have e : rcol a b (T ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
      = rcol a b T ++ [((a + 2, 0, 0) : ℕ × ℕ × ℕ)] := by
    have e1 : shiftr01 (a + 1) 0 [((1, 0, 0) : ℕ × ℕ × ℕ)]
        = [((a + 2, 0, 0) : ℕ × ℕ × ℕ)] := by
      simp only [shiftr01, List.map_cons, List.map_nil, List.cons.injEq, and_true]
      exact Prod.ext (by first | (dsimp only; omega) | dsimp only | omega | rfl) (Prod.ext (by first | (dsimp only; omega) | dsimp only | omega | rfl) rfl)
    simp only [rcol, shiftr01_append0, e1, List.cons_append]
  rw [rword_append, rword_singleton, e]
  simpa [List.append_assoc] using h

#print axioms GoodFb_of_keyR
#print axioms GoodFb_snoc_operR
#print axioms GoodFb_snoc_dupR

end GwS
end TRIO
