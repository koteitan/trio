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

/-! ## 空の字（頭の潰れ）: 字の中身は持ち上がらない

`SmallA` の `rise_wordJ` / `oper_z1wJ` / `GoodFb_snoczJ` の写し。字の木の構造
（`not_le1_jk1`）の代わりに、一般補題 `not_le1_blocked` と `RiseOk` を使う。 -/

/-- 行 1 の子孫の鎖は、途中に行 1 が根以下の行 0 祖先があると張れない。 -/
theorem not_le1_blocked {M : TrioSeq} {p : ℕ} :
    ∀ {c : ℕ}, le1 M p c → ∀ k, p < k → le0 M k c → entry M 1 k ≤ entry M 1 p → False := by
  intro c hle
  obtain ⟨hpl, hcl, hch⟩ := hle
  revert hcl
  induction hch with
  | refl =>
      intro _ k hpk hkc _
      have := le0_le' hkc
      omega
  | @tail e c' hpe hec ih =>
      intro _ k hpk hkc hk1
      obtain ⟨hel, hc'l, hlt, h1lt, hle0, hmin⟩ := hec
      have hpe1 : entry M 1 p ≤ entry M 1 e := le1_row1_le hpe
      rcases lt_or_ge e k with hek | hke
      · have := hmin k ⟨hek, hkc⟩
        omega
      · rcases eq_or_lt_of_le hke with hke0 | hke'
        · subst hke0
          have hpk' : p ≠ k := by omega
          have := le1_row1_lt (⟨hpl, hel, hpe⟩ : le1 M p k) hpk'
          omega
        · exact ih hel k hpk (le0_of_le0_le0 hkc hle0 hke') hk1

/-- 行 0 の祖先の鎖を、一様にずらした区間へ運ぶ。 -/
theorem rtg0_block {M T : TrioSeq} {q d : ℕ} (hlen : q + T.length ≤ M.length)
    (hent : ∀ t, t < T.length → entry M 0 (q + t) = entry T 0 t + d) :
    ∀ {k u : ℕ}, Relation.ReflTransGen (nextrel0 T) k u → u < T.length →
      Relation.ReflTransGen (nextrel0 M) (q + k) (q + u) := by
  intro k u h
  induction h with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @tail b c hkb hbc ih =>
      intro hcT
      obtain ⟨hb, hc, hbc', h0, hmin⟩ := hbc
      refine Relation.ReflTransGen.tail (ih hb) ⟨by omega, by omega, by omega, ?_, ?_⟩
      · rw [hent b hb, hent c hcT]; omega
      · intro j hj
        obtain ⟨t, rfl⟩ : ∃ t, j = q + t := ⟨j - q, by omega⟩
        have ht : t < T.length := by omega
        rw [hent c hcT, hent t ht]
        have := hmin t ⟨by omega, by omega⟩
        omega

def MzR (Y0 : TrioSeq) (a b : ℕ) (l : List TrioSeq) : TrioSeq :=
  Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: rword a b l ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])

theorem MzR_length (Y0 : TrioSeq) (a b : ℕ) (l : List TrioSeq) :
    (MzR Y0 a b l).length = Y0.length + 1 + (rword a b l).length + 1 := by
  simp [MzR]; omega

theorem entry_MzR_p (Y0 : TrioSeq) (a b : ℕ) (l : List TrioSeq) (r : ℕ) :
    entry (MzR Y0 a b l) r Y0.length = entry [((a, b, 0) : ℕ × ℕ × ℕ)] r 0 := by
  rw [MzR, entry_append_at]
  simp [entry]

theorem entry_MzR_word (Y0 : TrioSeq) (a b : ℕ) (l : List TrioSeq) (r i : ℕ)
    (hi : i < (rword a b l).length) :
    entry (MzR Y0 a b l) r (Y0.length + 1 + i) = entry (rword a b l) r i := by
  have e : MzR Y0 a b l = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)]) ++
      (rword a b l ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) := by
    simp [MzR]
  rw [e, show Y0.length + 1 + i = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)]).length + i from by
      simp only [List.length_append, List.length_singleton],
    entry_append_right, Small.entry_append_left hi]

theorem entry_rword_pos (Y0 : TrioSeq) (a b : ℕ) (l1 l3 : List TrioSeq) (T : TrioSeq)
    (r t : ℕ) (ht : t < (rcol a b T).length) :
    entry (MzR Y0 a b (l1 ++ T :: l3)) r (Y0.length + 1 + (rword a b l1).length + t)
      = entry (rcol a b T) r t := by
  have e : MzR Y0 a b (l1 ++ T :: l3)
      = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)] ++ rword a b l1) ++
        (rcol a b T ++ (rword a b l3 ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])) := by
    simp [MzR, rword_append, rword_cons, List.append_assoc]
  rw [e, show Y0.length + 1 + (rword a b l1).length + t
      = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)] ++ rword a b l1).length + t from by
        simp only [List.length_append, List.length_singleton],
    entry_append_right, Small.entry_append_left ht]

theorem entry_rword_ge (a b : ℕ) (l : List TrioSeq) {i : ℕ} (hi : i < (rword a b l).length) :
    a + 1 ≤ entry (rword a b l) 0 i := by
  have hmem : (rword a b l).getD i (0, 0, 0) ∈ rword a b l := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  exact rword_ge a b l _ hmem

/-- 字の頭は記録 `(a,b,0)` の行 1 の子。 -/
theorem le1_zposR (Y0 : TrioSeq) (a b : ℕ) (l1 l3 : List TrioSeq) (T : TrioSeq) :
    le1 (MzR Y0 a b (l1 ++ T :: l3)) Y0.length (Y0.length + 1 + (rword a b l1).length) := by
  set M := MzR Y0 a b (l1 ++ T :: l3) with hM
  set q := Y0.length + 1 + (rword a b l1).length with hq
  have hlenw : (rword a b (l1 ++ T :: l3)).length
      = (rword a b l1).length + (rcol a b T).length + (rword a b l3).length := by
    rw [rword_append, rword_cons, List.length_append, List.length_append]
    omega
  have hlen : M.length = Y0.length + 1 + (rword a b (l1 ++ T :: l3)).length + 1 := by
    rw [hM, MzR_length]
  have hcl : 0 < (rcol a b T).length := by rw [rcol_length]; omega
  have hql : q < M.length := by omega
  have e0p : entry M 0 Y0.length = a := by rw [hM, entry_MzR_p]; simp [entry]
  have e1p : entry M 1 Y0.length = b := by rw [hM, entry_MzR_p]; simp [entry]
  have eq0 : entry M 0 q = a + 1 := by
    have h := entry_rword_pos Y0 a b l1 l3 T 0 0 hcl
    rw [Nat.add_zero] at h
    rw [hM, hq, h]; simp [rcol, entry]
  have eq1 : entry M 1 q = b + 1 := by
    have h := entry_rword_pos Y0 a b l1 l3 T 1 0 hcl
    rw [Nat.add_zero] at h
    rw [hM, hq, h]; simp [rcol, entry]
  have hge : ∀ j', Y0.length < j' → j' ≤ q → a + 1 ≤ entry M 0 j' := by
    intro j' h1 h2
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < (rword a b (l1 ++ T :: l3)).length ∧ j' = Y0.length + 1 + i :=
      ⟨j' - (Y0.length + 1), by omega, by omega⟩
    rw [hM, entry_MzR_word Y0 a b _ 0 i hi]
    exact entry_rword_ge a b _ hi
  have hl0 : le0 M Y0.length q := le0_of_between e0p q (by omega) hql hge
  refine ⟨by omega, hql, Relation.ReflTransGen.single ?_⟩
  refine ⟨by omega, hql, by omega, by rw [e1p, eq1]; omega, hl0, ?_⟩
  intro j hj
  have := le0_eq_of_min hj.1 hj.2 eq0 (fun j'' h1 h2 => hge j'' h1 (by omega))
  subst this; exact le_rfl

/-- 字の中身の列は記録 `(a,b,0)` の行 1 の子孫ではない（`RiseOk`）。 -/
theorem not_le1_treeR (Y0 : TrioSeq) (a b : ℕ) (hb : 1 ≤ b) (l1 l3 : List TrioSeq)
    {T : TrioSeq} (hT : RawOk T) (u : ℕ) (hu : u < T.length) :
    ¬ le1 (MzR Y0 a b (l1 ++ T :: l3)) Y0.length
      (Y0.length + 1 + (rword a b l1).length + (u + 1)) := by
  set M := MzR Y0 a b (l1 ++ T :: l3) with hM
  have hlenw : (rword a b (l1 ++ T :: l3)).length
      = (rword a b l1).length + (rcol a b T).length + (rword a b l3).length := by
    rw [rword_append, rword_cons, List.length_append, List.length_append]
    omega
  have hlen : M.length = Y0.length + 1 + (rword a b (l1 ++ T :: l3)).length + 1 := by
    rw [hM, MzR_length]
  have hcl := rcol_length a b T
  have hent : ∀ (r t : ℕ), t < T.length →
      entry M r (Y0.length + 1 + (rword a b l1).length + 1 + t)
        = entry (shiftr01 (a + 1) 0 T) r t := by
    intro r t ht
    have h := entry_rword_pos Y0 a b l1 l3 T r (t + 1) (by omega)
    rw [rcol, entry_cons_succ] at h
    rw [hM, show Y0.length + 1 + (rword a b l1).length + 1 + t
      = Y0.length + 1 + (rword a b l1).length + (t + 1) from by omega]
    exact h
  have hp1 : entry M 1 Y0.length = b := by rw [hM, entry_MzR_p]; simp [entry]
  intro hle
  have hlt := le1_row1_lt hle (by omega)
  rw [show Y0.length + 1 + (rword a b l1).length + (u + 1)
      = Y0.length + 1 + (rword a b l1).length + 1 + u from by omega] at hle hlt
  rw [hent 1 u hu, entry1_shiftr01, hp1] at hlt
  obtain ⟨k, hku, hch, hk1⟩ := hT.2.2 u hu (by omega)
  have hkc : le0 M (Y0.length + 1 + (rword a b l1).length + 1 + k)
      (Y0.length + 1 + (rword a b l1).length + 1 + u) := by
    refine ⟨by omega, by omega, rtg0_block (d := a + 1) (by omega) (fun t ht => ?_) hch hu⟩
    rw [hent 0 t ht, entry0_shiftr01 ht]
  refine not_le1_blocked hle _ (by omega) hkc ?_
  rw [hent 1 k (by omega), entry1_shiftr01, hp1]; omega

theorem entry_rcol_zero (a b : ℕ) (T : TrioSeq) (r : ℕ) :
    entry (rcol a b T) r 0 = entry [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] r 0 := by
  simp [rcol, entry]

theorem entry_rcol_succ (a b : ℕ) (T : TrioSeq) (r t : ℕ) :
    entry (rcol a b T) r (t + 1) = entry (shiftr01 (a + 1) 0 T) r t := by
  simp [rcol, entry]

theorem rise_rcol (a b k : ℕ) (T : TrioSeq) (P : ℕ → Prop) [DecidablePred P]
    (hP0 : P 0) (hP : ∀ t, 1 ≤ t → t < (rcol a b T).length → ¬ P t) :
    (List.range (rcol a b T).length).map (fun t =>
      ((entry (rcol a b T) 0 t + k, entry (rcol a b T) 1 t + (if P t then k else 0),
        entry (rcol a b T) 2 t) : ℕ × ℕ × ℕ)) = rcol (a + k) (b + k) T := by
  apply List.ext_getElem
  · simp [rcol_length]
  · intro t h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have h1' : t < (rcol a b T).length := by simpa using h1
    clear h1
    have h1 := h1'
    cases t with
    | zero =>
        rw [entry_rcol_zero, entry_rcol_zero, entry_rcol_zero, if_pos hP0]
        simp [rcol, entry]
        try omega
    | succ u =>
        have hu : u < T.length := by rw [rcol_length] at h1; omega
        rw [entry_rcol_succ, entry_rcol_succ, entry_rcol_succ,
          if_neg (hP (u + 1) (by omega) h1), entry0_shiftr01 hu, entry1_shiftr01,
          entry2_shiftr01]
        simp [rcol, shiftr01, entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]
        try omega

open Classical in
/-- 語全体の上昇（接頭辞 `l1` を蓄積する帰納法）。 -/
theorem rise_rword (Y0 : TrioSeq) (a b k : ℕ) (hb : 1 ≤ b) {l : List TrioSeq} (hw : WOkR l) :
    ∀ (l2 l1 l3 : List TrioSeq), l = l1 ++ l2 ++ l3 →
      (List.range (rword a b l2).length).map (fun i =>
        ((entry (rword a b l2) 0 i + k, entry (rword a b l2) 1 i +
          (if le1 (MzR Y0 a b l) Y0.length (Y0.length + 1 + (rword a b l1).length + i)
            then k else 0), entry (rword a b l2) 2 i) : ℕ × ℕ × ℕ))
      = rword (a + k) (b + k) l2
  | [], _, _, _ => by simp [rword]
  | (T :: l2), l1, l3, hl => by
      have hl' : l = (l1 ++ [T]) ++ l2 ++ l3 := by rw [hl]; simp
      have hl'' : l = l1 ++ T :: (l2 ++ l3) := by rw [hl]; simp
      have hT : RawOk T := hw T (by rw [hl]; simp)
      have ih := rise_rword Y0 a b k hb hw l2 (l1 ++ [T]) l3 hl'
      rw [rword_cons, rword_cons, List.length_append, List.range_add, List.map_append,
        List.map_map]
      congr 1
      · rw [← rise_rcol a b k T (fun t => le1 (MzR Y0 a b l) Y0.length
            (Y0.length + 1 + (rword a b l1).length + t))
            (by rw [hl'']; simpa using le1_zposR Y0 a b l1 (l2 ++ l3) T)
            (by intro t ht1 ht
                obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
                rw [hl'']
                refine not_le1_treeR Y0 a b hb l1 (l2 ++ l3) hT u ?_
                rw [rcol_length] at ht; omega)]
        apply List.map_congr_left
        intro t ht
        rw [List.mem_range] at ht
        rw [Small.entry_append_left ht, Small.entry_append_left ht,
          Small.entry_append_left ht]
      · rw [← ih]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp]
        rw [entry_append_right, entry_append_right, entry_append_right, rword_append,
          rword_singleton, List.length_append,
          show Y0.length + 1 + (rword a b l1).length + ((rcol a b T).length + i)
            = Y0.length + 1 + ((rword a b l1).length + (rcol a b T).length) + i from by omega]

open Classical in
/-- ★ 生の字の語の上の z の列の展開: 記録と語の対角の塔。 -/
theorem oper_z1wR (Y0 : TrioSeq) (a b : ℕ) (hb : 1 ≤ b) {l : List TrioSeq}
    (hw : WOkR l) (n : ℕ) :
    (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: rword a b l ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧
      = Y0 ++ Dzf (fun a b => rword a b l) a b n := by
  rw [oper_z1_mask Y0 a b (rword a b l) (rword_ge a b l) n]
  congr 1
  apply List.flatMap_congr
  intro k _
  congr 1
  have := rise_rword Y0 a b k hb hw l [] [] (by simp)
  simpa [rword, MzR] using this

theorem z1wR_mem {Y0 : TrioSeq} {a b : ℕ} (hb : 1 ≤ b) {l : List TrioSeq} (hw : WOkR l)
    (htw : ∀ n, Y0 ++ Dzf (fun a b => rword a b l) a b n ∈ W 0) :
    Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: rword a b l ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])
      ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_z1wR Y0 a b hb hw]
  exact htw n

theorem rcol_nil (a b : ℕ) : rcol a b [] = [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] := by
  simp [rcol, shiftr01]

theorem RawOk_nil : RawOk [] :=
  ⟨by simp, by simp [Mono], fun u hu => by simp at hu⟩

/-- (G3) 語の最後に空の字を継ぐ。 -/
theorem GoodFb_snoczR {l : List TrioSeq} (hw : WOkR l)
    (hG : GoodFb (fun a b => rword a b l)) :
    GoodFb (fun a b => rword a b (l ++ [[]])) where
  ge := fun a b => rword_ge a b _
  mono := fun a b => rword_mono (WOkR_append hw (WOkR_singleton RawOk_nil))
  shift := fun a b s => rword_shift a b s _
  pu := by
    intro y c hy
    refine ⟨fun x hx => by have := rword_ge (c + 1) (y + 1) _ x hx; omega,
      rword_mono (WOkR_append hw (WOkR_singleton RawOk_nil)), ?_⟩
    intro E hE t Z hZ
    rw [rword_shift, rword_append, rword_singleton, rcol_nil]
    have h := z1wR_mem (Y0 := Z) (a := c + 1 + t) (b := y + 1) (by omega) hw
      (fun n => by
        have := Dzf_W hG hy hE (c := c + t) (by simpa using hZ) n
        simpa [show c + t + 1 = c + 1 + t from by omega] using this)
    simpa [List.append_assoc] using h
  pk := by
    intro c E hI
    refine ⟨fun x hx => by have := rword_ge (c + 1) 2 _ x hx; omega,
      rword_mono (WOkR_append hw (WOkR_singleton RawOk_nil)), ?_⟩
    intro j t X hX
    rw [rword_shift, rword_append, rword_singleton, rcol_nil]
    have h := z1wR_mem (Y0 := X) (a := c + 1 + t) (b := 2) (by omega) hw
      (fun n => by
        have := Dzf_W_RunG hG hI (c := c + t) hX n
        simpa [show c + t + 1 = c + 1 + t from by omega] using this)
    simpa [List.append_assoc] using h
  seg := by
    intro h
    have hmid : MidD (h + 2) (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: rword (h + 1) 1 (l ++ [[]])) := by
      have h1 := MidD_rword (h + 1) 1 (by omega) (by omega)
        (l := l ++ [[]]) (WOkR_append hw (WOkR_singleton RawOk_nil))
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    refine ⟨hmid, by simp [entry], ?_⟩
    intro P hP s A' hA'
    rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: rword (h + 1) 1 (l ++ [[]])
        = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ rword (h + 1) 1 (l ++ [[]]) from rfl,
      shiftr01_append0, shift_col, rword_shift, rword_append, rword_singleton, rcol_nil]
    have hz := z1wR_mem (Y0 := A') (a := h + 1 + s) (b := 1) (by omega) hw
      (fun n => by
        have := Dzf_W_LwA hG (h := h + s) ⟨P, hP, hA'⟩ n
        simpa [show h + s + 1 = h + 1 + s from by omega] using this)
    simpa [List.append_assoc] using hz

#print axioms GoodFb_snoczR

end GwS
end TRIO
