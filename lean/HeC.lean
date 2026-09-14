/-
HeC.lean: 道の集合の作り方（延長と段 l での閉包）と、その性質（追記577）。

    ext1 P l := {Q ++ [(us, l)] | Q ∈ P, us ∈ Gd P}
    clE l B 0 = B、clE l B (i+1) = clE l B i ∪ ext1 (clE l B i) l、clS l B := ⋃_i clE l B i
    PNil := {[]}、P0 := clS 0 PNil（F のタイの子の位置と、そこからタイで下る位置）
    chS0 P := clS 0 (ext1 P 0)（段 0 のタイの子の位置）、chU P l := ext1 P l（段 l の節点の子の位置）

- PSOK（生の条件・埋め込み・段の持ち上げ）は延長と閉包で保たれる。
- PSDec: 空でない道は、親の集合 P' の道に P' で良い成分を足した形で、P' の全ての良い延長を含む（flat の複製で使う）。
- clS_closed: clS l B は段 l の延長で閉じる（Ext (clS l B) l (clS l B)。上の葉の塔で使う）。
- LastL: 集合の道の最後の成分の段（空の道は F のタイで段 0）。
-/
import HeB

namespace TRIO
namespace HeC

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HeB

/-! ## 最後の段 -/

def lastL : Path → ℕ
  | [] => 0
  | [p] => p.2
  | _ :: q => lastL q

theorem lastL_snoc : ∀ (Q : Path) (us : List UT) (l : ℕ), lastL (Q ++ [(us, l)]) = l
  | [], _, _ => rfl
  | [p], us, l => rfl
  | p :: p2 :: q, us, l => by
      rw [List.cons_append, List.cons_append]
      have := lastL_snoc (p2 :: q) us l
      rw [List.cons_append] at this
      simpa [lastL] using this

def LastL (P : PS) (p : ℕ) : Prop := ∀ C o f u Q, P C o f u Q → lastL Q = p

/-! ## 作り方 -/

def ext1 (P : PS) (l : ℕ) : PS := fun C o f u Q =>
  ∃ Q' us, Q = Q' ++ [(us, l)] ∧ P C o f u Q' ∧ Gd P C o f u us

def clE (l : ℕ) (B : PS) : ℕ → PS
  | 0 => B
  | i + 1 => fun C o f u Q => clE l B i C o f u Q ∨ ext1 (clE l B i) l C o f u Q

def clS (l : ℕ) (B : PS) : PS := fun C o f u Q => ∃ i, clE l B i C o f u Q

def PNil : PS := fun _ _ _ _ Q => Q = []

def P0 : PS := clS 0 PNil

def chS0 (P : PS) : PS := clS 0 (ext1 P 0)

def chU (P : PS) (l : ℕ) : PS := ext1 P l

/-! ## 包含 -/

theorem clE_le (l : ℕ) (B : PS) : ∀ {i j : ℕ}, i ≤ j → ∀ C o f u Q, clE l B i C o f u Q → clE l B j C o f u Q
  | i, 0, hij, C, o, f, u, Q, h => by
      have : i = 0 := by omega
      subst this; exact h
  | i, j + 1, hij, C, o, f, u, Q, h => by
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact Or.inl (clE_le l B (show i ≤ j by omega) C o f u Q h)
      · have : i = j + 1 := by omega
        subst this; exact h

theorem clE_sub (l : ℕ) (B : PS) (i : ℕ) : ∀ C o f u Q, clE l B i C o f u Q → clS l B C o f u Q :=
  fun _ _ _ _ _ h => ⟨i, h⟩

theorem B_sub_clS (l : ℕ) (B : PS) : ∀ C o f u Q, B C o f u Q → clS l B C o f u Q :=
  fun _ _ _ _ _ h => ⟨0, h⟩

theorem Ext_ext1 (P : PS) (l : ℕ) : Ext P l (ext1 P l) :=
  fun _ _ _ _ Q us hQ hus => ⟨Q, us, rfl, hQ, hus⟩

theorem Ext_mono {P Pc Pc' : PS} {l : ℕ} (h : Ext P l Pc) (hsub : ∀ C o f u Q, Pc C o f u Q → Pc' C o f u Q) :
    Ext P l Pc' := fun C o f u Q us hQ hus => hsub _ _ _ _ _ (h C o f u Q us hQ hus)

/-- ★ 閉包は段 l の延長で閉じる。 -/
theorem clS_closed (l : ℕ) (B : PS) : Ext (clS l B) l (clS l B) := by
  intro C o f u Q us hQ hus
  obtain ⟨i, hi⟩ := hQ
  refine ⟨i + 1, Or.inr ⟨Q, us, rfl, hi, ?_⟩⟩
  exact Gd_mono (clE_sub l B i) hus

theorem Ext_clS_base (P : PS) (l : ℕ) : Ext P l (clS l (ext1 P l)) :=
  Ext_mono (Ext_ext1 P l) (B_sub_clS l _)

theorem Ext_chS0 (P : PS) : Ext P 0 (chS0 P) := Ext_clS_base P 0

theorem Ext_chU (P : PS) (l : ℕ) : Ext P l (chU P l) := Ext_ext1 P l

theorem PNil_P0 : ∀ C o f u, P0 C o f u [] := fun _ _ _ _ => ⟨0, rfl⟩

/-! ## PSOK -/

theorem PSOK_ext1 {P : PS} (hP : PSOK P) (l : ℕ) : PSOK (ext1 P l) where
  raw := by
    rintro C o f u Q ⟨Q', us, rfl, hQ', hus⟩ p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hP.raw _ _ _ _ _ hQ' p hp
    · simp at hp; subst hp; exact hus.1
  emb := by
    rintro C o f u Q ⟨Q', us, rfl, hQ', hus⟩ G S o2 f2 hE
    refine ⟨mapQ (relTs C f G u) Q', relTs C f G u us, mapQ_snoc _ _ _ _, hP.emb _ _ _ _ _ hQ' _ _ _ _ hE, ?_⟩
    exact Gd_emb hus hE
  lift := by
    rintro C o f u Q ⟨Q', us, rfl, hQ', hus⟩ u' hu
    exact ⟨mapQ (mlTs u (u' - u)) Q', mlTs u (u' - u) us, mapQ_snoc _ _ _ _,
      hP.lift _ _ _ _ _ hQ' u' hu, Gd_lift hus hu⟩

theorem PSOK_clE {B : PS} (hB : PSOK B) (l : ℕ) : ∀ i, PSOK (clE l B i)
  | 0 => hB
  | i + 1 => by
      have ih := PSOK_clE hB l i
      have hx := PSOK_ext1 ih l
      refine ⟨fun C o f u Q h => ?_, fun C o f u Q h => ?_, fun C o f u Q h => ?_⟩
      · rcases h with h | h
        · exact ih.raw _ _ _ _ _ h
        · exact hx.raw _ _ _ _ _ h
      · intro G S o2 f2 hE
        rcases h with h | h
        · exact Or.inl (ih.emb _ _ _ _ _ h _ _ _ _ hE)
        · exact Or.inr (hx.emb _ _ _ _ _ h _ _ _ _ hE)
      · intro u' hu
        rcases h with h | h
        · exact Or.inl (ih.lift _ _ _ _ _ h u' hu)
        · exact Or.inr (hx.lift _ _ _ _ _ h u' hu)

theorem PSOK_clS {B : PS} (hB : PSOK B) (l : ℕ) : PSOK (clS l B) where
  raw := fun C o f u Q ⟨i, h⟩ => (PSOK_clE hB l i).raw _ _ _ _ _ h
  emb := fun C o f u Q ⟨i, h⟩ G S o2 f2 hE => ⟨i, (PSOK_clE hB l i).emb _ _ _ _ _ h _ _ _ _ hE⟩
  lift := fun C o f u Q ⟨i, h⟩ u' hu => ⟨i, (PSOK_clE hB l i).lift _ _ _ _ _ h u' hu⟩

theorem PSOK_PNil : PSOK PNil where
  raw := by intro C o f u Q h p hp; simp only [PNil] at h; subst h; simp at hp
  emb := by intro C o f u Q h G S o2 f2 _; simp only [PNil] at h ⊢; subst h; rfl
  lift := by intro C o f u Q h u' _; simp only [PNil] at h ⊢; subst h; rfl

theorem PSOK_P0 : PSOK P0 := PSOK_clS PSOK_PNil 0

theorem PSOK_chS0 {P : PS} (hP : PSOK P) : PSOK (chS0 P) := PSOK_clS (PSOK_ext1 hP 0) 0

theorem PSOK_chU {P : PS} (hP : PSOK P) (l : ℕ) : PSOK (chU P l) := PSOK_ext1 hP l

/-! ## 分解 -/

/-- 空でない道は、親の集合 P' の道に P' で良い成分を段 l で足した形で、P' の良い延長を全て含む。 -/
def PSDec (P : PS) : Prop :=
  ∀ C o f u Q, P C o f u Q → Q = [] ∨
    ∃ (P' : PS) (Q' : Path) (us0 : List UT) (l : ℕ),
      Q = Q' ++ [(us0, l)] ∧ P' C o f u Q' ∧ Gd P' C o f u us0 ∧ Ext P' l P

theorem PSDec_ext1 (P : PS) (l : ℕ) : PSDec (ext1 P l) := by
  rintro C o f u Q ⟨Q', us, rfl, hQ', hus⟩
  exact Or.inr ⟨P, Q', us, l, rfl, hQ', hus, Ext_ext1 P l⟩

theorem PSDec_clS {B : PS} (hB : PSDec B) (l : ℕ) : PSDec (clS l B) := by
  rintro C o f u Q ⟨i, hi⟩
  induction i generalizing Q with
  | zero =>
      rcases hB _ _ _ _ _ hi with h | ⟨P', Q', us0, l', rfl, hQ', hus, hX⟩
      · exact Or.inl h
      · exact Or.inr ⟨P', Q', us0, l', rfl, hQ', hus, Ext_mono hX (B_sub_clS l B)⟩
  | succ i ih =>
      rcases hi with hi | ⟨Q', us, rfl, hQ', hus⟩
      · exact ih Q hi
      · refine Or.inr ⟨clE l B i, Q', us, l, rfl, hQ', hus, ?_⟩
        intro C' o' f' u' Q'' us' hQ'' hus'
        exact ⟨i + 1, Or.inr ⟨Q'', us', rfl, hQ'', hus'⟩⟩

theorem PSDec_PNil : PSDec PNil := fun _ _ _ _ _ h => Or.inl h

theorem PSDec_P0 : PSDec P0 := PSDec_clS PSDec_PNil 0

theorem PSDec_chS0 (P : PS) : PSDec (chS0 P) := PSDec_clS (PSDec_ext1 P 0) 0

theorem PSDec_chU (P : PS) (l : ℕ) : PSDec (chU P l) := PSDec_ext1 P l

/-! ## 最後の段 -/

theorem LastL_ext1 (P : PS) (l : ℕ) : LastL (ext1 P l) l := by
  rintro C o f u Q ⟨Q', us, rfl, -, -⟩
  exact lastL_snoc Q' us l

theorem LastL_clS {B : PS} {l : ℕ} (hB : LastL B l) : LastL (clS l B) l := by
  rintro C o f u Q ⟨i, hi⟩
  induction i generalizing Q with
  | zero => exact hB _ _ _ _ _ hi
  | succ i ih =>
      rcases hi with hi | ⟨Q', us, rfl, -, -⟩
      · exact ih Q hi
      · exact lastL_snoc Q' us l

theorem LastL_PNil : LastL PNil 0 := by
  intro C o f u Q h; simp only [PNil] at h; subst h; rfl

theorem LastL_P0 : LastL P0 0 := LastL_clS LastL_PNil

theorem LastL_chS0 (P : PS) : LastL (chS0 P) 0 := LastL_clS (LastL_ext1 P 0)

theorem LastL_chU (P : PS) (l : ℕ) : LastL (chU P l) l := LastL_ext1 P l

theorem P0_closed : Ext P0 0 P0 := clS_closed 0 PNil

theorem chS0_closed (P : PS) : Ext (chS0 P) 0 (chS0 P) := clS_closed 0 _

/-! ## 位置 0 -/

/-- ★ P0 で良い並びは、F のタイの子として GoodChtX に足せる。 -/
theorem Gd_P0_good {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {x : List UT} (h : Gd P0 A k H c x)
    {G : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ} (hE : EmbU A k H G S o f) {u : ℕ} (hcu : c ≤ u)
    {Lds : List (List UT)} (hL : GoodChtX (S ++ A) o f u Lds) :
    GoodChtX (S ++ A) o f u (Lds ++ [imgT A H G c u x]) := by
  have := Gd_good PSOK_P0 h hE hcu hL (PNil_P0 _ _ _ _)
  simpa [plugQ] using this

end HeC
end TRIO
