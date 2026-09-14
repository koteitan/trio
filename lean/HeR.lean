/-
HeR.lean: 深い葉の位置の集合 clB2（段 p と段 l の両方の延長で閉じた閉包）と、その性質（HeC.clS の 2 段版）。

- clB2 p l B: B から、段 p の延長と段 l の延長で閉じた閉包。
- clB2_closed_p / clB2_closed_l: 両方の段の延長で閉じる。
- PSOK_clB2 / PSDec_clB2: 生の条件・埋め込み・段の持ち上げ、分解。
深い葉の塔（tie0 = 段 0、descent の再下降 = 段 l）が集合の中で回る。
-/
import HeQ

namespace TRIO
namespace HeR

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ
open HeB HeC HeQ

/-! ## 2 段の閉包 -/

def extB (p l : ℕ) (B : PS) : ℕ → PS
  | 0 => B
  | i + 1 => fun C o f u Q =>
      extB p l B i C o f u Q ∨ ext1 (extB p l B i) p C o f u Q ∨ ext1 (extB p l B i) l C o f u Q

def clB2 (p l : ℕ) (B : PS) : PS := fun C o f u Q => ∃ i, extB p l B i C o f u Q

theorem extB_sub (p l : ℕ) (B : PS) (i : ℕ) : ∀ C o f u Q, extB p l B i C o f u Q → clB2 p l B C o f u Q :=
  fun _ _ _ _ _ h => ⟨i, h⟩

theorem B_sub_clB2 (p l : ℕ) (B : PS) : ∀ C o f u Q, B C o f u Q → clB2 p l B C o f u Q :=
  fun _ _ _ _ _ h => ⟨0, h⟩

/-- ★ 段 p の延長で閉じる。 -/
theorem clB2_closed_p (p l : ℕ) (B : PS) : Ext (clB2 p l B) p (clB2 p l B) := by
  intro C o f u Q us hQ hus
  obtain ⟨i, hi⟩ := hQ
  exact ⟨i + 1, Or.inr (Or.inl ⟨Q, us, rfl, hi, Gd_mono (extB_sub p l B i) hus⟩)⟩

/-- ★ 段 l の延長で閉じる。 -/
theorem clB2_closed_l (p l : ℕ) (B : PS) : Ext (clB2 p l B) l (clB2 p l B) := by
  intro C o f u Q us hQ hus
  obtain ⟨i, hi⟩ := hQ
  exact ⟨i + 1, Or.inr (Or.inr ⟨Q, us, rfl, hi, Gd_mono (extB_sub p l B i) hus⟩)⟩

/-! ## PSOK -/

theorem PSOK_extB {p l : ℕ} {B : PS} (hB : PSOK B) : ∀ i, PSOK (extB p l B i)
  | 0 => hB
  | i + 1 => by
      have ih := PSOK_extB (p := p) (l := l) hB i
      have hxp := PSOK_ext1 ih p
      have hxl := PSOK_ext1 ih l
      refine ⟨fun C o f u Q h => ?_, fun C o f u Q h => ?_, fun C o f u Q h => ?_⟩
      · rcases h with h | h | h
        · exact ih.raw _ _ _ _ _ h
        · exact hxp.raw _ _ _ _ _ h
        · exact hxl.raw _ _ _ _ _ h
      · intro G S o2 f2 hE
        rcases h with h | h | h
        · exact Or.inl (ih.emb _ _ _ _ _ h _ _ _ _ hE)
        · exact Or.inr (Or.inl (hxp.emb _ _ _ _ _ h _ _ _ _ hE))
        · exact Or.inr (Or.inr (hxl.emb _ _ _ _ _ h _ _ _ _ hE))
      · intro u' hu
        rcases h with h | h | h
        · exact Or.inl (ih.lift _ _ _ _ _ h u' hu)
        · exact Or.inr (Or.inl (hxp.lift _ _ _ _ _ h u' hu))
        · exact Or.inr (Or.inr (hxl.lift _ _ _ _ _ h u' hu))

theorem PSOK_clB2 {p l : ℕ} {B : PS} (hB : PSOK B) : PSOK (clB2 p l B) where
  raw := fun C o f u Q ⟨i, h⟩ => (PSOK_extB hB i).raw _ _ _ _ _ h
  emb := fun C o f u Q ⟨i, h⟩ G S o2 f2 hE => ⟨i, (PSOK_extB hB i).emb _ _ _ _ _ h _ _ _ _ hE⟩
  lift := fun C o f u Q ⟨i, h⟩ u' hu => ⟨i, (PSOK_extB hB i).lift _ _ _ _ _ h u' hu⟩

/-! ## 分解 -/

theorem PSDec_clB2 {p l : ℕ} {B : PS} (hB : PSDec B) : PSDec (clB2 p l B) := by
  rintro C o f u Q ⟨i, hi⟩
  induction i generalizing Q with
  | zero =>
      rcases hB _ _ _ _ _ hi with h | ⟨P', Q', us0, l', rfl, hQ', hus, hX⟩
      · exact Or.inl h
      · exact Or.inr ⟨P', Q', us0, l', rfl, hQ', hus, Ext_mono hX (B_sub_clB2 p l B)⟩
  | succ i ih =>
      rcases hi with hi | ⟨Q', us, rfl, hQ', hus⟩ | ⟨Q', us, rfl, hQ', hus⟩
      · exact ih Q hi
      · refine Or.inr ⟨extB p l B i, Q', us, p, rfl, hQ', hus, ?_⟩
        intro C' o' f' u' Q'' us' hQ'' hus'
        exact ⟨i + 1, Or.inr (Or.inl ⟨Q'', us', rfl, hQ'', hus'⟩)⟩
      · refine Or.inr ⟨extB p l B i, Q', us, l, rfl, hQ', hus, ?_⟩
        intro C' o' f' u' Q'' us' hQ'' hus'
        exact ⟨i + 1, Or.inr (Or.inr ⟨Q'', us', rfl, hQ'', hus'⟩)⟩

end HeR
end TRIO
