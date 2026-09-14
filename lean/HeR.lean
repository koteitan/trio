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

/-! ## clD: 段 0 は full、段 l は空前置のみ -/

/-- 空前置の段 l の延長。 -/
def snocNil (l : ℕ) (P : PS) : PS := fun C o f u Q => ∃ Q', Q = Q' ++ [([], l)] ∧ P C o f u Q'

/-- 空前置の延長で閉じることを表す述語。 -/
def ExtNil (P : PS) (l : ℕ) (Pc : PS) : Prop := ∀ C o f u Q, P C o f u Q → Pc C o f u (Q ++ [([], l)])

def extD (l : ℕ) (B : PS) : ℕ → PS
  | 0 => B
  | i + 1 => fun C o f u Q =>
      extD l B i C o f u Q ∨ ext1 (extD l B i) 0 C o f u Q ∨ snocNil l (extD l B i) C o f u Q

def clD (l : ℕ) (B : PS) : PS := fun C o f u Q => ∃ i, extD l B i C o f u Q

theorem extD_sub (l : ℕ) (B : PS) (i : ℕ) : ∀ C o f u Q, extD l B i C o f u Q → clD l B C o f u Q :=
  fun _ _ _ _ _ h => ⟨i, h⟩

theorem B_sub_clD (l : ℕ) (B : PS) : ∀ C o f u Q, B C o f u Q → clD l B C o f u Q :=
  fun _ _ _ _ _ h => ⟨0, h⟩

/-- ★ 段 0 の（full の）延長で閉じる。 -/
theorem clD_closed_0 (l : ℕ) (B : PS) : Ext (clD l B) 0 (clD l B) := by
  intro C o f u Q us hQ hus
  obtain ⟨i, hi⟩ := hQ
  exact ⟨i + 1, Or.inr (Or.inl ⟨Q, us, rfl, hi, Gd_mono (extD_sub l B i) hus⟩)⟩

/-- ★ 段 l の空前置の延長で閉じる。 -/
theorem clD_closed_l (l : ℕ) (B : PS) : ExtNil (clD l B) l (clD l B) := by
  intro C o f u Q hQ
  obtain ⟨i, hi⟩ := hQ
  exact ⟨i + 1, Or.inr (Or.inr ⟨Q, rfl, hi⟩)⟩

theorem PSOK_snocNil {P : PS} (hP : PSOK P) (l : ℕ) : PSOK (snocNil l P) where
  raw := by
    rintro C o f u Q ⟨Q', rfl, hQ'⟩ p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hP.raw _ _ _ _ _ hQ' p hp
    · simp at hp; subst hp; simp [RawTs]
  emb := by
    rintro C o f u Q ⟨Q', rfl, hQ'⟩ G S o2 f2 hE
    refine ⟨mapQ (relTs C f G u) Q', ?_, hP.emb _ _ _ _ _ hQ' _ _ _ _ hE⟩
    rw [mapQ_snoc]; simp [relTs]
  lift := by
    rintro C o f u Q ⟨Q', rfl, hQ'⟩ u' hu
    refine ⟨mapQ (mlTs u (u' - u)) Q', ?_, hP.lift _ _ _ _ _ hQ' u' hu⟩
    rw [mapQ_snoc]; simp [mlTs]

theorem PSOK_extD {l : ℕ} {B : PS} (hB : PSOK B) : ∀ i, PSOK (extD l B i)
  | 0 => hB
  | i + 1 => by
      have ih := PSOK_extD (l := l) hB i
      have hx0 := PSOK_ext1 ih 0
      have hxl := PSOK_snocNil ih l
      refine ⟨fun C o f u Q h => ?_, fun C o f u Q h => ?_, fun C o f u Q h => ?_⟩
      · rcases h with h | h | h
        · exact ih.raw _ _ _ _ _ h
        · exact hx0.raw _ _ _ _ _ h
        · exact hxl.raw _ _ _ _ _ h
      · intro G S o2 f2 hE
        rcases h with h | h | h
        · exact Or.inl (ih.emb _ _ _ _ _ h _ _ _ _ hE)
        · exact Or.inr (Or.inl (hx0.emb _ _ _ _ _ h _ _ _ _ hE))
        · exact Or.inr (Or.inr (hxl.emb _ _ _ _ _ h _ _ _ _ hE))
      · intro u' hu
        rcases h with h | h | h
        · exact Or.inl (ih.lift _ _ _ _ _ h u' hu)
        · exact Or.inr (Or.inl (hx0.lift _ _ _ _ _ h u' hu))
        · exact Or.inr (Or.inr (hxl.lift _ _ _ _ _ h u' hu))

theorem PSOK_clD {l : ℕ} {B : PS} (hB : PSOK B) : PSOK (clD l B) where
  raw := fun C o f u Q ⟨i, h⟩ => (PSOK_extD hB i).raw _ _ _ _ _ h
  emb := fun C o f u Q ⟨i, h⟩ G S o2 f2 hE => ⟨i, (PSOK_extD hB i).emb _ _ _ _ _ h _ _ _ _ hE⟩
  lift := fun C o f u Q ⟨i, h⟩ u' hu => ⟨i, (PSOK_extD hB i).lift _ _ _ _ _ h u' hu⟩

/-! ## 空前置の spine の再下降 -/

/-- 空前置の段 l の spine（全成分が ([], l)）。 -/
def SpineL (l : ℕ) (Q : Path) : Prop := ∀ s ∈ Q, s = ([], l)

theorem SpineL_nil (l : ℕ) : SpineL l [] := fun _ h => by simp at h

theorem clD_append_spine {l : ℕ} {B : PS} {Q : Path} (hQ : SpineL l Q) :
    ∀ C o f u Qp, clD l B C o f u Qp → clD l B C o f u (Qp ++ Q) := by
  induction Q using List.reverseRecOn with
  | nil => intro C o f u Qp h; simpa using h
  | append_singleton Q s ih =>
      intro C o f u Qp h
      have hs : s = ([], l) := hQ s (by simp)
      subst hs
      have hQ' : SpineL l Q := fun s' hs' => hQ s' (List.mem_append_left _ hs')
      rw [← List.append_assoc]
      exact clD_closed_l l B C o f u (Qp ++ Q) (ih hQ' C o f u Qp h)

theorem imgT_plugQ_spine {A : List ℕ} {H G : ℕ → ℕ} {c u : ℕ} {l : ℕ} {Q : Path} (hQ : SpineL l Q) :
    ∀ W : List UT, imgT A H G c u (plugQ Q W) = plugQ Q (imgT A H G c u W) := by
  induction Q with
  | nil => intro W; simp [plugQ]
  | cons s Q ih =>
      intro W
      have hs : s = ([], l) := hQ s (by simp)
      subst hs
      have hQ' : SpineL l Q := fun s' hs' => hQ s' (by simp [hs'])
      simp only [plugQ, List.nil_append, imgT_append, imgT_tie, ih hQ' W, imgT_nil, List.nil_append]

theorem plugQ_append : ∀ (Q Q' : Path) (T : List UT), plugQ (Q ++ Q') T = plugQ Q (plugQ Q' T)
  | [], Q', T => by simp [plugQ]
  | (us, l) :: Q, Q', T => by simp only [List.cons_append, plugQ, plugQ_append Q Q' T]

theorem RawTs_plugQ_spine {l : ℕ} {Q : Path} (hQ : SpineL l Q) {k : ℕ} {W : List UT} (hW : RawTs k W) :
    RawTs k (plugQ Q W) := by
  induction Q with
  | nil => simpa [plugQ] using hW
  | cons s Q ih =>
      have hs : s = ([], l) := hQ s (by simp)
      subst hs
      have hQ' : SpineL l Q := fun s' hs' => hQ s' (by simp [hs'])
      simp only [plugQ, List.nil_append, RawTs]
      exact ⟨RawT_tie.mpr (ih hQ'), trivial⟩

/-- ★ 空前置の spine の再下降は clD-good を保つ。 -/
theorem Gd_redescend {l : ℕ} {B : PS} {Q : Path} (hQ : SpineL l Q) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ}
    {c : ℕ} {W : List UT} (h : Gd (clD l B) A k H c W) : Gd (clD l B) A k H c (plugQ Q W) := by
  refine ⟨RawTs_plugQ_spine hQ h.1, fun G S o f hE u hcu Lds hL Qp hQp => ?_⟩
  rw [imgT_plugQ_spine hQ]
  intro b hub ws hC hR
  have hQpQ : clD l B (S ++ A) o f u (Qp ++ Q) := clD_append_spine hQ _ _ _ _ _ hQp
  have := h.2 G S o f hE u hcu Lds hL (Qp ++ Q) hQpQ b hub ws hC hR
  rwa [plugQ_append] at this

/-! ## 深い葉の塔の良さ -/

/-- ★ 深い葉の塔の各段が clD-good（tie0 = 段 0 の延長、再下降 = Gd_redescend）。 -/
theorem Gd_deep_towers {l : ℕ} {B : PS} {Q : Path} (hQ : SpineL l Q) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ}
    (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k) (hAk : ∀ a ∈ A, a < k) {c : ℕ} {us : List UT}
    (hus : Gd (clD l B) A k H c us) : ∀ j, Gd (clD l B) A k H c (Xtow Q us j)
  | 0 => hus
  | j + 1 => by
      rw [show Xtow Q us (j + 1) = us ++ [UT.tie 0 (plugQ Q (Xtow Q us j))] from rfl]
      exact Gd_tie (clD_closed_0 l B) hA01 hk hAk hus
        (Gd_redescend hQ (Gd_deep_towers hQ hA01 hk hAk hus j))

end HeR
end TRIO
