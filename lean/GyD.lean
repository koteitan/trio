/-
GyD.lean: GpT の族 (h ↦ GpT A o h) を文脈とする遠い塔の公理（根が差し込み口の節点より上: ge）。
-/
import GyC

namespace TRIO
namespace GyD

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY GyA GyB GyC

/-! ## 底の条件の保存 -/

theorem rtg0_congr0 {M M' : TrioSeq} (hlen : M.length = M'.length)
    (h0 : ∀ i, entry M 0 i = entry M' 0 i) {a b : ℕ} :
    Relation.ReflTransGen (nextrel0 M) a b ↔ Relation.ReflTransGen (nextrel0 M') a b := by
  have key : ∀ x y, nextrel0 M x y ↔ nextrel0 M' x y := by
    intro x y; unfold nextrel0; rw [hlen]; simp only [h0]
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hyz ih => exact ih.tail ((key _ _).1 hyz)
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hyz ih => exact ih.tail ((key _ _).2 hyz)

theorem rtg0_snoc_iff {Q : TrioSeq} {c : ℕ × ℕ × ℕ} {a y : ℕ} (hy : y < Q.length) :
    Relation.ReflTransGen (nextrel0 (Q ++ [c])) a y ↔ Relation.ReflTransGen (nextrel0 Q) a y := by
  have ht : (Q ++ [c]).take Q.length = Q := by simp
  constructor
  · intro h
    have := rtg0_take_mpr (X := Q ++ [c]) (l := Q.length) (by simp) h hy
    rwa [ht] at this
  · intro h
    have h' : Relation.ReflTransGen (nextrel0 ((Q ++ [c]).take Q.length)) a y := by rwa [ht]
    exact rtg0_take_mp (by simp) h'

theorem amin_snoc_bottom {Q : TrioSeq} {d v z : ℕ} (hbot : BotGe Q d v) :
    amin (Q ++ [((d, v, z) : ℕ × ℕ × ℕ)]) Q.length = v := by
  refine le_antisymm ?_ ?_
  · have := amin_self_le (Q ++ [((d, v, z) : ℕ × ℕ × ℕ)]) Q.length
    rw [show Q.length = Q.length + 0 from rfl, entry_append_right] at this
    exact this
  · obtain ⟨y, hy, hey⟩ := amin_mem (Q ++ [((d, v, z) : ℕ × ℕ × ℕ)]) Q.length
    rw [← hey]
    have hyle := rtg0_le hy
    rcases Nat.lt_or_ge y Q.length with hyQ | hyQ
    · rw [Small.entry_append_left hyQ]; exact hbot _ y rfl hyQ hy
    · have hyeq : y = Q.length := by omega
      subst hyeq
      rw [show Q.length = Q.length + 0 from rfl, entry_append_right]
      exact le_rfl

theorem BotGe_slift {Q : TrioSeq} {d v : ℕ} (hbot : BotGe Q d v) {φ : ℕ → ℕ} (hφ : Stair φ) :
    BotGe (slift Q φ) d (φ v) := by
  intro c y hc hy hr
  rw [slift_length] at hy
  have hr' : Relation.ReflTransGen (nextrel0 (Q ++ [c])) y Q.length := by
    have h0 : ∀ i, entry (slift Q φ ++ [c]) 0 i = entry (Q ++ [c]) 0 i := by
      intro i
      rcases Nat.lt_or_ge i Q.length with hi | hi
      · rw [Small.entry_append_left (by rw [slift_length]; exact hi), Small.entry_append_left hi,
          entry0_slift]
      · obtain ⟨q, rfl⟩ : ∃ q, i = Q.length + q := ⟨i - Q.length, by omega⟩
        have e1 : entry (slift Q φ ++ [c]) 0 (Q.length + q) = entry [c] 0 q := by
          have := entry_append_right (slift Q φ) [c] 0 q
          rwa [slift_length] at this
        rw [e1, entry_append_right]
    have := (rtg0_congr0 (by simp) h0).1 hr
    rwa [slift_length] at this
  have hyv := hbot c y hc hy hr'
  obtain ⟨y2, hy2, hey2⟩ := amin_mem Q y
  have hy2le := rtg0_le hy2
  have hamin : v ≤ amin Q y := by
    rw [← hey2]
    exact hbot c y2 hc (by omega) (((rtg0_snoc_iff hy).2 hy2).trans hr')
  rw [entry1_slift hy]
  have h1 := hφ.mono hamin
  have h2 := hφ.ge (amin Q y)
  have h3 := amin_self_le Q y
  omega

theorem BotGe_node {X Q : TrioSeq} (hX : Fr X) {d v r z : ℕ} (hvr : v ≤ r) (hbot : BotGe Q d v) :
    BotGe (X ++ ((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Q) (d + 1) v := by
  intro c y hc hy hr
  have hc' : [c] = shiftr01 1 0 [((d, c.2.1, c.2.2) : ℕ × ℕ × ℕ)] := by
    obtain ⟨c1, c2, c3⟩ := c
    simp only at hc; subst hc
    simp [shiftr01]
  have eM : X ++ ((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Q ++ [c]
      = X ++ (((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (Q ++ [((d, c.2.1, c.2.2) : ℕ × ℕ × ℕ)])) := by
    rw [hc', shiftr01_append0]; simp
  have hlen : (X ++ ((1, r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Q).length = X.length + 1 + Q.length := by
    simp [shiftr01]; omega
  rw [eM, hlen] at hr
  rw [hlen] at hy
  rcases Nat.lt_or_ge y X.length with hyX | hyX
  · exfalso
    have hw := window_of_rtg0 hr (by simp [shiftr01]; omega) X.length hyX (by omega)
    rw [Small.entry_append_left hyX, show X.length = X.length + 0 from rfl, entry_append_right] at hw
    have := getD_row0_ge hX hyX
    have e : entry (((1, r, z) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (Q ++ [((d, c.2.1, c.2.2) : ℕ × ℕ × ℕ)])) 0 0 = 1 := rfl
    rw [e] at hw
    omega
  · obtain ⟨w, rfl⟩ : ∃ w, y = X.length + w := ⟨y - X.length, by omega⟩
    have hr1 := rtg0_append_unlift (Nat.le_add_right _ _) hr (1 + Q.length) (by omega)
    rw [show X.length + w - X.length = w by omega] at hr1
    rcases Nat.eq_zero_or_pos w with rfl | hwpos
    · rw [entry_append_right]
      exact hvr
    · obtain ⟨w', rfl⟩ : ∃ w', w = 1 + w' := ⟨w - 1, by omega⟩
      have hr1' : Relation.ReflTransGen (nextrel0 ([((1, r, z) : ℕ × ℕ × ℕ)] ++
          shiftr01 1 0 (Q ++ [((d, c.2.1, c.2.2) : ℕ × ℕ × ℕ)]))) (1 + w') (1 + Q.length) := by
        rw [List.singleton_append]; exact hr1
      have hr2 := rtg0_append_unlift (A := [((1, r, z) : ℕ × ℕ × ℕ)]) (by simp) hr1' Q.length
        (by simp)
      simp only [List.length_singleton, show 1 + w' - 1 = w' by omega] at hr2
      have hr3 := rtg0_shiftr01.mp hr2
      have hw' : w' < Q.length := by omega
      rw [entry_append_right, show 1 + w' = w' + 1 by omega, entry_cons, entry1_shiftr01]
      exact hbot _ w' rfl hw' hr3

theorem coneV_of_BotGe {Q : TrioSeq} {d v z b : ℕ} (hbot : BotGe Q d v) (hbv : b < v) :
    coneV (Q ++ [((d, v, z) : ℕ × ℕ × ℕ)]) b Q.length := by
  rw [coneV_iff_amin, amin_snoc_bottom hbot]; exact hbv

/-! ## 節点自身の級 -/

theorem lowP_all {f : ℕ → ℕ} {A : List ℕ} {r : ℕ} (h : ∀ a ∈ A, liftVal f A a < r) :
    lowP f A r = A := by
  unfold lowP; exact filter_all (fun a ha => by simpa using h a ha)

theorem liftVal_lt_liftOff {f : ℕ → ℕ} {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {a : ℕ}
    (ha : a ∈ A) : liftVal f A a < liftOff f A o := by
  unfold liftVal liftOff
  have h1 := stepSum_mono 0 f (show a + 1 ≤ o by have := hA a ha; omega) A
  have h2 := hA a ha
  omega

theorem sumOn_liftOff {f : ℕ → ℕ} {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) :
    liftOff f A o = o + sumOn f A := by
  unfold liftOff; rw [stepSum_all 0 o f (fun a ha => by have := hA a ha; omega)]

theorem GC_slot {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (f : ℕ → ℕ) (b : ℕ) (L : TrioSeq) :
    GC A f (liftOff f A o) b L = GpT A o f b L := by
  unfold GC
  rw [lowP_all (fun a ha => liftVal_lt_liftOff hA ha), sumOn_liftOff hA, Nat.add_sub_cancel]

/-! ## 具体化の部品 -/

theorem GpT_elim0 {A : List ℕ} {o : ℕ} {H : ℕ → ℕ} {b : ℕ} {E : TrioSeq} (h : GpT A o H b E)
    {R : (ℕ → ℕ) → ℕ → TrioSeq → Prop} (hR : CtxP (GC A) A o R) :
    nslot (R H) (liftOff H A o) b E := by
  have := GpT_elim h hR (fun _ => 0)
  have e : addF H (fun _ => 0) = H := by funext a; simp [addF]
  rwa [e, reliftX_zero] at this

theorem relift_chain {b u' b3 : ℕ} (hu : b ≤ u') (hb3 : u' ≤ b3) (f g0 g' : ℕ → ℕ) (A : List ℕ)
    (P : TrioSeq) :
    reliftX b3 (addF f g0) g' A (mlift (mlift (reliftX b f g0 A P) b (u' - b)) u' (b3 - u'))
      = reliftX b3 f (addF g0 g') A (mlift P b (b3 - b)) := by
  have e := mlift_mlift (reliftX b f g0 A P) b (u' - b) (b3 - u')
  rw [show b + (u' - b) = u' by omega, show u' - b + (b3 - u') = b3 - b by omega] at e
  rw [e, mlift_reliftX, show b + (b3 - b) = b3 by omega, reliftX_comp]

/-- 文脈の接頭辞 X ++ 節点 :: Q↑1 を段 b3 に上げて持ち上げた形。 -/
theorem relift_prefix {X Q : TrioSeq} (hX : Fr X) (hQ : Fr Q) {u' b3 k : ℕ} (hk : 1 ≤ k)
    (hb3 : u' ≤ b3) (F g' : ℕ → ℕ) (A : List ℕ) :
    reliftX b3 F g' A (mlift (X ++ ((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Q) u' (b3 - u'))
      = reliftX b3 F g' A (mlift X u' (b3 - u')) ++ ((1, b3 + reOff F g' A k, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (reliftX b3 F g' (lowP F A k) (mlift Q u' (b3 - u'))) := by
  rw [mlift_app hX (Hd_node _ _), mlift_nodez (show u' < u' + k by omega) hQ,
    show u' + k + (b3 - u') = b3 + k by omega,
    reliftX_app (Fr_mlift hX _ _) (Hd_nodez _ _ _)]
  rw [reliftX_node (Fr_mlift hQ _ _) b3 k 0 F g' A]

theorem addF_zero (H : ℕ → ℕ) : addF H (fun _ => 0) = H := by funext a; simp [addF]

/-! ## ge: 根が差し込み口の節点より上 -/

theorem FarP_GpT_ge {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) {f : ℕ → ℕ} {s : ℕ} (hs2 : 2 ≤ s) (hso : s ≤ liftOff f A o) :
    FarP (GC A) (fun h => GpT A o h) A f s := by
  intro b P d hP hd hbot h1 h2
  refine GpT_intro hA (fun R hR g0 => ?_)
  rw [reliftX_snoc_bottom hd b hbot f g0 A]
  have hk1 : 1 ≤ liftOff (addF f g0) A o := by unfold liftOff; omega
  have hs'k : reOff f g0 A s ≤ liftOff (addF f g0) A o := by
    rw [← reOff_liftOff]; exact reOff_mono f g0 A hso
  have hs'2 : 2 ≤ reOff f g0 A s := by unfold reOff; omega
  intro u' hu X hX hRX
  have hQ : Fr (reliftX b f g0 A P) := Fr_reliftX hP _ _ _ _
  have hbotQ : BotGe (reliftX b f g0 A P) d (b + reOff f g0 A s) := by
    have := BotGe_slift hbot (reStair_stair b f g0 A)
    rwa [reStair_base] at this
  have hbotQu : BotGe (mlift (reliftX b f g0 A P) b (u' - b)) d (u' + reOff f g0 A s) := by
    have := BotGe_slift hbotQ (stair_step b (u' - b))
    rw [← mlift_eq_slift] at this
    rwa [if_pos (by omega), show b + reOff f g0 A s + (u' - b) = u' + reOff f g0 A s by omega]
      at this
  have eB : mlift (reliftX b f g0 A P ++ [((d, b + reOff f g0 A s, 0) : ℕ × ℕ × ℕ)]) b (u' - b)
      = mlift (reliftX b f g0 A P) b (u' - b) ++ [((d, u' + reOff f g0 A s, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_cone _ _ (coneV_of_BotGe hbotQ (by omega))]
    show _ ++ [((d, b + reOff f g0 A s + (u' - b), 0) : ℕ × ℕ × ℕ)] = _
    rw [show b + reOff f g0 A s + (u' - b) = u' + reOff f g0 A s by omega]
  rw [eB]
  have eV : X ++ ((1, u' + liftOff (addF f g0) A o, 0) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift (reliftX b f g0 A P) b (u' - b) ++
          [((d, u' + reOff f g0 A s, 0) : ℕ × ℕ × ℕ)])
      = (X ++ ((1, u' + liftOff (addF f g0) A o, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift (reliftX b f g0 A P) b (u' - b))) ++
          [((d + 1, u' + reOff f g0 A s, 0) : ℕ × ℕ × ℕ)] := by
    simp [shiftr01, List.append_assoc]
  rw [eV]
  have hQu : Fr (mlift (reliftX b f g0 A P) b (u' - b)) := Fr_mlift hQ _ _
  have hlowk : ∀ H : ℕ → ℕ, lowP H A (liftOff H A o) = A :=
    fun H => lowP_all (fun a ha => liftVal_lt_liftOff hA ha)
  refine (hR (addF f g0)).2.2.2 _ hs'2 hs'k u' _ (d + 1)
    (Fr_append hX (Fr_node _ _)) (by omega)
    (BotGe_node hX (by omega) hbotQu) (fun g' b3 hb3 => ?_) (fun g' b3 hb3 τ L h1τ hτ hL hGL => ?_)
  · -- h1
    rw [relift_prefix hX hQu hk1 hb3, hlowk, reOff_liftOff, addF_assoc]
    have hX3 : R (addF f (addF g0 g')) b3 (reliftX b3 (addF f g0) g' A (mlift X u' (b3 - u'))) := by
      have := (hR (addF f g0)).2.2.1 g' b3 _ (Fr_mlift hX _ _)
        ((hR (addF f g0)).1.lift u' X hX hRX b3 hb3)
      rwa [addF_assoc] at this
    have hE := GpT_elim0 (h1 (addF g0 g') b3 (le_trans hu hb3)) hR
    have := hE b3 le_rfl _ (Fr_reliftX (Fr_mlift hX _ _) _ _ _ _) hX3
    rwa [Nat.sub_self, mlift_zero, ← relift_chain hu hb3 f g0 g' A P] at this
  · -- h2
    rw [relift_prefix hX hQu hk1 hb3, hlowk, reOff_liftOff, addF_assoc]
    have hX3 : R (addF f (addF g0 g')) b3 (reliftX b3 (addF f g0) g' A (mlift X u' (b3 - u'))) := by
      have := (hR (addF f g0)).2.2.1 g' b3 _ (Fr_mlift hX _ _)
        ((hR (addF f g0)).1.lift u' X hX hRX b3 hb3)
      rwa [addF_assoc] at this
    have hτ' : τ < reOff f (addF g0 g') A s := by rw [← reOff_comp]; exact hτ
    rw [addF_assoc] at hGL
    have hE := GpT_elim0 (h2 (addF g0 g') b3 (le_trans hu hb3) τ L h1τ hτ' hL hGL) hR
    have := hE b3 le_rfl _ (Fr_reliftX (Fr_mlift hX _ _) _ _ _ _) hX3
    rw [Nat.sub_self, mlift_zero, ← relift_chain hu hb3 f g0 g' A P] at this
    rw [show d + 1 - 1 = d by omega]
    have eU : ∀ (Y Z : TrioSeq) (w : ℕ × ℕ × ℕ) (U : TrioSeq),
        Y ++ w :: shiftr01 1 0 (Z ++ shiftr01 (d - 1) 0 U) = (Y ++ w :: shiftr01 1 0 Z) ++ shiftr01 d 0 U := by
      intro Y Z w U
      rw [shiftr01_append0, shiftr01_add0, show d - 1 + 1 = d by omega]
      simp [List.append_assoc]
    rwa [eU] at this

/-! ## lt: 根が差し込み口の節点そのもの（塔の写し） -/

theorem reOff_strict (f g : ℕ → ℕ) (A : List ℕ) {m n : ℕ} (h : m < n) :
    reOff f g A m < reOff f g A n := by
  unfold reOff; have := reStep_mono 0 f g A (le_of_lt h) A; omega

theorem FarP_GpT_lt {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (ho : 1 ≤ o)
    {f : ℕ → ℕ} {s : ℕ} (hs : liftOff f A o < s) :
    FarP (GC A) (fun h => GpT A o h) A f s := by
  intro b P d hP hd hbot h1 h2
  refine GpT_intro hA (fun R hR g0 => ?_)
  rw [reliftX_snoc_bottom hd b hbot f g0 A]
  have hk1 : 1 ≤ liftOff (addF f g0) A o := by unfold liftOff; omega
  have hks : liftOff (addF f g0) A o < reOff f g0 A s := by
    rw [← reOff_liftOff]; exact reOff_strict f g0 A hs
  intro u' hu X hX hRX
  have hQ0 : Fr (reliftX b f g0 A P) := Fr_reliftX hP _ _ _ _
  have hbotQ : BotGe (reliftX b f g0 A P) d (b + reOff f g0 A s) := by
    have := BotGe_slift hbot (reStair_stair b f g0 A)
    rwa [reStair_base] at this
  have hbotQu : BotGe (mlift (reliftX b f g0 A P) b (u' - b)) d (u' + reOff f g0 A s) := by
    have := BotGe_slift hbotQ (stair_step b (u' - b))
    rw [← mlift_eq_slift] at this
    rwa [if_pos (by omega), show b + reOff f g0 A s + (u' - b) = u' + reOff f g0 A s by omega]
      at this
  have eB : mlift (reliftX b f g0 A P ++ [((d, b + reOff f g0 A s, 0) : ℕ × ℕ × ℕ)]) b (u' - b)
      = mlift (reliftX b f g0 A P) b (u' - b) ++ [((d, u' + reOff f g0 A s, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_cone _ _ (coneV_of_BotGe hbotQ (by omega))]
    show _ ++ [((d, b + reOff f g0 A s + (u' - b), 0) : ℕ × ℕ × ℕ)] = _
    rw [show b + reOff f g0 A s + (u' - b) = u' + reOff f g0 A s by omega]
  rw [eB]
  -- 記号を置く
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = mlift (reliftX b f g0 A P) b (u' - b) := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = liftOff (addF f g0) A o := ⟨_, rfl⟩
  obtain ⟨s', hs'def⟩ : ∃ s', s' = reOff f g0 A s := ⟨_, rfl⟩
  rw [← hQdef, ← hkdef, ← hs'def]
  rw [← hQdef, ← hs'def] at hbotQu
  rw [← hkdef, ← hs'def] at hks
  rw [← hkdef] at hk1
  have hQ : Fr Q := by rw [hQdef]; exact Fr_mlift hQ0 _ _
  have hQeq : Q = reliftX u' f g0 A (mlift P b (u' - b)) := by
    rw [hQdef, mlift_reliftX, show b + (u' - b) = u' by omega]
  obtain ⟨R', hR'⟩ : ∃ R', R' = Q ++ [((d, u' + s', 0) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  have hRFr : Fr R' := by
    rw [hR']
    exact Fr_append hQ (fun y hy => by simp at hy; subst hy; show 1 ≤ d; omega)
  have hRok : argOK R' := fun p hp => by have := hRFr p hp; omega
  have hRne : R' ≠ [] := by rw [hR']; simp
  have hlast : R'.length - 1 = Q.length + 0 := by rw [hR']; simp
  have eL : ∀ r, entry R' r (R'.length - 1) = entry [((d, u' + s', 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r; rw [hlast, hR', entry_append_right]
  have e0 : entry R' 0 (R'.length - 1) = d := by rw [eL]; rfl
  have e1 : entry R' 1 (R'.length - 1) = u' + s' := by rw [eL]; rfl
  have e2 : entry R' 2 (R'.length - 1) = 0 := by rw [eL]; rfl
  have hsr : srow R' (R'.length - 1) = 1 := by unfold srow; rw [e2, e1]; simp; omega
  have hnpR : ¬ hasParent R' 1 (R'.length - 1) := by
    rintro ⟨j, hj, -⟩
    unfold nextR at hj
    rw [if_neg (by omega), if_pos rfl] at hj
    obtain ⟨-, -, hjlt, hj1, hle0, -⟩ := hj
    rw [hlast] at hjlt hle0
    rw [e1] at hj1
    have hjQ : j < Q.length := by omega
    rw [hR', Small.entry_append_left hjQ] at hj1
    have hr := hle0.2.2
    rw [hR'] at hr
    have := hbotQu _ j rfl hjQ (by simpa using hr)
    omega
  have hd' : domT R' (2 * (u' + s') - 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2]; omega
    · rw [hsr]; exact hnpR
  have hRl : 0 < R'.length := List.length_pos_iff.mpr hRne
  have hpM : hasParent (((0, u' + k, 0) : ℕ × ℕ × ℕ) :: R') (srow R' (R'.length - 1)) R'.length := by
    rw [hsr]
    refine hasParent_one_of (b := R'.length) (k := 0) (by simp) hRl
      ⟨by simp, by simp, rtg0_zero (fun l hl0 hl => ?_) (by simp)⟩ ?_
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [entry_cons]
      have hl' : l' < R'.length := by simp at hl; omega
      have hmem : R'.getD l' (0, 0, 0) ∈ R' := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl']; exact List.getElem_mem hl'
      have := hRok _ hmem
      show 0 < (R'.getD l' (0, 0, 0)).1
      omega
    · rw [entry_cons_last hRne 1, e1]; show u' + k < u' + s'; omega
  have hdl : R'.dropLast = Q := by rw [hR', List.dropLast_concat]
  have htow : ∀ j, shiftr01 1 0 (tow (u' + k) 0 R' (j + 1))
      = ((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (Q ++ shiftr01 d 0 (tow (u' + k) 0 R' j)) := by
    intro j
    rw [tow, graft_eq_shift, e0, hdl]
    simp [shiftr01]
  have hFrL : ∀ j, Fr (Q ++ shiftr01 d 0 (tow (u' + k) 0 R' j)) := fun j =>
    Fr_append hQ (fun y hy => by
      simp only [shiftr01, List.mem_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      dsimp only; omega)
  have hG : ∀ j, GpT A o (addF f g0) u' (Q ++ shiftr01 d 0 (tow (u' + k) 0 R' j)) := by
    intro j
    induction j with
    | zero =>
        simp only [tow, shiftr01, List.map_nil, List.append_nil]
        rw [hQeq]; exact h1 g0 u' hu
    | succ j ih =>
        have e : Q ++ shiftr01 d 0 (tow (u' + k) 0 R' (j + 1))
            = Q ++ shiftr01 (d - 1) 0 (((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
                shiftr01 1 0 (Q ++ shiftr01 d 0 (tow (u' + k) 0 R' j))) := by
          rw [← htow, shiftr01_add0, show 1 + (d - 1) = d by omega]
        rw [e]
        have hGC : GC A (addF f g0) k u' (Q ++ shiftr01 d 0 (tow (u' + k) 0 R' j)) := by
          have e2 := GC_slot hA (addF f g0) u' (Q ++ shiftr01 d 0 (tow (u' + k) 0 R' j))
          rw [← hkdef] at e2
          rw [e2]; exact ih
        have := h2 g0 u' hu k _ hk1 (by rw [← hs'def]; exact hks) (hFrL j) hGC
        rwa [← hQeq] at this
  have eV : ((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 R'
      = shiftr01 1 0 (((0, u' + k, 0) : ℕ × ℕ × ℕ) :: R') := by simp [shiftr01]
  rw [← hR', eV]
  have hlen2 : 2 ≤ (((0, u' + k, 0) : ℕ × ℕ × ℕ) :: R').length := by simp; omega
  have hpM' : hasParent (((0, u' + k, 0) : ℕ × ℕ × ℕ) :: R')
      (srow (((0, u' + k, 0) : ℕ × ℕ × ℕ) :: R') ((((0, u' + k, 0) : ℕ × ℕ × ℕ) :: R').length - 1))
      ((((0, u' + k, 0) : ℕ × ℕ × ℕ) :: R').length - 1) := by
    have hl : ((((0, u' + k, 0) : ℕ × ℕ × ℕ) :: R').length - 1) = R'.length := by simp
    rw [hl, srow_cons_last hRne]; exact hpM
  refine (hR (addF f g0)).1.oper u' X _ hX (Fr_shift1 _) (fun _ => ?_)
    (by rw [shiftr01_length]; exact hlen2)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpM') (fun m hm => ?_)
  · rw [entry0_shiftr01 (by simp)]; rfl
  · have eO := oper_shift [] (((0, u' + k, 0) : ℕ × ℕ × ℕ) :: R') 1 m hlen2 hpM'
    simp only [List.nil_append] at eO
    rw [eO, oper_cons_tower1 hRok hRne hd' hsr hpM]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [htow]
    have := GpT_elim0 (hG j) hR u' le_rfl X hX hRX
    rwa [Nat.sub_self, mlift_zero, ← hkdef] at this

/-- ★ GpT の族は、任意の上限 o' の文脈の公理を満たす。 -/
theorem CtxP_GpT {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (o' : ℕ) : CtxP (GC A) A o' (fun h => GpT A o h) := by
  intro f
  refine ⟨GpT_ax hA hA1 ho f, fun f' b X hff h => GpT_congr hA hff h,
    fun g b X _ h => GpT_lift hA h g, fun s hs2 _ => ?_⟩
  by_cases hs : s ≤ liftOff f A o
  · exact FarP_GpT_ge hA hA1 ho hs2 hs
  · exact FarP_GpT_lt hA ho (by omega)

end GyD
end TRIO
