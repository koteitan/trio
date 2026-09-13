/-
GyF.lean: 子の級の制限 CtxP_restrict と、子を置く規則（GpT_nil / GpT_node / GpT_load）。
-/
import GyE

namespace TRIO
namespace GyF

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE

/-! ## 部品 -/

def upperF (A1 : List ℕ) (g : ℕ → ℕ) : ℕ → ℕ := fun a => if a ∈ A1 then 0 else g a

theorem G_split (A1 : List ℕ) (G : ℕ → ℕ) : addF (maskF A1 G) (upperF A1 G) = G := by
  funext a; by_cases ha : a ∈ A1 <;> simp [addF, maskF, upperF, ha]

theorem reStep_filter_ind (b m : ℕ) (f g : ℕ → ℕ) (A0 : List ℕ) (p : ℕ → Bool) : ∀ {L : List ℕ},
    (∀ x ∈ L, p x = false → ¬ (b + liftVal f A0 x < m)) →
    reStep b f g A0 L m = reStep b f g A0 (L.filter p) m
  | [], _ => rfl
  | x :: L, h => by
      have ih := reStep_filter_ind b m f g A0 p (L := L)
        (fun y hy => h y (List.mem_cons_of_mem x hy))
      rw [List.filter_cons]
      by_cases hp : p x = true
      · rw [if_pos hp]; simp only [reStep, ih]
      · rw [if_neg hp]
        have hn := h x (by simp) (by simpa using hp)
        simp only [reStep, ih, if_neg hn, Nat.zero_add]

theorem filter_filter_congr {A : List ℕ} {p q r : ℕ → Bool} (h : ∀ x ∈ A, q x = (r x && p x)) :
    A.filter q = (A.filter p).filter r := by
  rw [List.filter_filter]
  exact List.filter_congr h

theorem BotGe_top {X : TrioSeq} (hX : Fr X) (v : ℕ) : BotGe X 1 v := by
  intro c y hc hy hr
  exfalso
  have hw := window_of_rtg0 hr (by simp) X.length hy le_rfl
  rw [Small.entry_append_left hy, show X.length = X.length + 0 from rfl, entry_append_right] at hw
  have := getD_row0_ge hX hy
  have e : entry [c] 0 0 = c.1 := rfl
  rw [e, hc] at hw
  omega

theorem Fr_shift_node (k r : ℕ) (L : TrioSeq) :
    Fr (shiftr01 k 0 (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) := by
  intro y hy
  simp only [shiftr01, List.mem_map] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  have := Fr_node r L p hp
  dsimp only; omega

/-- 子の持ち上げ後の値までは、上の錨は持ち上げに入らない。 -/
theorem reOff_merge {A : List ℕ} {h0 : ℕ → ℕ} {τ1 : ℕ} (h' G : ℕ → ℕ) {s : ℕ}
    (hs : s ≤ liftOff h' (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1))) :
    reOff (mergeF (lowP h0 A τ1) h' h0) G A s = reOff h' G (lowP h0 A τ1) s := by
  unfold reOff
  congr 1
  have hup : ∀ x ∈ A, x ∉ lowP h0 A τ1 → s ≤ liftVal (mergeF (lowP h0 A τ1) h' h0) A x := by
    intro x hx hnx
    have := liftVal_merge_upper h' (fun _ => 0) hx hnx
    rw [addF_zero] at this
    omega
  rw [reStep_filter_ind 0 s (mergeF (lowP h0 A τ1) h' h0) G A
    (fun x => decide (liftVal h0 A x < τ1)) (L := A) (fun x hx hpx => ?_)]
  · change reStep 0 (mergeF (lowP h0 A τ1) h' h0) G A (lowP h0 A τ1) s = _
    exact reStep_congr2 0 s (fun x hx => liftVal_merge h' h0 hx) (fun x _ => rfl)
  · have hnx : x ∉ lowP h0 A τ1 := fun hm => by
      have := (mem_lowP_iff.mp hm).2; simp [this] at hpx
    have := hup x hx hnx
    omega

/-- 差し替えた状態の子の級は、子の錨の列の級。 -/
theorem GC_merge {A : List ℕ} {h0 : ℕ → ℕ} {τ1 : ℕ} (h' G : ℕ → ℕ) {s τ : ℕ}
    (hs : s ≤ liftOff h' (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1)))
    (hτ : τ < reOff h' G (lowP h0 A τ1) s) {b : ℕ} {L : TrioSeq}
    (h : GC A (addF (mergeF (lowP h0 A τ1) h' h0) G) τ b L) :
    GC (lowP h0 A τ1) (addF h' G) τ b L := by
  have eH : addF (mergeF (lowP h0 A τ1) h' h0) G
      = mergeF (lowP h0 A τ1) (addF h' G) (addF h0 G) := by
    funext a; by_cases ha : a ∈ lowP h0 A τ1 <;> simp [mergeF, addF, ha]
  rw [eH] at h
  have hup : ∀ x ∈ A, x ∉ lowP h0 A τ1 →
      τ < liftVal (mergeF (lowP h0 A τ1) (addF h' G) (addF h0 G)) A x := by
    intro x hx hnx
    have h1 := liftVal_merge_upper (addF h' G) G hx hnx
    have h2 := (reOff_liftOff h' G (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1))).symm
    have h3 := reOff_mono h' G (lowP h0 A τ1) hs
    omega
  have hlist : lowP (mergeF (lowP h0 A τ1) (addF h' G) (addF h0 G)) A τ
      = lowP (addF h' G) (lowP h0 A τ1) τ := by
    refine filter_filter_congr (p := fun a => decide (liftVal h0 A a < τ1)) (fun x hx => ?_)
    dsimp only
    by_cases hxA1 : x ∈ lowP h0 A τ1
    · have hx1 : liftVal h0 A x < τ1 := (mem_lowP_iff.mp hxA1).2
      rw [liftVal_merge (addF h' G) (addF h0 G) hxA1]
      simp [hx1]
    · have hx1 : ¬ liftVal h0 A x < τ1 := fun h => hxA1 (mem_lowP_iff.mpr ⟨hx, h⟩)
      have := hup x hx hxA1
      have hx2 : ¬ liftVal (mergeF (lowP h0 A τ1) (addF h' G) (addF h0 G)) A x < τ := by omega
      simp [hx1, hx2]
  unfold GC at h ⊢
  rw [hlist] at h
  have hsum : sumOn (mergeF (lowP h0 A τ1) (addF h' G) (addF h0 G)) (lowP (addF h' G) (lowP h0 A τ1) τ)
      = sumOn (addF h' G) (lowP (addF h' G) (lowP h0 A τ1) τ) :=
    sumOn_congr (fun x hx => by
      have := (mem_lowP_iff.mp hx).1
      unfold mergeF; rw [if_pos this])
  rw [hsum] at h
  exact GpT_congr (fun x hx => (lowP_lt_o1 x hx).1) (fun x hx => by
      have := (mem_lowP_iff.mp hx).1
      unfold mergeF; rw [if_pos this]) h

/-- 上の錨だけの持ち上げは、底に足した単位を動かさない。 -/
theorem reliftX_upper_unit {A : List ℕ} {h0 : ℕ → ℕ} {τ1 : ℕ} (h' G : ℕ → ℕ) {s τ : ℕ}
    (hs : s ≤ liftOff h' (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1)))
    (hτ : τ < reOff h' G (lowP h0 A τ1) s) {Y L : TrioSeq} (hL : Fr L) {d b' : ℕ} (hd : 1 ≤ d)
    (hbot : BotGe Y d (b' + τ)) :
    reliftX b' (addF (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G))
        (upperF (lowP h0 A τ1) G) A
        (Y ++ shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L))
      = reliftX b' (addF (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G))
          (upperF (lowP h0 A τ1) G) A Y
          ++ shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  rw [reliftX_bottom hL hd b' hbot]
  have eF : addF (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G)
      = mergeF (lowP h0 A τ1) (addF h' G) (addF h0 (fun _ => 0)) := by
    rw [addF_zero, mergeF_add]
  have hup : ∀ x ∈ A, x ∉ lowP h0 A τ1 →
      τ < liftVal (addF (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G)) A x := by
    intro x hx hnx
    rw [eF]
    have h1 := liftVal_merge_upper (addF h' G) (fun _ => 0) hx hnx
    have h2 := (reOff_liftOff h' G (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1))).symm
    have h3 := reOff_mono h' G (lowP h0 A τ1) hs
    omega
  have eoff : reOff (addF (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G))
      (upperF (lowP h0 A τ1) G) A τ = τ := by
    unfold reOff
    have key : ∀ L' : List ℕ, (∀ x ∈ L', x ∈ A) →
        reStep 0 (addF (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G))
          (upperF (lowP h0 A τ1) G) A L' τ = 0 := by
      intro L' hL'
      induction L' with
      | nil => rfl
      | cons x L' ih =>
          simp only [reStep]
          rw [ih (fun y hy => hL' y (List.mem_cons_of_mem x hy))]
          by_cases hx : x ∈ lowP h0 A τ1
          · simp [upperF, hx]
          · rw [if_neg (by have := hup x (hL' x (by simp)) hx; omega)]
    rw [key A (fun x hx => hx), Nat.add_zero]
  have elow : reliftX b' (addF (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G))
      (upperF (lowP h0 A τ1) G)
      (lowP (addF (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G)) A τ) L = L := by
    rw [reliftX_congr b' (f' := addF (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G))
      (g' := fun _ => 0) (fun a _ => rfl) (fun a ha => ?_) L, reliftX_zero]
    have hlt := (mem_lowP_iff.mp ha).2
    have haA := (mem_lowP_iff.mp ha).1
    by_cases hA1 : a ∈ lowP h0 A τ1
    · simp [upperF, hA1]
    · exact absurd hlt (by have := hup a haA hA1; omega)
  rw [eoff, elow]

/-! ## 制限の定理 -/

/-- ★ 文脈の族を、子の錨の列だけの状態に制限する。 -/
theorem CtxP_restrict {A : List ℕ} {o' : ℕ} {R : (ℕ → ℕ) → ℕ → TrioSeq → Prop}
    (hR : CtxP (GC A) A o' R) (hAo' : ∀ a ∈ A, a < o') {h0 : ℕ → ℕ} {τ1 : ℕ}
    (hbound : τ1 ≤ liftOff h0 A o') :
    CtxP (GC (lowP h0 A τ1)) (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1))
      (fun h' => R (mergeF (lowP h0 A τ1) h' h0)) := by
  intro h'
  refine ⟨(hR _).1, fun h'' b X hagree hX => ?_, fun g b X hXFr hX => ?_, fun s hs2 hs => ?_⟩
  · have e : mergeF (lowP h0 A τ1) h' h0 = mergeF (lowP h0 A τ1) h'' h0 := by
      funext a; unfold mergeF; split_ifs with ha
      · exact hagree a ha
      · rfl
    show R (mergeF (lowP h0 A τ1) h'' h0) b X
    rw [← e]; exact hX
  · have := (hR _).2.2.1 (maskF (lowP h0 A τ1) g) b X hXFr hX
    show R (mergeF (lowP h0 A τ1) (addF h' g) h0) b (reliftX b h' g (lowP h0 A τ1) X)
    rwa [mergeF_add, ← reliftX_merge (A := A) (h0 := h0) (τ1 := τ1) b h' h0 g X]
  · intro b P d hP hd hbot h1' h2'
    have hsM : s ≤ liftOff (mergeF (lowP h0 A τ1) h' h0) A o' := by
      have hsub : ∀ L : List ℕ, (∀ x ∈ L, x ∈ A) → ∀ F : ℕ → ℕ, stepSum 0 F L o' = sumOn F L :=
        fun L hL F => stepSum_all 0 o' F (fun x hx => by have := hAo' x (hL x hx); omega)
      have sM := stepSum_lowPU 0 o' (mergeF (lowP h0 A τ1) h' h0) h0 A τ1
      have s0 := stepSum_lowPU 0 o' h0 h0 A τ1
      have hPA : ∀ x ∈ lowP h0 A τ1, x ∈ A := fun x hx => (mem_lowP_iff.mp hx).1
      have hUA : ∀ x ∈ lowU h0 A τ1, x ∈ A := fun x hx => (mem_lowU_iff.mp hx).1
      rw [hsub A (fun x hx => hx), hsub _ hPA, hsub _ hUA] at sM s0
      have ePM : sumOn (mergeF (lowP h0 A τ1) h' h0) (lowP h0 A τ1) = sumOn h' (lowP h0 A τ1) :=
        sumOn_congr (fun x hx => by unfold mergeF; rw [if_pos hx])
      have eUM : sumOn (mergeF (lowP h0 A τ1) h' h0) (lowU h0 A τ1) = sumOn h0 (lowU h0 A τ1) :=
        sumOn_congr (fun x hx => by
          unfold mergeF
          rw [if_neg (fun hm => (mem_lowU_iff.mp hx).2 (mem_lowP_iff.mp hm).2)])
      have hb := hbound
      unfold liftOff at hb ⊢
      rw [hsub A (fun x hx => hx)] at hb ⊢
      by_cases hne : lowP h0 A τ1 = []
      · have hlo : liftOff h' (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1)) = τ1 := by
          rw [hne]; simp [liftOff, stepSum, sumOn]
        have hs0 : sumOn h' (lowP h0 A τ1) = 0 := by rw [hne]; rfl
        have hs0' : sumOn h0 (lowP h0 A τ1) = 0 := by rw [hne]; rfl
        rw [hlo] at hs
        omega
      · have hlo : liftOff h' (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1))
            = τ1 - sumOn h0 (lowP h0 A τ1) + sumOn h' (lowP h0 A τ1) :=
          liftOff_eq_sumOn (fun x hx => (lowP_lt_o1 x hx).1)
        obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil _ hne
        have hsum := (lowP_lt_o1 x0 hx0).2
        rw [hlo] at hs
        omega
    refine (hR _).2.2.2 s hs2 hsM b P d hP hd hbot (fun G b' hb' => ?_)
      (fun G b' hb' τ L h1τ hτ hL hGL => ?_)
    · have e1 := h1' G b' hb'
      simp only at e1
      rw [mergeF_add, ← reliftX_merge (A := A) (h0 := h0) (τ1 := τ1) b' h' h0 G] at e1
      have e2 := (hR _).2.2.1 (upperF (lowP h0 A τ1) G) b' _ (Fr_reliftX (Fr_mlift hP _ _) _ _ _ _) e1
      rwa [reliftX_comp, addF_assoc, G_split] at e2
    · have hτ' : τ < reOff h' G (lowP h0 A τ1) s := by
        rw [← reOff_merge (A := A) (h0 := h0) (τ1 := τ1) h' G hs]; exact hτ
      have hGL' := GC_merge (A := A) (h0 := h0) (τ1 := τ1) h' G hs hτ' hGL
      have e1 := h2' G b' hb' τ L h1τ hτ' hL hGL'
      simp only at e1
      rw [mergeF_add, ← reliftX_merge (A := A) (h0 := h0) (τ1 := τ1) b' h' h0 G] at e1
      have hY : Fr (reliftX b' (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G) A
          (mlift P b (b' - b))) := Fr_reliftX (Fr_mlift hP _ _) _ _ _ _
      have hbotY : BotGe (reliftX b' (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G) A
          (mlift P b (b' - b))) d (b' + τ) := by
        have b1 := BotGe_slift hbot (stair_step b (b' - b))
        rw [← mlift_eq_slift, if_pos (by omega), show b + s + (b' - b) = b' + s by omega] at b1
        have b2 := BotGe_slift b1
          (reStair_stair b' (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G) A)
        rw [reStair_base] at b2
        have e3 : reOff (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G) A s
            = reOff h' G (lowP h0 A τ1) s := by
          rw [reOff_merge (A := A) (h0 := h0) (τ1 := τ1) h' _ hs]
          unfold reOff
          rw [reStep_congr 0 s (fun _ _ => rfl) (fun x hx => by unfold maskF; rw [if_pos hx])]
        rw [e3] at b2
        exact BotGe_mono b2 (by omega)
      have hU : Fr (reliftX b' (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G) A
          (mlift P b (b' - b)) ++ shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) :=
        Fr_append hY (Fr_shift_node _ _ _)
      have e2 := (hR _).2.2.1 (upperF (lowP h0 A τ1) G) b' _ hU e1
      rw [reliftX_upper_unit (A := A) (h0 := h0) (τ1 := τ1) h' G hs hτ' hL hd hbotY,
        reliftX_comp, addF_assoc, G_split] at e2
      exact e2

/-! ## 文脈に子を置く -/

/-- ★ 文脈の族 R に、子の級の並びを持つ節点を置く。 -/
theorem R_child {A : List ℕ} {o' : ℕ} {R : (ℕ → ℕ) → ℕ → TrioSeq → Prop}
    (hR : CtxP (GC A) A o' R) (hAo' : ∀ a ∈ A, a < o') {h : ℕ → ℕ} {τ b : ℕ} {X L : TrioSeq}
    (hX : Fr X) (hRX : R h b X) (hL : GC A h τ b L) (hτ : τ ≤ liftOff h A o') :
    R h b (X ++ ((1, b + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  have hR1 := CtxP_restrict hR hAo' (h0 := h) (τ1 := τ) hτ
  unfold GC at hL
  have hn := GpT_elim0 hL hR1
  simp only [mergeF_self] at hn
  rw [liftOff_lowP] at hn
  have := hn b le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero] at this

theorem reStep_lowP (f g : ℕ → ℕ) (A : List ℕ) (τ : ℕ) :
    reStep 0 f g A A τ = sumOn g (lowP f A τ) := by
  rw [reStep_filter_ind 0 τ f g A (fun x => decide (liftVal f A x < τ)) (L := A)
    (fun x _ hpx => by simpa using hpx)]
  change reStep 0 f g A (lowP f A τ) τ = _
  have key : ∀ L : List ℕ, (∀ x ∈ L, liftVal f A x < τ) → reStep 0 f g A L τ = sumOn g L := by
    intro L hL
    induction L with
    | nil => rfl
    | cons x L ih =>
        simp only [reStep, sumOn]
        rw [if_pos (by have := hL x (by simp); omega),
          ih (fun y hy => hL y (List.mem_cons_of_mem x hy))]
  exact key _ (fun x hx => (mem_lowP_iff.mp hx).2)

/-- 子の級の持ち上げ。 -/
theorem GC_lift {A : List ℕ} {f : ℕ → ℕ} {τ b : ℕ} {L : TrioSeq} (h : GC A f τ b L) (g : ℕ → ℕ) :
    GC A (addF f g) (reOff f g A τ) b (reliftX b f g (lowP f A τ) L) := by
  have hlist : lowP (addF f g) A (reOff f g A τ) = lowP f A τ := by
    unfold lowP
    apply List.filter_congr
    intro x _
    have := ind_relift 0 f g A x τ
    simp only [Nat.zero_add] at this
    have e : reStair 0 f g A τ = reOff f g A τ := rfl
    rw [e] at this
    simp [this]
  unfold GC at h ⊢
  rw [hlist]
  have hA1 : ∀ x ∈ lowP f A τ, x < τ - sumOn f (lowP f A τ) := fun x hx => (lowP_lt_o1 x hx).1
  have e2 : reOff f g A τ - sumOn (addF f g) (lowP f A τ) = τ - sumOn f (lowP f A τ) := by
    have hs : sumOn (addF f g) (lowP f A τ) = sumOn f (lowP f A τ) + sumOn g (lowP f A τ) := by
      have key : ∀ L : List ℕ, sumOn (addF f g) L = sumOn f L + sumOn g L := by
        intro L; induction L with
        | nil => rfl
        | cons x L ih => simp only [sumOn, addF, ih]; omega
      exact key _
    have hro : reOff f g A τ = τ + sumOn g (lowP f A τ) := by unfold reOff; rw [reStep_lowP]
    by_cases hne : lowP f A τ = []
    · rw [hs, hro, hne]; simp [sumOn]
    · obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil _ hne
      have := (lowP_lt_o1 x0 hx0).2
      rw [hs, hro]; omega
  rw [e2]
  exact GpT_lift hA1 h g

/-! ## 子を置く規則 -/

theorem GpT_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (ho : 2 ≤ o) (f : ℕ → ℕ) (b : ℕ) :
    GpT A o f b [] := by
  refine GpT_intro hA (fun R hR g => ?_)
  intro u' hu X hX hRX
  have e0 : mlift (reliftX b f g A []) b (u' - b) = [] := by
    unfold reliftX; rw [slift_nil, mlift_nil]
  rw [e0]
  have hk : 2 ≤ liftOff (addF f g) A o := by unfold liftOff; omega
  have eX : X ++ [((1, u' + liftOff (addF f g) A o, 0) : ℕ × ℕ × ℕ)]
      = X ++ ((1, u' + liftOff (addF f g) A o, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 [] := by
    simp [shiftr01]
  rw [← eX]
  refine (hR (addF f g)).2.2.2 _ hk le_rfl u' X 1 hX le_rfl (BotGe_top hX _)
    (fun G b3 hb3 => ?_) (fun G b3 hb3 τ L h1τ hτ hL hGL => ?_)
  · exact (hR (addF f g)).2.2.1 G b3 _ (Fr_mlift hX _ _) ((hR (addF f g)).1.lift u' X hX hRX b3 hb3)
  · have hX3 := (hR (addF f g)).2.2.1 G b3 _ (Fr_mlift hX _ _)
      ((hR (addF f g)).1.lift u' X hX hRX b3 hb3)
    have hτo : τ ≤ liftOff (addF (addF f g) G) A o := by
      rw [← reOff_liftOff]; omega
    have := R_child hR hA (Fr_reliftX (Fr_mlift hX _ _) _ _ _ _) hX3 hGL hτo
    simpa [shiftr01_zero'] using this

theorem GpT_node {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {f : ℕ → ℕ} {b τ : ℕ} {C L : TrioSeq} (hC : Fr C) (hLFr : Fr L)
    (hGC : GpT A o f b C) (hGL : GC A f τ b L) :
    GpT A o f b (C ++ ((1, b + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  refine GpT_intro hA (fun R hR g => ?_)
  rw [reliftX_app hC (Hd_node _ _), reliftX_node hLFr b τ 0 f g A]
  have hRG := CtxP_GpT hA hA1 ho (o + reOff f g A τ)
  have hC' := GpT_lift hA hGC g
  have hL' := GC_lift hGL g
  have hτ : reOff f g A τ ≤ liftOff (addF f g) A (o + reOff f g A τ) := by unfold liftOff; omega
  have := R_child hRG (fun a ha => by have := hA a ha; omega) (Fr_reliftX hC _ _ _ _) hC' hL' hτ
  exact GpT_elim0 this hR

theorem GpT_load {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {f : ℕ → ℕ} {b : ℕ} {K Z : TrioSeq} (hK : Fr K) (h : GpT A o f b K) (hZ : Z ∈ Wg (2 * b))
    (hb : based Z) : GpT A o f b (K ++ shiftr01 1 0 Z) :=
  slot_load (GpT_ax hA hA1 ho f) hK h Z hZ hb

end GyF
end TRIO
