/-
HaN.lean: 接頭辞を抽象化した F の語の塔。

    TowP Q := Q r は Fr、節点の段より上で t の持ち上げと一緒に動き（lift）、再持ち上げで字と一緒に動き（relift）、
              全ての級 (A, o, f) で良い（good）。
    towQ Q r 0 := Q r ++ [(1,r,1)]、towQ Q r (m+1) := Q r ++ (1,r,1) :: ((1,r,0) :: (towQ Q (r+1) m)↑)↑
    QF Q r := towQ Q r 0 ++ [(2,r,1)]（Q のあとに中身なしの遠い語）

- towQ_GpT: TowP Q なら塔は全ての級で良い（HaI.towF_GpT の写し）。
- TowP_QF: TowP Q → TowP (QF Q)（HaL.GpT_PfF の写し。潰れの展開は towQ）。
- 最上段: Lw n v := [W_tie] ++ (W_far)^n について BwT v (Lw n v)（n の帰納、展開の塔は towQ (QFn n)）。
-/
import GzJ
import HaL

namespace TRIO
namespace HaN

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF HaG HaI HaL

structure TowP (Q : ℕ → TrioSeq) : Prop where
  fr : ∀ r, Fr (Q r)
  lift : ∀ v r t, v < r → mlift (Q r) v t = Q (r + t)
  relift : ∀ (A : List ℕ) (o : ℕ), (∀ a ∈ A, a < o) → ∀ (b : ℕ) (f g : ℕ → ℕ),
    reliftX b f g A (Q (b + liftOff f A o + 1)) = Q (b + liftOff (addF f g) A o + 1)
  good : ∀ (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), (∀ a ∈ A, a < o) → (∀ a ∈ A, 1 ≤ a) → 1 ≤ o →
    GpT A o f b (Q (b + liftOff f A o + 1))

theorem TowP_Pf : TowP Pf :=
  ⟨Fr_Pf, fun _ _ t h => mlift_Pf h t, fun _ _ hA b f g => reliftX_Pf hA b f g,
    fun _ _ f b hA hA1 ho => GpT_Pf hA hA1 ho f b⟩

theorem TowP.pvp {Q : ℕ → TrioSeq} (hQ : TowP Q) {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o)
    (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o) (f : ℕ → ℕ) (b : ℕ) :
    PVP A o f b (Q (b + liftOff f A o + 1)) := by
  intro t
  rw [hQ.lift (b + liftOff f A o) (b + liftOff f A o + 1) t (by omega)]
  have := hQ.good A (o + t) f b (fun a ha => by have := hA a ha; omega) hA1 (by omega)
  rwa [liftOff_add_t hA, show b + (liftOff f A o + t) + 1 = b + liftOff f A o + 1 + t by omega]
    at this

/-! ## 塔 -/

def towQ (Q : ℕ → TrioSeq) (r : ℕ) : ℕ → TrioSeq
  | 0 => Q r ++ [((1, r, 1) : ℕ × ℕ × ℕ)]
  | m + 1 => Q r ++ ((1, r, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towQ Q (r + 1) m))

theorem Fr_towQ {Q : ℕ → TrioSeq} (hQ : TowP Q) : ∀ m r, Fr (towQ Q r m)
  | 0, r => by rw [towQ]; exact Fr_append (hQ.fr r) (GzF.Fr_single le_rfl _ _)
  | m + 1, r => by rw [towQ]; exact Fr_append (hQ.fr r) (Fr_letter _ _)

theorem towQ_GpT {Q : ℕ → TrioSeq} (hQ : TowP Q) :
    ∀ (m : ℕ) (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), (∀ a ∈ A, a < o) →
    (∀ a ∈ A, 1 ≤ a) → 1 ≤ o → GpT A o f b (towQ Q (b + liftOff f A o + 1) m)
  | 0, A, o, f, b, hA, hA1, ho => by
      rw [towQ]
      exact PVP_to_GpT (PVP_snocz hA hA1 ho (hQ.fr _) (hQ.pvp hA hA1 ho f b))
  | m + 1, A, o, f, b, hA, hA1, ho => by
      have hAo' : ∀ a ∈ o :: A, a < o + 1 := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · omega
        · have := hA a ha; omega
      have hA1' : ∀ a ∈ o :: A, 1 ≤ a := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact ho
        · exact hA1 a ha
      obtain ⟨H, hH⟩ : ∃ H : ℕ → ℕ, H = upF o 0 f := ⟨_, rfl⟩
      have hHo : H o = 0 := by rw [hH]; simp [upF]
      have hHA : ∀ a ∈ A, H a = f a := by rw [hH]; exact upF_low hA 0 f
      have e1 : liftOff H (o :: A) (o + 1) = liftOff f A o + 1 := by
        rw [sumOn_liftOff hAo', sumOn_liftOff hA]
        simp only [sumOn, hHo, sumOn_congr hHA]
        omega
      have hL := towQ_GpT hQ m (o :: A) (o + 1) H b hAo' hA1' (by omega)
      rw [e1, show b + (liftOff f A o + 1) + 1 = b + liftOff f A o + 1 + 1 by omega] at hL
      have hGC : GC (o :: A) H (liftOff f A o + 1) b (towQ Q (b + liftOff f A o + 1 + 1) m) := by
        rw [← e1, GC_slot hAo']; exact hL
      have hRL := R_child (CtxP_RLC hA hA1 ho) hAo' Fr_nil (RLC_nil hA hA1 ho H b) hGC
        (le_of_eq e1.symm)
      have h1 := hRL (fun _ => 0) b le_rfl
      rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero, hHo, Nat.add_zero,
        List.nil_append] at h1
      have hLC := LC1_congr hA hHA h1
      have := hLC _ (hQ.fr _) (hQ.pvp hA hA1 ho f b)
      rw [show b + (liftOff f A o + 1) = b + liftOff f A o + 1 by omega] at this
      rw [towQ]
      exact PVP_to_GpT this

theorem towQ0_P {Q : ℕ → TrioSeq} (hQ : TowP Q) (u : ℕ) :
    Fr (towQ Q (u + 1) 0) ∧
    coneV (towQ Q (u + 1) 0 ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)]) u (towQ Q (u + 1) 0).length := by
  refine ⟨Fr_towQ hQ 0 (u + 1), ?_⟩
  have hbot : BotGe (Q (u + 1) ++ ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 []) (0 + 1 + 1) (u + 1) :=
    BotGe_node (hQ.fr _) le_rfl (BotGe_top Fr_nil _)
  have := coneV_of_BotGe (z := 1) hbot (show u < u + 1 by omega)
  simpa [towQ, shiftr01] using this

theorem mlift_towQ0 {Q : ℕ → TrioSeq} (hQ : TowP Q) {c : ℕ} (j : ℕ) :
    mlift (towQ Q (c + 1) 0) c j = towQ Q (c + 1 + j) 0 := by
  rw [show towQ Q (c + 1) 0 = Q (c + 1) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)] from rfl,
    show towQ Q (c + 1 + j) 0 = Q (c + 1 + j) ++ [((1, c + 1 + j, 1) : ℕ × ℕ × ℕ)] from rfl,
    mlift_app (hQ.fr _) (fun _ => rfl), hQ.lift c (c + 1) j (by omega), mlift_one (by omega)]

theorem towQ_flat {Q : ℕ → TrioSeq} (hQ : TowP Q) : ∀ m c, (List.range (m + 1)).flatMap (fun j =>
      shiftr01 (j * 2) 0 (((0, c + j, 0) : ℕ × ℕ × ℕ) :: mlift (towQ Q (c + 1) 0) c j))
      = ((0, c, 0) : ℕ × ℕ × ℕ) :: towQ Q (c + 1) m
  | 0, c => by simp [mlift_towQ0 hQ]
  | m + 1, c => by
      rw [GzF.flatMap_range_cons _ (m + 1)]
      have e : ∀ j, shiftr01 ((j + 1) * 2) 0 (((0, c + (j + 1), 0) : ℕ × ℕ × ℕ) ::
          mlift (towQ Q (c + 1) 0) c (j + 1))
          = shiftr01 2 0 (shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (towQ Q (c + 1 + 1) 0) (c + 1) j)) := by
        intro j
        rw [mlift_towQ0 hQ, mlift_towQ0 hQ (c := c + 1), GzF.shift_shift,
          show c + (j + 1) = c + 1 + j by omega, show c + 1 + (j + 1) = c + 1 + 1 + j by omega,
          show (j + 1) * 2 = j * 2 + 2 by omega]
      simp only [e]
      rw [← GzF.shift_flatMap 2 (fun j => shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (towQ Q (c + 1 + 1) 0) (c + 1) j)), towQ_flat hQ m (c + 1)]
      have eT : shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towQ Q (c + 1 + 1) m))
          = shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towQ Q (c + 1 + 1) m) := by
        rw [show shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towQ Q (c + 1 + 1) m)
            = shiftr01 (1 + 1) 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towQ Q (c + 1 + 1) m) from rfl,
          ← GzF.shift_shift]
        rfl
      rw [show towQ Q (c + 1) (m + 1) = Q (c + 1) ++ ((1, c + 1, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towQ Q (c + 1 + 1) m)) from rfl, eT]
      simp [mlift_zero, towQ]

/-! ## 中身なしの遠い語を足す -/

def QF (Q : ℕ → TrioSeq) (r : ℕ) : TrioSeq := towQ Q r 0 ++ [((2, r, 1) : ℕ × ℕ × ℕ)]

theorem QF_eq (Q : ℕ → TrioSeq) (r : ℕ) :
    QF Q r = Q r ++ ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 [((1, r, 1) : ℕ × ℕ × ℕ)] := by
  simp [QF, towQ, shiftr01]

theorem GpT_QF {Q : ℕ → TrioSeq} (hQ : TowP Q)
    (hrel : ∀ (A : List ℕ) (o : ℕ), (∀ a ∈ A, a < o) → ∀ (b : ℕ) (f g : ℕ → ℕ),
      reliftX b f g A (QF Q (b + liftOff f A o + 1)) = QF Q (b + liftOff (addF f g) A o + 1))
    (hml : ∀ v r t, v < r → mlift (QF Q r) v t = QF Q (r + t))
    {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (f : ℕ → ℕ) (b : ℕ) : GpT A o f b (QF Q (b + liftOff f A o + 1)) := by
  refine GpT_intro hA (fun R hR' g => ?_)
  rw [hrel A o hA b f g]
  obtain ⟨F, hF⟩ : ∃ F, F = addF f g := ⟨_, rfl⟩
  obtain ⟨kk, hkk⟩ : ∃ kk, kk = liftOff F A o := ⟨_, rfl⟩
  rw [← hF, ← hkk]
  have hk1 : o ≤ kk := by rw [hkk]; unfold liftOff; omega
  intro u' hu X hX hRX
  rw [hml b (b + kk + 1) (u' - b) (by omega), show b + kk + 1 + (u' - b) = u' + kk + 1 by omega]
  obtain ⟨c, hc⟩ : ∃ c, c = u' + kk := ⟨_, rfl⟩
  rw [← hc]
  obtain ⟨hP, hcone⟩ := towQ0_P hQ c
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq, U0 = ((0, c, 0) : ℕ × ℕ × ℕ) ::
      (towQ Q (c + 1) 0 ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) := ⟨_, rfl⟩
  have eU : ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (QF Q (c + 1)) = shiftr01 1 0 U0 := by
    rw [hU0, QF]; simp [shiftr01]
  rw [eU]
  have hlen : 2 ≤ U0.length := by rw [hU0]; simp
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom hP (show 1 ≤ 2 by omega) hcone
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h | h
    · exfalso
      have hl : U0.length - 1 = (((0, c, 0) : ℕ × ℕ × ℕ) :: towQ Q (c + 1) 0).length + 0 := by
        rw [hU0]; simp
      rw [hl] at h
      unfold lev at h
      rw [hU0, show ((0, c, 0) : ℕ × ℕ × ℕ) :: (towQ Q (c + 1) 0 ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)])
          = (((0, c, 0) : ℕ × ℕ × ℕ) :: towQ Q (c + 1) 0) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)] by simp,
        entry_append_right, entry_append_right] at h
      simp [entry] at h
    · exact h
  refine (hR' F).1.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
    (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp), hU0]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] U0 1 m hlen hpV
  simp only [List.nil_append] at eO
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [eO, hU0, oper_zcone hP (show 1 ≤ 2 by omega) hcone (m' + 1), towQ_flat hQ m' c]
  have eS : shiftr01 1 0 (((0, c, 0) : ℕ × ℕ × ℕ) :: towQ Q (c + 1) m')
      = ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towQ Q (c + 1) m') := by
    simp [shiftr01]
  rw [eS]
  have hD := towQ_GpT hQ m' A o F u' hA hA1 ho
  rw [← hkk, show u' + kk + 1 = c + 1 by omega] at hD
  have h := GpT_elim0 hD hR'
  rw [← hkk] at h
  have := h u' le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero, ← hc] at this

theorem TowP_QF {Q : ℕ → TrioSeq} (hQ : TowP Q) : TowP (QF Q) := by
  have hfr : ∀ r, Fr (QF Q r) := fun r => by rw [QF_eq]; exact Fr_append (hQ.fr r) (Fr_letter _ _)
  have hml : ∀ v r t, v < r → mlift (QF Q r) v t = QF Q (r + t) := by
    intro v r t h
    rw [QF_eq, QF_eq, mlift_app (hQ.fr r) (Hd_letter _ _), hQ.lift v r t h,
      mlift_letter h (GzF.Fr_single le_rfl _ _) t, mlift_one h]
  have hrel : ∀ (A : List ℕ) (o : ℕ), (∀ a ∈ A, a < o) → ∀ (b : ℕ) (f g : ℕ → ℕ),
      reliftX b f g A (QF Q (b + liftOff f A o + 1)) = QF Q (b + liftOff (addF f g) A o + 1) := by
    intro A o hA b f g
    have hlow : lowP f A (liftOff f A o + 1) = A :=
      lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
    have hnode : reliftX b f g A [((1, b + (liftOff f A o + 1), 1) : ℕ × ℕ × ℕ)]
        = [((1, b + (liftOff (addF f g) A o + 1), 1) : ℕ × ℕ × ℕ)] := by
      have := reliftX_node (V := []) Fr_nil b (liftOff f A o + 1) 1 f g A
      rw [hlow, reOff_above hA f g 1] at this
      simpa [shiftr01, reliftX, slift_nil] using this
    rw [QF_eq, QF_eq, reliftX_app (hQ.fr _) (Hd_letter _ _), hQ.relift A o hA b f g,
      show b + liftOff f A o + 1 = b + (liftOff f A o + 1) by omega,
      reliftX_node (GzF.Fr_single le_rfl _ _) b (liftOff f A o + 1) 1 f g A, hlow,
      reOff_above hA f g 1, hnode]
    simp only [← Nat.add_assoc]
  exact ⟨hfr, hml, hrel, fun A o f b hA hA1 ho => GpT_QF hQ hrel hml hA hA1 ho f b⟩

/-! ## F の語のあとに n 個の中身なしの遠い語 -/

def QFn : ℕ → ℕ → TrioSeq
  | 0 => Pf
  | n + 1 => QF (QFn n)

theorem TowP_QFn : ∀ n, TowP (QFn n)
  | 0 => TowP_Pf
  | n + 1 => TowP_QF (TowP_QFn n)

/-- ★ 節点の子の並び（語の述語）: F の語のあとに n 個の中身なしの遠い語。 -/
theorem PVF_QFn (n : ℕ) {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (b : ℕ) : PVF A o b (QFn n (b + o + 1)) := by
  have := (TowP_QFn n).pvp hA hA1 ho (fun _ => 0) b
  rw [liftOff_zeroF] at this
  exact ⟨this, (TowP_QFn n).fr _⟩

/-! ## 最上段 -/

def Lw (n v : ℕ) : List TrioSeq := [fwTop v [none]] ++ List.replicate n (fwTop v [])

theorem Fr_Lw (n v : ℕ) : ∀ X ∈ Lw n v, ∀ x ∈ X, 1 ≤ x.1 := by
  intro X hX
  simp only [Lw, List.mem_append, List.mem_singleton, List.mem_replicate] at hX
  rcases hX with rfl | ⟨-, rfl⟩ <;> exact Fr_fwTop v _

theorem rword_Lw (v : ℕ) : ∀ n, rword 0 v (Lw n v) = QFn n (v + 1)
  | 0 => by simp [Lw, QFn, rword, rcol, fwTop, unitsC, unitC, Pf, shiftr01]
  | n + 1 => by
      have e : Lw (n + 1) v = Lw n v ++ [fwTop v []] := by
        simp [Lw, List.replicate_succ']
      rw [e, rword_append, rword_Lw v n, QFn, QF_eq]
      simp [rword, rcol, fwTop, unitsC, shiftr01]

theorem map_mlift_Lw {v u : ℕ} (hu : v ≤ u) (n : ℕ) :
    (Lw n v).map (fun X => mlift X v (u - v)) = Lw n u := by
  simp only [Lw, List.map_append, List.map_singleton, List.map_replicate]
  rw [mlift_fwTop (RawU_cons_none (RawU_nil v)), mlift_fwTop (RawU_nil v), show v + (u - v) = u by omega]

theorem topTQ_Wg {n u : ℕ} (hB : BwT u (Lw n u)) (m : ℕ) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: towQ (QFn n) (u + 1) m) ∈ Wg (2 * u) := by
  have key : ∀ K : TrioSeq, WordsG u [K] →
      (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (Lw n u ++ [K])) ∈ Wg (2 * u) := by
    intro K hK
    refine Wg_of_starOK ⟨?_, fun p hp => rword_ge 0 u _ p hp⟩
    have hB2 := BwT_append_words (Fr_Lw n u) hB [K] hK u le_rfl
    rw [Nat.sub_self] at hB2
    simpa only [mlift_zero, List.map_id'] using hB2
  cases m with
  | zero =>
      have := key [] (WordsG_consT (v := u) (TF_nil u) (WordsG_nil u))
      rw [rword_append, rword_Lw] at this
      simpa [towQ, rword, rcol, shiftr01] using this
  | succ m =>
      have hG := towQ_GpT (TowP_QFn n) m [] 1 (fun _ => 0) u (by simp) (by simp) le_rfl
      rw [liftOff_zeroF] at hG
      have := key _ (WordsG_consT (v := u) (TF_tieG (u := u) (TF_nil u)
        (GF_of_GPF ⟨hG, Fr_towQ (TowP_QFn n) m _⟩)) (WordsG_nil u))
      rw [rword_append, rword_Lw] at this
      simpa [towQ, rword, rcol, shiftr01] using this

/-- ★ [W_tie] ++ (W_far)^n は最上段の全ての段で良い。 -/
theorem BwT_Lw : ∀ n v, BwT v (Lw n v)
  | 0, v => by
      have := BwT_topFarTie (v := v) [] (RawUs_nil v) (by simp) [] (RawU_nil v) (by simp [NoTie])
      simpa [Lw] using this
  | n + 1, v => by
      intro u hu
      rw [map_mlift_Lw hu, rword_Lw u (n + 1), QFn]
      simp only [Wstarv, Set.mem_setOf_eq]
      intro _ a ha
      obtain ⟨hP, hc⟩ := towQ0_P (TowP_QFn n) u
      refine A1g_intro (Or.inr (Or.inl ⟨zcone_natDom hP (show 1 ≤ 2 by omega) hc, fun k hk => ?_⟩))
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [show QF (QFn n) (u + 1) = towQ (QFn n) (u + 1) 0 ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)] from rfl,
        oper_zcone hP (show 1 ≤ 2 by omega) hc (m + 1), towQ_flat (TowP_QFn n) m u]
      exact Wg_mono ha (topTQ_Wg (BwT_Lw n u) m)

/-- ★ [W_tie] ++ (W_far)^n のあとに TF の語の並び。 -/
theorem starOK_tieFarN (n : ℕ) {v : ℕ} {Ls : List TrioSeq} (hW : WordsG v Ls) :
    StarOK v (rword 0 v (Lw n v ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_append_words (Fr_Lw n v) (BwT_Lw n v) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end HaN
end TRIO
