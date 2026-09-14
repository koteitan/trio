/-
HaI.lean: シート行 1489 = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(1,1,1)(2,1,1)（最上段で、子のないタイで終わる遠い語のあとに遠い語）。

最後の遠い語の潰れの写し j の中で、最上段のタイは字と同じ行 1 の F になる。展開は F の語の塔:
    Pf r := (1,r,1)(2,r,1)(2,r,0)
    towF r 0     := Pf r ++ [(1,r,1)]
    towF r (m+1) := Pf r ++ (1,r,1) :: ((1,r,0) :: (towF (r+1) m)↑)↑
- GPF_Pf: 状態 0 の Pf は HaG.GPF_farWA_F（中身なし）。GpT_Pf: 状態 f へは GpT_lift と Pf の再持ち上げの計算。
- towF_GpT: 全ての級 (A, o, f) で塔の良さ（GzU.towWk_GpT と同じ形。接頭辞 Pf の PVP と、F の子を置く R_child (CtxP_RLC)）。
- 最上段: 展開の塔 (0,u,0) :: towF (u+1) m は starOK_topFarTie と TF_tieG（子は towF_GpT の級 ([], 1)）。
-/
import GzJ
import HaG

namespace TRIO
namespace HaI

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF HaG

/-! ## F の語 -/

def Pf (r : ℕ) : TrioSeq :=
  [((1, r, 1) : ℕ × ℕ × ℕ), ((2, r, 1) : ℕ × ℕ × ℕ), ((2, r, 0) : ℕ × ℕ × ℕ)]

theorem Fr_V2 (r : ℕ) : Fr [((1, r, 1) : ℕ × ℕ × ℕ), ((1, r, 0) : ℕ × ℕ × ℕ)] := by
  intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp

theorem Pf_node (r : ℕ) :
    Pf r = ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 [((1, r, 1) : ℕ × ℕ × ℕ), ((1, r, 0) : ℕ × ℕ × ℕ)] := by
  simp [Pf, shiftr01]

theorem Fr_Pf (r : ℕ) : Fr (Pf r) := by
  intro y hy; simp [Pf] at hy; rcases hy with rfl | rfl | rfl <;> simp

theorem Pf_eq (b r : ℕ) : farW b r [] ++ fwW b r b [] ++ [((2, r, 0) : ℕ × ℕ × ℕ)] = Pf r := by
  simp [Pf, farW, fwW, mlift_nil, shiftr01]

theorem GPF_Pf {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (b : ℕ) : GPF A o b (Pf (b + o + 1)) := by
  have := GPF_farWA_F hA hA1 ho le_rfl (OkWsA_nil A o b) (okRA_nil A o b)
  rwa [Pf_eq] at this

theorem mlift_V2 {v r : ℕ} (hvr : v < r) (t : ℕ) :
    mlift [((1, r, 1) : ℕ × ℕ × ℕ), ((1, r, 0) : ℕ × ℕ × ℕ)] v t
      = [((1, r + t, 1) : ℕ × ℕ × ℕ), ((1, r + t, 0) : ℕ × ℕ × ℕ)] := by
  have e : [((1, r, 1) : ℕ × ℕ × ℕ), ((1, r, 0) : ℕ × ℕ × ℕ)]
      = [((1, r, 1) : ℕ × ℕ × ℕ)] ++ [((1, r, 0) : ℕ × ℕ × ℕ)] := rfl
  rw [e, mlift_app (Fr_single le_rfl _ _) (fun _ => rfl)]
  have h1 := mlift_nodez hvr (V := []) Fr_nil 1 t
  have h0 := mlift_nodez hvr (V := []) Fr_nil 0 t
  simp only [shiftr01, List.map_nil, mlift_nil] at h1 h0
  rw [h1, h0]; rfl

theorem mlift_Pf {v r : ℕ} (hvr : v < r) (t : ℕ) : mlift (Pf r) v t = Pf (r + t) := by
  rw [Pf_node, mlift_nodez hvr (Fr_V2 r) 1 t, mlift_V2 hvr t, Pf_node]

theorem reliftX_Pf {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (b : ℕ) (f g : ℕ → ℕ) :
    reliftX b f g A (Pf (b + liftOff f A o + 1)) = Pf (b + liftOff (addF f g) A o + 1) := by
  have hlow : lowP f A (liftOff f A o + 1) = A :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  have hnode : ∀ z : ℕ, reliftX b f g A [((1, b + (liftOff f A o + 1), z) : ℕ × ℕ × ℕ)]
      = [((1, b + (liftOff (addF f g) A o + 1), z) : ℕ × ℕ × ℕ)] := by
    intro z
    have := reliftX_node (V := []) Fr_nil b (liftOff f A o + 1) z f g A
    rw [hlow, reOff_above hA f g 1] at this
    simpa [shiftr01, reliftX, slift_nil] using this
  rw [show b + liftOff f A o + 1 = b + (liftOff f A o + 1) by omega, Pf_node,
    reliftX_node (Fr_V2 _) b (liftOff f A o + 1) 1 f g A, hlow, reOff_above hA f g 1]
  have e : [((1, b + (liftOff f A o + 1), 1) : ℕ × ℕ × ℕ), ((1, b + (liftOff f A o + 1), 0) : ℕ × ℕ × ℕ)]
      = [((1, b + (liftOff f A o + 1), 1) : ℕ × ℕ × ℕ)] ++
        [((1, b + (liftOff f A o + 1), 0) : ℕ × ℕ × ℕ)] := rfl
  rw [e, reliftX_app (Fr_single le_rfl _ _) (fun _ => rfl), hnode 1, hnode 0, Pf_node]
  simp only [List.singleton_append, ← Nat.add_assoc]

theorem GpT_Pf {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (f : ℕ → ℕ) (b : ℕ) : GpT A o f b (Pf (b + liftOff f A o + 1)) := by
  have h1 := GpT_lift hA (GPF_Pf hA hA1 ho b).1 f
  have e := reliftX_Pf hA b (fun _ => 0) f
  rw [liftOff_zeroF] at e
  rw [e] at h1
  have e0 : addF (fun _ => (0 : ℕ)) f = f := by funext a; simp [addF]
  rwa [e0] at h1

theorem PVP_Pf {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (f : ℕ → ℕ) (b : ℕ) : PVP A o f b (Pf (b + liftOff f A o + 1)) := by
  intro t
  rw [mlift_Pf (show b + liftOff f A o < b + liftOff f A o + 1 by omega) t]
  have := GpT_Pf (A := A) (o := o + t) (fun a ha => by have := hA a ha; omega) hA1 (by omega) f b
  rwa [liftOff_add_t hA, show b + (liftOff f A o + t) + 1 = b + liftOff f A o + 1 + t by omega]
    at this

/-! ## F の語の塔 -/

def towF (r : ℕ) : ℕ → TrioSeq
  | 0 => Pf r ++ [((1, r, 1) : ℕ × ℕ × ℕ)]
  | m + 1 => Pf r ++ ((1, r, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towF (r + 1) m))

theorem Fr_towF : ∀ m r, Fr (towF r m)
  | 0, r => by rw [towF]; exact Fr_append (Fr_Pf r) (Fr_single le_rfl _ _)
  | m + 1, r => by rw [towF]; exact Fr_append (Fr_Pf r) (Fr_letter _ _)

theorem towF_GpT : ∀ (m : ℕ) (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), (∀ a ∈ A, a < o) →
    (∀ a ∈ A, 1 ≤ a) → 1 ≤ o → GpT A o f b (towF (b + liftOff f A o + 1) m)
  | 0, A, o, f, b, hA, hA1, ho => by
      rw [towF]
      exact PVP_to_GpT (PVP_snocz hA hA1 ho (Fr_Pf _) (PVP_Pf hA hA1 ho f b))
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
      have hL := towF_GpT m (o :: A) (o + 1) H b hAo' hA1' (by omega)
      rw [e1, show b + (liftOff f A o + 1) + 1 = b + liftOff f A o + 1 + 1 by omega] at hL
      have hGC : GC (o :: A) H (liftOff f A o + 1) b (towF (b + liftOff f A o + 1 + 1) m) := by
        rw [← e1, GC_slot hAo']; exact hL
      have hRL := R_child (CtxP_RLC hA hA1 ho) hAo' Fr_nil (RLC_nil hA hA1 ho H b) hGC
        (le_of_eq e1.symm)
      have h1 := hRL (fun _ => 0) b le_rfl
      rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero, hHo, Nat.add_zero,
        List.nil_append] at h1
      have hLC := LC1_congr hA hHA h1
      have := hLC _ (Fr_Pf _) (PVP_Pf hA hA1 ho f b)
      rw [show b + (liftOff f A o + 1) = b + liftOff f A o + 1 by omega] at this
      rw [towF]
      exact PVP_to_GpT this

/-! ## 最上段 -/

theorem towF0_P (u : ℕ) :
    Fr (towF (u + 1) 0) ∧
    coneV (towF (u + 1) 0 ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)]) u (towF (u + 1) 0).length := by
  refine ⟨Fr_towF 0 (u + 1), ?_⟩
  have hbot : BotGe (Pf (u + 1) ++ ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 []) (0 + 1 + 1) (u + 1) :=
    BotGe_node (Fr_Pf _) le_rfl (BotGe_top Fr_nil _)
  have := coneV_of_BotGe (z := 1) hbot (show u < u + 1 by omega)
  simpa [towF, shiftr01] using this

theorem mlift_towF0 {c : ℕ} (j : ℕ) : mlift (towF (c + 1) 0) c j = towF (c + 1 + j) 0 := by
  rw [show towF (c + 1) 0 = Pf (c + 1) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)] from rfl,
    show towF (c + 1 + j) 0 = Pf (c + 1 + j) ++ [((1, c + 1 + j, 1) : ℕ × ℕ × ℕ)] from rfl,
    mlift_app (Fr_Pf _) (fun _ => rfl), mlift_Pf (by omega) j, mlift_one (by omega)]

theorem towF_flat : ∀ m c, (List.range (m + 1)).flatMap (fun j =>
      shiftr01 (j * 2) 0 (((0, c + j, 0) : ℕ × ℕ × ℕ) :: mlift (towF (c + 1) 0) c j))
      = ((0, c, 0) : ℕ × ℕ × ℕ) :: towF (c + 1) m
  | 0, c => by simp [mlift_towF0]
  | m + 1, c => by
      rw [flatMap_range_cons _ (m + 1)]
      have e : ∀ j, shiftr01 ((j + 1) * 2) 0 (((0, c + (j + 1), 0) : ℕ × ℕ × ℕ) ::
          mlift (towF (c + 1) 0) c (j + 1))
          = shiftr01 2 0 (shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (towF (c + 1 + 1) 0) (c + 1) j)) := by
        intro j
        rw [mlift_towF0, mlift_towF0 (c := c + 1), shift_shift,
          show c + (j + 1) = c + 1 + j by omega, show c + 1 + (j + 1) = c + 1 + 1 + j by omega,
          show (j + 1) * 2 = j * 2 + 2 by omega]
      simp only [e]
      rw [← shift_flatMap 2 (fun j => shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (towF (c + 1 + 1) 0) (c + 1) j)), towF_flat m (c + 1)]
      have eT : shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towF (c + 1 + 1) m))
          = shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towF (c + 1 + 1) m) := by
        rw [show shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towF (c + 1 + 1) m)
            = shiftr01 (1 + 1) 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towF (c + 1 + 1) m) from rfl,
          ← shift_shift]
        rfl
      rw [show towF (c + 1) (m + 1) = Pf (c + 1) ++ ((1, c + 1, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towF (c + 1 + 1) m)) from rfl, eT]
      simp [mlift_zero, towF]

theorem top_towF_Wg (m : ℕ) : (((0, 0, 0) : ℕ × ℕ × ℕ) :: towF 1 m) ∈ Wg 0 := by
  cases m with
  | zero =>
      have h := Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq)))
        (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie])
        (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))
      simpa [shiftr01, rword, rcol, unitsC, unitC, fwTop, towF, Pf] using h
  | succ m =>
      have hG := towF_GpT m [] 1 (fun _ => 0) 0 (by simp) (by simp) le_rfl
      rw [liftOff_zeroF] at hG
      have h := Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq)))
        (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie])
        (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF ⟨hG, Fr_towF m _⟩))
          (WordsG_nil 0)))
      simpa [shiftr01, rword, rcol, unitsC, unitC, fwTop, towF, Pf] using h

/-- ★ シート行 1489。 -/
theorem R1489_mem :
    ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  apply GxB.Wg0_sub_W0
  obtain ⟨hP, hc⟩ := towF0_P 0
  have hM : (((0, 0, 0) : ℕ × ℕ × ℕ) :: (towF (0 + 1) 0 ++ [((2, 0 + 1, 1) : ℕ × ℕ × ℕ)])) ∈ Wg 0 := by
    refine A1g_intro (Or.inr (Or.inl ⟨zcone_natDom hP (show 1 ≤ 2 by omega) hc, fun k hk => ?_⟩))
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [oper_zcone hP (show 1 ≤ 2 by omega) hc (m + 1), towF_flat m 0]
    simpa using top_towF_Wg m
  simpa [towF, Pf] using hM

end HaI
end TRIO
