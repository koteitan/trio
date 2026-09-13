/-
GzF.lean: 先頭に続く遠い語 n 個（節点の下の語と、最上段の語）。

    farR r 0     = []
    farR r (n+1) = farR r n ++ [(1,r,1), (2,r,1)]
    towF r n 0     = farR r n ++ [(1,r,1)]
    towF r n (m+1) = farR r n ++ (1,r,1) :: ((1,r,0) :: (towF (r+1) n m)↑1)↑1

    ((0,c,0) :: farR (c+1) (n+1))⟦m+1⟧ = (0,c,0) :: towF (c+1) n m

最後の遠い語の潰れは、字の中身の F とその子の並び（錨の列が 1 つ伸びる）の塔。
n の帰納法: farR n の GpT（全ての錨の列と状態）から towF n m の GpT、そこから farR (n+1) の GpT。
-/
import GzD

namespace TRIO
namespace GzF

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD

def farR (r : ℕ) : ℕ → TrioSeq
  | 0 => []
  | n + 1 => farR r n ++ [((1, r, 1) : ℕ × ℕ × ℕ), ((2, r, 1) : ℕ × ℕ × ℕ)]

def towF : ℕ → ℕ → ℕ → TrioSeq
  | r, n, 0 => farR r n ++ [((1, r, 1) : ℕ × ℕ × ℕ)]
  | r, n, m + 1 => farR r n ++ ((1, r, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towF (r + 1) n m))

/-! ## 行 1 が一定の列 -/

def CR (r : ℕ) (Z : TrioSeq) : Prop := ∀ x ∈ Z, x.2.1 = r

theorem entry1_CR {r : ℕ} {Z : TrioSeq} (h : CR r Z) {i : ℕ} (hi : i < Z.length) :
    entry Z 1 i = r := by
  have e := entry_triple hi
  have hm := h _ (List.getElem_mem hi)
  rw [← e] at hm
  exact hm

theorem coneV_CR {r v : ℕ} {Z : TrioSeq} (h : CR r Z) (hv : v < r) {j : ℕ} (hj : j < Z.length) :
    coneV Z v j := by
  intro y hy
  have := rtg0_le hy
  rw [entry1_CR h (by omega)]; exact hv

theorem amin_CR {r : ℕ} {Z : TrioSeq} (h : CR r Z) {j : ℕ} (hj : j < Z.length) : amin Z j = r := by
  obtain ⟨y, hy, hey⟩ := amin_mem Z j
  have := rtg0_le hy
  rw [← hey, entry1_CR h (by omega)]

theorem slift_CR {r : ℕ} {Z : TrioSeq} (h : CR r Z) (φ : ℕ → ℕ) :
    slift Z φ = shiftr01 0 (φ r - r) Z := by
  refine List.ext_getElem (by rw [slift_length, shiftr01_length]) ?_
  intro i h1 h2
  rw [slift_length] at h1
  unfold slift shiftr01
  simp only [List.getElem_map, List.getElem_range]
  rw [amin_CR h h1, ← entry_triple h1]
  rfl

theorem mlift_CR {r v : ℕ} {Z : TrioSeq} (h : CR r Z) (hv : v < r) (d : ℕ) :
    mlift Z v d = shiftr01 0 d Z := by
  rw [mlift_eq_slift, slift_CR h, if_pos hv, Nat.add_sub_cancel_left]

theorem CR_append {r : ℕ} {A B : TrioSeq} (hA : CR r A) (hB : CR r B) : CR r (A ++ B) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hA x h
  · exact hB x h

theorem CR_single (a r z : ℕ) : CR r [((a, r, z) : ℕ × ℕ × ℕ)] := by
  intro x hx; simp at hx; subst hx; rfl

theorem Fr_single {a : ℕ} (ha : 1 ≤ a) (r z : ℕ) : Fr [((a, r, z) : ℕ × ℕ × ℕ)] := by
  intro x hx; simp at hx; subst hx; exact ha

theorem shift_shift (a b : ℕ) (X : TrioSeq) :
    shiftr01 a 0 (shiftr01 b 0 X) = shiftr01 (b + a) 0 X := by
  simp [shiftr01, Function.comp_def, Nat.add_assoc]

/-! ## 遠い語の列 -/

theorem CR_farR (r : ℕ) : ∀ n, CR r (farR r n)
  | 0 => fun x hx => by simp [farR] at hx
  | n + 1 => fun x hx => by
      simp only [farR, List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | rfl | hx
      · exact CR_farR r n x hx
      · rfl
      · rfl
      · simp at hx

theorem Fr_farR (r : ℕ) : ∀ n, Fr (farR r n)
  | 0 => Fr_nil
  | n + 1 => by
      refine Fr_append (Fr_farR r n) ?_
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · show 1 ≤ 1; omega
      · show 1 ≤ 2; omega
      · simp at hx

theorem shift_farR (r d : ℕ) : ∀ n, shiftr01 0 d (farR r n) = farR (r + d) n
  | 0 => rfl
  | n + 1 => by
      have ih := shift_farR r d n
      unfold shiftr01 at ih ⊢
      simp only [farR, List.map_append, ih, List.map_cons, List.map_nil]

theorem mlift_farR {r v : ℕ} (hv : v < r) (d n : ℕ) : mlift (farR r n) v d = farR (r + d) n := by
  rw [mlift_CR (CR_farR r n) hv, shift_farR]

theorem reliftX_farR {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (b : ℕ) (f g : ℕ → ℕ) (n : ℕ) :
    reliftX b f g A (farR (b + liftOff f A o + 1) n)
      = farR (b + liftOff (addF f g) A o + 1) n := by
  unfold reliftX
  rw [slift_CR (CR_farR _ n), shift_farR]
  have e : reStair b f g A (b + liftOff f A o + 1) = b + liftOff (addF f g) A o + 1 := by
    rw [show b + liftOff f A o + 1 = b + (liftOff f A o + 1) by omega, reStair_base, reOff_above hA]
    omega
  have hk : liftOff f A o ≤ liftOff (addF f g) A o := by rw [liftOff_addF hA]; omega
  rw [e]
  congr 1
  omega

theorem farR_P (c n : ℕ) :
    Fr (farR (c + 1) n ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ∧
    coneV ((farR (c + 1) n ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) c
      (farR (c + 1) n ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]).length :=
  ⟨Fr_append (Fr_farR _ n) (Fr_single le_rfl _ _),
   coneV_CR (CR_append (CR_append (CR_farR _ n) (CR_single _ _ _)) (CR_single _ _ _)) (by omega)
     (by simp)⟩

theorem Fr_towF : ∀ (m r n : ℕ), Fr (towF r n m)
  | 0, r, n => by rw [towF]; exact Fr_append (Fr_farR r n) (Fr_single le_rfl _ _)
  | m + 1, r, n => by rw [towF]; exact Fr_append (Fr_farR r n) (Fr_letter _ _)

/-! ## 展開の平坦化 -/

theorem mlift_P (c n j : ℕ) :
    mlift (farR (c + 1) n ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j
      = farR (c + 1 + j) n ++ [((1, c + 1 + j, 1) : ℕ × ℕ × ℕ)] := by
  rw [mlift_CR (CR_append (CR_farR _ n) (CR_single _ _ _)) (show c < c + 1 by omega)]
  rw [show shiftr01 0 j (farR (c + 1) n ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])
      = shiftr01 0 j (farR (c + 1) n) ++ shiftr01 0 j [((1, c + 1, 1) : ℕ × ℕ × ℕ)] by
    simp only [shiftr01, List.map_append], shift_farR]
  rfl

theorem shift_flatMap (d : ℕ) (G : ℕ → TrioSeq) : ∀ L : List ℕ,
    shiftr01 d 0 (L.flatMap G) = L.flatMap (fun j => shiftr01 d 0 (G j))
  | [] => rfl
  | x :: L => by
      rw [List.flatMap_cons, List.flatMap_cons, ← shift_flatMap d G L]
      simp only [shiftr01, List.map_append]

theorem flatMap_range_cons (F : ℕ → TrioSeq) : ∀ m,
    (List.range (m + 1)).flatMap F = F 0 ++ (List.range m).flatMap (fun j => F (j + 1))
  | 0 => by simp
  | m + 1 => by
      rw [show List.range (m + 1 + 1) = List.range (m + 1) ++ [m + 1] from List.range_succ,
        List.flatMap_append, flatMap_range_cons F m,
        show List.range (m + 1) = List.range m ++ [m] from List.range_succ]
      simp [List.append_assoc]

theorem farR_flat (n : ℕ) : ∀ m c, (List.range (m + 1)).flatMap (fun j =>
    shiftr01 (j * 2) 0 (((0, c + j, 0) : ℕ × ℕ × ℕ) ::
      mlift (farR (c + 1) n ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j))
    = ((0, c, 0) : ℕ × ℕ × ℕ) :: towF (c + 1) n m
  | 0, c => by simp [mlift_P, towF]
  | m + 1, c => by
      rw [flatMap_range_cons _ (m + 1)]
      have e : ∀ j, shiftr01 ((j + 1) * 2) 0 (((0, c + (j + 1), 0) : ℕ × ℕ × ℕ) ::
          mlift (farR (c + 1) n ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c (j + 1))
          = shiftr01 2 0 (shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (farR (c + 1 + 1) n ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)) := by
        intro j
        rw [mlift_P, mlift_P, shift_shift, show c + (j + 1) = c + 1 + j by omega,
          show c + 1 + (j + 1) = c + 1 + 1 + j by omega, show (j + 1) * 2 = j * 2 + 2 by omega]
      simp only [e]
      rw [← shift_flatMap 2 (fun j => shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (farR (c + 1 + 1) n ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)),
        farR_flat n m (c + 1)]
      have eT : shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towF (c + 1 + 1) n m))
          = shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towF (c + 1 + 1) n m) := by
        rw [show shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towF (c + 1 + 1) n m)
            = shiftr01 (1 + 1) 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towF (c + 1 + 1) n m) from rfl,
          ← shift_shift]
        rfl
      rw [towF, eT]
      simp [mlift_P]

/-! ## 節点の下: 遠い語 n 個の GpT -/

def FarC (n : ℕ) : Prop :=
  ∀ (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), (∀ a ∈ A, a < o) → (∀ a ∈ A, 1 ≤ a) → 1 ≤ o →
    GpT A o f b (farR (b + liftOff f A o + 1) n)

theorem farR_PVP {n : ℕ} (hC : FarC n) {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o)
    (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o) (f : ℕ → ℕ) (b : ℕ) :
    PVP A o f b (farR (b + liftOff f A o + 1) n) := by
  intro t
  rw [mlift_farR (show b + liftOff f A o < b + liftOff f A o + 1 by omega)]
  have := hC A (o + t) f b (fun a ha => by have := hA a ha; omega) hA1 (by omega)
  rwa [liftOff_add_t hA, show b + (liftOff f A o + t) + 1 = b + liftOff f A o + 1 + t by omega] at this

theorem towF_GpT {n : ℕ} (hC : FarC n) : ∀ (m : ℕ) (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ),
    (∀ a ∈ A, a < o) → (∀ a ∈ A, 1 ≤ a) → 1 ≤ o →
    GpT A o f b (towF (b + liftOff f A o + 1) n m)
  | 0, A, o, f, b, hA, hA1, ho => by
      rw [towF]
      exact PVP_to_GpT (PVP_snocz hA hA1 ho (Fr_farR _ n) (farR_PVP hC hA hA1 ho f b))
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
      have hL := towF_GpT hC m (o :: A) (o + 1) H b hAo' hA1' (by omega)
      rw [e1, show b + (liftOff f A o + 1) + 1 = b + liftOff f A o + 1 + 1 by omega] at hL
      have hGC : GC (o :: A) H (liftOff f A o + 1) b (towF (b + liftOff f A o + 1 + 1) n m) := by
        rw [← e1, GC_slot hAo']; exact hL
      have hRL := R_child (CtxP_RLC hA hA1 ho) hAo' Fr_nil (RLC_nil hA hA1 ho H b) hGC
        (le_of_eq e1.symm)
      have h1 := hRL (fun _ => 0) b le_rfl
      rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero, hHo, Nat.add_zero,
        List.nil_append] at h1
      have hLC := LC1_congr hA hHA h1
      have := hLC _ (Fr_farR _ n) (farR_PVP hC hA hA1 ho f b)
      rw [show b + (liftOff f A o + 1) = b + liftOff f A o + 1 by omega] at this
      rw [towF]
      exact PVP_to_GpT this

/-- ★ 遠い語 n 個は、全ての錨の列と状態で節点の子の並び。 -/
theorem farR_GpT : ∀ n, FarC n
  | 0 => by
      intro A o f b hA hA1 ho
      rw [farR]
      rcases Nat.lt_or_ge o 2 with h | h
      · have ho1 : o = 1 := by omega
        subst ho1
        have hA0 : A = [] := List.eq_nil_iff_forall_not_mem.mpr
          (fun a ha => by have := hA a ha; have := hA1 a ha; omega)
        subst hA0
        exact GpT_nil1 f b
      · exact GpT_nil hA h f b
  | n + 1 => by
      intro A o f b hA hA1 ho
      have hC := farR_GpT n
      refine GpT_intro hA (fun R hR g => ?_)
      rw [reliftX_farR hA]
      obtain ⟨F, hF⟩ : ∃ F, F = addF f g := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k, k = liftOff F A o := ⟨_, rfl⟩
      rw [← hF, ← hk]
      intro u' hu X hX hRX
      rw [mlift_farR (show b < b + k + 1 by omega),
        show b + k + 1 + (u' - b) = u' + k + 1 by omega]
      obtain ⟨c, hc⟩ : ∃ c, c = u' + k := ⟨_, rfl⟩
      rw [← hc]
      obtain ⟨hP, hcone⟩ := farR_P c n
      obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq, U0 = ((0, c, 0) : ℕ × ℕ × ℕ) ::
          ((farR (c + 1) n ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) :=
        ⟨_, rfl⟩
      have eU : ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (farR (c + 1) (n + 1)) = shiftr01 1 0 U0 := by
        rw [hU0]; simp [shiftr01, farR]
      rw [eU]
      have hlen : 2 ≤ U0.length := by rw [hU0]; simp
      have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
        have hn := zcone_natDom hP (show 1 ≤ 2 by omega) hcone
        rw [← hU0] at hn
        rcases natDom_iff.mp hn with h | h
        · exfalso
          have hl : U0.length - 1 = (((0, c, 0) : ℕ × ℕ × ℕ) ::
              (farR (c + 1) n ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])).length + 0 := by
            rw [hU0]; simp
          rw [hl] at h
          unfold lev at h
          rw [hU0, show ((0, c, 0) : ℕ × ℕ × ℕ) :: ((farR (c + 1) n ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++
              [((2, c + 1, 1) : ℕ × ℕ × ℕ)])
            = (((0, c, 0) : ℕ × ℕ × ℕ) :: (farR (c + 1) n ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])) ++
              [((2, c + 1, 1) : ℕ × ℕ × ℕ)] by simp,
            entry_append_right, entry_append_right] at h
          simp [entry] at h
        · exact h
      refine (hR F).1.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
        (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp), hU0]; rfl)
        (by rw [shiftr01_length]; exact hlen)
        (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
      have eO := oper_shift [] U0 1 m hlen hpV
      simp only [List.nil_append] at eO
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [eO, hU0, oper_zcone hP (show 1 ≤ 2 by omega) hcone (m' + 1), farR_flat n m' c]
      have eS : shiftr01 1 0 (((0, c, 0) : ℕ × ℕ × ℕ) :: towF (c + 1) n m')
          = ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towF (c + 1) n m') := by
        simp [shiftr01]
      rw [eS]
      have hD := towF_GpT hC m' A o F u' hA hA1 ho
      rw [← hk, ← hc] at hD
      have h := GpT_elim0 hD hR
      rw [← hk] at h
      have := h u' le_rfl X hX hRX
      rwa [Nat.sub_self, mlift_zero, ← hc] at this

theorem PVF_farR {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (b n : ℕ) : PVF A o b (farR (b + o + 1) n) := by
  have := farR_PVP (farR_GpT n) hA hA1 ho (fun _ => 0) b
  rw [liftOff_zeroF] at this
  exact ⟨this, Fr_farR _ n⟩

/-! ## 最上段: 遠い語 n 個のあとに GT の語 -/

theorem rword_rep (u : ℕ) : ∀ n,
    rword 0 u (List.replicate n [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) = farR (u + 1) n
  | 0 => rfl
  | n + 1 => by
      have ih := rword_rep u n
      unfold rword at ih ⊢
      rw [List.replicate_succ', List.flatMap_append, ih]
      simp [farR, rcol, shiftr01]

theorem rword_rep_snoc (u n : ℕ) (C : TrioSeq) :
    rword 0 u (List.replicate n [((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [C])
      = farR (u + 1) n ++ ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 C := by
  have := rword_rep u n
  unfold rword at this ⊢
  rw [List.flatMap_append, this]
  simp [rcol]

theorem towF_Wg {n : ℕ} (hB : ∀ (v : ℕ) (Ls : List TrioSeq), WordsG v Ls →
      BwT v (List.replicate n [((1, v + 1, 1) : ℕ × ℕ × ℕ)] ++ Ls)) (u : ℕ) :
    ∀ m, (((0, u, 0) : ℕ × ℕ × ℕ) :: towF (u + 1) n m) ∈ Wg (2 * u) := by
  have key : ∀ C, WordsG u [C] → (((0, u, 0) : ℕ × ℕ × ℕ) ::
      rword 0 u (List.replicate n [((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [C])) ∈ Wg (2 * u) := by
    intro C hC
    refine Wg_of_starOK ⟨?_, fun p hp => rword_ge 0 u _ p hp⟩
    have := hB u [C] hC u le_rfl
    rw [Nat.sub_self] at this
    simpa only [mlift_zero, List.map_id'] using this
  intro m
  cases m with
  | zero =>
      have := key [] (WordsG_consT (TF_nil u) (WordsG_nil u))
      rw [rword_rep_snoc] at this
      rw [towF]
      simpa [shiftr01] using this
  | succ m =>
      have hG := towF_GpT (farR_GpT n) m [] 1 (fun _ => 0) u (by simp) (by simp) le_rfl
      rw [liftOff_zeroF] at hG
      have := key _ (WordsG_consT (TF_tieG (u := u) (TF_nil u)
        (GF_of_GPF ⟨hG, Fr_towF m _ n⟩)) (WordsG_nil u))
      rw [rword_rep_snoc] at this
      rw [towF]
      simpa using this

theorem BwT_rep_succ {n : ℕ} (hB : ∀ (v : ℕ) (Ls : List TrioSeq), WordsG v Ls →
      BwT v (List.replicate n [((1, v + 1, 1) : ℕ × ℕ × ℕ)] ++ Ls)) (v : ℕ) :
    BwT v (List.replicate (n + 1) [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) := by
  intro u hu _ a ha
  have e : rword 0 u ((List.replicate (n + 1) [((1, v + 1, 1) : ℕ × ℕ × ℕ)]).map
      (fun X => mlift X v (u - v)))
      = (farR (u + 1) n ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp only [List.map_replicate, mlift_one_letter]
    rw [show v + 1 + (u - v) = u + 1 by omega, rword_rep]
    simp [farR]
  show (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u ((List.replicate (n + 1)
    [((1, v + 1, 1) : ℕ × ℕ × ℕ)]).map (fun X => mlift X v (u - v)))) ∈ Wg a
  rw [e]
  obtain ⟨hP, hcone⟩ := farR_P u n
  refine A1g_intro (Or.inr (Or.inl ⟨zcone_natDom hP (show 1 ≤ 2 by omega) hcone, fun k hk => ?_⟩))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [oper_zcone hP (show 1 ≤ 2 by omega) hcone (m + 1), farR_flat n m u]
  exact Wg_mono ha (towF_Wg hB u m)

/-- ★ 最上段の先頭に遠い語 n 個、そのあとに GT の語。 -/
theorem BwT_farN : ∀ (n v : ℕ) (Ls : List TrioSeq), WordsG v Ls →
    BwT v (List.replicate n [((1, v + 1, 1) : ℕ × ℕ × ℕ)] ++ Ls)
  | 0, v, Ls, h => by simpa using BwT_wordsG Ls h
  | n + 1, v, Ls, h => by
      induction Ls using List.reverseRecOn with
      | nil => simpa using BwT_rep_succ (BwT_farN n) v
      | append_singleton Ls K ih =>
          have hK := h K (by simp)
          rw [← List.append_assoc]
          refine hK.1 _ (fun X hX => ?_) (ih (fun X hX => h X (List.mem_append_left _ hX)))
          rcases List.mem_append.mp hX with hX | hX
          · rw [List.mem_replicate] at hX
            rw [hX.2]
            intro x hx; simp at hx; subst hx; show 1 ≤ 1; omega
          · exact (h X (List.mem_append_left _ hX)).2

theorem starOK_farN {v : ℕ} (n : ℕ) {Ls : List TrioSeq} (h : WordsG v Ls) :
    StarOK v (rword 0 v (List.replicate n [((1, v + 1, 1) : ℕ × ℕ × ℕ)] ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_farN n v Ls h v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end GzF
end TRIO
