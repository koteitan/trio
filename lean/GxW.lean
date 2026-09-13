/-
GxW.lean: 節点の下の語。

    BwN u Ls := ∀ σ ≥ 1, Gof σ u (rword 0 (u+σ) (Ls.map (mlift · (u+1) (σ-1))))

タイの下の字の潰れは、子の並びを段 u+1 で持ち上げた写しを行 1 が 1 ずつ上がる節点の入れ子に置く。
-/
import GxV

namespace TRIO
namespace GxW

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ
open GxD
open GxG
open GxJ
open GxK
open GxL
open GxN
open GxP
open GxR
open GxT
open GxV

/-! ## 低い段での持ち上げ -/

open Classical in
theorem mlift_cons_root' {X : TrioSeq} (hX : ∀ x ∈ X, 1 ≤ x.1) {b r : ℕ} (hr : b < r) (t z : ℕ) :
    mlift (((0, r, z) : ℕ × ℕ × ℕ) :: X) b t = ((0, r + t, z) : ℕ × ℕ × ℕ) :: mlift X b t := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [mlift_length] at hi
  rw [mlift_getD hi]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · have hc : coneV (((0, r, z) : ℕ × ℕ × ℕ) :: X) b 0 := by
      rw [coneV_iff_amin, amin_zero]; simpa [entry] using hr
    rw [if_pos hc]
    simp [entry]
  · obtain ⟨j, rfl⟩ : ∃ j, i = 1 + j := ⟨i - 1, by omega⟩
    have hj : j < X.length := by simp at hi; omega
    have e : ∀ q, entry (((0, r, z) : ℕ × ℕ × ℕ) :: X) q (1 + j) = entry X q j := by
      intro q; rw [show 1 + j = j + 1 by omega, entry_cons]
    rw [e 0, e 1, e 2]
    have eg : (((0, r + t, z) : ℕ × ℕ × ℕ) :: mlift X b t).getD (1 + j) (0, 0, 0)
        = (mlift X b t).getD j (0, 0, 0) := by
      rw [show 1 + j = j + 1 by omega]; rfl
    rw [eg, mlift_getD hj]
    have hiff := coneV_cons_iff (B := r) (z := z) (v := b) (fun p hp => hX p hp) hj
    by_cases hc : coneV X b j
    · rw [if_pos (hiff.mpr ⟨hr, hc⟩), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.mp h).2), if_neg hc]

theorem mlift_rcol' {X : TrioSeq} (hX : ∀ x ∈ X, 1 ≤ x.1) {b v : ℕ} (hb : b ≤ v) (t : ℕ) :
    mlift (rcol 0 v X) b t = rcol 0 (v + t) (mlift X b t) := by
  have e1 : rcol 0 v X = shiftr01 1 0 (((0, v + 1, 1) : ℕ × ℕ × ℕ) :: X) := by
    simp [rcol, shiftr01]
  have e2 : rcol 0 (v + t) (mlift X b t)
      = shiftr01 1 0 (((0, v + t + 1, 1) : ℕ × ℕ × ℕ) :: mlift X b t) := by
    simp [rcol, shiftr01]
  rw [e1, e2, mlift_shift0, mlift_cons_root' hX (show b < v + 1 by omega),
    show v + 1 + t = v + t + 1 by omega]

theorem mlift_rword' {b v : ℕ} (hb : b ≤ v) (t : ℕ) : ∀ (L : List TrioSeq),
    (∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) →
    mlift (rword 0 v L) b t = rword 0 (v + t) (L.map (fun X => mlift X b t))
  | [], _ => by simp [rword, mlift]
  | (X :: L'), hL => by
      rw [rword_cons, List.map_cons, rword_cons]
      have hrs : ∀ x ∈ rcol 0 v X, entry (rword 0 v L') 0 0 ≤ x.1 := by
        intro x hx
        have h1 := rcol_ge 0 v X x hx
        cases L' with
        | nil => simp [rword, entry]
        | cons Y L'' => rw [rword_cons]; simp [rcol, entry]; omega
      rw [mlift_append hrs, mlift_rcol' (hL X (by simp)) hb,
        mlift_rword' hb t L' (fun Y hY => hL Y (List.mem_cons_of_mem _ hY))]

/-- 段 u と段 u+1 の持ち上げの入れ替え。 -/
theorem mlift_comm (X : TrioSeq) (u s d : ℕ) :
    mlift (mlift X (u + 1) s) u d = mlift (mlift X u d) (u + 1 + d) s := by
  rw [mlift_eq_slift, mlift_eq_slift, mlift_eq_slift, mlift_eq_slift,
    slift_slift (stair_step (u + 1) s) (stair_step u d),
    slift_slift (stair_step u d) (stair_step (u + 1 + d) s)]
  congr 1
  funext m
  split_ifs <;> omega

#print axioms mlift_comm


theorem coneV_top1 {K : TrioSeq} (hK : Fr K) {u r : ℕ} (hr : u < r) :
    coneV (K ++ [((1, r, 1) : ℕ × ℕ × ℕ)]) u K.length := by
  intro y hy
  have hyle := rtg0_le hy
  rcases Nat.lt_or_ge y K.length with hlt | hge
  · exfalso
    have hrec := rtg0_rec hy K.length hlt le_rfl
    rw [Small.entry_append_left hlt, show K.length = K.length + 0 from rfl,
      entry_append_right] at hrec
    have h1 := getD_row0_ge hK hlt
    have e : entry [((1, r, 1) : ℕ × ℕ × ℕ)] 0 0 = 1 := rfl
    rw [e] at hrec
    omega
  · have hy' : y = K.length := by simp at hyle; omega
    subst hy'
    rw [show K.length = K.length + 0 from rfl, entry_append_right]
    show u < r; exact hr

/-! ## 節点の下の語 -/

def WF (Ls : List TrioSeq) : Prop := ∀ X ∈ Ls, ∀ x ∈ X, 1 ≤ x.1

def BwN (u : ℕ) (Ls : List TrioSeq) : Prop :=
  ∀ σ, 1 ≤ σ → Gof σ u (rword 0 (u + σ) (Ls.map (fun X => mlift X (u + 1) (σ - 1))))

theorem Fr_rword (v : ℕ) (Ls : List TrioSeq) : Fr (rword 0 v Ls) :=
  fun x hx => rword_ge 0 v Ls x hx

theorem BwN_nil (u : ℕ) : BwN u [] := by
  intro σ hσ
  simp only [List.map_nil, rword_nil]
  rcases Nat.eq_or_lt_of_le hσ with h | h
  · subst h; exact (Gof_one_iff u []).mpr (GTs_nil u)
  · exact Gof_nil (by omega) u

theorem BwN_snocz {u : ℕ} {Ls : List TrioSeq} (hL : WF Ls) (hB : BwN u Ls) :
    BwN u (Ls ++ [[]]) := by
  intro σ hσ
  rw [List.map_append, List.map_singleton, mlift_nil, rword_append, rword_singleton]
  have erc : rcol 0 (u + σ) ([] : TrioSeq) = [((1, u + σ + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [rcol, shiftr01]
  rw [erc, Gof_eq]
  intro Q hQ hF u' hu X hX hQX
  obtain ⟨d, hd⟩ : ∃ d, d = u' - u := ⟨_, rfl⟩
  rw [← hd]
  have hLσ : WF (Ls.map (fun X => mlift X (u + 1) (σ - 1))) := mlift_map_ge hL (u + 1) (σ - 1)
  -- 基準 u' での語の型紙
  obtain ⟨T, hT⟩ : ∃ T : ℕ → List TrioSeq,
      T = fun τ => Ls.map (fun X => mlift (mlift X u d) (u' + 1) (τ - 1)) := ⟨_, rfl⟩
  have hTWF : ∀ τ, WF (T τ) := by
    intro τ X hX
    rw [hT] at hX
    simp only [List.mem_map] at hX
    obtain ⟨Y, hY, rfl⟩ := hX
    exact mlift_ge (mlift_ge (hL Y hY) u d) (u' + 1) (τ - 1)
  have eLift : ∀ τ, 1 ≤ τ →
      (Ls.map (fun X => mlift X (u + 1) (τ - 1))).map (fun X => mlift X u d) = T τ := by
    intro τ _
    rw [hT, List.map_map]
    apply List.map_congr_left
    intro X _
    simp only [Function.comp_apply]
    rw [mlift_comm, show u + 1 + d = u' + 1 by omega]
  have eStep : ∀ τ, 1 ≤ τ → (T τ).map (fun X => mlift X (u' + τ) 1) = T (τ + 1) := by
    intro τ hτ
    rw [hT, List.map_map]
    apply List.map_congr_left
    intro X _
    simp only [Function.comp_apply]
    have := mlift_mlift (mlift X u d) (u' + 1) (τ - 1) 1
    rw [show u' + 1 + (τ - 1) = u' + τ by omega, show τ - 1 + 1 = τ + 1 - 1 by omega] at this
    exact this
  have hBase : ∀ τ, 1 ≤ τ → Gof τ u' (rword 0 (u' + τ) (T τ)) := by
    intro τ hτ
    have h1 := (Gof_ax hτ).lift u _ (Fr_rword _ _) (hB τ hτ) u' hu
    rw [← hd, mlift_rword' (by omega) d _ (mlift_map_ge hL (u + 1) (τ - 1)), eLift τ hτ,
      show u + τ + d = u' + τ by omega] at h1
    exact h1
  have claim : ∀ m τ, 1 ≤ τ →
      Gof τ u' (rword 0 (u' + τ) (T τ) ++
        shiftr01 1 0 (PzW (u' + τ + 1) (T (τ + 1)) m)) := by
    intro m
    induction m with
    | zero =>
        intro τ hτ
        simp only [PzW, List.range_zero, List.flatMap_nil, shiftr01, List.map_nil, List.append_nil]
        exact hBase τ hτ
    | succ m ih =>
        intro τ hτ
        rw [PzW_succ, show u' + τ + 1 = u' + (τ + 1) by omega, eStep (τ + 1) (by omega)]
        have eS : shiftr01 1 0 (((0, u' + (τ + 1), 0) : ℕ × ℕ × ℕ) ::
            (rword 0 (u' + (τ + 1)) (T (τ + 1)) ++
              shiftr01 1 0 (PzW (u' + (τ + 1) + 1) (T (τ + 1 + 1)) m)))
            = ((1, u' + (τ + 1), 0) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (rword 0 (u' + (τ + 1)) (T (τ + 1)) ++
                shiftr01 1 0 (PzW (u' + (τ + 1) + 1) (T (τ + 1 + 1)) m)) := by
          simp [shiftr01]
        rw [eS]
        exact Gof_node (ρ := τ) (σ := τ + 1) hτ (by omega) (Fr_rword _ _) (hBase τ hτ)
          (ih (τ + 1) (by omega))
  -- 最後の字の単位
  have hcA : coneV (rword 0 (u + σ) (Ls.map (fun X => mlift X (u + 1) (σ - 1))) ++
      [((1, u + σ + 1, 1) : ℕ × ℕ × ℕ)]) u
      (rword 0 (u + σ) (Ls.map (fun X => mlift X (u + 1) (σ - 1)))).length :=
    coneV_top1 (Fr_rword _ _) (by omega)
  rw [mlift_snoc_cone _ _ hcA d, mlift_rword' (by omega) d _ hLσ, eLift σ hσ]
  have eL1 : (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ).1, ((1, u + σ + 1, 1) : ℕ × ℕ × ℕ).2.1 + d,
      ((1, u + σ + 1, 1) : ℕ × ℕ × ℕ).2.2) = ((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ) := by
    show ((1, u + σ + 1 + d, 1) : ℕ × ℕ × ℕ) = _
    rw [show u + σ + 1 + d = u' + σ + 1 by omega]
  rw [eL1, show u + σ + d = u' + σ by omega]
  obtain ⟨V, hV⟩ : ∃ V : TrioSeq, V = (((0, u' + σ, 0) : ℕ × ℕ × ℕ) :: rword 0 (u' + σ) (T σ)) ++
      [((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  have eU : ((1, u' + σ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (rword 0 (u' + σ) (T σ) ++
      [((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ)]) = shiftr01 1 0 V := by
    rw [hV]; simp [shiftr01]
  rw [eU]
  have hlen : 2 ≤ V.length := by rw [hV]; simp
  have hpV : hasParent V (srow V (V.length - 1)) (V.length - 1) := by
    have hn := natDom_zroot (u' + σ) (X := rword 0 (u' + σ) (T σ)) (rword_ge 0 _ _)
    rw [← hV] at hn
    rcases natDom_iff.mp hn with h | h
    · exfalso
      have hl : V.length - 1 = (((0, u' + σ, 0) : ℕ × ℕ × ℕ) :: rword 0 (u' + σ) (T σ)).length + 0 := by
        rw [hV]; simp
      rw [hl] at h
      unfold lev at h
      rw [hV, entry_append_right, entry_append_right] at h
      simp [entry] at h
    · exact h
  refine hQ.oper u' X (shiftr01 1 0 V) hX (Fr_shift1 V)
    (fun _ => by rw [entry0_shiftr01 (by rw [hV]; simp), hV]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] V 1 m hlen hpV
  simp only [List.nil_append] at eO
  rw [eO, hV, oper_zword (u' + σ) (T σ) (hTWF σ) m]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [PzW_succ, eStep σ hσ]
  have eS : shiftr01 1 0 (((0, u' + σ, 0) : ℕ × ℕ × ℕ) ::
      (rword 0 (u' + σ) (T σ) ++ shiftr01 1 0 (PzW (u' + σ + 1) (T (σ + 1)) m')))
      = ((1, u' + σ, 0) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (rword 0 (u' + σ) (T σ) ++ shiftr01 1 0 (PzW (u' + σ + 1) (T (σ + 1)) m')) := by
    simp [shiftr01]
  rw [eS]
  have h := (Gof_eq σ u' _).mp (claim m' σ hσ) Q hQ hF u' le_rfl X hX hQX
  rwa [Nat.sub_self, mlift_zero] at h

#print axioms BwN_snocz


/-! ## 節点の下の字の中身 -/

def GTN (u : ℕ) (K : TrioSeq) : Prop := ∀ Ls, WF Ls → BwN u Ls → BwN u (Ls ++ [K])

theorem rword_snocT (v : ℕ) (Ls : List TrioSeq) (f : TrioSeq → TrioSeq) (K : TrioSeq) :
    rword 0 v ((Ls ++ [K]).map f)
      = rword 0 v (Ls.map f) ++ ((1, v + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (f K) := by
  rw [List.map_append, List.map_singleton, rword_append, rword_singleton]
  simp [rcol]

theorem Fr_letter (r : ℕ) (W : TrioSeq) : Fr (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 W) := by
  intro x hx
  simp only [List.mem_cons, shiftr01, List.mem_map] at hx
  rcases hx with rfl | ⟨p, -, rfl⟩
  · show 1 ≤ 1; omega
  · dsimp only; omega

theorem Hd_letter (r : ℕ) (W : TrioSeq) : Hd (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 W) :=
  fun _ => rfl

theorem GTN_oper {u : ℕ} {K U : TrioSeq} (hK : Fr K) (hH : Hd U) (hlen : 2 ≤ U.length)
    (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → GTN u (K ++ U⟦m⟧)) : GTN u (K ++ U) := by
  intro Ls hL hB σ hσ
  have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  rw [rword_snocT, mlift_app hK hH]
  have hlen' : 2 ≤ (mlift U (u + 1) (σ - 1)).length := by rw [mlift_length]; exact hlen
  have hUlne : mlift U (u + 1) (σ - 1) ≠ [] := by
    intro h; have := congrArg List.length h; rw [mlift_length, List.length_nil] at this; omega
  have hp' := (hasParent_mlift_iff (u + 1) (σ - 1) hUne).mpr hp
  refine (Gof_ax hσ).oper u _ _ (Fr_rword _ _) (Fr_letter _ _) (Hd_letter _ _)
    (by simp only [List.length_cons, List.length_append, shiftr01_length]; omega)
    (node_hasParent _ _ _ hp' hUlne) (fun m hm => ?_)
  rw [node_oper _ _ _ hlen' hp' m, mlift_oper', ← mlift_app hK (Hd_oper hH hUne hm)]
  have h := hIH m hm Ls hL hB σ hσ
  rwa [rword_snocT] at h

theorem GTN_flat {u : ℕ} {K : TrioSeq} (hK : Fr K) (h : GTN u K) :
    GTN u (K ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := by
  intro Ls hL hB σ hσ
  have hrep : ∀ m, BwN u (Ls ++ List.replicate m K) := by
    intro m
    induction m with
    | zero => simpa using hB
    | succ m ih =>
        have hW : WF (Ls ++ List.replicate m K) := by
          intro X hX
          rcases List.mem_append.mp hX with hX | hX
          · exact hL X hX
          · rw [List.eq_of_mem_replicate hX]; exact hK
        have := h _ hW ih
        rwa [List.append_assoc, ← List.replicate_succ'] at this
  rw [rword_snocT, mlift_snoc_flat K 1 (u + 1) (σ - 1) hK]
  obtain ⟨M, hM⟩ : ∃ M : TrioSeq,
      M = ((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift K (u + 1) (σ - 1)) := ⟨_, rfl⟩
  have eV : ((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (mlift K (u + 1) (σ - 1) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
      = M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
    rw [hM, node_split, shift_col]
  rw [eV]
  have hMne : M ≠ [] := by rw [hM]; simp
  have hMl : 1 ≤ M.length := by rw [hM]; simp
  have hhead : entry M 0 0 < 2 := by rw [hM]; show 1 < 2; omega
  have htail : ∀ r, 1 ≤ r → r < M.length → 2 ≤ entry M 0 r := by
    intro r hr1 hr2
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hr' : r' < (mlift K (u + 1) (σ - 1)).length := by
      rw [hM] at hr2; simp only [List.length_cons, shiftr01_length] at hr2; omega
    rw [hM, entry_cons, entry0_shiftr01 hr']
    have := getD_row0_ge (Fr_mlift hK (u + 1) (σ - 1)) hr'
    omega
  have hpV : hasParent (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)])
      (srow (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1))
      ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
    have hidx : (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1 = M.length + 0 := by simp
    rw [hidx, srow_append_right]
    have hs : srow [((2, 0, 0) : ℕ × ℕ × ℕ)] 0 = 0 := rfl
    rw [hs]
    refine (hasParent_zero_iff (by first | omega | (simp; omega) | simp)).mpr
      ⟨0, by first | omega | (simp; omega) | simp, ?_⟩
    rw [Small.entry_append_left (by omega), entry_append_right]
    exact hhead
  refine (Gof_ax hσ).oper u _ (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) (Fr_rword _ _)
    (Fr_append (by rw [hM]; exact Fr_letter _ _)
      (by intro y hy; simp at hy; subst hy; show 1 ≤ 2; omega))
    (fun _ => by rw [hM]; rfl) (by simp only [List.length_append, List.length_singleton]; omega)
    hpV (fun m _ => ?_)
  have eO := oper_snoc00'' [] hMne hhead htail m
  simp only [List.nil_append] at eO
  rw [eO]
  have h2 := hrep m σ hσ
  rw [List.map_append, rword_append, List.map_replicate, rword_replicate] at h2
  have er : rcol 0 (u + σ) (mlift K (u + 1) (σ - 1)) = M := by rw [hM]; simp [rcol]
  rwa [er] at h2

#print axioms GTN_flat


theorem BwN_lift {u : ℕ} {Ls : List TrioSeq} (hL : WF Ls) (hB : BwN u Ls) {u' : ℕ} (hu : u ≤ u') :
    BwN u' (Ls.map (fun X => mlift X u (u' - u))) := by
  intro σ hσ
  have h1 := (Gof_ax hσ).lift u _ (Fr_rword _ _) (hB σ hσ) u' hu
  rw [mlift_rword' (by omega) (u' - u) _ (mlift_map_ge hL (u + 1) (σ - 1)),
    show u + σ + (u' - u) = u' + σ by omega] at h1
  have e : (Ls.map (fun X => mlift X (u + 1) (σ - 1))).map (fun X => mlift X u (u' - u))
      = (Ls.map (fun X => mlift X u (u' - u))).map (fun X => mlift X (u' + 1) (σ - 1)) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro X _
    simp only [Function.comp_apply]
    rw [mlift_comm, show u + 1 + (u' - u) = u' + 1 by omega]
  rwa [e] at h1

theorem WF_lift {Ls : List TrioSeq} (hL : WF Ls) (u t : ℕ) : WF (Ls.map (fun X => mlift X u t)) :=
  mlift_map_ge hL u t

/-- 字 (1, r, 1) :: A↑1 の後ろに B↑1 を足した列で、A↑1 の列は B↑1 の列の祖先にならない。 -/
theorem letter_anc_row1 {r : ℕ} {A B : TrioSeq} (hA : Fr A) (hBH : Hd B) (hBne : B ≠ [])
    {k b : ℕ} (hk : k < ((((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 A)).length)
    (hb : b < (shiftr01 1 0 B).length)
    (h : Relation.ReflTransGen (nextrel0 ((((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 A) ++
      shiftr01 1 0 B)) k ((((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 A).length + b)) :
    k = 0 := by
  by_contra hk0
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hrec := rtg0_rec h ((((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 A)).length hk (by omega)
  rw [Small.entry_append_left hk, show ((((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 A)).length
      = ((((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 A)).length + 0 from rfl,
    entry_append_right, entry_cons] at hrec
  have hk' : k' < A.length := by simp [shiftr01] at hk; omega
  have hBl : 0 < B.length := List.length_pos_iff.mpr hBne
  rw [entry0_shiftr01 hk', entry0_shiftr01 hBl, hBH hBne] at hrec
  have := getD_row0_ge hA hk'
  omega

#print axioms BwN_lift


theorem coneV_mlift_up {A : TrioSeq} {u j : ℕ} (hj : j < A.length) (hc : coneV A u j) (b t : ℕ) :
    coneV (mlift A b t) u j := by
  rw [coneV_iff_amin] at hc ⊢
  rw [mlift_eq_slift, amin_slift (stair_step b t) hj]
  have := (stair_step b t).ge (amin A j)
  omega

theorem mlift_letter {u r : ℕ} (hr : u < r) {V : TrioSeq} (hV : Fr V) (t : ℕ) :
    mlift (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V) u t
      = ((1, r + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift V u t) := by
  have e1 : ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V
      = shiftr01 1 0 (((0, r, 1) : ℕ × ℕ × ℕ) :: V) := by simp [shiftr01]
  have e2 : ((1, r + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift V u t)
      = shiftr01 1 0 (((0, r + t, 1) : ℕ × ℕ × ℕ) :: mlift V u t) := by simp [shiftr01]
  rw [e1, e2, mlift_shift0, mlift_cons_root hV hr]

theorem GTN_orph {u : ℕ} {K U : TrioSeq} {h j : ℕ} (hK : Fr K)
    (hU : Fr (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
    (hj1 : 1 ≤ j) (hj : j ≤ u)
    (hnp : ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z → GTN u (K ++ (U ++ shiftr01 h 0 z))) :
    GTN u (K ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
  intro Ls hL hB σ hσ
  have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u + 1 := by show j ≤ u + 1; omega
  have eL : mlift (K ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (u + 1) (σ - 1)
      = mlift K (u + 1) (σ - 1) ++ (mlift U (u + 1) (σ - 1) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_app hK hH, mlift_snoc_low U _ hc]
  rw [rword_snocT, eL]
  have eV : ((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift K (u + 1) (σ - 1) ++ (mlift U (u + 1) (σ - 1) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
      = (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift K (u + 1) (σ - 1) ++ mlift U (u + 1) (σ - 1)))
        ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by
    rw [← List.append_assoc, shiftr01_append0, shift_col]; rfl
  rw [eV]
  refine (Gof_ax hσ).orph u _ _ (h + 1) j (Fr_rword _ _) (by rw [← eV]; exact Fr_letter _ _)
    (by rw [← eV]; exact Hd_letter _ _) hj1 hj ?_ (fun z hz' hbz => ?_)
  · have eAB : (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift K (u + 1) (σ - 1) ++ mlift U (u + 1) (σ - 1)))
          ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]
        = (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift K (u + 1) (σ - 1))) ++
          shiftr01 1 0 (mlift U (u + 1) (σ - 1) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      rw [← eV, node_split]
    have eidx : (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift K (u + 1) (σ - 1) ++ mlift U (u + 1) (σ - 1))).length
        = (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift K (u + 1) (σ - 1))).length +
          (mlift U (u + 1) (σ - 1)).length := by simp [shiftr01]; omega
    rw [eAB, eidx]
    have hBH : Hd (mlift U (u + 1) (σ - 1) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      rw [← mlift_snoc_low U _ hc]; exact Hd_mlift hH _ _
    refine noParent_ctx (j := j) (by simp [shiftr01]) (fun k' hk' hrt => ?_) ?_ ?_
    · have := letter_anc_row1 (Fr_mlift hK (u + 1) (σ - 1)) hBH (by simp) hk' (by simp [shiftr01]) hrt
      subst this
      show j ≤ u + σ + 1
      omega
    · rw [entry1_shiftr01, show (mlift U (u + 1) (σ - 1)).length = (mlift U (u + 1) (σ - 1)).length + 0
        from rfl, entry_append_right]; rfl
    · intro hh
      apply hnp
      rw [hasParent_shiftr01, ← mlift_snoc_low U _ hc, mlift_eq_slift,
        hasParent_slift (stair_step (u + 1) (σ - 1)), mlift_length] at hh
      exact hh
  · have hzz := hz z hz' hbz Ls hL hB σ hσ
    rw [rword_snocT] at hzz
    have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
    have hHz : Hd (U ++ shiftr01 h 0 z) := by
      intro hne
      by_cases hUn : U = []
      · subst hUn
        have hh1 : h = 1 := by have := hH (by simp); simpa [entry] using this
        have hzne : z ≠ [] := by intro hz0; apply hne; subst hz0; rfl
        simp only [List.nil_append]
        rw [entry0_shiftr01 (List.length_pos_iff.mpr hzne), show entry z 0 0 = 0 from hbz, hh1]
      · rw [Small.entry_append_left (List.length_pos_iff.mpr hUn)]
        have := hH (by simp)
        rwa [Small.entry_append_left (List.length_pos_iff.mpr hUn)] at this
    rw [mlift_app hK hHz, mlift_append_low (low_of_Wg hzW h (by omega))] at hzz
    rw [show (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift K (u + 1) (σ - 1) ++ mlift U (u + 1) (σ - 1))) ++ shiftr01 (h + 1) 0 z
        = ((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift K (u + 1) (σ - 1) ++
            (mlift U (u + 1) (σ - 1) ++ shiftr01 h 0 z)) by
      rw [← List.append_assoc, shiftr01_append0 _ (mlift K (u + 1) (σ - 1) ++ mlift U (u + 1) (σ - 1)),
        shiftr01_add0]; rfl]
    exact hzz

#print axioms GTN_orph

theorem GTN_tie {u : ℕ} {K U : TrioSeq} {x : ℕ} (hK : Fr K)
    (hU : Fr (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u U.length)
    (hload : ∀ u', u ≤ u' → ∀ Z ∈ Wg (2 * u'), based Z →
      GTN u' (mlift (K ++ U) u (u' - u) ++ shiftr01 x 0 Z)) :
    GTN u (K ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])) := by
  intro Ls hL hB σ hσ
  have hcl : (((x, u + 1, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u + 1 := le_rfl
  have eL : mlift (K ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])) (u + 1) (σ - 1)
      = mlift K (u + 1) (σ - 1) ++ (mlift U (u + 1) (σ - 1) ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_app hK hH, mlift_snoc_low U _ hcl]
  rw [rword_snocT, eL]
  have eV : ((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift K (u + 1) (σ - 1) ++ (mlift U (u + 1) (σ - 1) ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]))
      = (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift K (u + 1) (σ - 1) ++ mlift U (u + 1) (σ - 1)))
        ++ [((x + 1, u + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [← List.append_assoc, shiftr01_append0, shift_col]; rfl
  rw [eV]
  have hHU : Hd U := by
    intro hne
    have := hH (by simp)
    rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
  refine (Gof_ax hσ).tie u _ _ (x + 1) (Fr_rword _ _) (by rw [← eV]; exact Fr_letter _ _)
    (by rw [← eV]; exact Hd_letter _ _) ?_ (fun u'' hu'' Z hZ hbZ => ?_)
  · have eAB : (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift K (u + 1) (σ - 1) ++ mlift U (u + 1) (σ - 1)))
          ++ [((x + 1, u + 1, 0) : ℕ × ℕ × ℕ)]
        = (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift K (u + 1) (σ - 1))) ++
          shiftr01 1 0 (mlift U (u + 1) (σ - 1) ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) := by
      rw [← eV, node_split]
    have eidx : (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift K (u + 1) (σ - 1) ++ mlift U (u + 1) (σ - 1))).length
        = (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift K (u + 1) (σ - 1))).length +
          (mlift U (u + 1) (σ - 1)).length := by simp [shiftr01]; omega
    rw [eAB, eidx]
    have hPCA : PathCone u 1 (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift K (u + 1) (σ - 1))) := by
      intro y hy _ hd
      rcases y with _ | y
      · show u < u + σ + 1; omega
      · exfalso
        rw [entry_cons] at hd
        have hy' : y < (mlift K (u + 1) (σ - 1)).length := by
          rw [mlift_length]; simp [shiftr01] at hy; omega
        rw [entry0_shiftr01 hy'] at hd
        have := getD_row0_ge (Fr_mlift hK (u + 1) (σ - 1)) hy'
        omega
    have hB0 : shiftr01 1 0 (mlift U (u + 1) (σ - 1) ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) ≠ [] →
        entry (shiftr01 1 0 (mlift U (u + 1) (σ - 1) ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])) 0 0 = 1 + 1 := by
      intro _
      have hBH : Hd (mlift U (u + 1) (σ - 1) ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) := by
        have := Hd_mlift hH (u + 1) (σ - 1)
        rwa [mlift_snoc_low U _ hcl] at this
      rw [entry0_shiftr01 (by simp), hBH (by simp)]
    rw [coneV_pathB hPCA hB0 (by simp [shiftr01]), coneV_shift0]
    have := coneV_mlift_up (by simp) hc (u + 1) (σ - 1)
    rwa [mlift_snoc_low U _ hcl, ← mlift_length U (u + 1) (σ - 1)] at this
  · have h1 := hload u'' hu'' Z hZ hbZ (Ls.map (fun X => mlift X u (u'' - u))) (WF_lift hL u _)
      (BwN_lift hL hB hu'') σ hσ
    rw [rword_snocT, mlift_append_low (low_of_Wg hZ x (by omega))] at h1
    have hWU : Fr (mlift K (u + 1) (σ - 1) ++ mlift U (u + 1) (σ - 1)) :=
      Fr_append (Fr_mlift hK _ _) (Fr_mlift (fun y hy => hU y (List.mem_append_left _ hy)) _ _)
    have eW : mlift (rword 0 (u + σ) (Ls.map (fun X => mlift X (u + 1) (σ - 1)))) u (u'' - u)
        = rword 0 (u'' + σ) ((Ls.map (fun X => mlift X u (u'' - u))).map
            (fun X => mlift X (u'' + 1) (σ - 1))) := by
      rw [mlift_rword' (by omega) (u'' - u) _ (mlift_map_ge hL (u + 1) (σ - 1)),
        show u + σ + (u'' - u) = u'' + σ by omega, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro X _
      simp only [Function.comp_apply]
      rw [mlift_comm, show u + 1 + (u'' - u) = u'' + 1 by omega]
    have eKU : mlift (mlift K (u + 1) (σ - 1) ++ mlift U (u + 1) (σ - 1)) u (u'' - u)
        = mlift (mlift (K ++ U) u (u'' - u)) (u'' + 1) (σ - 1) := by
      rw [← mlift_app hK hHU, mlift_comm, show u + 1 + (u'' - u) = u'' + 1 by omega]
    rw [mlift_app (Fr_rword _ _) (Hd_letter _ _), eW, mlift_letter (by omega) hWU, eKU,
      show u + σ + 1 + (u'' - u) = u'' + σ + 1 by omega, List.append_assoc]
    rw [shiftr01_append0, shiftr01_add0] at h1
    simpa [List.append_assoc] using h1

#print axioms GTN_tie


/-! ## 全ての段での字の中身と差し込み口の公理 -/

def GTNall (u : ℕ) (K : TrioSeq) : Prop := ∀ u', u ≤ u' → GTN u' (mlift K u (u' - u))

theorem GTNall_nil (u : ℕ) : GTNall u [] := by
  intro u' _
  rw [mlift_nil]
  intro Ls hL hB
  exact BwN_snocz hL hB

theorem GTNall_ax : SlotAx GTNall where
  lift := by
    intro u W _ h u' hu u'' hu''
    have e := mlift_mlift W u (u' - u) (u'' - u')
    rw [show u + (u' - u) = u' by omega, show u' - u + (u'' - u') = u'' - u by omega] at e
    rw [e]
    exact h u'' (le_trans hu hu'')
  oper := by
    intro u W U hW hU hH hlen hp hIH u' hu
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    rw [mlift_app hW hH u (u' - u)]
    have hlen' : 2 ≤ (mlift U u (u' - u)).length := by rw [mlift_length]; exact hlen
    have hp' := (hasParent_mlift_iff u (u' - u) hUne).mpr hp
    refine GTN_oper (Fr_mlift hW _ _) (Hd_mlift hH _ _) hlen' hp' (fun m hm => ?_)
    rw [mlift_oper', ← mlift_app hW (Hd_oper hH hUne hm)]
    exact hIH m hm u' hu
  orph := by
    intro u W U h j hW hU hH hj1 hj hnp hz u' hu
    have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u := hj
    have eL : mlift (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) u (u' - u)
        = mlift W u (u' - u) ++ (mlift U u (u' - u) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      rw [mlift_app hW hH, mlift_snoc_low U _ hc]
    rw [eL]
    refine GTN_orph (Fr_mlift hW _ _) (by rw [← mlift_snoc_low U _ hc]; exact Fr_mlift hU _ _)
      (by rw [← mlift_snoc_low U _ hc]; exact Hd_mlift hH _ _) hj1 (le_trans hj hu) ?_
      (fun z hz' hbz => ?_)
    · intro hh
      apply hnp
      have hl : U.length = (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1 := by simp
      rw [hl]
      rw [← mlift_snoc_low U _ hc, mlift_eq_slift, show (mlift U u (u' - u)).length
        = (slift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) (fun m => m + (if u < m then (u' - u) else 0))).length - 1
        by simp, hasParent_slift (stair_step u (u' - u))] at hh
      rwa [slift_length] at hh
    · have hzz := hz z hz' hbz u' hu
      have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
      have hHz : Hd (U ++ shiftr01 h 0 z) := by
        intro hne
        by_cases hUn : U = []
        · subst hUn
          have hh1 : h = 1 := by have := hH (by simp); simpa [entry] using this
          have hzne : z ≠ [] := by intro hz0; apply hne; subst hz0; rfl
          simp only [List.nil_append]
          rw [entry0_shiftr01 (List.length_pos_iff.mpr hzne), show entry z 0 0 = 0 from hbz, hh1]
        · rw [Small.entry_append_left (List.length_pos_iff.mpr hUn)]
          have := hH (by simp)
          rwa [Small.entry_append_left (List.length_pos_iff.mpr hUn)] at this
      rw [mlift_app hW hHz, mlift_append_low (low_of_Wg hzW h hj)] at hzz
      exact hzz
  tie := by
    intro u W U x hW hU hH hc hload u' hu
    have eL : mlift (W ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])) u (u' - u)
        = mlift W u (u' - u) ++ (mlift U u (u' - u) ++ [((x, u' + 1, 0) : ℕ × ℕ × ℕ)]) := by
      rw [mlift_app hW hH, mlift_snoc_cone U _ hc]
      show _ ++ (_ ++ [((x, u + 1 + (u' - u), 0) : ℕ × ℕ × ℕ)]) = _
      rw [show u + 1 + (u' - u) = u' + 1 by omega]
    rw [eL]
    have hHU : Hd U := by
      intro hne
      have := hH (by simp)
      rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
    have hU' : Fr (mlift U u (u' - u) ++ [((x, u' + 1, 0) : ℕ × ℕ × ℕ)]) := by
      have := Fr_mlift hU u (u' - u)
      rwa [mlift_snoc_cone U _ hc, show u + 1 + (u' - u) = u' + 1 by omega] at this
    have hH' : Hd (mlift U u (u' - u) ++ [((x, u' + 1, 0) : ℕ × ℕ × ℕ)]) := by
      have := Hd_mlift hH u (u' - u)
      rwa [mlift_snoc_cone U _ hc, show u + 1 + (u' - u) = u' + 1 by omega] at this
    have hc' : coneV (mlift U u (u' - u) ++ [((x, u' + 1, 0) : ℕ × ℕ × ℕ)]) u'
        (mlift U u (u' - u)).length := by
      have := coneV_mlift (by simp) hc (u' - u)
      rwa [mlift_snoc_cone U _ hc, show u + 1 + (u' - u) = u' + 1 by omega,
        show u + (u' - u) = u' by omega, ← mlift_length U u (u' - u)] at this
    refine GTN_tie (Fr_mlift hW _ _) hU' hH' hc' (fun u'' hu'' Z hZ hbZ => ?_)
    have h1 := hload u'' (le_trans hu hu'') Z hZ hbZ u'' le_rfl
    rw [Nat.sub_self, mlift_zero] at h1
    have e1 : mlift (mlift W u (u' - u) ++ mlift U u (u' - u)) u' (u'' - u')
        = mlift (W ++ U) u (u'' - u) := by
      rw [← mlift_app hW hHU]
      have e := mlift_mlift (W ++ U) u (u' - u) (u'' - u')
      rw [show u + (u' - u) = u' by omega, show u' - u + (u'' - u') = u'' - u by omega] at e
      exact e
    rw [e1]
    exact h1
  flat := by
    intro u W hW h u' hu
    rw [mlift_snoc_flat W 1 u (u' - u) hW]
    exact GTN_flat (Fr_mlift hW _ _) (h u' hu)

#print axioms GTNall_ax

theorem GTN_of_GTNall {u : ℕ} {K : TrioSeq} (h : GTNall u K) : GTN u K := by
  have := h u le_rfl
  rwa [Nat.sub_self, mlift_zero] at this

theorem GTNall_load {u : ℕ} {K : TrioSeq} (hK : Fr K) (h : GTNall u K) {Z : TrioSeq}
    (hZ : Z ∈ Wg (2 * u)) (hb : based Z) : GTNall u (K ++ shiftr01 1 0 Z) :=
  slot_load GTNall_ax hK h Z hZ hb

theorem GTNall_tie {u : ℕ} {K D : TrioSeq} (hK : Fr K) (h : GTNall u K) (hD : GTs u D) :
    GTNall u (K ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) := by
  have := hD GTNall GTNall_ax u le_rfl K hK h
  rwa [Nat.sub_self, mlift_zero] at this

/-- タイの子が語のとき。 -/
theorem GTs_of_BwN {u : ℕ} {Ls : List TrioSeq} (hB : BwN u Ls) : GTs u (rword 0 (u + 1) Ls) := by
  have := hB 1 le_rfl
  simp only [Nat.sub_self, mlift_zero, List.map_id'] at this
  exact (Gof_one_iff u _).mp this

/-- 行 1060 の試し。 -/
theorem R1060_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have hK : GTN 0 [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
    have := GTN_of_GTNall (GTNall_load Fr_nil (GTNall_nil 0) (Om_mem_Wg 0) rfl)
    simpa [shiftr01] using this
  have hB : BwN 0 [[((1, 0, 0) : ℕ × ℕ × ℕ)]] := by
    have := hK [] (fun _ h => by simp at h) (BwN_nil 0)
    simpa using this
  have hD := GTs_of_BwN hB
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0)
    (WordsG_consT (TF_tie (TF_nil 0) ⟨hD, Fr_rword _ _⟩) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

#print axioms R1060_mem


/-! ## 森の条件つきの組み立て -/

def GNF (u : ℕ) (K : TrioSeq) : Prop := GTNall u K ∧ Fr K

theorem GNF_nil (u : ℕ) : GNF u [] := ⟨GTNall_nil u, Fr_nil⟩

theorem GNF_load {u : ℕ} {K Z : TrioSeq} (h : GNF u K) (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    GNF u (K ++ shiftr01 1 0 Z) := ⟨GTNall_load h.2 h.1 hZ hb, Fr_append h.2 (Fr_shift1 Z)⟩

theorem GNF_tie {u : ℕ} {K D : TrioSeq} (h : GNF u K) (hD : GF 1 u D) :
    GNF u (K ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) :=
  ⟨GTNall_tie h.2 h.1 ((Gof_one_iff u D).mp hD.1), Fr_append h.2 (Fr_node _ _)⟩

def BWF (u : ℕ) (Ls : List TrioSeq) : Prop := BwN u Ls ∧ WF Ls

theorem BWF_nil (u : ℕ) : BWF u [] := ⟨BwN_nil u, fun _ h => by simp at h⟩

theorem BWF_snoc {u : ℕ} {Ls : List TrioSeq} {K : TrioSeq} (h : BWF u Ls) (hK : GNF u K) :
    BWF u (Ls ++ [K]) := by
  refine ⟨GTN_of_GTNall hK.1 Ls h.2 h.1, fun X hX => ?_⟩
  rcases List.mem_append.mp hX with hX | hX
  · exact h.2 X hX
  · simp only [List.mem_singleton] at hX; subst hX; exact hK.2

theorem GF_of_BWF {u : ℕ} {Ls : List TrioSeq} (h : BWF u Ls) : GF 1 u (rword 0 (u + 1) Ls) := by
  refine ⟨?_, Fr_rword _ _⟩
  have := h.1 1 le_rfl
  simpa only [Nat.sub_self, mlift_zero, List.map_id'] using this

end GxW
end TRIO
