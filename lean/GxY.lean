/-
GxY.lean: 基準 u+σ の持ち上げで作る型紙（錨つきの子の並び）。

    PV b σ W := ∀ t, Gof (σ+t) b (mlift W (b+σ) t)

σ 節点の下の字の潰れは基準 b+σ で持ち上げる。行 1 が b+σ 以下の列（σ 節点の写しを含む）は持ち上がらない。
-/
import GxW

namespace TRIO
namespace GxY

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
open GxW

theorem mlift_commk (X : TrioSeq) (u k s d : ℕ) :
    mlift (mlift X (u + k) s) u d = mlift (mlift X u d) (u + k + d) s := by
  rw [mlift_eq_slift, mlift_eq_slift, mlift_eq_slift, mlift_eq_slift,
    slift_slift (stair_step (u + k) s) (stair_step u d),
    slift_slift (stair_step u d) (stair_step (u + k + d) s)]
  congr 1
  funext m
  split_ifs <;> omega

def PV (b σ : ℕ) (W : TrioSeq) : Prop := ∀ t, Gof (σ + t) b (mlift W (b + σ) t)

/-- 任意の子の並びの後ろの空の字。 -/
theorem Gof_snocz_core {b σ : ℕ} (hσ : 1 ≤ σ) {W : TrioSeq} (hW : Fr W)
    (hPV : ∀ t, Gof (σ + t) b (mlift W (b + σ) t)) :
    Gof σ b (W ++ [((1, b + σ + 1, 1) : ℕ × ℕ × ℕ)]) := by
  rw [Gof_eq]
  intro Q hQ hF u' hu X hX hQX
  obtain ⟨d, hd⟩ : ∃ d, d = u' - b := ⟨_, rfl⟩
  rw [← hd]
  obtain ⟨V, hV⟩ : ∃ V : ℕ → TrioSeq, V = fun τ => mlift (mlift W b d) (u' + σ) (τ - σ) :=
    ⟨_, rfl⟩
  have hVFr : ∀ τ, Fr (V τ) := fun τ => by rw [hV]; exact Fr_mlift (Fr_mlift hW _ _) _ _
  have hBase : ∀ τ, σ ≤ τ → Gof τ u' (V τ) := by
    intro τ hτ
    have h0 := hPV (τ - σ)
    rw [show σ + (τ - σ) = τ by omega] at h0
    have h1 := (Gof_ax (by omega : 1 ≤ τ)).lift b _ (Fr_mlift hW _ _) h0 u' hu
    rw [← hd, mlift_commk, show b + σ + d = u' + σ by omega] at h1
    rw [hV]; exact h1
  have eStep : ∀ τ, σ ≤ τ → mlift (V τ) (u' + τ) 1 = V (τ + 1) := by
    intro τ hτ
    rw [hV]
    have := mlift_mlift (mlift W b d) (u' + σ) (τ - σ) 1
    rw [show u' + σ + (τ - σ) = u' + τ by omega, show τ - σ + 1 = τ + 1 - σ by omega] at this
    exact this
  have claim : ∀ m τ, σ ≤ τ →
      Gof τ u' (V τ ++ shiftr01 1 0 ((((0, u' + τ + 1, 0) : ℕ × ℕ × ℕ) ::
        (V (τ + 1) ++ [((1, u' + τ + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m⟧)) := by
    intro m
    induction m with
    | zero =>
        intro τ hτ
        rw [oper_zcone (hVFr (τ + 1)) le_rfl (coneV_top1 (hVFr (τ + 1)) (by omega)) 0]
        simp only [List.range_zero, List.flatMap_nil, shiftr01, List.map_nil, List.append_nil]
        exact hBase τ hτ
    | succ m ih =>
        intro τ hτ
        rw [oper_zcone_succ (hVFr (τ + 1)) le_rfl (coneV_top1 (hVFr (τ + 1)) (by omega)) m,
          show u' + τ + 1 = u' + (τ + 1) by omega, eStep (τ + 1) (by omega)]
        have eS : shiftr01 1 0 (((0, u' + (τ + 1), 0) : ℕ × ℕ × ℕ) ::
            (V (τ + 1) ++ shiftr01 1 0 ((((0, u' + (τ + 1) + 1, 0) : ℕ × ℕ × ℕ) ::
              (V (τ + 1 + 1) ++ [((1, u' + (τ + 1) + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m⟧)))
            = ((1, u' + (τ + 1), 0) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (V (τ + 1) ++ shiftr01 1 0 ((((0, u' + (τ + 1) + 1, 0) : ℕ × ℕ × ℕ) ::
                (V (τ + 1 + 1) ++ [((1, u' + (τ + 1) + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m⟧)) := by
          simp [shiftr01]
        rw [eS]
        exact Gof_node (ρ := τ) (σ := τ + 1) (by omega) (by omega) (hVFr τ) (hBase τ hτ)
          (ih (τ + 1) (by omega))
  have hcA := coneV_top1 hW (show b < b + σ + 1 by omega)
  rw [mlift_snoc_cone W _ hcA d]
  have eL1 : (((1, b + σ + 1, 1) : ℕ × ℕ × ℕ).1, ((1, b + σ + 1, 1) : ℕ × ℕ × ℕ).2.1 + d,
      ((1, b + σ + 1, 1) : ℕ × ℕ × ℕ).2.2) = ((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ) := by
    show ((1, b + σ + 1 + d, 1) : ℕ × ℕ × ℕ) = _
    rw [show b + σ + 1 + d = u' + σ + 1 by omega]
  have eV0 : mlift W b d = V σ := by rw [hV]; simp [mlift_zero]
  rw [eL1, eV0]
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq,
      U0 = ((0, u' + σ, 0) : ℕ × ℕ × ℕ) :: (V σ ++ [((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ)]) := ⟨_, rfl⟩
  have eU : ((1, u' + σ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (V σ ++ [((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ)])
      = shiftr01 1 0 U0 := by rw [hU0]; simp [shiftr01]
  rw [eU]
  have hlen : 2 ≤ U0.length := by rw [hU0]; simp
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom (hVFr σ) le_rfl (coneV_top1 (hVFr σ) (show u' + σ < u' + σ + 1 by omega))
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h | h
    · exfalso
      have hl : U0.length - 1 = (((0, u' + σ, 0) : ℕ × ℕ × ℕ) :: V σ).length + 0 := by
        rw [hU0]; simp
      rw [hl] at h
      unfold lev at h
      rw [hU0, show ((0, u' + σ, 0) : ℕ × ℕ × ℕ) :: (V σ ++ [((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ)])
        = (((0, u' + σ, 0) : ℕ × ℕ × ℕ) :: V σ) ++ [((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ)] by simp,
        entry_append_right, entry_append_right] at h
      simp [entry] at h
    · exact h
  refine hQ.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
    (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp), hU0]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] U0 1 m hlen hpV
  simp only [List.nil_append] at eO
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [eO, hU0, oper_zcone_succ (hVFr σ) le_rfl (coneV_top1 (hVFr σ) (by omega)) m', eStep σ le_rfl]
  have eS : shiftr01 1 0 (((0, u' + σ, 0) : ℕ × ℕ × ℕ) ::
      (V σ ++ shiftr01 1 0 ((((0, u' + σ + 1, 0) : ℕ × ℕ × ℕ) ::
        (V (σ + 1) ++ [((1, u' + σ + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m'⟧)))
      = ((1, u' + σ, 0) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (V σ ++ shiftr01 1 0 ((((0, u' + σ + 1, 0) : ℕ × ℕ × ℕ) ::
          (V (σ + 1) ++ [((1, u' + σ + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m'⟧)) := by
    simp [shiftr01]
  rw [eS]
  have h := (Gof_eq σ u' _).mp (claim m' σ le_rfl) Q hQ hF u' le_rfl X hX hQX
  rwa [Nat.sub_self, mlift_zero] at h

#print axioms Gof_snocz_core

theorem PV_snocz {b σ : ℕ} (hσ : 1 ≤ σ) {W : TrioSeq} (hW : Fr W) (h : PV b σ W) :
    PV b σ (W ++ [((1, b + σ + 1, 1) : ℕ × ℕ × ℕ)]) := by
  intro t
  have hcA := coneV_top1 hW (show b + σ < b + σ + 1 by omega)
  rw [mlift_snoc_cone W _ hcA t]
  have eL : (((1, b + σ + 1, 1) : ℕ × ℕ × ℕ).1, ((1, b + σ + 1, 1) : ℕ × ℕ × ℕ).2.1 + t,
      ((1, b + σ + 1, 1) : ℕ × ℕ × ℕ).2.2) = ((1, b + (σ + t) + 1, 1) : ℕ × ℕ × ℕ) := by
    show ((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) = _
    rw [show b + σ + 1 + t = b + (σ + t) + 1 by omega]
  rw [eL]
  refine Gof_snocz_core (by omega) (Fr_mlift hW _ _) (fun t' => ?_)
  have := h (t + t')
  rw [show σ + (t + t') = σ + t + t' by omega] at this
  have e := mlift_mlift W (b + σ) t t'
  rw [show b + σ + t = b + (σ + t) by omega] at e
  rwa [e]

#print axioms PV_snocz


/-! ## 錨つきの字の中身 -/

/-- 段 b、錨 σ の字の中身: どの錨つきの接頭辞の後ろにも、中身 Y の字を足せる。 -/
def LC (b σ : ℕ) (Y : TrioSeq) : Prop :=
  ∀ W, Fr W → PV b σ W → PV b σ (W ++ ((1, b + σ + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y)


theorem mlift_letterU {W Y : TrioSeq} (hW : Fr W) (hY : Fr Y) {a r : ℕ} (hr : a < r) (t : ℕ) :
    mlift (W ++ ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y) a t
      = mlift W a t ++ ((1, r + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift Y a t) := by
  rw [mlift_app hW (Hd_letter _ _), mlift_letter hr hY]

theorem PV_lift {b σ : ℕ} (hσ : 1 ≤ σ) {W : TrioSeq} (hW : Fr W) (h : PV b σ W) {b' : ℕ}
    (hb : b ≤ b') : PV b' σ (mlift W b (b' - b)) := by
  intro t
  have h1 := (Gof_ax (by omega : 1 ≤ σ + t)).lift b _ (Fr_mlift hW _ _) (h t) b' hb
  rw [mlift_commk, show b + σ + (b' - b) = b' + σ by omega] at h1
  exact h1

theorem LC_nil {b σ : ℕ} (hσ : 1 ≤ σ) : LC b σ [] := by
  intro W hW hPV
  have := PV_snocz hσ hW hPV
  simpa [shiftr01] using this

theorem LC_oper {b σ : ℕ} (hσ : 1 ≤ σ) {Y U : TrioSeq} (hY : Fr Y) (hU : Fr U) (hH : Hd U)
    (hlen : 2 ≤ U.length) (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → LC b σ (Y ++ U⟦m⟧)) : LC b σ (Y ++ U) := by
  intro W hW hPV t
  have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  rw [mlift_letterU hW (Fr_append hY hU) (show b + σ < b + σ + 1 by omega), mlift_app hY hH]
  have hlen' : 2 ≤ (mlift U (b + σ) t).length := by rw [mlift_length]; exact hlen
  have hUlne : mlift U (b + σ) t ≠ [] := by
    intro h; have := congrArg List.length h; rw [mlift_length, List.length_nil] at this; omega
  have hp' := (hasParent_mlift_iff (b + σ) t hUne).mpr hp
  refine (Gof_ax (by omega : 1 ≤ σ + t)).oper b _ _ (Fr_mlift hW _ _) (Fr_letter _ _) (Hd_letter _ _)
    (by simp only [List.length_cons, List.length_append, shiftr01_length]; omega)
    (node_hasParent _ _ _ hp' hUlne) (fun m hm => ?_)
  rw [node_oper _ _ _ hlen' hp' m, mlift_oper', ← mlift_app hY (Hd_oper hH hUne hm)]
  have h := hIH m hm W hW hPV t
  rwa [mlift_letterU hW (Fr_append hY (Fr_oper hU m)) (show b + σ < b + σ + 1 by omega)] at h

theorem mlift_rep {W L : TrioSeq} (hW : Fr W) (hL : Fr L) (hH : Hd L) (a t : ℕ) :
    ∀ m, mlift (W ++ (List.range m).flatMap (fun _ => L)) a t
      = mlift W a t ++ (List.range m).flatMap (fun _ => mlift L a t)
  | 0 => by simp
  | (m + 1) => by
      have hFr : Fr (W ++ (List.range m).flatMap (fun _ => L)) := by
        refine Fr_append hW (fun y hy => ?_)
        simp only [List.mem_flatMap] at hy
        obtain ⟨-, -, hy⟩ := hy
        exact hL y hy
      rw [List.range_succ, List.flatMap_append, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [← List.append_assoc, mlift_app hFr hH, mlift_rep hW hL hH a t m, List.append_assoc]

theorem LC_flat {b σ : ℕ} (hσ : 1 ≤ σ) {Y : TrioSeq} (hY : Fr Y) (h : LC b σ Y) :
    LC b σ (Y ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := by
  intro W hW hPV t
  have hrep : ∀ m, PV b σ (W ++ (List.range m).flatMap
      (fun _ => ((1, b + σ + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y)) ∧
      Fr (W ++ (List.range m).flatMap (fun _ => ((1, b + σ + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y)) := by
    intro m
    induction m with
    | zero => simpa using And.intro hPV hW
    | succ m ih =>
        rw [List.range_succ, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [← List.append_assoc]
        exact ⟨h _ ih.2 ih.1, Fr_append ih.2 (Fr_letter _ _)⟩
  have hY1 : Fr (Y ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) :=
    Fr_append hY (by intro y hy; simp at hy; subst hy; show 1 ≤ 1; omega)
  rw [mlift_letterU hW hY1 (show b + σ < b + σ + 1 by omega), mlift_snoc_flat Y 1 (b + σ) t hY]
  obtain ⟨M, hM⟩ : ∃ M : TrioSeq,
      M = ((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift Y (b + σ) t) := ⟨_, rfl⟩
  have eV : ((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (mlift Y (b + σ) t ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
      = M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
    rw [hM, node_split, shift_col]
  rw [eV]
  have hMne : M ≠ [] := by rw [hM]; simp
  have hMl : 1 ≤ M.length := by rw [hM]; simp
  have hhead : entry M 0 0 < 2 := by rw [hM]; show 1 < 2; omega
  have htail : ∀ r, 1 ≤ r → r < M.length → 2 ≤ entry M 0 r := by
    intro r hr1 hr2
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hr' : r' < (mlift Y (b + σ) t).length := by
      rw [hM] at hr2; simp only [List.length_cons, shiftr01_length] at hr2; omega
    rw [hM, entry_cons, entry0_shiftr01 hr']
    have := getD_row0_ge (Fr_mlift hY (b + σ) t) hr'
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
  refine (Gof_ax (by omega : 1 ≤ σ + t)).oper b _ (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)])
    (Fr_mlift hW _ _)
    (Fr_append (by rw [hM]; exact Fr_letter _ _)
      (by intro y hy; simp at hy; subst hy; show 1 ≤ 2; omega))
    (fun _ => by rw [hM]; rfl) (by simp only [List.length_append, List.length_singleton]; omega)
    hpV (fun m _ => ?_)
  have eO := oper_snoc00'' [] hMne hhead htail m
  simp only [List.nil_append] at eO
  rw [eO]
  have h2 := (hrep m).1 t
  rw [mlift_rep hW (Fr_letter _ _) (Hd_letter _ _),
    mlift_letter (show b + σ < b + σ + 1 by omega) hY, ← hM] at h2
  exact h2

#print axioms LC_flat


theorem LC_orph {b σ : ℕ} (hσ : 1 ≤ σ) {Y U : TrioSeq} {h j : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
    (hj1 : 1 ≤ j) (hj : j ≤ b)
    (hnp : ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z → LC b σ (Y ++ (U ++ shiftr01 h 0 z))) :
    LC b σ (Y ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
  intro W hW hPV t
  have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ b + σ := by show j ≤ b + σ; omega
  have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
  have hh1 : 1 ≤ h := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
  have eL : mlift (Y ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (b + σ) t
      = mlift Y (b + σ) t ++ (mlift U (b + σ) t ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_app hY hH, mlift_snoc_low U _ hc]
  rw [mlift_letterU hW (Fr_append hY hU) (show b + σ < b + σ + 1 by omega), eL]
  have eV : ((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift Y (b + σ) t ++ (mlift U (b + σ) t ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
      = (((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + σ) t ++ mlift U (b + σ) t))
        ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by
    rw [← List.append_assoc, shiftr01_append0, shift_col]; rfl
  rw [eV]
  refine (Gof_ax (by omega : 1 ≤ σ + t)).orph b _ _ (h + 1) j (Fr_mlift hW _ _)
    (by rw [← eV]; exact Fr_letter _ _) (by rw [← eV]; exact Hd_letter _ _) hj1 hj ?_
    (fun z hz' hbz => ?_)
  · have eAB : (((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + σ) t ++ mlift U (b + σ) t))
          ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]
        = (((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift Y (b + σ) t)) ++
          shiftr01 1 0 (mlift U (b + σ) t ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      rw [← eV, node_split]
    have eidx : (((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + σ) t ++ mlift U (b + σ) t)).length
        = (((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift Y (b + σ) t)).length +
          (mlift U (b + σ) t).length := by simp [shiftr01]; omega
    rw [eAB, eidx]
    have hBH : Hd (mlift U (b + σ) t ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      rw [← mlift_snoc_low U _ hc]; exact Hd_mlift hH _ _
    refine noParent_ctx (j := j) (by simp [shiftr01]) (fun k' hk' hrt => ?_) ?_ ?_
    · have := letter_anc_row1 (Fr_mlift hY (b + σ) t) hBH (by simp) hk' (by simp [shiftr01]) hrt
      subst this
      show j ≤ b + σ + 1 + t
      omega
    · rw [entry1_shiftr01, show (mlift U (b + σ) t).length = (mlift U (b + σ) t).length + 0
        from rfl, entry_append_right]; rfl
    · intro hh
      apply hnp
      rw [hasParent_shiftr01, ← mlift_snoc_low U _ hc, mlift_eq_slift,
        hasParent_slift (stair_step (b + σ) t), mlift_length] at hh
      exact hh
  · have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
    have hHz : Hd (U ++ shiftr01 h 0 z) := by
      intro hne
      by_cases hUn : U = []
      · subst hUn
        have hh1' : h = 1 := by have := hH (by simp); simpa [entry] using this
        have hzne : z ≠ [] := by intro hz0; apply hne; subst hz0; rfl
        simp only [List.nil_append]
        rw [entry0_shiftr01 (List.length_pos_iff.mpr hzne), show entry z 0 0 = 0 from hbz, hh1']
      · rw [Small.entry_append_left (List.length_pos_iff.mpr hUn)]
        have := hH (by simp)
        rwa [Small.entry_append_left (List.length_pos_iff.mpr hUn)] at this
    have hFrz : Fr (U ++ shiftr01 h 0 z) := by
      refine Fr_append hUc (fun y hy => ?_)
      simp only [shiftr01, List.mem_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      dsimp only; omega
    have hzz := hz z hz' hbz W hW hPV t
    rw [mlift_letterU hW (Fr_append hY hFrz) (show b + σ < b + σ + 1 by omega), mlift_app hY hHz,
      mlift_append_low (low_of_Wg hzW h (by omega))] at hzz
    rw [show (((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + σ) t ++ mlift U (b + σ) t)) ++ shiftr01 (h + 1) 0 z
        = ((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift Y (b + σ) t ++
            (mlift U (b + σ) t ++ shiftr01 h 0 z)) by
      rw [← List.append_assoc, shiftr01_append0 _ (mlift Y (b + σ) t ++ mlift U (b + σ) t),
        shiftr01_add0]; rfl]
    exact hzz

#print axioms LC_orph

theorem LC_tie {b σ : ℕ} (hσ : 1 ≤ σ) {Y U : TrioSeq} {x : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) b U.length)
    (hload : ∀ b', b ≤ b' → ∀ Z ∈ Wg (2 * b'), based Z →
      LC b' σ (mlift (Y ++ U) b (b' - b) ++ shiftr01 x 0 Z)) :
    LC b σ (Y ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) := by
  intro W hW hPV t
  have hcl : (((x, b + 1, 0) : ℕ × ℕ × ℕ)).2.1 ≤ b + σ := by show b + 1 ≤ b + σ; omega
  have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
  have eL : mlift (Y ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) (b + σ) t
      = mlift Y (b + σ) t ++ (mlift U (b + σ) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_app hY hH, mlift_snoc_low U _ hcl]
  rw [mlift_letterU hW (Fr_append hY hU) (show b + σ < b + σ + 1 by omega), eL]
  have eV : ((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift Y (b + σ) t ++ (mlift U (b + σ) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
      = (((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + σ) t ++ mlift U (b + σ) t))
        ++ [((x + 1, b + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [← List.append_assoc, shiftr01_append0, shift_col]; rfl
  rw [eV]
  have hHU : Hd U := by
    intro hne
    have := hH (by simp)
    rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
  refine (Gof_ax (by omega : 1 ≤ σ + t)).tie b _ _ (x + 1) (Fr_mlift hW _ _)
    (by rw [← eV]; exact Fr_letter _ _) (by rw [← eV]; exact Hd_letter _ _) ?_
    (fun b'' hb'' Z hZ hbZ => ?_)
  · have eAB : (((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + σ) t ++ mlift U (b + σ) t))
          ++ [((x + 1, b + 1, 0) : ℕ × ℕ × ℕ)]
        = (((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift Y (b + σ) t)) ++
          shiftr01 1 0 (mlift U (b + σ) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
      rw [← eV, node_split]
    have eidx : (((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + σ) t ++ mlift U (b + σ) t)).length
        = (((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift Y (b + σ) t)).length +
          (mlift U (b + σ) t).length := by simp [shiftr01]; omega
    rw [eAB, eidx]
    have hPCA : PathCone b 1 (((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift Y (b + σ) t)) := by
      intro y hy _ hd
      rcases y with _ | y
      · show b < b + σ + 1 + t; omega
      · exfalso
        rw [entry_cons] at hd
        have hy' : y < (mlift Y (b + σ) t).length := by
          rw [mlift_length]; simp [shiftr01] at hy; omega
        rw [entry0_shiftr01 hy'] at hd
        have := getD_row0_ge (Fr_mlift hY (b + σ) t) hy'
        omega
    have hB0 : shiftr01 1 0 (mlift U (b + σ) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) ≠ [] →
        entry (shiftr01 1 0 (mlift U (b + σ) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) 0 0 = 1 + 1 := by
      intro _
      have hBH : Hd (mlift U (b + σ) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
        have := Hd_mlift hH (b + σ) t
        rwa [mlift_snoc_low U _ hcl] at this
      rw [entry0_shiftr01 (by simp), hBH (by simp)]
    rw [coneV_pathB hPCA hB0 (by simp [shiftr01]), coneV_shift0]
    have := coneV_mlift_up (by simp) hc (b + σ) t
    rwa [mlift_snoc_low U _ hcl, ← mlift_length U (b + σ) t] at this
  · have hFrYU : Fr (Y ++ U) := Fr_append hY hUc
    have hFrZ : Fr (mlift (Y ++ U) b (b'' - b) ++ shiftr01 x 0 Z) := by
      have hx1 : 1 ≤ x := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
      refine Fr_append (Fr_mlift hFrYU _ _) (fun y hy => ?_)
      simp only [shiftr01, List.mem_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      dsimp only; omega
    have h1 := hload b'' hb'' Z hZ hbZ (mlift W b (b'' - b)) (Fr_mlift hW _ _)
      (PV_lift hσ hW hPV hb'') t
    rw [mlift_letterU (Fr_mlift hW _ _) hFrZ (show b'' + σ < b'' + σ + 1 by omega),
      mlift_append_low (low_of_Wg hZ x (by omega))] at h1
    have hWU : Fr (mlift Y (b + σ) t ++ mlift U (b + σ) t) :=
      Fr_append (Fr_mlift hY _ _) (Fr_mlift hUc _ _)
    have eW : mlift (mlift W (b + σ) t) b (b'' - b) = mlift (mlift W b (b'' - b)) (b'' + σ) t := by
      rw [mlift_commk, show b + σ + (b'' - b) = b'' + σ by omega]
    have eKU : mlift (mlift Y (b + σ) t ++ mlift U (b + σ) t) b (b'' - b)
        = mlift (mlift (Y ++ U) b (b'' - b)) (b'' + σ) t := by
      rw [← mlift_app hY hHU, mlift_commk, show b + σ + (b'' - b) = b'' + σ by omega]
    rw [mlift_app (Fr_mlift hW _ _) (Hd_letter _ _), eW, mlift_letter (by omega) hWU, eKU,
      show b + σ + 1 + t + (b'' - b) = b'' + σ + 1 + t by omega, List.append_assoc]
    rw [shiftr01_append0, shiftr01_add0] at h1
    simpa [List.append_assoc] using h1

#print axioms LC_tie


/-! ## 全ての錨と全ての段 -/

def LCup (b σ : ℕ) (Y : TrioSeq) : Prop := ∀ t, LC b (σ + t) (mlift Y (b + σ) t)

def LCall (σ b : ℕ) (Y : TrioSeq) : Prop := ∀ b', b ≤ b' → LCup b' σ (mlift Y b (b' - b))

theorem LCall_nil {σ : ℕ} (hσ : 1 ≤ σ) (b : ℕ) : LCall σ b [] := by
  intro b' _ t
  rw [mlift_nil, mlift_nil]
  exact LC_nil (by omega)

theorem LCup_oper {b σ : ℕ} (hσ : 1 ≤ σ) {Y U : TrioSeq} (hY : Fr Y) (hU : Fr U) (hH : Hd U)
    (hlen : 2 ≤ U.length) (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → LCup b σ (Y ++ U⟦m⟧)) : LCup b σ (Y ++ U) := by
  intro t
  have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  rw [mlift_app hY hH]
  refine LC_oper (by omega) (Fr_mlift hY _ _) (Fr_mlift hU _ _) (Hd_mlift hH _ _)
    (by rw [mlift_length]; exact hlen) ((hasParent_mlift_iff _ _ hUne).mpr hp) (fun m hm => ?_)
  rw [mlift_oper', ← mlift_app hY (Hd_oper hH hUne hm)]
  exact hIH m hm t

theorem LCup_flat {b σ : ℕ} (hσ : 1 ≤ σ) {Y : TrioSeq} (hY : Fr Y) (h : LCup b σ Y) :
    LCup b σ (Y ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := by
  intro t
  rw [mlift_snoc_flat Y 1 (b + σ) t hY]
  exact LC_flat (by omega) (Fr_mlift hY _ _) (h t)

theorem Hd_append_shift {U z : TrioSeq} {h j : ℕ} (hH : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
    (hbz : based z) : Hd (U ++ shiftr01 h 0 z) := by
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

theorem LCup_orph {b σ : ℕ} (hσ : 1 ≤ σ) {Y U : TrioSeq} {h j : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
    (hj1 : 1 ≤ j) (hj : j ≤ b)
    (hnp : ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z → LCup b σ (Y ++ (U ++ shiftr01 h 0 z))) :
    LCup b σ (Y ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
  intro t
  have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ b + σ := by show j ≤ b + σ; omega
  have eL : mlift (Y ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (b + σ) t
      = mlift Y (b + σ) t ++ (mlift U (b + σ) t ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_app hY hH, mlift_snoc_low U _ hc]
  rw [eL]
  refine LC_orph (by omega) (Fr_mlift hY _ _) (by rw [← mlift_snoc_low U _ hc]; exact Fr_mlift hU _ _)
    (by rw [← mlift_snoc_low U _ hc]; exact Hd_mlift hH _ _) hj1 hj ?_ (fun z hz' hbz => ?_)
  · intro hh
    apply hnp
    have hl : U.length = (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1 := by simp
    rw [hl]
    rw [← mlift_snoc_low U _ hc, mlift_eq_slift, show (mlift U (b + σ) t).length
      = (slift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) (fun m => m + (if b + σ < m then t else 0))).length - 1
      by simp, hasParent_slift (stair_step (b + σ) t)] at hh
    rwa [slift_length] at hh
  · have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
    have := hz z hz' hbz t
    rw [mlift_app hY (Hd_append_shift hH hbz), mlift_append_low (low_of_Wg hzW h (by omega))] at this
    exact this

theorem LCup_tie {b σ : ℕ} (hσ : 1 ≤ σ) {Y U : TrioSeq} {x : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) b U.length)
    (hload : ∀ b', b ≤ b' → ∀ Z ∈ Wg (2 * b'), based Z →
      LCup b' σ (mlift (Y ++ U) b (b' - b) ++ shiftr01 x 0 Z)) :
    LCup b σ (Y ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) := by
  intro t
  have hcl : (((x, b + 1, 0) : ℕ × ℕ × ℕ)).2.1 ≤ b + σ := by show b + 1 ≤ b + σ; omega
  have eL : mlift (Y ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) (b + σ) t
      = mlift Y (b + σ) t ++ (mlift U (b + σ) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_app hY hH, mlift_snoc_low U _ hcl]
  rw [eL]
  have hHU : Hd U := by
    intro hne
    have := hH (by simp)
    rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
  have hc' : coneV (mlift U (b + σ) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) b (mlift U (b + σ) t).length := by
    have := coneV_mlift_up (by simp) hc (b + σ) t
    rwa [mlift_snoc_low U _ hcl, ← mlift_length U (b + σ) t] at this
  refine LC_tie (by omega) (Fr_mlift hY _ _) (by rw [← mlift_snoc_low U _ hcl]; exact Fr_mlift hU _ _)
    (by rw [← mlift_snoc_low U _ hcl]; exact Hd_mlift hH _ _) hc' (fun b' hb' Z hZ hbZ => ?_)
  have h1 := hload b' hb' Z hZ hbZ t
  rw [mlift_append_low (low_of_Wg hZ x (by omega))] at h1
  rw [← mlift_app hY hHU, mlift_commk, show b + σ + (b' - b) = b' + σ by omega]
  exact h1

theorem LCall_ax {σ : ℕ} (hσ : 1 ≤ σ) : SlotAx (LCall σ) where
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
    refine LCup_oper hσ (Fr_mlift hW _ _) (Fr_mlift hU _ _) (Hd_mlift hH _ _) hlen' hp' (fun m hm => ?_)
    rw [mlift_oper', ← mlift_app hW (Hd_oper hH hUne hm)]
    exact hIH m hm u' hu
  orph := by
    intro u W U h j hW hU hH hj1 hj hnp hz u' hu
    have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u := hj
    have eL : mlift (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) u (u' - u)
        = mlift W u (u' - u) ++ (mlift U u (u' - u) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      rw [mlift_app hW hH, mlift_snoc_low U _ hc]
    rw [eL]
    refine LCup_orph hσ (Fr_mlift hW _ _) (by rw [← mlift_snoc_low U _ hc]; exact Fr_mlift hU _ _)
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
      rw [mlift_app hW (Hd_append_shift hH hbz), mlift_append_low (low_of_Wg hzW h hj)] at hzz
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
    refine LCup_tie hσ (Fr_mlift hW _ _) hU' hH' hc' (fun u'' hu'' Z hZ hbZ => ?_)
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
    exact LCup_flat hσ (Fr_mlift hW _ _) (h u' hu)

#print axioms LCall_ax

end GxY
end TRIO
