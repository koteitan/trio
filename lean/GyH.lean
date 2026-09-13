/-
GyH.lean: 節点（錨の列 A、行 1 の差 o、状態 H）の下の字の中身（状態を固定）。

    LC1 A o H b Y := ∀ W, PVP A o H b W → PVP A o H b (W ++ (1, b + liftOff H A o + 1, 1) :: Y↑1)

GxY の LC_nil / LC_oper / LC_flat / LC_orph / LC_tie を GpT の世界に移したもの。
-/
import GyG

namespace TRIO
namespace GyH

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG

def LC1 (A : List ℕ) (o : ℕ) (H : ℕ → ℕ) (b : ℕ) (Y : TrioSeq) : Prop :=
  ∀ W, Fr W → PVP A o H b W →
    PVP A o H b (W ++ ((1, b + liftOff H A o + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y)

theorem PVP_lift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {W : TrioSeq} (hW : Fr W) (h : PVP A o H b W) {b' : ℕ} (hb : b ≤ b') :
    PVP A o H b' (mlift W b (b' - b)) := by
  intro t
  have h1 := (GpT_ax (fun a ha => by have := hA a ha; omega) hA1 (by omega) H).lift b _
    (Fr_mlift hW _ _) (h t) b' hb
  rw [mlift_commk, show b + liftOff H A o + (b' - b) = b' + liftOff H A o by omega] at h1
  exact h1

theorem LC1_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (H : ℕ → ℕ) (b : ℕ) : LC1 A o H b [] := by
  intro W hW hPV
  have := PVP_snocz hA hA1 ho hW hPV
  simpa [shiftr01] using this

theorem LC1_oper {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} (hY : Fr Y) (hU : Fr U) (hH : Hd U)
    (hlen : 2 ≤ U.length) (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → LC1 A o H b (Y ++ U⟦m⟧)) : LC1 A o H b (Y ++ U) := by
  intro W hW hPV t
  have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  rw [mlift_letterU hW (Fr_append hY hU)
    (show b + liftOff H A o < b + liftOff H A o + 1 by omega), mlift_app hY hH]
  have hlen' : 2 ≤ (mlift U (b + liftOff H A o) t).length := by rw [mlift_length]; exact hlen
  have hUlne : mlift U (b + liftOff H A o) t ≠ [] := by
    intro h; have := congrArg List.length h; rw [mlift_length, List.length_nil] at this; omega
  have hp' := (hasParent_mlift_iff (b + liftOff H A o) t hUne).mpr hp
  refine (GpT_ax (fun a ha => by have := hA a ha; omega) hA1 (by omega) H).oper b _ _
    (Fr_mlift hW _ _) (Fr_letter _ _) (Hd_letter _ _)
    (by simp only [List.length_cons, List.length_append, shiftr01_length]; omega)
    (node_hasParent _ _ _ hp' hUlne) (fun m hm => ?_)
  rw [node_oper _ _ _ hlen' hp' m, mlift_oper', ← mlift_app hY (Hd_oper hH hUne hm)]
  have h := hIH m hm W hW hPV t
  rwa [mlift_letterU hW (Fr_append hY (Fr_oper hU m))
    (show b + liftOff H A o < b + liftOff H A o + 1 by omega)] at h

theorem LC1_flat {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {Y : TrioSeq} (hY : Fr Y) (h : LC1 A o H b Y) :
    LC1 A o H b (Y ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := by
  intro W hW hPV t
  have hrep : ∀ m, PVP A o H b (W ++ (List.range m).flatMap
      (fun _ => ((1, b + liftOff H A o + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y)) ∧
      Fr (W ++ (List.range m).flatMap
        (fun _ => ((1, b + liftOff H A o + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y)) := by
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
  rw [mlift_letterU hW hY1 (show b + liftOff H A o < b + liftOff H A o + 1 by omega),
    mlift_snoc_flat Y 1 (b + liftOff H A o) t hY]
  obtain ⟨M, hM⟩ : ∃ M : TrioSeq,
      M = ((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift Y (b + liftOff H A o) t) := ⟨_, rfl⟩
  have eV : ((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
      = M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
    rw [hM, node_split, shift_col]
  rw [eV]
  have hMne : M ≠ [] := by rw [hM]; simp
  have hhead : entry M 0 0 < 2 := by rw [hM]; show 1 < 2; omega
  have htail : ∀ r, 1 ≤ r → r < M.length → 2 ≤ entry M 0 r := by
    intro r hr1 hr2
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hr' : r' < (mlift Y (b + liftOff H A o) t).length := by
      rw [hM] at hr2; simp only [List.length_cons, shiftr01_length] at hr2; omega
    rw [hM, entry_cons, entry0_shiftr01 hr']
    have := getD_row0_ge (Fr_mlift hY (b + liftOff H A o) t) hr'
    omega
  have hpV : hasParent (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)])
      (srow (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1))
      ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
    have hidx : (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1 = M.length + 0 := by simp
    rw [hidx, srow_append_right]
    have hs : srow [((2, 0, 0) : ℕ × ℕ × ℕ)] 0 = 0 := rfl
    rw [hs]
    refine (hasParent_zero_iff (by simp)).mpr ⟨0, by rw [hM]; simp, ?_⟩
    rw [Small.entry_append_left (by rw [hM]; simp), entry_append_right]
    exact hhead
  refine (GpT_ax (fun a ha => by have := hA a ha; omega) hA1 (by omega) H).oper b _
    (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) (Fr_mlift hW _ _)
    (Fr_append (by rw [hM]; exact Fr_letter _ _)
      (by intro y hy; simp at hy; subst hy; show 1 ≤ 2; omega))
    (fun _ => by rw [hM]; rfl) (by simp only [List.length_append, List.length_singleton]; rw [hM]; simp)
    hpV (fun m _ => ?_)
  have eO := oper_snoc00'' [] hMne hhead htail m
  simp only [List.nil_append] at eO
  rw [eO]
  have h2 := (hrep m).1 t
  rw [mlift_rep hW (Fr_letter _ _) (Hd_letter _ _),
    mlift_letter (show b + liftOff H A o < b + liftOff H A o + 1 by omega) hY, ← hM] at h2
  exact h2

theorem LC1_orph {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} {h j : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
    (hj1 : 1 ≤ j) (hj : j ≤ b)
    (hnp : ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z → LC1 A o H b (Y ++ (U ++ shiftr01 h 0 z))) :
    LC1 A o H b (Y ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
  intro W hW hPV t
  have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ b + liftOff H A o := by
    show j ≤ b + liftOff H A o; omega
  have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
  have eL : mlift (Y ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (b + liftOff H A o) t
      = mlift Y (b + liftOff H A o) t ++ (mlift U (b + liftOff H A o) t ++
          [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_app hY hH, mlift_snoc_low U _ hc]
  rw [mlift_letterU hW (Fr_append hY hU)
    (show b + liftOff H A o < b + liftOff H A o + 1 by omega), eL]
  have eV : ((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ (mlift U (b + liftOff H A o) t ++
          [((h, j, 0) : ℕ × ℕ × ℕ)]))
      = (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t))
        ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by
    rw [← List.append_assoc, shiftr01_append0, shift_col]; rfl
  rw [eV]
  refine (GpT_ax (fun a ha => by have := hA a ha; omega) hA1 (by omega) H).orph b _ _ (h + 1) j
    (Fr_mlift hW _ _) (by rw [← eV]; exact Fr_letter _ _) (by rw [← eV]; exact Hd_letter _ _)
    hj1 hj ?_ (fun z hz' hbz => ?_)
  · have eAB : (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t))
          ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]
        = (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift Y (b + liftOff H A o) t)) ++
          shiftr01 1 0 (mlift U (b + liftOff H A o) t ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      rw [← eV, node_split]
    have eidx : (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t)).length
        = (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift Y (b + liftOff H A o) t)).length +
          (mlift U (b + liftOff H A o) t).length := by simp [shiftr01]; omega
    rw [eAB, eidx]
    have hBH : Hd (mlift U (b + liftOff H A o) t ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      rw [← mlift_snoc_low U _ hc]; exact Hd_mlift hH _ _
    refine noParent_ctx (j := j) (by simp [shiftr01]) (fun k' hk' hrt => ?_) ?_ ?_
    · have := letter_anc_row1 (Fr_mlift hY (b + liftOff H A o) t) hBH (by simp) hk'
        (by simp [shiftr01]) hrt
      subst this
      show j ≤ b + liftOff H A o + 1 + t
      omega
    · rw [entry1_shiftr01, show (mlift U (b + liftOff H A o) t).length
          = (mlift U (b + liftOff H A o) t).length + 0 from rfl, entry_append_right]; rfl
    · intro hh
      apply hnp
      rw [hasParent_shiftr01, ← mlift_snoc_low U _ hc, mlift_eq_slift,
        hasParent_slift (stair_step (b + liftOff H A o) t), mlift_length] at hh
      exact hh
  · have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
    have hHz : Hd (U ++ shiftr01 h 0 z) := Hd_append_shift hH hbz
    have hFrz : Fr (U ++ shiftr01 h 0 z) := by
      have hh1 : 1 ≤ h := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
      refine Fr_append hUc (fun y hy => ?_)
      simp only [shiftr01, List.mem_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      dsimp only; omega
    have hzz := hz z hz' hbz W hW hPV t
    rw [mlift_letterU hW (Fr_append hY hFrz)
        (show b + liftOff H A o < b + liftOff H A o + 1 by omega), mlift_app hY hHz,
      mlift_append_low (low_of_Wg hzW h (by omega))] at hzz
    rw [show (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t)) ++
            shiftr01 (h + 1) 0 z
        = ((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++
              (mlift U (b + liftOff H A o) t ++ shiftr01 h 0 z)) by
      rw [← List.append_assoc, shiftr01_append0 _
        (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t), shiftr01_add0]; rfl]
    exact hzz

theorem LC1_tie {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} {x : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) b U.length)
    (hload : ∀ b', b ≤ b' → ∀ Z ∈ Wg (2 * b'), based Z →
      LC1 A o H b' (mlift (Y ++ U) b (b' - b) ++ shiftr01 x 0 Z)) :
    LC1 A o H b (Y ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) := by
  intro W hW hPV t
  have hk1 : 1 ≤ liftOff H A o := by unfold liftOff; omega
  have hcl : (((x, b + 1, 0) : ℕ × ℕ × ℕ)).2.1 ≤ b + liftOff H A o := by
    show b + 1 ≤ b + liftOff H A o; omega
  have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
  have eL : mlift (Y ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) (b + liftOff H A o) t
      = mlift Y (b + liftOff H A o) t ++ (mlift U (b + liftOff H A o) t ++
          [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_app hY hH, mlift_snoc_low U _ hcl]
  rw [mlift_letterU hW (Fr_append hY hU)
    (show b + liftOff H A o < b + liftOff H A o + 1 by omega), eL]
  have eV : ((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ (mlift U (b + liftOff H A o) t ++
          [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
      = (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t))
        ++ [((x + 1, b + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [← List.append_assoc, shiftr01_append0, shift_col]; rfl
  rw [eV]
  have hHU : Hd U := by
    intro hne
    have := hH (by simp)
    rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
  refine (GpT_ax (fun a ha => by have := hA a ha; omega) hA1 (by omega) H).tie b _ _ (x + 1)
    (Fr_mlift hW _ _) (by rw [← eV]; exact Fr_letter _ _) (by rw [← eV]; exact Hd_letter _ _) ?_
    (fun b'' hb'' Z hZ hbZ => ?_)
  · have eAB : (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t))
          ++ [((x + 1, b + 1, 0) : ℕ × ℕ × ℕ)]
        = (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift Y (b + liftOff H A o) t)) ++
          shiftr01 1 0 (mlift U (b + liftOff H A o) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
      rw [← eV, node_split]
    have eidx : (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t)).length
        = (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift Y (b + liftOff H A o) t)).length +
          (mlift U (b + liftOff H A o) t).length := by simp [shiftr01]; omega
    rw [eAB, eidx]
    have hPCA : PathCone b 1 (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift Y (b + liftOff H A o) t)) := by
      intro y hy _ hd
      rcases y with _ | y
      · show b < b + liftOff H A o + 1 + t; omega
      · exfalso
        rw [entry_cons] at hd
        have hy' : y < (mlift Y (b + liftOff H A o) t).length := by
          rw [mlift_length]; simp [shiftr01] at hy; omega
        rw [entry0_shiftr01 hy'] at hd
        have := getD_row0_ge (Fr_mlift hY (b + liftOff H A o) t) hy'
        omega
    have hB0 : shiftr01 1 0 (mlift U (b + liftOff H A o) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) ≠ [] →
        entry (shiftr01 1 0 (mlift U (b + liftOff H A o) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) 0 0
          = 1 + 1 := by
      intro _
      have hBH : Hd (mlift U (b + liftOff H A o) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
        have := Hd_mlift hH (b + liftOff H A o) t
        rwa [mlift_snoc_low U _ hcl] at this
      rw [entry0_shiftr01 (by simp), hBH (by simp)]
    rw [coneV_pathB hPCA hB0 (by simp [shiftr01]), coneV_shift0]
    have := coneV_mlift_up (by simp) hc (b + liftOff H A o) t
    rwa [mlift_snoc_low U _ hcl, ← mlift_length U (b + liftOff H A o) t] at this
  · have hFrYU : Fr (Y ++ U) := Fr_append hY hUc
    have hFrZ : Fr (mlift (Y ++ U) b (b'' - b) ++ shiftr01 x 0 Z) := by
      have hx1 : 1 ≤ x := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
      refine Fr_append (Fr_mlift hFrYU _ _) (fun y hy => ?_)
      simp only [shiftr01, List.mem_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      dsimp only; omega
    have h1 := hload b'' hb'' Z hZ hbZ (mlift W b (b'' - b)) (Fr_mlift hW _ _)
      (PVP_lift hA hA1 ho hW hPV hb'') t
    rw [mlift_letterU (Fr_mlift hW _ _) hFrZ
        (show b'' + liftOff H A o < b'' + liftOff H A o + 1 by omega),
      mlift_append_low (low_of_Wg hZ x (by omega))] at h1
    have hWU : Fr (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t) :=
      Fr_append (Fr_mlift hY _ _) (Fr_mlift hUc _ _)
    have eW : mlift (mlift W (b + liftOff H A o) t) b (b'' - b)
        = mlift (mlift W b (b'' - b)) (b'' + liftOff H A o) t := by
      rw [mlift_commk, show b + liftOff H A o + (b'' - b) = b'' + liftOff H A o by omega]
    have eKU : mlift (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t) b (b'' - b)
        = mlift (mlift (Y ++ U) b (b'' - b)) (b'' + liftOff H A o) t := by
      rw [← mlift_app hY hHU, mlift_commk,
        show b + liftOff H A o + (b'' - b) = b'' + liftOff H A o by omega]
    rw [mlift_app (Fr_mlift hW _ _) (Hd_letter _ _), eW, mlift_letter (by omega) hWU, eKU,
      show b + liftOff H A o + 1 + t + (b'' - b) = b'' + liftOff H A o + 1 + t by omega,
      List.append_assoc]
    rw [shiftr01_append0, shiftr01_add0] at h1
    simpa [List.append_assoc] using h1

end GyH
end TRIO
