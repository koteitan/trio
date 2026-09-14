/-
HdJ.lean: 右から見える道が錐（PathCone）の接頭辞 Y のあとの、深さ d の尾の段（木の単位の入れ子の位置の差し込み口の一般形）。

    語 P ++ (Y ++ U↑d)（U の頭は行 0 が 1、Y の右から見える行 0 ≤ d の列は行 1 > b）
- tstep_oper / tstep_orph / tstep_tie: GpT_ax の oper / orph / tie（HbM.fwH_*_step の深さ付きの形）。
- tstep_flat: 尾の flat (d+1, 0, 0) は直前の行 0 が d の列から始まる塊 M の複製（oper_snoc00''）。
- BotGe_pathcone: 道が錐なら、行 0 が d+1 の底の列の祖先は行 1 ≥ v（FarP の BotGe）。
-/
import HdI

namespace TRIO
namespace HdJ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH HdI

theorem Fr_shiftr {U : TrioSeq} (hU : Fr U) (d : ℕ) : Fr (shiftr01 d 0 U) := by
  intro y hy
  simp only [shiftr01, List.mem_map] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  have := hU p hp
  dsimp only; omega

theorem Hd_app_ne {Y B : TrioSeq} (hYH : Hd Y) (hYne : Y ≠ []) : Hd (Y ++ B) := by
  intro _
  rw [Small.entry_append_left (List.length_pos_iff.mpr hYne)]
  exact hYH hYne

theorem PathCone_mono {u u' d : ℕ} (h : u' ≤ u) {Y : TrioSeq} (hP : PathCone u d Y) : PathCone u' d Y :=
  fun y hy hvis hd => by have := hP y hy hvis hd; omega

/-- 道が錐なら、頭の行 0 が d+1 の尾の列の Y の中の祖先は行 1 > u。 -/
theorem pathcone_anc {u d : ℕ} {Y B : TrioSeq} (hP : PathCone u d Y) (hB0 : entry B 0 0 = d + 1)
    {k i : ℕ} (hk : k < Y.length)
    (h : Relation.ReflTransGen (nextrel0 (Y ++ B)) k (Y.length + i)) : u < entry Y 1 k := by
  refine hP k hk (fun k' hk1 hk2 => ?_) ?_
  · have := rtg0_rec h k' hk1 (by omega)
    rwa [Small.entry_append_left hk, Small.entry_append_left hk2] at this
  · have := rtg0_rec h Y.length hk (by omega)
    rw [Small.entry_append_left hk, show Y.length = Y.length + 0 from rfl, entry_append_right, hB0] at this
    omega

theorem BotGe_pathcone {v d : ℕ} (hv : 1 ≤ v) {Y : TrioSeq} (hP : PathCone (v - 1) d Y) :
    BotGe Y (d + 1) v := by
  intro c y hc hy hr
  have hB0 : entry [c] 0 0 = d + 1 := by rw [← hc]; rfl
  have := pathcone_anc (i := 0) hP hB0 hy hr
  omega

/-! ## 尾の段 -/

section
variable {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o) (f : ℕ → ℕ)
include hA hA1 ho

theorem tstep_oper {b d : ℕ} {P Y U : TrioSeq} (hP : Fr P) (hY : Fr Y) (hYH : Hd Y) (hYne : Y ≠ [])
    (hU : Fr U) (hlen : 2 ≤ U.length) (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → GpT A o f b (P ++ (Y ++ shiftr01 d 0 (U⟦m⟧)))) :
    GpT A o f b (P ++ (Y ++ shiftr01 d 0 U)) := by
  refine (GpT_ax hA hA1 ho f).oper b P (Y ++ shiftr01 d 0 U) hP (Fr_append hY (Fr_shiftr hU d))
    (Hd_app_ne hYH hYne) (by simp only [List.length_append, shiftr01_length]; omega) ?_
    (fun m hm => ?_)
  · have hidx : (Y ++ shiftr01 d 0 U).length - 1 = Y.length + ((shiftr01 d 0 U).length - 1) := by
      simp only [List.length_append, shiftr01_length]; omega
    rw [hidx, srow_append_right, shiftr01_length, srow_shiftr01]
    exact hasParent_append_right_of _ _ (hasParent_shiftr01.mpr hp)
  · rw [oper_shift Y U d m hlen hp]
    exact hIH m hm

theorem tstep_orph {b d : ℕ} {P Y U : TrioSeq} {h j : ℕ} (hP : Fr P) (hY : Fr Y) (hYH : Hd Y)
    (hYne : Y ≠ []) (hPC : PathCone b d Y) (hUj : Fr (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
    (hHU : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hj1 : 1 ≤ j) (hj : j ≤ b)
    (hnp : ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z →
      GpT A o f b (P ++ (Y ++ shiftr01 d 0 (U ++ shiftr01 h 0 z)))) :
    GpT A o f b (P ++ (Y ++ shiftr01 d 0 (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))) := by
  have eN : Y ++ shiftr01 d 0 (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])
      = (Y ++ shiftr01 d 0 U) ++ [((h + d, j, 0) : ℕ × ℕ × ℕ)] := by
    simp [shiftr01]
  have hB0 : entry (shiftr01 d 0 (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) 0 0 = d + 1 := by
    rw [entry0_shiftr01 (by simp), hHU (by simp)]; omega
  rw [eN]
  refine (GpT_ax hA hA1 ho f).orph b P (Y ++ shiftr01 d 0 U) (h + d) j hP
    (by rw [← eN]; exact Fr_append hY (Fr_shiftr hUj d)) (by rw [← eN]; exact Hd_app_ne hYH hYne)
    hj1 hj ?_ (fun z hz' hbz => ?_)
  · have hidx : (Y ++ shiftr01 d 0 U).length = Y.length + U.length := by
      simp only [List.length_append, shiftr01_length]
    rw [← eN, hidx]
    refine noParent_ctx (j := j) (by simp [shiftr01]) (fun k hk hrt => ?_) ?_ ?_
    · have := pathcone_anc hPC hB0 hk hrt
      omega
    · rw [entry1_shiftr01, show U.length = U.length + 0 from rfl, entry_append_right]; rfl
    · rw [hasParent_shiftr01]; exact hnp
  · have := hz z hz' hbz
    have ez : Y ++ shiftr01 d 0 (U ++ shiftr01 h 0 z) = (Y ++ shiftr01 d 0 U) ++ shiftr01 (h + d) 0 z := by
      rw [shiftr01_append0, shiftr01_add0, List.append_assoc]
    rwa [ez] at this

theorem tstep_tie {b d : ℕ} {P Y U : TrioSeq} {x : ℕ} (hP : Fr P) (hY : Fr Y) (hYH : Hd Y)
    (hYne : Y ≠ []) (hPC : PathCone b d Y) (hU : Fr (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
    (hHU : Hd (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) b U.length)
    (hload : ∀ b'', b ≤ b'' → ∀ Z ∈ Wg (2 * b''), based Z →
      GpT A o f b'' (mlift P b (b'' - b) ++ (mlift Y b (b'' - b) ++
        shiftr01 d 0 (mlift U b (b'' - b) ++ shiftr01 x 0 Z)))) :
    GpT A o f b (P ++ (Y ++ shiftr01 d 0 (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))) := by
  have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
  have eN : Y ++ shiftr01 d 0 (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])
      = (Y ++ shiftr01 d 0 U) ++ [((x + d, b + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [shiftr01]
  have hB0 : ∀ V : TrioSeq, Hd V → Fr V → (shiftr01 d 0 V ≠ [] → entry (shiftr01 d 0 V) 0 0 = d + 1) := by
    intro V hV _ hne
    have hVne : V ≠ [] := by intro h0; apply hne; simp [h0, shiftr01]
    rw [entry0_shiftr01 (List.length_pos_iff.mpr hVne), hV hVne]; omega
  rw [eN]
  refine (GpT_ax hA hA1 ho f).tie b P (Y ++ shiftr01 d 0 U) (x + d) hP
    (by rw [← eN]; exact Fr_append hY (Fr_shiftr hU d)) (by rw [← eN]; exact Hd_app_ne hYH hYne) ?_
    (fun b'' hb'' Z hZ hbZ => ?_)
  · have hidx : (Y ++ shiftr01 d 0 U).length = Y.length + U.length := by
      simp only [List.length_append, shiftr01_length]
    rw [← eN, hidx, coneV_pathB hPC (hB0 _ hHU hU) (by simp [shiftr01]), coneV_shift0]
    exact hc
  · have := hload b'' hb'' Z hZ hbZ
    have hHU' : Hd U := by
      intro hne
      have := hHU (by simp)
      rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
    have eM : mlift (P ++ (Y ++ shiftr01 d 0 U)) b (b'' - b) ++ shiftr01 (x + d) 0 Z
        = mlift P b (b'' - b) ++ (mlift Y b (b'' - b) ++
          shiftr01 d 0 (mlift U b (b'' - b) ++ shiftr01 x 0 Z)) := by
      rw [mlift_app hP (Hd_app_ne hYH hYne), mlift_pathB hPC (hB0 _ hHU' hUc)]
      have e3 : mlift (shiftr01 d 0 U) b (b'' - b) = shiftr01 d 0 (mlift U b (b'' - b)) := by
        rw [mlift_eq_slift, mlift_eq_slift, slift_shift0]
      rw [e3, shiftr01_append0, shiftr01_add0]
      simp only [List.append_assoc]
    rw [eM]; exact this

theorem tstep_flat {b d : ℕ} {P Y0 M : TrioSeq} (hP : Fr P) (hY0M : Fr (Y0 ++ M)) (hHd : Hd (Y0 ++ M))
    (hMne : M ≠ []) (hhead : entry M 0 0 = d)
    (htail : ∀ r, 1 ≤ r → r < M.length → d + 1 ≤ entry M 0 r)
    (hrep : ∀ n, GpT A o f b (P ++ (Y0 ++ (List.range n).flatMap (fun _ => M)))) :
    GpT A o f b (P ++ (Y0 ++ M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)])) := by
  have hMpos : 0 < M.length := List.length_pos_iff.mpr hMne
  have hlast : hasParent (Y0 ++ M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)])
      (srow (Y0 ++ M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)]) ((Y0 ++ M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)]).length - 1))
      ((Y0 ++ M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
    have hidx : (Y0 ++ M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)]).length - 1 = (Y0 ++ M).length + 0 := by simp
    rw [hidx, srow_append_right]
    have hs : srow [((d + 1, 0, 0) : ℕ × ℕ × ℕ)] 0 = 0 := rfl
    rw [hs]
    refine (hasParent_zero_iff (by simp)).mpr ⟨Y0.length, by simp; omega, ?_⟩
    rw [Small.entry_append_left (by simp; omega), entry_append_right, show Y0.length = Y0.length + 0 from rfl,
      entry_append_right, hhead]
    show d < d + 1; omega
  refine (GpT_ax hA hA1 ho f).oper b P (Y0 ++ M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)]) hP
    (Fr_append hY0M (GzF.Fr_single (by omega) _ _))
    (Hd_app_ne hHd (by simp [hMne]))
    (by simp; omega) hlast (fun m _ => ?_)
  have eO := oper_snoc00'' Y0 hMne (by omega) htail m
  rw [eO]
  exact hrep m

end

end HdJ
end TRIO
