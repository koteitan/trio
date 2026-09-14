/-
HdR.lean: 最上段の F のタイの子の木の良さ（高さの跳びの階層）の土台。

    BotC u Uss Q T := GTC CLT u (wLT u (Uss ++ [plugQ Q T], []))
    DT t v x := 全ての段 u ≥ v、良い Uss（GoodTT）、高さ t の良い道 Q（PT t）で BotC
    PT 0 Q := Q = []、PT (t+1) (Q ++ [us0]) := PT t Q ∧ DT t us0
- 最上段の木は段によらない（topTs u が段で語を作る）ので、像は要らない。
- 語は wLT u (Uss ++ [plugQ Q []], []) ++ (T の語)↑(|Q|+1)（wLT_plugQ）。接頭辞の道の頭は行 1 が u+1（PathCone_Ytop）。
- gtc_oper / gtc_orph / gtc_tie / gtc_flat: 道の錐の接頭辞のあとの GTC の段（HdJ の写し）。
-/
import HdQ

namespace TRIO
namespace HdR

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdL HdM HdN HdO HdP HdQ

/-! ## 道の錐の接頭辞のあとの GTC の段 -/

section
variable {C : ℕ → List TrioSeq → Prop}

theorem gtc_oper {u d : ℕ} {Y U : TrioSeq} (hlen : 2 ≤ U.length)
    (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ n, 1 ≤ n → GTC C u (Y ++ shiftr01 d 0 (U⟦n⟧))) : GTC C u (Y ++ shiftr01 d 0 U) := by
  refine GTC_oper (by simp only [List.length_append, shiftr01_length]; omega) ?_ (fun n hn => ?_)
  · have hidx : (Y ++ shiftr01 d 0 U).length - 1 = Y.length + ((shiftr01 d 0 U).length - 1) := by
      simp only [List.length_append, shiftr01_length]; omega
    rw [hidx, srow_append_right, shiftr01_length, srow_shiftr01]
    exact hasParent_append_right_of _ _ (hasParent_shiftr01.mpr hp)
  · rw [oper_shift Y U d n hlen hp]; exact hIH n hn

theorem gtc_orph {u d : ℕ} {Y U : TrioSeq} {h j : ℕ}
    (hPC : PathCone u d Y) (hHU : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hj1 : 1 ≤ j) (hj : j ≤ u)
    (hnp : ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z → GTC C u (Y ++ shiftr01 d 0 (U ++ shiftr01 h 0 z))) :
    GTC C u (Y ++ shiftr01 d 0 (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
  have eN : Y ++ shiftr01 d 0 (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])
      = (Y ++ shiftr01 d 0 U) ++ [((h + d, j, 0) : ℕ × ℕ × ℕ)] := by simp [shiftr01]
  have hB0 : entry (shiftr01 d 0 (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) 0 0 = d + 1 := by
    rw [entry0_shiftr01 (by simp), hHU (by simp)]; omega
  rw [eN]
  refine GTC_orph hj1 hj ?_ (fun z hz' hbz => ?_)
  · have hidx : ((Y ++ shiftr01 d 0 U) ++ [((h + d, j, 0) : ℕ × ℕ × ℕ)]).length - 1
        = Y.length + U.length := by
      simp only [List.length_append, shiftr01_length, List.length_singleton]; omega
    rw [hidx, ← eN]
    refine noParent_ctx (j := j) (by simp [shiftr01]) (fun k hk hrt => ?_) ?_ ?_
    · have := pathcone_anc hPC hB0 hk hrt
      omega
    · rw [entry1_shiftr01, show U.length = U.length + 0 from rfl, entry_append_right]; rfl
    · rw [hasParent_shiftr01]; exact hnp
  · have := hz z hz' hbz
    have ez : Y ++ shiftr01 d 0 (U ++ shiftr01 h 0 z) = (Y ++ shiftr01 d 0 U) ++ shiftr01 (h + d) 0 z := by
      rw [shiftr01_append0, shiftr01_add0, List.append_assoc]
    rwa [ez] at this

theorem gtc_tie {u d : ℕ} {Y U : TrioSeq} {x : ℕ}
    (hPC : PathCone u d Y) (hU : Fr (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]))
    (hHU : Hd (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u U.length)
    (hload : ∀ u', u ≤ u' → ∀ Z ∈ Wg (2 * u'), based Z →
      GTC C u' (mlift Y u (u' - u) ++ shiftr01 d 0 (mlift U u (u' - u) ++ shiftr01 x 0 Z)))
    (hClift : ∀ L, C u L → ∀ u', u ≤ u' → C u' (L.map (fun X => mlift X u (u' - u)))) :
    GTC C u (Y ++ shiftr01 d 0 (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])) := by
  have eN : Y ++ shiftr01 d 0 (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])
      = (Y ++ shiftr01 d 0 U) ++ [((x + d, u + 1, 0) : ℕ × ℕ × ℕ)] := by simp [shiftr01]
  have hB0 : ∀ V : TrioSeq, Hd V → (shiftr01 d 0 V ≠ [] → entry (shiftr01 d 0 V) 0 0 = d + 1) := by
    intro V hV hne
    have hVne : V ≠ [] := by intro h0; apply hne; simp [h0, shiftr01]
    rw [entry0_shiftr01 (List.length_pos_iff.mpr hVne), hV hVne]; omega
  have hHU' : Hd U := by
    intro hne
    have := hHU (by simp)
    rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
  rw [eN]
  refine GTC_tie ?_ (fun u' hu' Z hZ hbZ => ?_) hClift
  · have hidx : (Y ++ shiftr01 d 0 U).length = Y.length + U.length := by
      simp only [List.length_append, shiftr01_length]
    rw [← eN, hidx, coneV_pathB hPC (hB0 _ hHU) (by simp [shiftr01]), coneV_shift0]
    exact hc
  · have := hload u' hu' Z hZ hbZ
    have eM : mlift (Y ++ shiftr01 d 0 U) u (u' - u) ++ shiftr01 (x + d) 0 Z
        = mlift Y u (u' - u) ++ shiftr01 d 0 (mlift U u (u' - u) ++ shiftr01 x 0 Z) := by
      rw [mlift_pathB hPC (hB0 _ hHU')]
      have e3 : mlift (shiftr01 d 0 U) u (u' - u) = shiftr01 d 0 (mlift U u (u' - u)) := by
        rw [mlift_eq_slift, mlift_eq_slift, slift_shift0]
      rw [e3, shiftr01_append0, shiftr01_add0]
      simp only [List.append_assoc]
    rw [eM]; exact this

theorem gtc_flat {u d : ℕ} {Y0 M : TrioSeq} (hMne : M ≠ [])
    (hhead : entry M 0 0 = d) (htail : ∀ r, 1 ≤ r → r < M.length → d + 1 ≤ entry M 0 r)
    (hrep : ∀ n, GTC C u (Y0 ++ (List.range n).flatMap (fun _ => M))) :
    GTC C u (Y0 ++ M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)]) := by
  have hMpos : 0 < M.length := List.length_pos_iff.mpr hMne
  have hlast : hasParent (M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)])
      (srow (M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)]) ((M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)]).length - 1))
      ((M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
    have hidx : (M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)]).length - 1 = M.length + 0 := by simp
    rw [hidx, srow_append_right]
    have hs : srow [((d + 1, 0, 0) : ℕ × ℕ × ℕ)] 0 = 0 := rfl
    rw [hs]
    refine (hasParent_zero_iff (by simp)).mpr ⟨0, by omega, ?_⟩
    rw [Small.entry_append_left hMpos, entry_append_right, hhead]
    show d < d + 1; omega
  refine GTC_oper ?_ ?_ (fun n _ => ?_)
  · simp only [List.length_append, List.length_singleton]; omega
  · have hidx : (Y0 ++ M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)]).length - 1
        = Y0.length + ((M ++ [((d + 1, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [hidx, List.append_assoc, srow_append_right]
    exact hasParent_append_right_of _ _ hlast
  · rw [oper_snoc00'' Y0 hMne (by omega) htail n]
    exact hrep n

end

/-! ## 語の形 -/

theorem farTs_append : ∀ us vs : List UT, farTs (us ++ vs) = farTs us ++ farTs vs
  | [], vs => by simp [farTs]
  | x :: us, vs => by simp only [List.cons_append, farTs, farTs_append us vs]

theorem farTs_plugQ : ∀ (Q : List (List UT)) (T : List UT),
    farTs (plugQ Q T) = plugQ (Q.map farTs) (farTs T)
  | [], T => by simp [plugQ]
  | q :: Q, T => by
      simp only [plugQ, List.map_cons, farTs_append]
      rw [show farTs [UT.tie 0 (plugQ Q T)] = [UT.tie 0 (farTs (plugQ Q T))] by simp [farTs, farT],
        farTs_plugQ Q T]

theorem topTs_plugQ (u : ℕ) (Q : List (List UT)) (T : List UT) :
    topTs u (plugQ Q T) = topTs u (plugQ Q []) ++ shiftr01 Q.length 0 (topTs u T) := by
  rw [← chT_farTs, ← chT_farTs, ← chT_farTs, farTs_plugQ, farTs_plugQ, chT_plugQ, chT_plugQ,
    List.length_map]
  simp [farTs, chT, shiftr01]

theorem wLT_plugQ (u : ℕ) (Uss Q : List (List UT)) (T : List UT) :
    wLT u (Uss ++ [plugQ Q T], [])
      = wLT u (Uss ++ [plugQ Q []], []) ++ shiftr01 (Q.length + 1) 0 (topTs u T) := by
  simp only [wLT, List.map_append, List.map_singleton, FTL0_snoc, unitsC, List.flatMap_nil,
    List.append_nil]
  rw [topTs_plugQ u Q T, shiftr01_append0, shiftr01_add0]
  simp

theorem PathCone_Ytop (u : ℕ) (Uss Q : List (List UT)) (hQ : ∀ us ∈ Q, TRaws u us) :
    PathCone u (Q.length + 1) (wLT u (Uss ++ [plugQ Q []], [])) := by
  have e1 : topTs u (plugQ Q []) = chTQ u (u + 1) u (Q.map farTs) := by
    rw [← chT_farTs, farTs_plugQ, chT_plugQ]; simp [farTs, chT, shiftr01]
  have e : wLT u (Uss ++ [plugQ Q []], [])
      = [] ++ FTL0 (u + 1) (Uss.map (topTs u)) ++ [((0 + 1, u + 1, 0) : ℕ × ℕ × ℕ)] ++
          shiftr01 1 0 (chTQ u (u + 1) u (Q.map farTs)) := by
    simp only [wLT, List.map_append, List.map_singleton, FTL0_snoc, unitsC, List.flatMap_nil,
      List.append_nil, e1]
    simp
  rw [e]
  have h0 : PathCone u 0 ([] : TrioSeq) := fun y hy => by simp at hy
  have h1 := PathCone_tieSnoc (show u < u + 1 by omega) h0 (V := FTL0 (u + 1) (Uss.map (topTs u)))
    (fun c hc => Fr_FTL0 _ _ c hc)
  have h2 := PathCone_chTQ (show u < u + 1 by omega) u u (u + 0) (Q.map farTs) (0 + 1) _
    (fun us h' => by
      simp only [List.mem_map] at h'
      obtain ⟨us0, h0', rfl⟩ := h'
      exact RawTs_farTs us0 (hQ us0 h0')) h1
  rwa [List.length_map, show 0 + 1 + Q.length = Q.length + 1 by omega] at h2

theorem TRaws_plugQ {u : ℕ} : ∀ (Q : List (List UT)) (T : List UT), (∀ us ∈ Q, TRaws u us) →
    TRaws u T → TRaws u (plugQ Q T)
  | [], T, _, hT => hT
  | q :: Q, T, hQ, hT => by
      simp only [plugQ]
      exact TRaws_snoc.mpr ⟨hQ q (by simp), rfl, TRaws_plugQ Q T (fun us h => hQ us (by simp [h])) hT⟩

theorem Fr_Ytop (u : ℕ) (Uss Q : List (List UT)) : Fr (wLT u (Uss ++ [plugQ Q []], [])) :=
  fun x hx => Fr_wLT u _ x hx

theorem mlift_Ytop {u u' : ℕ} (hu : u ≤ u') {Uss Q : List (List UT)} (hU : ∀ us ∈ Uss, TRaws u us)
    (hQ : ∀ us ∈ Q, TRaws u us) :
    mlift (wLT u (Uss ++ [plugQ Q []], [])) u (u' - u) = wLT u' (Uss ++ [plugQ Q []], []) := by
  refine mlift_wLT hu (fun us hus => ?_) (by simp [GzJ.NoTie]) (RawU_nil u)
  rcases List.mem_append.mp hus with hus | hus
  · exact hU us hus
  · simp at hus; subst hus; exact TRaws_plugQ Q [] hQ trivial

/-! ## 跳びの階層 -/

def GoodTT (v : ℕ) (Uss : List (List UT)) : Prop := ∀ u, v ≤ u → GTC CLT u (wLT u (Uss, []))

def BotC (u : ℕ) (Uss Q : List (List UT)) (T : List UT) : Prop :=
  GTC CLT u (wLT u (Uss ++ [plugQ Q T], []))

theorem BotC_snoc_eq (u : ℕ) (Uss Q : List (List UT)) (us T : List UT) :
    BotC u Uss (Q ++ [us]) T = BotC u Uss Q (us ++ [UT.tie 0 T]) := by
  unfold BotC; rw [plugQ_snoc]

def DTdef (P : ℕ → List (List UT) → Prop) (v : ℕ) (x : List UT) : Prop :=
  TRaws v x ∧ ∀ u, v ≤ u → ∀ Uss, (∀ us ∈ Uss, TRaws u us) → GoodTT u Uss →
    ∀ Q, P u Q → BotC u Uss Q x

def PT : ℕ → ℕ → List (List UT) → Prop
  | 0, _, Q => Q = []
  | t + 1, u, Q => ∃ Q' us0, Q = Q' ++ [us0] ∧ PT t u Q' ∧ DTdef (PT t) u us0

/-- ★ 最上段の高さ t の子の並びの良さ。 -/
def DT (t : ℕ) : ℕ → List UT → Prop := DTdef (PT t)

theorem DT_mono {t v v' : ℕ} {x : List UT} (h : DT t v x) (hv : v ≤ v') : DT t v' x :=
  ⟨TRaws_mono hv x h.1, fun u hu => h.2 u (le_trans hv hu)⟩

theorem PT_mono : ∀ {t u u' : ℕ} {Q : List (List UT)}, PT t u Q → u ≤ u' → PT t u' Q
  | 0, _, _, _, h, _ => h
  | t + 1, _, _, _, h, hu => by
      obtain ⟨Q', us0, rfl, hQ', hus0⟩ := h
      exact ⟨Q', us0, rfl, PT_mono hQ' hu, DT_mono (t := t) hus0 hu⟩

theorem PT_raw : ∀ {t u : ℕ} {Q : List (List UT)}, PT t u Q → ∀ us ∈ Q, TRaws u us
  | 0, _, _, h => by intro us hus; simp only [PT] at h; subst h; simp at hus
  | t + 1, _, _, h => by
      obtain ⟨Q', us0, rfl, hQ', hus0⟩ := h
      intro us hus
      rcases List.mem_append.mp hus with hus | hus
      · exact PT_raw hQ' us hus
      · simp at hus; subst hus; exact hus0.1

theorem PT_length : ∀ {t u : ℕ} {Q : List (List UT)}, PT t u Q → Q.length = t
  | 0, _, _, h => by simp only [PT] at h; subst h; rfl
  | t + 1, _, _, h => by
      obtain ⟨Q', us0, rfl, hQ', -⟩ := h
      simp [PT_length hQ']

theorem DT_good {t v : ℕ} {x : List UT} (h : DT t v x) {u : ℕ} (hvu : v ≤ u) {Uss : List (List UT)}
    (hU : ∀ us ∈ Uss, TRaws u us) (hG : GoodTT u Uss) {Q : List (List UT)} (hQ : PT t u Q) :
    GoodTT u (Uss ++ [plugQ Q x]) :=
  fun u' hu' => by
    have := h.2 u' (le_trans hvu hu') Uss (fun us hus => TRaws_mono hu' us (hU us hus))
      (fun u'' hu'' => hG u'' (le_trans hu' hu'')) Q (PT_mono hQ hu')
    exact this

theorem DT_jump {t v : ℕ} {cs : List UT} (h : DT (t + 1) v cs) {u : ℕ} (hvu : v ≤ u) {us0 : List UT}
    (hus : DT t u us0) : DT t u (us0 ++ [UT.tie 0 cs]) := by
  refine ⟨TRaws_snoc.mpr ⟨hus.1, rfl, TRaws_mono hvu cs h.1⟩, fun u' hu' Uss hU hG Q hQ => ?_⟩
  rw [← BotC_snoc_eq]
  exact h.2 u' (le_trans hvu hu') Uss hU hG (Q ++ [us0]) ⟨Q, us0, rfl, hQ, DT_mono hus hu'⟩

theorem DT_of_jump {t v : ℕ} {cs : List UT} (hraw : TRaws v cs)
    (hJ : ∀ u, v ≤ u → ∀ us0, DT t u us0 → DT t u (us0 ++ [UT.tie 0 cs])) : DT (t + 1) v cs := by
  refine ⟨hraw, fun u hu Uss hU hG Q hQ => ?_⟩
  obtain ⟨Q', us0, rfl, hQ', hus0⟩ := hQ
  rw [BotC_snoc_eq]
  exact (hJ u hu us0 hus0).2 u le_rfl Uss hU hG Q' hQ'

theorem DT_tie {t v : ℕ} {us cs : List UT} (hus : DT t v us) (hcs : DT (t + 1) v cs) :
    DT t v (us ++ [UT.tie 0 cs]) := DT_jump hcs le_rfl hus

/-- ★ 最上段の新しい F のタイ（子の並びは空）。 -/
theorem DT_nil0 (v : ℕ) : DT 0 v [] := by
  refine ⟨trivial, fun u _ Uss hU hG Q hQ => ?_⟩
  simp only [PT] at hQ
  subst hQ
  show GTC CLT u (wLT u (Uss ++ [[]], []))
  have e : wLT u (Uss ++ [[]], []) = wLT u (Uss, []) ++ [((1, u + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [wLT, FTL0_snoc, topTs, unitsC, shiftr01]
  rw [e]
  refine GTC_tie (C := CLT) (coneV_top (Fr_wLT u _) u) (fun u' hu' Z hZ hbZ => ?_)
    (fun L hC u'' hu'' => CLT_lift L u hC u'' hu'')
  have hR' : ∀ us ∈ Uss, TRaws u' us := fun us hus => TRaws_mono hu' us (hU us hus)
  rw [mlift_wLT hu' (p := (Uss, [])) hU (by simp [GzJ.NoTie]) (RawU_nil u)]
  have := GTC_load_CLT (v := u') (Uss := Uss) (us := []) hR' (by simp [GzJ.NoTie]) (RawU_nil u')
    (hG u' hu') Z hZ hbZ
  rwa [show wLT u' (Uss, [] ++ [some Z]) = wLT u' (Uss, []) ++ shiftr01 1 0 Z by
    simp [wLT, unitsC, unitC]] at this

end HdR
end TRIO
