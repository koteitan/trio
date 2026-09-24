/-
PmD.lean: 木のクラス TX（深い葉を任意の接頭辞の後ろに置ける、深い節点の中の先頭 tie 1 []）と、その遠い像側。

要点: 許される道の集合（PSOK, PSDec, 段 0 の延長で閉じる, 最後の段 0, 空の並びが良い）全部の和集合 UF は
それ自体が許される集合。なので「全ての許される集合で良い」＝「UF で良い」。深い葉の塔が要求する
「接頭辞がより深い集合でも良い」は UF 1 つで済む（より深い集合は UF の部分集合）。
-/
import PmC

namespace TRIO
namespace PmD

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ HeK
open PmB PmC

/-! ## 木のクラス TX -/

/-- 木のクラス（段 v）。並びを後ろから 1 つずつ作る。
- deep: (0,true) の並びの後ろに深い葉。
- head1: 深い節点 tie 1 の子の並び (1,false) の先頭の tie 1 []。 -/
inductive TX (v : ℕ) : ℕ → Bool → List UT → Prop
  | nil (p : ℕ) (cl : Bool) : TX v p cl []
  | ch {p : ℕ} {cl : Bool} {us : List UT} {Z : TrioSeq} :
      TX v p cl us → Z ∈ Wg (2 * v) → based Z → TX v p cl (us ++ [UT.ch Z])
  | tie0 {p : ℕ} {cl : Bool} {us cs : List UT} :
      TX v p cl us → TX v 0 true cs → TX v p cl (us ++ [UT.tie 0 cs])
  | up {p : ℕ} {us : List UT} {l : ℕ} {cs : List UT} :
      TX v p true us → p < l + 1 → TX v (l + 1) false cs → TX v p true (us ++ [UT.tie (l + 1) cs])
  | deep {us : List UT} : TX v 0 true us → TX v 0 true (us ++ [deepU])
  | head1 : TX v 1 false [UT.tie 1 []]

theorem TX_raw {v : ℕ} {p : ℕ} {cl : Bool} {us : List UT} (h : TX v p cl us) : TRawLs v us := by
  induction h with
  | nil => trivial
  | ch _ hZ hb ih => exact TRawLs_snoc.mpr ⟨ih, hZ, hb⟩
  | tie0 _ _ ih ihc => exact TRawLs_snoc.mpr ⟨ih, ihc⟩
  | up _ _ _ ih ihc => exact TRawLs_snoc.mpr ⟨ih, ihc⟩
  | deep _ ih => exact TRawLs_snoc.mpr ⟨ih, by simp [deepU, TRawL, TRawLs]⟩
  | head1 => simp [TRawL, TRawLs]

theorem TX_mono {v u : ℕ} (hvu : v ≤ u) {p : ℕ} {cl : Bool} {us : List UT} (h : TX v p cl us) :
    TX u p cl us := by
  induction h with
  | nil p cl => exact TX.nil p cl
  | ch _ hZ hb ih => exact TX.ch ih (Wg_mono (by omega) hZ) hb
  | tie0 _ _ ih ihc => exact TX.tie0 ih ihc
  | up _ hpl _ ih ihc => exact TX.up ih hpl ihc
  | deep _ ih => exact TX.deep ih
  | head1 => exact TX.head1

theorem farTs_snoc (us : List UT) (x : UT) : farTs (us ++ [x]) = farTs us ++ [farT x] := by
  rw [HdR.farTs_append]; rfl

/-! ## 遠い像側: 許される集合の和集合 UF -/

/-- 許される集合（遠い像側、段 0 の子の位置）。 -/
def AdmF (P : HeB.PS) : Prop :=
  HeB.PSOK P ∧ HeC.PSDec P ∧ HeB.Ext P 0 P ∧ HeC.LastL P 0 ∧
    ∀ (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (c : ℕ), HeB.Gd P A k H c []

/-- ★ 許される集合全部の和集合。 -/
def UF : HeB.PS := fun C o f u Q => ∃ P, AdmF P ∧ P C o f u Q

theorem UF_sub {P : HeB.PS} (hP : AdmF P) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {x : List UT}
    (h : HeB.Gd UF A k H c x) : HeB.Gd P A k H c x :=
  HeB.Gd_mono (fun C o f u Q hQ => ⟨P, hP, hQ⟩) h

theorem UF_PSOK : HeB.PSOK UF where
  raw := fun C o f u Q ⟨P, hP, hQ⟩ => hP.1.raw C o f u Q hQ
  emb := fun C o f u Q ⟨P, hP, hQ⟩ G S o2 f2 hE => ⟨P, hP, hP.1.emb C o f u Q hQ G S o2 f2 hE⟩
  lift := fun C o f u Q ⟨P, hP, hQ⟩ u' hu => ⟨P, hP, hP.1.lift C o f u Q hQ u' hu⟩

theorem UF_PSDec : HeC.PSDec UF := by
  rintro C o f u Q ⟨P, hP, hQ⟩
  rcases hP.2.1 C o f u Q hQ with h | ⟨P', Q', us0, l, h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨P', Q', us0, l, h1, h2, h3,
      fun C' o' f' u' Q'' us hQ'' hus => ⟨P, hP, h4 C' o' f' u' Q'' us hQ'' hus⟩⟩

theorem UF_closed : HeB.Ext UF 0 UF := by
  rintro C o f u Q us ⟨P, hP, hQ⟩ hus
  exact ⟨P, hP, hP.2.2.1 C o f u Q us hQ (UF_sub hP hus)⟩

theorem UF_last : HeC.LastL UF 0 := fun C o f u Q ⟨P, hP, hQ⟩ => hP.2.2.2.1 C o f u Q hQ

theorem UF_nil {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} : HeB.Gd UF A k H c [] := by
  refine ⟨by simp [RawTs], fun G S o f hE u hcu Lds hL Q hQ => ?_⟩
  obtain ⟨P, hP, hQ⟩ := hQ
  exact (hP.2.2.2.2 A k H c).2 G S o f hE u hcu Lds hL Q hQ

theorem AdmF_chS0 {P : HeB.PS} (hP : HeB.PSOK P) (hD : HeC.PSDec P) : AdmF (HeC.chS0 P) :=
  ⟨HeC.PSOK_chS0 hP, HeC.PSDec_chS0 P, HeC.chS0_closed P, HeC.LastL_chS0 P,
    fun _ _ _ _ => HeG.Gd_nil_chS0 hP hD⟩

theorem AdmF_P0 : AdmF HeC.P0 :=
  ⟨HeC.PSOK_P0, HeC.PSDec_P0, HeC.P0_closed, HeC.LastL_P0, fun _ _ _ _ => HeG.Gd_nil_P0⟩

theorem Gd_nil_chU1 {l : ℕ} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} :
    HeB.Gd (HeC.chU UF (l + 1)) A k H c [] :=
  HeH.Gd_nil_chU UF_PSOK UF_closed UF_last (by omega)

/-! ## 遠い像側: 任意の接頭辞の後ろの深い葉 -/

theorem imgT_Lt (A : List ℕ) (H G : ℕ → ℕ) (c u : ℕ) (pre : List UT) : ∀ j,
    HeB.imgT A H G c u (Lt pre j) = Lt (HeB.imgT A H G c u pre) j
  | 0 => by simp only [Lt, HeB.imgT_append, HeB.imgT_tie, HeB.imgT_nil]
  | j + 1 => by
      simp only [Lt, HeB.imgT_append, HeB.imgT_tie, imgT_Lt A H G c u pre j]

section
variable {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k) (hAk : ∀ a ∈ A, a < k) {H : ℕ → ℕ}
include hA01 hk hAk

/-- UF で良い並びの後ろの深い葉の塔は UF で良い。 -/
theorem Gd_Lt {c : ℕ} {pre : List UT} (h : HeB.Gd UF A k H c pre) : ∀ j, HeB.Gd UF A k H c (Lt pre j)
  | 0 => HeH.Gd_upleaf UF_PSOK UF_closed UF_last (by omega) hA01 hk hAk h
  | j + 1 => by
      have hin : HeB.Gd (HeC.chS0 (HeC.chU UF 1)) A k H c (Lt pre j) :=
        UF_sub (AdmF_chS0 (HeC.PSOK_chU UF_PSOK 1) (HeC.PSDec_chU UF 1)) (Gd_Lt h j)
      have hcs := HeB.Gd_tie (HeC.Ext_chS0 (HeC.chU UF 1)) hA01 hk hAk (Gd_nil_chU1 (l := 0)) hin
      rw [List.nil_append] at hcs
      exact HeB.Gd_tie (HeC.Ext_chU UF 1) hA01 hk hAk h hcs

/-- ★★★ 遠い像側: UF で良い並びの後ろに深い葉を置いても UF で良い。 -/
theorem Gd_deepAfter {c : ℕ} {pre : List UT} (h : HeB.Gd UF A k H c pre) :
    HeB.Gd UF A k H c (pre ++ [deepU]) := by
  refine ⟨RawTs_snoc.mpr ⟨h.1, by simp [deepU, RawTs, RawT]⟩, fun G S o f hE u hcu Lds hL Q hQ => ?_⟩
  intro b hub ws hC hR
  have hA := hE.2.2.1
  have hA1 := hE.2.2.2.1
  have ho := hE.2.2.2.2.1
  have hRaw := HeB.RawTs_imgT hE hcu h.1
  rw [HeB.imgT_append, show HeB.imgT A H G c u [deepU] = [deepU] from PmA.imgT_deep A H G c u]
  have hrep : ∀ j, GpT (S ++ A) o f b (farWt b (b + liftOff f (S ++ A) o + 1)
      (ws ++ [(Lds ++ [HeB.plugQ Q (Lt (HeB.imgT A H G c u pre) j)], u, [])])) := by
    intro j
    have := (Gd_Lt hA01 hk hAk h j).2 G S o f hE u hcu Lds hL Q hQ b hub ws hC hR
    rwa [imgT_Lt] at this
  obtain ⟨q0, hq0⟩ : ∃ q0, q0 = b + liftOff f (S ++ A) o := ⟨_, rfl⟩
  rw [← hq0] at hrep ⊢
  obtain ⟨E, hEd⟩ : ∃ E, E = chT b (q0+1) u (HeB.imgT A H G c u pre) := ⟨_, rfl⟩
  have hEF : Fr E := by rw [hEd]; exact Fr_chT _ hRaw
  have eC : chT b (q0+1) u (HeB.imgT A H G c u pre ++ [deepU])
      = E ++ [((1, q0+1+1, 0) : ℕ×ℕ×ℕ), ((2, q0+1+1, 0) : ℕ×ℕ×ℕ)] := by
    rw [chT_append, hEd, show deepU = UT.tie 1 [UT.tie 1 []] from rfl, PmA.chT_deep]
  have htow : ∀ j, (tow (q0+1) 0 (E ++ [((1,q0+1+1,0):ℕ×ℕ×ℕ),((2,q0+1+1,0):ℕ×ℕ×ℕ)]) (j+1) : TrioSeq)
      = ((0,q0+1,0):ℕ×ℕ×ℕ) :: chT b (q0+1) u (Lt (HeB.imgT A H G c u pre) j) := by
    intro j; rw [hEd]; exact chT_Lt b (q0+1) u _ j
  have e1 : (((1, q0+1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0
        (E ++ [((1, q0+1+1, 0) : ℕ×ℕ×ℕ), ((2, q0+1+1, 0) : ℕ×ℕ×ℕ)]))
      = shiftr01 1 0 (((0, q0+1, 0) : ℕ×ℕ×ℕ) ::
          (E ++ [((1,q0+1+1,0):ℕ×ℕ×ℕ), ((2,q0+1+1,0):ℕ×ℕ×ℕ)])) := by
    simp [shiftr01]
  rcases List.eq_nil_or_concat Q with rfl | ⟨Q', ⟨v, p'⟩, rfl⟩
  · obtain ⟨Yp, hYpd⟩ : ∃ Yp, Yp = ((1, q0+1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FTLt b (q0+1) u Lds) := ⟨_, rfl⟩
    have eW : ∀ T : List UT, farWt b (q0+1) (ws ++ [(Lds ++ [HeB.plugQ [] T], u, [])])
        = farWt b (q0+1) ws ++ (Yp ++ shiftr01 1 0
            (((1, q0+1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b (q0+1) u T))) := by
      intro T
      rw [show HeB.plugQ [] T = T from rfl, farWt_snoc, hYpd]
      simp [fwH, FTLt_snoc, mlift_nil, shiftr01_append0]
    have hYpF : Fr Yp := by rw [hYpd]; exact Fr_letter _ _
    have hYpne : Yp ≠ [] := by rw [hYpd]; simp
    have hYpH : Hd Yp := by rw [hYpd]; exact fun _ => rfl
    rw [eW, eC, e1]
    refine upleaf_deep_coreE_far hA hA1 ho f (Fr_farWt _ _ _) hYpF hYpH hYpne hEF
      (d := 1) (q := q0+1) (m := q0+1+1) (by omega) (by omega) ?_
    intro m' hm'
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    rw [htow j]
    have := hrep j
    rw [eW] at this
    simpa [shiftr01] using this
  · simp only [List.concat_eq_append] at hQ hrep ⊢
    have hp' : p' = 0 := by have := UF_last _ _ _ _ _ hQ; rwa [HeC.lastL_snoc] at this
    subst hp'
    have hv := UF_PSOK.raw _ _ _ _ _ hQ (v, 0) (by simp)
    obtain ⟨Yp, hYpd⟩ : ∃ Yp, Yp = fwH b (q0+1) (FTLt b (q0+1) u (Lds ++ [HeB.plugQ Q' []])) u [] ++
        shiftr01 (Q'.length + 2) 0 (chT b (q0+1) u v) := ⟨_, rfl⟩
    have eW : ∀ T : List UT, farWt b (q0+1) (ws ++ [(Lds ++ [HeB.plugQ (Q' ++ [(v, 0)]) T], u, [])])
        = farWt b (q0+1) ws ++ (Yp ++ shiftr01 (Q'.length + 2) 0
            (((1, q0+1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b (q0+1) u T))) := by
      intro T
      rw [HeB.plugQ_snoc, HeD.farWt_botT, hYpd, chT_append, shiftr01_append0]
      simp [chT, unitT, List.append_assoc]
    have hYpF : Fr Yp := by rw [hYpd]; exact Fr_append (Fr_fwH _ _ _ _ _) (Fr_shiftr (Fr_chT _ hv) _)
    have hYpne : Yp ≠ [] := by rw [hYpd]; simp [fwH]
    have hYpH : Hd Yp := by rw [hYpd]; exact Hd_app_ne (Hd_fwH _ _ _ _ _) (by simp [fwH])
    rw [eW, eC, e1]
    refine upleaf_deep_coreE_far hA hA1 ho f (Fr_farWt _ _ _) hYpF hYpH hYpne hEF
      (d := Q'.length + 2) (q := q0+1) (m := q0+1+1) (by omega) (by omega) ?_
    intro m' hm'
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    rw [htow j]
    have := hrep j
    rw [eW] at this
    simpa [shiftr01] using this

end

/-- ★ 遠い像側: 深い節点の子の位置（chU UF 1）で先頭の tie 1 [] は良い。 -/
theorem Gd_head1 {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} :
    HeB.Gd (HeC.chU UF 1) A k H c [UT.tie 1 []] := by
  refine ⟨by simp [RawTs, RawT], fun G S o f hE u _ Lds hL Q hQ => ?_⟩
  obtain ⟨Q', us, rfl, hQ', hus⟩ := hQ
  rw [show HeB.imgT A H G c u [UT.tie 1 []] = [UT.tie 1 []] by
    simp only [HeB.imgT_tie, HeB.imgT_nil], HeB.BotT_snoc_eq]
  have := (Gd_deepAfter hE.2.2.2.1 hE.2.2.2.2.1 hE.2.2.1 hus).2 (fun _ => 0) [] o f
    (HcM.EmbU_triv hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 f) u le_rfl Lds hL Q' hQ'
  rwa [HeB.imgT_zero] at this

/-! ## 遠い像側の本定理: TX の並びの遠い像は良い -/

section
variable {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k) (hAk : ∀ a ∈ A, a < k) (H : ℕ → ℕ)
include hA01 hk hAk

/-- ★★★ TX の並びの遠い像は、(0,true) なら UF で、(l+1,false) なら chU UF (l+1) で良い。 -/
theorem Gd_TX {c p : ℕ} {cl : Bool} {us : List UT} (h : TX c p cl us) :
    (cl = true → p = 0 → HeB.Gd UF A k H c (farTs us)) ∧
    (∀ l, cl = false → p = l + 1 → HeB.Gd (HeC.chU UF (l + 1)) A k H c (farTs us)) := by
  induction h with
  | nil p cl => exact ⟨fun _ _ => UF_nil, fun l _ _ => Gd_nil_chU1⟩
  | @ch p cl us Z _ hZ hb ih =>
      have hX : HeG.okLowP c (shiftr01 1 0 Z) := by
        have := HeG.okLowP_load (HeG.okLowP_nil c) hZ hb
        simpa using this
      rw [farTs_snoc]
      exact ⟨fun h1 h2 => HeI.Gd_snoc_ch UF_PSOK UF_PSDec hA01 hk (ih.1 h1 h2) hX,
        fun l h1 h2 => HeI.Gd_snoc_ch (HeC.PSOK_chU UF_PSOK (l + 1)) (HeC.PSDec_chU UF (l + 1)) hA01 hk
          (ih.2 l h1 h2) hX⟩
  | @tie0 p cl us cs _ _ ih ihc =>
      rw [farTs_snoc]
      have hcs := ihc.1 rfl rfl
      refine ⟨fun h1 h2 => ?_, fun l h1 h2 => ?_⟩
      · exact HeB.Gd_tie (HeC.Ext_chS0 UF) hA01 hk hAk (ih.1 h1 h2)
          (UF_sub (AdmF_chS0 UF_PSOK UF_PSDec) hcs)
      · exact HeB.Gd_tie (HeC.Ext_chS0 (HeC.chU UF (l + 1))) hA01 hk hAk (ih.2 l h1 h2)
          (UF_sub (AdmF_chS0 (HeC.PSOK_chU UF_PSOK (l + 1)) (HeC.PSDec_chU UF (l + 1))) hcs)
  | @up p us l cs _ _ _ ih ihc =>
      rw [farTs_snoc]
      refine ⟨fun _ h2 => ?_, fun _ h1 _ => absurd h1 (by simp)⟩
      exact HeB.Gd_tie (HeC.Ext_chU UF (l + 1)) hA01 hk hAk (ih.1 rfl h2) (ihc.2 l rfl rfl)
  | @deep us _ ih =>
      rw [farTs_snoc]
      refine ⟨fun _ _ => ?_, fun _ h1 _ => absurd h1 (by simp)⟩
      exact Gd_deepAfter hA01 hk hAk (ih.1 rfl rfl)
  | head1 =>
      refine ⟨fun h1 _ => absurd h1 (by simp), fun l _ h2 => ?_⟩
      obtain rfl : l = 0 := by omega
      exact Gd_head1

end

/-- ★ TX の並びを後ろに足しても WOK。 -/
theorem WOK_snoc_TX {u : ℕ} {Uss : List (List UT)} {T : List UT} (hU : WOK u Uss) (hT : TX u 0 true T) :
    WOK u (Uss ++ [T]) := by
  refine ⟨fun us hus => ?_, fun u' hu' => ?_⟩
  · rcases List.mem_append.mp hus with hus | hus
    · exact hU.1 us hus
    · simp only [List.mem_singleton] at hus; subst hus; exact TX_raw hT
  · have hL : GoodChtX ([] ++ []) 1 (fun _ => 0) u' (Uss.map farTs) := by simpa using hU.2 u' hu'
    have hG : HeB.Gd HeC.P0 [] 1 (fun _ => 0) u' (farTs T) :=
      UF_sub AdmF_P0 ((Gd_TX (A := []) (k := 1) (by simp) (le_refl 1) (by simp) (fun _ => 0)
        (TX_mono hu' hT)).1 rfl rfl)
    have := HeC.Gd_P0_good hG (HcM.EmbU_triv (A := []) (by simp) (by simp) (by decide) (fun _ => 0))
      le_rfl hL
    rw [List.map_append, List.map_singleton]
    simpa [HeB.imgT_zero] using this

end PmD
end TRIO
