/-
GzI.lean: 遠い字と単位の語の、単位の段（タイ、荷）と、節点の下の並びの全体。

    GTU b0 us := ∀ uss, FarCU b0 uss → FarCU b0 (uss ++ [us])
    GTU_nil  : 潰れ（GzH.farU_collapse）
    GTU_tie  : 行 1 が b+1 のタイは、語の並びの族の tie 公理で荷に置き換わる
    GTU_load : 荷 Z の Wg の帰納（slot_load と同じ場合分けを語の中の深さ 2 で）。
               flat（Z の最後が (0,0,0)）は語の複写 W ++ U^m になり、GTU の繰り返しで出る
    FarCU_all : 全ての単位の列の並び
-/
import GzH

namespace TRIO
namespace GzI

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH

def GTU (b0 : ℕ) (us : List (Option TrioSeq)) : Prop :=
  ∀ uss, FarCU b0 uss → FarCU b0 (uss ++ [us])

theorem FarCU_mono {b0 b1 : ℕ} (h : b0 ≤ b1) {uss : List (List (Option TrioSeq))}
    (hC : FarCU b0 uss) : FarCU b1 uss :=
  fun A o f b hb hR hA hA1 ho => hC A o f b (by omega) hR hA hA1 ho

theorem GTU_nil (b0 : ℕ) : GTU b0 [] := fun _ hC => farU_collapse hC

theorem GTU_rep {b0 : ℕ} {us : List (Option TrioSeq)} (h : GTU b0 us)
    {uss : List (List (Option TrioSeq))} (hC : FarCU b0 uss) :
    ∀ m, FarCU b0 (uss ++ List.replicate m us)
  | 0 => by simpa using hC
  | m + 1 => by
      have := h _ (GTU_rep h hC m)
      rwa [List.append_assoc, ← List.replicate_succ'] at this

theorem farU_rep (b r : ℕ) (uss : List (List (Option TrioSeq))) (us : List (Option TrioSeq)) :
    ∀ m, farU b r (uss ++ List.replicate m us)
      = farU b r uss ++ (List.range m).flatMap (fun _ => fwU b r us)
  | 0 => by simp [farU]
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, farU_snoc, farU_rep b r uss us m,
        List.range_succ, List.flatMap_append, List.append_assoc]
      simp

theorem fwU_none (b r : ℕ) (us : List (Option TrioSeq)) :
    fwU b r (us ++ [none]) = fwU b r us ++ [((2, b + 1, 0) : ℕ × ℕ × ℕ)] := by
  simp [fwU, unitsC_snoc, unitC, shiftr01]

theorem fwU_some (b r : ℕ) (us : List (Option TrioSeq)) (Z : TrioSeq) :
    fwU b r (us ++ [some Z]) = fwU b r us ++ shiftr01 2 0 Z := by
  simp [fwU, unitsC_snoc, unitC, shiftr01, Function.comp_def, Nat.add_assoc]

theorem Fr_shift2 (Z : TrioSeq) : Fr (shiftr01 2 0 Z) := by
  intro y hy
  simp only [shiftr01, List.mem_map] at hy
  obtain ⟨p, -, rfl⟩ := hy
  dsimp only; omega

theorem GTU_some_nil {b0 : ℕ} {us : List (Option TrioSeq)} (h : GTU b0 us) :
    GTU b0 (us ++ [some []]) := by
  intro uss hC A o f b hb hR hA hA1 ho
  have hRu : RawUs b (uss ++ [us]) := fun us' h' => by
    rcases List.mem_append.mp h' with h' | h'
    · exact hR us' (List.mem_append_left _ h')
    · simp at h'; subst h'
      exact RawU_prefix (hR _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have := h uss hC A o f b hb hRu hA hA1 ho
  rw [farU_snoc] at this ⊢
  rw [fwU_some]
  simpa [shiftr01] using this

/-! ## タイ -/

theorem GTU_tie {us : List (Option TrioSeq)} (h : ∀ b0 Z, GTU b0 (us ++ [some Z])) (b0 : ℕ) :
    GTU b0 (us ++ [none]) := by
  intro uss hC A o f b hb hR hA hA1 ho
  rw [farU_snoc, fwU_none]
  have hR0 : RawUs b uss := fun us' h' => hR us' (List.mem_append_left _ h')
  have hRus : RawU b us :=
    RawU_prefix (hR _ (List.mem_append_right _ (List.mem_singleton_self _)))
  refine (GpT_ax hA hA1 ho f).tie b (farU b (b + liftOff f A o + 1) uss)
    (fwU b (b + liftOff f A o + 1) us) 2 (Fr_farU _ _ _)
    (Fr_append (Fr_fwU _ _ _) (Fr_single (by omega) _ _))
    (fun _ => rfl) ?_ (fun u' hu Z hZ hbZ => ?_)
  · have hbot : BotGe ([] ++ ((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ) :: unitsC b us)) (1 + 1) (b + 1) :=
      BotGe_node Fr_nil (by omega) (BotGe_top (Fr_FLunits _ _ us) (b + 1))
    simp only [List.nil_append] at hbot
    exact coneV_of_BotGe hbot (by omega)
  · rw [mlift_app (Fr_farU _ _ _) (Hd_fwU _ _ _),
      mlift_farU_base (show b < b + liftOff f A o + 1 by omega) _ uss hR0,
      mlift_fwU_base (show b < b + liftOff f A o + 1 by omega) hRus, List.append_assoc, ← fwU_some,
      show b + (u' - b) = u' by omega,
      show b + liftOff f A o + 1 + (u' - b) = u' + liftOff f A o + 1 by omega, ← farU_snoc]
    refine h b0 Z uss hC A o f u' (by omega) ?_ hA hA1 ho
    intro us' hus'
    rcases List.mem_append.mp hus' with hus' | hus'
    · exact RawU_mono hu (hR0 us' hus')
    · simp at hus'; subst hus'
      intro Z' hZ'
      rcases List.mem_append.mp hZ' with hZ' | hZ'
      · exact RawU_mono hu hRus Z' hZ'
      · simp at hZ'; subst hZ'; exact ⟨hZ, hbZ⟩

/-! ## 荷 -/

theorem GTU_load {us : List (Option TrioSeq)} (hus : ∀ b0, GTU b0 us) (b1 : ℕ) :
    ∀ Z ∈ Wg (2 * b1), based Z → GTU b1 (us ++ [some Z]) := by
  have key : Wg (2 * b1) ⊆ {Z : TrioSeq | Z ∈ Wg (2 * b1) ∧
      (based Z → GTU b1 (us ++ [some Z]))} := by
    refine A2g' ?_
    intro Z hAZ
    have hZW : Z ∈ Wg (2 * b1) := A1g_intro (Aopg_mono_X hAZ (fun U hU => hU.1))
    refine ⟨hZW, fun hb => ?_⟩
    intro uss hC A o f b hbb hR hA hA1 ho
    have hk : o ≤ liftOff f A o := by unfold liftOff; omega
    obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f A o + 1 := ⟨_, rfl⟩
    rw [← hr]
    have hR0 : RawUs b uss := fun us' h' => hR us' (List.mem_append_left _ h')
    have hRus : RawU b us :=
      RawU_prefix (hR _ (List.mem_append_right _ (List.mem_singleton_self _)))
    have hRext : ∀ Z', Z' ∈ Wg (2 * b1) → based Z' → ∀ m,
        RawUs b (uss ++ List.replicate m (us ++ [some Z'])) := by
      intro Z' hZ' hbZ' m us' hus'
      rcases List.mem_append.mp hus' with hus' | hus'
      · exact hR0 us' hus'
      · rw [List.eq_of_mem_replicate hus']
        intro Z'' hZ''
        rcases List.mem_append.mp hZ'' with hZ'' | hZ''
        · exact hRus Z'' hZ''
        · simp at hZ''; subst hZ''; exact ⟨Wg_mono (by omega) hZ', hbZ'⟩
    have hGU : ∀ Z', Z' ∈ Wg (2 * b1) → based Z' → GTU b1 (us ++ [some Z']) →
        GpT A o f b (farU b r uss ++ (fwU b r us ++ shiftr01 2 0 Z')) := by
      intro Z' hZ' hbZ' hG
      have := hG uss hC A o f b hbb (by simpa using hRext Z' hZ' hbZ' 1) hA hA1 ho
      rwa [← hr, farU_snoc, fwU_some] at this
    have hflat : ∀ Z1, Z1 ∈ Wg (2 * b1) → based Z1 → GTU b1 (us ++ [some Z1]) →
        GpT A o f b (farU b r uss ++ (fwU b r (us ++ [some Z1]) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)])) := by
      intro Z1 hZ1 hbZ1 hG
      obtain ⟨M, hM⟩ : ∃ M, M = fwU b r (us ++ [some Z1]) := ⟨_, rfl⟩
      rw [← hM]
      have hMne : M ≠ [] := by rw [hM]; simp [fwU]
      have hMpos : 0 < M.length := List.length_pos_iff.mpr hMne
      have hhead : entry M 0 0 < 2 := by rw [hM]; show 1 < 2; omega
      have htail : ∀ r', 1 ≤ r' → r' < M.length → 2 ≤ entry M 0 r' := by
        intro r' hr1 hr2
        obtain ⟨w, rfl⟩ : ∃ w, r' = w + 1 := ⟨r' - 1, by omega⟩
        have hw : w < (((1, r, 1) : ℕ × ℕ × ℕ) :: unitsC b (us ++ [some Z1])).length := by
          rw [hM] at hr2; simp only [fwU, List.length_cons, shiftr01_length] at hr2 ⊢; omega
        rw [hM, fwU, entry_cons, entry0_shiftr01 hw]
        have := getD_row0_ge (Fr_FLunits b r (us ++ [some Z1])) hw
        omega
      have hlast : hasParent (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)])
          (srow (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1))
          ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
        have hidx : (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1 = M.length + 0 := by simp
        rw [hidx, srow_append_right]
        have hs : srow [((2, 0, 0) : ℕ × ℕ × ℕ)] 0 = 0 := rfl
        rw [hs]
        refine (hasParent_zero_iff (by simp)).mpr ⟨0, by omega, ?_⟩
        rw [Small.entry_append_left hMpos, entry_append_right]
        exact hhead
      refine (GpT_ax hA hA1 ho f).oper b _ (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) (Fr_farU _ _ _)
        (Fr_append (by rw [hM]; exact Fr_fwU _ _ _) (Fr_single (by omega) _ _))
        (fun _ => by rw [Small.entry_append_left hMpos, hM]; rfl)
        (by simp; omega) hlast (fun m hm => ?_)
      have eO := oper_snoc00'' [] hMne hhead htail m
      simp only [List.nil_append] at eO
      rw [eO, hM, ← farU_rep]
      have := GTU_rep hG hC m A o f b hbb (hRext Z1 hZ1 hbZ1 m) hA hA1 ho
      rwa [← hr] at this
    rw [farU_snoc, fwU_some]
    have hb0 : entry Z 0 0 = 0 := hb
    by_cases hZnil : Z = []
    · subst hZnil
      have hRu : RawUs b (uss ++ [us]) := by
        intro us' h'
        rcases List.mem_append.mp h' with h' | h'
        · exact hR0 us' h'
        · simp at h'; subst h'; exact hRus
      have := hus b1 uss hC A o f b hbb hRu hA hA1 ho
      rw [← hr, farU_snoc] at this
      simpa [shiftr01] using this
    have hZlen : 0 < Z.length := List.length_pos_iff.mpr hZnil
    set c := Z.getLast hZnil with hc
    have hsplit : Z = Z.dropLast ++ [c] := (List.dropLast_append_getLast hZnil).symm
    have hclast : ∀ r', entry Z r' (Z.length - 1) = entry [c] r' 0 := by
      intro r'
      have h := entry_append_right Z.dropLast [c] r' 0
      rw [← hsplit] at h
      rw [show Z.length - 1 = Z.dropLast.length + 0 by simp]
      exact h
    have hlev0 : lev Z (Z.length - 1) = 0 → c.2.1 = 0 ∧ c.2.2 = 0 := by
      intro hz
      unfold lev at hz
      rw [hclast 1, hclast 2] at hz
      have e1 : entry [c] 1 0 = c.2.1 := rfl
      have e2 : entry [c] 2 0 = c.2.2 := rfl
      rw [e1, e2] at hz
      omega
    have hc10 : Z.length = 1 → c.1 = 0 := by
      intro hZ1
      have : entry Z 0 (Z.length - 1) = c.1 := hclast 0
      rw [show Z.length - 1 = 0 by omega, hb0] at this; omega
    have hZflat : c.2.1 = 0 → c.2.2 = 0 → c.1 = 0 →
        farU b r uss ++ (fwU b r us ++ shiftr01 2 0 Z)
          = farU b r uss ++ (fwU b r (us ++ [some Z.dropLast]) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) := by
      intro h1 h2 h0
      have hceq : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext h0 (Prod.ext h1 h2)
      conv_lhs => rw [hsplit, hceq]
      rw [fwU_some]
      simp [shiftr01, List.append_assoc]
    have hHd2 : Hd (fwU b r us ++ shiftr01 2 0 Z) := fun _ => by
      rw [Small.entry_append_left (by simp [fwU])]; rfl
    rcases hAZ with ⟨hl, hw0⟩ | ⟨hnat, hop⟩ | ⟨m', hm, hd, h20, hgr⟩
    · have hZ1 : Z.length = 1 := by omega
      have hz : lev Z (Z.length - 1) = 0 := by rw [hZ1]; exact hw0
      have hdl : Z.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      rw [hZflat (hlev0 hz).1 (hlev0 hz).2 (hc10 hZ1), hdl]
      exact hflat [] (Wg_nil _) based_nil (GTU_some_nil (hus b1))
    · by_cases hp : 2 ≤ Z.length ∧ hasParent Z (srow Z (Z.length - 1)) (Z.length - 1)
      · obtain ⟨hlen2, hp⟩ := hp
        refine (GpT_ax hA hA1 ho f).oper b _ (fwU b r us ++ shiftr01 2 0 Z) (Fr_farU _ _ _)
          (Fr_append (Fr_fwU _ _ _) (Fr_shift2 Z)) hHd2
          (by simp only [List.length_append, shiftr01_length]; omega) ?_ (fun m hm => ?_)
        · have hidx : (fwU b r us ++ shiftr01 2 0 Z).length - 1
              = (fwU b r us).length + (Z.length - 1) := by
            simp only [List.length_append, shiftr01_length]; omega
          rw [hidx, srow_append_right, srow_shiftr01]
          exact hasParent_append_right_of _ _ (hasParent_shiftr01.mpr hp)
        · rw [oper_shift (fwU b r us) Z 2 m hlen2 hp]
          exact hGU _ (hop m hm).1 (based_oper hm hb) ((hop m hm).2 (based_oper hm hb))
      · have hlev : lev Z (Z.length - 1) = 0 := by
          rcases natDom_iff.mp hnat with h | h
          · exact h
          · exfalso
            have hZ1 : Z.length = 1 := by
              by_contra hne; exact hp ⟨by omega, h⟩
            rw [hZ1] at h
            obtain ⟨j0, hj0, -⟩ := h
            exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
        obtain ⟨h1, h2⟩ := hlev0 hlev
        have hsr0 : srow Z (Z.length - 1) = 0 := by
          unfold srow; rw [hclast 1, hclast 2]
          show (if 0 < c.2.2 then 2 else if 0 < c.2.1 then 1 else 0) = 0
          simp [h1, h2]
        by_cases hZ1 : Z.length = 1
        · have hdl : Z.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
          rw [hZflat h1 h2 (hc10 hZ1), hdl]
          exact hflat [] (Wg_nil _) based_nil (GTU_some_nil (hus b1))
        · have h0 : c.1 = 0 := by
            by_contra hne
            have hc10' : entry Z 0 (Z.length - 1) = c.1 := hclast 0
            exact hp ⟨by omega, by
              rw [hsr0]
              exact (hasParent_zero_iff (by omega)).mpr ⟨0, by omega, by rw [hb0, hc10']; omega⟩⟩
          have h1' := hop 1 le_rfl
          rw [oper_one_eq_dropLast (by omega)] at h1'
          rw [hZflat h1 h2 h0]
          exact hflat Z.dropLast h1'.1 (based_dropLast hb) (h1'.2 (based_dropLast hb))
    · have hlev := hd.1
      unfold lev at hlev
      have h20' : entry Z 2 (Z.length - 1) = 0 := h20
      have hj1 : 1 ≤ entry Z 1 (Z.length - 1) := by omega
      have hjv : entry Z 1 (Z.length - 1) ≤ b1 := by omega
      have hm' : m' = 2 * entry Z 1 (Z.length - 1) - 1 := by omega
      subst hm'
      have hsr : srow Z (Z.length - 1) = 1 := by
        unfold srow; rw [if_neg (by omega), if_pos (by omega)]
      have hnp : ¬ hasParent Z 1 (Z.length - 1) := fun hh => hd.2 (by rw [hsr]; exact hh)
      have hc1' : c.2.1 = entry Z 1 (Z.length - 1) := (hclast 1).symm
      have hc20 : c.2.2 = 0 := by have := hclast 2; rw [h20'] at this; exact this.symm
      generalize hjdef : entry Z 1 (Z.length - 1) = j at hj1 hjv hc1' hgr hnp
      have hcj : c = ((c.1, j, 0) : ℕ × ℕ × ℕ) := Prod.ext rfl (Prod.ext hc1' hc20)
      have eZ : fwU b r us ++ shiftr01 2 0 Z
          = (fwU b r us ++ shiftr01 2 0 Z.dropLast) ++ [((c.1 + 2, j, 0) : ℕ × ℕ × ℕ)] := by
        conv_lhs => rw [hsplit, hcj]
        simp [shiftr01, List.append_assoc]
      have e22 : shiftr01 2 0 Z = shiftr01 1 0 (shiftr01 1 0 Z) := by rw [shift_shift]
      have hHdS : Hd (shiftr01 1 0 Z) := fun _ => by rw [entry0_shiftr01 hZlen, hb0]
      have hnpZ : ¬ hasParent (fwU b r us ++ shiftr01 2 0 Z) 1
          ((fwU b r us).length + (Z.length - 1)) := by
        refine noParent_ctx (j := j) (by rw [shiftr01_length]; omega) (fun k' hk' hrt => ?_)
          (by rw [entry1_shiftr01]; exact hjdef) (by rw [hasParent_shiftr01]; exact hnp)
        rw [e22] at hrt
        have hk0 := letter_anc_row1 (Fr_FLunits b r us) hHdS
          (by unfold shiftr01; rw [Ne, List.map_eq_nil_iff]; exact hZnil) hk'
          (by rw [shiftr01_length, shiftr01_length]; omega) hrt
        subst hk0
        show j ≤ r
        omega
      rw [eZ]
      refine (GpT_ax hA hA1 ho f).orph b _ (fwU b r us ++ shiftr01 2 0 Z.dropLast) (c.1 + 2) j
        (Fr_farU _ _ _) (by rw [← eZ]; exact Fr_append (Fr_fwU _ _ _) (Fr_shift2 Z))
        (by rw [← eZ]; exact hHd2) hj1 (by omega) ?_ (fun z hz hbz => ?_)
      · rw [← eZ]
        have hidx : (fwU b r us ++ shiftr01 2 0 Z.dropLast).length
            = (fwU b r us).length + (Z.length - 1) := by
          rw [List.length_append, shiftr01_length, List.length_dropLast]
        rw [hidx]; exact hnpZ
      · have hg := hgr z hz hbz
        have hbg := based_graft_arg hZnil hb hbz
        have hgz := hGU (graft Z z) hg.1 hbg (hg.2 hbg)
        have e : graft Z z = Z.dropLast ++ shiftr01 c.1 0 z := by
          rw [graft_eq_shift, hclast 0]; rfl
        rw [e] at hgz
        have e2 : fwU b r us ++ shiftr01 2 0 (Z.dropLast ++ shiftr01 c.1 0 z)
            = (fwU b r us ++ shiftr01 2 0 Z.dropLast) ++ shiftr01 (c.1 + 2) 0 z := by
          simp [shiftr01, List.append_assoc, Function.comp_def, Nat.add_assoc]
        rwa [e2] at hgz
  intro Z hZ hb
  exact (key hZ).2 hb

theorem GTU_some {us : List (Option TrioSeq)} (hus : ∀ b0, GTU b0 us) (Z : TrioSeq) (b0 : ℕ) :
    GTU b0 (us ++ [some Z]) := by
  intro uss hC A o f b hb hR hA hA1 ho
  have hZ := hR _ (List.mem_append_right _ (List.mem_singleton_self _)) Z (by simp)
  exact GTU_load hus b Z hZ.1 hZ.2 uss (FarCU_mono hb hC) A o f b le_rfl hR hA hA1 ho

/-- ★ 単位の列 us の遠い字の語は、どの段でも標準の並びの後ろに足せる。 -/
theorem GTU_units : ∀ (us : List (Option TrioSeq)) (b0 : ℕ), GTU b0 us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => exact GTU_nil
  | append_singleton us o ih =>
      cases o with
      | none => exact GTU_tie (fun b0 Z => GTU_some ih Z b0)
      | some Z => exact GTU_some ih Z

/-- ★ 遠い字と単位の語の並びは、全ての錨の列と状態で節点の子の並び。 -/
theorem FarCU_all (b0 : ℕ) : ∀ uss, FarCU b0 uss := by
  intro uss
  induction uss using List.reverseRecOn with
  | nil => exact FarCU_nil b0
  | append_singleton uss us ih => exact GTU_units us b0 uss ih

theorem PVF_farU {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (b : ℕ) (uss : List (List (Option TrioSeq))) (hR : RawUs b uss) :
    PVF A o b (farU b (b + o + 1) uss) := by
  have := farU_PVP (FarCU_all b uss) hA hA1 ho (fun _ => 0) b le_rfl hR
  rw [liftOff_zeroF] at this
  exact ⟨this, Fr_farU _ _ uss⟩

end GzI
end TRIO
