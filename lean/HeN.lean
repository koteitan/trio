/-
HeN.lean: 最上段の上の葉（段 l+1 の空の節点、親の段 0）、段つきの木の並びの良さ、文脈 CLTL の語の並び
（HdU と HdS の後半の写し、道の集合）。

- upleafT_core: 接頭辞 Y のあとの深さ d の塊 (1, q, 0) :: (D ++ [(1, m, 0)])↑1（q < m）は、
  展開 (1, q, 0) :: (HeH.towR q D j)↑1 が全て GTC なら GTC（gtc_oper と oper_cons_tower1）。
- GdT_upleaf: 段 0 の延長で閉じた集合で、GdT P us → GdT P (us ++ [tie (l+1) []])。塔の各段は GdT_jump の繰り返し。
- GdT_treeL: TreeTs v p cl us → GdT P pre → GdT P (pre ++ us)。GoodTTL_all・GTC_wLTL・BwT_CLTL・starOK_CLTL。
-/
import HeM

namespace TRIO
namespace HeN

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ
open HeB HeG HeH HeI HeK HeL HeM

theorem topTs_towT (u : ℕ) (Y : List UT) (p : ℕ) :
    ∀ j, topTs u (HeH.towT p Y j) = HeH.towR (u + 1 + p) (topTs u Y) j
  | 0 => rfl
  | j + 1 => by
      simp only [HeH.towT, HeH.towR, topTs_append]
      simp [topTs, topT, topTs_towT u Y p j]

/-- ★ 最上段の深さ d の塊の最後の上の葉の展開は、親の塊の入れ子。 -/
theorem upleafT_core {C : ℕ → List TrioSeq → Prop} {u : ℕ} {Y D : TrioSeq} {d q m : ℕ} (hD : Fr D)
    (hqm : q < m)
    (hrep : ∀ j, GTC C u (Y ++ shiftr01 d 0
      (((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (HeH.towR q D j)))) :
    GTC C u (Y ++ shiftr01 d 0
      (((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ [((1, m, 0) : ℕ × ℕ × ℕ)]))) := by
  obtain ⟨R, hR⟩ : ∃ R : TrioSeq, R = D ++ [((1, m, 0) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  rw [← hR]
  have hRok : argOK R := by
    intro x hx
    rw [hR] at hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hD x hx; omega
    · simp at hx; subst hx; show 0 < 1; omega
  have hRne : R ≠ [] := by simp [hR]
  have hRlen : R.length - 1 = D.length + 0 := by simp [hR]
  have eL : ∀ i, entry R i (R.length - 1) = entry [((1, m, 0) : ℕ × ℕ × ℕ)] i 0 := by
    intro i; rw [hRlen, hR, entry_append_right]
  have e0 : entry R 0 (R.length - 1) = 1 := by rw [eL]; rfl
  have e1 : entry R 1 (R.length - 1) = m := by rw [eL]; rfl
  have e2' : entry R 2 (R.length - 1) = 0 := by rw [eL]; rfl
  have hsr : srow R (R.length - 1) = 1 := by unfold srow; rw [e2', e1]; simp; omega
  have hnpR : ¬ hasParent R 1 (R.length - 1) := by
    rintro ⟨k, hk, -⟩
    have hk' : nextrel1 R k (R.length - 1) := by
      unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
    obtain ⟨-, -, hkl, -, hle0, -⟩ := hk'
    have hrec := rtg0_rec hle0.2.2 (R.length - 1) hkl le_rfl
    rw [e0] at hrec
    have hkD : k < D.length := by omega
    rw [hR, Small.entry_append_left hkD] at hrec
    have := getD_row0_ge hD hkD
    omega
  have hd : domT R (2 * m - 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2']; omega
    · rw [hsr]; exact hnpR
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hpM : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
    rw [hsr]
    refine hasParent_one_of (b := R.length) (k := 0) (by simp) hRl
      ⟨by simp, by simp, rtg0_zero (fun l hl0 hl => ?_) (by simp)⟩ ?_
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [entry_cons]
      have hl' : l' < R.length := by simp at hl; omega
      have hmem : R.getD l' (0, 0, 0) ∈ R := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl']; exact List.getElem_mem hl'
      have := hRok _ hmem
      show 0 < (R.getD l' (0, 0, 0)).1
      omega
    · rw [entry_cons_last hRne 1, e1]; show q < m; omega
  have hdl : R.dropLast = D := by rw [hR, List.dropLast_concat]
  have htow : ∀ j, shiftr01 1 0 (tow q 0 R (j + 1))
      = ((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ shiftr01 1 0 (tow q 0 R j)) := by
    intro j
    rw [tow, graft_eq_shift, e0, hdl]
    simp [shiftr01]
  have htR : ∀ j, D ++ shiftr01 1 0 (tow q 0 R j) = HeH.towR q D j := by
    intro j
    induction j with
    | zero => simp [tow, HeH.towR, shiftr01]
    | succ j ih => rw [htow, ih]; rfl
  have eV : ((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 R
      = shiftr01 1 0 (((0, q, 0) : ℕ × ℕ × ℕ) :: R) := by simp [shiftr01]
  have hlen2 : 2 ≤ (((0, q, 0) : ℕ × ℕ × ℕ) :: R).length := by simp; omega
  have hpM' : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, q, 0) : ℕ × ℕ × ℕ) :: R) ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1) := by
    have hl : ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]; exact hpM
  rw [eV]
  refine HdR.gtc_oper (by rw [shiftr01_length]; exact hlen2)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpM') (fun m' hm' => ?_)
  have eO := oper_shift [] (((0, q, 0) : ℕ × ℕ × ℕ) :: R) 1 m' hlen2 hpM'
  simp only [List.nil_append] at eO
  rw [eO, oper_cons_tower1 hRok hRne hd hsr hpM]
  obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
  rw [htow, htR]
  exact hrep j

theorem GdT_towT {P : TPS} (hcl : TExt P 0 true 0 P) {v : ℕ} {us : List UT} (h : GdT P 0 true v us) :
    ∀ j, GdT P 0 true v (HeH.towT 0 us j)
  | 0 => h
  | j + 1 => GdT_jump hcl (TieOK_zero 0 true) (GdT_towT hcl h j) h

/-- ★ 最上段の上の葉: 段 0 の延長で閉じた集合で、段 l+1 の空の節点を足せる。 -/
theorem GdT_upleaf {P : TPS} (hP : TPSOK P 0 true) (hcl : TExt P 0 true 0 P) (hlast : TLast P 0) {l : ℕ}
    {v : ℕ} {us : List UT} (h : GdT P 0 true v us) : GdT P 0 true v (us ++ [UT.tie (l + 1) []]) := by
  refine ⟨TreeTs_append.mpr ⟨h.1, ⟨rfl, by omega, trivial⟩, trivial⟩, fun u hu Uss hU hG Q hQ => ?_⟩
  have hT := GdT_towT hcl h
  have hrep : ∀ j, BotCL u Uss Q (HeH.towT 0 us j) := fun j => (hT j).2 u hu Uss hU hG Q hQ
  have hDF : Fr (topTs u us) := Fr_topTs u us
  have eT : topTs u (us ++ [UT.tie (l + 1) []])
      = topTs u us ++ [((1, u + 1 + (l + 1), 0) : ℕ × ℕ × ℕ)] := by
    simp [topTs_append, topTs, topT, shiftr01]
  rcases List.eq_nil_or_concat Q with rfl | ⟨Q', ⟨v', p'⟩, rfl⟩
  · have eW : ∀ T : List UT, BotCL u Uss [] T
        = GTC CLTL u (FTL0 (u + 1) (Uss.map (topTs u)) ++ shiftr01 0 0
            (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u T))) := by
      intro T
      show GTC CLTL u (wLT u (Uss ++ [T], [])) = _
      rw [shiftr01_zero', Nat.add_zero]
      simp only [wLT, List.map_append, List.map_singleton, FTL0_snoc]
      rw [show unitsC u ([] : List (Option TrioSeq)) = [] from rfl, List.append_nil]
    rw [eW, eT]
    refine upleafT_core hDF (by omega) (fun j => ?_)
    have := hrep j
    rwa [eW, topTs_towT] at this
  · simp only [List.concat_eq_append] at hQ hrep ⊢
    have hp' : p' = 0 := by have := hlast u _ hQ; rwa [HeC.lastL_snoc] at this
    subst hp'
    have eW : ∀ T : List UT, BotCL u Uss (Q' ++ [(v', 0)]) T
        = GTC CLTL u ((wLT u (Uss ++ [plugQ Q' []], []) ++ shiftr01 (Q'.length + 1) 0 (topTs u v')) ++
            shiftr01 (Q'.length + 1) 0
              (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u T))) := by
      intro T
      rw [BotCL_snoc_eq, BotCL_word, topTs_snoc_tieL, shiftr01_append0, List.append_assoc]
    rw [eW, eT]
    refine upleafT_core hDF (by omega) (fun j => ?_)
    have := hrep j
    rwa [eW, topTs_towT] at this

/-- ★ 段 l+1 の節点の子の位置の空の並び（親の集合で上の葉）。 -/
theorem GdT_nil_tchU {P : TPS} (hP : TPSOK P 0 true) (hcl : TExt P 0 true 0 P) (hlast : TLast P 0)
    {l v : ℕ} : GdT (tchU P 0 (l + 1)) (l + 1) false v [] := by
  refine ⟨trivial, fun u _ Uss hU hG Q hQ => ?_⟩
  obtain ⟨Q', us, rfl, hQ', hus⟩ := hQ
  rw [BotCL_snoc_eq]
  exact (GdT_upleaf hP hcl hlast hus).2 u le_rfl Uss hU hG Q' hQ'

/-! ## 木 -/

mutual
theorem GdT_treeU : ∀ (x : UT) (P : TPS) (p : ℕ) (cl : Bool), TPSOK P p cl → TPSDec P p cl → TLast P p →
    (cl = true → p = 0 ∧ TExt P 0 true 0 P) → ∀ (v : ℕ) (pre : List UT), TreeTU v p cl x →
    GdT P p cl v pre → GdT P p cl v (pre ++ [x])
  | .ch Z, P, _, _, hP, hD, _, _, _, pre, hx, hpre => GdT_load hP hD Z hx.1 hx.2 pre hpre
  | .tie 0 cs, P, p, cl, hP, hD, _, _, v, pre, hx, hpre => by
      have hcs := GdT_treeL cs (tchS0 P p cl) 0 true (TPSOK_tchS0 hP) (TPSDec_tchS0 P p cl)
        (TLast_tchS0 P p cl) (fun _ => ⟨rfl, tchS0_closed P p cl⟩) v [] hx (GdT_nil_tchS0 hP hD)
      rw [List.nil_append] at hcs
      exact GdT_jump (TExt_tchS0 P p cl) (TieOK_zero p cl) hcs hpre
  | .tie (l + 1) cs, P, p, cl, hP, hD, hlast, hcl, v, pre, hx, hpre => by
      obtain ⟨hcl1, hpl, hx⟩ := hx
      subst hcl1
      obtain ⟨rfl, hclo⟩ := hcl rfl
      have hcs := GdT_treeL cs (tchU P 0 (l + 1)) (l + 1) false (TPSOK_tchU hP hpl) (TPSDec_tchU P hpl)
        (TLast_tchU P 0 (l + 1)) (fun h => absurd h (by simp)) v [] hx (GdT_nil_tchU hP hclo hlast)
      rw [List.nil_append] at hcs
      exact GdT_jump (TExt_tchU P 0 (l + 1)) (TieOK_up hpl) hcs hpre
theorem GdT_treeL : ∀ (us : List UT) (P : TPS) (p : ℕ) (cl : Bool), TPSOK P p cl → TPSDec P p cl →
    TLast P p → (cl = true → p = 0 ∧ TExt P 0 true 0 P) → ∀ (v : ℕ) (pre : List UT), TreeTs v p cl us →
    GdT P p cl v pre → GdT P p cl v (pre ++ us)
  | [], _, _, _, _, _, _, _, _, pre, _, hpre => by rw [List.append_nil]; exact hpre
  | x :: us, P, p, cl, hP, hD, hlast, hcl, v, pre, hx, hpre => by
      have := GdT_treeL us P p cl hP hD hlast hcl v (pre ++ [x]) hx.2
        (GdT_treeU x P p cl hP hD hlast hcl v pre hx.1 hpre)
      rwa [List.append_assoc, List.singleton_append] at this
end

/-- ★ 段つきの木の並びは F のタイの子の位置 TP0 で良い。 -/
theorem GdT_treeTP0 {v : ℕ} {us : List UT} (h : TreeTs v 0 true us) : GdT TP0 0 true v us := by
  have := GdT_treeL us TP0 0 true TPSOK_TP0 TPSDec_TP0 TLast_TP0 (fun _ => ⟨rfl, TP0_closed⟩) v [] h
    GdT_nil_TP0
  rwa [List.nil_append] at this

theorem GoodTTL_nil (v : ℕ) : GoodTTL v [] := by
  intro u _
  have e : wLT u ([], []) = GzJ.fwTop u [] := by simp [wLT, FTL0, GzJ.fwTop, unitsC]
  rw [e]; exact GTC_far_CLTL u

/-- ★ 段つきの木の F のタイの子の並びの語は良い。 -/
theorem GoodTTL_all {v : ℕ} : ∀ Uss : List (List UT), (∀ us ∈ Uss, TreeTs v 0 true us) → GoodTTL v Uss := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _; exact GoodTTL_nil v
  | append_singleton Uss us ih =>
      intro h
      have h' : ∀ us' ∈ Uss, TreeTs v 0 true us' := fun us' hus' => h us' (List.mem_append_left _ hus')
      have hus := h us (List.mem_append_right _ (List.mem_singleton_self _))
      have := GdT_good TPSOK_TP0 (GdT_treeTP0 hus) le_rfl h' (ih h') (TPNil_TP0 v)
      simpa [plugQ] using this

theorem GTC_wLTL {v : ℕ} {Uss : List (List UT)} (hU : ∀ us ∈ Uss, TreeTs v 0 true us) (hG : GoodTTL v Uss) :
    ∀ us : List (Option TrioSeq), GzJ.NoTie us → RawU v us → GTC CLTL v (wLT v (Uss, us)) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact hG v le_rfl
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : GzJ.NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          exact GTC_load_CLTL hU hNT' (RawU_prefix hR) (ih hNT' (RawU_prefix hR)) Z hZ.1 hZ.2

theorem BwT_CLTL (v : ℕ) : ∀ ps : List (List (List UT) × List (Option TrioSeq)),
    PsLTL v ps → BwT v (ps.map (wLT v)) := by
  intro ps
  induction ps using List.reverseRecOn with
  | nil => intro _; exact BwT_nil v
  | append_singleton ps p ih =>
      intro h
      have h' : PsLTL v ps := fun q hq => h q (List.mem_append_left _ hq)
      have hp := h p (List.mem_append_right _ (List.mem_singleton_self _))
      have hG := GTC_wLTL hp.1 (GoodTTL_all p.1 hp.1) p.2 hp.2.1 hp.2.2
      have := hG _ ⟨ps, h', rfl⟩ (Fr_CLT v ps) (ih h')
      rw [List.map_append, List.map_singleton]
      exact this

/-- ★ F のタイの子に段つきの木を持つ語の並びと、そのあとに TF の語の並び。 -/
theorem starOK_CLTL {v : ℕ} (ps : List (List (List UT) × List (Option TrioSeq)))
    (h : PsLTL v ps) {Ls : List TrioSeq} (hW : WordsG v Ls) :
    StarOK v (rword 0 v (ps.map (wLT v) ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_append_words (Fr_CLT v ps) (BwT_CLTL v ps h) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end HeN
end TRIO
