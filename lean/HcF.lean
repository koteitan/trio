/-
HcF.lean: 最後の F のタイの子の差し込み口の族 ChOK と、その差し込み口の公理。

    ChOK v D := Hd D ∧ LowC (v+1) D ∧ ∀ u, v ≤ u → ∀ Lds, GoodLc u Lds → GoodLc u (Lds ++ [mlift D v (u − v)])

- 子の段（GpT の段）: cstep_oper / cstep_orph / cstep_tie（F のタイの節点と字の下の深さ 2 の差し込み口）、flat は HbU.child_flat_step。
- lift の場は定義の ∀ u から、flat の場は F のタイの複製を GoodLc の並びの帰納で出す。
-/
import HbU
import HcE

namespace TRIO
namespace HcF

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcB HcC HcD HcE

/-! ## 子の段 -/

theorem cstep_oper {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (f : ℕ → ℕ) {b r : ℕ} {H P W U : TrioSeq} (hP : Fr P)
    (hlen : 2 ≤ U.length) (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → GpT A o f b (P ++ fwH b r H b
      (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (W ++ U⟦m⟧)))) :
    GpT A o f b (P ++ fwH b r H b (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (W ++ U))) := by
  have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  show GpT A o f b (P ++ fwH b r H b ([] ++ ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (W ++ U)))
  refine fwH_oper_step hA hA1 ho f hP Fr_nil (Fr_node _ _) (Hd_node _ _)
    (by simp only [List.length_cons, shiftr01_length, List.length_append]; omega)
    (node_hasParent _ W U hp hUne) (fun m hm => ?_)
  rw [List.nil_append, node_oper _ W U hlen hp m]
  exact hIH m hm

theorem cstep_orph {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (f : ℕ → ℕ) {b r : ℕ} (hbr : b < r) {H P W U : TrioSeq} {h j : ℕ} (hH : Fr H) (hP : Fr P)
    (hW : Fr W) (hHU : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
    (hj1 : 1 ≤ j) (hj : j ≤ b) (hnp : ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z → GpT A o f b (P ++ fwH b r H b
      (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (W ++ (U ++ shiftr01 h 0 z))))) :
    GpT A o f b (P ++ fwH b r H b (((1, r, 0) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])))) := by
  obtain ⟨V, hV⟩ : ∃ V : TrioSeq, V = ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (W ++ U) := ⟨_, rfl⟩
  have eN : ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
      = V ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by
    rw [hV]; simp [shiftr01]
  have eZ : ∀ z : TrioSeq, ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (W ++ (U ++ shiftr01 h 0 z))
      = V ++ shiftr01 (h + 1) 0 z := by
    intro z; rw [hV]; simp [shiftr01, Function.comp_def, Nat.add_assoc]
  have eAB : V ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]
      = (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 W) ++ shiftr01 1 0 (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
    rw [hV]; simp [shiftr01]
  have hlenV : V.length = (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 W).length + U.length := by
    rw [hV]; simp only [List.length_cons, List.length_append, shiftr01_length]; omega
  rw [eN]
  show GpT A o f b (P ++ fwH b r H b ([] ++ (V ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)])))
  refine fwH_orph_step hA hA1 ho f (u := b) le_rfl hbr hH hP Fr_nil
    (by rw [← eN]; exact Fr_node _ _) (by rw [← eN]; exact Hd_node _ _) hj1 hj ?_
    (fun z hz' hbz => ?_)
  · have hZl : U.length < (shiftr01 1 0 (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])).length := by
      simp [shiftr01]
    rw [eAB, hlenV]
    refine noParent_ctx (j := j) hZl (fun k hk hrt => ?_) ?_ ?_
    · have := node_anc_row1 hW hHU (by simp) hk hZl hrt
      subst this
      show j ≤ r
      omega
    · rw [entry1_shiftr01, show U.length = U.length + 0 from rfl, entry_append_right]
      rfl
    · rw [hasParent_shiftr01]
      exact hnp
  · rw [List.nil_append, ← eZ z]
    exact hz z hz' hbz

theorem cstep_tie {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (f : ℕ → ℕ) {b r : ℕ} (hbr : b < r) {H P W U : TrioSeq} {x : ℕ} (hH : Fr H) (hP : Fr P)
    (hW : Fr W) (hHlow : ∀ y, y < H.length → entry H 0 y ≤ 1 → b < entry H 1 y)
    (Pb Hb : ℕ → TrioSeq) (hPl : ∀ b'', b ≤ b'' → mlift P b (b'' - b) = Pb b'')
    (hHl : ∀ b'', b ≤ b'' → mlift H b (b'' - b) = Hb b'')
    (hU : Fr (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) (hHU : Hd (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) b U.length)
    (hload : ∀ b'', b ≤ b'' → ∀ Z ∈ Wg (2 * b''), based Z →
      GpT A o f b'' (Pb b'' ++ fwH b'' (r + (b'' - b)) (Hb b'') b''
        (((1, r + (b'' - b), 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift (W ++ U) b (b'' - b) ++ shiftr01 x 0 Z)))) :
    GpT A o f b (P ++ fwH b r H b (((1, r, 0) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (W ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])))) := by
  have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
  have hFWU : Fr (W ++ U) := Fr_append hW hUc
  obtain ⟨Y, hY⟩ : ∃ Y : TrioSeq,
      Y = ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (H ++ ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 W) :=
    ⟨_, rfl⟩
  obtain ⟨U', hU'⟩ : ∃ U' : TrioSeq, U' = Y ++ shiftr01 2 0 U := ⟨_, rfl⟩
  have eQ : fwH b r H b (((1, r, 0) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (W ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])))
      = U' ++ [((x + 2, b + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [hU', hY]; unfold fwH; rw [Nat.sub_self, mlift_zero]
    simp [shiftr01, Function.comp_def, Nat.add_assoc]
  have eU'' : U' = ((1, r, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (H ++ ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (W ++ U)) := by
    rw [hU', hY]; simp [shiftr01, Function.comp_def, Nat.add_assoc]
  rw [eQ]
  have hFrU' : Fr (U' ++ [((x + 2, b + 1, 0) : ℕ × ℕ × ℕ)]) := by rw [← eQ]; exact Fr_fwH _ _ _ _ _
  have hHdU' : Hd (U' ++ [((x + 2, b + 1, 0) : ℕ × ℕ × ℕ)]) := by rw [← eQ]; exact Hd_fwH _ _ _ _ _
  refine (GpT_ax hA hA1 ho f).tie b P U' (x + 2) hP hFrU' hHdU' ?_ (fun b'' hb'' Z hZ hbZ => ?_)
  · have hPC : PathCone b 2 Y := by
      intro y hy _ hd
      rw [hY] at hy hd ⊢
      rcases y with _ | y
      · show b < r; omega
      · rw [entry_cons] at hd ⊢
        have hy' : y < (H ++ ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 W).length := by
          simp only [List.length_cons, shiftr01_length] at hy; omega
        rw [entry0_shiftr01 hy'] at hd
        rw [entry1_shiftr01]
        rcases Nat.lt_or_ge y H.length with hlt | hge
        · rw [Small.entry_append_left hlt] at hd ⊢
          exact hHlow y hlt (by omega)
        · obtain ⟨w, rfl⟩ : ∃ w, y = H.length + w := ⟨y - H.length, by omega⟩
          rw [entry_append_right] at hd ⊢
          rcases w with _ | w
          · show b < r; omega
          · exfalso
            rw [entry_cons] at hd
            have hw : w < W.length := by
              simp only [List.length_cons, List.length_append, shiftr01_length] at hy'; omega
            rw [entry0_shiftr01 hw] at hd
            have := getD_row0_ge hW hw
            omega
    have hB0 : shiftr01 2 0 (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) ≠ [] →
        entry (shiftr01 2 0 (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) 0 0 = 2 + 1 := by
      intro _
      rw [entry0_shiftr01 (by simp), hHU (by simp)]
    have eYB : U' ++ [((x + 2, b + 1, 0) : ℕ × ℕ × ℕ)]
        = Y ++ shiftr01 2 0 (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
      rw [hU']; simp [shiftr01]
    have eidx : U'.length = Y.length + U.length := by
      rw [hU', List.length_append, shiftr01_length]
    rw [eYB, eidx, coneV_pathB hPC hB0 (by simp [shiftr01]), coneV_shift0]
    exact hc
  · have := hload b'' hb'' Z hZ hbZ
    have eM : mlift (P ++ U') b (b'' - b) ++ shiftr01 (x + 2) 0 Z
        = Pb b'' ++ fwH b'' (r + (b'' - b)) (Hb b'') b''
          (((1, r + (b'' - b), 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift (W ++ U) b (b'' - b) ++ shiftr01 x 0 Z)) := by
      rw [mlift_app hP (by rw [eU'']; exact Hd_letter _ _), hPl b'' hb'', eU'',
        mlift_letter hbr (Fr_append hH (Fr_node _ _)) (b'' - b),
        mlift_app hH (Hd_node _ _) b (b'' - b), hHl b'' hb'', mlift_node hbr hFWU (b'' - b)]
      unfold fwH
      rw [Nat.sub_self, mlift_zero]
      simp [shiftr01, Function.comp_def, Nat.add_assoc, List.append_assoc]
    rw [eM]; exact this

/-! ## 頭の補題 -/

theorem FTLc_low_row1 (b r c : ℕ) : ∀ (Lds : List TrioSeq), (∀ D ∈ Lds, Fr D) →
    ∀ y, y < (FTLc b r c Lds).length → entry (FTLc b r c Lds) 0 y ≤ 1 →
      entry (FTLc b r c Lds) 1 y = r := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil =>
      intro _ y hy _
      have hy0 : y = 0 := by
        simp only [FTLc, List.flatMap_nil, List.length_cons, List.length_nil] at hy; omega
      subst hy0; rfl
  | append_singleton Lds D ih =>
      intro hFr y hy h0
      have hFrD : Fr D := hFr D (List.mem_append_right _ (List.mem_singleton_self _))
      have ih' := ih (fun D' h' => hFr D' (List.mem_append_left _ h'))
      rw [FTLc_snoc] at hy h0 ⊢
      rcases Nat.lt_or_ge y (FTLc b r c Lds).length with hlt | hge
      · rw [Small.entry_append_left hlt] at h0 ⊢
        exact ih' y hlt h0
      · obtain ⟨w, rfl⟩ : ∃ w, y = (FTLc b r c Lds).length + w :=
          ⟨y - (FTLc b r c Lds).length, by omega⟩
        rw [entry_append_right] at h0 ⊢
        rcases w with _ | w
        · rfl
        · exfalso
          rw [entry_cons] at h0
          have hw : w < (mlift D c (b - c)).length := by
            simp only [List.length_append, List.length_cons, shiftr01_length] at hy; omega
          rw [entry0_shiftr01 hw] at h0
          have := getD_row0_ge (Fr_mlift hFrD c (b - c)) hw
          omega

theorem FTLc_rep (b r u : ℕ) (Lds : List TrioSeq) (D : TrioSeq) : ∀ m,
    FTLc b r u (Lds ++ List.replicate m D)
      = FTLc b r u Lds ++ (List.range m).flatMap
          (fun _ => ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift D u (b - u)))
  | 0 => by simp
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, FTLc_snoc, FTLc_rep b r u Lds D m,
        List.range_succ, List.flatMap_append]
      simp

theorem fwH_FTLc_snoc (b r u : ℕ) (Lds : List TrioSeq) (D : TrioSeq) :
    fwH b r (FTLc b r u (Lds ++ [D])) u []
      = fwH b r (FTLc b r u Lds) b (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift D u (b - u))) := by
  simp only [fwH, FTLc_snoc, mlift_nil, Nat.sub_self, mlift_zero, List.append_nil]

/-! ## 最後の子の GoodLc の出し入れ -/

theorem GoodLc_snoc_of {u : ℕ} {Lds : List TrioSeq} (hL : GoodLc u Lds) {D : TrioSeq}
    (hD : Fr D ∧ LowC (u + 1) D)
    (hstep : ∀ (A0 : List ℕ) (k0 : ℕ), (∀ a ∈ A0, 1 ≤ a) → 1 ≤ k0 → ∀ (H : ℕ → ℕ) (b0 : ℕ)
      (ws : List (List TrioSeq × ℕ × TrioSeq)), FarCAc A0 k0 H b0 ws →
      ∀ (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), (∀ a ∈ A0, f a = addF H g a) →
        b0 ≤ b → RawWsAc A0 k0 H b (ws ++ [(Lds ++ [D], u, [])]) →
        (∀ s ∈ S, ∀ a ∈ A0, a < s) → (∀ a ∈ S ++ A0, a < o) → (∀ a ∈ S ++ A0, 1 ≤ a) → 1 ≤ o →
        (∀ s ∈ S, reOff (fun _ => 0) (addF H g) A0 k0 ≤ liftVal f (S ++ A0) s) →
        reOff (fun _ => 0) (addF H g) A0 k0 ≤ liftOff f (S ++ A0) o →
        GpT (S ++ A0) o f b (farWc b (b + liftOff f (S ++ A0) o + 1) (relWsc A0 H g ws) ++
          fwH b (b + liftOff f (S ++ A0) o + 1) (FTLc b (b + liftOff f (S ++ A0) o + 1) u Lds) b
            (((1, b + liftOff f (S ++ A0) o + 1, 0) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (mlift D u (b - u))))) :
    GoodLc u (Lds ++ [D]) := by
  have hraw : ∀ D' ∈ Lds ++ [D], Fr D' ∧ LowC (u + 1) D' := by
    intro D' hD'
    rcases List.mem_append.mp hD' with hD' | hD'
    · exact hL.1 D' hD'
    · rw [List.mem_singleton] at hD'; rw [hD']; exact hD
  refine ⟨hraw, fun A0 k0 hA01 hk1 H b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
  have e0 : ∀ c (K G : ℕ → ℕ), reliftX c K G A0 ([] : TrioSeq) = [] := fun c K G => by
    unfold reliftX; exact slift_nil _
  simp only [relWsc_snoc, farWc_snoc]
  rw [e0, map_tie_inv hA01 (fun D' hD' => (hraw D' hD').2) H g, fwH_FTLc_snoc]
  exact hstep A0 k0 hA01 hk1 H b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo

theorem GoodLc_snoc_elim {u : ℕ} {Lds : List TrioSeq} {D : TrioSeq} (h : GoodLc u (Lds ++ [D]))
    {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0) (H : ℕ → ℕ) (b0 : ℕ)
    (ws : List (List TrioSeq × ℕ × TrioSeq)) (hC : FarCAc A0 k0 H b0 ws)
    (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ) (hf : ∀ a ∈ A0, f a = addF H g a)
    (hb : b0 ≤ b) (hR : RawWsAc A0 k0 H b (ws ++ [(Lds ++ [D], u, [])]))
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (hA : ∀ a ∈ S ++ A0, a < o) (hA1 : ∀ a ∈ S ++ A0, 1 ≤ a)
    (ho : 1 ≤ o) (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF H g) A0 k0 ≤ liftVal f (S ++ A0) s)
    (hKo : reOff (fun _ => 0) (addF H g) A0 k0 ≤ liftOff f (S ++ A0) o) :
    GpT (S ++ A0) o f b (farWc b (b + liftOff f (S ++ A0) o + 1) (relWsc A0 H g ws) ++
      fwH b (b + liftOff f (S ++ A0) o + 1) (FTLc b (b + liftOff f (S ++ A0) o + 1) u Lds) b
        (((1, b + liftOff f (S ++ A0) o + 1, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift D u (b - u)))) := by
  have := h.2 A0 k0 hA01 hk1 H b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo
  have e0 : ∀ c (K G : ℕ → ℕ), reliftX c K G A0 ([] : TrioSeq) = [] := fun c K G => by
    unfold reliftX; exact slift_nil _
  simp only [relWsc_snoc, farWc_snoc] at this
  rw [e0, map_tie_inv hA01 (fun D' hD' => (h.1 D' hD').2) H g, fwH_FTLc_snoc] at this
  exact this

theorem RawWsAc_child {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} {Lds : List TrioSeq} {D D' : TrioSeq} {u : ℕ}
    (hR : RawWsAc A0 k0 H b (ws ++ [(Lds ++ [D], u, [])]))
    (hD' : Fr D' ∧ LowC (u + reOff (fun _ => 0) H A0 k0) D') :
    RawWsAc A0 k0 H b (ws ++ [(Lds ++ [D'], u, [])]) := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact hR w (List.mem_append_left _ hw)
  · rw [List.mem_singleton] at hw
    subst hw
    have h1 := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
    refine ⟨h1.1, fun Ld hLd => ?_, h1.2.2⟩
    rcases List.mem_append.mp hLd with hLd | hLd
    · exact h1.2.1 Ld (List.mem_append_left _ hLd)
    · rw [List.mem_singleton] at hLd
      rw [hLd]; exact hD'

/-! ## 子の差し込み口の族 -/

def ChOK (v : ℕ) (D : TrioSeq) : Prop :=
  Hd D ∧ LowC (v + 1) D ∧
    ∀ u, v ≤ u → ∀ Lds, GoodLc u Lds → GoodLc u (Lds ++ [mlift D v (u - v)])

theorem mlift_comp_vub {v u b : ℕ} (hvu : v ≤ u) (hub : u ≤ b) (X : TrioSeq) :
    mlift (mlift X v (u - v)) u (b - u) = mlift X v (b - v) := by
  have e := mlift_mlift X v (u - v) (b - u)
  rw [show v + (u - v) = u by omega, show u - v + (b - u) = b - v by omega] at e
  exact e

theorem LowC_v1_lift {v u : ℕ} (hvu : v ≤ u) {X : TrioSeq} (h : LowC (v + 1) X) :
    LowC (u + 1) (mlift X v (u - v)) := by
  have := LowC_mliftk h (u - v)
  rwa [show v + 1 + (u - v) = u + 1 by omega] at this

theorem GoodLc_rep {u : ℕ} {D : TrioSeq} (hD : ∀ Lds, GoodLc u Lds → GoodLc u (Lds ++ [D]))
    {Lds : List TrioSeq} (hL : GoodLc u Lds) : ∀ m, GoodLc u (Lds ++ List.replicate m D)
  | 0 => by simpa using hL
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc]
      exact hD _ (GoodLc_rep hD hL m)

/-- ★ 最後の F のタイの子の差し込み口の公理。 -/
theorem ChOK_ax : SlotAx ChOK where
  lift := by
    intro v W hW h u1 hu1
    refine ⟨Hd_mlift h.1 v (u1 - v), LowC_v1_lift hu1 h.2.1, fun u hu Lds hL => ?_⟩
    have e := mlift_mlift W v (u1 - v) (u - u1)
    rw [show v + (u1 - v) = u1 by omega, show u1 - v + (u - u1) = u - v by omega] at e
    rw [e]
    exact h.2.2 u (le_trans hu1 hu) Lds hL
  oper := by
    intro v W U hW hU hH hlen hp hIH
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    have hI1 := hIH 1 le_rfl
    have hU1 : U⟦1⟧ = U.dropLast := oper_one_eq_dropLast (by omega)
    have hLow : LowC (v + 1) (W ++ U) := by
      have hI1' := hI1.2.1
      rw [hU1] at hI1'
      obtain ⟨q, hq, -⟩ := hp
      have hqlt : q < U.length - 1 := nextR_index_lt hq
      have hrt := rtg_nextrel0_lift W U (rtg0_of_nextR' hq)
      have hsplit : W ++ U = (W ++ U.dropLast) ++ [U.getLast hUne] := by
        rw [List.append_assoc, List.dropLast_append_getLast hUne]
      rw [hsplit] at hrt ⊢
      have hlenD : (W ++ U.dropLast).length = W.length + (U.length - 1) := by
        rw [List.length_append, List.length_dropLast]
      rw [← hlenD] at hrt
      exact LowC_snoc_anc hI1' (by rw [hlenD]; omega) hrt
    refine ⟨Hd_append_of hH hI1.1, hLow, fun u hu Lds hL => ?_⟩
    refine GoodLc_snoc_of hL ⟨Fr_mlift (Fr_append hW hU) _ _, LowC_v1_lift hu hLow⟩
      (fun A0 k0 hA01 hk1 H b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_)
    have hw := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hub : u ≤ b := hw.1
    have hKge : k0 ≤ reOff (fun _ => 0) H A0 k0 := by unfold reOff; omega
    rw [mlift_comp_vub hu hub, mlift_app hW hH]
    refine cstep_oper hA hA1 ho f (Fr_farWc _ _ _) (by rw [mlift_length]; exact hlen)
      ((hasParent_mlift_iff v (b - v) hUne).mpr hp) (fun m hm => ?_)
    have hIm := hIH m hm
    have hRm := RawWsAc_child hR (D' := mlift (W ++ U⟦m⟧) v (u - v))
      ⟨Fr_mlift (Fr_append hW (Fr_oper hU m)) _ _,
        LowC_mono (by omega) (LowC_v1_lift hu hIm.2.1)⟩
    have := GoodLc_snoc_elim (hIm.2.2 u hu Lds hL) hA01 hk1 H b0 ws hC g S o f b hf hb hRm hSA hA
      hA1 ho hK hKo
    rw [mlift_comp_vub hu hub, mlift_app hW (Hd_oper hH hUne hm), ← mlift_oper'] at this
    exact this
  orph := by
    intro v W U h j hW hU hH hj1 hj hnp hz
    have hz0 := hz [] (Wg_nil _) based_nil
    have e0 : W ++ (U ++ shiftr01 h 0 []) = W ++ U := by simp [shiftr01]
    rw [e0] at hz0
    have hLow : LowC (v + 1) (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
      rw [← List.append_assoc]
      exact LowC_snoc hz0.2.1 _ (by show j ≤ v + 1; omega)
    refine ⟨Hd_append_of hH hz0.1, hLow, fun u hu Lds hL => ?_⟩
    refine GoodLc_snoc_of hL ⟨Fr_mlift (Fr_append hW hU) _ _, LowC_v1_lift hu hLow⟩
      (fun A0 k0 hA01 hk1 H b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_)
    have hw := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hub : u ≤ b := hw.1
    have hKge : k0 ≤ reOff (fun _ => 0) H A0 k0 := by unfold reOff; omega
    have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
    have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ v := hj
    rw [mlift_comp_vub hu hub, mlift_app hW hH, mlift_snoc_low U _ hc]
    refine cstep_orph hA hA1 ho f (show b < b + liftOff f (S ++ A0) o + 1 by omega) (Fr_FTLc _ _ _ _)
      (Fr_farWc _ _ _) (Fr_mlift hW _ _)
      (by rw [← mlift_snoc_low U _ hc]; exact Hd_mlift hH _ _) hj1 (by omega) ?_
      (fun z hz' hbz => ?_)
    · intro hh
      apply hnp
      rw [← mlift_snoc_low U _ hc, mlift_eq_slift, hasParent_slift (stair_step _ _),
        mlift_length] at hh
      exact hh
    · have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
      have hHz : Hd (U ++ shiftr01 h 0 z) := Hd_append_shift hH hbz
      have hFrz : Fr (U ++ shiftr01 h 0 z) := by
        have hh1 : 1 ≤ h := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
        refine Fr_append hUc (fun y hy => ?_)
        simp only [shiftr01, List.mem_map] at hy
        obtain ⟨p, -, rfl⟩ := hy
        dsimp only; omega
      have hzz := hz z hz' hbz
      have hlowz := low_of_Wg hzW h (show j ≤ v by omega)
      have hRz := RawWsAc_child hR (D' := mlift (W ++ (U ++ shiftr01 h 0 z)) v (u - v))
        ⟨Fr_mlift (Fr_append hW hFrz) _ _, LowC_mono (by omega) (LowC_v1_lift hu hzz.2.1)⟩
      have := GoodLc_snoc_elim (hzz.2.2 u hu Lds hL) hA01 hk1 H b0 ws hC g S o f b hf hb hRz hSA hA
        hA1 ho hK hKo
      rw [mlift_comp_vub hu hub, mlift_app hW hHz, mlift_append_low hlowz] at this
      exact this
  tie := by
    intro v W U x hW hU hH hc hload
    have h0 := hload v le_rfl [] (Wg_nil _) based_nil
    have e0 : mlift (W ++ U) v (v - v) ++ shiftr01 x 0 [] = W ++ U := by
      simp [shiftr01, mlift_zero]
    rw [e0] at h0
    have hLow : LowC (v + 1) (W ++ (U ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)])) := by
      rw [← List.append_assoc]
      exact LowC_snoc h0.2.1 _ (by show v + 1 ≤ v + 1; omega)
    refine ⟨Hd_append_of hH h0.1, hLow, fun u hu Lds hL => ?_⟩
    refine GoodLc_snoc_of hL ⟨Fr_mlift (Fr_append hW hU) _ _, LowC_v1_lift hu hLow⟩
      (fun A0 k0 hA01 hk1 H b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_)
    have hw := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hub : u ≤ b := hw.1
    have hR0 : RawWsAc A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
    have hKge : k0 ≤ reOff (fun _ => 0) H A0 k0 := by unfold reOff; omega
    have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
    have hHU : Hd U := by
      intro hne
      have := hH (by simp)
      rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
    have hLds : ∀ D ∈ Lds, Fr D := fun D hD => (hL.1 D hD).1
    have eT : mlift (U ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) v (b - v)
        = mlift U v (b - v) ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)] := by
      rw [mlift_snoc_cone U _ hc]
      show _ ++ [((x, v + 1 + (b - v), 0) : ℕ × ℕ × ℕ)] = _
      rw [show v + 1 + (b - v) = b + 1 by omega]
    rw [mlift_comp_vub hu hub, mlift_app hW hH, eT]
    obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f (S ++ A0) o + 1 := ⟨_, rfl⟩
    rw [← hr]
    refine cstep_tie hA hA1 ho f (show b < r by omega) (Fr_FTLc _ _ _ _) (Fr_farWc _ _ _)
      (Fr_mlift hW _ _) (fun y hy h0y => by rw [FTLc_low_row1 b r u Lds hLds y hy h0y]; omega)
      (fun b'' => farWc b'' (b'' + liftOff f (S ++ A0) o + 1) (relWsc A0 H g ws))
      (fun b'' => FTLc b'' (b'' + liftOff f (S ++ A0) o + 1) u Lds)
      (fun b'' hb'' => ?_) (fun b'' hb'' => ?_)
      (by rw [← eT]; exact Fr_mlift hU _ _) (by rw [← eT]; exact Hd_mlift hH _ _) ?_
      (fun b'' hb'' Z hZ hbZ => ?_)
    · show mlift (farWc b r (relWsc A0 H g ws)) b (b'' - b)
        = farWc b'' (b'' + liftOff f (S ++ A0) o + 1) (relWsc A0 H g ws)
      rw [mlift_farWc_basek (show b < r by omega) (b'' - b) _ (RawWskc_relWsc hR0 g),
        show b + (b'' - b) = b'' by omega, show r + (b'' - b) = b'' + liftOff f (S ++ A0) o + 1 by omega]
    · show mlift (FTLc b r u Lds) b (b'' - b) = FTLc b'' (b'' + liftOff f (S ++ A0) o + 1) u Lds
      rw [mlift_FTLc_base (show b < r by omega) hub (b'' - b) Lds hLds,
        show b + (b'' - b) = b'' by omega, show r + (b'' - b) = b'' + liftOff f (S ++ A0) o + 1 by omega]
    · have h0' := coneV_mlift (by simp) hc (b - v)
      rw [eT, show v + (b - v) = b by omega] at h0'
      rw [mlift_length]
      exact h0'
    · have hFrWU : Fr (W ++ U) := Fr_append hW hUc
      have hx1 : 1 ≤ x := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hL2 := hload b'' (by omega) Z hZ hbZ
      obtain ⟨Y, hY⟩ : ∃ Y, Y = mlift (W ++ U) v (b'' - v) ++ shiftr01 x 0 Z := ⟨_, rfl⟩
      rw [← hY] at hL2
      have hGb : GoodLc b'' (Lds.map (fun D => mlift D u (b'' - u))) := GoodLc_lift hL (by omega)
      have hGY := hL2.2.2 b'' le_rfl _ hGb
      rw [Nat.sub_self, mlift_zero] at hGY
      have hFrY : Fr Y := by
        rw [hY]
        refine Fr_append (Fr_mlift hFrWU _ _) (fun y hy => ?_)
        simp only [shiftr01, List.mem_map] at hy
        obtain ⟨p, -, rfl⟩ := hy
        dsimp only; omega
      have hKb : ∀ D ∈ Lds.map (fun D => mlift D u (b'' - u)) ++ [Y],
          Fr D ∧ LowC (b'' + reOff (fun _ => 0) H A0 k0) D :=
        fun D hD => ⟨(hGY.1 D hD).1, LowC_mono (by omega) (hGY.1 D hD).2⟩
      have hRb : RawWsAc A0 k0 H b'' (ws ++ [(Lds.map (fun D => mlift D u (b'' - u)) ++ [Y], b'', [])]) :=
        RawWsAc_snoc (RawWsAc_mono (by omega) hR0) ⟨le_rfl, hKb, Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
      have := GoodLc_snoc_elim hGY hA01 hk1 H b0 ws hC g S o f b'' hf (by omega) hRb hSA hA hA1 ho hK hKo
      rw [Nat.sub_self, mlift_zero, FTLc_rebase (show u ≤ b'' by omega) le_rfl] at this
      have eY : Y = mlift (mlift W v (b - v) ++ mlift U v (b - v)) b (b'' - b) ++ shiftr01 x 0 Z := by
        rw [hY, ← mlift_app hW hHU]
        have e := mlift_mlift (W ++ U) v (b - v) (b'' - b)
        rw [show v + (b - v) = b by omega, show b - v + (b'' - b) = b'' - v by omega] at e
        rw [e]
      rw [eY] at this
      dsimp only
      rw [show b'' + liftOff f (S ++ A0) o + 1 = r + (b'' - b) by omega]
      rw [show b'' + liftOff f (S ++ A0) o + 1 = r + (b'' - b) by omega] at this
      exact this
  flat := by
    intro v W hW h
    have hLow : LowC (v + 1) (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) :=
      LowC_snoc h.2.1 _ (by show 0 ≤ v + 1; omega)
    refine ⟨Hd_append_of (V' := []) (fun _ => rfl) (by simpa using h.1), hLow, fun u hu Lds hL => ?_⟩
    have hFrW1 : Fr (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := Fr_append hW (GzF.Fr_single le_rfl _ _)
    refine GoodLc_snoc_of hL ⟨Fr_mlift hFrW1 _ _, LowC_v1_lift hu hLow⟩
      (fun A0 k0 hA01 hk1 H b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_)
    have hw := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hub : u ≤ b := hw.1
    have hR0 : RawWsAc A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
    have hKge : k0 ≤ reOff (fun _ => 0) H A0 k0 := by unfold reOff; omega
    rw [mlift_comp_vub hu hub, mlift_snoc_flat W 1 v (b - v) hW]
    refine HbU.child_flat_step hA hA1 ho f (Fr_FTLc _ _ _ _) (Fr_farWc _ _ _) (Fr_mlift hW _ _)
      (fun m => ?_)
    have hDW : ∀ Lds', GoodLc u Lds' → GoodLc u (Lds' ++ [mlift W v (u - v)]) :=
      fun Lds' hL' => h.2.2 u hu Lds' hL'
    have hGm := GoodLc_rep hDW hL m
    have hRm : RawWsAc A0 k0 H b (ws ++ [(Lds ++ List.replicate m (mlift W v (u - v)), u, [])]) := by
      refine RawWsAc_snoc hR0 ⟨hub, fun D hD => ⟨(hGm.1 D hD).1,
        LowC_mono (show u + 1 ≤ u + reOff (fun _ => 0) H A0 k0 by omega) (hGm.1 D hD).2⟩,
        Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
    have := hGm.2 A0 k0 hA01 hk1 H b0 ws hC g S o f b hf hb hRm hSA hA hA1 ho hK hKo
    have e0 : ∀ c (K G : ℕ → ℕ), reliftX c K G A0 ([] : TrioSeq) = [] := fun c K G => by
      unfold reliftX; exact slift_nil _
    simp only [relWsc_snoc, farWc_snoc] at this
    rw [e0, map_tie_inv hA01 (fun D hD => (hGm.1 D hD).2) H g, FTLc_rep, mlift_comp_vub hu hub] at this
    have ef : ∀ Y, fwH b (b + liftOff f (S ++ A0) o + 1) Y u [] = fwH b (b + liftOff f (S ++ A0) o + 1) Y b [] := by
      intro Y; simp [fwH, mlift_nil]
    rw [ef] at this
    exact this

end HcF
end TRIO
