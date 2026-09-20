/-
RFsnoc.lean: PVP_snoc_gen — general-f 遠い語頭+内容 append（PVF_snoc の general-f 版）。
GpT_snocz_core(GyG:93, bare頭, general-f) の塔に内容 Y を通す手術。
PVP_snoc_gen の ∀t wrapper は完成（hPV' を mlift_mlift で埋め、PVP_snocz に倣う）。
残余 = GpT_snocz_content（塔+内容の core）+ RLC level-shift（hY'）。
-/
import GzD
import RFarword

namespace TRIO
namespace RFsnoc

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD

/-- 内容 oper（末端 tie 版, P=[]）: 根+遠い語頭+tie の展開 = (根,遠い語頭) の塔。
    モデル検証済み（tools/trio.py）。bad root=tie(行1), 親=根(col0), d0=2, d1=0。 -/
theorem oper_headtie (u n : ℕ) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 0) : ℕ × ℕ × ℕ)])⟦n⟧
      = (List.range n).flatMap (fun k =>
          [((2 * k, u, 0) : ℕ × ℕ × ℕ), ((2 * k + 1, u + 1, 1) : ℕ × ℕ × ℕ)]) := by
  set M : TrioSeq := ((0, u, 0) : ℕ × ℕ × ℕ) ::
    [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 0) : ℕ × ℕ × ℕ)] with hM
  have hj1 : (2 : ℕ) = M.length - 1 := by rw [hM]; rfl
  have hRne : ([((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 0) : ℕ × ℕ × ℕ)] : TrioSeq) ≠ [] := by simp
  have hRarg : argOK ([((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 0) : ℕ × ℕ × ℕ)] : TrioSeq) := by
    intro p hp
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp
  have hsrow : srow M 2 = 1 := by rw [hM]; simp [srow, entry]
  have hle02 : le0 M 0 2 := by
    have := le0_cons_zero (v := u) (z := 0) hRarg 1 (by simp); rw [hM]; exact this
  have hpar : hasParent M 1 2 :=
    H12Export.hasParent1_of_le0 (by rw [hM]; simp) hle02 (by rw [hM]; simp [entry])
  have hsrowR : srow ([((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
      (([((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 0) : ℕ × ℕ × ℕ)] : TrioSeq).length - 1) = 1 := by
    simp [srow, entry]
  have hdomT : domT ([((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 0) : ℕ × ℕ × ℕ)] : TrioSeq) (2 * u + 1) := by
    refine ⟨by simp [lev, entry]; omega, ?_⟩
    rw [hsrowR]
    rintro ⟨j0, hnr, -⟩
    -- R の最後の tie (2,u+1,0) は R 内に行1の親を持たない（col 0 の行1 = u+1 = tie の行1）
    unfold nextR at hnr
    rw [if_neg (by omega), if_pos rfl] at hnr
    obtain ⟨-, -, hj0lt, hentlt, -, -⟩ := hnr
    simp only [List.length_cons, List.length_nil] at hj0lt hentlt
    have hj00 : j0 = 0 := by omega
    subst hj00
    simp [entry] at hentlt
  have hpM : hasParent M (srow ([((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
      (([((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 0) : ℕ × ℕ × ℕ)] : TrioSeq).length - 1))
      ([((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 0) : ℕ × ℕ × ℕ)] : TrioSeq).length := by
    rw [hsrowR]; exact hpar
  have hj0 : (0 : ℕ) = parent M 1 2 := by
    have h := parent_cons_eq_zero (v := u) (z := 0) hRne hdomT hpM
    rw [hsrowR] at h; exact h.symm
  rw [L53.oper_unfold (j1 := 2) (i1 := 1) (j0 := 0) (d0 := 2) (d1 := 0) hj1 (by omega)
    (by rw [hM]; simp [entry]) hsrow.symm hpar hj0
    (by rw [hM]; simp [entry]) (by simp) n]
  simp only [List.take_zero, List.nil_append, Nat.sub_zero]
  apply List.flatMap_congr
  intro k _
  have hR : argOK ([((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 0) : ℕ × ℕ × ℕ)] : TrioSeq) := by
    intro p hp
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp
  have hl00 : le0 M 0 0 := ⟨by rw [hM]; simp, by rw [hM]; simp, Relation.ReflTransGen.refl⟩
  have hl01 : le0 M 0 1 := by
    have := le0_cons_zero (v := u) (z := 0) hR 0 (by simp)
    rw [hM]; exact this
  show List.map _ (List.range' 0 2) = _
  rw [show (2 : ℕ) = 1 + 1 from rfl, List.range'_succ, List.range'_one, List.map_cons,
    List.map_cons, List.map_nil]
  rw [if_pos hl00, if_pos hl01, hM]
  simp only [entry, List.getD_cons_zero, List.getD_cons_succ, if_true, ite_self,
    Nat.mul_zero, Nat.add_zero, List.cons.injEq, Prod.mk.injEq, and_true, List.nil_eq]
  refine ⟨⟨by omega, rfl, rfl⟩, by omega, rfl, rfl⟩

/-- GpT レベルの 遠い語頭+内容（general f）。内容 Y は具体的な Wg-load（based）。
    Y の末尾 tie が graft し (根, 遠い語頭) を複写する（oper_cons_tower1, モデル検証済み）。 -/
theorem GpT_snocz_content {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) {f : ℕ → ℕ} {b : ℕ} {W Y : TrioSeq} (hW : Fr W) (hYfr : Fr Y)
    (hPV : ∀ t, GpT A (o + t) f b (mlift W (b + liftOff f A o) t))
    (hbY : based Y) (hYW : Y ∈ Wg (2 * b)) :
    GpT A o f b (W ++ ((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y) := by
  refine GpT_intro hA (fun R hR g => ?_)
  rw [reliftX_app hW (Hd_letter _ _) b f g,
    show ((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ) = ((1, b + (liftOff f A o + 1), 1) : ℕ × ℕ × ℕ)
      from by rw [Nat.add_assoc],
    reliftX_node hYfr b (liftOff f A o + 1) 1 f g A,
    reOff_above hA f g 1,
    show lowP f A (liftOff f A o + 1) = A from
      lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)]
  have hW1 : Fr (reliftX b f g A W) := Fr_reliftX hW _ _ _ _
  have hY1 : Fr (reliftX b f g A Y) := Fr_reliftX hYfr _ _ _ _
  have hPV1 : ∀ t, GpT A (o + t) (addF f g) b
      (mlift (reliftX b f g A W) (b + liftOff (addF f g) A o) t) := by
    intro t
    have := GpT_lift (fun a ha => by have := hA a ha; omega) (hPV t) g
    rwa [mlift_reliftX_high hA] at this
  obtain ⟨F, hF⟩ : ∃ F, F = addF f g := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = liftOff F A o := ⟨_, rfl⟩
  rw [← hF] at hPV1 ⊢
  rw [← hk] at hPV1 ⊢
  intro u' hu X hX hRX
  obtain ⟨d, hd⟩ : ∃ d, d = u' - b := ⟨_, rfl⟩
  rw [← hd]
  rw [mlift_app hW1 (Hd_letter (b + (k + 1)) (reliftX b f g A Y)) b d,
    mlift_letter (show b < b + (k + 1) by omega) hY1 d]
  obtain ⟨V, hV⟩ : ∃ V : ℕ → TrioSeq,
      V = fun τ => mlift (mlift (reliftX b f g A W) b d) (u' + k) (τ - k) := ⟨_, rfl⟩
  obtain ⟨Vy, hVy⟩ : ∃ Vy : ℕ → TrioSeq,
      Vy = fun τ => mlift (mlift (reliftX b f g A Y) b d) (u' + k) (τ - k) := ⟨_, rfl⟩
  have hVFr : ∀ τ, Fr (V τ) := fun τ => by rw [hV]; exact Fr_mlift (Fr_mlift hW1 _ _) _ _
  have hVyFr : ∀ τ, Fr (Vy τ) := fun τ => by rw [hVy]; exact Fr_mlift (Fr_mlift hY1 _ _) _ _
  have hk1 : 1 ≤ k := by rw [hk]; unfold liftOff; omega
  have hBase : ∀ τ, k ≤ τ → GpT A (o + (τ - k)) F u' (V τ) := by
    intro τ hτ
    have h0 := hPV1 (τ - k)
    have h1 := (GpT_ax (fun a ha => by have := hA a ha; omega) hA1 (by omega) F).lift b _
      (Fr_mlift hW1 _ _) h0 u' hu
    rw [← hd, mlift_commk, show b + k + d = u' + k by omega] at h1
    rw [hV]; exact h1
  have eStep : ∀ τ, k ≤ τ → mlift (V τ) (u' + τ) 1 = V (τ + 1) := by
    intro τ hτ
    rw [hV]
    have := mlift_mlift (mlift (reliftX b f g A W) b d) (u' + k) (τ - k) 1
    rw [show u' + k + (τ - k) = u' + τ by omega, show τ - k + 1 = τ + 1 - k by omega] at this
    exact this
  rw [show mlift (reliftX b f g A W) b d = V k from by rw [hV]; simp [mlift_zero],
    show mlift (reliftX b f g A Y) b d = Vy k from by rw [hVy]; simp [mlift_zero],
    show ((1, b + (k + 1) + d, 1) : ℕ × ℕ × ℕ) = ((1, u' + k + 1, 1) : ℕ × ℕ × ℕ) from by
      rw [hd, show b + (k + 1) + (u' - b) = u' + k + 1 by omega]]
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq,
      U0 = ((0, u' + k, 0) : ℕ × ℕ × ℕ) ::
        (V k ++ ((1, u' + k + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (Vy k)) := ⟨_, rfl⟩
  have eU : ((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (V k ++ ((1, u' + k + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (Vy k))
      = shiftr01 1 0 U0 := by rw [hU0]; simp [shiftr01]
  rw [eU]
  have hlen : 2 ≤ U0.length := by rw [hU0]; simp; omega
  refine (hR F).1.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
    (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp), hU0]; rfl)
    (by rw [shiftr01_length]; exact hlen) ?_ (fun m hm => ?_)
  · -- hasParent: U0 の最後の列（Vy k の末尾 tie）の親は根 (0,u'+k,0)。
    -- モデル: (0,u,0)(1,u+1,1)(2,u+1,0) の bad root の親 = col 0（根）。
    sorry
  · -- oper reduction: (shiftr01 1 0 U0)⟦m⟧ を計算 → 内容 tie が graft し (根,遠い語頭) を複写する
    -- 塔（bare-head far-word tower）になる（モデル検証済み）。この塔は GpT_snocz_core の機構で閉じる。
    -- 残余 = 内容 oper 補題 (0,u,0)(1,u+1,1)(2,u+1,0)⟦m⟧ = flatMap k<m [(2k,u,0),(2k+1,u+1,1)]。
    sorry

/-- **PVP_snoc_gen**: general-f の PVF_snoc。∀t で GpT_snocz_content を回す。
    内容 Y は具体 Wg-load。based Wg-load は row1 ≤ b ≤ u なので mlift Y u t = Y（mlift-closed）。 -/
theorem PVP_snoc_gen {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {f : ℕ → ℕ} {b : ℕ} {W Y : TrioSeq} (hW : Fr W) (hYfr : Fr Y)
    (h : PVP A o f b W) (hbY : based Y) (hYW : Y ∈ Wg (2 * b))
    (hYlow : ∀ y ∈ Y, y.2.1 ≤ b) :
    PVP A o f b (W ++ ((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y) := by
  intro t
  set u := b + liftOff f A o with hu
  have hYfix : mlift Y u t = Y := by
    -- based Wg-load: 全列 row1 ≤ b ≤ u なので coneV Y u j は偽 → mlift 恒等
    sorry
  have eML : mlift (W ++ ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y) u t
      = mlift W u t ++ ((1, u + 1 + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y := by
    rw [mlift_app hW (Hd_letter _ _), mlift_letter (show u < u + 1 by omega) hYfr t, hYfix]
  rw [eML]
  have ehead : u + 1 + t = b + liftOff f A (o + t) + 1 := by rw [hu, liftOff_add_t hA]; omega
  rw [ehead]
  have huteq : b + liftOff f A (o + t) = u + t := by rw [hu, liftOff_add_t hA]; omega
  refine GpT_snocz_content (o := o + t) (fun a ha => by have := hA a ha; omega) hA1 (by omega)
    (Fr_mlift hW _ _) hYfr (fun t' => ?_) hbY hYW
  -- hPV': GpT A (o+t+t') f b (mlift (mlift W u t) (b+liftOff f A (o+t)) t')
  rw [huteq, mlift_mlift W u t t']
  have := h (t + t')
  rwa [show o + (t + t') = o + t + t' by omega, ← hu] at this

/-- **GT 0 Trc4 を直接証明**（GT_tie/GTC_tie を迂回、Om は flat なので ∀荷でなく bare-head 塔）。 -/
theorem gt_trc4' : GT 0 RFarword.Trc4 := by
  intro L hL hB u hu
  refine fun harg a ha => ?_
  rw [List.map_append, List.map_singleton, rword_append, rword_singleton, Nat.sub_zero,
    RFarword.render_Trc4]
  -- 核: Q ++ [dh1,dh2,tie] ∈ Wg a, ただし Q = (0,u,0)::rword 0 u (mapped L) ∈ Wg a（hB より）。
  -- tie (3,u+1,0) の親 = 根 (0,u,0)。oper は根→tie を複写（bare double-head の塔）。
  have hQ : ((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (L.map (fun X => mlift X 0 u)) ∈ Wg a := by
    have hargL : argOK (rword 0 u (L.map (fun X => mlift X 0 (u - 0)))) := argOK_rword u _
    have h := hB u hu hargL a ha
    rwa [Nat.sub_zero] at h
  -- 核: Q ++ [(1,u+1,1),(2,u+1,1),(3,u+1,0)] ∈ Wg a （Q=hQ ∈ Wg a）。
  -- tie (3,u+1,0) の行1親 = 根 (0,u,0)。oper は (根..tie) = Q+二重頭 を複写（bare-head 塔 over Q）。
  -- Aopg case-b（natDom ∧ ∀n oper∈Wg）+ 塔機構（tower1_mem_v / oper_headtie 系）で閉じる。
  sorry

end RFsnoc
end TRIO
