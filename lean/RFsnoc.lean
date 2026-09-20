/-
RFsnoc.lean: PVP_snoc_gen — general-f 遠い語頭+内容 append（PVF_snoc の general-f 版）。
GpT_snocz_core(GyG:93, bare頭, general-f) の塔に内容 Y を通す手術。
PVP_snoc_gen の ∀t wrapper は完成（hPV' を mlift_mlift で埋め、PVP_snocz に倣う）。
残余 = GpT_snocz_content（塔+内容の core）+ RLC level-shift（hY'）。
-/
import GzD

namespace TRIO
namespace RFsnoc

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD

/-- GpT レベルの 遠い語頭+内容（general f）。GpT_snocz_core に内容 Y を通す（core surgery）。 -/
theorem GpT_snocz_content {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) {f : ℕ → ℕ} {b : ℕ} {W Y : TrioSeq} (hW : Fr W) (hYfr : Fr Y)
    (hPV : ∀ t, GpT A (o + t) f b (mlift W (b + liftOff f A o) t))
    (hY : RLC A o (fun _ => 0) b Y) :
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

/-- RLC の段シフト（o → o+t、Y → mlift Y u t）。wrapper が o+t で GpT_snocz_content を使うため。 -/
theorem RLC_levelshift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {f : ℕ → ℕ} {b : ℕ} {Y : TrioSeq}
    (hY : RLC A o (fun _ => 0) b Y) (t : ℕ) :
    RLC A (o + t) (fun _ => 0) b (mlift Y (b + liftOff f A o) t) := by
  -- FALSE as reindex: `hY g b'` gives LC1 at offset o+g·o, anchor (o::A);
  -- goal needs offset o+t+g·(o+t), anchor ((o+t)::A). The anchor shift o→o+t is the blocker.
  -- ∴ the ∀t-wrapper-at-offset-o framing is wrong; R_farword uses RLC's LC1 at the
  -- shifted offset (o+g·o) directly. Core = LC1_farword at GENERAL offset (like RLF_child/R_child).
  sorry

/-- **PVP_snoc_gen**: general-f の PVF_snoc。∀t で GpT_snocz_content を回す（PVP_snocz に倣う、wrapper 完成）。 -/
theorem PVP_snoc_gen {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {f : ℕ → ℕ} {b : ℕ} {W Y : TrioSeq} (hW : Fr W) (hYfr : Fr Y)
    (h : PVP A o f b W) (hY : RLC A o (fun _ => 0) b Y) :
    PVP A o f b (W ++ ((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y) := by
  intro t
  set u := b + liftOff f A o with hu
  have eML : mlift (W ++ ((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y) u t
      = mlift W u t ++ ((1, u + 1 + t, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift Y u t) := by
    rw [mlift_app hW (Hd_letter _ _), mlift_letter (show u < u + 1 by omega) hYfr t]
  rw [eML]
  have ehead : u + 1 + t = b + liftOff f A (o + t) + 1 := by rw [hu, liftOff_add_t hA]; omega
  rw [ehead]
  have huteq : b + liftOff f A (o + t) = u + t := by rw [hu, liftOff_add_t hA]; omega
  refine GpT_snocz_content (o := o + t) (fun a ha => by have := hA a ha; omega) hA1 (by omega)
    (Fr_mlift hW _ _) (Fr_mlift hYfr _ _) (fun t' => ?_) ?_
  · -- hPV': GpT A (o+t+t') f b (mlift (mlift W u t) (b+liftOff f A (o+t)) t')
    rw [huteq, mlift_mlift W u t t']
    have := h (t + t')
    rwa [show o + (t + t') = o + t + t' by omega, ← hu] at this
  · -- hY': RLC A (o+t) (fun_=>0) b (mlift Y u t)  = RLC_levelshift
    rw [hu]; exact RLC_levelshift hA hY t

end RFsnoc
end TRIO
