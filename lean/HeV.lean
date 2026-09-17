/-
HeV.lean: 深い葉 keystone GoodChtX_deep の下流。深い葉の遠い語が FarCAt/RawWsAt を満たす
（GoodChtX_deep + OkWsAt_cons + FarCAt_of_OkWsAt）。これが topCLT_WgL_deep → GTC_far_deep →
証明中の行 BwT [K,K2] への第一歩。
-/
import HeU

namespace TRIO
namespace HeV

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ HeI HeK HeU

/-- 深い葉の遠い語（子 = 深い葉 [tie 1 [tie 1 []]]、段 u、荷なし）。 -/
def dlws (u : ℕ) : List (List (List HdA.UT) × ℕ × TrioSeq) :=
  [([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], u, ([] : TrioSeq))]

/-- ★ 深い葉の遠い語は OkWsAt（子は GoodChtX_deep、荷は okRAt_nil）。 -/
theorem OkWsAt_deep {u b : ℕ} (hub : u ≤ b) : OkWsAt [] 1 b (dlws u) := by
  refine HdH.OkWsAt_cons hub ?_ (HdH.okRAt_nil [] 1 u) (HdH.OkWsAt_nil [] 1 b)
  exact HeU.GoodChtX_deep (by simp) (by simp) (by decide)

/-- ★ 深い葉の遠い語は FarCAt。 -/
theorem FarCAt_deep {u b : ℕ} (hub : u ≤ b) (b0 : ℕ) : FarCAt [] 1 (fun _ => 0) b0 (dlws u) :=
  HdH.FarCAt_of_OkWsAt (by simp) (by simp) (by decide) (dlws u) (OkWsAt_deep hub) b0

/-- ★ 深い葉の遠い語は RawWsAt。 -/
theorem RawWsAt_deep {u b : ℕ} (hub : u ≤ b) : RawWsAt [] 1 (fun _ => 0) b (dlws u) :=
  HdH.RawWsAt_of_OkWsAt (OkWsAt_deep hub)

/-! ## topCLT_WgL の一般化（PsLTL でなく FarCAt/RawWsAt を直接取る） -/

/-- ★★ topCLT_WgL の一般版: 文脈を PsLTL でなく FarCAt+RawWsAt+BwT で取る。
    深い葉の文脈（GoodChtX_deep 経由）にも使える。HeK.topCLT_WgL の写し。 -/
theorem topCLT_WgL_gen {u : ℕ} {ps : List (List (List UT) × List (Option TrioSeq))}
    (hB : BwT u (ps.map (wLT u))) (hFar : FarCAt [] 1 (fun _ => 0) u (psLT u ps))
    (hRaw : RawWsAt [] 1 (fun _ => 0) u (psLT u ps)) (m : ℕ) :
    (((0, u, 0) : ℕ × ℕ × ℕ) :: towWt u (psLT u ps) (u + 1) m) ∈ Wg (2 * u) := by
  have key : ∀ K : TrioSeq, WordsG u [K] →
      (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (ps.map (wLT u) ++ [K])) ∈ Wg (2 * u) := by
    intro K hK
    refine Wg_of_starOK ⟨?_, fun p hp => rword_ge 0 u _ p hp⟩
    have hB2 := BwT_append_words (Fr_CLT u ps) hB [K] hK u le_rfl
    rw [Nat.sub_self] at hB2
    simpa only [mlift_zero, List.map_id'] using hB2
  cases m with
  | zero =>
      have := key [] (WordsG_consT (v := u) (TF_nil u) (WordsG_nil u))
      rw [rword_append, rword_psLT] at this
      simpa [towWt, rword, rcol, shiftr01] using this
  | succ m =>
      have hG := towWt_GpT hFar (fun _ => 0) m [] 1 (fun _ => 0) u (fun a ha => by simp at ha) le_rfl
        hRaw (by simp) (by simp) (by simp) le_rfl (by simp)
        (by rw [HaG.reOff_zz]; simp [liftOff_zeroF])
      simp only [List.append_nil, relWst_zero, liftOff_zeroF] at hG
      have := key _ (WordsG_consT (v := u) (TF_tieG (u := u) (TF_nil u)
        (GF_of_GPF ⟨hG, Fr_towWt _ _ m _⟩)) (WordsG_nil u))
      rw [rword_append, rword_psLT] at this
      simpa [towWt, rword, rcol, shiftr01] using this

end HeV
end TRIO
