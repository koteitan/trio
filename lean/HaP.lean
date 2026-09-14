/-
HaP.lean: 最上段の [W_tie] ++ (W_far)^n のあとに、中身が遠い字と零列 (1,0,0) の語（行 1501 の形）。

文脈 CLw v L := ∃ n, L = Lw n v。
- 中身なしの遠い語はこの文脈で良い（GTC、BwT_Lw (n+1)）。文脈はその語を足しても閉じる。
- よって GTC_flat（最後の零列の展開は直前の語の繰り返し）で、零列つきの語も良い。
-/
import GzJ
import HaN

namespace TRIO
namespace HaP

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF HaG HaI HaL HaN

def CLw (v : ℕ) (L : List TrioSeq) : Prop := ∃ n, L = Lw n v

theorem Lw_succ (n v : ℕ) : Lw n v ++ [fwTop v []] = Lw (n + 1) v := by
  simp [HaN.Lw, List.replicate_succ']

theorem GTC_far_Lw (v : ℕ) : GTC CLw v (fwTop v []) := by
  intro L hC _ _
  obtain ⟨n, rfl⟩ := hC
  rw [Lw_succ]
  exact BwT_Lw (n + 1) v

/-- ★ [W_tie] ++ (W_far)^n のあとに、遠い字と零列の語。 -/
theorem BwT_tieFarFlat (n v : ℕ) :
    BwT v (Lw n v ++ [fwTop v [] ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]]) := by
  have hG := GTC_flat (C := CLw) (v := v) (K := fwTop v []) (x := 1) le_rfl (Fr_fwTop v [])
    (fun y hy => Fr_fwTop v [] y hy) (GTC_far_Lw v)
    (fun L hL => by obtain ⟨m, rfl⟩ := hL; exact ⟨m + 1, Lw_succ m v⟩)
  exact hG (Lw n v) ⟨n, rfl⟩ (Fr_Lw n v) (BwT_Lw n v)

/-- ★ そのあとに TF の語の並び。 -/
theorem starOK_tieFarFlat (n : ℕ) {v : ℕ} {Ls : List TrioSeq} (hW : WordsG v Ls) :
    StarOK v (rword 0 v (Lw n v ++ [fwTop v [] ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]] ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hFr : ∀ X ∈ Lw n v ++ [fwTop v [] ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]], ∀ x ∈ X, 1 ≤ x.1 := by
    intro X hX
    rcases List.mem_append.mp hX with h | h
    · exact Fr_Lw n v X h
    · simp only [List.mem_singleton] at h
      subst h
      intro x hx
      rcases List.mem_append.mp hx with h1 | h1
      · exact Fr_fwTop v [] x h1
      · simp at h1; subst h1; simp
  have hB := BwT_append_words hFr (BwT_tieFarFlat n v) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end HaP
end TRIO
