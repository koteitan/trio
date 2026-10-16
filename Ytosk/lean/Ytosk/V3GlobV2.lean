/-
**行列ごとの共通の残り（2026-10-16、top）。**

最後の列の枠の 10 欄（TakeFrameV2）と葉の条件（TP1LeafG・TP1WLeafG）は、どれも行列ごとの主張。
drop（M.take x）・t0（M[n]）・t1（各コピー）・t2（M[n]）が同じ種類の残りを持つので、
「どの標準形でも、Cons・Rk・Good3 を満たす評価で成り立つ」という共通の残りを 1 つずつ置く。

- `HFrameV2`: 枠の 10 欄。`HLeafV2`: 葉の 2 条件。
- 変換: `hTake_of_glob`（drop の HTakeV2）、`t0Frame_of_glob`・`t0Leaf_of_glob`（t0 の T0NRes）。

注意: 共通の形は前件が弱い（親の行列の Inv3V2 を使えない）ので、担当ごとの形より強い主張。
担当ごとの形（TakeResV2・T0NRes TakeFrameV2 など）で示してもよい。
-/
import Ytosk.V3MainV2

namespace Ytosk

open T

/-- **The last-column frame fields of every standard matrix.** -/
def HFrameV2 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → N ≠ [] → Cons N σ → Rk N rk → Good3 N σ → TakeFrameV2 N σ rk

/-- **The two leaf conditions of every standard matrix.** -/
def HLeafV2 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → N ≠ [] → Cons N σ → Rk N rk → Good3 N σ →
    TP1LeafG N σ ∧ TP1WLeafG N σ

/-- `HTakeV2` from the two shared residuals. -/
theorem hTake_of_glob (hF : HFrameV2) (hL : HLeafV2) : HTakeV2 := by
  intro M ρ rk hM hS hl I R
  have S := sInv_std hM hS
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have V := valInv_drop1 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.rank
    ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ R.drop
  have hM1 := std_take hM (M.length - 1) (by omega)
  have hS1 := ne_SRO_of_rk hRk1
  have hE1 := take_ne_nil_of (M := M) (j := M.length - 1) (by omega) (by omega)
  obtain ⟨h1, h2⟩ := hL _ _ rk hM1 hS1 hE1 hC1 hRk1 V.g
  exact ⟨hF _ _ rk hM1 hS1 hE1 hC1 hRk1 V.g, h1, h2⟩

theorem gexp_t0_facts {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (C : StepCtxV2 M ρ rk) (hlen : r + L + 1 = M.length) (hL : 0 < L) (hp : par M 0 (r + L) = some r)
    (he1 : entry M 1 (r + L) = 0) (n : Nat) (hn : 2 ≤ n) :
    Std (TRIO.gexp M r L 0 0 n) ∧ TRIO.gexp M r L 0 0 n ≠ [] := by
  refine ⟨std_gexp_t0C C.std (Inv3V2.toC C.S C.I) hlen hL hp he1 n, ?_⟩
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen (show 1 ≤ n by omega)
  apply List.ne_nil_of_length_pos
  have : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
  omega

theorem t0Frame_of_glob (hF : HFrameV2) : T0NRes TakeFrameV2 := by
  intro M ρ rk r L C hlen hL hp he1 n hn σ rkN hCN hRN hGN
  obtain ⟨hStd, hE⟩ := gexp_t0_facts C hlen hL hp he1 n hn
  exact hF _ σ rkN hStd (ne_SRO_of_rk hRN) hE hCN hRN hGN

theorem t0Leaf_of_glob (hL0 : HLeafV2) : T0NRes (fun N σ _ => TP1LeafG N σ ∧ TP1WLeafG N σ) := by
  intro M ρ rk r L C hlen hL hp he1 n hn σ rkN hCN hRN hGN
  obtain ⟨hStd, hE⟩ := gexp_t0_facts C hlen hL hp he1 n hn
  exact hL0 _ σ rkN hStd (ne_SRO_of_rk hRN) hE hCN hRN hGN

end Ytosk
