/-
**3 行・t = 2: 残り T2VAncStep を標準形全体の主張 HVAncStd にした（2026-10-24）。**

T2VAncStep は「t = 2 の行列 M のすべての展開 M[n]（n ≥ 2）で VAncStep」。M[n] は標準形（`Std.exp`）で、
順位を持つ（`rk_expand_t2`）。よって「順位を持つ標準形 N（SRO でない）のどの評価でも VAncStep」
（`HVAncStd`、行 1 の親子 m = P₁(c) で v(m) の成分は Ω_{v(c)} 以下か v(c) の成分以下）から出る。
測定: VAncStep は 11 集合で例外 0（desc「VAncStep（vanc1.py）」）。
-/
import Ytosk.V3RwClCopy
import Ytosk.V3ExpT2I
import Ytosk.V3TopC
import Ytosk.V3ResV2

namespace Ytosk

/-- **Residual (standard matrices): `VAncStep`** at every standard matrix with a ranking. -/
def HVAncStd : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → VAncStep N σ

theorem t2VAncStep_of_std (h : HVAncStd) :
    ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
      T2VAncStep M := by
  intro M ρ rk C hz h2 n hn σ hσ
  obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
  obtain ⟨rk', hR⟩ := rk_expand_t2 hX hJ hz h2 C.I.rank n (by omega)
  exact h _ σ rk' (Std.exp n C.std) (ne_SRO_of_rk hR) hσ hR

end Ytosk
