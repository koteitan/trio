/-
**3 行・t = 2・Bad2: 残り (c) `WfSrcC.SrcCRes` を列の値の上界に下げる（2026-10-31、WfSrcC2）。**

(c) で要るのは、DropFail の形（L = 1・P0 r = p・P0 p = i・P0 x = P1 x = r）で、吸収されない v(P1 i) の加数 s が
  s < B(v(r))、B(v) = ψ_v(Ω_{v+1})
であること（`WfSrcB.SrcC`）。

- Origins（`T2SrcOrigins.source_summand_origin`）: ψ(2) 以上の加数 s は、P1 i の行 1 の鎖の列 b の上げ先 k の bump 項
  s = bumpW(k) = ω^{1 + Σ_j ω^{Σ_{c ∈ ch(j)} o(c)}}（j は k の bump 子）。
- 項の補題: B(v) は 1 より大きく、和と ω 冪で閉じている（`add_lt_single`・`sumN_lt_single`・`omega_lt_bnd`）。
  よって k の bump 子 j の子 c がすべて o(c) < B(v(r)) なら bumpW(k) < B(v(r))（`bumpW_lt_bnd`）。

新しい残り `SrcC2Res`: その s の出どころ k について、k の bump 子の子 c の o(c) < B(v(r))。
橋 `srcC_of_c2 : SrcC2Res → WfSrcB.SrcC`、`t2AbsNSrcW_of_c2`（(a)(b) と合わせて `WfT2Src.T2AbsNSrcW`）。

測定（tmp/wf/WfSrcC2/notes.md）: DropFail の 1195 枠で、出どころはただ 1 つ（b = P1 i、k の bump 子は 1 個）、
その最初の子 c1 は r の写し（行 1・2 と上げ先が r と同じ、v(c1) = v(r)）で、c1 の数える子は行 1 が c1 より小さく
v が v(r) 以下。o(c) < B(v(r)) は k の bump 子のすべての子で成り立つ。
-/
import Ytosk.WfSrcB1
import Ytosk.WfSrcC1
import Ytosk.WfSrcABC
import Ytosk.V3T2SrcOrigins
import Ytosk.WfT2Exp

namespace Ytosk.WfSrcC2

open T WfT2Abs

set_option linter.unusedSectionVars false

/-! ## 項の補題: B(v) は和と ω 冪で閉じている -/

/-- Below a single term only the head matters. -/
theorem lt_single_rest {a b c c' V Y : T} (h : psi a b c < psi V Y z) : psi a b c' < psi V Y z :=
  psi_lt_psi_z_iff.mpr (psi_lt_psi_z_iff.mp h)

/-- **A single term is additively closed.** -/
theorem add_lt_single {V Y : T} : ∀ {x y : T}, x < psi V Y z → y < psi V Y z → add x y < psi V Y z
  | z, y, _, hy => by simpa [add] using hy
  | psi a b c, y, hx, hy => by
    cases y with
    | z => simpa [add] using hx
    | psi d e f =>
      simp only [add]
      split
      · exact hy
      · exact lt_single_rest hx

theorem foldl_lt_single {V Y : T} : ∀ (l : List T) (acc : T), isOT acc = true → acc < psi V Y z →
    (∀ t ∈ l, isOT t = true) → (∀ t ∈ l, t < psi V Y z) →
    l.foldl (fun a b => sf (add a b)) acc < psi V Y z
  | [], acc, _, h, _, _ => h
  | t :: l, acc, hacc, h, hot, hlt => by
    simp only [List.foldl_cons]
    have ht := hot t (List.mem_cons_self ..)
    rw [sf_ot (isOT_add hacc ht)]
    exact foldl_lt_single l _ (isOT_add hacc ht) (add_lt_single h (hlt t (List.mem_cons_self ..)))
      (fun u hu => hot u (List.mem_cons_of_mem _ hu)) (fun u hu => hlt u (List.mem_cons_of_mem _ hu))

/-- **A sum of standard terms below a single term is below it.** -/
theorem sumN_lt_single {V Y : T} {l : List T} (hot : ∀ t ∈ l, isOT t = true)
    (hlt : ∀ t ∈ l, t < psi V Y z) : sumN l < psi V Y z :=
  foldl_lt_single l z rfl (T.z_lt_psi _ _ _) hot hlt

theorem one_lt_bnd (V : T) : one < Bnd V :=
  lt_of_lt_of_le one_lt_E0 (WfT2Exp.eps_le_bnd V)

/-- **`B(V)` is closed under `ω^·`.** -/
theorem omega_lt_bnd {V x : T} (hV : isOT V = true) (hx : isOT x = true) (h : x < Bnd V) :
    omega x < Bnd V := by
  unfold omega
  split
  · rename_i hE
    have hE' : x < psi z (psi one z z) z := hE
    have hx1 : x < psi one z z :=
      lt_trans hE' (psi_lt_psi_z_iff.mpr (Or.inl (T.z_lt_psi _ _ _)))
    exact lt_of_lt_of_le (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hx1⟩)) (WfT2Exp.eps_le_bnd V)
  · cases x with
    | z => exact one_lt_bnd V
    | psi s b c =>
      simp only
      unfold Bnd at h ⊢
      rcases psi_lt_psi_z_iff.mp h with hs | ⟨rfl, hb⟩
      · exact psi_lt_psi_z_iff.mpr (Or.inl hs)
      · apply psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, ?_⟩)
        have hVs : s < add s one := by rw [add_one_eq_succ hV]; exact lt_succ_self s
        have hsplit : (split b (psi (add s one) z z)).1 = z := by
          cases b with
          | z => rfl
          | psi a' b' c' =>
            have hh : lt (psi a' b' z) (psi (add s one) z z) = true :=
              (show psi a' b' z < psi (add s one) z z from lt_single_rest hb)
            simp only [split, hh, if_true]
        rw [hsplit]
        simp only [add, sub]
        split
        · exact psi_lt_psi_z_iff.mpr (Or.inl hVs)
        · cases c with
          | z => exact T.z_lt_psi _ _ _
          | psi a' b' c' =>
            simp only [sub]
            have hhd : psi a' b' z ≤ psi s b z := ((isOT_psi_iff.mp hx).2.2.2.1)
            have ha' : a' ≤ s := by
              rcases lt_or_eq_of_le hhd with hl | hl
              · rcases psi_lt_psi_z_iff.mp hl with h1 | ⟨h1, _⟩
                · exact le_of_lt h1
                · exact le_of_eq h1
              · simp only [psi.injEq] at hl; exact le_of_eq hl.1
            exact psi_lt_psi_z_iff.mpr (Or.inl (lt_of_le_of_lt ha' hVs))

/-- **The bump term of `k` is below `B(V)`** when every child of a bump child of `k` has `o < B(V)`. -/
theorem bumpW_lt_bnd {M : Mat} {ρ : Valn} (hG : Good3 M ρ) {V : T} (hV : isOT V = true) {k : Nat}
    (h : ∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j, ρ.o c < Bnd V) :
    bumpW M ρ k < Bnd V := by
  have hot : ∀ t ∈ one :: (children M k).map (bumpTerm M ρ k), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm hG k j
  unfold bumpW
  apply omega_lt_bnd hV (isOT_sumN _ hot)
  apply sumN_lt_single hot
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact one_lt_bnd V
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    unfold bumpTerm
    split
    · rename_i hb
      have hcs : ∀ t ∈ (children M j).map ρ.o, isOT t = true := by
        intro t ht
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
        exact hG.ot_o c (mem_children hc).2
      apply omega_lt_bnd hV (isOT_sumN _ hcs)
      apply sumN_lt_single hcs
      intro t ht
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
      exact h j hj hb c hc
    · exact T.z_lt_psi _ _ _

/-! ## 新しい残りと橋 -/

/-- **Residual (c), at the origin of the summand**: in the `DropFail` shape (`WfSrcB.SrcC`'s premises), for a
non-absorbed summand `s` of `v(P1 i)` that is the bump term of the upgrade target `k` of a column `b` on the row-1
chain of `m = P1 i`, every child `c` of a bump child of `k` has `o(c) < B(v(r))`. -/
def SrcC2Res : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r, r + 2 = M.length → par M 2 (r + 1) = some r → par M 0 (r + 1) = some r → par M 1 (r + 1) = some r →
      ∀ τ, Cons (M.take (r + 1)) τ →
      ∀ p i, par M 0 r = some p → par M 0 p = some i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        WfT2Abs.DropFail M ρ τ (r + 1) i → WfT2Src.SrcFacts M ρ τ (r + 1) i →
        ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z → s < bumpW M ρ i →
          ¬ Lhd z s (bumpW M ρ i) →
          ∀ m b k, par M 1 i = some m → WfHUACDeep.Up1 M b m → upg M b = some k → s = bumpW M ρ k →
            ∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j, ρ.o c < Bnd (ρ.v r)

/-- **Bridge**: `WfSrcB.SrcC` from `SrcC2Res`. -/
theorem srcC_of_c2 (h : SrcC2Res) : WfSrcB.SrcC := by
  intro M ρ rk C hB2 hz hs r hlen hr h0 h1x τ hτ p i hp hpi h1 h2 hfail hfacts s hsm hs2 hlt hnl
  have hpr := par_lt M 0 r p hp
  have hip := par_lt M 0 p i hpi
  have hiN : i < M.length := by omega
  have hrN : r < M.length := by omega
  obtain ⟨m, hm⟩ := par1_exists C.S.e00 C.S.r01 (show 0 < entry M 1 i by omega)
  obtain ⟨b, k, hb, hu, hk⟩ :=
    T2SrcOrigins.source_summand_origin C.S C.I.cons C.I.good hiN hm hsm hs2
  have hk' : s = bumpW M ρ k := hk
  rw [hk']
  exact bumpW_lt_bnd C.I.good (C.I.good.ot_v r hrN)
    (h M ρ rk C hB2 hz hs r hlen hr h0 h1x τ hτ p i hp hpi h1 h2 hfail hfacts s hsm hs2 hlt hnl m b k hm hb hu
      hk')

/-- **Bridge**: `T2AbsNSrcW` from (a) `SrcARem2`, (b) `SrcBNonlost2`, (c) `SrcC2Res`. -/
theorem t2AbsNSrcW_of_c2 (hA : WfSrcA.SrcARem2) (hB : WfSrcB.SrcBNonlost2) (hC : SrcC2Res) :
    WfT2Src.T2AbsNSrcW :=
  WfSrcB.t2AbsNSrcW_of (WfSrcABC.srcA_of_rem2 hA) (WfSrcB.srcBNonlost_of_2 hB) (srcC_of_c2 hC)

end Ytosk.WfSrcC2
