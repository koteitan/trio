/-
**最上位の兄弟の残りを CanonicalNeed に狭めた（2026-10-24）。**

`HSibColV2`（すべての標準形で SibColU）の使う側は qn の `QNUncRes` と C の `T2SeedCBig` の 2 か所だけで、
どちらも `CanonicalNeed`（t = 2 の行 2 の根の隣り合う子 a < b、a は x − 1 から上げられ topped、b は数える子、
で v(b) ≤ v(a)）から出る（V3SibConsumer の `qnUncRes_of_canonical`・`t2SeedCBig_of_canonical`）。
CanonicalNeed は SibColU の特別な場合（a と b は同じ列で、a は数えない）。
-/
import Ytosk.V3TopV2
import Ytosk.V3SibConsumer

namespace Ytosk

open T

/-- **Residual: `CanonicalNeed` of every standard matrix** (the special case of `SibColU` that the seeds use). -/
def HCanonV2 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ → SibConsumer.CanonicalNeed N σ

/-- **The seed residuals of t2** from `CanonicalNeed` (the form of `t2SeedPResR_of_sib`). -/
theorem t2SeedPResR_of_canon (hCan : HCanonV2) (h : T2SeedPResRCV2) : T2SeedPResRV2 := by
  intro M ρ rk C hz h2
  have H := h M ρ rk C hz h2
  have IW := Inv3W.ofV2 C.S C.I
  refine ⟨H.qr, fun r L hlen hr hq hux => ?_, fun r L q hlen hr hq hqr Lc hCL => ?_,
    fun r L q hlen hr hq hqr hncl => ⟨t2SeedCRes_of C.std C.ne IW hlen hr hq hqr (H.C r L q hlen hr hq hqr hncl), ?_⟩⟩
  · obtain ⟨hSt, hlhd⟩ := H.sv r L hlen hr hq hux
    exact ⟨sv_rw_of C.std C.ne IW C.toW hlen hr hq hux hSt, hlhd⟩
  · exact t2SeedQNResR_of2 C.std C.ne IW hlen hr hq hqr hCL
      ⟨SibConsumer.qnUncRes_of_canonical C.std C.ne IW hlen hr hq hqr hCL
          (hCan M ρ rk C.std C.ne C.I.cons C.I.rank C.I.good),
        H.qn r L q hlen hr hq hqr Lc hCL⟩
  · have hL : 0 < L := by
      have := par_lt M 0 (r + L) q hq
      have := par_lt M 2 (r + L) r hr; omega
    obtain ⟨I1, _⟩ := C.pre (r + L) (by omega) (by omega)
    exact SibConsumer.t2SeedCBig_of_canonical C.std C.ne IW C.toW hlen hr hq hqr hncl
      (t2SeedCRes_of C.std C.ne IW hlen hr hq hqr (H.C r L q hlen hr hq hqr hncl))
      (fun τ hτ hG => hCan _ τ rk (std_take C.std (r + L) (by omega)) (ne_SRO_of_rk I1.rank) hτ I1.rank hG)

end Ytosk
