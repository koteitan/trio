/-
**WfExQ5 (2026-11-01): FrameClosed through the DQ copy (part of `CarryV3`, WfExQ2).**
Copy of `frameClosed_N_t1` (V3FrameClN) for `glueQ` with `DQ` values on `D`, through `trig_back_DQ` (WfExQ4).
The standard form of the new values comes from `Good3` of `M[n]`.  The leaf residual is `FrameClosedOmN` at the
new valuation (as for `glueZ`).
-/
import Ytosk.WfExQ4

namespace Ytosk.WfExQ5
open T Ytosk Ytosk.G Ytosk.WfExQ1 Ytosk.WfExQ2 Ytosk.WfExQ4 Ytosk.WfQrL1 Ytosk.WfQrL7

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

theorem frameClosed_N_t1Q (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {oq vq : Nat → T} (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hFC : FrameClosed M ρ)
    (hOmN : FrameClosedOmN M r L ρ (glueQ M (r + L) ρ (shiftV ρP L) oq vq))
    (hGN : ∀ c, c < r + L → DepX M (r + L) true c → isOT (oq c) = true)
    (hFCP : FrameClosed (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hDQ : ∀ c, c < r + L → DepX M (r + L) true c → ∃ η, DQ η false (ρ.o c) (oq c))
    (hlex : ρP.o r ≤ ρ.o (r + L)) (hox : ∃ t, ρ.o (r + L) = psi (succ t) z z) :
    FrameClosed (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) := by
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  intro i hi Lc c R hCL s y hc ht
  rcases Nat.lt_or_ge i (r + L) with h | h
  · obtain ⟨hCLM, hv, hLo⟩ := frameHead_ltQ hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hCP hOS h hCL
    rw [hv, hLo] at ht ⊢
    have hcCL : c ∈ CL M i := by rw [hCLM]; simp
    have hcM := mem_children (List.mem_filter.mp hcCL).1
    have hiM : i < M.length := by omega
    obtain ⟨s0, y0, h0⟩ := o_psi_form hC hcM.2
    have hc0 := hc
    by_cases hcx : c = r + L
    · rw [hcx] at hc hCLM hc0
      rw [glueQ_o_ge (le_refl _)] at hc
      have hc' : ρP.o r = psi s y z := by
        have : (shiftV ρP L).o (r + L) = ρP.o r := by show ρP.o (r + L - L) = _; rw [Nat.add_sub_cancel]
        rw [← this]; exact hc
      obtain ⟨t, hto⟩ := hox
      have hnt := trig_back_succ (by rw [← hto]; exact hlex) hc' ht
      exact hOmN i h Lc (r + L) R hCLM t hto hnt s y hc0 ht
    · have hcx' : c < r + L := by omega
      by_cases hd : DepX M (r + L) true c
      · rw [glueQ_o_dep hcx' hd] at hc
        obtain ⟨η, hDq⟩ := hDQ c hcx' hd
        rcases trig_back_DQ hDq rfl h0 hc ht with ⟨hss, hyy, htM⟩ | ⟨t, hst, hy0, hnt⟩
        · subst hss
          have hD := hFC i hiM Lc c R hCLM s y0 h0 htM
          have hc1 : isOT (psi s y z) = true := by rw [← hc]; exact hGN c hcx' hd
          have hc2 : isOT (psi s y0 z) = true := by rw [← h0]; exact hG.ot_o c hcM.2
          exact FrameDom.mono hD (H_mono hc1 hc2 hyy)
        · exact hOmN i h Lc c R hCLM t (by rw [h0, hst, hy0]) hnt s y hc0 ht
      · rw [glueQ_o_lt hcx' hd] at hc
        exact hFC i hiM Lc c R hCLM s y hc ht
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    obtain ⟨Lc', c', R', hsp, hv, hLo, hco⟩ :=
      frameHead_copyQ hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hCP hOS ha hCL
    rw [hv, hLo] at ht ⊢
    rw [hco] at hc
    exact hFCP (r + a) (by rw [hlP]; omega) Lc' c' R' hsp s y hc ht

end

/-- **The leaf residual of FrameClosed** at the new values. -/
def FCOmRes (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (oq vq : Nat → T),
    Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP → Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    Cons (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) →
    Good3 (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) →
    ExDQX M r L ρ n ρP oq vq →
    FrameClosedOmN M r L ρ (glueQ M (r + L) ρ (shiftV ρP L) oq vq)

/-- **FrameClosed is carried through the DQ copy**, given its leaf residual. -/
theorem expStepQR_fc {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hOm : FCOmRes M r L d0 ρ) :
    ExpStepQR PnV3 (fun N σ => FrameClosed N σ) (ExDQX M r L ρ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  obtain ⟨_, J⟩ := hPP
  have hxnb := hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
  have hlN := len_N (d0 := d0) hlen hn
  have hGo : ∀ c, c < r + L → DepX M (r + L) true c → isOT (oq c) = true := by
    intro c hc hd
    have := hGN.ot_o c (by omega)
    rwa [glueQ_o_dep hc hd] at this
  exact frameClosed_N_t1Q hlen hL hA hd0e hn hpath hx2 hxnb (S.z2 r) hiu hiux hCP hOS I.cons I.good I.fc
    (hOm n hn ρP oq vq hCP hGP hCN hGN hEx) hGo J.fc hEx.1.1 hEx.2 hox

end Ytosk.WfExQ5
