/-
**RwClosed を運ぶ: t = 1（2026-10-17、lead）。**

`expT1Out_V2`（V3T1VSRAll）の運ぶ述語に `RwClosed` を足した形。各段は `expStep_rwClosed_t1S`（V3RwClT1）、
基底 M.take x は `rwClosed_take`（落とす補題の結論から）。
-/
import Ytosk.V3T1VSRAll
import Ytosk.V3RwClT1
import Ytosk.V3RwClDrop

namespace Ytosk

open T

/-- **`ExpT1OutR`** (`RwClosed` carried through the copies) from the shared frame and leaf residuals. -/
theorem expT1OutR_V2 (hF : HFrameV2) (hLf : HLeafV2) (hS1 : S1Std) : ExpT1OutR := by
  intro M ρ rk C hz h1t n hn
  have I := C.I
  have S := C.S
  obtain ⟨r, hr⟩ := parLast_of S.e00 S.r01 S.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h1t] at hr
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  have hx2 : entry M 2 (M.length - 1) = 0 := by
    unfold TRIO.srow at h1t
    by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
    · rw [if_pos ha] at h1t; cases h1t
    · show TRIO.entry M 2 (M.length - 1) = 0; omega
  have hexp := expand_eq_gexp_t1 M n hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hStdN : Std (expand M n) := Std.exp n C.std
  have hsd := C.R.seed
  have hdr := C.R.drop
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hI1 := (C.pre (r + L) (by omega) (by omega)).1
  rw [hL] at hexp hr hx2 hdr hsd
  simp only [Nat.add_sub_cancel_left] at hexp
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  have hPR : PassRootRes M r L ρ := passRootRes_of_S1 (sInvXJ_std C.std C.ne).1 (hS1 M C.std C.ne) hlen hr hx2
  have hstep : ExpStepT1 (fun N σ => (T1Core r ρ N σ ∧ (FrameMapT1 M ρ r L N σ ∧ VrDomQ M ρ r L N σ)) ∧
      RwClosed N σ) M r L (entry M 0 (r + L) - entry M 0 r) ρ :=
    expStep_and (expStep_and (expStep_core_vsmallF_pass_inv3V2 S I hlen hL0 hd0e hr hx2 hPR)
      (expStep_frameMapT1 S I.cons I.good I.rank hlen hL0 hd0e hr hx2))
      (expStep_rwClosed_t1S S I.cons I.good I.rank C.rw hlen hL0 hd0e hr hx2)
  have hdrop := drop_all hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hI1.cons hI1.rank
    I.vs hdr.vst I.fc I.fo hdr.argT
    (bump_drop hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hI1.cons hI1.rank
      I.kd I.td hdr.ab hdr.ws) hdr.ua
  have hbase : (T1Core r ρ (M.take (r + L)) (drop1 M (r + L) rk) ∧
      (FrameMapT1 M ρ r L (M.take (r + L)) (drop1 M (r + L) rk) ∧
        VrDomQ M ρ r L (M.take (r + L)) (drop1 M (r + L) rk))) ∧
      RwClosed (M.take (r + L)) (drop1 M (r + L) rk) :=
    ⟨⟨(t1_base S I hlen hr hdr hI1).1,
      frameMapT1_take S I.cons I.good hI1.cons hI1.rank hlen hx2 hdrop hdr.ua⟩,
      rwClosed_take hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hI1.cons hI1.rank hdrop C.rw⟩
  rw [hexp] at hStdN ⊢
  have hfin : ∃ ρN rkN, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) rkN ∧
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      ((T1Core r ρ (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
        (FrameMapT1 M ρ r L (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
          VrDomQ M ρ r L (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN)) ∧
        RwClosed (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) ∧
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN < root M ρ := by
    by_cases hq : par M 0 (r + L) = some r
    · exact qr_final4S hlen hL0 hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
        hr hx2 hq I.cons I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
        I.tp1w I.tplow I.auwl I.auw0 I.adw I.tp1 I.trigs I.tplon I.adn I.rootS I.rootP (hsd r hr hq)
        _ hbase hstep n hn
    · have hrM : r < M.length := by omega
      obtain ⟨br, hro⟩ := o_psi_sub I.cons hrM
      rw [sf_ot (I.good.ot_v r hrM)] at hro
      have hne : (drop1 M (r + L) rk).o r ≠ ρ.o r :=
        ne_of_lt (o_r_strict0 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2
          hr hx2 hq I.cons I.good hI1.cons hI1.rank hdrop)
      exact t1_main_vlocS hlen hL0 hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
        hr hx2 hq I.cons I.good I.rank I.vs I.fc I.fo I.tp1 I.tplos I.ads I.aus hdr.argT
        I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua hne rfl hro I.rootS I.rootP hI1.good
        _ hbase hstep n hn
  obtain ⟨ρN, rkN, hCN, hRN, hGN, ⟨⟨hcore, hmap, _⟩, hrwN⟩, hot, hlt⟩ := hfin
  have hNE : TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [len_N (d0 := entry M 0 (r + L) - entry M 0 r) hlen (show 2 ≤ n from hn)]
    omega
  have hNS := ne_SRO_of_rk hRN
  obtain ⟨hTP, hTPW⟩ := hLf _ ρN rkN hStdN hNS hNE hCN hRN hGN
  exact ⟨ρN, rkN, inv3V2_of_core hRN hcore (vsmallRAll_of_mapT1 hmap I.vra)
    (hF _ ρN rkN hStdN hNS hNE hCN hRN hGN) hTP hTPW, hot, hlt, hrwN⟩


theorem expT1OutR_V2_glob (hF : HFrameV2) (hLf : HLeafV2) : ExpT1OutR :=
  expT1OutR_V2 hF hLf s1Std

end Ytosk
