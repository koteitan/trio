/-
**Inv3V2 の上の最上位の定理（2026-10-16、top）。**

旧 `Inv3`・`Inv3V` を使わずに、Desc3 と停止性を組み立てる。残りの仮定はどれも V3ResV2 の名前つきの Prop。

- 帰納法（`hInvV2_all`）: Std についての帰納法で、SRO 以外の空でない標準形に Inv3V2 を持つ評価がある。
  基底は `hBaseV2_holds`、接頭辞は `inv3V2_take` を 1 列ずつ（`pre_V2`）、n ≥ 2 は型ごとの仮定。
- 接頭辞の評価は `drop1 M j rk`、順位は M と同じ。評価を取り替えないので、Inv3V2 の欄の合同の補題は要らない。
- 下降（`desc_stepV2`）: 旧 `desc_step` を旧 Inv3 の偽でない欄（`Inv3C`、V3T0C）だけで動く形に写した。
  t = 1・n ≥ 2 は `qr_final_inv3V2`・`qn_final_inv3V2`、t = 2 は旧 `t2_drops` の写し `t2_dropsC`。
  t = 0・n ≥ 2 の `Res3.t0` は、`ExpT0V2` の評価から合同（Good3・rootS・rootP）で出す。
-/
import Ytosk.V3ResV2
import Ytosk.V3BaseInv2
import Ytosk.V3T0M
import Ytosk.V3T0Res
import Ytosk.V3Congr
import Ytosk.V3InvJ
import Ytosk.TwoRowZ
import Ytosk.V3TopC
import Ytosk.V3T0Inv2
import Ytosk.V3T2QUBad
import Ytosk.V3T2UpgAbs
import Ytosk.V3RwClDrop

namespace Ytosk

open T

/-! ## 接ぎ木の悪い形 `Bad2` の残り（2026-10-24） -/

/-- **Residual: the one-column drop of a `Bad2` matrix** keeps the invariant and does not increase the root (the
outputs of `HTakeV2` and of the descent to `M[1] = M.take (|M| − 1)`, from the drop lemma, which fails on
`Bad2`). -/
def TakeBadV2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Bad2 M → Inv3V2 M ρ rk →
    Inv3V2 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk ∧
      root (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) < root M ρ

/-- **Residual: the step of a `Bad2` matrix** for `n ≥ 2`: the invariant of `M[n]` and the descent of the root
(the outputs of the engines, whose drop and frame fields fail on `Bad2`; `n = 0, 1` follow from `TakeBadV2` and the
prefix chain). -/
def BadOutV2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Bad2 M → Inv3V2 M ρ rk →
    ∀ n, 2 ≤ n → (∃ ρN rkN, Inv3V2 (expand M n) ρN rkN) ∧ DropsAt M ρ n

/-! ## 下降: 旧 `t2_drops`・`desc_step` を `Inv3C` で（証明は同じ） -/

/-- **The part of `Res3` that the descent uses** (2026-10-17): the drop and the chain of the prefixes. The
`t = 0` fields (`t0`, the strong absorption `abS`) are replaced by the descent from t0's engine (`ExpT0OutV2`). -/
structure Res3D (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  drop : DropRes M (M.length - 1) ρ (drop1 M (M.length - 1) rk)
  chain : ∀ j, j + 1 < M.length → ¬ Bad2 (M.take (j + 1)) →
    DropRes (M.take (j + 1)) j (drop1 M (j + 1) rk) (drop1 M j rk)

/-- **Step 1 for `t = 2`**: from the invariants, the remaining hypotheses (`Res3`, `Res3T2`) and a
valuation of each `M[n]` (`n ≥ 2`), every expansion drops the root value. -/
theorem t2_dropsC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (I : Inv3C M ρ rk) (R : Res3D M ρ rk) (R2 : Res3T2 M ρ rk) (hX : SInvX M) (hJ : RowJ M)
    (hCh : ∀ j k, j ≤ k → k < M.length → root (M.take j) (drop1 M j rk) ≤ root (M.take k) (drop1 M k rk))
    (hPv : ∀ j, j < M.length → Cons (M.take j) (drop1 M j rk) ∧ Rk (M.take j) rk ∧
      isOT (root (M.take j) (drop1 M j rk)) = true)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hNval : ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
      ∃ σ rkN, Cons (expand M n) σ ∧ Rk (expand M n) rkN ∧ Good3 (expand M n) σ) :
    ∀ n, DropsAt M ρ n := by
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  rw [hL] at hr
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (by omega) hr
  have hxbr : col M (r + L) ≠ bump M r := fun h => by
    have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
  have hXu_of : upg M (r + L - 1) ≠ some (r + L) → ∀ i, upg M i ≠ some (r + L) := by
    intro hux i hu
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    have hi : i < M.length := by
      by_contra h
      exact (upg_e12 hu).1 (entry_out (by omega) 1)
    rcases hcase with h | ⟨_, h⟩
    · exact hux (by rw [show r + L - 1 = i by omega]; exact hu)
    · omega
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  have hrU : isUpg M r = false := by
    cases h : isUpg M r with
    | false => rfl
    | true =>
      exfalso
      unfold isUpg at h
      obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
      have := upg_target_e2 (of_decide_eq_true hk); omega
  have hrcl_of : par M 0 (r + L) = some r → upg M (r + L - 1) ≠ some (r + L) → CL M r ≠ [] := by
    intro hq hux hnil
    have hcnt : Counted M r (r + L) := ⟨hxbr, by rw [isUpg_x_false (hXu_of hux)]; simp⟩
    have hxin : r + L ∈ CL M r := by
      unfold CL; rw [List.mem_filter]
      exact ⟨mem_children_iff.mpr ⟨by omega, hq⟩, by simpa using hcnt⟩
    rw [hnil] at hxin; simp at hxin
  have hexp : ∀ n, expand M n = TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  -- the valuation of `M.take x`
  have hdr : DropRes M (r + L) ρ (drop1 M (r + L) rk) := by
    have := R.drop; rw [hL] at this; exact this
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank (hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat)
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rk) :=
    good3_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
      ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr
  have hdrop := drop_all (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs hdr.vst
    I.fc I.fo hdr.argT
    (bump_drop (by omega) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td hdr.ab hdr.ws)
    hdr.ua
  have hseed1 : UpgAbsX M (r + L) ρ → ∀ p, p < r + L → CL M p ≠ [] → (drop1 M (r + L) rk).o p ≠ ρ.o p →
      Lhd z ((drop1 M (r + L) rk).o p) (ρ.o p) :=
    fun hua p hp hcl hne => lhd_of_po I.cons I.good (by omega) hcl
      (PO.zero_of_strong (by omega) hua I.cons I.good (by omega) (hdrop p hp).1 (hdrop p hp).2) hne
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hrq : r ≤ q := (anc0_par hA (by omega) hq).le
  have hqx : q < r + L := par_lt M 0 _ q hq
  -- `n ≤ 1`: the drop to `M.take x`
  have hlast : isOT (root (M.take (r + L)) (drop1 M (r + L) rk)) = true ∧
      root (M.take (r + L)) (drop1 M (r + L) rk) < root M ρ := by
    by_cases hqr : q = r
    · rw [hqr] at hq
      have T := R2.qr r L hlen hr hq
      have hua' : UpgAbsX M (r + L) ρ ∨ T2UABad M (r + L) :=
        (T2UpgAbs.strong_or_old_target hlen I.cons I.good hdr.ua).imp_right
          (fun ⟨k, hk, hkx, hNB⟩ => ⟨⟨r, hq, hr⟩, ⟨k, hk, hkx⟩, hNB⟩)
      have hAbs := absWN_of_absC hdr.ab hC1 hq hrb
      cases hux : upg M (r + L - 1) with
      | none =>
        have T' := T.nn hux
        have hua := hua'.resolve_right (fun hb => by
          obtain ⟨_, ⟨k, hk, _⟩, _⟩ := hb; rw [hux] at hk; cases hk)
        obtain ⟨hdv, hos, hvsh⟩ := qr_shapes hlen hL0 hq (hXu_of (by rw [hux]; simp)) hxbr hrb
          I.r0p I.z2 I.sd I.z1 I.uat I.uab
        exact t2_qr_take hlen hL0 hq hxbr I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb (hrcl_of hq (by rw [hux]; simp)) hrU hux
          hdv hos hvsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hAbs
          (hseed1 hua r (by omega) (hrcl_of hq (by rw [hux]; simp)) T'.seed1)
      | some k =>
        have hkl := upg_lt (by omega) hux
        by_cases hkx : k = r + L
        · rw [hkx] at hux
          have T' := T.sv hux
          have hua := hua'.resolve_right (fun hb => by
            obtain ⟨_, ⟨k', hk', hk'x⟩, _⟩ := hb; rw [hux] at hk'; cases hk'; omega)
          obtain ⟨Sp1, _, Sdv, Sos, Svsh⟩ := sv_shapes hlen hL0 hq hux (rx_of_sv hlen I.z2 I.z1 hr hux) hrb he2r
            I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be
          exact t2_sv_take hlen hL0 hq hux I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb (rcl_sv hlen hq hr hux I.z2 I.z1 I.r0p I.uat I.be he2r) hrU
            Sp1 Sdv Sos Svsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hAbs
            (hseed1 hua r (by omega) (rcl_sv hlen hq hr hux I.z2 I.z1 I.r0p I.uat I.be he2r) T'.seed1)
        · have hk : k < r + L := by omega
          have T' := T.up k hux hk
          obtain ⟨hp1, hdv, hos, hvsh⟩ :
              (∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SV r (r + L - 1)) false m) ∧
              (∀ c, c < r + L → c ≠ r → DepS M (SV r (r + L - 1)) false c → CL M c = []) ∧
              OSh M (SV r (r + L - 1)) (r + L) ∧ VSh M (SV r (r + L - 1)) (r + L) := by
            by_cases hrx : r = r + L - 1
            · exact qu_shapes hlen hL0 hq hrx (hXu_of (by rw [hux]; intro h; cases h; omega)) hxbr hrb he2r
                I.r0p I.z2 I.sd I.z1 I.uat I.uab
            · obtain ⟨h1, _, h3, h4, h5⟩ := sv_shapes hlen hL0 hq hux hrx hrb he2r I.r0p I.z2 I.sd I.z1 I.uat
                I.uab I.r12 I.be
              exact ⟨h1, fun c hc _ hd => h3 c hc hd, h4, h5⟩
          by_cases hbad : T2UABad M (r + L)
          · -- the strong absorption may fail: the seed moves to the parent of `x − 1`
            obtain ⟨_, _, hbp⟩ := hbad
            have hux' : upg M (r + L - 1) = some k := hux
            have he1j : entry M 1 (r + L - 1) ≠ 0 := (upg_e12 hux').1
            have he0j : entry M 0 (r + L - 1) ≠ 0 := fun h => he1j (I.r01 _ h)
            have hj0 : 0 < r + L - 1 := by
              rcases Nat.eq_zero_or_pos (r + L - 1) with h | h
              · rw [h] at he0j; exact absurd I.e00 he0j
              · exact h
            obtain ⟨pr, hpr⟩ := par0_some_of (M := M) hj0 (by rw [I.e00]; omega)
            exact t2_qu_take_bad hlen hL0 hq hxbr I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb
              (hrcl_of hq (by rw [hux]; intro h; cases h; omega)) hrU hux hk
              (I.uat _ k hux (by omega)) hp1 hdv
              (fun hrx => (sv_shapes hlen hL0 hq hux hrx hrb he2r I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be).2.1)
              hos hvsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hAbs
              (fun h => lhd_of_po I.cons I.good (by omega) (hrcl_of hq (by rw [hux]; intro h'; cases h'; omega))
                (PO.zero_of_ne (by omega) I.cons I.good (by omega) (hdrop r (by omega)).1 (hdrop r (by omega)).2)
                (T'.seed1 h))
              hpr (fun g hg => hbp pr g (by rw [show r + L - 1 = r + L - 1 from rfl]; exact hpr) hg)
              (fun hrx => by
                have hcnt : Counted M r (r + L) :=
                  ⟨hxbr, by rw [isUpg_x_false (hXu_of (by rw [hux]; intro h; cases h; omega))]; simp⟩
                unfold CL; rw [List.mem_filter]
                exact ⟨mem_children_iff.mpr ⟨by omega, hq⟩, by simpa using hcnt⟩)
              I.r0p I.sd I.z1 I.uab hdrop
          have hua := hua'.resolve_right hbad
          exact t2_qu_take hlen hL0 hq hxbr I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb (hrcl_of hq (by rw [hux]; intro h; cases h; omega)) hrU hux hk
            (I.uat _ k hux (by omega)) hp1 hdv
            (fun hrx => (sv_shapes hlen hL0 hq hux hrx hrb he2r I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be).2.1)
            hos hvsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd
            hua hAbs
            (fun h => hseed1 hua r (by omega) (hrcl_of hq (by rw [hux]; intro h'; cases h'; omega)) (T'.seed1 h))
    · obtain ⟨pq, hpq⟩ := par0_of_anc (anc0_par hA (by omega) hq) (fun h => hqr h.symm)
      have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
      have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
      have T := R2.qn r L (q - r) pq hlen hr hq' (by omega) hpq'
      obtain ⟨Txb, Tqb, Te2pq, Tclq, Tclpq⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
      obtain ⟨Tp1, TqL, Tdv, Tos, Tvsh⟩ := qn_shapes hlen hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd I.z1
        I.uat I.uab I.r12 hpq' Tqb
      have hAbs := absWN_of_absC hdr.ab hC1 hq' (fun i h => by rw [hpq'] at h; cases h; exact Tqb)
      have hs1 := T2UpgAbs.strong_seed_of_drop hlen I.cons I.good
        (by have := par_lt M 0 _ _ hpq; omega) (by have := par_lt M 0 _ _ hpq; omega) Tclpq
        (hdrop pq (by have := par_lt M 0 _ _ hpq; omega)) T.seed1
      cases hux : upg M (r + L - 1) with
      | none =>
        exact t2_qn_take hlen hL0 hA hq' (by omega) Txb I.be I.z2 I.uat I.r12 I.r01 I.e00 hpq' Tqb Te2pq
          Tclq Tclpq hux Tp1 TqL Tdv Tos Tvsh I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd
          hAbs hs1
      | some k =>
        obtain ⟨Up1, Up1a, Uqsh, Udv, Uos, Uvsh⟩ := qnu_shapes hlen hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd
          I.z1 I.uat I.uab I.r12 hpq' Tqb hux
        exact T2UpgAbs.qnu_take_of_drop hlen hL0 hA hq' (by omega) Txb I.be
          I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.r01 I.e00
          hpq' Tqb Te2pq Tclq Tclpq hux Up1 Up1a Uqsh Udv Uos Uvsh
          I.cons I.good I.rank hC1 hG1 hRk1 I.fc I.vs I.td I.kd hdr.ua hdrop hAbs hs1
  -- `n ≥ 2`
  have hbig : ∀ n, 2 ≤ n → ∀ σ rkN,
      Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n) σ) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ <
        root M ρ := by
    intro n hn σ rkN hCN hRN hGN
    have hT : (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n).take
        (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
    have hUN : UAT (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) := by
      rw [← hexp n]; exact (sInvX_expand hX n).toSInv.uat
    have hlN := TRIO.gexp_length (M := M) (j0 := r) (Lb := L) (d0 := entry M 0 (r + L) - entry M 0 r)
      (d1 := entry M 1 (r + L) - entry M 1 r) (n := n) hlen
    have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
    have hcolN : ∀ d, d < r + L →
        col (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) d = col M d :=
      fun d hd => col_gexp_pre hlen (by omega) hd
    have hbN : ∀ c, c < r + L →
        bump (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) c = bump M c :=
      fun c hc => by unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hc, entry_gexp_pre hlen (by omega) 1 hc]
    by_cases hqr : q = r
    · rw [hqr] at hq
      have T := R2.qr r L hlen hr hq
      have hAbs := R2.absN r L hlen hr n σ hn hCN hGN
      by_cases hux : upg M (r + L - 1) = some (r + L)
      · have T' := T.sv hux
        obtain ⟨Sp1, _, Sdv, Sos, Svsh⟩ := sv_shapes hlen hL0 hq hux (rx_of_sv hlen I.z2 I.z1 hr hux) hrb he2r
          I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be
        have hseed := T'.big n σ hn hCN
        have hIUt : ∀ c, c < r + L → topped M c = true →
            isUpg (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) c =
              isUpg M c := by
          intro c hc htM
          have hcr : c ≠ r := by
            intro hcr'
            rw [hcr'] at htM
            have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
            have hsplit := children_split_x hlen hxr
            unfold topped at htM; rw [hsplit] at htM; simp at htM
            exact hxbr htM
          have hch := children_N2 (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hq hd0e (by omega) hn hc
          apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
          rw [topped_eq_of hch (fun d hd => hcolN d (by
            have := (mem_children hd).2
            by_contra h'
            have hdx : d = r + L := by omega
            have := (mem_children_iff.mp hd).2; rw [hdx, hq] at this; exact hcr (Option.some.inj this).symm))
            (hbN c hc)]
          exact htM
        exact t2_sv_main hlen hL0 hq hd0e hn hux I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hrb (rcl_sv hlen hq hr hux I.z2 I.z1 I.r0p I.uat I.be he2r) hIUt
          Sp1 Sdv Sos Svsh I.cons I.good I.rank hCN hGN hRN I.fc I.vs I.td I.kd hAbs hseed
      · have hseed := T.big hux n σ hn hCN
        have hIU : ∀ c, c < r + L → topped M c = true →
            isUpg (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) c =
              isUpg M c := by
          intro c hc htM
          apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
          rw [topped_N2 (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hq hd0e hn (hXu_of hux) hxbr he2r hc]
          exact htM
        have hxcN : Counted (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
            (entry M 1 (r + L) - entry M 1 r) n) r (r + L) := by
          have hx2 := (entry_xprime (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hq hd0e (by omega) hn).1
          refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
          · have := e2_of_col (show col _ (r + L) = (_, _, 1) from h); omega
          · unfold isUpg at hiu
            obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
            have := upg_target_e2 (of_decide_eq_true hk0); omega
        exact t2_qr_main hlen hL0 hq hd0e hn (hXu_of hux) hxbr hrb he2r hIU I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12
          I.be I.r01 I.e00 I.cons I.good I.rank hCN hGN hRN I.fc I.vs I.td I.kd hAbs hxcN hseed
    · obtain ⟨pq, hpq⟩ := par0_of_anc (anc0_par hA (by omega) hq) (fun h => hqr h.symm)
      have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
      have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
      have T := R2.qn r L (q - r) pq hlen hr hq' (by omega) hpq'
      obtain ⟨Txb, Tqb, Te2pq, Tclq, Tclpq⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
      obtain ⟨Tp1, TqL, Tdv, Tos, Tvsh⟩ := qn_shapes hlen hA hq' (by omega) Txb I.be I.r0p I.z2 I.sd I.z1
        I.uat I.uab I.r12 hpq' Tqb
      have hAbs := R2.absN r L hlen hr n σ hn hCN hGN
      have hseed := T.big n σ hn hCN
      have hIUt : ∀ c, c < r + L → c ≠ r + (q - r) → topped M c = true →
          isUpg (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) c =
            isUpg M c := by
        intro c hc hcq htM
        have hch := children_N2Q (d1 := entry M 1 (r + L) - entry M 1 r) hlen hL0 hA hq' (by omega) hd0e
          (by omega) hn hc
        apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
        rw [topped_eq_of hch (fun d hd => hcolN d (by
          have := (mem_children hd).2
          by_contra h'
          have hdx : d = r + L := by omega
          have := (mem_children_iff.mp hd).2; rw [hdx, hq'] at this; exact hcq (Option.some.inj this).symm))
          (hbN c hc)]
        exact htM
      exact t2_qn_main hlen hL0 hA hq' (by omega) hd0e hn Txb I.be I.z2 I.uat I.r12 I.r01 I.e00 he2r hpq'
        Tqb Te2pq Tclq Tclpq hIUt Tp1 TqL Tdv Tos Tvsh I.cons I.good I.rank hCN hGN hRN
        I.fc I.vs I.td I.kd hAbs hseed
  intro n
  rcases n with _ | _ | n
  · by_cases hBp : ∃ j, j + 1 < M.length ∧ Bad2 (M.take (j + 1))
    · apply dropsAt_of (by rw [hexp 0, gexp_zero_gen])
      obtain ⟨hc, hrk, hot⟩ := hPv r (by omega)
      exact ⟨_, _, hc, hrk, hot, lt_of_le_of_lt (hCh r (r + L) (by omega) (by omega)) hlast.2⟩
    apply dropsAt_of (by rw [hexp 0, gexp_zero_gen])
    exact drop_n0_gen hlen hL0 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
      ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr
      (fun j _ hj => R.chain j (by omega) (fun hb => hBp ⟨j, by omega, hb⟩)) hlast.2
  · apply dropsAt_of (by rw [hexp 1, gexp_one_gen hlen])
    exact ⟨_, _, hC1, hRk1, hlast⟩
  · have hne := gexp_ne_SRO (n := n + 2) hlen hL0 hA hd0e
      (show entry M 1 (r + L) = entry M 1 r + (entry M 1 (r + L) - entry M 1 r) by omega) he2r h1lt
      (by omega)
    have hnil : TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n + 2)
        ≠ [] := by
      intro h
      have hl := TRIO.gexp_length (M := M) (j0 := r) (Lb := L)
        (d0 := entry M 0 (r + L) - entry M 0 r) (d1 := entry M 1 (r + L) - entry M 1 r) (n := n + 2) hlen
      rw [h] at hl
      have : L ≤ (n + 2) * L := Nat.le_mul_of_pos_left L (by omega)
      simp at hl; omega
    obtain ⟨σ, rkN, hCN, hRN, hGN⟩ := hNval (n + 2) (by omega) (by rw [hexp]; exact hne)
      (by rw [hexp]; exact hnil)
    rw [hexp] at hCN hRN hGN
    apply dropsAt_of (hexp (n + 2))
    exact ⟨σ, rkN, hCN, hRN, hbig (n + 2) (by omega) σ rkN hCN hRN hGN⟩

theorem desc_stepV2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hne : M ≠ [])
    (I : Inv3C M ρ rk) (R : Res3D M ρ rk)
    (hCh : ∀ j k, j ≤ k → k < M.length → root (M.take j) (drop1 M j rk) ≤ root (M.take k) (drop1 M k rk))
    (hPv : ∀ j, j < M.length → Cons (M.take j) (drop1 M j rk) ∧ Rk (M.take j) rk ∧
      isOT (root (M.take j) (drop1 M j rk)) = true)
    (hT0 : col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 → ∀ n, 2 ≤ n → DropsAt M ρ n)
    (hT1 : col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → ∀ n, 2 ≤ n → DropsAt M ρ n)
    (hT2 : col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n)
    (n : Nat) : DropsAt M ρ n := by
  have hpos : 0 < M.length := List.length_pos_of_ne_nil hne
  by_cases hz : col M (M.length - 1) = (0, 0, 0)
  · exact zero_last_desc hne I.cons I.good I.rank hz n
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hlen2 : 2 ≤ M.length := by
    by_contra h
    have hx0 : M.length - 1 = 0 := by omega
    apply hz
    rw [hx0]
    have e0 := I.e00
    have e1 := I.r01 0 e0
    have e2 := I.r12 0 e1
    exact (col_zero_iff M 0).mpr ⟨e0, e1, e2⟩
  have hsrow : TRIO.srow M (M.length - 1) = 0 ∨ TRIO.srow M (M.length - 1) = 1 ∨
      TRIO.srow M (M.length - 1) = 2 := by
    unfold TRIO.srow; split_ifs <;> simp
  rcases hsrow with h0 | h1t | h2
  · -- `t = 0`
    have he1 : entry M 1 (M.length - 1) = 0 := by
      unfold TRIO.srow at h0
      by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
      · rw [if_pos ha] at h0; cases h0
      · rw [if_neg ha] at h0
        by_cases hb : 0 < TRIO.entry M 1 (M.length - 1)
        · rw [if_pos hb] at h0; cases h0
        · show TRIO.entry M 1 (M.length - 1) = 0; omega
    have hx2 : entry M 2 (M.length - 1) = 0 := I.r12 _ he1
    rw [h0] at hr
    have hexp := expand_eq_gexp M n hlen2 hzT (by rw [h0]; exact hr)
    rw [h0] at hexp
    simp only [show ¬ (0 < 0) from by omega, show ¬ (1 < 0) from by omega, if_false] at hexp
    have hdr := R.drop
    have hch := R.chain
    have hrx : r < M.length - 1 := par_lt M 0 _ r hr
    obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
    rw [hL] at hexp hr he1 hx2 hdr
    simp only [Nat.add_sub_cancel_left] at hexp
    have hlen : r + L + 1 = M.length := by omega
    have hL0 : 0 < L := by omega
    have hnx : ¬ DepX M (r + L) false (r + L) := by
      intro h
      cases h with
      | vpar h1 _ _ => exact h1 he1
      | vupg h1 _ _ _ => exact h1 he1
      | vbump h1 _ _ _ _ _ => exact h1 he1
    rcases n with _ | _ | n
    · by_cases hBp : ∃ j, j + 1 < M.length ∧ Bad2 (M.take (j + 1))
      · have hd1 := drop_n1 (d0 := 0) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hL0 hx2 hr hnx I.cons
          I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
        obtain ⟨ρ1, rk1, hc1, hrk1, _, hlt1⟩ := hd1
        rw [gexp_one_gen hlen] at hc1 hrk1 hlt1
        have he : root (M.take (r + L)) ρ1 = root (M.take (r + L)) (drop1 M (r + L) rk) :=
          val_unique ⟨ρ1, rk1, hc1, hrk1, rfl⟩
            ⟨_, rk, (hPv (r + L) (by omega)).1, (hPv (r + L) (by omega)).2.1, rfl⟩
        apply dropsAt_of hexp
        rw [gexp_zero_gen]
        obtain ⟨hc, hrk, hot⟩ := hPv r (by omega)
        exact ⟨_, _, hc, hrk, hot, lt_of_le_of_lt (hCh r (r + L) (by omega) (by omega)) (he ▸ hlt1)⟩
      apply dropsAt_of hexp
      exact drop_n0r (d0 := 0) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hL0 hx2 hr hnx I.cons
        I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
        (fun j _ hj => hch j (by omega) (fun hb => hBp ⟨j, by omega, hb⟩))
    · apply dropsAt_of hexp
      exact drop_n1 (d0 := 0) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hL0 hx2 hr hnx I.cons
        I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
    · exact hT0 hz h0 (n + 2) (by omega)
  · -- `t = 1`
    have hx2 : entry M 2 (M.length - 1) = 0 := by
      unfold TRIO.srow at h1t
      by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
      · rw [if_pos ha] at h1t; cases h1t
      · show TRIO.entry M 2 (M.length - 1) = 0; omega
    rw [h1t] at hr
    have hexp := expand_eq_gexp_t1 M n hlen2 hzT (by rw [h1t]; exact hr) h1t
    have hdr := R.drop
    have hch := R.chain
    have hrx : r < M.length - 1 := par_lt M 1 _ r hr
    obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
    rw [hL] at hexp hr hx2 hdr
    simp only [Nat.add_sub_cancel_left] at hexp
    have hlen : r + L + 1 = M.length := by omega
    have hL0 : 0 < L := by omega
    have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
    have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
      have := anc0_e0_lt hA (by omega); omega
    obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
    have hnx : ¬ DepX M (r + L) false (r + L) := by
      intro h
      cases h with
      | vpar _ hp hdm =>
        rw [hr] at hp; cases hp
        by_cases hqr : q = r
        · subst hqr
          exact (qr_dep hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq).2.1 hdm
        · exact v_r_not_chg hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hA (by omega)
            (fun h' => hqr (Option.some.inj (hq.symm.trans h')))
            (hpath_of_par1 hr hA (by omega)) (depX_chgX hdm)
      | vupg _ _ hu _ => have := upg_succ_lt hu; omega
      | vbump _ h2 _ _ _ _ => exact h2 hx2
    rcases n with _ | _ | n
    · by_cases hBp : ∃ j, j + 1 < M.length ∧ Bad2 (M.take (j + 1))
      · have hd1 := drop_n1 (d0 := entry M 0 (r + L) - entry M 0 r) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12
          I.be I.r01 I.e00 hL0 hx2 hq hnx I.cons
          I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
        obtain ⟨ρ1, rk1, hc1, hrk1, _, hlt1⟩ := hd1
        rw [gexp_one_gen hlen] at hc1 hrk1 hlt1
        have he : root (M.take (r + L)) ρ1 = root (M.take (r + L)) (drop1 M (r + L) rk) :=
          val_unique ⟨ρ1, rk1, hc1, hrk1, rfl⟩
            ⟨_, rk, (hPv (r + L) (by omega)).1, (hPv (r + L) (by omega)).2.1, rfl⟩
        apply dropsAt_of hexp
        rw [gexp_zero_gen]
        obtain ⟨hc, hrk, hot⟩ := hPv r (by omega)
        exact ⟨_, _, hc, hrk, hot, lt_of_le_of_lt (hCh r (r + L) (by omega) (by omega)) (he ▸ hlt1)⟩
      apply dropsAt_of hexp
      exact drop_n0r (d0 := entry M 0 (r + L) - entry M 0 r) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12
        I.be I.r01 I.e00 hL0 hx2 hq hnx I.cons
        I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
        (fun j _ hj => hch j (by omega) (fun hb => hBp ⟨j, by omega, hb⟩))
    · apply dropsAt_of hexp
      exact drop_n1 (d0 := entry M 0 (r + L) - entry M 0 r) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12
        I.be I.r01 I.e00 hL0 hx2 hq hnx I.cons
        I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
    · exact hT1 hz h1t (n + 2) (by omega)
  · exact hT2 hz h2 n

/-! ## 行列ごとの残りから Res3A、1 列落とし、接頭辞 -/

theorem res3AW_of_V2 (hD : HDropV2) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (hE : M ≠ []) (hNB : ¬ Bad2 M) (I : Inv3V2 M ρ rk) :
    Res3AW M ρ rk := by
  have S := sInv_std hM hS
  have hl : 1 ≤ M.length := List.length_pos_of_ne_nil hE
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) hl S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  exact ⟨DropRes.ofH hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons
    ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ (hD M ρ rk hM hS hE hNB I) (cons_of_rk hRk1) hRk1⟩

/-- **`RootP` of `M.take x` when `x` is a root column** (the residual `hRP0` of `inv3V2_take`). -/
theorem rootP0_take {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V2 M ρ rk)
    (hl : 2 ≤ M.length) (h0 : entry M 0 (M.length - 1) = 0) :
    RootP (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have h1 := S.r01 _ h0
  have h2 := S.r12 _ h1
  have hk : col M (M.length - 1) = (0, 0, 0) := (col_zero_iff M _).mpr ⟨h0, h1, h2⟩
  exact rootP_take_root hx hk I.cons (cons_of_rk hRk1) hRk1 I.rootP

/-- **The one-column drop** with the drop valuation and the same ranking. -/
theorem last_V2 (hD : HDropV2) (hT : HTakeV2) (hTB : TakeBadV2) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (hl : 2 ≤ M.length) (I : Inv3V2 M ρ rk) :
    Inv3V2 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk := by
  have hE : M ≠ [] := by intro h; rw [h] at hl; simp at hl
  by_cases hB : Bad2 M
  · exact (hTB M ρ rk hM hS hl hB I).1
  have R := res3AW_of_V2 hD hM hS hE hB I
  have T := hT M ρ rk hM hS hl I R
  exact inv3V2_take (sInv_std hM hS) I hl R.drop T.frame T.leaf T.leafW
    (rootP0_take (sInv_std hM hS) I hl)

theorem take_ne_nil_of {M : Mat} {j : Nat} (hj : 1 ≤ j) (hjl : j ≤ M.length) : M.take j ≠ [] := by
  exact List.ne_nil_of_length_pos (by rw [List.length_take]; omega)

/-- **Every prefix** `M.take j` (`1 ≤ j < |M|`) has the invariant with `drop1 M j rk`. -/
theorem pre_V2 (hD : HDropV2) (hT : HTakeV2) (hTB : TakeBadV2) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3V2 M ρ rk) :
    ∀ j, 1 ≤ j → j < M.length →
      Inv3V2 (M.take j) (drop1 M j rk) rk ∧ (¬ Bad2 (M.take j) → Res3AW (M.take j) (drop1 M j rk) rk) := by
  have key : ∀ m j, 1 ≤ j → j + 1 + m = M.length → Inv3V2 (M.take j) (drop1 M j rk) rk := by
    intro m
    induction m with
    | zero =>
      intro j hj hm
      have := last_V2 hD hT hTB hM hS (by omega) I
      rwa [show M.length - 1 = j by omega] at this
    | succ m ih =>
      intro j hj hm
      have I1 := ih (j + 1) (by omega) (by omega)
      have hl1 : (M.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
      have hM1 : Std (M.take (j + 1)) := std_take hM (j + 1) (by omega)
      have hS1 : M.take (j + 1) ≠ SRO := ne_SRO_of_rk I1.rank
      have := last_V2 hD hT hTB hM1 hS1 (by omega) I1
      rw [hl1, show j + 1 - 1 = j by omega, take_take_succ, drop1_take_succ] at this
      exact this
  intro j hj hjl
  have Ij := key (M.length - 1 - j) j hj (by omega)
  exact ⟨Ij, fun hNBj => res3AW_of_V2 hD (std_take hM j (by omega)) (ne_SRO_of_rk Ij.rank)
    (take_ne_nil_of hj (by omega)) hNBj Ij⟩

theorem ctx_V2 (hD : HDropV2) (hT : HTakeV2) (hTB : TakeBadV2) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (hE : M ≠ []) (hNB : ¬ Bad2 M) (I : Inv3V2 M ρ rk) :
    StepCtxV2 M ρ rk :=
  ⟨hM, hS, sInv_std hM hS, I, res3AW_of_V2 hD hM hS hE hNB I, hNB, pre_V2 hD hT hTB hM hS I⟩

/-- **`RwClosed` passes to the last drop** `M.take (|M| − 1)` with `drop1` (the drop lemma from `Res3AW.drop`). -/
theorem rw_last_V2 (hD : HDropV2) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (hl : 2 ≤ M.length) (hNB : ¬ Bad2 M) (I : Inv3V2 M ρ rk)
    (hRw : RwClosed M ρ) : RwClosed (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) := by
  have hE : M ≠ [] := by intro h; rw [h] at hl; simp at hl
  have S := sInv_std hM hS
  have R := res3AW_of_V2 hD hM hS hE hNB I
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdr := R.drop
  have hdrop := drop_all hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.vs hdr.vst
    I.fc I.fo hdr.argT
    (bump_drop hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.kd I.td hdr.ab hdr.ws) hdr.ua
  exact rwClosed_take hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 hdrop hRw

/-- **`RwClosed` of every prefix** `M.take j` (`1 ≤ j < |M|`) with `drop1 M j rk`. -/
theorem rw_pre_V2 (hD : HDropV2) (hT : HTakeV2) (hTB : TakeBadV2) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3V2 M ρ rk) (hRw : RwClosed M ρ)
    (hNBp : ∀ j, 2 ≤ j → j ≤ M.length → ¬ Bad2 (M.take j)) :
    ∀ j, 1 ≤ j → j < M.length → RwClosed (M.take j) (drop1 M j rk) := by
  have key : ∀ m j, 1 ≤ j → j + 1 + m = M.length → RwClosed (M.take j) (drop1 M j rk) := by
    intro m
    induction m with
    | zero =>
      intro j hj hm
      have := rw_last_V2 hD hM hS (by omega) (by simpa using hNBp M.length (by omega) le_rfl) I hRw
      rwa [show M.length - 1 = j by omega] at this
    | succ m ih =>
      intro j hj hm
      have R1 := ih (j + 1) (by omega) (by omega)
      have I1 := (pre_V2 hD hT hTB hM hS I (j + 1) (by omega) (by omega)).1
      have hl1 : (M.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
      have hM1 : Std (M.take (j + 1)) := std_take hM (j + 1) (by omega)
      have hS1 : M.take (j + 1) ≠ SRO := ne_SRO_of_rk I1.rank
      have := rw_last_V2 hD hM1 hS1 (by omega) (hNBp (j + 1) (by omega) (by omega)) I1 R1
      rw [hl1, show j + 1 - 1 = j by omega, take_take_succ, drop1_take_succ] at this
      exact this
  intro j hj hjl
  exact key (M.length - 1 - j) j hj (by omega)

/-- **The base `SRO[n]` with `RwClosed`.** -/
theorem hBaseR (n : Nat) : ∃ ρ rk, Inv3V2 (expand SRO n) ρ rk ∧ RwClosed (expand SRO n) ρ := by
  rw [expand_SRO_eq]
  have hF : BaseFit (1 + 3 * n) one := Or.inl ⟨by omega, rfl⟩
  obtain ⟨ρ, rk, I, _⟩ := hBaseV2_holds n
  rw [expand_SRO_eq] at I
  refine ⟨bval (1 + 3 * n) one, brk (1 + 3 * n), ?_, base_rwClosed hF⟩
  exact ⟨bval_cons hF, base_good3 hF, brk_rk le_rfl,
      base_vsmallF hF, base_frameClosed hF, base_frameOT hF, base_kd hF, base_td hF,
      G.base_ph3c hF, G.base_fc3 hF, base_vsmallRAll hF,
      base_absDS, base_absUS, base_tp1 hF, base_tplos, base_tp1w hF,
      fun _ => base_tplow hF, base_absUWL, base_absUW0, fun _ => base_adw hF, base_trigS0 hF,
      base_tplon hF, base_adn hF, base_rootS hF (by omega), base_rootP hF (by omega)⟩

/-! ## t = 1: 1 コピーの保存から展開の Inv3V2 と下降 -/

/-- **`ExpT1OutV2` from `ExpT1V2`** through the two `t = 1` entries. The seed condition is `Res3AW.seed`,
the prefix is `StepCtxV2.pre`. -/
theorem expT1Out_of_step (h1 : ExpT1V2) : ExpT1OutV2 := by
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
  have hdr := C.R.drop
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hI1 := (C.pre (r + L) (by omega) (by omega)).1
  rw [hL] at hexp hr hx2 hdr
  simp only [Nat.add_sub_cancel_left] at hexp
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  have hPs := h1 M ρ rk r L _ C hlen hL0 hd0e hr hx2
  rw [hexp]
  by_cases hq : par M 0 (r + L) = some r
  · exact qr_final_inv3V2 hlen hL0 hd0e S I hr hx2 hq C.nb2 hdr hI1 hPs n hn
  · exact qn_final_inv3V2 hlen hL0 hd0e S I hr hx2 hq hdr hI1 hPs n hn

/-! ## 帰納法 -/

/-- **Every nonempty standard matrix other than SRO has a valuation with `Inv3V2`.** -/
theorem hInvV2_all (hD : HDropV2) (hT : HTakeV2) (hTB : TakeBadV2) (hBO : BadOutV2)
    (h0 : ExpT0OutV2) (h1 : ExpT1OutV2) (h2 : ExpT2V2) (hCB : T2CBadOut) :
    ∀ M, Std M → M ≠ SRO → M ≠ [] → ∃ ρ rk, Inv3V2 M ρ rk := by
  intro M hM
  induction hM with
  | sro => intro h; exact absurd rfl h
  | @exp M n hM ih =>
    intro hNS hNE
    by_cases hMS : M = SRO
    · subst hMS
      obtain ⟨ρ, rk, I, _⟩ := hBaseR n
      exact ⟨ρ, rk, I⟩
    by_cases hME : M = []
    · subst hME; exact absurd rfl hNE
    obtain ⟨ρ, rk, I⟩ := ih hMS hME
    have hpre : ∀ j, j < M.length → M.take j ≠ [] → ∃ ρ' rk', Inv3V2 (M.take j) ρ' rk' := by
      intro j hj hjE
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h; exact absurd List.take_zero hjE
        · exact h
      exact ⟨_, rk, (pre_V2 hD hT hTB hM hMS I j hj1 hj).1⟩
    have hlen : 0 < M.length := List.length_pos_of_ne_nil hME
    by_cases hz : col M (M.length - 1) = (0, 0, 0)
    · rw [expand_zero_last hME hz n] at hNE ⊢
      exact hpre _ (by omega) hNE
    rcases Nat.lt_or_ge n 2 with hn | hn
    swap
    · by_cases hB : Bad2 M
      · exact (hBO M ρ rk hM hMS hME hB I n hn).1
      have C := ctx_V2 hD hT hTB hM hMS hME hB I
      have hsrow : TRIO.srow M (M.length - 1) = 0 ∨ TRIO.srow M (M.length - 1) = 1 ∨
          TRIO.srow M (M.length - 1) = 2 := by
        unfold TRIO.srow; split_ifs <;> simp
      rcases hsrow with hs | hs | hs
      · obtain ⟨ρN, rkN, IN, _⟩ := h0 M ρ rk C hz hs n hn
        exact ⟨ρN, rkN, IN⟩
      · obtain ⟨ρN, rkN, IN, _⟩ := h1 M ρ rk C hz hs n hn
        exact ⟨ρN, rkN, IN⟩
      · by_cases hb : T2CBad M
        · exact (hCB M ρ rk C hb hz hs).1 n hn
        · exact h2 M ρ rk ⟨C, hb⟩ hz hs n hn
    · rcases Nat.lt_or_ge n 1 with hn0 | hn1
      · obtain rfl : n = 0 := by omega
        obtain ⟨j, hj, he⟩ := expand_zero_take hME
        rw [he] at hNE ⊢
        exact hpre j hj hNE
      · obtain rfl : n = 1 := by omega
        rw [expand_one] at hNE ⊢
        exact hpre _ (by omega) hNE

/-! ## 下降の残り `Res3` -/

/-- **`Res3D` of a matrix in the induction**: the drop of the context, the chain from the prefixes. -/
theorem res3D_of_V2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtxV2 M ρ rk) : Res3D M ρ rk := by
  refine ⟨C.R.drop, ?_⟩
  intro j hj hNBj
  have hlj : (M.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
  have hD := ((C.pre (j + 1) (by omega) hj).2 hNBj).drop
  rw [hlj, show j + 1 - 1 = j by omega, drop1_take_succ] at hD
  exact hD

/-! ## 接頭辞の根の鎖（`Bad2` の段は `TakeBadV2`） -/

theorem root_take_zero (M : Mat) (σ : Valn) : root (M.take 0) σ = z := by simp [root, sumN]

/-- **The prefixes of the context** have a valuation (`drop1`), the ranking and a standard root. -/
theorem prefix_facts_of_pre {M : Mat} {rk : Bool → Nat → Nat}
    (hpre : ∀ j, 1 ≤ j → j < M.length →
      Inv3V2 (M.take j) (drop1 M j rk) rk ∧ (¬ Bad2 (M.take j) → Res3AW (M.take j) (drop1 M j rk) rk)) :
    ∀ j, j < M.length → Cons (M.take j) (drop1 M j rk) ∧ Rk (M.take j) rk ∧
      isOT (root (M.take j) (drop1 M j rk)) = true := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · have hR : Rk (M.take 0) rk := fun i hi => absurd hi (by simp)
    exact ⟨cons_of_rk hR, hR, by rw [root_take_zero]; rfl⟩
  · have I := (hpre j hj1 hj).1
    exact ⟨I.cons, I.rank, root_ot I.good⟩

theorem prefix_facts_pre {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtxV2 M ρ rk) :
    ∀ j, j < M.length → Cons (M.take j) (drop1 M j rk) ∧ Rk (M.take j) rk ∧
      isOT (root (M.take j) (drop1 M j rk)) = true :=
  prefix_facts_of_pre C.pre

/-- **One drop of a prefix does not increase the root**: the drop lemma at a non-`Bad2` prefix, `TakeBadV2` at a
`Bad2` one. -/
theorem root_step_pre (hTB : TakeBadV2) {M : Mat} {rk : Bool → Nat → Nat} (hM : Std M) (hpre : ∀ j, 1 ≤ j → j < M.length →
      Inv3V2 (M.take j) (drop1 M j rk) rk ∧ (¬ Bad2 (M.take j) → Res3AW (M.take j) (drop1 M j rk) rk))
    {k : Nat} (hk1 : 1 ≤ k) (hk : k + 1 < M.length) :
    root (M.take k) (drop1 M k rk) ≤ root (M.take (k + 1)) (drop1 M (k + 1) rk) := by
  have hPl : (M.take (k + 1)).length = k + 1 := by rw [List.length_take]; omega
  have IP := (hpre (k + 1) (by omega) hk).1
  have hStdP : Std (M.take (k + 1)) := std_take hM (k + 1) (by omega)
  have hSP : M.take (k + 1) ≠ SRO := ne_SRO_of_rk IP.rank
  by_cases hB : Bad2 (M.take (k + 1))
  · have h := (hTB _ _ rk hStdP hSP (by omega) hB IP).2
    rw [hPl, show k + 1 - 1 = k by omega, take_take_succ, drop1_take_succ] at h
    exact le_of_lt h
  · have RP := ((hpre (k + 1) (by omega) hk).2 hB).drop
    rw [hPl, show k + 1 - 1 = k by omega] at RP
    have S := sInv_std hStdP hSP
    have IK := (hpre k hk1 (by omega)).1
    have hD := (DropHypV.of ⟨IP.good, IP.vs, IP.fc, IP.fo, IP.kd, IP.td⟩ RP).toDropHyp S.uat S.uab
    have h := drop_root_le (N := M.take (k + 1)) (x := k) hPl.symm S.r0p S.z2 S.sibDec S.z1c hD IP.cons
      (by rw [take_take_succ, drop1_take_succ]; exact IK.cons) (by rw [take_take_succ]; exact IK.rank)
    rw [take_take_succ, drop1_take_succ] at h
    exact h.2

/-- **The chain of the prefixes**: the root does not increase from `M.take j` to `M.take k` (`j ≤ k < |M|`). -/
theorem root_chain_of_pre (hTB : TakeBadV2) {M : Mat} {rk : Bool → Nat → Nat} (hM : Std M) (hpre : ∀ j, 1 ≤ j → j < M.length →
      Inv3V2 (M.take j) (drop1 M j rk) rk ∧ (¬ Bad2 (M.take j) → Res3AW (M.take j) (drop1 M j rk) rk)) :
    ∀ j k, j ≤ k → k < M.length → root (M.take j) (drop1 M j rk) ≤ root (M.take k) (drop1 M k rk) := by
  have key : ∀ d j, j + d < M.length → root (M.take j) (drop1 M j rk) ≤ root (M.take (j + d)) (drop1 M (j + d) rk) := by
    intro d
    induction d with
    | zero => intro j _; exact le_refl _
    | succ d ih =>
      intro j hjd
      refine le_trans (ih j (by omega)) ?_
      rw [show j + (d + 1) = (j + d) + 1 by omega]
      rcases Nat.eq_zero_or_pos (j + d) with h0 | h1
      · rw [h0, root_take_zero]; exact z_le _
      · exact root_step_pre hTB hM hpre h1 (by omega)
  intro j k hjk hk
  have := key (k - j) j (by omega)
  rwa [show j + (k - j) = k by omega] at this

theorem root_chain_pre (hTB : TakeBadV2) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtxV2 M ρ rk) :
    ∀ j k, j ≤ k → k < M.length → root (M.take j) (drop1 M j rk) ≤ root (M.take k) (drop1 M k rk) :=
  root_chain_of_pre hTB C.std C.pre

/-! ## 最上位 -/

theorem hT0_V2 (h0 : ExpT0OutV2) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxV2 M ρ rk) :
    col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → DropsAt M ρ n := by
  intro hz hs n hn
  obtain ⟨ρN, rkN, IN, hot, hlt⟩ := h0 M ρ rk C hz hs n hn
  exact dropsAt_of rfl ⟨ρN, rkN, IN.cons, IN.rank, hot, hlt⟩

theorem hT1_V2 (h1 : ExpT1OutV2) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxV2 M ρ rk) :
    col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
      ∀ n, 2 ≤ n → DropsAt M ρ n := by
  intro hz hs n hn
  obtain ⟨ρN, rkN, IN, hot, hlt⟩ := h1 M ρ rk C hz hs n hn
  exact dropsAt_of rfl ⟨ρN, rkN, IN.cons, IN.rank, hot, hlt⟩

theorem hT2_V2 (h2 : ExpT2V2) (hR2 : R2V2) (hCB : T2CBadOut) (hTB : TakeBadV2) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxV2 M ρ rk) (R : Res3D M ρ rk) :
    col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n := by
  intro hz hs
  obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
  by_cases hb : T2CBad M
  · apply t2_dropsC (Inv3V2.toC C.S C.I) R (hCB M ρ rk C hb hz hs).2 hX hJ (root_chain_pre hTB C) (prefix_facts_pre C) hz hs
    intro n hn _ _
    obtain ⟨ρN, rkN, IN⟩ := (hCB M ρ rk C hb hz hs).1 n hn
    exact ⟨ρN, rkN, IN.cons, IN.rank, IN.good⟩
  · apply t2_dropsC (Inv3V2.toC C.S C.I) R (hR2 M ρ rk ⟨C, hb⟩ hz hs) hX hJ (root_chain_pre hTB C) (prefix_facts_pre C) hz hs
    intro n hn _ _
    obtain ⟨ρN, rkN, IN⟩ := h2 M ρ rk ⟨C, hb⟩ hz hs n hn
    exact ⟨ρN, rkN, IN.cons, IN.rank, IN.good⟩

/-- **Desc3 from the residuals**, with `t = 0` and `t = 1` in the conclusion forms `ExpT0OutV2`・`ExpT1OutV2`
(2026-10-17: no strong absorption `HAbSV2`; the `t = 0` descent comes from t0's engine). -/
theorem desc3_V2O (hD : HDropV2) (hT : HTakeV2) (hTB : TakeBadV2) (hBO : BadOutV2)
    (h0 : ExpT0OutV2) (h1 : ExpT1OutV2) (h2 : ExpT2V2) (hR2 : R2V2) (hCB : T2CBadOut) : Desc3 := by
  intro M n hM hS hE
  obtain ⟨ρ, rk, I⟩ := hInvV2_all hD hT hTB hBO h0 h1 h2 hCB M hM hS hE
  by_cases hB : Bad2 M
  · have hl2 : 2 ≤ M.length := by
      obtain ⟨⟨k, hu⟩, _⟩ := hB
      have := upg_succ_lt hu; omega
    have hpre := pre_V2 hD hT hTB hM hS I
    obtain ⟨IT, hlast⟩ := hTB M ρ rk hM hS hl2 hB I
    rcases n with _ | _ | n
    · obtain ⟨j, hj, he⟩ := expand_zero_take hE
      obtain ⟨hc, hrk, _⟩ := prefix_facts_of_pre hpre j hj
      refine ⟨root M ρ, root (M.take j) (drop1 M j rk), ⟨ρ, rk, I.cons, I.rank, rfl⟩, ?_, root_ot I.good,
        lt_of_le_of_lt (root_chain_of_pre hTB hM hpre j (M.length - 1) (by omega) (by omega)) hlast⟩
      rw [he]; exact ⟨_, rk, hc, hrk, rfl⟩
    · refine ⟨root M ρ, _, ⟨ρ, rk, I.cons, I.rank, rfl⟩, ?_, root_ot I.good, hlast⟩
      rw [expand_one]; exact ⟨_, rk, IT.cons, IT.rank, rfl⟩
    · obtain ⟨t', hv, _, hlt⟩ := (hBO M ρ rk hM hS hE hB I (n + 2) (by omega)).2
      exact ⟨root M ρ, t', ⟨ρ, rk, I.cons, I.rank, rfl⟩, hv, root_ot I.good, hlt⟩
  have C := ctx_V2 hD hT hTB hM hS hE hB I
  have R := res3D_of_V2 C
  obtain ⟨t', hv, _, hlt⟩ := desc_stepV2 hE (Inv3V2.toC C.S I) R (root_chain_pre hTB C) (prefix_facts_pre C)
    (hT0_V2 h0 C) (hT1_V2 h1 C) (hT2_V2 h2 hR2 hCB hTB C R) n
  exact ⟨root M ρ, t', ⟨ρ, rk, I.cons, I.rank, rfl⟩, hv, root_ot I.good, hlt⟩

end Ytosk
