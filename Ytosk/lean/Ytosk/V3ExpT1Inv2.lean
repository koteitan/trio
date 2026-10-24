/-
**t = 1 の展開の Inv3V2 と下降の組み立て `expT1Out_of_res`（2026-10-16、t1）。**

top の V3ResV2 の `ExpT1OutV2` を、次の名前つきの残りから出す:
- `HFrameV2`・`HLeafV2`（top の共通の残り）: N = M[n] の枠の 10 欄と葉の 2 条件。TP1C・TP1WC は PH3cG と葉から。
- `S1Std`: SRO 以外のどの標準形でも S1（V3EqSibS1）。S1 ⇒ EqSibUpg ⇒ PassRootRes で VSmallF が運べる。
- `T1VSRAllStep`: VSmallRAll の 1 コピーごとの保存（運ぶ束の残りの部分 CopyCoreV2・VrLe・VSmallF を前提にしてよい）。
エンジン（qr_final4S・t1_main_vlocS）に運ぶ述語は CopyCoreV2 ∧ VrLe ∧ VSmallF ∧ VSmallRAll。
始点は M.take x の Inv3V2（StepCtxV2.pre）、1 列落としは Res3A.drop、q = r の始点の条件は Res3A.seed。
-/
import Ytosk.V3GlobV2
import Ytosk.V3EqSibS1
import Ytosk.V3ExpInv2

namespace Ytosk

open T

/-- **One copy carries `Q`, given `P` before and after** (the step premises of `ExpStepT1At`). -/
def ExpStepT1R (P Q : Mat → Valn → Prop) (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T),
    Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP → Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    P (TRIO.gexp M r L d0 0 (n - 1)) ρP → Q (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    Good3 (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    (∀ i, i < r + L → DepX M (r + L) true i → isOT (fsD (ρ.o i) (Z i)) = true) →
    (∀ i, i < r + L → DepX M (r + L) false i → isOT (fsD (ρ.v i) (Z i)) = true) →
    (∀ c, c < r + L → DepX M (r + L) true c → fsD (ρ.o c) (Z c) ≤ ρ.o c ∧ fsD (ρ.o c) (Z c) ≠ z) →
    (ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z) →
    (∃ μ br vr seed k0, HoleData M (r + L) ρ μ br vr seed ∧
      (∀ i, ∃ k, k0 ≤ k ∧ Z i = gamS μ br seed k) ∧ ρP.o r = gamS μ br seed k0 ∧ k0 = n - 2 ∧
      μ = vr ∧ ρ.o r = psi vr br z) →
    P (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    Q (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z)

theorem expStep_andR {P Q : Mat → Valn → Prop} {M : Mat} {r L d0 : Nat} {ρ : Valn}
    (hP : ExpStepT1 P M r L d0 ρ) (hQ : ExpStepT1R P Q M r L d0 ρ) :
    ExpStepT1 (fun N σ => P N σ ∧ Q N σ) M r L d0 ρ :=
  fun n hn ρP Z hCP hGP hPQ hCN hGN ho hv hle hlex hH =>
    have hPN := hP n hn ρP Z hCP hGP hPQ.1 hCN hGN ho hv hle hlex hH
    ⟨hPN, hQ n hn ρP Z hCP hGP hPQ.1 hPQ.2 hCN hGN ho hv hle hlex hH hPN⟩

/-- The part of the carried bundle whose one-copy preservation is proved (modulo `PassRootRes`). -/
def T1Core (r : Nat) (ρ : Valn) (N : Mat) (σ : Valn) : Prop :=
  CopyCoreV2 N σ ∧ VrLe r ρ N σ ∧ VSmallF N σ

/-- **R-t1-vra**: `VSmallRAll` survives each `t = 1` copy. -/
def T1VSRAllStep : Prop :=
  ∀ M ρ rk r L d0, StepCtxV2 M ρ rk → r + L + 1 = M.length → 0 < L →
    entry M 0 (r + L) = entry M 0 r + d0 → par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
    ExpStepT1R (T1Core r ρ) (fun N σ => VSmallRAll N σ) M r L d0 ρ

/-- The carried bundle at the prefix `M.take x`. -/
theorem t1_base {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk) (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r)
    (R : DropRes M (r + L) ρ (drop1 M (r + L) rk)) (I1 : Inv3V2 (M.take (r + L)) (drop1 M (r + L) rk) rk) :
    T1Core r ρ (M.take (r + L)) (drop1 M (r + L) rk) ∧ VSmallRAll (M.take (r + L)) (drop1 M (r + L) rk) :=
  ⟨⟨I1.copyCore, vrle_prefix_inv3V2 S I hlen h1 R I1, I1.vs⟩, I1.vra⟩

/-- The carried bundle with the frame fields and the leaves gives `Inv3V2` of the expansion. -/
theorem inv3V2_of_core {N : Mat} {σ : Valn} {r0 : Nat} {ρ : Valn}
    {rkN : Bool → Nat → Nat} (hR : Rk N rkN) (hC : T1Core r0 ρ N σ) (hV : VSmallRAll N σ)
    (F : TakeFrameV2 N σ rkN) (hTP : TP1LeafG N σ) (hTPW : TP1WLeafG N σ) : Inv3V2 N σ rkN :=
  have K := hC.1
  ⟨K.cons, K.good, hR, hC.2.2, K.fc, K.fo, K.kd, K.td, K.ph, K.fc3, hV, F.ads, F.aus,
    tp1C_of_ph3cG K.cons ⟨K.good.ot_o, K.good.ot_v⟩ K.ph hTP, F.tplos,
    tp1WC_of_ph3cG K.cons ⟨K.good.ot_o, K.good.ot_v⟩ K.ph hTPW, F.tplow, F.auwl, F.auw0, F.adw,
    F.trigs, F.tplon, F.adn, K.rootS, K.rootP⟩

/-- **`ExpT1OutV2` from the named residuals.** -/
theorem expT1Out_of_res (hF : HFrameV2) (hLf : HLeafV2) (hS1 : S1Std) (hV : T1VSRAllStep) :
    ExpT1OutV2 := by
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
  have hPR : PassRootRes M r L ρ := passRootRes_of_S1 (sInvXJ_std C.std C.ne).1 (hS1 M C.std C.ne) hlen hr hx2
  have hstep : ExpStepT1 (fun N σ => T1Core r ρ N σ ∧ VSmallRAll N σ) M r L
      (entry M 0 (r + L) - entry M 0 r) ρ :=
    expStep_andR (expStep_core_vsmallF_pass_inv3V2 S I hlen hL0 hd0e hr hx2 hPR)
      (hV M ρ rk r L _ C hlen hL0 hd0e hr hx2)
  have hbase := t1_base S I hlen hr hdr hI1
  rw [hexp] at hStdN ⊢
  have hfin : ∃ ρN rkN, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) rkN ∧
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      (T1Core r ρ (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
        VSmallRAll (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) ∧
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN < root M ρ := by
    by_cases hq : par M 0 (r + L) = some r
    · exact qr_final4S hlen hL0 hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
        hr hx2 hq I.cons I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua
        I.tp1w (I.tplowAt hlen hr) I.auwl I.auw0 (I.adwAt hlen hr) I.tp1 I.trigs I.tplon I.adn I.rootS I.rootP
        _ hbase hstep n hn
    · have hrM : r < M.length := by omega
      obtain ⟨br, hro⟩ := o_psi_sub I.cons hrM
      rw [sf_ot (I.good.ot_v r hrM)] at hro
      have hdrop := drop_all hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hI1.cons hI1.rank
        I.vs hdr.vst I.fc I.fo hdr.argT
        (bump_drop hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hI1.cons hI1.rank
          I.kd I.td hdr.ab hdr.ws) hdr.ua
      have hne : (drop1 M (r + L) rk).o r ≠ ρ.o r :=
        ne_of_lt (o_r_strict0 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2
          hr hx2 hq I.cons I.good hI1.cons hI1.rank hdrop)
      exact t1_main_vlocS hlen hL0 hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
        hr hx2 hq I.cons I.good I.rank I.vs I.fc I.fo I.tp1 I.tplos I.ads I.aus hdr.argT
        I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua hne rfl hro I.rootS I.rootP hI1.good
        _ hbase hstep n hn
  obtain ⟨ρN, rkN, hCN, hRN, hGN, ⟨hcore, hvra⟩, hot, hlt⟩ := hfin
  have hNE : TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [len_N (d0 := entry M 0 (r + L) - entry M 0 r) hlen (show 2 ≤ n from hn)]
    omega
  have hNS := ne_SRO_of_rk hRN
  obtain ⟨hTP, hTPW⟩ := hLf _ ρN rkN hStdN hNS hNE hCN hRN hGN
  exact ⟨ρN, rkN, inv3V2_of_core hRN hcore hvra (hF _ ρN rkN hStdN hNS hNE hCN hRN hGN) hTP hTPW, hot, hlt⟩

end Ytosk
