/- QR producer chain using one genuine single-tail witness. Conditional only;
its matrix inputs must still be measured before adopting a new top. -/
import Ytosk.V3QRCanonical
import Ytosk.V3T1V3

namespace Ytosk.QRCanonicalChain
open T WfQrL1 WfQrL5 WfQrL6 WfQrL7 WfQrL8 WfQrL9 WfQrL10 WfQrL16 WfQrL18
  WfQrH5 WfQrH6 WfQrH2 QRCanonical WfExQ1 WfExQ2 WfExQ4 WfExQ8 WfExQ10 WfExQ11
section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e
theorem qr_chain_tail (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ n, 2 ≤ n → ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ n, 2 ≤ n → ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : ∀ n, 2 ≤ n → isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    (hnd : ∀ n, 2 ≤ n → ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (h1x : entry M 1 (r + L) ≠ 0) (hp1 : par M 1 (r + L) = some r)
    (hrD : DepX M (r + L) true r)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (Ex : Nat → Valn → (Nat → T) → (Nat → T) → Prop)
    (hOSD : ∀ i, i < r + L → DepX M (r + L) true i → OShapeD M (r + L) i)
    (hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i)
    (hPre : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      isOT (preState M ρ i L') = true)
    (hLocH : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r < ρ.o (r + L) → ρP.o r ≠ z → Cons (TRIO.gexp M r L d0 0 n) σ →
        -- C_strip (standard form of the new values)
        (∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) ∧
        Ex n ρP σ.o σ.v ∧
        -- the `o` frame fields
        (∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → DepX M (r + L) true c →
          ∀ η, DQ η false (ρ.o c) (σ.o c) → OFieldsTail (ρ.v i) (preState M ρ i L') (ρ.o c) (σ.o c) η) ∧
        (∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k → entry M 2 i = 0 →
          Single (last (ρ.v k)) ∧ Single (last (σ.v k)) ∧
          ∀ η, DQ η true (ρ.v k) (σ.v k) → DQ η false (last (ρ.v k)) (last (σ.v k))) ∧
        (∀ i L' K j k, i < r + L → DepX M (r + L) false i → children M i = L' ++ [j] → col M j = bump M i →
          children M j = K ++ [k] → DepX M (r + L) true k →
          Single (bumpW M ρ i) ∧ Single (bumpWQ M ρ i L' K (σ.o k)) ∧
          ((∃ η, DQ η false (ρ.o k) (σ.o k)) →
            ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L' K (σ.o k)))))
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    (hv1 : ρ1.v r ≤ ρ.v r)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (TRIO.gexp M r L d0 0 1) ρ1) (hPs : ExpStepQ Pn Ex M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      ρN.o r < ρ.o r ∧ ρN.o r < ρ.o (r + L) ∧ ρN.o r ≠ z ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have h1 : (TRIO.gexp M r L d0 0 1).length = r + 1 * L := TRIO.gexp_length hlen
  have hr1M : r < (TRIO.gexp M r L d0 0 1).length := by omega
  have hrM : r < M.length := by omega
  have hr1 : ρ1.o r < ρ.o (r + L) := by
    obtain ⟨Y, hY⟩ := WfSrcC.o_psi_form hC1 hr1M (hG1.ot_v r hr1M)
    rw [ox_eq hC hG hlen h1x hx2 hp1 hrM, hY, psi_lt_psi_z_iff]
    exact Or.inl (lt_of_le_of_lt hv1 (lt_succ_self _))
  refine qr_chainG hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hC hG hRM hOS h1x hp1 hrD hRA hR0 hRlast hRd
    hsM hpM Ex hOSD hVS hPre ?_ hC1 hR1 hG1 hr1 (o_ne_z_of_cons hC1 hr1M) hPv1 Pn hP1 hPs
  intro n hn ρP σ hCP hPr hPrz hCσ
  obtain ⟨hDo, hDv, hEx, hFr, hUpgL, hBW2⟩ := hLocH n hn ρP σ hCP hPr hPrz hCσ
  have hlN := len_N (d0 := d0) (n := n) hlen hn
  have hpos : 0 < (n - 1) * L := Nat.mul_pos (by omega) hL
  have hxN : r + L < (TRIO.gexp M r L d0 0 n).length := by omega
  obtain ⟨hSo, hSv⟩ := std_of_DQC hG hlen hCσ hxN hDo hDv
  have hRx : Rt < r + L := by
    rcases Nat.eq_or_lt_of_le hRA.le with h | h
    · exfalso
      have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hR0; rw [hR0]; rfl
      have h1 : entry M 0 (r + L) ≠ 0 := by
        have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
      rw [h] at hR0e; exact h1 hR0e
    · exact h
  refine ⟨(hSo Rt (by omega) hRd).1, fun i hi hd => (hSo i (by omega) hd).2, hSv,
    fun c hc _ => o_ne_z_of_cons hCσ (by omega), hEx, hSo, ?_, hUpgL, hBW2⟩
  exact hOF_of_fields_tail hlen hPre (fun c hc _ => single_o hC hG (by omega)) (fun c hc hd => (hSo c hc hd).1) hFr
theorem qr_chainV3f_tail (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ n, 2 ≤ n → ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ n, 2 ≤ n → ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : ∀ n, 2 ≤ n → isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    (hnd : ∀ n, 2 ≤ n → ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (h1x : entry M 1 (r + L) ≠ 0) (hp1 : par M 1 (r + L) = some r)
    (hrD : DepX M (r + L) true r)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hOSD : ∀ i, i < r + L → DepX M (r + L) true i → OShapeD M (r + L) i)
    (hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i)
    (hPre : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      isOT (preState M ρ i L') = true)
    (hLocH : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r < ρ.o (r + L) → ρP.o r ≠ z → Cons (TRIO.gexp M r L d0 0 n) σ →
        -- C_strip (standard form of the new values)
        (∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) ∧
        -- the `o` frame fields
        (∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → DepX M (r + L) true c →
          ∀ η, DQ η false (ρ.o c) (σ.o c) → OFieldsTail (ρ.v i) (preState M ρ i L') (ρ.o c) (σ.o c) η) ∧
        (∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k → entry M 2 i = 0 →
          Single (last (ρ.v k)) ∧ Single (last (σ.v k)) ∧
          ∀ η, DQ η true (ρ.v k) (σ.v k) → DQ η false (last (ρ.v k)) (last (σ.v k))) ∧
        (∀ i L' K j k, i < r + L → DepX M (r + L) false i → children M i = L' ++ [j] → col M j = bump M i →
          children M j = K ++ [k] → DepX M (r + L) true k →
          Single (bumpW M ρ i) ∧ Single (bumpWQ M ρ i L' K (σ.o k)) ∧
          ((∃ η, DQ η false (ρ.o k) (σ.o k)) →
            ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L' K (σ.o k)))))
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    (hv1 : ρ1.v r ≤ ρ.v r)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (S : SInv M) (I : Inv3V3 M ρ rkM) (hq : par M 0 (r + L) = some r)
    (hVSF : VSFResQ M r L d0 ρ)
    (hFr : FrameAtN M r L d0)
    (hP1 : PnV3 (TRIO.gexp M r L d0 0 1) ρ1) (hs1 : ρ1.o r < ρ.o r)
    (hF1 : FrameMapT1 M ρ r L (TRIO.gexp M r L d0 0 1) ρ1 ∧ VrDomQ M ρ r L (TRIO.gexp M r L d0 0 1) ρ1) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ PnV3f M ρ r L (TRIO.gexp M r L d0 0 n) ρN ∧
      ρN.o r < ρ.o r ∧ ρN.o r < ρ.o (r + L) ∧ ρN.o r ≠ z ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ :=
  qr_chain_tail hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hC hG hRM hOS h1x hp1 hrD hRA hR0 hRlast hRd
    hsM hpM (ExDQX M r L ρ) hOSD hVS hPre
    (fun n hn ρP σ hCP hlt hne hCN => by
      obtain ⟨ho, hv, hOF, hU, hB⟩ := hLocH n hn ρP σ hCP hlt hne hCN
      exact ⟨ho, hv, WfExQ7.exDQX_of_loc n ρP hlt ho hv, hOF, hU, hB⟩)
    hC1 hR1 hG1 hv1 hPv1 (PnV3f M ρ r L) ⟨hP1, hs1, hv1, hF1⟩
    (expStepQ_V3f S I hlen hL hd0e hp1 hx2 hq hVSF hFr)

end
end Ytosk.QRCanonicalChain

namespace Ytosk.V3Main
open T WfExQ1 WfExQ2 WfQnE3 WfBad WfQrL1 WfQrL5 WfQrL6 WfQrL8 WfQrL9 WfQrL10 WfQrL16 WfQrL18
  WfQrH5 WfQrH6 WfQrH2 WfExQ10
def QrLocTailV3 (M : Mat) (ρ : Valn) (r L d0 : Nat) : Prop :=
  ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r < ρ.o (r + L) → ρP.o r ≠ z → Cons (TRIO.gexp M r L d0 0 n) σ →
        -- C_strip (standard form of the new values)
        (∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) ∧
        -- the `o` frame fields
        (∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → DepX M (r + L) true c →
          ∀ η, DQ η false (ρ.o c) (σ.o c) → QRCanonical.OFieldsTail (ρ.v i) (preState M ρ i L') (ρ.o c) (σ.o c) η) ∧
        (∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k → entry M 2 i = 0 →
          Single (last (ρ.v k)) ∧ Single (last (σ.v k)) ∧
          ∀ η, DQ η true (ρ.v k) (σ.v k) → DQ η false (last (ρ.v k)) (last (σ.v k))) ∧
        (∀ i L' K j k, i < r + L → DepX M (r + L) false i → children M i = L' ++ [j] → col M j = bump M i →
          children M j = K ++ [k] → DepX M (r + L) true k →
          Single (bumpW M ρ i) ∧ Single (bumpWQ M ρ i L' K (σ.o k)) ∧
          ((∃ η, DQ η false (ρ.o k) (σ.o k)) →
            ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L' K (σ.o k))))
theorem qr_carrier_tailV3 (hF : HFrameV3) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtx3 M ρ rk) {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hq : par M 0 (r + L) = some r)
    (hUA : UAwRA M ρ (r + L)) (hLoc : QrLocTailV3 M ρ r L d0)
    (hVSF : VSFResQ M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ σ rkN, Inv3V3 (TRIO.gexp M r L d0 0 n) σ rkN ∧
      root (TRIO.gexp M r L d0 0 n) σ < root M ρ := by
  have S := C.S
  have I := C.I
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r < r + L := by omega
  have hpath := hpath_of_par1 h1 hA (by omega)
  have I1 := C.pre (r + L) (by omega) (by omega)
  have hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV2 M ρ (drop1 M (r + L) rk) i := by
    have h := (C.drop (show 2 ≤ M.length from by omega)).1
    rwa [show M.length - 1 = r + L from by omega] at h
  have hs1 := qr_seed_lt2 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2 hq
    I.cons I.good I.rank hdrop
  have h3 : NoBad3 M ρ ∨ r + 2 = M.length := by
    by_cases hb : Bad2 M
    · exact Or.inr (t1qr_bad_xm1 S.r0p S.sibDec S.z1c hb hlen h1 hq hx2)
    · exact Or.inl (noBad3_of_nb2 hb I.cons)
  have hFM := frameMapT1_takeG3 S I.cons I.good I1.cons I1.rank hlen hx2 hdrop
    (fun k W hi hu hv hW => hUA r k W hi hu hv hW) (fun _ => h3)
  have hdep := qr_dep hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2 hq
  obtain ⟨Rt, hRA, hRt0, hRlast⟩ := root_t1 S.r01 S.r12 S.e00 (r + L)
  have hRd := dep_anc_x S.uat S.z2 S.r12 S.bumpE2 hlen hx2 hRA
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
  have hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i :=
    fun i hi hd => dv_shape hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq hi hd
  have hFr := WfExQ3.frameAtN_of_glob hF C.std hlen hL h1 hx2
  rw [show entry M 0 (r + L) - entry M 0 r = d0 from by omega] at hFr
  intro n hn
  obtain ⟨σ, rkN, hCN, hRN, hGN, hPN, htail⟩ :=
    QRCanonicalChain.qr_chainV3f_tail hlen hL hA hd0e hpath hx2
      (hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1) (S.z2 r)
      (fun n hn => hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn)
      (fun n hn => hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn)
      (hnd_t1 hlen hL hA hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2)
      I.cons I.good I.rank hOS (by have := par1_entry_lt h1; omega) h1 hdep.1
      hRA hRt0 hRlast hRd I.rootS I.rootP (oShapeD_t1 S hlen hx2 hq) hVS
      (fun i A c B hi hd he => preState_ot_of_good I.good (fun d hdA => by
        have hdM : d ∈ children M i := by rw [he]; simp [hdA]
        exact (mem_children hdM).2)) hLoc
      (ρ1 := drop1 M (r + L) rk) (rk1 := rk)
      (by rw [gexp_one_eq hlen]; exact I1.cons)
      (by rw [gexp_one_eq hlen]; exact I1.rank)
      (by rw [gexp_one_eq hlen]; exact I1.good)
      ((hdrop r hrx).2.le)
      (fun g hg a ha h => by
        rw [gexp_one_eq hlen] at h
        exact base_v_read hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good I1.cons I1.rank hg ha h)
      S I hq hVSF hFr (by rw [gexp_one_eq hlen]; exact ⟨rk, I1⟩) hs1
      (by rw [gexp_one_eq hlen]; exact hFM) n hn
  obtain ⟨rkV3, J⟩ := hPN.1
  exact ⟨σ, rkV3, J, htail.2.2.2.2.2⟩


structure QrInputsTailV3 (M : Mat) (ρ : Valn) (r L d0 : Nat) : Prop where
  ua : UAwRA M ρ (r + L)
  loc : QrLocTailV3 M ρ r L d0
  vsf : VSFResQ M r L d0 ρ

def HQRInputsTailV3 : Prop :=
  ∀ M ρ rk, StepCtx3 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 1 (r + L) = some r → entry M 2 (r + L) = 0 → par M 0 (r + L) = some r →
      QrInputsTailV3 M ρ r L (entry M 0 (r + L) - entry M 0 r)

theorem expOut1_of_tail_inputs (hF : HFrameV3) (hQR : HQRInputsTailV3) (hQN : HQNInputsV3) : ExpOutV3 1 := by
  intro M ρ rk C hz hs n hn
  obtain ⟨r, hr⟩ := parLast_of C.S.e00 C.S.r01 C.S.r12 hz
  rw [hs] at hr
  have hrx := par_lt M 1 (M.length - 1) r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  have hx2 : entry M 2 (r + L) = 0 := by
    unfold TRIO.srow at hs
    split_ifs at hs with he2 he1
    · cases hs
    · show entry M 2 (r + L) = 0
      have : ¬ 0 < entry M 2 (M.length - 1) := he2
      rw [hL] at this; omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp := expand_eq_gexp_t1 M n (by omega) hzT (by rw [hs]; exact hr) hs
  rw [hL] at hexp hr
  simp only [Nat.add_sub_cancel_left] at hexp
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  rw [hexp]
  by_cases hq : par M 0 (r + L) = some r
  · have F := hQR M ρ rk C r L hlen hL0 hr hx2 hq
    exact qr_carrier_tailV3 hF C hlen hL0 hd0e hr hx2 hq F.ua F.loc F.vsf n hn
  · obtain ⟨br, hro⟩ := o_psi_sub C.I.cons (show r < M.length from by omega)
    rw [sf_ot (C.I.good.ot_v r (by omega))] at hro
    have F := hQN M ρ rk C r L hlen hL0 hr hx2 hq br hro
    exact qn_carrierV3 C hlen hL0 hd0e hr hx2 hq hro F.inn F.vlt F.before F.kids F.window F.rest F.step n hn

end Ytosk.V3Main
