/-
The q=r t=1 engine attached to StepCtx3.
All structural, prefix and base facts are supplied by the repaired context.
The remaining local DQ conditions and VSFResQ are those of WfExQ11;
UAwRA supplies the base component map. No old absorption field is restored.
-/
import Ytosk.V3EngineV3
import Ytosk.WfExQ11
import Ytosk.WfExQ3
import Ytosk.WfSdP7

namespace Ytosk.V3Main
open T WfExQ1 WfExQ2 WfQrL1 WfQrL5 WfQrL6 WfQrL8 WfQrL9 WfQrL10 WfQrL16 WfQrL18
  WfQrH5 WfQrH6 WfQrH3 WfQrH2 WfExQ10

/-- Exactly the local DQ assumptions of qr_chainV3f, with no extra frame shape. -/
def QrLocV3 (M : Mat) (ρ : Valn) (r L d0 : Nat) : Prop :=
  ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r < ρ.o (r + L) → ρP.o r ≠ z → Cons (TRIO.gexp M r L d0 0 n) σ →
        -- C_strip (standard form of the new values)
        (∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) ∧
        -- the `o` frame fields
        (∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → DepX M (r + L) true c →
          ∀ η, DQ η false (ρ.o c) (σ.o c) → OFields (ρ.v i) (preState M ρ i L') (ρ.o c) (σ.o c) η) ∧
        (∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k → entry M 2 i = 0 →
          Single (last (ρ.v k)) ∧ Single (last (σ.v k)) ∧
          ∀ η, DQ η true (ρ.v k) (σ.v k) → DQ η false (last (ρ.v k)) (last (σ.v k))) ∧
        (∀ i L' K j k, i < r + L → DepX M (r + L) false i → children M i = L' ++ [j] → col M j = bump M i →
          children M j = K ++ [k] → DepX M (r + L) true k →
          Single (bumpW M ρ i) ∧ Single (bumpWQ M ρ i L' K (σ.o k)) ∧
          ((∃ η, DQ η false (ρ.o k) (σ.o k)) →
            ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L' K (σ.o k))))
/-- OShape already names the unique changing counted child. Export its D fact. -/
theorem oShapeD_t1 {M : Mat} {r L : Nat} (S : SInv M)
    (hlen : r + L + 1 = M.length) (hx2 : entry M 2 (r + L) = 0)
    (hq : par M 0 (r + L) = some r) :
    ∀ i, i < r + L → DepX M (r + L) true i → OShapeD M (r + L) i := by
  intro i hi hD
  by_cases hv : DepX M (r + L) false i
  · exact Or.inl ⟨hv, fun d hd => not_counted_iff
      (uncnt_of_depv hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq hi hv hd)⟩
  · refine Or.inr ⟨hv, ?_⟩
    cases hD with
    | leaf => exact absurd hi (lt_irrefl _)
    | @ochild _ c hc hcb hcu hdc =>
      obtain ⟨A, B, he⟩ := List.append_of_mem hc
      obtain ⟨hA, hB⟩ := sib_order (children_sorted M i) he
      refine ⟨A, c, B, he, hcb, hcu, ?_, ?_, hdc⟩
      · intro d hd
        have hdM : d ∈ children M i := by rw [he]; simp [hd]
        exact not_counted_iff (fun h => p1_dep hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
          hi hc hdM (hB d hd) hdc h)
      · intro d hd hcnt hdD
        have hdM : d ∈ children M i := by rw [he]; simp [hd]
        exact p1_dep hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq hi hdM hc
          (hA d hd) hdD ⟨hcb, hcu⟩
    | ov h => exact (hv h).elim

/-- The old pre-state has a standard argument, without an extra local hypothesis. -/
theorem preState_ot_of_good {M : Mat} {ρ : Valn} (G : Good3 M ρ) {i : Nat} {A : List Nat}
    (hA : ∀ d ∈ A, d < M.length) : isOT (preState M ρ i A) = true := by
  unfold preState
  apply isOT_spArg _ _ z rfl
  apply isOT_sumN
  intro t ht
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_filter.mp ht).1
  rw [cnt_eq_ite]
  split_ifs
  · exact G.ot_o d (hA d hd)
  · rfl

/-- Full q=r expansion output from the repaired source and existing local DQ engine. -/
theorem qr_carrierV3 (hF : HFrameV3) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtx3 M ρ rk) {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hq : par M 0 (r + L) = some r)
    (hUA : UAwRA M ρ (r + L)) (hLoc : QrLocV3 M ρ r L d0)
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
    WfExQ11.qr_chainV3f hlen hL hA hd0e hpath hx2
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

end Ytosk.V3Main
