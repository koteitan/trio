/-
The q!=r t=1 engine attached to the repaired source bundle.
The bad-closure local facts and StepT1B remain explicit, exactly as in WfQnA18.
This theorem supplies the context, source fields, seed decrease and prefix invariant.
-/
import Ytosk.V3EngineV3
import Ytosk.WfQnA18

namespace Ytosk.V3Main
open T WfExQ1 WfExQ2 WfQnE3 WfBad

/-- q!=r expansion preservation on Inv3V3. StepT1B PnV3 is the remaining
invariant step, not an old Inv3V2 output. -/
theorem qn_carrierV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtx3 M ρ rk) {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hqr : par M 0 (r + L) ≠ some r) {br : T} (hro : ρ.o r = psi (ρ.v r) br z)
    (hin : ∀ m, WfQnH3.TPLoSXIn M ρ r (ρ.v r) (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) m))
    (hVlt : ∀ m i, BadSet M (r + L) ρ r (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) m) i → vOpt ρ (par M 1 i) < ρ.o r)
    (hBr : ∀ m i, BadSet M (r + L) ρ r (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) m) i → i < r)
    (hKr : ∀ m i, BadSet M (r + L) ρ r (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) m) i → ∀ j ∈ children M i,
      col M j = bump M i → ∀ k ∈ children M j, DepX M (r + L) true k → r ≤ k)
    (hRwin : ∀ m i, BadSet M (r + L) ρ r (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) m) i →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < fsD (ρ.o r) (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) m) → q < ρ.o r →
        Lhd z q (ρ.o r))
    (hRest : WfQnA15.ResT1Bv M r L d0 ρ (ρ.v r) br ((drop1 M (r + L) rk).o r)
      (fun n => BadSet M (r + L) ρ r (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) (n - 2))))
    (hPsB : WfQnA8.StepT1B PnV3 M r L d0 ρ (ρ.v r) br ((drop1 M (r + L) rk).o r)
      (fun n => BadSet M (r + L) ρ r (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) (n - 2)))) :
    ∀ n, 2 ≤ n → ∃ σ rkN, Inv3V3 (TRIO.gexp M r L d0 0 n) σ rkN ∧
      root (TRIO.gexp M r L d0 0 n) σ < root M ρ := by
  have S := C.S
  have I := C.I
  have I1 := C.pre (r + L) (by omega) (by omega)
  have hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV2 M ρ (drop1 M (r + L) rk) i := by
    have h := (C.drop (show 2 ≤ M.length from by omega)).1
    rwa [show M.length - 1 = r + L from by omega] at h
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hnr := not_depX_v_r1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2
  have hnx : ¬ DepX M (r + L) false (r + L) := by
    intro hd
    cases hd with
    | vpar _ hp hm => rw [h1] at hp; cases hp; exact hnr hm
    | vupg _ _ hu _ => have := upg_succ_lt hu; omega
    | vbump _ h2 _ _ _ _ => exact h2 hx2
  have hdep := dep_anc_x S.uat S.z2 S.r12 S.bumpE2 hlen hx2 hA
  have hlt := dep_strict02 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good I1.cons I1.rank
    hdrop hx2 hq hnx true r hdep (by omega)
  intro n hn
  obtain ⟨σ, rkN, hCN, hRN, hGN, hPN, hot, hltN⟩ :=
    WfQnA18.t1_main_vlocSX3 hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab
      S.r12 S.bumpE2 S.r01 S.e00 h1 hx2 hqr I.cons I.good I.rank I.vs I.fc I.fo I.tp1
      I.tplosx I.adsx I.aus I.kd I.td hdrop (ne_of_lt hlt) rfl hro I.rootS I.rootP I1.good
      hin hVlt hBr hKr hRwin hRest PnV3 ⟨rk, I1⟩ hPsB n hn
  obtain ⟨rkV3, J⟩ := hPN
  exact ⟨σ, rkV3, J, hltN⟩

end Ytosk.V3Main
