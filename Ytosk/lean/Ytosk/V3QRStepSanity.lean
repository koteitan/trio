/- Finite-instance sanity checks for the replacement QR interface. -/
import Ytosk.V3QRStepV3
import Ytosk.V3QRLocFalse
import Ytosk.WfQnL4
namespace Ytosk.QRStepSanity
open T WfQrH6 WfQrH2 WfQrL1 QRCanonical QRLocFalse
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- The actual five local conjuncts of QrLocStepV3 at one pair of valuations.
This is a finite-instance sanity check, not a proof of all expansion lengths. -/
def LocalFields (M : Mat) (ρ σ : Valn) (x : Nat) : Prop :=
-- C_strip (standard form of the new values)
        (∀ c, c ≤ x → DepX M (x) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS) ∧
        (∀ i, i < x → DepX M (x) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) ∧
        -- the `o` frame fields
        (∀ i L' c R, i < x → DepX M (x) true i → children M i = L' ++ c :: R → DepX M (x) true c →
          FStep (ρ.v i) (preState M ρ i L') (ρ.o c) (σ.o c)) ∧
        (∀ i k, i < x → DepX M (x) false i → upg M i = some k → entry M 2 i = 0 →
          Single (last (ρ.v k)) ∧ Single (last (σ.v k)) ∧
          ∀ η, DQ η true (ρ.v k) (σ.v k) → DQ η false (last (ρ.v k)) (last (σ.v k))) ∧
        (∀ i L' K j k, i < x → DepX M (x) false i → children M i = L' ++ [j] → col M j = bump M i →
          children M j = K ++ [k] → DepX M (x) true k →
          Single (bumpW M ρ i) ∧ Single (bumpWQ M ρ i L' K (σ.o k)) ∧
          ((∃ η, DQ η false (ρ.o k) (σ.o k)) →
            ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L' K (σ.o k))))
private theorem no_zero : ¬ DepX M 2 false 0 := by
  intro h
  cases h with
  | vpar h1 _ _ => exact h1 (by decide)
  | vupg h1 _ _ _ => exact h1 (by decide)
  | vbump h1 _ _ _ _ _ => exact h1 (by decide)
private theorem no_one : ¬ DepX M 2 false 1 := by
  intro h
  cases h with
  | @vpar _ m _ hp hd =>
    have he : par M 1 1 = some 0 := by decide
    rw [he] at hp
    cases hp
    exact no_zero hd
  | vupg _ _ hu _ =>
    have he : upg M 1 = none := by decide
    rw [he] at hu; cases hu
  | vbump _ h2 _ _ _ _ => exact h2 (by decide)
private theorem no_v {i : Nat} (hi : i < 2) : ¬ DepX M 2 false i := by
  have he : i = 0 ∨ i = 1 := by omega
  rcases he with rfl | rfl
  · exact no_zero
  · exact no_one

private theorem dqc_leaf (η : T) (hlt : η < om2) (hot : isOT η = true) :
    DQC η false om2 η η := by
  have hf : fsD om2 η = η := WfQrL11.fsD_om_succ one η
  have h := DQC.base (η := η) (l := om2) (by rwa [hf]) (by rwa [hf])
  simpa only [hf] using h

private theorem dqc_arg {a : T} (η : T) (hlt : η < om2) (hot : isOT η = true)
    (ha : isOT (psi a η z) = true) :
    DQC η false (psi a om2 z) (psi a η z) (psi a η z) := by
  have ht : DQC η true om2 η η := by
    have h := DQC.mk (B := z) (Q := z) rfl (dqc_leaf η hlt hot) (by simp [summands]) (by rfl)
    simpa [app] using h
  exact DQC.arg ht ha (fun g hg hn => False.elim (hn hg))

private theorem nonzero_tail : DQ z false om2 om1 := by
  have h0 : DQ z false one z := by
    have h := DQ.base (η := z) (l := one) (by decide : fsD one z < one)
    simpa [one,fsD] using h
  have h1 : DQ z true (succ one) one := by
    have h := DQ.mk (B := one) (Q := z) rfl h0 (by simp [summands])
    simpa [one,succ,app] using h
  exact DQ.sub h1

private theorem fields : OFieldsTail z z (psi one om2 z) (psi one om1 z) z := by
  constructor
  · intro he _
    exact False.elim ((by decide : fsD (psi one om2 z) z ≠ psi one om1 z) he)
  · intro s y yN ho hn ht
    obtain ⟨rfl,rfl,-⟩ := T.psi.inj ho
    obtain ⟨_,rfl,-⟩ := T.psi.inj hn
    refine ⟨?_,z,z,om2,om1,z,?_,?_,?_,?_,nonzero_tail,?_,?_⟩
    · constructor <;> decide
    · simp [app]
    · exact ⟨succ one,z,rfl⟩
    · simp [app]
    · exact ⟨by decide,one,z,rfl⟩
    · simp [summands]
    · intro _; exact Or.inl rfl

private theorem repaired_frame : FStep z z (psi one om2 z) (psi one om1 z) :=
  frame_step_fields_tail (by decide) ⟨by decide,one,om2,rfl⟩ ⟨by decide,one,om1,rfl⟩
    (DQ.arg zero_tail) fields
theorem local_two : LocalFields M ρ σ 2 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro c hc _
    have he : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    rcases he with rfl | rfl | rfl
    · exact ⟨psi one om1 z, psi z (psi one om1 z) z,
        dqc_arg (a := z) (psi one om1 z) (by decide) (by decide) (by decide)⟩
    · exact ⟨om1,psi one om1 z,dqc_arg (a := one) om1 (by decide) (by decide) (by decide)⟩
    · exact ⟨om1,om1,dqc_leaf om1 (by decide) (by decide)⟩
  · intro i hi hd; exact False.elim (no_v hi hd)
  · intro i A c R hi _ hch _
    have hc : c ∈ children M i := by rw [hch]; simp
    have hei : i = 0 ∨ i = 1 := by omega
    have hlen : (children M i).length = 1 := by rcases hei with rfl | rfl <;> decide
    have hAl : A.length = 0 := by
      have hh := congrArg List.length hch
      simp only [List.length_append,List.length_cons] at hh
      rw [hlen] at hh; omega
    have hA : A = [] := List.eq_nil_of_length_eq_zero hAl
    subst A
    rcases hei with rfl | rfl
    · have hc1 : c = 1 := by
        have hh : children M 0 = [1] := by decide
        simpa [hh] using hc
      subst c
      exact repaired_frame
    · have hc2 : c = 2 := by
        have hh : children M 1 = [2] := by decide
        simpa [hh] using hc
      subst c
      change ∃ η, DQ η false (psi one om2 z) (psi one om1 z)
      exact ⟨z,DQ.arg zero_tail⟩
  · intro i k hi hd; exact False.elim (no_v hi hd)
  · intro i A K j k hi hd; exact False.elim (no_v hi hd)

theorem seed_component_input : UAwRA M ρ 2 := by
  intro i k W hi hu
  have he : i = 1 := by omega
  subst i
  have hn : upg M 1 = none := by decide
  rw [hn] at hu; cases hu

theorem changed_child_input : WfExQ10.VSFResQ M 1 1 1 ρ := by
  intro n hn ρP oq vq hCP hGP hCN hGN hEx i hi A c R hCL hdc hc g hg
  exact False.elim (no_v hc hdc)

end Ytosk.QRStepSanity
