/-
A zero-tail DQ decomposition that is quantified by QrLocV3/OFields but
was omitted by probes choosing only the new last nonzero summand.
-/
import Ytosk.V3TranslationInputsV3
import Ytosk.ExpGexp

namespace Ytosk.QRLocFalse
open T WfQrH3 WfQrH6 WfExQ1
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def M : Mat := [(0,0,0),(1,1,0),(2,2,0)]
def N : Mat := [(0,0,0),(1,1,0),(2,1,0)]
def om1 : T := psi one z z
def om2 : T := psi (succ one) z z

def ρ : Valn := ⟨fun i => [psi z om2 z, psi one om2 z, om2].getD i z,
  fun i => [z,one,succ one].getD i z⟩
def σ : Valn := ⟨fun i => [psi z (H one om1) z, psi one om1 z, om1].getD i z,
  fun i => [z,one,one].getD i z⟩
def τ : Valn := ⟨fun i => [psi z om1 z,om1].getD i z,
  fun i => [z,one].getD i z⟩

theorem standard : Std M := by
  have h : expand (expand (expand (expand SRO 1) 1) 1) 3 = M := by decide
  rw [← h]
  exact Std.exp 3 (Std.exp 1 (Std.exp 1 (Std.exp 1 Std.sro)))

theorem ne_sro : M ≠ SRO := by decide

theorem cons : Cons M ρ := by unfold Cons; decide

theorem consN : Cons N σ := by unfold Cons; decide

theorem consP : Cons (M.take 2) τ := by unfold Cons; decide

theorem expand_two : expand M 2 = N := by decide

theorem gexp_two : TRIO.gexp M 1 1 1 0 2 = N := by
  have he : expand M 2 = TRIO.gexp M 1 1 1 0 2 :=
    expand_eq_gexp_t1 M 2 (by decide) (by decide) (by decide) (by decide)
  rw [← he]; exact expand_two

theorem zero_tail : DQ z true om2 om1 := by
  have h : DQ z false om2 z := by
    have h := DQ.base (η := z) (l := om2) (by decide : fsD om2 z < om2)
    simpa [om2,one,fsD,succ,app] using h
  have hq : ∀ q ∈ summands om1, z ≤ q ∧ q < om2 := by decide
  exact DQ.mk (B := z) (Q := om1) rfl h hq

theorem not_ofields : ¬ OFields z z (psi one om2 z) (psi one om1 z) z := by
  intro h
  have hb : DQ z false om2 z := by
    have h := DQ.base (η := z) (l := om2) (by decide : fsD om2 z < om2)
    simpa [om2,one,fsD,succ,app] using h
  have htrigger : Trig z z one om2 := by constructor <;> decide
  have hf := h.2 one om2 om1 rfl rfl zero_tail htrigger
  exact hf.2.1 z om2 z om1 rfl ⟨succ one,z,rfl⟩ rfl hb rfl

theorem not_qrLoc : ¬ V3Main.QrLocV3 M ρ 1 1 1 := by
  intro h
  have hCP : Cons (TRIO.gexp M 1 1 1 0 (2-1)) τ := by
    have he : TRIO.gexp M 1 1 1 0 (2-1) = M.take 2 := gexp_one_gen (by decide)
    rw [he]; exact consP
  have hCN : Cons (TRIO.gexp M 1 1 1 0 2) σ := by rw [gexp_two]; exact consN
  have H := h 2 (by omega) τ σ hCP (by decide) (by decide) hCN
  have hd : DQ z false (ρ.o 1) (σ.o 1) := DQ.arg zero_tail
  have hdc : DepX M 2 true 1 :=
    DepX.ochild (c := 2) (by decide) (by decide) (by decide) DepX.leaf
  have hdi : DepX M 2 true 0 :=
    DepX.ochild (c := 1) (by decide) (by decide) (by decide) hdc
  have ho := H.2.2.1 0 [] 1 [] (by omega) hdi (by decide) hdc z hd
  exact not_ofields ho

/-- The obstruction is independent of the particular consistent valuation. -/
theorem not_qrLoc_of_cons {ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ') (hR : Rk M rk) : ¬ V3Main.QrLocV3 M ρ' 1 1 1 := by
  intro h
  have hag := agree_of_cons hC cons hR
  have he1 : ρ'.o 1 = ρ.o 1 := (hag 1 (by decide)).1
  have he2 : ρ'.o 2 = ρ.o 2 := (hag 2 (by decide)).1
  have hv0 : ρ'.v 0 = ρ.v 0 := (hag 0 (by decide)).2
  have hCP : Cons (TRIO.gexp M 1 1 1 0 (2-1)) τ := by
    rw [gexp_one_gen (by decide : 1+1+1=M.length)]; exact consP
  have hCN : Cons (TRIO.gexp M 1 1 1 0 2) σ := by rw [gexp_two]; exact consN
  have H := h 2 (by omega) τ σ hCP (by rw [he2]; decide) (by decide) hCN
  have hd : DQ z false (ρ'.o 1) (σ.o 1) := by rw [he1]; exact DQ.arg zero_tail
  have hdc : DepX M 2 true 1 :=
    DepX.ochild (c := 2) (by decide) (by decide) (by decide) DepX.leaf
  have hdi : DepX M 2 true 0 :=
    DepX.ochild (c := 1) (by decide) (by decide) (by decide) hdc
  have ho := H.2.2.1 0 [] 1 [] (by omega) hdi (by decide) hdc z hd
  change OFields (ρ'.v 0) z (ρ'.o 1) (σ.o 1) z at ho
  rw [hv0,he1] at ho
  exact not_ofields ho

/-- The current engine-input hypotheses are jointly inconsistent.
This uses the repaired induction itself, never an old Inv3V2 existence theorem. -/
theorem inconsistent_engine_inputs
    (hD : V3Main.HDropV3) (hF : WfExQ2.HFrameV3)
    (hAbs : V3Main.T0AtV3 (fun M ρ r L => T0AbsW M r L ρ))
    (hSeeds : V3Main.T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : V3Main.HQRInputsV3) (hQN : V3Main.HQNInputsV3)
    (hBX : V3Main.T2AtV3 V3Main.T2BelowAtV3)
    (hFO : V3Main.T2AtV3 (fun M _ => T2SeedFrames QFO M))
    (hSF : V3Main.T2AtV3 (fun M _ => T2SeedFrames G.QT2F M))
    (hSP : V3Main.T2AtV3 (fun M _ => T2SeedFrames G.QT2P M))
    (hN : V3Main.T2SmallV3) : False := by
  have h0 := V3Main.expOutV3_of_core hF (V3Main.expCore0_of_seeds hAbs hSeeds)
  have h1 := V3Main.expOut1_of_inputs hF hQR hQN
  have h2 := V3Main.expOut2_of_inputs hF hBX hFO hSF hSP hN
  obtain ⟨ρ',rk,I⟩ := V3Main.inv3V3_all hD hF h0 h1 h2 M standard ne_sro (by decide)
  have C := V3Main.ctx3 hD hF standard ne_sro (by decide) I
  have F := hQR M ρ' rk C 1 1 (by decide) (by omega) (by decide) (by decide) (by decide)
  exact not_qrLoc_of_cons I.cons I.rank F.loc

end Ytosk.QRLocFalse
