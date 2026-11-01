/-
A zero-tail DQ decomposition that is quantified by QrLocV3/OFields but
was omitted by probes choosing only the new last nonzero summand.
-/
import Ytosk.V3QRCarrierV3
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

end Ytosk.QRLocFalse
