/- The unresolved bad-leaf pair is outside DQ for EVERY eta, not merely
outside the finite measurement pool. DQX is needed to represent this shape. -/
import Ytosk.V3DQXSanity
import Ytosk.V3T0Thr

namespace Ytosk.DQNoBadLeaf
open T WfQrH6 WfQrL2 WfQrL12
set_option maxRecDepth 100000

def w : T := psi z one z
def a : T := app w w
def L : T := psi a z z
def R : T := psi (succ w) L z
def YOld : T := app L L
def YNew : T := app L R
def WOld : T := psi w YOld z
def WNew : T := psi w YNew z

private theorem false_inv {η old new : T} (h : DQ η false old new) :
    (new = fsD old η) ∨
    (∃ b bN, old = psi b z z ∧ new = psi bN z z ∧ DQ η true b bN) ∨
    (∃ b c cN, old = psi b c z ∧ new = psi b cN z ∧ DQ η true c cN) := by
  cases h with
  | base _ => exact Or.inl rfl
  | sub h => exact Or.inr (Or.inl ⟨_,_,rfl,rfl,h⟩)
  | arg h => exact Or.inr (Or.inr ⟨_,_,_,rfl,rfl,h⟩)

theorem fsD_L_shape (η : T) : fsD L η = psi (fsD a η) z z := by
  have ha : a ≠ z := by decide
  have hs : isSucc a = false := by decide
  change fsD (psi a z z) η = _
  rw [fsD]
  simp only [if_neg ha,hs,Bool.false_eq_true,if_false,if_true]

private theorem fsD_a (η : T) : fsD a η = app w (mulT one (count η)) := by
  rfl

private theorem mul_one_nat (n : Nat) : mulT one n = natT n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change psi z z (mulT one n) = psi z z (natT n)
    rw [ih]

/-- `w + count eta` is represented by `app w (natT (count eta))`. -/
theorem fsD_L (η : T) : fsD L η = psi (app w (natT (count η))) z z := by
  rw [fsD_L_shape,fsD_a,mul_one_nat]

private theorem dq_L_is_leaf {η new : T} (h : DQ η false L new) :
    ∃ b, new = psi b z z := by
  rcases false_inv h with he | ⟨b,bN,ho,hn,hd⟩ | ⟨b,c,cN,ho,hn,hd⟩
  · exact ⟨_,he.trans (fsD_L_shape η)⟩
  · exact ⟨bN,hn⟩
  · have hc : c = z := ((T.psi.inj ho).2.1).symm
    rw [hc] at hd
    exact False.elim (T.not_lt_z _ hd.lt)

theorem not_DQ_L_R (η : T) : ¬ DQ η false L R := by
  intro h
  obtain ⟨b,hb⟩ := dq_L_is_leaf h
  have hz : L = z := (T.psi.inj hb).2.1
  exact (by decide : L ≠ z) hz

theorem not_DQ_L_zero (η : T) : ¬ DQ η false L z := by
  intro h
  obtain ⟨b,hb⟩ := dq_L_is_leaf h
  cases hb

private theorem not_DQ_Y (η : T) : ¬ DQ η true YOld YNew := by
  intro h
  obtain ⟨B,l,lN,Q,s,y,ey,eyn,hl,hd,hQ⟩ := DQ.true_inv h
  have hsplit : app L (psi a z z) = app B (psi s y z) := by
    simpa only [YOld,L,hl] using ey
  obtain ⟨hB,hs,hy⟩ := app_last_inj hsplit
  have hlL : l = L := by rw [hl,← hs,← hy]; rfl
  rw [hlL] at hd
  rw [← hB] at eyn
  have htail : R = app Q lN := app_left_cancel0 (show app L R = app L (app Q lN) from eyn)
  cases hq : Q with
  | z =>
    have hln : lN = R := by simpa [hq,app] using htail.symm
    rw [hln] at hd
    exact not_DQ_L_R η hd
  | psi b c d =>
    rw [hq] at htail
    have hz : app d lN = z := ((T.psi.inj htail).2.2).symm
    have hln : lN = z := (app_eq_z hz).2
    rw [hln] at hd
    exact not_DQ_L_zero η hd

private theorem fsD_W_shape (η : T) :
    fsD WOld η = psi w (app L (psi (fsD a η) z z)) z := by
  have hy0 : YOld ≠ z := by decide
  have hs : isSucc YOld = false := by decide
  have hc : cof YOld = .omega := by decide
  change fsD (psi w YOld z) η = _
  rw [fsD]
  simp only [if_neg hy0,hs,Bool.false_eq_true,if_false,hc]
  change psi w (app L (fsD L η)) z = _
  rw [fsD_L_shape]

/-- No basic-sequence index can represent this actual W change. -/
theorem not_DQ_W2 (η : T) : ¬ DQ η false WOld WNew := by
  intro h
  rcases false_inv h with he | ⟨b,bN,ho,hn,hd⟩ | ⟨b,c,cN,ho,hn,hd⟩
  · rw [fsD_W_shape] at he
    have ha := (T.psi.inj he).2.1
    have ht : R = psi (fsD a η) z z := app_left_cancel0 ha
    have hz : L = z := (T.psi.inj ht).2.1
    exact (by decide : L ≠ z) hz
  · have hz : YOld = z := (T.psi.inj ho).2.1
    exact (by decide : YOld ≠ z) hz
  · have hb : b = w := (T.psi.inj ho).1.symm
    have hec : c = YOld := (T.psi.inj ho).2.1.symm
    have hen : cN = YNew := (T.psi.inj hn).2.1.symm
    rw [hec,hen] at hd
    exact not_DQ_Y η hd

theorem not_DQC_W2 (η tS : T) : ¬ DQC η false WOld WNew tS :=
  fun h => not_DQ_W2 η h.toDQ

theorem not_DQC_W36407 (η tS : T) :
    ¬ DQC η false (bumpW DQXSanity.M0 DQXSanity.ρ0 34)
      (bumpW DQXSanity.N0 DQXSanity.σ0 34) tS := by
  change ¬ DQC η false WOld WNew tS
  exact not_DQC_W2 η tS

theorem not_DQC_W36420 (η tS : T) :
    ¬ DQC η false (bumpW DQXSanity.M1 DQXSanity.ρ1 35)
      (bumpW DQXSanity.N1 DQXSanity.σ1 35) tS := by
  change ¬ DQC η false WOld WNew tS
  exact not_DQC_W2 η tS

end Ytosk.DQNoBadLeaf
