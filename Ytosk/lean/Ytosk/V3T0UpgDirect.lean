import Ytosk.V3T0UpgAbs
import Ytosk.V3T2UpgAbs
import Ytosk.V3ResV2

namespace Ytosk.T0UpgDirect
open T

/-- A genuinely small bump term makes absorption strong, independently of
row0-parent geometry or the weak drop field. -/
theorem absorption_of_small_target {M : Mat} {ρ : Valn} {i k : Nat} {W : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hi : i < M.length)
    (hu : upg M i = some k)
    (hv : ρ.v k = add (vOpt ρ (par M 1 i)) W)
    (hsmall : bumpW M ρ k < E0) :
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < W → Lhd z q W := by
  obtain ⟨m, hm, _, _, _⟩ := upg_spec hu
  have hV : isOT (vOpt ρ (par M 1 i)) = true := by
    rw [hm]
    exact hG.ot_v m (Nat.lt_trans (par_lt M 1 i m hm) hi)
  obtain ⟨_, _, _, _, hvk, _⟩ := upg_target_val hC hG hi hu
  have he : W = bumpW M ρ k := T2UpgAbs.add_right_injective _ (hv.symm.trans hvk)
  intro q hq hlt
  exact lhd_lt_small (isOT_mem_summands hV hq) (by rw [he]; exact hsmall) hlt

/-- The precise remaining direct-proof case. Failure outside T0Easy must be
an old, unchanged ancestor target with a bump term at least epsilon0. -/
theorem remaining_case {M : Mat} {ρ : Valn} {x : Nat}
    (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M)
    (hUAT : UAT M) (hUAB : UAB M)
    (hC : Cons M ρ) (hG : Good3 M ρ)
    (hUA : UpgAbsXW0 M x ρ) (hne : ¬ T0Easy M x)
    (hfail : ¬ UpgAbsX M x ρ) :
    ∃ r g i k W q,
      par M 0 x = some r ∧ par M 0 r = some g ∧ col M r = bump M g ∧
      i + 1 = x ∧ upg M i = some k ∧ k < x ∧ Anc0 M k i ∧ k < i ∧
      ¬ ChgX M x false k ∧ ¬ bumpW M ρ k < E0 ∧
      ρ.v k = add (vOpt ρ (par M 1 i)) W ∧ W ≠ z ∧
      q ∈ summands (vOpt ρ (par M 1 i)) ∧ q < W ∧ ¬ Lhd z q W := by
  classical
  unfold UpgAbsX at hfail
  push Not at hfail
  obtain ⟨i,k,W,hix,hu,hv,hW,q,hq,hlt,hnl⟩ := hfail
  have hi : i < M.length := by omega
  have hie : i = x-1 := by omega
  have hnb : NBParX M x i := by
    rcases hUA i k W hix hu hv hW with hs | hw
    · exact False.elim (hnl (hs q hq hlt))
    · exact hw.2.2
  have hnbx : ¬ NBPar M x := by
    intro hn
    refine hne ⟨hn, fun hpx => ?_⟩
    subst hie
    exact hnb.nb_of_child hpx
  unfold NBPar at hnbx
  push Not at hnbx
  obtain ⟨r,g,hp,hg,hb⟩ := hnbx
  have hkne : k ≠ x := by
    intro he
    subst k
    exact hnl (T2UpgAbs.absorption_at_leaf hC hG hi hu (children_last hx) hv q hq hlt)
  have hkx : k < x := by have := upg_le hu; omega
  obtain ⟨_,_,_,_,hcase⟩ := upg_spec hu
  have hA : Anc0 M k i ∧ k < i := hcase.resolve_left (by omega)
  have hnc : ¬ ChgX M x false k := by
    intro hchg
    exact no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
      ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hchg).1 rfl hkx) hkx hu hA.1 hA.2
  exact ⟨r,g,i,k,W,q,hp,hg,hb,hix,hu,hkx,hA.1,hA.2,hnc,
    fun hs => hnl (absorption_of_small_target hC hG hi hu hv hs q hq hlt),
    hv,hW,hq,hlt,hnl⟩

#print axioms absorption_of_small_target
#print axioms remaining_case
end Ytosk.T0UpgDirect
