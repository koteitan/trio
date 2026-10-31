/-
**WfQrH3 (2026-11-01): the leaf-parent `o` frame and the assembled frame step `hOF` of `qr_chainF`.**
Leaf parent (`c = x`, `o(x) = Ω_{a+1}`, `o_N(x) = e`): if `e` does not trigger, the add shape (`frame_DQ_add`);
if it triggers, the leafpar shape (`frame_DQ_leafpar`).  `frame_step_fields` combines WfQrH2 into the frame step
from the fields `OFields`; `hOF_of_fields` is the conjunct `hOF` of `qr_chainF.hLocE` from them.
-/
import Ytosk.WfQrH2
import Ytosk.WfQrH1

namespace Ytosk.WfQrH3
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL4 Ytosk.WfQrL11 Ytosk.WfQrL15 Ytosk.WfQrL16 Ytosk.WfQrH2

/-- The leafpar fields at `o(x) = Ω_{a+1}`, `o_N(x) = ψ_{s'}(y')` (frames.py: hold on every leaf-parent frame). -/
def LeafPar (v pre a s' y' : T) : Prop :=
  ∃ B Q, Trig v pre s' y' ∧ (split y' (psi (succ s') z z)).2 ≠ z ∧
    add pre (psi (succ a) z z) = app B (psi (succ a) z z) ∧ (split y' (psi (succ s') z z)).1 = app B Q ∧
    (∀ q ∈ summands Q, psi s' y' z ≤ q ∧ q < psi (succ a) z z)

/-- **The leaf-parent frame step**: no trigger at `e` (add), or the leafpar fields. -/
theorem frame_step_leaf {v pre a e : T} (hpre : isOT pre = true) (hSN : Single e) (he : e < psi (succ a) z z)
    (hcase : (∀ s' y', e = psi s' y' z → ¬ Trig v pre s' y') ∨ (∃ s' y', e = psi s' y' z ∧ LeafPar v pre a s' y')) :
    FStep v pre (psi (succ a) z z) e := by
  rcases hcase with hnt | ⟨s', y', rfl, B, Q, htN, hloN, hadd, hhi, hQ⟩
  · obtain ⟨η, hd⟩ := WfQrH1.hX_of_omsucc he
    exact ⟨η, frame_DQ_add hpre hSN hd notTrig_z hnt⟩
  · exact frame_DQ_leafpar hSN.1 notTrig_z htN hloN hadd hhi hQ he

/-- **The fields of one `o` frame** (`o(c) = oc`, `o_N(c) = oN`, `DQ η false oc oN`):
- base form `oN = fsD(oc, η)`: the leaf parent `oc = Ω_{a+1}` with its case split, or `oc = Ω_s → oN = Ω_{s'}`, or
  an argument decomposition `oc = ψ_s(y)`, `oN = ψ_s(y_N)`, `DQ η true y y_N` (then as the argument form);
- triggered argument form: trigger in `M[n]` (TrigN), `last(y_N) ≠ 0` (lNz), low-part trichotomy (Last). -/
def OFields (v pre oc oN η : T) : Prop :=
  (fsD oc η = oN → fsD oc η < oc →
    (∃ a, oc = psi (succ a) z z ∧
      ((∀ s' y', oN = psi s' y' z → ¬ Trig v pre s' y') ∨ (∃ s' y', oN = psi s' y' z ∧ LeafPar v pre a s' y'))) ∨
    (∃ s s', oc = psi s z z ∧ oN = psi s' z z) ∨
    (∃ s y yN, oc = psi s y z ∧ oN = psi s yN z ∧ DQ η true y yN)) ∧
  (∀ s y yN, oc = psi s y z → oN = psi s yN z → DQ η true y yN → Trig v pre s y →
    Trig v pre s yN ∧
    (∀ B l lN Q, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → yN = app B (app Q lN) → DQ η false l lN → lN ≠ z) ∧
    (∀ B l lN Q, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → yN = app B (app Q lN) → DQ η false l lN →
      (split y (psi (succ s) z z)).2 = z →
      l = psi (succ s) z z ∨ (¬ lN < psi (succ s) z z ∧ ∀ q ∈ summands lN, ¬ q < psi (succ s) z z)))

/-- The argument form of the frame step from the triggered-argument fields. -/
theorem frame_step_arg {v pre s y yN η : T} (hpre : isOT pre = true) (hcot : isOT (psi s y z) = true)
    (hSN : Single (psi s yN z)) (hdy : DQ η true y yN)
    (hF : Trig v pre s y → Trig v pre s yN ∧
      (∀ B l lN Q, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → yN = app B (app Q lN) → DQ η false l lN → lN ≠ z) ∧
      (∀ B l lN Q, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → yN = app B (app Q lN) → DQ η false l lN →
        (split y (psi (succ s) z z)).2 = z →
        l = psi (succ s) z z ∨ (¬ lN < psi (succ s) z z ∧ ∀ q ∈ summands lN, ¬ q < psi (succ s) z z))) :
    FStep v pre (psi s y z) (psi s yN z) := by
  by_cases ht : Trig v pre s y
  · obtain ⟨htN, hlNz, hLast⟩ := hF ht
    exact frame_step_trigArg hcot hSN.1 (isOT_arg hcot) hdy ht htN hlNz hLast
  · refine ⟨η, frame_DQ_add hpre hSN (DQ.arg hdy) ht ?_⟩
    intro s' y' he
    obtain ⟨rfl, rfl, -⟩ := T.psi.inj he
    exact notTrig_arg hdy.lt ht

/-- **The frame step from the fields.** -/
theorem frame_step_fields {v pre oc oN η : T} (hpre : isOT pre = true) (hSc : Single oc) (hSN : Single oN)
    (hd : DQ η false oc oN) (hF : OFields v pre oc oN η) : FStep v pre oc oN := by
  obtain ⟨hcot, s, y, rfl⟩ := hSc
  refine frame_step_reduce hpre hd hSN (fun he hlt => ?_) (fun yN hyN hdy ht => ?_)
  · rcases hF.1 he hlt with ⟨a, ha, hcase⟩ | ⟨s1, s', ha, hN⟩ | ⟨s1, y1, yN, ha, hN, hdy⟩
    · obtain ⟨rfl, rfl, -⟩ := T.psi.inj ha
      rw [fsD_om_succ] at he hlt
      subst he
      exact frame_step_leaf hpre hSN hlt hcase
    · obtain ⟨rfl, rfl, -⟩ := T.psi.inj ha
      refine ⟨η, frame_DQ_add hpre hSN (by rw [← he]; exact DQ.base hlt) notTrig_z ?_⟩
      intro s'' y'' he'
      rw [hN] at he'
      obtain ⟨-, rfl, -⟩ := T.psi.inj he'
      exact notTrig_z
    · obtain ⟨rfl, rfl, -⟩ := T.psi.inj ha
      subst hN
      exact frame_step_arg hpre hcot hSN hdy (fun ht => hF.2 s y yN rfl rfl hdy ht)
  · subst hyN
    exact frame_step_arg hpre hcot hSN hdy (fun ht => hF.2 s y yN rfl rfl hdy ht)

/-- **The conjunct `hOF` of `qr_chainF.hLocE` from the frame fields** (with the standard-form facts on `D`). -/
theorem hOF_of_fields {M : Mat} {x : Nat} {ρ σ : Valn} (hx : x + 1 = M.length)
    (hPre : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → isOT (preState M ρ i L) = true)
    (hSρ : ∀ c, c ≤ x → DepX M x true c → Single (ρ.o c))
    (hSσ : ∀ c, c ≤ x → DepX M x true c → Single (σ.o c))
    (hF : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → DepX M x true c →
      ∀ η, DQ η false (ρ.o c) (σ.o c) → OFields (ρ.v i) (preState M ρ i L) (ρ.o c) (σ.o c) η) :
    ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → DepX M x true c →
      (∃ η, DQ η false (ρ.o c) (σ.o c)) →
      ∃ η', DQ η' false (psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (ρ.o c)) z)
        (psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (σ.o c)) z) := by
  intro i L c R hi hd hch hcd ⟨η, hη⟩
  have hc : c ∈ children M i := by rw [hch]; simp
  have hcx : c ≤ x := by
    have := (mem_children hc).2
    omega
  exact frame_step_fields (hPre i L c R hi hd hch) (hSρ c hcx hcd) (hSσ c hcx hcd) hη
    (hF i L c R hi hd hch hcd η hη)

end Ytosk.WfQrH3
