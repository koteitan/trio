/- Canonical single-tail fields for QR, avoiding universal zero-tail decompositions.
This is a conditional consumer interface; its truth on all standard matrices
is not asserted here. The old QR input remains separately refuted. -/
import Ytosk.V3QRCarrierV3
import Ytosk.WfQrL12

namespace Ytosk.QRCanonical
open T WfQrL1 WfQrL2 WfQrL3 WfQrL4 WfQrL11 WfQrL12 WfQrL14 WfQrL16 WfQrH2 WfQrH3

/-- Choose one DQ witness whose new tail is the genuine nonzero single last
summand. The low-part condition is required only of that chosen witness. -/
def TailFields (s y yN : T) : Prop :=
  ∃ η B l lN Q, y = app B l ∧ (∃ s0 y0, l = psi s0 y0 z) ∧
    yN = app B (app Q lN) ∧ Single lN ∧ DQ η false l lN ∧
    (∀ q ∈ summands Q, lN ≤ q ∧ q < l) ∧
    ((split y (psi (succ s) z z)).2 = z →
      l = psi (succ s) z z ∨ (¬ lN < psi (succ s) z z ∧ ∀ q ∈ summands lN, ¬ q < psi (succ s) z z))

theorem tailFields_last {s y yN : T} (h : TailFields s y yN) :
    ∃ lN, Single lN ∧ last yN = lN := by
  obtain ⟨η,B,l,lN,Q,_,_,he,hS,_⟩ := h
  refine ⟨lN,hS,?_⟩
  obtain ⟨a,b,hl⟩ := hS.2
  rw [he,hl,← app_assoc,last_app_single]

/-- Triggered frames use the chosen witness, not an arbitrary DQ inversion. -/
theorem frame_step_tail {v pre s y yN : T}
    (hy : isOT (psi s y z) = true) (hyN : isOT (psi s yN z) = true)
    (hyot : isOT y = true) (ht : Trig v pre s y) (htN : Trig v pre s yN)
    (hF : TailFields s y yN) : FStep v pre (psi s y z) (psi s yN z) := by
  obtain ⟨η,B,l,lN,Q,ey,⟨s0,y0,hl⟩,eyN,hSingle,hdl,hQ,hLast⟩ := hF
  have hlz : lN ≠ z := single_ne_z hSingle
  have hd : DQ η true y yN := by
    rw [ey,eyN]
    exact DQ.mk hl hdl hQ
  have hYz : app Q lN ≠ z := fun he => hlz (app_eq_z he).2
  by_cases hlo : (split y (psi (succ s) z z)).2 = z
  · -- no low part in `y`
    rcases hLast hlo with hθ | hkeep
    · -- node: `l = Ω_{s+1}`
      by_cases hloN : (split yN (psi (succ s) z z)).2 = z
      · exact ⟨η, frame_DQ_trig hy hyN hd ht htN hlo hloN⟩
      · refine frame_DQ_node hy hyN ht htN hlo hloN (B := B) (by rw [ey, hθ]) ?_ ?_
        · -- `hi(y_N) = B`
          have hlt : lN < psi (succ s) z z := by rw [← hθ]; exact hdl.lt
          have hY : head (app Q lN) < psi (succ s) z z := by
            cases hQc : Q with
            | z => simpa [app] using lt_of_le_of_lt (head_le_self lN) hlt
            | psi a1 b1 c1 =>
              have := (hQ (psi a1 b1 z) (by rw [hQc]; simp [summands])).2
              rw [hθ] at this
              simpa [app, head] using this
          have hBlo : (split B (psi (succ s) z z)).2 = z := by
            apply split_snd_z_of_ge
            intro q hq
            have e := split_app (psi (succ s) z z) y
            rw [hlo, app_z_right] at e
            have : q ∈ summands (split y (psi (succ s) z z)).1 := by
              rw [e, ey, summands_app]; exact List.mem_append_left _ hq
            exact split_fst_ge _ y q this
          rw [eyN, WfQrL3.split_app_low hY hYz]
          have e2 := split_app (psi (succ s) z z) B
          rw [hBlo, app_z_right] at e2
          exact e2
        · rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self s)
    · have hyall : ∀ q ∈ summands y, ¬ q < psi (succ s) z z := by
        intro q hq
        have e := split_app (psi (succ s) z z) y
        rw [hlo, app_z_right] at e
        rw [← e] at hq
        exact split_fst_ge _ y q hq
      have hloN : (split yN (psi (succ s) z z)).2 = z := by
        rw [eyN]
        apply split_snd_z_of_ge
        intro q hq
        rw [summands_app, summands_app] at hq
        rcases List.mem_append.mp hq with hq | hq
        · apply hyall; rw [ey, summands_app]; exact List.mem_append_left _ hq
        · rcases List.mem_append.mp hq with hq | hq
          · intro hqt
            exact hkeep.1 (lt_of_le_of_lt (hQ q hq).1 hqt)
          · exact hkeep.2 q hq
      exact ⟨η, frame_DQ_trig hy hyN hd ht htN hlo hloN⟩
  · -- low part in `y`: kept
    have hlt : l < psi (succ s) z z := by
      rw [ey, hl] at hyot hlo; rw [hl]; exact last_lt_of_lo hyot hlo
    have hYl : head (app Q lN) < psi (succ s) z z := by
      cases hQc : Q with
      | z => simpa [app] using lt_of_le_of_lt (head_le_self lN) (lt_trans hdl.lt hlt)
      | psi a1 b1 c1 =>
        have := (hQ (psi a1 b1 z) (by rw [hQc]; simp [summands])).2
        simpa [app, head] using lt_trans this hlt
    have hl0 : head l < psi (succ s) z z := by rw [hl]; simpa [head] using (show psi s0 y0 z < _ by rw [← hl]; exact hlt)
    have hlnz : l ≠ z := by rw [hl]; simp
    have e1 : split yN (psi (succ s) z z) = ((split B (psi (succ s) z z)).1, app (split B (psi (succ s) z z)).2 (app Q lN)) := by
      rw [eyN, WfQrL3.split_app_low hYl hYz]
    have e2 : split y (psi (succ s) z z) = ((split B (psi (succ s) z z)).1, app (split B (psi (succ s) z z)).2 l) := by
      rw [ey, WfQrL3.split_app_low hl0 hlnz]
    have hhi : (split yN (psi (succ s) z z)).1 = (split y (psi (succ s) z z)).1 := by rw [e1, e2]
    have hloN : (split yN (psi (succ s) z z)).2 ≠ z := by
      rw [e1]; exact fun he => hYz (app_eq_z he).2
    exact ⟨η, frame_DQ_trig_lo hy hyN hd ht htN hlo hloN hhi⟩


/-- Base cases retain the old definition; the argument branch names one
canonical tail instead of quantifying over every decomposition. -/
def OFieldsTail (v pre oc oN η : T) : Prop :=
  (fsD oc η = oN → fsD oc η < oc →
    (∃ a, oc = psi (succ a) z z ∧
      ((∀ s' y', oN = psi s' y' z → ¬ Trig v pre s' y') ∨ (∃ s' y', oN = psi s' y' z ∧ LeafPar v pre a s' y'))) ∨
    (∃ s s', oc = psi s z z ∧ oN = psi s' z z) ∨
    (∃ s y yN, oc = psi s y z ∧ oN = psi s yN z ∧ DQ η true y yN)) ∧
  (∀ s y yN, oc = psi s y z → oN = psi s yN z → Trig v pre s y →
    Trig v pre s yN ∧ TailFields s y yN)

theorem frame_step_arg_tail {v pre s y yN η : T} (hpre : isOT pre = true)
    (hcot : isOT (psi s y z) = true) (hSN : Single (psi s yN z))
    (hdy : DQ η true y yN)
    (hF : Trig v pre s y → Trig v pre s yN ∧ TailFields s y yN) :
    FStep v pre (psi s y z) (psi s yN z) := by
  by_cases ht : Trig v pre s y
  · obtain ⟨htN,hTail⟩ := hF ht
    exact frame_step_tail hcot hSN.1 (isOT_arg hcot) ht htN hTail
  · refine ⟨η, frame_DQ_add hpre hSN (DQ.arg hdy) ht ?_⟩
    intro s' y' he
    obtain ⟨rfl,rfl,-⟩ := T.psi.inj he
    exact notTrig_arg hdy.lt ht
theorem frame_step_fields_tail {v pre oc oN η : T} (hpre : isOT pre = true) (hSc : Single oc) (hSN : Single oN)
    (hd : DQ η false oc oN) (hF : OFieldsTail v pre oc oN η) : FStep v pre oc oN := by
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
      exact frame_step_arg_tail hpre hcot hSN hdy (fun ht => hF.2 s y yN rfl rfl ht)
  · subst hyN
    exact frame_step_arg_tail hpre hcot hSN hdy (fun ht => hF.2 s y yN rfl rfl ht)

theorem hOF_of_fields_tail {M : Mat} {x : Nat} {ρ σ : Valn} (hx : x + 1 = M.length)
    (hPre : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → isOT (preState M ρ i L) = true)
    (hSρ : ∀ c, c ≤ x → DepX M x true c → Single (ρ.o c))
    (hSσ : ∀ c, c ≤ x → DepX M x true c → Single (σ.o c))
    (hF : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → DepX M x true c →
      ∀ η, DQ η false (ρ.o c) (σ.o c) → OFieldsTail (ρ.v i) (preState M ρ i L) (ρ.o c) (σ.o c) η) :
    ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → DepX M x true c →
      (∃ η, DQ η false (ρ.o c) (σ.o c)) →
      ∃ η', DQ η' false (psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (ρ.o c)) z)
        (psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (σ.o c)) z) := by
  intro i L c R hi hd hch hcd ⟨η, hη⟩
  have hc : c ∈ children M i := by rw [hch]; simp
  have hcx : c ≤ x := by
    have := (mem_children hc).2
    omega
  exact frame_step_fields_tail (hPre i L c R hi hd hch) (hSρ c hcx hcd) (hSσ c hcx hcd) hη
    (hF i L c R hi hd hch hcd η hη)


end Ytosk.QRCanonical
