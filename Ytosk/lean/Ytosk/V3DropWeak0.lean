import Ytosk.V3DropStrong

namespace Ytosk.DropWeak0
open T

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hVS : VSmallF M ρ) (hVN : VSmallNew M x ρ ρ') (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
  (hHard : HardArg M x ρ ρ')
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hHard

theorem pv_of_hard {i : Nat} (hi : i < x) (hWC : WeakCS M x ρ ρ')
    (hBump : ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV M ρ ρ' i)
    (hX1 : ∀ k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
        (WCSP M ρ i (add (vOpt ρ (par M 1 i)) one) ∧
          (∀ g ∈ comps z (add (vOpt ρ (par M 1 i)) one), g < psi (add (vOpt ρ (par M 1 i)) one) z z) ∧
          NBPar M i))
    (hup : ∀ k, upg (M.take x) i = some k → PV M ρ ρ' k ∧
      ∀ j ∈ children (M.take x) k, col (M.take x) j = bump (M.take x) k →
        ∀ k' ∈ children (M.take x) j, Single (ρ'.o k')) :
    PV M ρ ρ' i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : i < (M.take x).length := by omega
  have hiM : i < M.length := by omega
  have hoff := chg_off hx hC hG hC' hRk'
  by_cases hCv : ChgX M x false i
  swap
  · rw [PV, (hoff i hi).2 hCv]
    exact ⟨Or.inl (Or.inl rfl), hG.ot_v i hiM⟩
  have h1 := chgx_e1 hCv
  by_cases h2 : entry M 2 i = 0
  swap
  · exact hBump hCv h1 h2
  -- the row-1 parent does not change
  have hV : vOpt ρ' (par (M.take x) 1 i) = vOpt ρ (par M 1 i) := by
    rw [par_take M 1 i hi]
    cases hp : par M 1 i with
    | none => rfl
    | some m =>
      show ρ'.v m = ρ.v m
      have hm := par_lt M 1 i m hp
      apply (hoff m (by omega)).2
      intro hCm
      exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCm).1 rfl (by omega) |>.2.2 i hi hp
  have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  have hoot : ∀ k, ∀ j ∈ children M k, col M j = bump M k → ∀ k' ∈ children M j, isOT (ρ.o k') = true :=
    fun k j _ _ k' hk' => hG.ot_o k' (mem_children hk').2
  -- `v′(i)` when the upgrade is gone or absent
  have hv1 : upg (M.take x) i = none → ρ'.v i = sf (add (vOpt ρ (par M 1 i)) one) := by
    intro hu
    rw [(hC' i hiT).2]; unfold vRhs
    rw [entry_take M 1 hi, entry_take M 2 hi, if_neg h1, if_pos h2, hu, hV]
  by_cases hix : i + 1 < x
  · have hupT : upg (M.take x) i = upg M i := upg_take M hix
    cases hu : upg M i with
    | none =>
      have e1 := hv1 (by rw [hupT, hu])
      have e2 : ρ.v i = sf (add (vOpt ρ (par M 1 i)) one) := by
        rw [(hC i hiM).2]; unfold vRhs; rw [if_neg h1, if_pos h2, hu]
      rw [PV, e1, ← e2]
      exact ⟨Or.inl (Or.inl rfl), hG.ot_v i hiM⟩
    | some k =>
      have huT : upg (M.take x) i = some k := by rw [hupT, hu]
      obtain ⟨hPVk, hook⟩ := hup k huT
      have ek : ρ.v i = ρ.v k := v_upg_eq hC hiM h1 h2 hu hVot (hoot k)
      have ek' : ρ'.v i = ρ'.v k := v_upg_eq hC' hiT (by rw [entry_take M 1 hi]; exact h1)
        (by rw [entry_take M 2 hi]; exact h2) huT (by rw [hV]; exact hVot)
        (fun j hj hjb k' hk' => (hook j hj hjb k' hk').1)
      unfold PV
      rw [ek, ek']
      refine ⟨?_, hPVk.2⟩
      rcases hPVk.1 with h | ⟨hW, -, _⟩
      · exact Or.inl h
      · by_cases hlv : LhdE (ρ'.v k) (ρ.v k)
        · exact Or.inl hlv
        right
        refine ⟨hW, ?_, ?_⟩
        · have h' := hWC i hi (by rw [ek, ek']; exact hlv)
          rw [ek'] at h'; exact h'
        obtain ⟨m, _, _, _, hcase⟩ := upg_spec hu
        rcases hcase with rfl | ⟨hA, hki⟩
        · left
          intro c hc _
          have := leaf_of_upg_next hR0 hu c (Anc0.step (mem_children_iff.mp hc).2 (Anc0.refl i))
          have := (mem_children hc).1; omega
        · exfalso
          have hk : k < x := by omega
          have hCk : ChgX M x false k := by
            by_contra hn
            have := (hoff k hk).2 hn
            rw [this] at hW; exact lt_irrefl' _ hW.1
          exact no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
            ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCk).1 rfl hk) hk hu hA hki
  · -- `i = x − 1`
    have hixe : i + 1 = x := by omega
    have huT : upg (M.take x) i = none := by
      have : i = x - 1 := by omega
      rw [this]; exact upg_take_last M (by omega) (by omega)
    have e1 := hv1 huT
    have hot1 : isOT (add (vOpt ρ (par M 1 i)) one) = true := isOT_add hVot rfl
    unfold PV
    rw [e1, sf_ot hot1]
    refine ⟨?_, hot1⟩
    cases hu : upg M i with
    | none =>
      have e2 : ρ.v i = sf (add (vOpt ρ (par M 1 i)) one) := by
        rw [(hC i hiM).2]; unfold vRhs; rw [if_neg h1, if_pos h2, hu]
      rw [e2, sf_ot hot1]; exact Or.inl (Or.inl rfl)
    | some k =>
      have ek : ρ.v i = ρ.v k := v_upg_eq hC hiM h1 h2 hu hVot (hoot k)
      have hk := upg_lt hiM hu
      obtain ⟨m, hm1, hm2, hcol, _⟩ := upg_spec hu
      have hk1 : entry M 1 k ≠ 0 := by
        have : entry M 1 k = (col M k).2.1 := rfl
        rw [this, hcol]; exact h1
      have hk2 : entry M 2 k ≠ 0 := by
        have : entry M 2 k = (col M k).2.2 := rfl
        rw [this, hcol]; simp
      have hVk : vOpt ρ (par M 1 k) = vOpt ρ (par M 1 i) := by rw [hm1, hm2]
      obtain ⟨sW, yW, hvk, hWot, hW1⟩ := v_bump_form hC hk hk1 hk2 (by rw [hVk]; exact hVot) (hoot k)
      rw [hVk] at hvk
      rw [ek, hvk]
      by_cases hR : ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < psi sW yW z → Lhd z r (psi sW yW z)
      · have := v_frame_xm1 hVot hWot hW1 (fun r hr _ hlt => hR r hr hlt)
        rw [sf_ot hot1] at this
        exact Or.inl this
      · -- the weak alternative: `v′ = V + 1 < V + W`, `x` is the only possible counted child
        obtain ⟨hwc, -, hnb⟩ := (hX1 k _ hixe hu hvk (by simp)).resolve_left hR
        rcases (le_iff _ _).mp (add_le_add_single (vOpt ρ (par M 1 i)) ⟨z, z, rfl⟩ ⟨sW, yW, rfl⟩ hW1)
          with hlt | heq
        · refine Or.inr ⟨⟨hlt, le_add_single _ ⟨z, z, rfl⟩, hot1⟩, hwc,
            Or.inr ⟨fun c hc _ => ?_, hnb, k, _, by omega, hu, hvk, by simp, hR⟩⟩
          have := mem_children hc; omega
        · exact Or.inl (Or.inl heq)

/-- **The drop lemma** (modulo the bump-type frames and the absorption at `x − 1`): at every column of
`M.take x`, `o` and `v` are `⊴` the values in `M` or weakly below them, and standard. -/
theorem drop_all_hard
    (hBump : (∀ i, i < x → (∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < x →
        PO ρ ρ' k ∧ PV M ρ ρ' k) → ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV M ρ ρ' i) ∧
      WeakCS M x ρ ρ')
    (hX1 : ∀ i k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
        (WCSP M ρ i (add (vOpt ρ (par M 1 i)) one) ∧
          (∀ g ∈ comps z (add (vOpt ρ (par M 1 i)) one), g < psi (add (vOpt ρ (par M 1 i)) one) z z) ∧
          NBPar M i)) :
    ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have key : ∀ N, ∀ i, i < x → (rk true i ≤ N → PO ρ ρ' i) ∧ (rk false i ≤ N → PV M ρ ρ' i) := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      have hPV : ∀ i, i < x → rk false i ≤ N → PV M ρ ρ' i := by
        intro i hi hN
        obtain ⟨_, _, hR⟩ := hRk' i (by omega)
        apply pv_of_hard hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hHard hi hBump.2
        · intro hCv h1 h2
          apply hBump.1 i hi _ hCv h1 h2
          intro j hj hjb k hk hkx
          have hjx : j < x := by have := (mem_children hk).1; omega
          have hjT : j ∈ children (M.take x) i := by
            rw [children_take, List.mem_filter]; exact ⟨hj, by simpa using hjx⟩
          have hkT : k ∈ children (M.take x) j := by
            rw [children_take, List.mem_filter]; exact ⟨hk, by simpa using hkx⟩
          have hlt := (hR (by rw [entry_take M 1 hi]; exact h1)).2.2 (by rw [entry_take M 2 hi]; exact h2)
            j hjT (by rw [col_take M hjx, bump_take M hi]; exact hjb) k hkT
          have hlt2 := (hRk' k (by omega)).1
          exact ⟨(ih _ (by omega) k hkx).1 (Nat.le_refl _), (ih _ (by omega) k hkx).2 (Nat.le_refl _)⟩
        · exact fun k W => hX1 i k W
        · intro k hk
          have h1 : entry (M.take x) 1 i ≠ 0 := by
            intro he; unfold upg at hk; rw [if_pos (Or.inl he)] at hk; cases hk
          have h2 : entry (M.take x) 2 i = 0 := by
            by_contra he
            have := upg_target_e2 hk
            unfold upg at hk
            split at hk
            · cases hk
            · rename_i hc
              have hz := hZ2 i
              rw [entry_take M 2 hi] at he hc
              exact hc (Or.inr (Or.inl (by omega)))
          have hlt := (hR h1).2.1 h2 k hk
          have hkx : k < x := by have := upg_lt (show i < (M.take x).length by omega) hk; omega
          refine ⟨(ih _ (by omega) k hkx).2 (Nat.le_refl _), fun j hj hjb k' hk' => ?_⟩
          have hk'x : k' < x := by have := (mem_children hk').2; omega
          have hk1 : entry (M.take x) 1 k ≠ 0 := by
            obtain ⟨m, _, _, hcol, _⟩ := upg_spec hk
            have : entry (M.take x) 1 k = (col (M.take x) k).2.1 := rfl
            rw [this, hcol]; exact h1
          have hk2 : entry (M.take x) 2 k ≠ 0 := by
            obtain ⟨m, _, _, hcol, _⟩ := upg_spec hk
            have : entry (M.take x) 2 k = (col (M.take x) k).2.2 := rfl
            rw [this, hcol]; simp
          have hlt2 := (hRk' k (by omega)).2.2 hk1 |>.2.2 hk2 j hj hjb k' hk'
          exact ((ih _ (by omega) k' hk'x).1 (Nat.le_refl _)).2
      refine fun i hi => ⟨fun hN => ?_, hPV i hi⟩
      obtain ⟨hvo, hc, _⟩ := hRk' i (by omega)
      apply po_of_hard hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hHard hi
      · exact hPV i hi (by omega)
      · intro c hcT hcnt
        have hlt := hc c hcT hcnt.1 hcnt.2
        have hcx : c < x := by have := (mem_children hcT).2; omega
        have hlt2 := (hRk' c (by omega)).1
        exact ⟨(ih _ (by omega) c hcx).1 (Nat.le_refl _), (ih _ (by omega) c hcx).2 (Nat.le_refl _)⟩
  intro i hi
  exact ⟨(key _ i hi).1 (Nat.le_refl _), (key _ i hi).2 (Nat.le_refl _)⟩

end
#print axioms drop_all_hard
end Ytosk.DropWeak0
