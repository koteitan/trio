/-
**WfInvD1: a repair of the drop residual `HDropU` (2026-10-31, analysis round).**

`HDropU` is false twice (WfReM1: its `BumpAbsC` conjunct at a `t = 1` matrix outside `Bad2`; WfReM3: the component
conjunct of its `ua` field at a `t = 2` matrix outside `Bad2`). Both failing parts are read by no consumer at those
types:
- the component conjunct `∀ g ∈ comps z (V + 1), g < ψ_{V+1}(0)` of `ua` is discarded by every drop lemma
  (`pv_of_hard*`: `obtain ⟨hwc, -⟩`); it is read only at `t = 1` (`qr_dropSeed`, `frameMapT1_take`, both with
  `entry M 2 x = 0`). Here it is guarded by `entry N 2 x = 0` (`UAg`).
- `BumpAbsC` at `t = 1` is read only to build the drop conclusion (`bump_drop` in `t1_drop_of_fields`,
  `qr_dropSeed`, `t1_main_final`); the drop conclusion follows from `BumpAbsCB` (`bump_dropB`). Here `BumpAbsC`
  is asked only at `t = 0` and at `t = 2` outside `Bad2` (`HDropUg`).
- `drop_all_hardW`: `drop_all_hardB` with the weaker `hX1` (no component conjunct), a copy of its proof.
-/
import Ytosk.V3GlobV2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hVS : VSmallF M ρ) (hVN : VSmallNew M x ρ ρ') (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
  (hHard : HardArg M x ρ ρ')
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hHard

/-- `pv_of_hardB` without the component conjunct in `hX1` (it was discarded there). -/
theorem pv_of_hardW {i : Nat} (hi : i < x) (hWC : WeakCS M x ρ ρ')
    (hBump : ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV M ρ ρ' i)
    (hX1 : ∀ k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
        WCSP M ρ i (add (vOpt ρ (par M 1 i)) one))
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
        have hwc := (hX1 k _ hixe hu hvk (by simp)).resolve_left hR
        rcases (le_iff _ _).mp (add_le_add_single (vOpt ρ (par M 1 i)) ⟨z, z, rfl⟩ ⟨sW, yW, rfl⟩ hW1)
          with hlt | heq
        · refine Or.inr ⟨⟨hlt, le_add_single _ ⟨z, z, rfl⟩, hot1⟩, hwc, ?_⟩
          by_cases hxc : par M 0 x = some i
          · by_cases hnbi : NBPar M i
            · exact Or.inr (Or.inl ⟨fun c hc _ => by have := mem_children hc; omega, hnbi,
                k, _, by omega, hu, hvk, by simp, hR⟩)
            · unfold NBPar at hnbi
              push Not at hnbi
              obtain ⟨p, g, hp, hg, hb⟩ := hnbi
              have hi2 : M.length - 2 = i := by omega
              refine Or.inr (Or.inr ⟨fun c hc _ => by have := mem_children hc; omega, ?_, ?_⟩)
              · rw [hi2]; exact ⟨k, _, by omega, hu, hvk, by simp, hR⟩
              · rw [BadPos, hi2]
                exact ⟨p, g, hp, hg, hb, by
                  rw [show M.length - 1 = x by omega]
                  exact Anc0.step hxc (Anc0.step hp (Anc0.step hg (Anc0.refl g)))⟩
          · refine Or.inl fun c hc _ => hxc ?_
            have := mem_children hc
            obtain rfl : c = x := by omega
            exact (mem_children_iff.mp hc).2
        · exact Or.inl (Or.inl heq)

/-- `drop_all_hardB` without the component conjunct in `hX1`. **The drop lemma** (modulo the bump-type frames and the absorption at `x − 1`): at every column of
`M.take x`, `o` and `v` are `⊴` the values in `M` or weakly below them, and standard. -/
theorem drop_all_hardW
    (hBump : (∀ i, i < x → (∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < x →
        PO ρ ρ' k ∧ PV M ρ ρ' k) → ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV M ρ ρ' i) ∧
      WeakCS M x ρ ρ')
    (hX1 : ∀ i k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
        WCSP M ρ i (add (vOpt ρ (par M 1 i)) one)) :
    ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have key : ∀ N, ∀ i, i < x → (rk true i ≤ N → PO ρ ρ' i) ∧ (rk false i ≤ N → PV M ρ ρ' i) := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      have hPV : ∀ i, i < x → rk false i ≤ N → PV M ρ ρ' i := by
        intro i hi hN
        obtain ⟨_, _, hR⟩ := hRk' i (by omega)
        apply pv_of_hardW hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hHard hi hBump.2
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

/-- **The absorption at `x − 1`, with the component condition only when `x` has row 2 = 0** (2026-10-31). -/
def UAg (N : Mat) (x : Nat) (σ : Valn) : Prop :=
  ∀ i k W, i + 1 = x → upg N i = some k → σ.v k = add (vOpt σ (par N 1 i)) W → W ≠ z →
    (∀ r ∈ summands (vOpt σ (par N 1 i)), r < W → Lhd z r W) ∨
      (WCSP N σ i (add (vOpt σ (par N 1 i)) one) ∧
        (entry N 2 x = 0 → SmallSelf (add (vOpt σ (par N 1 i)) one)))

/-- **`DropResHB` with `UAg`.** -/
structure DropResHBg (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  hard : HardArg N x σ σ'
  vst : VSmallNew N x σ σ'
  ws : BumpWeakSrcB N x σ σ'
  ua : UAg N x σ
  ab : BumpAbsCB N x σ

/-- **The repaired drop residual** (2026-10-31): `DropResHBg` everywhere, and `BumpAbsC` only at `t = 0` and at
`t = 2` outside `Bad2` (the places where a consumer reads it beyond the drop conclusion). -/
def HDropUg : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk →
    DropResHBg M (M.length - 1) ρ (drop1 M (M.length - 1) rk) ∧
      (entry M 1 (M.length - 1) = 0 ∨ (entry M 2 (M.length - 1) ≠ 0 ∧ ¬ Bad2 M) →
        BumpAbsC M (M.length - 1) ρ)

theorem DropResHB.toG {N : Mat} {x : Nat} {σ σ' : Valn} (h : DropResHB N x σ σ') : DropResHBg N x σ σ' :=
  ⟨h.hard, h.vst, h.ws, fun i k W hi hu hv hW => (h.ua i k W hi hu hv hW).imp id
    (fun h' => ⟨h'.1, fun _ => h'.2⟩), h.ab⟩

/-- `HDropUg` is weaker than `HDropU`. -/
theorem hDropUg_of_U (h : HDropU) : HDropUg := fun M ρ rk hM hS hE I =>
  ⟨(h M ρ rk hM hS hE I).1.toG, fun hc => (h M ρ rk hM hS hE I).2 (by
    rcases hc with h1 | ⟨_, hnb⟩
    · exact Or.inr h1
    · exact Or.inl hnb)⟩

/-- `UAg` gives the `hX1` of `drop_all_hardW`. -/
theorem UAg.x1 {N : Mat} {x : Nat} {σ : Valn} (h : UAg N x σ) :
    ∀ i k W, i + 1 = x → upg N i = some k → σ.v k = add (vOpt σ (par N 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt σ (par N 1 i)), r < W → Lhd z r W) ∨
        WCSP N σ i (add (vOpt σ (par N 1 i)) one) :=
  fun i k W hi hu hv hW => (h i k W hi hu hv hW).imp id (fun h' => h'.1)

/-- **What the `t = 1` seeds read of the absorption** (`qr_seedC_of`, `frameMapT1_takeG`), from `UAg`. -/
theorem UAg.seed {N : Mat} {x : Nat} {σ : Valn} (h : UAg N x σ) (hx2 : entry N 2 x = 0) :
    ∀ i k W, i + 1 = x → upg N i = some k → σ.v k = add (vOpt σ (par N 1 i)) W → W ≠ z →
      (∀ s ∈ summands (vOpt σ (par N 1 i)), s < W → Lhd z s W) ∨ SmallSelf (add (vOpt σ (par N 1 i)) one) :=
  fun i k W hi hu hv hW => (h i k W hi hu hv hW).imp id (fun h' => h'.2 hx2)

/-- **`UpgAbsXW0` at `t ≤ 1` outside `Bad2`** from `UAg` (as in `hDropV2W_of_U`). -/
theorem UAg.toW0 {M : Mat} {ρ : Valn} (h : UAg M (M.length - 1) ρ) (hNB : ¬ Bad2 M)
    (hC : Cons M ρ) (hx2 : entry M 2 (M.length - 1) = 0) : UpgAbsXW0 M (M.length - 1) ρ := by
  intro i k W hix hu hvk hW
  rcases h i k W hix hu hvk hW with hs | ⟨hwc, hss⟩
  · exact Or.inl hs
  by_cases hs : ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W
  · exact Or.inl hs
  refine Or.inr ⟨hwc, hss hx2, fun p g hp hg hb => ?_⟩
  by_contra hc
  apply hNB
  have hi2 : M.length - 2 = i := by omega
  refine ⟨⟨k, by rw [hi2]; exact hu⟩, p, g, by rw [hi2]; exact hp, hg, hb, Or.inl ⟨?_, ρ, hC, ?_⟩⟩
  · by_contra hn
    push Not at hn
    exact hc ⟨hn.1, hn.2⟩
  · intro hS'
    exact hs (hS' i k W (by omega) hu hvk hW)

/-- **The parent condition at `t = 2` outside `Bad2`** from `UAg` (what `old_target_of_failure` reads of
`UpgAbsXW`: the strong form or `NBParX`). -/
theorem UAg.nbx {M : Mat} {ρ : Valn} (h : UAg M (M.length - 1) ρ) (hNB : ¬ Bad2 M) (hC : Cons M ρ) :
    ∀ i k W, i + 1 = M.length - 1 → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
        (WCSP M ρ i (add (vOpt ρ (par M 1 i)) one) ∧ NBParX M (M.length - 1) i) := by
  intro i k W hix hu hvk hW
  rcases h i k W hix hu hvk hW with hs | ⟨hwc, -⟩
  · exact Or.inl hs
  by_cases hs : ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W
  · exact Or.inl hs
  refine Or.inr ⟨hwc, fun p g hp hg hb => ?_⟩
  by_contra hc
  apply hNB
  have hi2 : M.length - 2 = i := by omega
  refine ⟨⟨k, by rw [hi2]; exact hu⟩, p, g, by rw [hi2]; exact hp, hg, hb, Or.inl ⟨?_, ρ, hC, ?_⟩⟩
  · by_contra hn
    push Not at hn
    exact hc ⟨hn.1, hn.2⟩
  · intro hS'
    exact hs (hS' i k W (by omega) hu hvk hW)

/-- **The conclusion of the drop lemma from `HDropUg`**, for every standard matrix (as `hdrop_of_U`). -/
theorem hdrop_of_Ug (h : HDropUg) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (hl : 2 ≤ M.length) (I : Inv3V2 M ρ rk) :
    ∀ i, i < M.length - 1 → PO ρ (drop1 M (M.length - 1) rk) i ∧ PV M ρ (drop1 M (M.length - 1) rk) i := by
  have hE : M ≠ [] := by intro he; rw [he] at hl; simp at hl
  obtain ⟨R, _⟩ := h M ρ rk hM hS hE I
  have S := sInv_std hM hS
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  exact drop_all_hardW hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.vs R.vst I.fc I.fo
    R.hard (bump_dropB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.kd I.td R.ab R.ws) R.ua.x1

/-- **`RootBadV2` from `HDropUg` and the `t = 2` part** (as `rootBad_of_T2`). -/
theorem rootBad_of_T2g (h : HDropUg) (h2 : RootBadV2T2) : RootBadV2 := by
  intro M ρ rk hM hS hl hB I
  by_cases hx2 : entry M 2 (M.length - 1) = 0
  · exact root_drop_e2z hM hS hl I (hdrop_of_Ug h hM hS hl I) hx2
  by_cases hub : (∃ i, upg M i = some (M.length - 1)) ∨
      ∃ p, par M 0 (M.length - 1) = some p ∧ col M (M.length - 1) = bump M p
  · exact h2 M ρ rk hM hS hl hB I hx2 hub
  push Not at hub
  exact root_drop_X hM hS hl I (hdrop_of_Ug h hM hS hl I) hub.1 hub.2

end Ytosk
