/-
**WfDrE1: the drop lemma with the weak component condition `WCS2` (2026-10-31).**

The drop conclusion `PV` is false on 19 standard matrices of graftD (tmp/wf/WfInvD, 37 and 40 columns; all of them
satisfy every field of `Inv3V2`, tmp/wf/WfDrE/aud19.out): its weak alternative asks `WCSP`, i.e. the components of
`v′(i)` at the levels `u ≤ v(P_0 i)` are countable (`< Ω_1`) or dominated by a component of `v(P_0 i)`. At the
witness `v′(35) = V + 1` has the component `Ω_{ψ(2)}` (inside a `ψ_0`), which is neither.

The only reader of the component condition is `lhd_weak_childA` (through `self_small_weakA`), and it needs only
`g ≤ ψ_{w′}(0)`, not `g < Ω_1`. `WCS2` asks exactly that. `PV2` / `WCSP2` / `WeakCS2` are `PV` / `WCSP` / `WeakCS`
with `WCS2`; `PV → PV2`. Measured (tmp/wf/WfDrE/pv2.py): `PV2` holds on all 19 failures of `PV` and everywhere else.

This file: the frame lemmas with `WCS2`, `o_frame_eval2`, `po_of_hard2`, `pv_of_hardW2`, `drop_all_hardW2`
(copies of the `WCS` versions with the weaker condition).
-/
import Ytosk.WfInvD1

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The weak component condition**: components of `w` at the levels `u ≤ a` are at most `Ω_w = ψ_w(0)` or
dominated by a component of `a`. (`WCS` has `g < Ω_1` in place of `g ≤ ψ_w(0)`.) -/
def WCS2 (a w : T) : Prop := ∀ u, ¬ lt a u = true → ∀ g ∈ comps u w, g ≤ psi w z z ∨ ∃ d ∈ comps u a, g ≤ d

theorem WCS.toWCS2 {a w : T} (h : WCS a w) (h1 : one ≤ w) : WCS2 a w :=
  fun u hu g hg => (h u hu g hg).imp (fun h' => le_of_lt (lt_of_lt_of_le h' (Om_one_le_psi h1))) id

theorem WCS2.of_cs {w : T} (h : CS w) (h1 : one ≤ w) (a : T) : WCS2 a w := (WCS.of_cs h a).toWCS2 h1

/-- **A weak child, up to the parent's components** (`self_small_weakA` with `WCS2`). -/
theorem self_small_weakA2 {a w' : T} (hcs : WCS2 a w') :
    ∀ u, ¬ lt a u = true → ∀ g ∈ comps u (psi w' z z), g ≤ psi w' z z ∨ ∃ d ∈ comps u a, g ≤ d := by
  intro u hu g hg
  simp only [comps, List.mem_append] at hg
  rcases hg with hg | hg
  · split at hg
    · simp at hg
    · simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | h | h
      · exact Or.inl (z_le _)
      · simp at h
      · exact hcs u hu g h
  · simp at hg

/-- **The `o` frame with a weak last child**: the new child is `ψ_{w′}(0)` (no rewrite), the relation
of the old side to the state without the child (`hdrop`) is a hypothesis. -/
theorem o_frame_weakA2 {a w' w F : T} {L : List T}
    (hs' : ∀ t ∈ L ++ [psi w' z z], Single t) (hp' : (L ++ [psi w' z z]).Pairwise (fun a b => b ≤ a))
    (hW : WkVA w' w) (hWC : WCS2 a w') (hdrop : LhdE (psi a (spArg a z (sumN L)) z) (psi a F z))
    (hlt : app (spArg a z (sumN L)) (psi w' z z) < F) :
    LhdE (psi a (spArg a z (sumN (L ++ [psi w' z z]))) z) (psi a F z) := by
  set B := spArg a z (sumN L) with hB
  have hc : Single (psi w' z z) := hs' _ (by simp)
  have e2 : sumN (L ++ [psi w' z z]) = app (sumN L) (psi w' z z) := by
    rw [sumN_append_dec hs' hp']
    congr 1
    show sf (add z (psi w' z z)) = psi w' z z
    rw [add_z_left]; exact sf_ot hc.1
  have hL := sumN_dec L (fun t ht => hs' t (List.mem_append_left _ ht)) (List.pairwise_append.mp hp').1
  have hBge : ∀ q ∈ summands B, psi w' z z ≤ q := by
    apply spArg_summands_ge ⟨w', z, rfl⟩ (sumN L) z hL.1
    · rw [hL.2]; intro q hq
      exact (List.pairwise_append.mp hp').2.2 q hq _ (by simp)
    · simp [summands]
  have estep : spArg a z (sumN (L ++ [psi w' z z])) = app B (psi w' z z) := by
    rw [e2, spArg_app, spArg_single, step_leaf, ← hB]
    exact add_eq_app_of_ge ⟨w', z, rfl⟩ B hBge
  have hBlt : B < app B (psi w' z z) := by
    have := app_lt_app_left B (show z < psi w' z z from T.z_lt_psi _ _ _)
    rwa [app_z_right] at this
  rw [estep]
  right
  rcases hdrop with he | hl
  · exfalso
    simp only [psi.injEq] at he
    have := lt_trans hBlt hlt
    rw [he.2.1] at this; exact lt_irrefl' _ this
  · exact lhd_weak_childA hl (by simp)
      (fun u hu g hg => (self_small_weakA2 hWC u hu g hg).imp
        (fun h => le_trans h (le_app_of_ge B hBge)) id) hlt

/-- `WCSP` with `WCS2`. -/
def WCSP2 (M : Mat) (ρ : Valn) (i : Nat) (w : T) : Prop :=
  CS w ∨ WCS2 (vOpt ρ (par M 0 i)) w

theorem WCSP2.wcs2 {M : Mat} {ρ : Valn} {i p : Nat} {w : T} (h : WCSP2 M ρ i w) (h1 : one ≤ w)
    (hp : par M 0 i = some p) : WCS2 (ρ.v p) w := by
  rcases h with h | h
  · exact WCS2.of_cs h h1 _
  · rw [hp] at h; exact h

theorem WCSP.toWCSP2 {M : Mat} {ρ : Valn} {i : Nat} {w : T} (h : WCSP M ρ i w) (h1 : one ≤ w) :
    WCSP2 M ρ i w :=
  h.imp id (fun h' => h'.toWCS2 h1)

/-- **The claim at a `v` call, with `WCS2`.** -/
def PV2 (M : Mat) (ρ ρ' : Valn) (i : Nat) : Prop :=
  (LhdE (ρ'.v i) (ρ.v i) ∨
    (WkVA (ρ'.v i) (ρ.v i) ∧ WCSP2 M ρ i (ρ'.v i) ∧ CntX M ρ i)) ∧
    isOT (ρ'.v i) = true

theorem PV.toPV2 {M : Mat} {ρ ρ' : Valn} {i : Nat} (h : PV M ρ ρ' i) : PV2 M ρ ρ' i :=
  ⟨h.1.imp id (fun ⟨hW, hc, hx⟩ => ⟨hW, hc.toWCSP2 hW.2.1, hx⟩), h.2⟩

/-- **Hypothesis on the drop, with `WCS2`.** -/
def WeakCS2 (M : Mat) (x : Nat) (ρ ρ' : Valn) : Prop :=
  ∀ i, i < x → ¬ LhdE (ρ'.v i) (ρ.v i) → WCSP2 M ρ i (ρ'.v i)

/-- `rel_of_po_pv` with `PV2`. -/
theorem rel_of_po_pv2 {M : Mat} {ρ ρ' : Valn} {c i : Nat} (hPO : PO ρ ρ' c) (hPV : PV2 M ρ ρ' c)
    (hp : par M 0 c = some i) (hvT : ∀ s y, ρ'.o c = psi s y z → s = ρ'.v c)
    (hvM : ∀ s y, ρ.o c = psi s y z → s = ρ.v c) :
    LhdE (ρ'.o c) (ρ.o c) ∨ (WkOA (ρ'.o c) (ρ.o c) ∧
      ∀ w', ρ'.o c = psi w' z z → WCS2 (ρ.v i) w') := by
  rcases hPO.1 with h | ⟨hW, -⟩
  · exact Or.inl h
  rcases hPV.1 with hl | ⟨hWV, hwc, _⟩
  · left
    obtain ⟨w', w, X, h1, h2, _⟩ := hW
    rw [h1, h2, hvT _ _ h1, hvM _ _ h2]
    exact lhdE_oq_v hl
  · right
    refine ⟨hW, fun w' h' => ?_⟩
    rw [hvT _ _ h']
    exact hwc.wcs2 hWV.2.1 hp

/-- **The `o` frame where `v` does not change**: the counted children of `M.take x` are those of `M`
up to a tail, and only the last one changes. -/
theorem o_frame_eval2 {M : Mat} {x : Nat} {ρ ρ' : Valn} {i cs : Nat} {Lc Tl : List Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hF : FrameClosed M ρ)
    (hC' : Cons (M.take x) ρ') (hiT : i < (M.take x).length) (hiM : i < M.length)
    (hv : ρ'.v i = ρ.v i)
    (hclT : CL (M.take x) i = Lc ++ [cs]) (hcl : CL M i = Lc ++ [cs] ++ Tl)
    (hsame : ∀ d ∈ Lc, ρ'.o d = ρ.o d)
    (hcs' : Single (ρ'.o cs))
    (hrel : LhdE (ρ'.o cs) (ρ.o cs) ∨ (WkOA (ρ'.o cs) (ρ.o cs) ∧
      ∀ w', ρ'.o cs = psi w' z z → WCS2 (ρ.v i) w'))
    (hss : ∀ s y s' y', ρ.o cs = psi s y z → ρ'.o cs = psi s' y' z → y' ≠ z → s' = s) :
    LhdE (ρ'.o i) (ρ.o i) := by
  set a := ρ.v i with ha
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
  rw [hcl] at hsM hpM
  simp only [List.map_append, List.map_cons, List.map_nil] at hsM hpM
  set Lv := Lc.map ρ.o with hLv
  set Tv := Tl.map ρ.o with hTv
  have hsL : ∀ t ∈ Lv, Single t := fun t ht => hsM t (by simp [ht])
  have hcsS : Single (ρ.o cs) := hsM _ (by simp)
  have hsT : ∀ t ∈ Tv, Single t := fun t ht => hsM t (by simp [ht])
  have hp1 := List.pairwise_append.mp hpM
  have hpL : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp1.1).1
  have hLc : ∀ t ∈ Lv, ρ.o cs ≤ t := fun t ht =>
    (List.pairwise_append.mp hp1.1).2.2 t ht _ (by simp)
  have hpcT : (ρ.o cs :: Tv).Pairwise (fun a b => b ≤ a) := by
    refine List.pairwise_cons.mpr ⟨fun t ht => hp1.2.2 _ (by simp) t ht, hp1.2.1⟩
  have hsC : ∀ t ∈ ρ.o cs :: Tv, Single t := fun t ht => by
    rcases List.mem_cons.mp ht with h | h
    · rw [h]; exact hcsS
    · exact hsT t h
  have hLC : ∀ u ∈ ρ.o cs :: Tv, u ≤ ρ.o cs := fun u hu => by
    rcases List.mem_cons.mp hu with h | h
    · rw [h]
    · exact hp1.2.2 _ (by simp) u h
  have hsLc : ∀ t ∈ Lv ++ [ρ.o cs], Single t := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hsL t h
    · simp at h; rw [h]; exact hcsS
  have hpLc : (Lv ++ [ρ.o cs]).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_append.mpr ⟨hpL, by simp, fun t ht b hb => by simp at hb; rw [hb]; exact hLc t ht⟩
  -- the value in `M.take x`
  have hmapT : (CL (M.take x) i).map ρ'.o = Lv ++ [ρ'.o cs] := by
    rw [hclT, List.map_append, List.map_singleton, hLv]
    congr 1
    exact List.map_congr_left hsame
  have hle' : ρ'.o cs ≤ ρ.o cs := by
    rcases hrel with h | ⟨h, _⟩
    · exact h.le
    · exact DRelOA.le (Or.inr h)
  have hs' : ∀ t ∈ Lv ++ [ρ'.o cs], Single t := by
    intro t ht; rcases List.mem_append.mp ht with ht | ht
    · exact hsL t ht
    · simp at ht; rw [ht]; exact hcs'
  have hp' : (Lv ++ [ρ'.o cs]).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_append.mpr ⟨hpL, by simp, fun t ht b hb => by
      simp at hb; rw [hb]; exact le_trans hle' (hLc t ht)⟩
  have hvot : isOT a = true := hG.ot_v i hiM
  have ho' : ρ'.o i = psi a (spArg a z (sumN (Lv ++ [ρ'.o cs]))) z := by
    have := o_cl_loc hC' hiT (by rw [hv]; exact hvot)
      (fun c hc => by
        have : ρ'.o c ∈ (CL (M.take x) i).map ρ'.o := List.mem_map_of_mem hc
        rw [hmapT] at this; exact hs' _ this)
      (by rw [hmapT]; exact hp')
    rw [this, hmapT, hv]
  have ho : ρ.o i = psi a (spArg a z (sumN (Lv ++ [ρ.o cs] ++ Tv))) z := by
    rw [o_spArg hC hG hiM, cvals_eq_map hC hG i, hcl]
    simp only [List.map_append, List.map_singleton]
    rfl
  rw [ho', ho]
  set B := spArg a z (sumN Lv) with hB
  have hLs := sumN_dec Lv hsL hpL
  -- the state before `cs` is above the children
  have hBge : ∀ t, Single t → t ≤ ρ.o cs → ∀ q ∈ summands B, t ≤ q := by
    intro t ht htc
    obtain ⟨s0, y0, rfl⟩ := ht.2
    apply spArg_summands_ge ⟨s0, y0, rfl⟩ (sumN Lv) z hLs.1
    · rw [hLs.2]; intro q hq; exact le_trans htc (hLc q hq)
    · simp [summands]
  have hCL : CL M i = Lc ++ cs :: Tl := by rw [hcl]; simp
  obtain ⟨s, y, hsy⟩ := hcsS.2
  rcases hrel with hrel | hW
  · -- `⊴` child: one frame, then the tail
    obtain ⟨s', y', hs'y'⟩ := hcs'.2
    rw [hsy, hs'y'] at hrel
    have hc := hcsS.1; rw [hsy] at hc
    have hc' := hcs'.1; rw [hs'y'] at hc'
    have hN := node_lhdD (a := a) (B := B) hc hc' hrel (hBge _ hcsS (le_refl _) |> fun h => by
        rw [hsy] at h; exact h) (hss s y s' y' hsy hs'y')
      (fun hr => hF i hiM Lc cs Tl hCL s y hsy hr)
    have hstate : spArg a z (sumN ((Lc ++ [cs]).map ρ.o)) = step a B s y z := by
      rw [List.map_append, List.map_singleton, ← hLv, sumN_append_dec hsLc hpLc,
        sumN_singleton hcsS, spArg_app, hsy, spArg_single]
    have hTcl := tailcl_of_frame hC hG hF hiM Tl (Lc ++ [cs]) (by rw [hcl])
    rw [hstate] at hTcl
    have hT := drop_tail a Tv (step a B s y z) hsT hp1.2.1
      (fun u hu q hq => by
        obtain ⟨s2, y2, hu2⟩ := (hsT u hu).2
        have := spArg_summands_ge (a := a) (c := u) ⟨s2, y2, hu2⟩ (psi s y z) B hc
          (by intro q2 hq2; simp [summands] at hq2; rw [hq2, ← hsy]; exact hp1.2.2 _ (by simp) u hu)
          (hBge u (hsT u hu) (hp1.2.2 _ (by simp) u hu))
        rw [spArg_single] at this
        exact this q hq) hTcl
    rw [hsy, hs'y']
    rw [hs'y'] at hs' hp'
    rw [hsy] at hsM hpM
    exact o_frame_term (L := Lv) (Tl := Tv) hsM hpM hs' hp' hN hT
  · -- weak child: the new child is a leaf `ψ_{w′}(0)`, the old child `ψ_s(y)` is arbitrary
    obtain ⟨⟨w', w, X, hw', hw, hWk⟩, hwc⟩ := hW
    have hWC := hwc w' hw'
    rw [hsy] at hw; simp only [psi.injEq] at hw; obtain ⟨rfl, rfl, -⟩ := hw
    have hc : isOT (psi s y z) = true := by rw [← hsy]; exact hcsS.1
    have hBc : ∀ q ∈ summands B, psi s y z ≤ q := by
      have := hBge _ hcsS (le_refl _); rwa [hsy] at this
    have hF' : spArg a z (sumN (Lv ++ [ρ.o cs] ++ Tv)) = spArg a B (sumN (ρ.o cs :: Tv)) := by
      rw [List.append_assoc, show [ρ.o cs] ++ Tv = ρ.o cs :: Tv from rfl,
        sumN_append_dec (fun t ht => hsM t (by simpa using ht)) (by simpa using hpM), spArg_app]
    rw [hF']
    have hTcl := tailcl_of_frame hC hG hF hiM (cs :: Tl) Lc (by rw [hCL])
    have hdrop := drop_tail a (ρ.o cs :: Tv) B hsC hpcT
      (fun u hu q hq => hBge u (hsC u hu) (hLC u hu) q hq) (by simpa using hTcl)
    -- the old state after `cs` is `step a B w X`, and the rest only grows
    have hstate : spArg a z (sumN ((Lc ++ [cs]).map ρ.o)) = step a B s y z := by
      rw [List.map_append, List.map_singleton, ← hLv, sumN_append_dec hsLc hpLc,
        sumN_singleton hcsS, spArg_app, hsy, spArg_single]
    have hTcl2 := tailcl_of_frame hC hG hF hiM Tl (Lc ++ [cs]) (by rw [hcl])
    rw [hstate] at hTcl2
    have hT := drop_tail a Tv (step a B s y z) hsT hp1.2.1
      (fun u hu q hq => by
        obtain ⟨s2, y2, hu2⟩ := (hsT u hu).2
        have := spArg_summands_ge (a := a) (c := u) ⟨s2, y2, hu2⟩ (psi s y z) B hc
          (by intro q2 hq2; simp [summands] at hq2; rw [hq2, ← hsy]; exact hp1.2.2 _ (by simp) u hu)
          (hBge u (hsT u hu) (hp1.2.2 _ (by simp) u hu))
        rw [spArg_single] at this
        exact this q hq) hTcl2
    have hgrow : step a B s y z ≤ spArg a B (sumN (ρ.o cs :: Tv)) := by
      have e : spArg a B (sumN (ρ.o cs :: Tv)) = spArg a (step a B s y z) (sumN Tv) := by
        rw [sumN_cons_dec hsC hpcT, hsy,
          show app (psi s y z) (sumN Tv) = psi s y (sumN Tv) from rfl, spArg_cons, step_rest a B s y (sumN Tv) z]
      rw [e]
      have := hT.le
      rcases (le_iff _ _).mp this with h | h
      · rw [psi_lt_psi_z_iff] at h
        rcases h with h | ⟨_, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact le_of_lt h
      · simp only [psi.injEq] at h; exact (le_iff _ _).mpr (Or.inr h.2.1)
    have hlt : app B (psi w' z z) < spArg a B (sumN (ρ.o cs :: Tv)) :=
      lt_of_lt_of_le (leaf_lt_step hc hBc (psi_lt_psi_z_iff.mpr (Or.inl hWk.1))) hgrow
    rw [hw'] at hs' hp'
    rw [hw']
    exact o_frame_weakA2 hs' hp' hWk hWC hdrop hlt

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hVS : VSmallF M ρ) (hVN : VSmallNew M x ρ ρ') (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
  (hHard : HardArg M x ρ ρ')
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hHard

/-- **One `o` step of the drop.** -/
theorem po_of_hard2 {i : Nat} (hi : i < x) (hv : PV2 M ρ ρ' i)
    (hch : ∀ c ∈ children (M.take x) i, Counted (M.take x) i c → PO ρ ρ' c ∧ PV2 M ρ ρ' c) :
    PO ρ ρ' i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : i < (M.take x).length := by omega
  have hiM : i < M.length := by omega
  have hoff := chg_off hx hC hG hC' hRk'
  unfold PO
  by_cases hCo : ChgX M x true i
  swap
  · rw [(hoff i hi).1 hCo]
    exact ⟨Or.inl (Or.inl rfl), single_o hC hG hiM⟩
  by_cases hCv : ChgX M x false i
  · -- `v(i)` changes: no counted child in `M.take x`
    have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl hi
    have ho' := o_of_no_counted hC' hiT hv.2 hT.2.1
    refine ⟨?_, by rw [ho']; exact ⟨by rw [isOT_psi_iff]; exact ⟨hv.2, rfl, rfl, z_le _,
      fun g hg => by simp [comps] at hg⟩, _, _, rfl⟩⟩
    by_cases hl : LhdE (ρ'.v i) (ρ.v i)
    · rw [ho', o_spArg hC hG hiM]; exact Or.inl (lhdE_oq_v hl)
    rcases hv.1 with h | ⟨hW, -, -⟩
    · exact absurd h hl
    · right
      refine ⟨?_, Or.inr hl⟩
      rw [ho', o_spArg hC hG hiM]
      exact ⟨_, _, _, rfl, rfl, hW⟩
  · -- `v(i)` does not change
    have hv' : ρ'.v i = ρ.v i := (hoff i hi).2 hCv
    obtain ⟨Tl, hTl⟩ := cl_prefix hx hR0 hZ2 hSD hZ1 hUAT hi
    have hvot : isOT (ρ.v i) = true := hG.ot_v i hiM
    rcases List.eq_nil_or_concat (CL (M.take x) i) with hnil | ⟨Lc, cs, hcl⟩
    · have hn : ∀ c ∈ children (M.take x) i, ¬ Counted (M.take x) i c := by
        intro c hc hcnt
        have : c ∈ CL (M.take x) i := by unfold CL; exact List.mem_filter.mpr ⟨hc, by simpa using hcnt⟩
        rw [hnil] at this; simp at this
      refine ⟨Or.inl (o_frame_empty hC hG hF hC' hiT hiM hv' hnil), ?_⟩
      rw [o_of_no_counted hC' hiT (by rw [hv']; exact hvot) hn]
      exact ⟨by rw [isOT_psi_iff]; exact ⟨by rw [hv']; exact hvot, rfl, rfl, z_le _,
        fun g hg => by simp [comps] at hg⟩, _, _, rfl⟩
    · rw [List.concat_eq_append] at hcl
      have hcsT : cs ∈ children (M.take x) i ∧ Counted (M.take x) i cs := by
        have : cs ∈ CL (M.take x) i := by rw [hcl]; simp
        unfold CL at this; rw [List.mem_filter] at this; exact ⟨this.1, by simpa using this.2⟩
      obtain ⟨hPOc, hPVc⟩ := hch cs hcsT.1 hcsT.2
      -- the earlier counted children do not change
      have hsame : ∀ d ∈ Lc, ρ'.o d = ρ.o d := by
        intro d hd
        have hdT : d ∈ CL (M.take x) i := by rw [hcl]; simp [hd]
        have hdc : d ∈ children (M.take x) i := by unfold CL at hdT; exact (List.mem_filter.mp hdT).1
        have hdcs : d < cs := by
          have hs := (children_sorted (M.take x) i).filter (fun c => decide (Counted (M.take x) i c))
          change (CL (M.take x) i).Pairwise _ at hs
          rw [hcl] at hs
          exact (List.pairwise_append.mp hs).2.2 d hd cs (by simp)
        have hdx : d < x := by
          rw [children_take, List.mem_filter] at hdc; simpa using hdc.2
        by_contra hne
        have hCd : ChgX M x true d := by
          by_contra hn; exact hne ((hoff d hdx).1 hn)
        exact chg_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hdc hCd cs hcsT.1 hdcs hcsT.2
      have hclM : CL M i = Lc ++ [cs] ++ Tl := by rw [hTl, hcl]
      have hcsM0 : cs < M.length := by
        have := (mem_children (cl_mem_children (show cs ∈ CL M i by rw [hclM]; simp))).2; omega
      have hcsx0 : cs < (M.take x).length := (mem_children hcsT.1).2
      have hvM : ∀ s y, ρ.o cs = psi s y z → s = ρ.v cs := by
        intro s y h
        obtain ⟨y0, hy0⟩ := o_psi_sub hC hcsM0
        rw [h] at hy0; simp only [psi.injEq] at hy0
        rw [hy0.1, sf_ot (hG.ot_v cs hcsM0)]
      have hvT : ∀ s y, ρ'.o cs = psi s y z → s = ρ'.v cs := by
        intro s y h
        obtain ⟨y0, hy0⟩ := o_psi_sub hC' hcsx0
        rw [h] at hy0; simp only [psi.injEq] at hy0
        rw [hy0.1, sf_ot hPVc.2]
      have hfr := hVS i hiM Lc cs Tl (by rw [hclM]; simp)
      have hchgv : ρ'.v cs ≠ ρ.v cs → ρ'.o cs = psi (ρ'.v cs) z z := by
        intro hvs
        have hCv : ChgX M x false cs := by
          by_contra hn; exact hvs ((hoff cs (by rw [hlenT] at hcsx0; exact hcsx0)).2 hn)
        have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl (by rw [hlenT] at hcsx0; exact hcsx0)
        exact o_of_no_counted hC' hcsx0 hPVc.2 hT.2.1
      have hssT : ∀ s y s' y', ρ.o cs = psi s y z → ρ'.o cs = psi s' y' z → y' ≠ z → s' = s := by
        intro s y s' y' h h' hy'
        rw [hvT s' y' h', hvM s y h]
        by_contra hvs
        rw [hchgv hvs] at h'; simp only [psi.injEq] at h'; exact hy' h'.2.1.symm
      have hsubA : ∀ s' y', ρ'.o cs = psi s' y' z → ∀ g ∈ comps (ρ.v i) s',
          g ≤ psi s' z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) := by
        intro s' y' h'
        rw [hvT s' y' h']
        by_cases hvs : ρ'.v cs = ρ.v cs
        · rw [hvs]; exact hfr
        · exact hVN i hi Lc cs hcl hvs
      have hpar : par M 0 cs = some i := by
        have := (mem_children_iff.mp hcsT.1).2
        rwa [par_take M 0 cs (by have := (mem_children hcsT.1).2; rw [List.length_take] at this; omega)] at this
      refine ⟨Or.inl (o_frame_eval2 hC hG hF hC' hiT hiM hv' hcl hclM hsame hPOc.2
        (rel_of_po_pv2 hPOc hPVc hpar hvT hvM) hssT), ?_⟩
      -- `o′(i)` is standard
      have hcsM : cs < M.length := by
        have := (mem_children (cl_mem_children (show cs ∈ CL M i by rw [hclM]; simp))).2; omega
      obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
      rw [hclM] at hsM hpM
      simp only [List.map_append, List.map_cons, List.map_nil] at hsM hpM
      have hle' : ρ'.o cs ≤ ρ.o cs := by
        rcases hPOc.1 with h | ⟨h, -⟩
        · exact h.le
        · exact DRelOA.le (Or.inr h)
      have hp1 := List.pairwise_append.mp hpM
      have hLc : ∀ t ∈ Lc.map ρ.o, ρ.o cs ≤ t := fun t ht =>
        (List.pairwise_append.mp hp1.1).2.2 t ht _ (by simp)
      have hmapT : (CL (M.take x) i).map ρ'.o = Lc.map ρ.o ++ [ρ'.o cs] := by
        rw [hcl, List.map_append, List.map_singleton]
        congr 1; exact List.map_congr_left hsame
      have hsT : ∀ c ∈ CL (M.take x) i, Single (ρ'.o c) := by
        intro c hc
        rw [hcl] at hc
        rcases List.mem_append.mp hc with hc | hc
        · rw [hsame c hc]; exact hsM _ (by simp only [List.mem_append, List.mem_map, List.mem_cons]; exact Or.inl (Or.inl ⟨c, hc, rfl⟩))
        · simp at hc; rw [hc]; exact hPOc.2
      have hpT : ((CL (M.take x) i).map ρ'.o).Pairwise (fun a b => b ≤ a) := by
        rw [hmapT]
        exact List.pairwise_append.mpr ⟨(List.pairwise_append.mp hp1.1).1, by simp,
          fun t ht b hb => by simp at hb; rw [hb]; exact le_trans hle' (hLc t ht)⟩
      obtain ⟨s', y', hs'y'⟩ := hPOc.2.2
      have hform := o_last_form hC' hiT (by rw [hv']; exact hvot) hcl hsT hpT hs'y'
      have hLm : Lc.map ρ'.o = Lc.map ρ.o := List.map_congr_left hsame
      rw [hform, hLm, hv']
      refine ⟨?_, _, _, rfl⟩
      have hBot := hFO i hiM Lc cs Tl (by rw [hclM]; simp)
      have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (by simp [ht])) (List.pairwise_append.mp hp1.1).1
      have hBge : ∀ t, Single t → t ≤ ρ.o cs →
          ∀ q ∈ summands (spArg (ρ.v i) z (sumN (Lc.map ρ.o))), t ≤ q := by
        intro t ht htc
        obtain ⟨s0, y0, rfl⟩ := ht.2
        apply spArg_summands_ge ⟨s0, y0, rfl⟩ _ z hLs.1
        · rw [hLs.2]; intro q hq; exact le_trans htc (hLc q hq)
        · simp [summands]
      rcases hPOc.1 with hrelL | ⟨⟨w1, w2, X, e1, _, _⟩, _⟩
      · -- a `⊴` child: one frame by `node_ot_hard`
        obtain ⟨s, y, hsy⟩ := (single_o hC hG hcsM).2
        have hcsS := single_o hC hG hcsM
        rw [hsy] at hcsS
        rw [hs'y', hsy] at hrelL
        have hCL : CL M i = Lc ++ cs :: Tl := by rw [hclM]; simp
        have hsLc : ∀ t ∈ Lc.map ρ.o ++ [ρ.o cs], Single t := fun t ht => hsM t (by
          rcases List.mem_append.mp ht with h | h
          · simp only [List.mem_append, List.mem_cons]; exact Or.inl (Or.inl h)
          · simp at h; rw [h]; simp)
        have hpLc : (Lc.map ρ.o ++ [ρ.o cs]).Pairwise (fun a b => b ≤ a) := hp1.1
        have hstate : spArg (ρ.v i) z (sumN ((Lc ++ [cs]).map ρ.o)) =
            step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z := by
          rw [List.map_append, List.map_singleton, sumN_append_dec hsLc hpLc,
            sumN_singleton (single_o hC hG hcsM), spArg_app, hsy, spArg_single]
        have hot : isOT (psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z) z) = true := by
          rw [← hstate]
          cases Tl with
          | nil =>
            have ho := o_spArg hC hG hiM
            rw [cvals_eq_map hC hG i, hclM] at ho
            simp only [List.append_nil] at ho
            rw [← ho]; exact hG.ot_o i hiM
          | cons c0 Tl' => exact hFO i hiM (Lc ++ [cs]) c0 Tl' (by rw [hclM])
        exact node_ot_hard hcsS.1 (by rw [← hs'y']; exact hPOc.2.1) hrelL
          (hBge _ (single_o hC hG hcsM) (le_refl _) |> fun h => by rw [hsy] at h; exact h)
          (hssT s y s' y' hsy hs'y') (by rw [hvM s y hsy]; exact hfr) (hsubA s' y' hs'y')
          (fun hss has ht' ht hhi => by
            subst hss
            exact hHard i hi Lc cs hcl s' y' y hs'y' hsy has ht' ht hhi)
          hot hBot
      · -- a weak child `ψ_{w′}(0)`: the argument is `0`
        rw [hs'y'] at e1; simp only [psi.injEq] at e1
        apply step_ot_of_leB hBot (by rw [← hs'y']; exact hPOc.2.1)
        · exact hBge _ hPOc.2 hle' |> fun h => by rw [hs'y'] at h; exact h
        · exact hsubA s' y' hs'y'
        · intro _ g hg; rw [e1.2.1] at hg; simp [comps] at hg

end


set_option linter.unusedSectionVars false

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hVS : VSmallF M ρ) (hVN : VSmallNew M x ρ ρ') (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
  (hHard : HardArg M x ρ ρ')
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hHard

/-- `pv_of_hardW` with `PV2` / `WeakCS2` / `WCSP2`. -/
theorem pv_of_hardW2 {i : Nat} (hi : i < x) (hWC : WeakCS2 M x ρ ρ')
    (hBump : ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV2 M ρ ρ' i)
    (hX1 : ∀ k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
        WCSP2 M ρ i (add (vOpt ρ (par M 1 i)) one))
    (hup : ∀ k, upg (M.take x) i = some k → PV2 M ρ ρ' k ∧
      ∀ j ∈ children (M.take x) k, col (M.take x) j = bump (M.take x) k →
        ∀ k' ∈ children (M.take x) j, Single (ρ'.o k')) :
    PV2 M ρ ρ' i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : i < (M.take x).length := by omega
  have hiM : i < M.length := by omega
  have hoff := chg_off hx hC hG hC' hRk'
  by_cases hCv : ChgX M x false i
  swap
  · rw [PV2, (hoff i hi).2 hCv]
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
      rw [PV2, e1, ← e2]
      exact ⟨Or.inl (Or.inl rfl), hG.ot_v i hiM⟩
    | some k =>
      have huT : upg (M.take x) i = some k := by rw [hupT, hu]
      obtain ⟨hPVk, hook⟩ := hup k huT
      have ek : ρ.v i = ρ.v k := v_upg_eq hC hiM h1 h2 hu hVot (hoot k)
      have ek' : ρ'.v i = ρ'.v k := v_upg_eq hC' hiT (by rw [entry_take M 1 hi]; exact h1)
        (by rw [entry_take M 2 hi]; exact h2) huT (by rw [hV]; exact hVot)
        (fun j hj hjb k' hk' => (hook j hj hjb k' hk').1)
      unfold PV2
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
    unfold PV2
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

/-- **The drop lemma with `PV2`** (`drop_all_hardW` with `WCS2` in the weak alternative) (modulo the bump-type frames and the absorption at `x − 1`): at every column of
`M.take x`, `o` and `v` are `⊴` the values in `M` or weakly below them, and standard. -/
theorem drop_all_hardW2
    (hBump : (∀ i, i < x → (∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < x →
        PO ρ ρ' k ∧ PV2 M ρ ρ' k) → ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV2 M ρ ρ' i) ∧
      WeakCS2 M x ρ ρ')
    (hX1 : ∀ i k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
        WCSP2 M ρ i (add (vOpt ρ (par M 1 i)) one)) :
    ∀ i, i < x → PO ρ ρ' i ∧ PV2 M ρ ρ' i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have key : ∀ N, ∀ i, i < x → (rk true i ≤ N → PO ρ ρ' i) ∧ (rk false i ≤ N → PV2 M ρ ρ' i) := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      have hPV : ∀ i, i < x → rk false i ≤ N → PV2 M ρ ρ' i := by
        intro i hi hN
        obtain ⟨_, _, hR⟩ := hRk' i (by omega)
        apply pv_of_hardW2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hHard hi hBump.2
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
      apply po_of_hard2 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hVS hVN hF hFO hHard hi
      · exact hPV i hi (by omega)
      · intro c hcT hcnt
        have hlt := hc c hcT hcnt.1 hcnt.2
        have hcx : c < x := by have := (mem_children hcT).2; omega
        have hlt2 := (hRk' c (by omega)).1
        exact ⟨(ih _ (by omega) c hcx).1 (Nat.le_refl _), (ih _ (by omega) c hcx).2 (Nat.le_refl _)⟩
  intro i hi
  exact ⟨(key _ i hi).1 (Nat.le_refl _), (key _ i hi).2 (Nat.le_refl _)⟩

end

end Ytosk
