/-
**WfExQ2 (2026-11-01): the `ExpStepQ` side of `Inv3V3` for the q = r chain (WfQrH7.qr_chainH3).**

The carried property is `PnV3 N σ := ∃ rk, Inv3V3 N σ rk` with the extra facts `ExDQ` (every `D` value of `M[n]`
is a `DQ` of the old value; this follows from the C_strip conjuncts of `hLocH`, `exDQ_of_strip`).
The 24 fields of `Inv3V3` on `M[n] = gexp M r L d0 0 n` split into three groups:
- **proved here** (structure, `Cons`, `Good3`, off-`D` values, and `DQ.lt` at the root `Rt`):
  `cons`, `good`, `rank` (`rk_gexp_t1`), `rootS` (`rootS_of_good`), `rootP` (`rootP_N_t1Q`);
- **carried through the DQ copy, need a new argument** (`CarryV3`): `vs`, `fc`, `fo`, `kd`, `td`, `ph`, `fc3`, `vra`
  (the old proofs are for `glueZ`, i.e. `D` values `fsD(old, Z)`; with `DQ` values the inserted summands `Q` enter);
- **frame fields of the last column of `M[n]`** (`FrameV3`, the analogue of the global residual `HFrameV2`) and the two
  leaf conditions (`HLeafV2`): `adsx`, `aus`, `tplosx`, `tploq`, `auwl`, `auw0`, `trigs`, `tplon`, `adn0`;
  `tp1`, `tp1w` follow from `ph` and the leaf conditions (`tp1C_of_ph3cG`, `tp1WC_of_ph3cG`).
`expStepQ_V3` assembles `ExpStepQ PnV3 (ExDQ M r L ρ)` from the two residual groups.
-/
import Ytosk.WfExQ1
import Ytosk.WfQrH7
import Ytosk.V3RootPN
import Ytosk.V3Total
import Ytosk.V3ExpInv2

namespace Ytosk.WfExQ2
open T Ytosk Ytosk.WfExQ1 Ytosk.WfQrL1 Ytosk.WfQrL7 Ytosk.WfQrH6

set_option linter.unusedSectionVars false

/-- The carried property of the chain. -/
def PnV3 (N : Mat) (σ : Valn) : Prop := ∃ rk, Inv3V3 N σ rk

/-- **The extra facts of a step**: every `D` value is a `DQ` of the old value. -/
def ExDQ (M : Mat) (r L : Nat) (ρ : Valn) (_n : Nat) (_ρP : Valn) (oq vq : Nat → T) : Prop :=
  (∀ c, c < r + L → DepX M (r + L) true c → ∃ η, DQ η false (ρ.o c) (oq c)) ∧
  (∀ i, i < r + L → DepX M (r + L) false i → ∃ η, DQ η true (ρ.v i) (vq i))

/-- `ExDQ` from the C_strip conjuncts of `hLocH` (WfQrH7.qr_chainH3). -/
theorem exDQ_of_strip {M : Mat} {r L : Nat} {ρ σ : Valn} (n : Nat) (ρP : Valn)
    (ho : ∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS)
    (hv : ∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) :
    ExDQ M r L ρ n ρP σ.o σ.v := by
  refine ⟨fun c hc hd => ?_, fun i hi hd => ?_⟩
  · obtain ⟨η, tS, h⟩ := ho c hc.le hd; exact ⟨η, h.toDQ⟩
  · obtain ⟨η, tS, h⟩ := hv i hi hd; exact ⟨η, h.toDQ⟩

/-- A step property with a premise `P` on `M[n-1]` and a conclusion `Q` on `M[n]` (as `ExpStepT1R`). -/
def ExpStepQR (P Q : Mat → Valn → Prop) (Ex : Nat → Valn → (Nat → T) → (Nat → T) → Prop)
    (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (oq vq : Nat → T),
    Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP → Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    P (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    Cons (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) →
    Good3 (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) →
    Ex n ρP oq vq →
    Q (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq)

/-- **The root order of `M[n]` with given `D` values** (`rootP_N_t1` for `glueQ`). -/
theorem rootP_N_t1Q {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
    {ρ ρN : Valn} {oq vq : Nat → T} {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hle : oq Rt ≤ ρ.o Rt) :
    ((roots (TRIO.gexp M r L d0 0 n)).map (glueQ M (r + L) ρ ρN oq vq).o).Pairwise (fun a b => b ≤ a) := by
  have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hR0; rw [hR0]; rfl
  have hRx := hRA.le
  have hsplit := roots_split hlen hRA hR0
  set pre := (roots M).filter (fun c => decide (c < Rt)) with hpre
  have hpre_lt : ∀ c ∈ pre, c < Rt := by
    intro c hc; rw [hpre, List.mem_filter] at hc; simpa using hc.2
  have hpre_nd : ∀ c ∈ pre, ¬ DepX M (r + L) true c := by
    intro c hc hd
    have := depX_ge (by omega) hR0e hRx hRlast hd
    have := hpre_lt c hc; omega
  have hRlt : Rt < r + L := by
    rcases Nat.eq_or_lt_of_le hRx with h | h
    · exfalso
      have h1 : entry M 0 (r + L) ≠ 0 := by
        have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
      rw [h] at hR0e
      exact h1 hR0e
    · exact h
  have hglue : (roots M).map (glueQ M (r + L) ρ ρN oq vq).o = pre.map ρ.o ++ [oq Rt] := by
    rw [hsplit, List.map_append, List.map_singleton, glueQ_o_dep hRlt hRd]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact glueQ_o_lt (by have := hpre_lt c hc; omega) (hpre_nd c hc)
  have hMl : (roots M).map ρ.o = pre.map ρ.o ++ [ρ.o Rt] := by
    rw [hsplit, List.map_append, List.map_singleton]
  rw [hMl] at hpM
  rw [roots_N_t1 hlen hL hA hd0e hn, hglue]
  rw [List.pairwise_append] at hpM ⊢
  refine ⟨hpM.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
  rw [List.mem_singleton] at hb; subst hb
  exact le_trans hle (hpM.2.2 a ha _ (List.mem_singleton_self _))

/-- **The fields proved from the structure, `Cons`, `Good3` and `DQ.lt` at the root.** -/
def EasyV3 (N : Mat) (σ : Valn) : Prop :=
  Cons N σ ∧ Good3 N σ ∧ (∃ rk, Rk N rk) ∧ (∀ i ∈ roots N, Single (σ.o i)) ∧ RootP N σ

/-- **`EasyV3` is carried** by every q = r (indeed every `t = 1`) step with `DQ` values on `D`. -/
theorem expStepQ_easy {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat} (hRM : Rk M rkM) (hpM : RootP M ρ) (P : Mat → Valn → Prop) :
    ExpStepQR P EasyV3 (ExDQ M r L ρ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨Rt, hRA, hRt0, hRlast⟩ := root_t1 hR01 hR12 h00 (r + L)
  have hRd := dep_anc_x hUAT hZ2 hR12 hBE hlen hx2 hRA
  have hRx : Rt < r + L := by
    rcases Nat.lt_or_ge Rt (r + L) with h | h
    · exact h
    · exfalso
      have : Rt = r + L := by have := hRA.le; omega
      rw [this] at hRt0
      have h2 := congrArg (fun p : Nat × Nat × Nat => p.2.1) hRt0
      have he : entry M 1 (r + L) = 0 := by
        unfold entry; unfold col at h2; simpa using h2
      have := par1_entry_lt h1; omega
  intro n hn ρP oq vq _ _ _ hCN hGN hEx
  refine ⟨hCN, hGN, rk_gexp_t1 hlen hL hA hd0e hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hRM n (by omega),
    rootS_of_good hCN hGN, ?_⟩
  obtain ⟨η, hD⟩ := hEx.1 Rt hRx hRd
  exact rootP_N_t1Q hlen hL hA hd0e hn hRA hRt0 hRlast hRd hpM (le_of_lt hD.lt)

/-- **The carried fields that need a new argument under `DQ` values.** -/
structure CarryV3 (N : Mat) (σ : Valn) : Prop where
  vs : VSmallF N σ
  fc : FrameClosed N σ
  fo : FrameOT N σ
  kd : BumpKidsDec N σ
  td : BumpTermDec N σ
  ph : PH3cG N σ
  fc3 : FC3 N σ
  vra : VSmallRAll N σ

/-- **The last-column frame fields** (as `TakeFrameV2`, with the new forms). -/
structure FrameV3 (N : Mat) (σ : Valn) (rk : Bool → Nat → Nat) : Prop where
  adsx : WfQnE2.AbsDSX N σ rk
  aus : AbsUS N σ rk
  tplosx : WfQnE2.TPLoSX N σ rk
  tploq : TPLoQ N σ rk
  auwl : AbsUWL N σ
  auw0 : AbsUW0 N σ rk
  trigs : TrigS0 N σ rk
  tplon : TPLoN N σ
  adn0 : AbsDN0 N σ rk

/-- `Inv3V3` from its three groups and the two leaf conditions. -/
theorem inv3V3_of_parts {N : Mat} {σ : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons N σ) (hG : Good3 N σ) (hR : Rk N rk) (hS : ∀ i ∈ roots N, Single (σ.o i)) (hP : RootP N σ)
    (K : CarryV3 N σ) (F : FrameV3 N σ rk) (hTP : TP1LeafG N σ) (hTPW : TP1WLeafG N σ) : Inv3V3 N σ rk :=
  ⟨hC, hG, hR, K.vs, K.fc, K.fo, K.kd, K.td, K.ph, K.fc3, K.vra, F.adsx, F.aus,
    tp1C_of_ph3cG hC ⟨hG.ot_o, hG.ot_v⟩ K.ph hTP, F.tplosx,
    tp1WC_of_ph3cG hC ⟨hG.ot_o, hG.ot_v⟩ K.ph hTPW, F.tploq, F.auwl, F.auw0, F.trigs, F.tplon, F.adn0, hS, hP⟩

/-- **The frame residual at the expansions**: every valuation of `M[n]` with `Cons`, `Rk`, `Good3` has the frame
fields and the leaf conditions (the analogue of `HFrameV2` ∧ `HLeafV2`, restricted to `M[n]`). -/
def FrameAtN (M : Mat) (r L d0 : Nat) : Prop :=
  ∀ n, 2 ≤ n → ∀ σ rk, Cons (TRIO.gexp M r L d0 0 n) σ → Rk (TRIO.gexp M r L d0 0 n) rk →
    Good3 (TRIO.gexp M r L d0 0 n) σ →
    FrameV3 (TRIO.gexp M r L d0 0 n) σ rk ∧ TP1LeafG (TRIO.gexp M r L d0 0 n) σ ∧
      TP1WLeafG (TRIO.gexp M r L d0 0 n) σ

/-- **The global frame residual** (for every standard matrix; `HFrameV2` ∧ `HLeafV2` with the new forms). -/
def HFrameV3 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → N ≠ [] → Cons N σ → Rk N rk → Good3 N σ →
    FrameV3 N σ rk ∧ TP1LeafG N σ ∧ TP1WLeafG N σ

/-- **`ExpStepQ` of `Inv3V3` (q = r chain)** from the carried residual `CarryV3` and the frame residual. -/
theorem expStepQ_V3 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat} (hRM : Rk M rkM) (hpM : RootP M ρ)
    (hCarry : ExpStepQR PnV3 CarryV3 (ExDQ M r L ρ) M r L d0 ρ)
    (hFr : FrameAtN M r L d0) :
    ExpStepQ PnV3 (ExDQ M r L ρ) M r L d0 ρ := by
  intro n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  obtain ⟨_, _, ⟨rk, hR⟩, hS, hP⟩ :=
    expStepQ_easy hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hRM hpM PnV3
      n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  have K := hCarry n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  obtain ⟨F, hTP, hTPW⟩ := hFr n hn _ rk hCN hR hGN
  exact ⟨rk, inv3V3_of_parts hCN hGN hR hS hP K F hTP hTPW⟩

end Ytosk.WfExQ2
