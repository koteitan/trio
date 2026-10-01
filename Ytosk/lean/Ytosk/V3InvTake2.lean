/-
**構造の不変条件は先頭部分で保たれる (2)**: UAT・UAB・R12・BumpE2・R01・左上が 0。

- UAB・R12・BumpE2・R01・左上が 0 は、M.take k の構造（子・上げ・列）が M のものの制限であることから。
- UAT は M の UAB から出る（M の UAT は要らない）: 祖先への上げ i → c（i + 1 < k）で、c が M.take k で
  topped なら、行 2 が 1 の c の子はすべてのりしろの子（`all_bump_of_last`）。i を含む c の子もそうなるが、
  それは UAB が禁じている。
これで落とす補題の仮定の束 `DropHyp` から構造の部分を外し、値の部分だけ（`DropHypV`）の t1_n0 を述べる
（`t1_n0v`）。
-/
import Ytosk.V3N0T1

namespace Ytosk

open T

/-- An ancestor in a prefix is an ancestor in `M`. -/
theorem anc0_of_take {M : Mat} {k a b : Nat} (h : Anc0 (M.take k) a b) : Anc0 M a b := by
  induction h with
  | refl => exact Anc0.refl _
  | @step b c hp _ ih =>
    by_cases hc : c < (M.take k).length
    · have hck : c < k := by rw [List.length_take] at hc; omega
      rw [par_take M 0 c hck] at hp
      exact Anc0.step hp ih
    · exact absurd hp (par0_out (by omega))

/-- An upgrade in a prefix is an upgrade of `M`, from a column before the last one of the prefix. -/
theorem upg_of_take {M : Mat} {k i c : Nat} (h : upg (M.take k) i = some c) :
    i + 1 < k ∧ upg M i = some c := by
  have h1 := upg_succ_lt h
  have hik : i + 1 < k := by rw [List.length_take] at h1; omega
  exact ⟨hik, by rw [← upg_take M hik]; exact h⟩

theorem UAB_take {M : Mat} (h : UAB M) (k : Nat) : UAB (M.take k) := by
  intro i c hu hne j hj hjb hA
  obtain ⟨hik, hu'⟩ := upg_of_take hu
  rw [children_take, List.mem_filter] at hj
  have hjk : j < k := by simpa using hj.2
  have hcj := (mem_children hj.1).1
  rw [col_take M hjk, bump_take M (by omega)] at hjb
  exact h i c hu' hne j hj.1 hjb (anc0_of_take hA)

/-- **UAT passes to prefixes**, from UAB of `M`. -/
theorem UAT_take {M : Mat} (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAB : UAB M)
    (k : Nat) : UAT (M.take k) := by
  intro i c hu hne
  obtain ⟨hik, hu'⟩ := upg_of_take hu
  obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu'
  rcases hcase with h | ⟨hA, hci⟩
  · exact absurd h hne
  · by_contra htop
    have htop' : topped (M.take k) c = true := by simpa using htop
    have hck : c < k := by omega
    obtain ⟨p, hpc, hpi⟩ := anc0_child hA (by omega)
    have hpk : p < k := by have := hpi.le; omega
    have hpl : p < M.length := by have := hpi.le; have := upg_succ_lt hu'; omega
    have hpM : p ∈ children M c := mem_children_iff.mpr ⟨hpl, hpc⟩
    have hpT : p ∈ children (M.take k) c := by
      rw [children_take, List.mem_filter]; exact ⟨hpM, by simpa using hpk⟩
    unfold topped at htop'
    cases hl : (children (M.take k) c).getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hpT; simp at hpT
    | some ℓ =>
      rw [hl] at htop'
      simp only [decide_eq_true_eq] at htop'
      have he2 : entry M 2 c = 1 := by have := upg_target_e2 hu'; have := hZ2 c; omega
      have hlast : children (M.take k) c = (children (M.take k) c).dropLast ++ [ℓ] := by
        rw [List.dropLast_append_getLast? _ hl]
      have hall := all_bump_of_last (R0P_take hR0 k) (Z2_take hZ2 k) (SibDec_take hSD k)
        (Z1C_take hZ1 k) (by rw [entry_take M 2 hck]; exact he2) hlast htop' p hpT
      rw [col_take M hpk, bump_take M hck] at hall
      exact hUAB i c hu' hne p hpM hall hpi

theorem R12_take {M : Mat} (h : R12 M) (k : Nat) : R12 (M.take k) := by
  intro i h1
  by_cases hi : i < k
  · rw [entry_take M 1 hi] at h1; rw [entry_take M 2 hi]; exact h i h1
  · exact entry_out' (by rw [List.length_take]; omega) 2

theorem R01_take {M : Mat} (h : R01 M) (k : Nat) : R01 (M.take k) := by
  intro i h0
  by_cases hi : i < k
  · rw [entry_take M 0 hi] at h0; rw [entry_take M 1 hi]; exact h i h0
  · exact entry_out' (by rw [List.length_take]; omega) 1

theorem BumpE2_take {M : Mat} (h : BumpE2 M) (k : Nat) : BumpE2 (M.take k) := by
  intro p c hc hcb
  rw [children_take, List.mem_filter] at hc
  have hck : c < k := by simpa using hc.2
  have hpc := (mem_children hc.1).1
  rw [col_take M hck, bump_take M (by omega)] at hcb
  rw [entry_take M 2 (by omega)]
  exact h p c hc.1 hcb

theorem e00_take {M : Mat} (h : entry M 0 0 = 0) (k : Nat) : entry (M.take k) 0 0 = 0 := by
  by_cases hk : 0 < k
  · rw [entry_take M 0 hk]; exact h
  · exact entry_out' (by rw [List.length_take]; omega) 0

/-! ## 値の部分だけの仮定 -/

/-- The value hypotheses of the drop lemma for dropping the last column `x` of `N`. -/
structure DropHypV (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  g : Good3 N σ
  vs : VSmallF N σ
  fc : FrameClosed N σ
  fo : FrameOT N σ
  argT : ∀ i, i < x → ∀ (Lc : List Nat) (cs : Nat), CL (N.take x) i = Lc ++ [cs] →
    ∀ s y, σ'.o cs = psi s y z → ¬ lt s (σ.v i) = true →
    ∀ g ∈ comps (σ.v i) y, g ≤ step (σ.v i) (spArg (σ.v i) z (sumN (Lc.map σ.o))) s y z
  kd : BumpKidsDec N σ
  td : BumpTermDec N σ
  ab : BumpAbsC N x σ
  ws : BumpWeakSrc N x σ σ'
  vst : VSmallNew N x σ σ'
  ua : UpgAbsX N x σ

theorem DropHypV.toDropHyp {N : Mat} {x : Nat} {σ σ' : Valn} (h : DropHypV N x σ σ')
    (hUAT : UAT N) (hUAB : UAB N) : DropHyp N x σ σ' :=
  ⟨hUAT, hUAB, h.g, h.vs, h.fc, h.fo, h.argT, h.kd, h.td, h.ab, h.ws, h.vst, h.ua⟩

/-- **`t = 1`, `q ≠ r`, `n = 0`**, given only the VALUE hypotheses of the drop lemma on the prefixes
`M.take (j + 1)` (`r ≤ j < x`); their structural invariants come from those of `M`. -/
theorem t1_n0v {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ) (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    {ζ μ : T} (hVL : ∀ i, i < r + L → DepX M (r + L) false i → VLocal M (r + L) ρ ζ μ i)
    (hstep : ∀ j, r ≤ j → j < r + L →
      DropHypV (M.take (j + 1)) j (drop1 M (j + 1) rkM) (drop1 M j rkM)) :
    ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 0) ρN ∧ Rk (TRIO.gexp M r L d0 0 0) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 0) ρN) = true ∧ root (TRIO.gexp M r L d0 0 0) ρN < root M ρ :=
  t1_n0 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hqr hC hG hRM hVS hF hFO hArgT
    hKD hTD hAbs hWS hVSt hUA hVL (fun j h1 h2 =>
      (hstep j h1 h2).toDropHyp (UAT_take hR0 hZ2 hSD hZ1 hUAB _) (UAB_take hUAB _))

end Ytosk
