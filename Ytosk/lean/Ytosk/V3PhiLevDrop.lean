/-
**LevLeafInv ∧ PrefLast を 1 列落としで運ぶ。**

- PrefLast: どの列 j と、j より前に行 1 の子を持つ列 p についても、v(p) は添字 v(P_1 j)・v(P_1 (P_0 j)) の
  部分項を持たない（5 集合で計 7000 万組、例外 0）。「各接頭辞の最後の列」の事実を M の値で書いたもの。
- 1 列落としで新しく出る後続の葉は、上げを失った x − 1（PrefLast の j = x − 1）か、唯一の数える子 x を
  失った P_0 x（PrefLast の j = x、2 番目の項）だけ。後者は明示的な仮定 LostKids（数える子をすべて失う列は
  P_0 x、5 集合で 52 万件、例外 0）。
-/
import Ytosk.V3PhiLevLink

namespace Ytosk

open T

theorem subT_size : ∀ {w t : T}, SubT w t → size w ≤ size t
  | _, _, .refl _ => Nat.le_refl _
  | _, _, .sub h => le_of_lt (lt_of_le_of_lt (subT_size h) (size_sub_lt _ _ _))
  | _, _, .arg h => le_of_lt (lt_of_le_of_lt (subT_size h) (size_arg_lt _ _ _))
  | _, _, .rest h => le_of_lt (lt_of_le_of_lt (subT_size h) (size_rest_lt _ _ _))

/-- **No subterm of `V` has subscript `V`.** -/
theorem levFree_self (V : T) : LevFree V V := by
  intro a b c h ha
  subst ha
  have := subT_size h
  have := size_sub_lt a b c
  omega

/-- **The prefix-last condition.** -/
def PrefLast (M : Mat) (ρ : Valn) : Prop :=
  ∀ j c p, j < M.length → c < j → par M 1 c = some p →
    (∀ q, par M 1 j = some q → ρ.v q ≠ z → LevFree (ρ.v q) (ρ.v p)) ∧
    (∀ i q, par M 0 j = some i → par M 1 i = some q → ρ.v q ≠ z → LevFree (ρ.v q) (ρ.v p))

section
variable {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
include hC hG

/-- **A successor `v` is `v(P_1) + 1`** (row 2 zero, no upgrade). -/
theorem v_succ_form {i : Nat} (hi : i < M.length) {μ : T} (hμ : ρ.v i = succ μ) :
    entry M 1 i ≠ 0 ∧ entry M 2 i = 0 ∧ upg M i = none ∧ μ = vOpt ρ (par M 1 i) := by
  have hv := (hC i hi).2
  unfold vRhs at hv
  by_cases h1 : entry M 1 i = 0
  · rw [if_pos h1] at hv; rw [hv] at hμ; exact absurd hμ.symm (succ_ne_z μ)
  rw [if_neg h1] at hv
  have hV0 : isOT (vOpt ρ (par M 1 i)) = true := by
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  by_cases h2 : entry M 2 i = 0
  · rw [if_pos h2] at hv
    cases hu : upg M i with
    | none =>
      rw [hu] at hv; simp only at hv
      rw [sf_ot (isOT_add hV0 rfl)] at hv
      rw [hv] at hμ
      exact ⟨h1, h2, rfl, (succ_of_add_single ⟨z, z, rfl⟩ hμ).2⟩
    | some k =>
      rw [hu] at hv; simp only at hv
      rw [upg_target_last hC hG hi hu] at hv
      have hW : isOT (bumpW M ρ k) = true := isOT_bumpOmega hC hG k
      rw [sf_ot (isOT_add hV0 hW)] at hv
      rw [hv] at hμ
      exact absurd (succ_of_add_single (omega_psi_form _) hμ).1 (bumpOmega_ne_one hC hG k)
  · rw [if_neg h2] at hv
    rw [sf_ot (isOT_add hV0 (isOT_bumpOmega hC hG i))] at hv
    rw [hv] at hμ
    exact absurd (succ_of_add_single (omega_psi_form _) hμ).1 (bumpOmega_ne_one hC hG i)

end

/-! ## 1 列落とし -/

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB

/-- **The lost-kids property**: a column that loses all its counted children is the parent of `x`. -/
def LostKids (M : Mat) (x : Nat) (ρ ρ' : Valn) : Prop :=
  ∀ i, i < x → cvals (M.take x) ρ' i = [] → cvals M ρ i ≠ [] → par M 0 x = some i

omit hx hZ2 hSD hZ1 hUAB in
/-- **An upgrade from the previous column leaves a counted earlier sibling**: if `c` is a child of
`i` and `c − 1` upgrades to `c`, then `P_1 (c − 1) = i`, and the child `p` of `i` above `c − 1` is
counted, or is itself upgraded from `p − 1` (an ancestor-type upgrade never lands on a topped
column, UAT), and then we go on with `p`. -/
theorem earlier_counted {i : Nat} :
    ∀ c, c ∈ children M i → upg M (c - 1) = some c → ∃ d ∈ children M i, d < c ∧ Counted M i d := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
  intro hc hu
  have hic := (mem_children hc).1
  have hcl := (mem_children hc).2
  have hpc := (mem_children_iff.mp hc).2
  obtain ⟨m, hmk, _, hcol, _⟩ := upg_spec hu
  have hAk : Anc0 M i (c - 1) :=
    anc_between (Anc0.step hpc (Anc0.refl i)) (c - 1) (by omega) (by omega)
  have he0c : entry M 0 c = entry M 0 m + 1 := by
    have : entry M 0 c = (col M c).1 := rfl
    rw [this, hcol]
  have he0 := hR0 c i hpc
  have hmi : m = i := anc0_eq_of_e0 (anc0_of_par M 1 m (c - 1) hmk) hAk (by omega)
  subst hmi
  have hik : m ≠ c - 1 := by have := par_lt M 1 (c - 1) m hmk; omega
  obtain ⟨p, hpm, hpk⟩ := anc0_child hAk hik
  have hpc' : p < c := by have := hpk.le; omega
  have hpch : p ∈ children M m := mem_children_iff.mpr ⟨by omega, hpm⟩
  by_cases hcnt : Counted M m p
  · exact ⟨p, hpch, hpc', hcnt⟩
  · have hmp := par_lt M 0 p m hpm
    have h1 := par1_between hmk p hpk hmp
    have h2 := par1_entry_lt hmk
    have hb : col M p ≠ bump M m := by
      intro h
      have e1 : entry M 1 p = (col M p).2.1 := rfl
      rw [e1, h] at h1
      unfold bump at h1
      simp only at h1
      omega
    have hut : isUpg M p = true ∧ topped M p = true := by
      unfold Counted at hcnt
      by_contra hn
      exact hcnt ⟨hb, hn⟩
    obtain ⟨hiu, htop⟩ := hut
    unfold isUpg at hiu
    rw [List.any_eq_true] at hiu
    obtain ⟨j, _, hju⟩ := hiu
    have hju' : upg M j = some p := of_decide_eq_true hju
    by_cases hjp : p = j + 1
    · subst hjp
      obtain ⟨d, hd, hdp, hdc⟩ := ih (j + 1) hpc' hpch (by simpa using hju')
      exact ⟨d, hd, by omega, hdc⟩
    · rw [hUAT j p hju' hjp] at htop
      cases htop

/-- **LostKids holds**: if `i` loses all its counted children, `x` is a child of `i`. Otherwise the
lost child `c` is topped and upgraded in `M.take x` (so `x` is its last child in `M`); the upgrade
comes from `c − 1` (UAT of the prefix), and an earlier counted sibling stays counted. -/
theorem lostKids {ρ ρ' : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ')
    (hG' : Good3 (M.take x) ρ') : LostKids M x ρ ρ' := by
  intro i hi hT hM
  rw [cvals_eq_map hC' hG', List.map_eq_nil_iff] at hT
  rw [cvals_eq_map hC hG] at hM
  by_contra hpx
  have hxi : x ∉ children M i := fun h => hpx (mem_children_iff.mp h).2
  have hmemT : ∀ d, d ∈ children M i → d < x → Counted (M.take x) i d → False := by
    intro d hd hdx hdc
    have hdT : d ∈ children (M.take x) i := by
      rw [children_take, List.mem_filter]; exact ⟨hd, by simpa using hdx⟩
    have : d ∈ CL (M.take x) i := by
      unfold CL; rw [List.mem_filter]; exact ⟨hdT, decide_eq_true hdc⟩
    rw [hT] at this
    cases this
  obtain ⟨c, hcM⟩ := List.exists_mem_of_ne_nil (CL M i) (fun h => hM (by rw [h]; rfl))
  unfold CL at hcM
  rw [List.mem_filter] at hcM
  have hcch := hcM.1
  have hcnt : Counted M i c := of_decide_eq_true hcM.2
  have hcx : c < x := by
    have := (mem_children hcch).2
    have : c ≠ x := fun e => hxi (e ▸ hcch)
    omega
  have hut : isUpg (M.take x) c = true ∧ topped (M.take x) c = true := by
    by_contra hn
    apply hmemT c hcch hcx
    refine ⟨?_, hn⟩
    rw [col_take M hcx, bump_take M hi]
    exact hcnt.1
  obtain ⟨k, hkx, hku⟩ := (isUpg_take M (by omega) c).mp hut.1
  have hck : c = k + 1 := by
    by_contra hne
    have := UAT_take hR0 hZ2 hSD hZ1 hUAB x k c (by rw [upg_take M hkx]; exact hku) hne
    rw [this] at hut
    exact absurd hut.2 (by simp)
  obtain ⟨d, hd, hdc, hdcnt⟩ := earlier_counted hR0 hUAT c hcch (by rw [show c - 1 = k by omega]; exact hku)
  apply hmemT d hd (by omega)
  by_contra hne
  have := cnt_change_last hx hi hd (by omega) (fun h => hne (h.mpr hdcnt)) c hcch hcx
  omega

theorem prefLast_take {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hR' : Rk (M.take x) rk') (hP : PrefLast M ρ) :
    PrefLast (M.take x) ρ' := by
  have hlen : (M.take x).length = x := by rw [List.length_take]; omega
  have hv := fun {c p : Nat} (hc : c < x) (hp : par M 1 c = some p) =>
    v_take_of_par1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hR' hc hp
  intro j c p hj hcj hp
  rw [hlen] at hj
  rw [par_take M 1 c (by omega)] at hp
  rw [hv (by omega) hp]
  refine ⟨fun q hq hne => ?_, fun i q hi hq hne => ?_⟩
  · rw [par_take M 1 j hj] at hq
    rw [hv hj hq] at hne ⊢
    exact (hP j c p (by omega) hcj hp).1 q hq hne
  · rw [par_take M 0 j hj] at hi
    have hij := par_lt M 0 j i hi
    rw [par_take M 1 i (by omega)] at hq
    rw [hv (by omega) hq] at hne ⊢
    exact (hP j c p (by omega) hcj hp).2 i q hi hq hne

/-- **LevLeafInv passes to `M.take x`**, given PrefLast. -/
theorem levLeaf_take {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hG' : Good3 (M.take x) ρ') (hR' : Rk (M.take x) rk')
    (hL : LevLeafInv M ρ) (hP : PrefLast M ρ) : LevLeafInv (M.take x) ρ' := by
  have hK := lostKids hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hG'
  have hlen : (M.take x).length = x := by rw [List.length_take]; omega
  have hv := fun {c p : Nat} (hc : c < x) (hp : par M 1 c = some p) =>
    v_take_of_par1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hR' hc hp
  intro c p i μ hc hp hi hcv hvi hμ
  rw [hlen] at hc hi
  rw [par_take M 1 c hc] at hp
  rw [hv hc hp]
  obtain ⟨h1, h2, hu', hμq⟩ := v_succ_form hC' hG' (by rw [hlen]; exact hi) hvi
  rw [entry_take M 1 hi] at h1
  rw [entry_take M 2 hi] at h2
  rw [par_take M 1 i hi] at hμq
  cases hq : par M 1 i with
  | none => rw [hq] at hμq; exact absurd hμq hμ
  | some q =>
    rw [hq] at hμq
    simp only [vOpt] at hμq
    rw [hv hi hq] at hμq
    subst hμq
    by_cases hix : i + 1 < x
    · -- the upgrade is unchanged, so `v(i) = v(q) + 1` in `M` too
      rw [upg_take M hix] at hu'
      have hvM : ρ.v i = succ (ρ.v q) := by
        have hvi' := (hC i (by omega)).2
        unfold vRhs at hvi'
        rw [if_neg h1, if_pos h2, hu', hq] at hvi'
        simp only [vOpt] at hvi'
        rw [hvi', sf_ot (isOT_add (hG.ot_v q (by have := par_lt M 1 i q hq; omega)) rfl), add_one_eq_app]
        rfl
      by_cases hcvM : cvals M ρ i = []
      · exact hL c p i _ (by omega) hp (by omega) hcvM hvM hμ
      · have hpx := hK i hi hcv hcvM
        exact (hP x c p (by omega) (by omega) hp).2 i q hpx hq hμ
    · -- `i = x − 1`
      have hix' : i = x - 1 := by omega
      by_cases hcx : c < x - 1
      · exact (hP (x - 1) c p (by omega) hcx hp).1 q (by rw [← hix']; exact hq) hμ
      · have hce : c = x - 1 := by omega
        rw [hce, ← hix', hq] at hp
        cases hp
        exact levFree_self _

end

/-! ## 基底 -/

theorem levFree_z (μ : T) : LevFree μ z := by intro a b c h; cases h

theorem base_levLeaf {L : Nat} {β : T} : LevLeafInv (Mlen L) (bval L β) := by
  intro c p i μ _ hp _ _ _ _
  rw [base_v_par1 hp]; exact levFree_z μ

theorem base_prefLast {L : Nat} {β : T} : PrefLast (Mlen L) (bval L β) := by
  intro j c p _ _ hp
  rw [base_v_par1 hp]
  exact ⟨fun _ _ _ => levFree_z _, fun _ _ _ _ _ => levFree_z _⟩

end Ytosk
