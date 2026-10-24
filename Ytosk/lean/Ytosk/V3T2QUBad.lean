/-
**t = 2・q = r・x − 1 が祖先 k < x へ上げる場合の n ≤ 1（強い吸収が破れる場合、2026-10-17）。**

x − 1 の上げの吸収が強い形 UpgAbsX で破れると（11 集合で 175 件、std_b で 89 件、どれも q = r・k < x）、
x − 1 は M.take x で上げを失い、v′(x − 1) = V + 1 は v(x − 1) = V + W に ◁ で下がらず、o′(x − 1) も ◁ で下がらない。
そこで x − 1 の o と v を弱い呼び出し W（≤ だけを運ぶ）にし、種を o(r)（r ≠ x − 1 のとき、PO.zero_of_ne から）と
x − 1 の親 pr の o にする（`t2_assemble2`）。
- o′(pr) ◁ o(pr): 落とす補題の PO は pr ≠ x − 1 で LhdE か弱い形（o(pr) = ψ_w(0)）。pr は数える子 x − 1 を持つので
  弱い形はない。等号は o_strict_frame（x − 1 は pr の最後の数える子）で除く。o′(x − 1) < o(x − 1) は、r = x − 1 なら
  x を失うことから、r ≠ x − 1 なら上げを失って v が下がること（`v_upg_drop_lt`）から。pr = r なら種 o(r) そのもの。
- v(x − 1) を読む列はない（x − 1 の行 2 は 0 なので上げの的にならない）。x − 1 は pr の数える子。
- pr がのりしろの子だと x − 1 は bump 項を通して読まれるので、それは仮定で除く（破れの例はどれもそう）。
- 種の集合 SV r (x − 1) ∪ {o(pr)} の D は SV r (x − 1) の D と同じ（o(pr) は v(x − 1) から o(x − 1) を通ってつながる）。
-/
import Ytosk.V3T2T
import Ytosk.V3StrictR
import Ytosk.V3MainT1D

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- `DepS` is monotone in the seeds. -/
theorem DepS.mono {M : Mat} {S S' : Bool → Nat → Prop} (hS : ∀ b i, S b i → S' b i) {b : Bool} {i : Nat}
    (h : DepS M S b i) : DepS M S' b i := by
  induction h with
  | seed hs => exact DepS.seed (hS _ _ hs)
  | ochild hc hcb hcu _ ih => exact DepS.ochild hc hcb hcu ih
  | ov _ ih => exact DepS.ov ih
  | vpar h1 hpm _ ih => exact DepS.vpar h1 hpm ih
  | vupg h1 h2 hu _ ih => exact DepS.vupg h1 h2 hu ih
  | vbump h1 h2 hj hjb hk _ ih => exact DepS.vbump h1 h2 hj hjb hk ih

/-- **The lost upgrade lowers `v`** (the part of `v_upg_drop` without the absorption). -/
theorem v_upg_drop_lt {M N : Mat} {ρ σ : Valn} {i k : Nat} (hZ2 : Z2 M)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hiM : i < M.length) (hkM : k < M.length)
    (hiN : i < N.length) (hu : upg M i = some k)
    (he1 : entry N 1 i = entry M 1 i) (he2 : entry N 2 i = entry M 2 i)
    (hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i)) (hun : upg N i = none)
    : σ.v i < ρ.v i := by
  obtain ⟨m, hm1, hmk, hcol, _⟩ := upg_spec hu
  obtain ⟨he1M, he2M⟩ := upg_e12 hu
  have he2z : entry M 2 i = 0 := by have := hZ2 i; omega
  set V := vOpt ρ (par M 1 i) with hVdef
  have hVot : isOT V = true := by
    rw [hVdef, hm1]; exact hG.ot_v m (by have := par_lt M 1 _ m hm1; omega)
  have he1k : entry M 1 k ≠ 0 := by rw [e1_of_col hcol]; exact he1M
  have he2k : entry M 2 k ≠ 0 := by rw [e2_of_col hcol]; omega
  have hY : isOT (sumN (one :: (children M k).map (bumpTerm M ρ k))) = true :=
    isOT_sumN _ (fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG k d)
  have hWs : Single (bumpW M ρ k) := single_omega hY
  have hvk : ρ.v k = add V (bumpW M ρ k) := by
    rw [(hC _ hkM).2]; unfold vRhs
    rw [if_neg he1k, if_neg he2k]
    have hVk : vOpt ρ (par M 1 k) = V := by rw [hVdef, hmk, hm1]
    show sf (add (vOpt ρ (par M 1 k)) (bumpW M ρ k)) = _
    rw [hVk, sf_ot (isOT_add hVot hWs.1)]
  have hlast : last (ρ.v k) = bumpW M ρ k := by
    obtain ⟨s, y, h⟩ := hWs.2
    rw [hvk, h, last_add_single]
  have ev : ρ.v i = add V (bumpW M ρ k) := by
    rw [(hC _ hiM).2]; unfold vRhs
    rw [if_neg he1M, if_pos he2z, hu]
    show sf (add V (last (ρ.v k))) = _
    rw [hlast, sf_ot (isOT_add hVot hWs.1)]
  have ev' : σ.v i = add V one := by
    rw [(hCN _ hiN).2]; unfold vRhs
    rw [he1, he2, if_neg he1M, if_pos he2z, hun, hV]
    show sf (add V one) = _
    rw [sf_ot (isOT_add hVot isOT_one)]
  have hone : one < bumpW M ρ k := by
    have h1 : one ≤ sumN (one :: (children M k).map (bumpTerm M ρ k)) :=
      le_sumN_append [one] _ (fun t ht => by simp at ht; rw [ht]; exact isOT_one)
        (fun t ht => by obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG k d)
    have h0 : z < sumN (one :: (children M k).map (bumpTerm M ρ k)) :=
      lt_of_lt_of_le (T.z_lt_psi z z z) h1
    have := omega_lt_omega rfl hY h0
    rw [omega_z] at this; exact this
  rw [ev, ev']
  exact add_lt_add_left V hone

/-- The seeds of the bad case: `SV r j` and `o(pr)`. -/
def SVp (r j pr : Nat) : Bool → Nat → Prop := fun b i => SV r j b i ∨ (b = true ∧ i = pr)

/-- **`D` from `SV r j ∪ {o(pr)}` is `D` from `SV r j`** when `r` is a counted child of `pr`. -/
theorem depS_SVp {M : Mat} {r j pr : Nat} (hc : r ∈ children M pr) (hcb : col M r ≠ bump M pr)
    (hcu : ¬ (isUpg M r = true ∧ topped M r = true)) {b : Bool} {i : Nat} (h : DepS M (SVp r j pr) b i) :
    DepS M (SV r j) b i := by
  induction h with
  | seed hs =>
    rcases hs with hs | ⟨rfl, rfl⟩
    · exact DepS.seed hs
    · exact DepS.ochild hc hcb hcu (DepS.seed (Or.inl ⟨rfl, rfl⟩))
  | ochild hc hcb hcu _ ih => exact DepS.ochild hc hcb hcu ih
  | ov _ ih => exact DepS.ov ih
  | vpar h1 hpm _ ih => exact DepS.vpar h1 hpm ih
  | vupg h1 h2 hu _ ih => exact DepS.vupg h1 h2 hu ih
  | vbump h1 h2 hj hjb hk _ ih => exact DepS.vbump h1 h2 hj hjb hk ih

section
variable {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hXb : col M (r + L) ≠ bump M r)
include hlen hL hp hXb

/-- **`t = 2`, `q = r`, `x − 1` upgrades to `k < x`, `n ≤ 1`, the strong absorption may fail**
(`M[n] = M.take x`): the weak calls are `o(x − 1)` and `v(x − 1)`, the seeds `o(r)` (when `r ≠ x − 1`) and
`o(pr)`, `pr` the parent of `x − 1`. -/
theorem t2_qu_take_bad (hBE : BumpE2 M) (hZ2 : Z2 M) (hUAT : UAT M) (hR12 : R12 M) (hR01 : R01 M)
    (h00 : entry M 0 0 = 0) (he2r : entry M 2 r = 0)
    (hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p) (hrCL : CL M r ≠ [])
    (hrU : isUpg M r = false) {k : Nat} (hu : upg M (r + L - 1) = some k) (hkx : k < r + L)
    (hkT : topped M k = false)
    -- the shape of `D` in `M`
    (hP1 : ∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SV r (r + L - 1)) false m)
    (hDvNil : ∀ c, c < r + L → c ≠ r → DepS M (SV r (r + L - 1)) false c → CL M c = [])
    (hvr : r ≠ r + L - 1 → ¬ DepS M (SV r (r + L - 1)) false r)
    (hOS : ∀ i, i < r + L → ¬ SV r (r + L - 1) true i →
      DepS M (SV r (r + L - 1)) true i → ¬ DepS M (SV r (r + L - 1)) false i →
      ∃ Lp c R, children M i = Lp ++ c :: R ∧ Counted M i c ∧ DepS M (SV r (r + L - 1)) true c ∧
        (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ Lp, Counted M i d → ¬ DepS M (SV r (r + L - 1)) true d))
    (hVSh : ∀ i, i < r + L → ¬ SV r (r + L - 1) false i → DepS M (SV r (r + L - 1)) false i →
      (∀ m, par M 1 i = some m → ¬ DepS M (SV r (r + L - 1)) false m) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
        children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M (SV r (r + L - 1)) true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M (SV r (r + L - 1)) true e)))
    -- values
    {ρ σ : Valn} {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons (M.take (r + L)) σ) (hGN : Good3 (M.take (r + L)) σ) (hRN : Rk (M.take (r + L)) rkN)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hAbs : AbsWN M (M.take (r + L)) (r + L) ρ σ)
    (hseed : r ≠ r + L - 1 → Lhd z (σ.o r) (ρ.o r))
    -- the bad case: the parent `pr` of `x − 1` is not a bump child, and the drop lemma
    {pr : Nat} (hpr : par M 0 (r + L - 1) = some pr)
    (hpb : ∀ g, par M 0 pr = some g → col M pr ≠ bump M g) (hxCL : r = r + L - 1 → r + L ∈ CL M r)
    (hR0 : R0P M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAB : UAB M)
    (hdrop : ∀ i, i < r + L → PO ρ σ i ∧ PV M ρ σ i) (h3 : NoBad3 M ρ) :
    isOT (root (M.take (r + L)) σ) = true ∧ root (M.take (r + L)) σ < root M ρ := by
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 0 r (r + L) hp
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hp] at h'; exact (Option.some.inj h').symm
  have hchN : ∀ i, i < r + L → i ≠ r → children (M.take (r + L)) i = children M i := by
    intro i _ hir
    rw [children_take, children_filter_x hlen (fun h => hir (hxc i (r + L) h (le_refl _)).2)]
  have hkr : k ≠ r := by
    intro h; have := upg_target_e2 hu; rw [h] at this; omega
  have hcnt : ∀ i c, i < r + L → c < r + L → (Counted (M.take (r + L)) i c ↔ Counted M i c) := by
    intro i c hi hc
    by_cases hcr : c = r
    · subst hcr
      unfold Counted
      rw [col_take M hc, bump_take M hi, isUpg_take_eq hlen (by
        rw [hu]; intro h; exact hkr (Option.some.inj h)) hc, hrU]
      simp
    · by_cases hck : c = k
      · subst hck
        unfold Counted
        rw [col_take M hc, bump_take M hi,
          topped_take_eq hlen hc (fun h => hcr (hxc c (r + L) h (le_refl _)).2), hkT]
        simp
      · by_contra h
        rcases cnt_change hlen hi hc h with h' | h'
        · exact hcr (hxc c (r + L) h' (le_refl _)).2
        · rw [hu] at h'; cases h'; exact hck rfl
  have hRD : ∀ R, R < r + L → Anc0 M R (r + L) → col M R = (0, 0, 0) →
      DepS M (SV r (r + L - 1)) true R ∧ ¬ (fun _ _ => False : Bool → Nat → Prop) true R := by
    intro R hR hRA _
    have hRr : Anc0 M R r := anc0_par hRA (by omega) hp
    refine ⟨?_, id⟩
    apply path_upS hUAT hZ2 hR12 hBE (r - R) R r (le_refl _) (by omega) hRr (ne_of_e2z he2r)
      (DepS.seed (Or.inl ⟨rfl, rfl⟩))
    intro t _ htr
    have := htr.le
    exact ⟨r + L, by omega, hA, not_anc_out (by omega) (by omega)⟩
  have hCLnil : ∀ c, c < r + L → ¬ (fun _ _ => False : Bool → Nat → Prop) true c → CL M c = [] →
      CL (M.take (r + L)) c = [] := by
    intro c hc _ hcl
    by_cases hcr : c = r
    · exact (hrCL (by rw [← hcr]; exact hcl)).elim
    · unfold CL at hcl ⊢
      rw [hchN c hc hcr, ← hcl]
      apply List.filter_congr
      intro d hd
      have hdx : d < r + L := by
        have := (mem_children hd).2
        by_contra h'
        exact hcr (hxc c d hd (by omega)).2
      simp only [hcnt c d hc hdx]
  set j := r + L - 1 with hj
  have hjx : j < r + L := by omega
  have hprj : pr < j := par_lt M 0 j pr hpr
  have hjch : j ∈ children M pr := mem_children_iff.mpr ⟨by omega, hpr⟩
  have he2j : entry M 2 j = 0 := by have := hZ2 j; have := (upg_e12 hu).2; omega
  have hjcb : col M j ≠ bump M pr := fun h => by
    have := e2_of_col (show col M j = (entry M 0 pr + 1, entry M 1 pr, 1) from h); omega
  have hjU : ∀ j', upg M j' ≠ some j := fun j' h => by have := upg_target_e2 h; omega
  have hjcu : ¬ (isUpg M j = true ∧ topped M j = true) := by
    rintro ⟨h, _⟩
    unfold isUpg at h
    obtain ⟨k', _, hk'⟩ := List.any_eq_true.mp h
    exact hjU k' (of_decide_eq_true hk')
  have hcntj : Counted M pr j := ⟨hjcb, hjcu⟩
  have hjCLp : j ∈ CL M pr := by
    unfold CL; rw [List.mem_filter]; exact ⟨hjch, by simpa using hcntj⟩
  -- `D` from the new seeds is `D` from `SV r j`
  have hconv : ∀ {b i}, DepS M (SVp r j pr) b i → DepS M (SV r j) b i := by
    intro b i h
    induction h with
    | seed hs =>
      rcases hs with hs | ⟨rfl, rfl⟩
      · exact DepS.seed hs
      · exact DepS.ochild hjch hjcb hjcu (DepS.ov (DepS.seed (Or.inr ⟨rfl, rfl⟩)))
    | ochild hc hcb hcu _ ih => exact DepS.ochild hc hcb hcu ih
    | ov _ ih => exact DepS.ov ih
    | vpar h1 hpm _ ih => exact DepS.vpar h1 hpm ih
    | vupg h1 h2 hu _ ih => exact DepS.vupg h1 h2 hu ih
    | vbump h1 h2 hj hjb hk _ ih => exact DepS.vbump h1 h2 hj hjb hk ih
  have hmono : ∀ {b i}, DepS M (SV r j) b i → DepS M (SVp r j pr) b i :=
    fun h => DepS.mono (fun _ _ hs => Or.inl hs) h
  set Wj : Bool → Nat → Prop := fun _ i => i = j with hWj
  exact t2_assemble2 (S := SVp r j pr) (W := Wj) (bnd := r + L) (p := r) hC hG hRM
    hCN hGN hRN hF hVS hTD hKD hR01 hR12 h00 hlen (by rw [hlT]) (fun i hi hir => hchN i hi hir)
    (Or.inl (Or.inl (Or.inl ⟨rfl, rfl⟩))) (Or.inl he2r) (fun i hr hb => hrb i (mem_children_iff.mp hr).2 hb)
    (fun y i hi => entry_take M y hi) (fun i hi => par_take M 1 i hi)
    (fun i hi hs => by
      rcases Nat.lt_or_ge (i + 1) (r + L) with h | h
      · exact upg_take M h
      · exact absurd (Or.inl (Or.inr ⟨rfl, by omega⟩)) hs)
    (fun i c hi _ _ hcx => hcnt i c hi hcx)
    (fun i c hi hc hcx => by obtain ⟨_, rfl⟩ := hxc i c hc hcx; exact Or.inl (Or.inl (Or.inl ⟨rfl, rfl⟩)))
    (fun i k hi hk hkx => by
      obtain ⟨_, _, _, _, hcase⟩ := upg_spec hk
      exact Or.inl (Or.inr ⟨rfl, by rcases hcase with h | ⟨_, h⟩ <;> omega⟩))
    (fun i j hi hj hjx _ => by have := (mem_children hj).2; rw [hlT] at this; omega)
    (fun i j hi hj hjx hjb => by
      obtain ⟨hjx', hir⟩ := hxc i j hj hjx
      rw [hjx', hir] at hjb; exact absurd hjb hXb)
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, hjr⟩ := hxc j k hk hkx
      rw [hjr] at hj hjb
      exact absurd hjb (hrb i (mem_children_iff.mp hj).2))
    (fun j hj0 hj => by rw [hlT] at hj; omega)
    (by have := anc0_e0_lt hA (by omega); omega)
    -- the weak calls `o(j)`, `v(j)`
    (fun i (h : i = j) => by subst h; exact DepS.ov (DepS.seed (Or.inl (Or.inr ⟨rfl, rfl⟩))))
    (fun i (h : i = j) => ⟨h, fun j' hj' => by rw [h] at hj'; exact hjU j' hj'⟩)
    (fun i c hc _ (hw : c = j) => by
      subst hw
      have h1 := (mem_children_iff.mp hc).2; rw [hpr] at h1; cases h1
      exact Or.inr ⟨rfl, rfl⟩)
    (fun i jj c _ _ hj hjb hc (hw : c = j) => by
      subst hw
      have h1 := (mem_children_iff.mp hc).2; rw [hpr] at h1; cases h1
      exact absurd hjb (hpb i (mem_children_iff.mp hj).2))
    (fun c hc hw hs hd => by
      have hcr : c ≠ r := fun h => hs (Or.inl (Or.inl ⟨rfl, h⟩))
      exact hDvNil c hc hcr (hconv hd))
    (fun c hc (hw : ¬ c = j) hs hd => by
      rcases hs with (⟨_, hcr⟩ | ⟨h, _⟩) | ⟨_, hcp⟩
      · subst hcr
        exact absurd (hconv hd) (hvr hw)
      · cases h
      · subst hcp
        by_cases hpr' : c = r
        · subst hpr'; exact absurd (hconv hd) (hvr hw)
        · have := hDvNil c hc hpr' (hconv hd)
          rw [this] at hjCLp; simp at hjCLp)
    (fun c hc _ hcl => hCLnil c hc id hcl)
    (fun i hi hns hnw hD hv => by
      obtain ⟨Lp, c, R, h1, h2, h3, h4, h5⟩ :=
        hOS i hi (fun h => hns (Or.inl h)) (hconv hD) (fun h => hv (hmono h))
      exact ⟨Lp, c, R, h1, h2, hmono h3, h4, fun d hd hc' hdD => h5 d hd hc' (hconv hdD)⟩)
    (fun i hi hns hD => by
      obtain ⟨h1, h2⟩ := hVSh i hi (fun h => hns (Or.inl h)) (hconv hD)
      refine ⟨fun m hm hdm => h1 m hm (hconv hdm), fun he => ?_⟩
      obtain ⟨Lb, Kb, j, k, a1, a2, a3, a4, a5⟩ := h2 he
      exact ⟨Lb, Kb, j, k, a1, a2, a3, fun d hd hdD => a4 d hd (hconv hdD),
        fun d hd e he' hdD => a5 d hd e he' (hconv hdD)⟩)
    (fun R hR hRA hR0c => by
      refine ⟨hmono (hRD R hR hRA hR0c).1, fun (hw : R = j) => ?_⟩
      subst hw
      have := anc0_e0_lt (anc0_of_par M 0 pr _ hpr) (by omega)
      rw [col_eq_entries] at hR0c; simp only [Prod.mk.injEq] at hR0c; omega)
    (fun i hi (hw : i = j) => by subst hw; exact (hdrop _ hi).1.le)
    hAbs
    (fun b i hs (hw : ¬ i = j) hi _ hoff _ => by
      rcases hs with (⟨hb, hir⟩ | ⟨_, hij⟩) | ⟨hb, hip⟩
      · subst hb; subst hir; exact hseed hw
      · exact absurd hij hw
      · subst hb; subst hip
        by_cases hpr' : i = r
        · subst hpr'; exact hseed hw
        show Lhd z (σ.o i) (ρ.o i)
        have hiM : i < M.length := by omega
        -- `o′(j) < o(j)`
        have hojlt : σ.o j < ρ.o j := by
          by_cases hrj : r = j
          · have hjM : j < r + L := hjx
            rw [← hrj]
            exact o_strict_frame (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hCN hRN
              hdrop (by omega) (hxCL hrj) (fun d hd => by have := (mem_children (cl_mem_children hd)).2; omega)
              (fun h => absurd h (Nat.lt_irrefl _))
          · have hjM : j < M.length := by omega
            have hjT : j < (M.take (r + L)).length := by rw [hlT]; exact hjx
            have hvlt : σ.v j < ρ.v j := by
              apply v_upg_drop_lt hZ2 hC hG hCN hjM (by omega) hjT hu
                (entry_take M 1 hjx) (entry_take M 2 hjx) _ (upg_take_last M (by omega) (by omega))
              rw [par_take M 1 _ hjx]
              cases hm : par M 1 j with
              | none => rfl
              | some m =>
                show σ.v m = ρ.v m
                exact (hoff m (by have := par_lt M 1 _ m hm; omega)).2 (fun h => hP1 m hm (hconv h))
            have hclj : CL M j = [] := hDvNil j hjx (Ne.symm hrj) (DepS.seed (Or.inr ⟨rfl, rfl⟩))
            have hclT : CL (M.take (r + L)) j = [] := hCLnil j hjx id hclj
            rw [o_of_no_counted hCN hjT (hGN.ot_v j hjT) (no_cnt_of_cl_nil hclT),
              o_of_no_counted hC hjM (hG.ot_v j hjM) (no_cnt_of_cl_nil hclj)]
            exact psi_lt_psi_z_iff.mpr (Or.inl hvlt)
        have hlt : σ.o i < ρ.o i :=
          o_strict_frame (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hCN hRN hdrop
            (show i < r + L by omega) hjCLp
            (fun d hd => by
              by_contra h'
              have hdc := cl_mem_children hd
              have hdM := (mem_children hdc).2
              have hdx : d = r + L := by omega
              have h1 := (mem_children_iff.mp hdc).2
              rw [hdx, hp] at h1; cases h1; exact hpr' rfl)
            (fun _ => hojlt)
        rcases PO.zero_of_ne (show i + 2 ≠ M.length by omega) hC hG hiM (hdrop i (by omega)).1
            (hdrop i (by omega)).2 h3 with h | ⟨_, w, hw'⟩
        · rcases h with h | h
          · rw [h] at hlt; exact absurd hlt (lt_irrefl _)
          · exact h
        · exfalso
          have hne : CL M i ≠ [] := List.ne_nil_of_mem hjCLp
          have hlt' := arg_lt_of_cl (σ := ρ) hC hG hiM hne
          rw [o_cl_eq hC hG hiM] at hw'
          simp only [psi.injEq] at hw'
          rw [hw'.2.1] at hlt'; exact lt_irrefl' _ hlt')

end

end Ytosk
