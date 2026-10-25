/-
**落とす補題の bump の場合を接ぎ木の悪い形 Bad2 でも（2026-10-25、lead）。**

`g_levelB`・`bump_relB`・`bump_dropB`: V3BumpDrop の `g_level`・`bump_rel`・`bump_drop` の写しで、弱い源の形の仮定を
`BumpWeakSrcB` に替えた。
- `BumpWeakShapeSrcB`: 弱い源 k の o は ψ_w(y)（y は任意。Bad2 では x − 1 が数える子 x を持つ）、i の子は [j] か、
  [j, x] で x − 1 の上げが吸収に失敗し BadPos（P₀(x) = g の形）。
- 弱い bump の列 i の CntX は、子が [j, x] のとき第 3 の選言（数える子は x だけ）。
- `NoBad3` は要らない（`nocnt_of_bump` を使わず、o(k) の形 ψ_w(y) を直接取る）。
測定: graftB・graftA・ext2b2・std_ab2・graftBb2Sf で例外 0（tmp の formB.py）。
-/
import Ytosk.V3BumpDrop
import Ytosk.V3T0F

namespace Ytosk

open T

/-- **The shape of the weak sources** (the `Bad2` form, 2026-10-25): when a source `k` under a bump child `j` of `i`
changes weakly and `x` is a counted child of `i`, the upgrade of `x − 1` fails the absorption at the bad position.
(The earlier form fixed `children M i = [j]` or `[j, x]` and `k` first among the children of `j`; both are false on the
expansions of `Bad2` matrices, b2grow1: `i` may have earlier bump children and `k` earlier siblings.) -/
def BumpWeakShapeSrcB (M : Mat) (x : Nat) (ρ ρ' : Valn) : Prop :=
  ∀ i, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ j ∈ children M i, col M j = bump M i →
    ∀ k ∈ children M j, (∃ w y, w ≠ z ∧ ρ.o k = psi w y z) →
      ((k = x ∧ children M j = [x] ∧ ¬ LhdE (ρ'.v i) (ρ.v i)) ∨
        (k < x ∧ ρ'.o k ≠ ρ.o k ∧ ¬ LhdE (ρ'.v k) (ρ.v k))) →
      x ∈ children M i → Counted M i x → UpgBad M ρ (M.length - 2) ∧ BadPos M

/-- **The absorption at a bump-type column** (the `Bad2` form): `BumpAbsC`, or the weak route of `PV` at `i`
(on graftB the absorption fails at 9 columns, where the weak route holds, desc). -/
def BumpAbsCB (M : Mat) (x : Nat) (ρ : Valn) : Prop :=
  ∀ σ', Cons (M.take x) σ' → ∀ i, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
    (∀ j ∈ children M i, col M j = bump M i → children M j = [x] → ρ.v x = z) →
    (StrongG M x ρ i ∨ XParNB M x ∨ ρ.v x = z) →
    (∀ r ∈ summands (vOpt ρ (par M 1 i)), ¬ r < bumpW (M.take x) σ' i → r < bumpW M ρ i →
        Lhd z r (bumpW M ρ i)) ∨
      (WkVA (σ'.v i) (ρ.v i) ∧ WCSP M ρ i (σ'.v i) ∧ CntX M ρ i)

theorem BumpAbsC.toB {M : Mat} {x : Nat} {ρ : Valn} (h : BumpAbsC M x ρ) : BumpAbsCB M x ρ :=
  fun σ' hσ i h1 h2 hx hg => Or.inl (h σ' hσ i h1 h2 hx hg)

/-- **The weak sources and the component condition** (the `Bad2` form, without `NoBad3`). -/
def BumpWeakSrcB (M : Mat) (x : Nat) (ρ ρ' : Valn) : Prop :=
  BumpWeakShapeSrcB M x ρ ρ' ∧ WeakCS M x ρ ρ'

theorem g_levelB {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hKD : BumpKidsDec M ρ) (hWS : BumpWeakSrcB M x ρ ρ')
    {i jl : Nat} (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hjlM : jl ∈ children M i) (hjlb : col M jl = bump M i)
    (hIH : ∀ k ∈ children M jl, k < x → PO ρ ρ' k ∧ PV M ρ ρ' k) :
    (∀ t ∈ (children (M.take x) jl).map ρ'.o, Single t) ∧
    (BRelS (sumN ((children (M.take x) jl).map ρ'.o)) (sumN ((children M jl).map ρ.o)) ∨
      (sumN ((children (M.take x) jl).map ρ'.o) ≤ sumN ((children M jl).map ρ.o) ∧
        ∃ k ∈ children M jl, ∃ w y, w ≠ z ∧ ρ.o k = psi w y z ∧
          ((k = x ∧ children M jl = [x]) ∨ (k < x ∧ ρ'.o k ≠ ρ.o k ∧ ¬ LhdE (ρ'.v k) (ρ.v k))))) := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have he2jl : entry M 2 jl ≠ 0 := by rw [e2_of_bump hjlb]; simp
  have hoff := chg_off hx hC hG hC' hRk'
  obtain ⟨XJ, hXJ, hXJc⟩ := children_M_eq hx jl
  have hdec := hKD i h1 h2 jl hjlM hjlb
  rcases List.eq_nil_or_concat (children (M.take x) jl) with hnil | ⟨K0, kl, hKT⟩
  · -- no child in `M.take x`
    rw [hnil] at hXJ ⊢
    simp only [List.map_nil, List.nil_append] at hXJ ⊢
    refine ⟨by simp, ?_⟩
    rcases hXJc with rfl | ⟨rfl, hxjl⟩
    · rw [hXJ]; left; exact brelS_refl
    · rw [hXJ]
      have hox : ρ.o x = psi (ρ.v x) z z := o_of_no_counted hC (by omega) (hG.ot_v x (by omega))
        (fun c hc => by have := mem_children hc; omega)
      have hsx : Single (ρ.o x) := single_o hC hG (by omega)
      simp only [List.map_cons, List.map_nil]
      rw [sumN_singleton hsx, hox]
      by_cases hvx : ρ.v x = z
      · left; rw [hvx]
        exact Or.inl ⟨Or.inr (lhd_zero (by simp)), one_lt_E0⟩
      · right; exact ⟨z_le _, x, by simp, _, z, hvx, hox, Or.inl ⟨rfl, by simp⟩⟩
  · rw [List.concat_eq_append] at hKT
    have hklT : kl ∈ children (M.take x) jl := by rw [hKT]; simp
    obtain ⟨hklx, hklM⟩ := mem_children_take hklT
    have hklL : kl < M.length := by omega
    have hklLT : kl < (M.take x).length := by omega
    obtain ⟨hPO, hPV⟩ := hIH kl hklM hklx
    have hK0lt : ∀ k ∈ K0, k < kl := by
      have hs := children_sorted (M.take x) jl
      rw [hKT] at hs
      exact fun k hk => (List.pairwise_append.mp hs).2.2 k hk kl (by simp)
    have hK0T : ∀ k ∈ K0, k ∈ children (M.take x) jl := fun k hk => by rw [hKT]; simp [hk]
    have hsame : ∀ k ∈ K0, ρ'.o k = ρ.o k := by
      intro k hk
      obtain ⟨hkx', hkM⟩ := mem_children_take (hK0T k hk)
      apply (hoff k hkx').1
      intro hCk
      exact chg_only_last hx hR0 hZ2 hSD hZ1 hUAT hUAB he2jl hkM hklT (hK0lt k hk) hCk (Anc0.refl k)
    have hchM : children M jl = K0 ++ [kl] ++ XJ := by rw [hXJ, hKT]
    rw [hchM] at hdec
    simp only [List.map_append, List.map_cons, List.map_nil] at hdec
    have hmapT : (children (M.take x) jl).map ρ'.o = K0.map ρ.o ++ [ρ'.o kl] := by
      rw [hKT, List.map_append, List.map_singleton]
      congr 1; exact List.map_congr_left hsame
    have hlekl : ρ'.o kl ≤ ρ.o kl := hPO.1.elim (fun h => h.le) (fun h => DRelOA.le (Or.inr h.1))
    have hsM : ∀ k ∈ children M jl, Single (ρ.o k) := fun k hk => single_o hC hG (mem_children hk).2
    have hsAll : ∀ t ∈ K0.map ρ.o ++ [ρ.o kl] ++ XJ.map ρ.o, Single t := by
      intro t ht
      have : t ∈ (children M jl).map ρ.o := by rw [hchM]; simpa using ht
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp this
      exact hsM k hk
    have hp1 := List.pairwise_append.mp hdec
    have hp0 := List.pairwise_append.mp hp1.1
    have hsK0 : ∀ t ∈ K0.map ρ.o, Single t := fun t ht => hsAll t (by simp [ht])
    have hsT : ∀ t ∈ K0.map ρ.o ++ [ρ'.o kl], Single t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hsK0 t ht
      · simp at ht; rw [ht]; exact hPO.2
    have eG' : sumN (K0.map ρ.o ++ [ρ'.o kl]) = app (sumN (K0.map ρ.o)) (ρ'.o kl) :=
      sumN_snoc_dec hsT (List.pairwise_append.mpr ⟨hp0.1, by simp, fun a ha b hb => by
        simp at hb; rw [hb]; exact le_trans hlekl (hp0.2.2 a ha _ (by simp))⟩)
    have eG : sumN (K0.map ρ.o ++ [ρ.o kl] ++ XJ.map ρ.o) =
        app (app (sumN (K0.map ρ.o)) (ρ.o kl)) (sumN (XJ.map ρ.o)) := by
      rw [sumN_append_dec hsAll hdec, sumN_snoc_dec (fun t ht => hsAll t (List.mem_append_left _ ht)) hp1.1]
    refine ⟨by rw [hmapT]; exact hsT, ?_⟩
    rw [hmapT, hchM]
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [eG', eG]
    by_cases hK0 : K0 = []
    · subst hK0
      simp only [List.map_nil, sumN_nil, app_z]
      obtain ⟨y0, hy0⟩ := o_psi_sub hC hklL
      rw [sf_ot (hG.ot_v kl hklL)] at hy0
      rw [hy0]
      simp only [app_psi, app_z]
      by_cases hv : ρ'.v kl = ρ.v kl
      · obtain ⟨y1, hy1⟩ := o_psi_sub hC' hklLT
        rw [sf_ot hPV.2, hv] at hy1
        rcases hPO.1 with hl | ⟨⟨w1, w2, X, e1, e2, hWk⟩, _⟩
        · left
          rw [hy1, hy0] at hl
          rw [hy1]
          exact brelS_single_same _ hl (hy1 ▸ hPO.2.1)
        · exfalso
          rw [hy1] at e1; rw [hy0] at e2
          simp only [psi.injEq] at e1 e2
          rw [← e1.1, ← e2.1] at hWk
          exact lt_irrefl' _ hWk.1
      · have hCk : ChgX M x false kl := by
          by_contra hn; exact hv ((hoff kl hklx).2 hn)
        have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCk).1 rfl hklx
        have ho' : ρ'.o kl = psi (ρ'.v kl) z z := o_of_no_counted hC' hklLT hPV.2 hT.2.1
        have he1 : entry M 1 kl ≠ 0 := by
          intro he; apply hv
          rw [v_z_of_e1 hC hklL he, v_z_of_e1 hC' hklLT (by rw [entry_take M 1 hklx]; exact he)]
        have hv'z : ρ'.v kl ≠ z := v_ne_z_of_e1 hC' hklLT (by rw [entry_take M 1 hklx]; exact he1)
        rw [ho']
        rcases hPV.1 with hl | ⟨hWk, hwc, hnc⟩
        · left; exact brelS_fix hl (one_le_of_ne_z hv'z)
        · by_cases hlv : LhdE (ρ'.v kl) (ρ.v kl)
          · left; exact brelS_fix hlv (one_le_of_ne_z hv'z)
          right
          refine ⟨(bwk_fix (le_trans (psi_le_psi_z (le_of_lt hWk.1)) (psi_le_psi_rest (z_le _)))
            hWk.2.1).1, kl, by simp, ρ.v kl, y0, ?_, hy0,
            Or.inr ⟨hklx, by
              rw [ho', hy0]
              intro h; simp only [psi.injEq] at h; exact hv h.1, hlv⟩⟩
          intro hz; rw [hz] at hWk; exact T.not_lt_z _ hWk.1
    · have hS0 : sumN (K0.map ρ.o) ≠ z := sumN_ne_z hsK0 hp0.1 (by simpa using hK0)
      rcases hPO.1 with hl | ⟨⟨w1, w2, X, e1', e2, hWk⟩, _⟩
      · left; exact brelS_app_same hS0 hl _
      · by_cases hlv : LhdE (ρ'.v kl) (ρ.v kl)
        · -- `v′ ⊴ v` gives `o′ = ψ_{v′}(0) ⊴ ψ_v(0) = o`: the strong route
          left
          have hlo : LhdE (ρ'.o kl) (ρ.o kl) := by
            obtain ⟨y1, hy1⟩ := o_psi_sub hC' hklLT
            rw [sf_ot hPV.2] at hy1
            obtain ⟨y0, hy0⟩ := o_psi_sub hC hklL
            rw [sf_ot (hG.ot_v kl hklL)] at hy0
            have ey1 : y1 = z := by
              rw [hy1] at e1'; simp only [psi.injEq] at e1'; exact e1'.2.1
            rw [hy1, hy0, ey1]
            exact lhdE_oq_v hlv
          exact brelS_app_same hS0 hlo _
        -- a weak last source after earlier siblings: only `≤` (2026-10-25, b2grow1)
        have hne : ρ'.o kl ≠ ρ.o kl := fun h => by
          rw [e1', e2] at h; simp only [psi.injEq] at h; rw [h.1] at hWk; exact lt_irrefl' _ hWk.1
        have hw2 : w2 ≠ z := by
          intro hz; rw [hz] at hWk; exact T.not_lt_z _ hWk.1
        right
        refine ⟨le_trans (app_le_app_left _ hlekl) (lhdE_prefix _ _).le, kl, by simp, w2, X, hw2, e2,
          Or.inr ⟨hklx, hne, hlv⟩⟩

/-- Lists with the same prefix and a smaller last element. -/
theorem forall2_le_snoc : ∀ (l : List T) {a b : T}, a ≤ b → List.Forall₂ (· ≤ ·) (l ++ [a]) (l ++ [b])
  | [], _, _, h => .cons h .nil
  | c :: l, _, _, h => .cons (le_refl c) (forall2_le_snoc l h)

theorem bump_relB {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsCB M x ρ) (hWS : BumpWeakSrcB M x ρ ρ')
    {i : Nat} (hi : i < x)
    (hIH : ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < x →
      PO ρ ρ' k ∧ PV M ρ ρ' k)
    (hCv : ChgX M x false i) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) :
    isOT (ρ'.v i) = true ∧
      (LhdE (ρ'.v i) (ρ.v i) ∨ (WkVA (ρ'.v i) (ρ.v i) ∧ WCSP M ρ i (ρ'.v i) ∧ CntX M ρ i)) := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : i < (M.take x).length := by omega
  have hiM : i < M.length := by omega
  have he2 : entry M 2 i = 1 := by have := hZ2 i; omega
  have hoff := chg_off hx hC hG hC' hRk'
  have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl hi
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
  set V := vOpt ρ (par M 1 i) with hVdef
  have hAb := bump_children_take hR0 hZ2 hSD hZ1 hi he2 hT
  obtain ⟨XI, hXI, hXIc⟩ := children_M_eq hx i
  have hpot := isOT_bumpP hG i
  have ev : ρ.v i = add V (omega (sumN (one :: (children M i).map (bumpTerm M ρ i)))) := by
    rw [(hC i hiM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, sf_ot (isOT_add hVot (isOT_omega hpot))]
  have ev'0 : ρ'.v i = sf (add V (omega (sumN (one :: (children (M.take x) i).map
      (bumpTerm (M.take x) ρ' i))))) := by
    rw [(hC' i hiT).2]; unfold vRhs
    rw [entry_take M 1 hi, entry_take M 2 hi, if_neg h1, if_neg h2, hV]
  rcases List.eq_nil_or_concat (children (M.take x) i) with hA | ⟨A0, jl, hA⟩
  · -- no child in `M.take x`
    rw [hA] at ev'0 hXI
    simp only [List.map_nil, List.nil_append] at ev'0 hXI
    have hone : sumN [one] = one := sumN_singleton ⟨rfl, z, z, rfl⟩
    rw [hone] at ev'0
    have hot1 : isOT (add V (omega one)) = true := isOT_add hVot (isOT_omega rfl)
    rw [sf_ot hot1] at ev'0
    rcases hXIc with rfl | ⟨rfl, hxi⟩
    · have he : ρ'.v i = ρ.v i := by rw [ev'0, ev, hXI]; simp [hone]
      exact ⟨he ▸ hG.ot_v i hiM, Or.inl (Or.inl he)⟩
    · have hxc : children M x = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro c hc; have := mem_children hc; omega
      by_cases hxb : col M x = bump M i
      · have hbx : bumpTerm M ρ i x = one := by
          unfold bumpTerm; rw [if_pos hxb, hxc]
          simp only [List.map_nil, sumN_nil]
          rw [omega_small (T.z_lt_psi _ _ _)]; rfl
        have htwo : sumN [one, one] = two := by
          rw [sumN_pair_one (t := one) ⟨rfl, z, z, rfl⟩, if_neg (lt_irrefl' _)]; rfl
        rw [hXI] at ev
        simp only [List.map_cons, List.map_nil, hbx, htwo] at ev
        rw [omega_small two_lt_E0] at ev
        rw [omega_small one_lt_E0] at ev'0
        refine ⟨by rw [ev'0]; exact isOT_add hVot (isOT_omega (show isOT one = true from rfl)), Or.inl ?_⟩
        rw [ev'0, ev]
        have hWE : psi z two z < E0 := psi_z_lt_E0 two_lt_E0
        have hWot : isOT (psi z two z) = true := by
          have := isOT_omega isOT_two; rwa [omega_small two_lt_E0] at this
        have hW'ot : isOT (psi z one z) = true := by
          have := isOT_omega (show isOT one = true from rfl); rwa [omega_small one_lt_E0] at this
        have hlt : psi z one z < psi z two z := by
          rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, one_lt_two⟩
        exact v_strong hVot ⟨hW'ot, _, _, rfl⟩ ⟨hWot, _, _, rfl⟩
          (Or.inr (lhd_lt_small hW'ot hWE hlt))
          (fun r hr _ hlt' => lhd_lt_small (isOT_mem_summands hVot hr) hWE hlt')
      · have hbx : bumpTerm M ρ i x = z := by unfold bumpTerm; rw [if_neg hxb]
        have he : ρ'.v i = ρ.v i := by
          rw [ev'0, ev, hXI]
          simp only [List.map_cons, List.map_nil, hbx]
          rw [show [one, z] = [one] ++ [z] from rfl, sumN_snoc_z (by simp; rfl), hone]
        exact ⟨he ▸ hG.ot_v i hiM, Or.inl (Or.inl he)⟩
  · rw [List.concat_eq_append] at hA
    have hjlT : jl ∈ children (M.take x) i := by rw [hA]; simp
    obtain ⟨hjlx, hjlM⟩ := mem_children_take hjlT
    have hjlb : col M jl = bump M i := hAb jl hjlT
    have hA0T : ∀ j ∈ A0, j ∈ children (M.take x) i := fun j hj => by rw [hA]; simp [hj]
    have hA0lt : ∀ j ∈ A0, j < jl := by
      have hs := children_sorted (M.take x) i
      rw [hA] at hs
      exact fun j hj => (List.pairwise_append.mp hs).2.2 j hj jl (by simp)
    have hearly : ∀ j ∈ A0, bumpTerm (M.take x) ρ' i j = bumpTerm M ρ i j := fun j hj =>
      (early_sib hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi h2 (mem_children_take (hA0T j hj)).2
        hjlT (hA0lt j hj)).2.2
    obtain ⟨hsG', hGrel⟩ := g_levelB hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hKD hWS h1 h2 hjlM
      hjlb (hIH jl hjlM hjlb)
    set G' := sumN ((children (M.take x) jl).map ρ'.o) with hG'def
    set G := sumN ((children M jl).map ρ.o) with hGdef
    have hG'ot : isOT G' = true := isOT_sumN _ (fun t ht => (hsG' t ht).1)
    have hGot : isOT G = true := isOT_sumN _ (fun t ht => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o k (mem_children hk).2)
    have hbjl' : bumpTerm (M.take x) ρ' i jl = omega G' := by
      unfold bumpTerm; rw [col_take M hjlx, bump_take M hi, if_pos hjlb]
    have hbjl : bumpTerm M ρ i jl = omega G := by unfold bumpTerm; rw [if_pos hjlb]
    set Pl := A0.map (bumpTerm M ρ i) with hPldef
    have hmapT : (children (M.take x) i).map (bumpTerm (M.take x) ρ' i) = Pl ++ [omega G'] := by
      rw [hA, List.map_append, List.map_singleton, hbjl']
      congr 1; exact List.map_congr_left hearly
    have hmapM : (children M i).map (bumpTerm M ρ i) = Pl ++ [omega G] ++ XI.map (bumpTerm M ρ i) := by
      rw [hXI, hA]; simp [hbjl, hPldef]
    have hsP : ∀ q ∈ Pl, Single q := by
      intro q hq
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have hjb : col M j = bump M i := hAb j (hA0T j hj)
      have := isOT_bumpTerm hG i j
      unfold bumpTerm at this ⊢; rw [if_pos hjb] at this ⊢
      exact single_omega (by
        apply isOT_sumN; intro t ht
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o k (mem_children hk).2)
    have hdecP := hTD i h1 h2
    rw [hmapM, nzs_append, nzs_append, nzs_eq_self (fun t ht => single_ne_z (hsP t ht)),
      nzs_single (omega_ne_z G)] at hdecP
    have hpre := (List.pairwise_append.mp (List.pairwise_append.mp hdecP).1)
    have hpP : Pl.Pairwise (fun a b => b ≤ a) := hpre.1
    have hPt : ∀ q ∈ Pl, omega G ≤ q := fun q hq => hpre.2.2 q hq _ (by simp)
    have hsL : ∀ t ∈ Pl ++ [omega G'], Single t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hsP t ht
      · simp at ht; rw [ht]; exact single_omega hG'ot
    have hp'ot : isOT (sumN (one :: Pl ++ [omega G'])) = true := by
      apply isOT_sumN; intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · exact (hsL t ht).1
    have ev' : ρ'.v i = add V (omega (sumN (one :: Pl ++ [omega G']))) := by
      rw [ev'0, hmapT, ← List.cons_append, sf_ot (isOT_add hVot (isOT_omega hp'ot))]
    have hv'ot : isOT (ρ'.v i) = true := by rw [ev']; exact isOT_add hVot (isOT_omega hp'ot)
    refine ⟨hv'ot, ?_⟩
    rcases hGrel with hS | ⟨hWk, k, hk, w, y, hw, hok, hkx⟩
    · -- the strong case
      -- no collapse: a bump child with the only child `x` has `v(x) = 0`
      have hexcl : ∀ j ∈ children M i, col M j = bump M i → children M j = [x] → ρ.v x = z := by
        intro j hj _ hjx
        by_contra hvx
        have hxj : x ∈ children M j := by rw [hjx]; simp
        have hjxlt : j < x := (mem_children hxj).1
        have hjT : j ∈ children (M.take x) i := by
          rw [children_take, List.mem_filter]; exact ⟨hj, by simpa using hjxlt⟩
        have hjjl : j = jl := by
          rcases Nat.lt_trichotomy j jl with h | h | h
          · exfalso
            have hAx : Anc0 M j x := Anc0.step (mem_children_iff.mp hxj).2 (Anc0.refl j)
            have h1' := anc_between hAx jl (by omega) (by omega)
            have hpjl : par M 0 jl = some i := (mem_children_iff.mp hjlM).2
            have := (anc0_par h1' (by omega) hpjl).le
            have := (mem_children hj).1; omega
          · exact h
          · exfalso
            rw [hA] at hjT
            rcases List.mem_append.mp hjT with h' | h'
            · have := hA0lt j h'; omega
            · simp at h'; omega
        subst hjjl
        have hT' : children (M.take x) j = [] := by rw [children_take, hjx]; simp
        have hG'z : G' = z := by rw [hG'def, hT']; rfl
        have hox : ρ.o x = psi (ρ.v x) z z := o_of_no_counted hC (by omega) (hG.ot_v x (by omega))
          (fun c hc => by have := mem_children hc; omega)
        have hGx : G = psi (ρ.v x) z z := by
          rw [hGdef, hjx, List.map_singleton, sumN_singleton (single_o hC hG (by omega)), hox]
        rw [hG'z, hGx] at hS
        exact hvx (brelS_z_psi hS)
      have ht := brelS_omega hG'ot hGot hS
      have hp := brelS_p hsP hpP hPt (single_omega hG'ot) (single_omega hGot) ht
      have hsLM : ∀ t ∈ one :: (Pl ++ [omega G]), Single t := by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨rfl, z, z, rfl⟩
        · rcases List.mem_append.mp ht with ht | ht
          · exact hsP t ht
          · simp at ht; rw [ht]; exact single_omega hGot
      have hpM : BRelS (sumN (one :: Pl ++ [omega G'])) (sumN (one :: (children M i).map (bumpTerm M ρ i))) := by
        rw [hmapM]
        rcases hXIc with rfl | ⟨rfl, hxi⟩
        · simpa using hp
        · have hxc : children M x = [] := by
            rw [List.eq_nil_iff_forall_not_mem]
            intro c hc; have := mem_children hc; omega
          by_cases hxb : col M x = bump M i
          · have hbx : bumpTerm M ρ i x = one := by
              unfold bumpTerm; rw [if_pos hxb, hxc]
              simp only [List.map_nil, sumN_nil]
              rw [omega_small (T.z_lt_psi _ _ _)]; rfl
            simp only [List.map_cons, List.map_nil, hbx]
            rw [show one :: (Pl ++ [omega G] ++ [one]) = (one :: (Pl ++ [omega G])) ++ [one] from rfl,
              sumN_snoc_ot (t := one) hsLM ⟨rfl, z, z, rfl⟩, add_one_eq_app]
            apply brelS_tail hp
            intro hz
            have := two_le_sumN_one_cons (l := Pl ++ [omega G]) (by simp)
              (fun t ht => hsLM t (List.mem_cons_of_mem _ ht))
            have hz' : sumN (one :: (Pl ++ [omega G])) = z := hz
            rw [hz'] at this
            exact absurd this (not_le_of_gt (T.z_lt_psi _ _ _))
          · have hbx : bumpTerm M ρ i x = z := by unfold bumpTerm; rw [if_neg hxb]
            simp only [List.map_cons, List.map_nil, hbx]
            rw [show one :: (Pl ++ [omega G] ++ [z]) = (one :: (Pl ++ [omega G])) ++ [z] from rfl,
              sumN_snoc_z (fun t ht => (hsLM t ht).1)]
            exact hp
      have hW := brelS_lhdE (brelS_omega hp'ot hpot hpM)
      by_cases hWE : omega (sumN (one :: (children M i).map (bumpTerm M ρ i))) < E0
      · left
        rw [ev', ev]
        apply v_strong hVot (single_omega hp'ot) (single_omega hpot) hW
        intro r hr _ hlt
        exact lhd_lt_small (isOT_mem_summands hVot hr) hWE hlt
      · have hSG : StrongG M x ρ i := by
          refine ⟨ρ', hC', fun j hjT hjb => ?_⟩
          rw [hA] at hjT
          rcases List.mem_append.mp hjT with hj0 | hj0
          · obtain ⟨hch, ho, -⟩ := early_sib hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi h2
              (mem_children_take (hA0T j hj0)).2 hjlT (hA0lt j hj0)
            rw [hch, List.map_congr_left ho]
            exact brelS_refl
          · simp at hj0; subst hj0; exact hS
        rcases hAbs ρ' hC' i h1 h2 hexcl (Or.inl hSG) with habs | hwk
        · left
          rw [ev', ev]
          apply v_strong hVot (single_omega hp'ot) (single_omega hpot) hW
          intro r hr hn hlt
          apply habs r hr _ hlt
          unfold bumpW
          rw [hmapT]
          simpa using hn
        · exact Or.inr hwk
    · -- the weak case (2026-10-25): `v′ ≤ v` from the sums, and `CntX` from the children (all bump children but `x`)
      by_cases hli : LhdE (ρ'.v i) (ρ.v i)
      · exact Or.inl hli
      have hkx' : (k = x ∧ children M jl = [x] ∧ ¬ LhdE (ρ'.v i) (ρ.v i)) ∨
          (k < x ∧ ρ'.o k ≠ ρ.o k ∧ ¬ LhdE (ρ'.v k) (ρ.v k)) := by
        rcases hkx with ⟨hk1, hk2⟩ | hk'
        · exact Or.inl ⟨hk1, hk2, hli⟩
        · exact Or.inr hk'
      have hwc := hWS.2 i hi hli
      have hωle : omega G' ≤ omega G := omega_le_omega hG'ot hGot hWk
      have hotL : ∀ t ∈ one :: (Pl ++ [omega G']), isOT t = true := fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht
        · rfl
        · exact (hsL t ht).1
      have hotR : ∀ t ∈ one :: (Pl ++ [omega G]), isOT t = true := fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht
        · rfl
        · rcases List.mem_append.mp ht with ht | ht
          · exact (hsP t ht).1
          · simp at ht; rw [ht]; exact isOT_omega hGot
      have hsum1 : sumN (one :: (Pl ++ [omega G'])) ≤ sumN (one :: (Pl ++ [omega G])) :=
        sumN_le2 (.cons (le_refl _) (forall2_le_snoc Pl hωle)) hotL hotR
      have hXIot : ∀ t ∈ XI.map (bumpTerm M ρ i), isOT t = true := fun t ht => by
        obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i d
      have hsum2 : sumN (one :: (Pl ++ [omega G])) ≤ sumN (one :: (children M i).map (bumpTerm M ρ i)) := by
        rw [hmapM, show one :: (Pl ++ [omega G] ++ XI.map (bumpTerm M ρ i)) =
          (one :: (Pl ++ [omega G])) ++ XI.map (bumpTerm M ρ i) from rfl]
        exact le_sumN_append _ _ hotR hXIot
      have hvle : ρ'.v i ≤ ρ.v i := by
        rw [ev', ev]
        exact add_le_add_single V (single_omega hp'ot).2 (single_omega hpot).2
          (omega_le_omega hp'ot hpot (le_trans hsum1 hsum2))
      have hvlt : ρ'.v i < ρ.v i := by
        rcases (le_iff _ _).mp hvle with h | h
        · exact h
        · exact absurd (Or.inl h) hli
      have h1v : one ≤ ρ'.v i := by
        rw [ev']
        exact le_trans (one_le_of_ne_z (single_ne_z (single_omega hp'ot))) (le_add_single V (single_omega hp'ot).2)
      have hwk : WkVA (ρ'.v i) (ρ.v i) := ⟨hvlt, h1v, hv'ot⟩
      have hTnc : ∀ c ∈ children (M.take x) i, ¬ Counted M i c := fun c hc hcnt => hcnt.1 (hAb c hc)
      refine Or.inr ⟨hwk, hwc, ?_⟩
      rcases hXIc with rfl | ⟨rfl, hxi⟩
      · refine Or.inl fun c hc => ?_
        rw [hXI, List.append_nil] at hc
        exact hTnc c hc
      · by_cases hxc : Counted M i x
        · obtain ⟨hub, hbp⟩ := hWS.1 i h1 h2 jl hjlM hjlb k hk ⟨w, y, hw, hok⟩ hkx' hxi hxc
          refine Or.inr (Or.inr ⟨fun c hc hcnt => ?_, hub, hbp⟩)
          rw [hXI] at hc
          rcases List.mem_append.mp hc with hc | hc
          · exact absurd hcnt (hTnc c hc)
          · simp at hc; omega
        · refine Or.inl fun c hc => ?_
          rw [hXI] at hc
          rcases List.mem_append.mp hc with hc | hc
          · exact hTnc c hc
          · simp at hc; rw [hc]; exact hxc

/-- **The bump-type `v` step of the drop** (the `Bad2` form). -/
theorem bump_dropB {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsCB M x ρ) (hWS : BumpWeakSrcB M x ρ ρ') :
    (∀ i, i < x → (∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < x →
        PO ρ ρ' k ∧ PV M ρ ρ' k) → ChgX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      PV M ρ ρ' i) ∧ WeakCS M x ρ ρ' := by
  refine ⟨fun i hi hIH hCv h1 h2 => ?_, hWS.2⟩
  obtain ⟨hot, hrel⟩ := bump_relB hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hKD hTD hAbs hWS hi hIH
    hCv h1 h2
  exact ⟨hrel, hot⟩

end Ytosk
