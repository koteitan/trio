/-
**3 行・t = 2・q ≠ r: 種 v(q) の ◁。**

q = P_0(x) ≠ r のとき x は q の bump 子（列が bump M q）で子がない。M では q の bump の項に ω^0 = 1 が
入るが、N では位置 x の列 x′ の行 2 が 0 なので bump 子でない。したがって
v_M(q) = V + ω^(S+1)、v_N(q) = V + ω^S（S = 1 + 他の bump の項の和）で、v_N(q) ◁ v_M(q)
（`v_bump_lost`）。V の加数で ω^S 以上 ω^(S+1) 未満のものは ω^S だけなので、吸収の仮定は要らない。
-/
import Ytosk.V3T2G
import Ytosk.V3T0B

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- A single summand between `ψ_s(b′)` and `ψ_s(b′ + 1)` is `ψ_s(b′)`. -/
theorem single_between {r s b' : T} (hr : ∃ s2 y2, r = psi s2 y2 z) (h1 : ¬ r < psi s b' z)
    (h2 : r < psi s (succ b') z) : r = psi s b' z := by
  obtain ⟨s2, y2, rfl⟩ := hr
  rw [psi_lt_psi_z_iff] at h1 h2
  rcases h2 with h2 | ⟨rfl, h2⟩
  · exact absurd (Or.inl h2) h1
  · rcases (le_iff _ _).mp (lt_succ_iff.mp h2) with h | h
    · exact absurd (Or.inr ⟨rfl, h⟩) h1
    · rw [h]

/-- `ω^S ◁ ω^(S+1)`. -/
theorem lhd_omega_succ {S : T} (hS : isOT S = true) : Lhd z (omega S) (omega (succ S)) := by
  obtain ⟨s, b', h1, h2⟩ := omega_succ_form hS
  have := lhd_mulT (η := z) (a := s) (b' := b') 1
  simp only [mulT, app_psi, app_z] at this
  rw [succ, h1, h2]; exact this

/-- **The lost bump term**: the last child `j` of `i` is a bump child without children in `M` and not a
bump child in `N`; then `v_N(i) ◁ v_M(i)`. -/
theorem v_bump_lost {M N : Mat} {ρ σ : Valn} {i j : Nat} {L : List Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hiM : i < M.length) (hiN : i < N.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (he1 : entry N 1 i = entry M 1 i)
    (he2 : entry N 2 i = entry M 2 i) (hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i))
    (hchM : children M i = L ++ [j]) (hchN : children N i = L ++ [j])
    (hbL : ∀ d ∈ L, bumpTerm N σ i d = bumpTerm M ρ i d)
    (hbjM : bumpTerm M ρ i j = one) (hbjN : bumpTerm N σ i j = z) :
    Lhd z (σ.v i) (ρ.v i) := by
  set V := vOpt ρ (par M 1 i) with hVdef
  have hVot : isOT V = true := by
    rw [hVdef]
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  set Lb := L.map (bumpTerm M ρ i) with hLb
  have hPot : ∀ t ∈ one :: Lb, isOT t = true := fun t ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i d
  set Sp := sumN (one :: Lb) with hSp
  have hSot : isOT Sp = true := isOT_sumN _ hPot
  have hsumM : sumN (one :: (children M i).map (bumpTerm M ρ i)) = succ Sp := by
    rw [hchM, List.map_append, List.map_singleton, hbjM, ← List.cons_append, sumN_snoc,
      add_one_eq_succ hSot, sf_ot (isOT_succ hSot)]
  have hsumN : sumN (one :: (children N i).map (bumpTerm N σ i)) = Sp := by
    rw [hchN, List.map_append, List.map_singleton, hbjN, List.map_congr_left hbL, ← List.cons_append,
      sumN_snoc_z hPot]
  have ev : ρ.v i = add V (omega (succ Sp)) := by
    rw [(hC i hiM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, hsumM, sf_ot (isOT_add hVot (isOT_omega (isOT_succ hSot)))]
  have ev' : σ.v i = add V (omega Sp) := by
    rw [(hCN i hiN).2]; unfold vRhs
    rw [he1, he2, if_neg h1, if_neg h2, hV, hsumN, sf_ot (isOT_add hVot (isOT_omega hSot))]
  have hl := lhd_omega_succ hSot
  have hE : LhdE (σ.v i) (ρ.v i) := by
    rw [ev', ev]
    apply v_strong hVot (single_omega hSot) (single_omega (isOT_succ hSot)) (Or.inr hl)
    intro r hr hn hlt
    obtain ⟨s, b', h1', h2'⟩ := omega_succ_form hSot
    rw [h1'] at hn
    rw [show succ Sp = app Sp one from rfl, h2'] at hlt ⊢
    have := single_between (mem_summands hr) hn hlt
    rw [this, ← h1', ← h2']; exact hl
  apply lhd_of_lhdE_lt hE
  rw [ev', ev]
  exact add_lt_add_left V (omega_lt_omega hSot (isOT_succ hSot) (lt_succ_self Sp))

section
variable {M : Mat} {S : Bool → Nat → Prop} (hUAT : UAT M) (hZ2 : Z2 M) (hR12 : R12 M) (hBE : BumpE2 M)
include hUAT hZ2 hR12 hBE

/-- **Up the path, `DepS` continues** (general start, the subtrees may continue below `d`): if `o(d)` is in `D`, `d` is neither a bump child nor upgraded, and the subtree of every
column strictly between `a` and `d` on the path ends at `d`, then `o(a)` is in `D`. -/
theorem path_upS (n : Nat) : ∀ a d, d - a ≤ n → d < M.length → Anc0 M a d →
    (∀ p, ((∃ t, par M 0 p = some t ∧ col M p = bump M t) ∨ isUpg M p = true) → p ≠ d) →
    DepS M S true d → (∀ t, a < t → Anc0 M t d → ∃ e, e < M.length ∧ Anc0 M d e ∧ ¬ Anc0 M t (e + 1)) →
    DepS M S true a := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro a d hn hdl had hd2 hD hend
  have key : ∀ m t, d - t ≤ m → Anc0 M a t → Anc0 M t d → DepS M S true t := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
    intro t hm hat htd
    by_cases htd' : t = d
    · subst htd'; exact hD
    obtain ⟨p, hpt, hpd⟩ := anc0_child htd htd'
    have htp := par_lt M 0 p t hpt
    have hpdl := hpd.le
    have hpl : p < M.length := by omega
    have hpM : p ∈ children M t := mem_children_iff.mpr ⟨hpl, hpt⟩
    have hat' := hat.le
    have hap : Anc0 M a p := Anc0.trans hat (Anc0.step hpt (Anc0.refl t))
    have hDp : DepS M S true p := ihm (d - p) (by omega) p (Nat.le_refl _) hap hpd
    by_cases hc : Counted M t p
    · exact DepS.ochild hpM hc.1 hc.2 hDp
    · rcases not_counted_iff hc with hb | ⟨hiu, htop⟩
      · -- a bump edge: `v(t)` reads the grandchild on the path
        have hp2 : entry M 2 p = 1 := e2_of_col (show col M p = (entry M 0 t + 1, entry M 1 t, 1) from hb)
        have hpd' : p ≠ d := hd2 p (Or.inl ⟨t, hpt, hb⟩)
        obtain ⟨p', hpp', hp'd⟩ := anc0_child hpd hpd'
        have hp'dl := hp'd.le
        have hp'M : p' ∈ children M p := mem_children_iff.mpr ⟨by omega, hpp'⟩
        have hpp'lt := par_lt M 0 p' p hpp'
        have hDp' : DepS M S true p' := ihm (d - p') (by omega) p' (Nat.le_refl _)
          (Anc0.trans hap (Anc0.step hpp' (Anc0.refl p))) hp'd
        have he1 : entry M 1 t ≠ 0 := by
          have h1 : entry M 1 p = entry M 1 t :=
            e1_of_col (show col M p = (entry M 0 t + 1, entry M 1 t, 1) from hb)
          intro h0
          rw [← h1] at h0
          have := hR12 p h0
          omega
        have he2 : entry M 2 t ≠ 0 := by rw [hBE t p hpM hb]; omega
        exact DepS.ov (DepS.vbump he1 he2 hpM hb hp'M hDp')
      · -- an upgraded, topped child: around through `p − 1`
        have hiu0 := hiu
        unfold isUpg at hiu
        rw [List.any_eq_true] at hiu
        obtain ⟨k0, _, hk0⟩ := hiu
        have hu : upg M k0 = some p := of_decide_eq_true hk0
        have hk0p : k0 = p - 1 := by
          obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
          rcases hcase with h | ⟨hA, hlt⟩
          · omega
          · exfalso
            have := hUAT k0 p hu (by have := hA.le; omega)
            rw [this] at htop; cases htop
        rw [hk0p] at hu
        obtain ⟨_, _, _, hcol, _⟩ := upg_spec hu
        have hp2 := upg_target_e2 hu
        have hpd' : p ≠ d := hd2 p (Or.inr hiu0)
        have hpd2 : p < d := by omega
        obtain ⟨p', hpp', hp'd⟩ := anc0_child hpd hpd'
        have hp'dl := hp'd.le
        have hpp'lt := par_lt M 0 p' p hpp'
        have hp'M : p' ∈ children M p := mem_children_iff.mpr ⟨by omega, hpp'⟩
        obtain ⟨e, hel, hde, hne⟩ := hend p (by omega) hpd
        have hlast := last_child_path hel hpp' (Anc0.trans hp'd hde) hne
        unfold topped at htop
        rw [hlast] at htop
        have hb' : col M p' = bump M p := by simpa using htop
        have hp'2 : entry M 2 p' = 1 :=
          e2_of_col (show col M p' = (entry M 0 p + 1, entry M 1 p, 1) from hb')
        have hp'd' : p' ≠ d := hd2 p' (Or.inl ⟨p, hpp', hb'⟩)
        obtain ⟨p'', hpp'', hp''d⟩ := anc0_child hp'd hp'd'
        have hp''dl := hp''d.le
        have hpp''lt := par_lt M 0 p'' p' hpp''
        have hp''M : p'' ∈ children M p' := mem_children_iff.mpr ⟨by omega, hpp''⟩
        have hDp'' : DepS M S true p'' := ihm (d - p'') (by omega) p'' (Nat.le_refl _)
          (Anc0.trans hap (Anc0.step hpp'' (Anc0.step hpp' (Anc0.refl p)))) hp''d
        obtain ⟨he1, he2⟩ := upg_e12 hu
        have he2z : entry M 2 (p - 1) = 0 := by have := hZ2 (p - 1); omega
        have hp1 : entry M 1 p = entry M 1 (p - 1) := e1_of_col hcol
        have hvp : DepS M S false p :=
          DepS.vbump (by rw [hp1]; exact he1) (by omega) hp'M hb' hp''M hDp''
        have hvp1 : DepS M S true (p - 1) := DepS.ov (DepS.vupg he1 he2z hu hvp)
        have hAt : Anc0 M t (p - 1) :=
          anc_between (Anc0.step hpt (Anc0.refl t)) (p - 1) (by omega) (by omega)
        refine ihn ((p - 1) - t) (by omega) t (p - 1) (Nat.le_refl _) (by omega) hAt (ne_of_e2z he2z) hvp1 ?_
        intro u htu hup
        refine ⟨p - 1, by omega, Anc0.refl _, fun hup' => ?_⟩
        rw [show p - 1 + 1 = p by omega] at hup'
        by_cases hup2 : u = p
        · have := hup.le; omega
        · have := (anc0_par hup' hup2 hpt).le; omega
  exact key (d - a) a (Nat.le_refl _) (Anc0.refl a) had

end

end Ytosk
