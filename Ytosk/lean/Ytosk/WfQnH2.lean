/-
**WfQnH2 (2026-11-01): `VLocal` and `OLocal` off the closure of the bad calls, from `TPLoSX` (step 1 of the q ≠ r
engine).**
- `vlocal_t1_at_locB`: `vlocal_t1_at_loc` (WfQnL1) with the low-part comparison `hTPLζ` asked only at `o` calls
  outside `DepXB M B` (it is read only at the last bump grandchild `k`, and `(true,k) ∈ DepXB → (false,i) ∈ DepXB`).
- `vlocal_t1_atXB`: with the `AbsDSX`-shaped field, every `v` call of `D` off `DepXB M (BadSet ..)` is `VLocal`.
-/
import Ytosk.WfQnL3

namespace Ytosk.WfQnH2
open T Ytosk Ytosk.WfQnE2 Ytosk.WfBad

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ br vr ζ X : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) {q : Nat} (hq : par M 0 x = some q)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
  (hrx : r < x) (hAr : Anc0 M r x) (hro : ρ.o r = psi vr br z)
  (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
  (hHx : HoleT μ br vr (ρ.o x))
  (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hS2 : ∀ i k, i ≤ r → DepX M x false i → entry M 2 i = 0 → upg M i = some k → k ≤ r)
  (hS3 : ∀ i j k, i ≤ r → j ∈ children M i → col M j = bump M i → k ∈ children M j →
    DepX M x true k → k ≤ r)
  {B : Nat → Prop}
  (hTPLζ : ∀ c, c < M.length → DepX M x true c → ¬ WfQnE3.DepXB M B true c → ∀ s y, ρ.o c = psi s y z →
    (split y (psi (succ s) z z)).2 = z → ∀ a, last y = psi a z z → isSucc a = false →
    OHole a → holeLev y = μ → ¬ psi (fsD a ζ) z z < psi (succ s) z z) (hAUζ : ∀ i k, i < x → DepX M x false i → upg M i = some k →
    OHole (last (ρ.v k)) → holeLev (last (ρ.v k)) = μ →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) → q < fsD (last (ρ.v k)) ζ) (hbrl : last br ≠ psi (succ μ) z z)
  (hζ : ζ = psi μ X z) (hXz : X ≠ z) (hζfix : omega ζ = ζ) (hζΩ : etaOm μ ≤ ζ)
  (hok : ∀ t, isOT t = true → HoleT μ br vr t → isOT (fsD t ζ) = true ∧ fsD t ζ < t)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hAr hro hcb hμr hbr hHx hF1 hOS hS2 hS3
  hTPLζ hAUζ hbrl hζ hXz hζfix hζΩ hok

/-- **`VLocal` at one call**, with the absorption field asked only there. -/
theorem vlocal_t1_at_locB (i : Nat) (hi : i < x) (hv : DepX M x false i) (hnb : ¬ WfQnE3.DepXB M B false i)
    (hADi : entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → OHole (bumpW M ρ i) →
      holeLev (bumpW M ρ i) = μ → ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
        q < fsD (bumpW M ρ i) ζ) : VLocal M x ρ ζ μ i := by
  have hH := t1_hole0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hAr hro hcb hμr hbr hHx
    hF1 hOS hS2 hS3
  have hζz : ζ ≠ z := by rw [hζ]; simp
  obtain ⟨h1, hpd, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hv
  refine ⟨h1, hpd, ?_⟩
  rcases hcase with ⟨h2, hu, hk, hdk⟩ | ⟨h2, L, K, j, k, hch, hjb, hchj, hdk, hKnd, hLnd⟩
  · -- the upgrade frame
    left
    obtain ⟨hHk, _, hSk⟩ := hH false (i + 1) hdk (Or.inl hk)
    simp only [valB, cond_false] at hHk
    have hk2 : entry M 2 (i + 1) ≠ 0 := by have := upg_target_e2 hu; omega
    have hVs := hSk rfl hk2
    have hkM : i + 1 < M.length := by omega
    have hHl := holeT_last_g hHk
    refine ⟨i + 1, h2, hu, hk, hVs, ?_, ?_⟩
    · apply single_fsD hVs.2 (holeT_not_succ hHl)
        (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHl)) ⟨μ, X, hζ⟩
      exact (hok _ hVs.1 hHl).1
    · intro t ht hlt
      have hOk := ohole_of_holeT hHl
      exact hAUζ i (i + 1) hi hv hu hOk (holeLev_holeT hHl) t ht hlt
  · -- the bump frame
    right
    have hkM : k < M.length := by
      have : k ∈ children M j := by rw [hchj]; simp
      exact (mem_children this).2
    obtain ⟨hHk, _, _⟩ := hH true k hdk (by
      rcases Nat.lt_or_ge k x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, rfl⟩)
    simp only [valB, cond_true] at hHk
    obtain ⟨hBD, _, _, _⟩ := v_bump_D hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hi h1 h2
      hch hjb hchj hHk
    set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
    set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
    have hkS : Single (ρ.o k) := hBD.sK _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hGot : isOT G = true := (sumN_dec _ hBD.sK hBD.pK).1
    have hGe : G = app (sumN (K.map ρ.o)) (ρ.o k) := sumN_snoc_dec hBD.sK hBD.pK
    have hHG : HoleT μ br vr G := by rw [hGe]; exact holeT_app _ (single_ne_z hkS) hHk
    have hHωG := holeT_omega hGot hHG hBD.passG
    have hωGz : omega G ≠ z := holeT_ne_z hHωG
    have hHY2 : HoleT μ br vr (app (sumN P) (omega G)) := holeT_app _ hωGz hHωG
    have hHW := holeT_omega hBD.potW hHY2 hBD.passP
    -- `fsD(o(k), ζ)`
    obtain ⟨hfkot, hfklt⟩ := hok _ (hG.ot_o k hkM) hHk
    have hfkS : Single (fsD (ρ.o k) ζ) := by
      apply single_fsD (o_psi_form hC hkM) (holeT_not_succ hHk)
        (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHk)) ⟨μ, X, hζ⟩ hfkot
    have hfkz : fsD (ρ.o k) ζ ≠ z := single_ne_z hfkS
    set G' := sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]) with hG'def
    have hsK' : ∀ t ∈ K.map ρ.o ++ [fsD (ρ.o k) ζ], Single t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hBD.sK t (List.mem_append_left _ ht)
      · rw [List.mem_singleton] at ht; rw [ht]; exact hfkS
    have hpK' : (K.map ρ.o ++ [fsD (ρ.o k) ζ]).Pairwise (fun a b => b ≤ a) := by
      have hpK := hBD.pK
      rw [List.pairwise_append] at hpK ⊢
      refine ⟨hpK.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb; rw [hb]
      exact le_trans (le_of_lt hfklt) (hpK.2.2 a ha _ (List.mem_singleton_self _))
    have hG'ot : isOT G' = true := (sumN_dec _ hsK' hpK').1
    have hG'e : G' = app (sumN (K.map ρ.o)) (fsD (ρ.o k) ζ) := sumN_snoc_dec hsK' hpK'
    have hG'z : G' ≠ z := by rw [hG'e]; intro he; exact hfkz (app_eq_z he).2
    have hG'lt : G' < G := by rw [hG'e, hGe]; exact app_lt_app_left _ hfklt
    have hωle : omega G' ≤ omega G := le_of_lt (omega_lt_omega hG'ot hGot hG'lt)
    have hfG : fsD G ζ = G' := by rw [hGe, hG'e]; exact fsD_app _ (single_ne_z hkS) ζ
    -- TPL for `G` and for `P + ω^G`
    have hTG : ∀ s b, G = psi s b z → (split b (psi (succ s) z z)).2 = z → ∀ a, last b = psi a z z →
        isSucc a = false → OHole a → ¬ psi (fsD a ζ) z z < psi (succ s) z z := by
      intro s b hGsb hl a hla has hOa
      have hK0 : sumN (K.map ρ.o) = z := by
        by_contra hK
        exact app_single_ne hK (single_ne_z hkS) (by rw [← hGe]; exact hGsb)
      have hok' : ρ.o k = psi s b z := by rw [← hGsb, hGe, hK0]; rfl
      have hb : b ≠ z := by
        intro hb0; rw [hb0] at hla; simp [last] at hla
      have hHb := holeT_arg hb (by rw [← hok']; exact hHk) hcb
      have hjm : j ∈ children M i := by rw [hch]; simp
      have hkm : k ∈ children M j := by rw [hchj]; simp
      exact hTPLζ k hkM hdk (fun hd => hnb (WfQnE3.DepXB.vbump h1 h2 hjm hjb hkm hd)) s b hok' hl a hla has hOa
        (holeLev_holeT hHb)
    have hTY2 : ∀ s b, app (sumN P) (omega G) = psi s b z → (split b (psi (succ s) z z)).2 = z →
        ∀ a, last b = psi a z z → isSucc a = false → OHole a →
        ¬ psi (fsD a ζ) z z < psi (succ s) z z := by
      intro s b hY hl
      have hP0 : sumN P = z := by
        by_contra hP; exact app_single_ne hP hωGz hY
      rw [hP0] at hY
      have hY' : omega G = psi s b z := hY
      have hfix := omega_single_nolo hGot (holeT_ne_z hHG) hY' hl
      exact hTG s b (by rw [← hfix]; exact hY') hl
    have hωGfs : fsD (omega G) ζ = omega G' := by
      rw [omega_fsD_hole_at hGot hHG hcb hbrl hζ hXz hζfix hζΩ hok hTG, hfG]
    have hωp : fsD (omega (app (sumN P) (omega G))) ζ = omega (app (sumN P) (omega G')) := by
      rw [omega_fsD_hole_at hBD.potW hHY2 hcb hbrl hζ hXz hζfix hζΩ hok hTY2,
        fsD_app _ hωGz ζ, hωGfs]
    -- absorption
    have hOW : OHole (bumpW M ρ i) := by rw [hBD.W]; exact ohole_of_holeT hHW
    have hA2 := hADi h1 h2 hOW (by rw [hBD.W]; exact holeLev_holeT hHW)
    rw [hBD.W] at hA2
    refine ⟨L, K, j, k, h2, hch, hjb, hchj, hKnd, hLnd, hfkS, hBD.sK, hBD.pK, hBD.sL, hBD.pp, ?_,
      hBD.gt, ?_, hωp, ?_, hBD.passG, hBD.passP⟩
    · -- pairwise with `ω^{G'}`
      have hpp := hBD.pp
      rw [List.pairwise_append] at hpp ⊢
      refine ⟨hpp.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb; rw [hb]
      exact le_trans hωle (hpp.2.2 a ha _ (List.mem_singleton_self _))
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hBD.gt t (List.mem_append_left _ ht)
      · rw [List.mem_singleton] at ht; rw [ht, ← omega_z]
        exact omega_lt_omega rfl hG'ot (lt_of_le_of_ne (z_le _) (Ne.symm hG'z))
    · intro t ht hlt
      rw [← hωp]
      exact hA2 t ht hlt


/-- **`VLocal` off the closure of the bad calls** (`TPLoS` asked only off the closure). -/
theorem vlocal_t1_atXB
    (hADX : ∀ i, i < x → DepX M x false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → OHole (bumpW M ρ i) →
      holeLev (bumpW M ρ i) = μ → ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
        q < fsD (bumpW M ρ i) ζ ∨ (BadShape1 M i ∧ bumpW M ρ i = ρ.o r))
    (hBB : B = BadSet M x ρ r ζ) :
    ∀ i, i < x → DepX M x false i → ¬ WfQnE3.DepXB M B false i → VLocal M x ρ ζ μ i := by
  intro i hi hv hnb
  apply vlocal_t1_at_locB hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hAr hro hcb hμr hbr hHx
    hF1 hOS hS2 hS3 hTPLζ hAUζ hbrl hζ hXz hζfix hζΩ hok i hi hv hnb
  intro h1 h2 hO hl
  have hb : ¬ BadCall M ρ r ζ i := by
    intro hb; subst hBB; exact hnb (WfQnE3.DepXB.leaf ⟨hi, hv, hb⟩)
  exact absorbed_of_not_bad (fun q hq hlt => hADX i hi hv h1 h2 hO hl q hq hlt) h1 h2 hb

end

end Ytosk.WfQnH2
