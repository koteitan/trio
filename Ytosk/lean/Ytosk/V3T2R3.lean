/-
**3 行・t = 2: seed1 の残り（sv・C）を証明し、hR2 を T2BelowXRes だけから出す（`hR2_t2_of`）。**

- sv（q = r、x − 1 = s が x へ上げる）: v(s) = v(x) = V + ω（x は子を持たない）、M′ = M.take x では s は最後の列で
  上げないので v′(s) = V + 1。よって v′(s) < v(s)、strict_top（a = r）で o′(r) < o(r)。
- C（q ≠ r、q が pq で数えられない）: q は上げの的で topped なので upg(q − 1) = q（UAT）。
  v′(q) < v(q)（v_strict_bump_x）と v(q − 1) = v(q) で v′(q − 1) < v(q − 1)、strict_top（a = pq、s = q − 1）。
-/
import Ytosk.V3T2R2
import Ytosk.V3T2Seed1G

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- The drop to `M.take x` from `Inv3 ∧ Res3`: consistency, ranking, `Good3` and the drop lemma. -/
theorem t2_drop_ctx {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) (R : Res3 M ρ rk)
    {x : Nat} (hlen : x + 1 = M.length) :
    Cons (M.take x) (drop1 M x rk) ∧ Rk (M.take x) rk ∧ Good3 (M.take x) (drop1 M x rk) ∧
      ∀ i, i < x → PO ρ (drop1 M x rk) i ∧ PV M ρ (drop1 M x rk) i := by
  have hdr : DropRes M x ρ (drop1 M x rk) := by
    have := R.drop; rw [show M.length - 1 = x by omega] at this; exact this
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = x by omega] at hcnt
  have hRk1 : Rk (M.take x) rk := rk_take (by omega) I.rank hcnt
  have hC1 : Cons (M.take x) (drop1 M x rk) := cons_of_rk hRk1
  have hG1 := good3_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank
    ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hdr
  have hdrop := drop_all hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs hdr.vst
    I.fc I.fo hdr.argT
    (bump_drop hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td hdr.ab hdr.ws)
    hdr.ua
  exact ⟨hC1, hRk1, hG1, fun i hi => ⟨(hdrop i hi).1, (hdrop i hi).2⟩⟩

/-- The row-1 parent `m` of a column `i < x` keeps its `v` under the drop. -/
theorem v_par1_keep {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    {i m : Nat} (hi : i < x) (hm : par M 1 i = some m) : ρ'.v m = ρ.v m := by
  have hml := par_lt M 1 i m hm
  apply ((chg_off hx hC hG hC' hRk') m (by omega)).2
  intro hCm
  exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCm).1 rfl (by omega) |>.2.2 i hi hm

/-- **seed1, `x − 1` upgrades to `x`.** -/
theorem t2Seed1SV_holds : T2Seed1SV := by
  intro M ρ rk hM I R hz h2 r L hlen hr hq hux
  obtain ⟨hC1, hRk1, hG1, hdrop⟩ := t2_drop_ctx I R hlen
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hrs : r ≠ r + L - 1 := rx_of_sv hlen I.z2 I.z1 hr hux
  obtain ⟨_, h1lt⟩ := par2_facts I.z2 (by omega) hr
  have hxM : r + L < M.length := by omega
  set s := r + L - 1 with hsdef
  have hs1 : s + 1 = r + L := by omega
  obtain ⟨h1s, h2s'⟩ := upg_e12 hux
  have h2s : entry M 2 s = 0 := by have := I.z2 s; omega
  obtain ⟨m, hm1s, hm1x, _, _⟩ := upg_spec hux
  have hml := par_lt M 1 s m hm1s
  have hVot : isOT (ρ.v m) = true := I.good.ot_v m (by omega)
  -- `v(s) = v(x) = V + ω`
  have ek : ρ.v s = ρ.v (r + L) := v_upg_eq I.cons (by omega) h1s h2s hux (by rw [hm1s]; exact hVot)
    (fun _ _ _ k' hk' => I.good.ot_o k' (mem_children hk').2)
  have hx2 : entry M 2 (r + L) ≠ 0 := by
    have := (upg_target_e2 hux); omega
  have hx1 : entry M 1 (r + L) ≠ 0 := fun h => hx2 (I.r12 _ h)
  have hsum1 : sumN [one] = one := rfl
  have hvx : ρ.v (r + L) = sf (add (ρ.v m) (omega one)) := by
    rw [(I.cons (r + L) hxM).2]; unfold vRhs
    rw [if_neg hx1, if_neg hx2, children_last_nil hlen, hm1x]
    simp only [List.map_nil]
    rw [hsum1]; rfl
  -- `v′(s) = V + 1`
  have hlenT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hsT : s < (M.take (r + L)).length := by omega
  have hvm : (drop1 M (r + L) rk).v m = ρ.v m :=
    v_par1_keep hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 (by omega) hm1s
  have hvs' : (drop1 M (r + L) rk).v s = sf (add (ρ.v m) one) := by
    rw [(hC1 s hsT).2]; unfold vRhs
    rw [entry_take M 1 (by omega), entry_take M 2 (by omega), if_neg h1s, if_pos h2s,
      par_take M 1 s (by omega), hm1s]
    have hup : upg (M.take (r + L)) s = none := by
      rw [hsdef]; exact upg_take_last M (by omega) (by omega)
    rw [hup]
    show sf (add ((drop1 M (r + L) rk).v m) one) = _
    rw [hvm]
  have hone : one < omega one := by
    have := omega_lt_omega (x := z) (y := one) rfl rfl (T.z_lt_psi _ _ _)
    rwa [omega_z] at this
  have hvlt : (drop1 M (r + L) rk).v s < ρ.v s := by
    rw [ek, hvx, hvs', sf_ot (isOT_add hVot rfl), sf_ot (isOT_add hVot (isOT_omega rfl))]
    exact add_lt_add_left _ hone
  -- the top step at `r`
  have hAx : Anc0 M r (r + L) := Anc0.step hq (Anc0.refl r)
  have hxbr : col M (r + L) ≠ bump M r := fun h => by
    have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
  have hlt := strict_top hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop hG1 I.be I.r12
    (a := r) (s := s) (by omega) h2s hvlt (anc_between hAx s (by omega) (by omega)) hrs
    ⟨r, by rw [hs1]; exact hq, le_refl r⟩
    (fun d hd hsd => by
      have hdl := (mem_children hd).2
      have hdx : d = r + L := by omega
      rw [hdx]
      refine ⟨fun hcnt => hcnt.2 ⟨?_, ?_⟩, hxbr⟩
      · unfold isUpg; apply List.any_eq_true.mpr
        exact ⟨s, List.mem_range.mpr (by omega), by simpa using hux⟩
      · unfold topped; rw [children_last_nil hlen]; rfl)
    (fun t ht h => by rw [hq] at ht; cases ht; omega)
  exact ne_of_lt hlt

/-- **seed1, `q ≠ r` is not a counted child of `pq`.** -/
theorem t2Seed1C_holds : T2Seed1C := by
  intro M ρ rk hM I R hz h2 r L q pq hlen hr hq hqr hpq hcl
  have hS : M ≠ SRO := ne_SRO_of_rk I.rank
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨hC1, hRk1, hG1, hdrop⟩ := t2_drop_ctx I R hlen
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hpqq : pq < q := par_lt M 0 _ _ hpq
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hrq : Anc0 M r q := anc0_par hA (by have := par_lt M 2 _ _ hr; omega) hq
  have hrq' : r ≤ q := hrq.le
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, Tqb, _, Tclq, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb Tqb Tclq
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have hqc : q ∈ children M pq := mem_children_iff.mpr ⟨by omega, hpq⟩
  have he2q := hX.loc.2.2.1 q (r + L) hxq Txb
  have h2q : entry M 2 q ≠ 0 := by omega
  have h1q : entry M 1 q ≠ 0 := fun h => h2q (I.r12 _ h)
  -- `q` is an upgrade target of `q − 1`
  have hncnt : ¬ Counted M pq q := fun h => hcl (by
    unfold CL; exact List.mem_filter.mpr ⟨hqc, by simpa using h⟩)
  have hupT : isUpg M q = true ∧ topped M q = true := by
    by_contra hn; exact hncnt ⟨Tqb, hn⟩
  have hup := hupT.1
  unfold isUpg at hup
  obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hup
  have hk0' : upg M k0 = some q := of_decide_eq_true hk0
  have hck : q = k0 + 1 := by
    by_contra hne
    have := I.uat k0 q hk0' hne; rw [hupT.2] at this; cases this
  obtain ⟨h1s, h2s'⟩ := upg_e12 hk0'
  have h2s : entry M 2 k0 = 0 := by have := I.z2 k0; omega
  -- `v′(q) < v(q)`, then `v′(q − 1) < v(q − 1)`
  have hvq : (drop1 M (r + L) rk).v q < ρ.v q :=
    v_strict_bump_x hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop hqx h1q h2q
      (children_split_x hlen hxq) Txb
  have hVot : isOT (vOpt ρ (par M 1 k0)) = true := by
    cases hp : par M 1 k0 with
    | none => rfl
    | some m' => exact I.good.ot_v m' (by have := par_lt M 1 k0 m' hp; omega)
  have ek : ρ.v k0 = ρ.v q := v_upg_eq I.cons (by omega) h1s h2s hk0' hVot
    (fun _ _ _ k' hk' => I.good.ot_o k' (mem_children hk').2)
  have hlenT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have huT : upg (M.take (r + L)) k0 = some q := by rw [upg_take M (by omega)]; exact hk0'
  have hVot' : isOT (vOpt (drop1 M (r + L) rk) (par (M.take (r + L)) 1 k0)) = true := by
    cases hp : par (M.take (r + L)) 1 k0 with
    | none => rfl
    | some m' => exact hG1.ot_v m' (by have := par_lt (M.take (r + L)) 1 k0 m' hp; omega)
  have ek' : (drop1 M (r + L) rk).v k0 = (drop1 M (r + L) rk).v q :=
    v_upg_eq hC1 (by omega) (by rw [entry_take M 1 (by omega)]; exact h1s)
      (by rw [entry_take M 2 (by omega)]; exact h2s) huT hVot'
      (fun _ _ _ k' hk' => hG1.ot_o k' (mem_children hk').2)
  have hvs : (drop1 M (r + L) rk).v k0 < ρ.v k0 := by rw [ek, ek']; exact hvq
  -- `q − 1` is not `pq`
  have hk0pq : k0 ≠ pq := by
    intro h
    obtain ⟨m', hm1, _, hcol, _⟩ := upg_spec hk0'
    have hmA := anc0_of_par M 1 m' k0 hm1
    have hmlt := par_lt M 1 k0 m' hm1
    have hme := anc0_e0_lt hmA (by omega)
    have h0 : entry M 0 q = entry M 0 m' + 1 := by
      rw [col_eq_entries] at hcol; exact (Prod.mk.inj hcol).1
    have h0' := I.r0p _ _ hpq
    rw [h] at hme
    omega
  have hApq : Anc0 M pq q := Anc0.step hpq (Anc0.refl pq)
  have hAqx : Anc0 M q (r + L) := Anc0.step hq (Anc0.refl q)
  have hlt := strict_top hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop hG1 I.be I.r12
    (a := pq) (s := k0) (by omega) h2s hvs (anc_between hApq k0 (by omega) (by omega)) (Ne.symm hk0pq)
    ⟨pq, by rw [← hck]; exact hpq, le_refl pq⟩
    (fun d hd hsd => by
      by_cases hdq : d = q
      · rw [hdq]; exact ⟨hncnt, Tqb⟩
      · exfalso
        have hdl := (mem_children hd).2
        have hAqd : Anc0 M q d := anc_between hAqx d (by omega) (by omega)
        have := par0_ge_of_anc hAqd (by omega) (le_refl d) (mem_children_iff.mp hd).2
        omega)
    (fun t ht h => by rw [hq] at ht; cases ht; omega)
  exact ne_of_lt hlt

/-- **`hR2` for `t = 2`** from `T2BelowXRes` only. -/
theorem hR2_t2_of (hB : T2BelowXRes) :
    ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk :=
  hR2_t2 hB t2Seed1SV_holds t2Seed1C_holds

end Ytosk
