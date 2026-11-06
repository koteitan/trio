/-- `t = 2` matrices have at least two columns. -/
theorem len2_of_t2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) : 2 ≤ M.length := by
  obtain ⟨r, hr⟩ := parLast_of Ctx.S.e00 Ctx.S.r01 Ctx.S.r12 hz
  rw [h2] at hr
  have := par_lt M 2 _ r hr
  omega

/-- `sv_children_ctx` (V3T2SeedRes) on the V3 context: `Good3` of `M.take x` from `DropV3`. -/
theorem sv_children_ctxV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    {τ : Valn} (hτ : Cons (M.take (r + L)) τ) :
    Good3 (M.take (r + L)) τ ∧ τ.v r = ρ.v r ∧
      ∀ d ∈ children (M.take (r + L)) r, succ (ρ.v r) < τ.v d := by
  obtain ⟨hX, _⟩ := sInvXJ_std hM hS
  have hxM : r + L < M.length := by omega
  have hrx : r < r + L := par_lt M 0 _ _ hq
  obtain ⟨he2r, he1x⟩ := par2_facts I.z2 hxM hr
  have he2x : entry M 2 (r + L) = 1 := by
    obtain ⟨_, _, _, he2, _, _⟩ := (par2_iff M hxM).mp hr
    have h' : entry M 2 r < entry M 2 (r + L) := he2
    have := I.z2 (r + L); omega
  have hτ' : Cons (M.take (M.length - 1)) τ := by rw [show M.length - 1 = r + L by omega]; exact hτ
  have hG := good3_take_anyV3U I (Ctx.drop (by omega)) (by omega) hτ'
  rw [show M.length - 1 = r + L by omega] at hG
  have hvr : τ.v r = ρ.v r :=
    v_take_of_untopped I (by omega) hrx (topP_sv hlen I.z2 I.z1 hr hq hux) hτ
  refine ⟨hG, hvr, fun c0 hc0 => ?_⟩
  have hc0x : c0 < r + L := by have := (mem_children hc0).2; rw [List.length_take] at this; omega
  have hpc : par M 0 c0 = some r := by
    have := (mem_children_iff.mp hc0).2; rwa [par_take M 0 c0 hc0x] at this
  have hcM : c0 ∈ children M r := mem_children_iff.mpr ⟨by omega, hpc⟩
  have hcol := t_child_col hX hq hxM he2x he1x hcM (le_of_lt hc0x)
  have hcx := t_col_x hX hq hxM he2x he1x
  have h1 : entry M 1 c0 = entry M 1 r + 1 := by
    have : entry M 1 c0 = (col M c0).2.1 := rfl; rw [this, hcol, hcx]
  have h2 : entry M 2 c0 = 1 := by
    have : entry M 2 c0 = (col M c0).2.2 := rfl; rw [this, hcol, hcx]
  have hp1 : par (M.take (r + L)) 1 c0 = some r := by
    rw [par_take M 1 c0 hc0x]; exact par1_of_child hpc (by omega)
  have hlt := v_child_gt hτ hG (by rw [List.length_take]; omega) (by rw [List.length_take]; omega) hp1
    (by rw [entry_take M 1 hc0x]; omega) (by rw [entry_take M 2 hc0x]; exact h2)
  rwa [hvr] at hlt

/-- `t2SVc0'_of_drop` (V3T2VRASV) on the V3 context: the PO of `DropV3`. -/
theorem t2SVc0'_of_dropV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) :
    T2SVc0' M ρ r L := by
  intro τ hτ Lc0 c0 hT s y hsy hy
  have IW := I
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hD := (Ctx.drop (by omega)).1
  have hx : M.length - 1 = r + L := by omega
  rw [hx] at hD
  have hcnt := counted_take_last (M := M) (by omega) IW.r0p IW.z2 IW.sd IW.z1 IW.uat
  rw [hx] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) IW.rank hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hc0m : c0 ∈ CL (M.take (r + L)) r := by rw [hT]; simp
  have hc0 := List.mem_filter.mp hc0m
  have hc0T : c0 < (M.take (r + L)).length := (mem_children hc0.1).2
  have hc0x : c0 < r + L := by rw [List.length_take] at hc0T; omega
  have hag := agree_of_cons hτ hC1 hRk1 c0 hc0T
  have hPO := (hD c0 hc0x).1.1
  -- `τ` on `M.take x` is good
  have hτ' : Cons (M.take (M.length - 1)) τ := by rw [hx]; exact hτ
  have hG := good3_take_anyV3U IW (Ctx.drop (by omega)) (by omega) hτ'
  rw [hx] at hG
  -- `v(c₀)` does not change
  have hnch : ¬ ChgX M (r + L) false c0 := by
    intro hch
    have hTop := (chg_struct hlen IW.r0p IW.z2 IW.sd IW.z1 IW.uat IW.uab hch).1 rfl hc0x
    have hCLe : CL (M.take (r + L)) c0 = [] := by
      unfold CL; rw [List.filter_eq_nil_iff]
      intro d hd hdc; exact hTop.2.1 d hd (by simpa using hdc)
    have ho := o_spArg hτ hG hc0T
    rw [cvals_eq_map hτ hG, hCLe, hsy] at ho
    simp only [psi.injEq] at ho
    exact hy (by rw [ho.2.1]; rfl)
  have hv := (chg_off hlen IW.cons IW.good hC1 hRk1 c0 hc0x).2 hnch
  -- the subscript of `o_{M.take x}(c₀)` is `v(c₀)`
  have hoT := o_spArg hτ hG hc0T
  rw [hsy] at hoT
  simp only [psi.injEq] at hoT
  have hs : s = ρ.v c0 := by rw [hoT.1, hag.2, hv]
  obtain ⟨Xm, hXm⟩ := o_arg_form IW (show c0 < M.length by omega)
  refine ⟨Xm, by rw [hXm, hs], ?_⟩
  have hle := LhdE.le (show LhdE ((drop1 M (r + L) rk).o c0) (ρ.o c0) from ?_)
  · rw [← hag.1, hsy, hXm, ← hs] at hle
    rcases (le_iff _ _).mp hle with h | h
    · rcases psi_lt_psi_z_iff.mp h with h' | ⟨_, h'⟩
      · exact absurd h' (lt_irrefl' _)
      · exact le_of_lt h'
    · simp only [psi.injEq] at h; rw [h.2.1]
  · rcases hPO with h | ⟨⟨w', w, X, h1, _, _⟩, _⟩
    · exact h
    · rw [← hag.1, hsy] at h1; simp only [psi.injEq] at h1; exact absurd h1.2.1 hy

/-- **The sv residual `T2SVc0`** on the V3 context: no residual. -/
theorem t2SVc0_ofV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) : T2SVc0 M ρ r L :=
  t2SVc0_of I hlen (t2SVc0'_of_dropV3 I Ctx hlen hr)
