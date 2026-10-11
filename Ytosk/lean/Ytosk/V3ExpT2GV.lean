/-
**3 行・t = 2: 写しの境界の事実 T2GuardVal（守られた列が読む守られない値の v は V = v(r) 以下）。**

行列 G（t = 2 では P = M[n − 1]）の値について:
- `v_form`: 行 1 が 0 でない列 c の v は v(P_1 c) + X（X は単項で標準形）。行 2 が 0 なら X は上げの項。
- `v_le_same_par1`: d と w が同じ P_1 = m を持ち、w が d の祖先で e1(d) ≤ e1(w)、e2(d) = 0 なら v(d) ≤ v(w)。
  d の上げの先 k は m の子で d の祖先。k = w なら X_d = last(v(w)) = X_w。k が w より上なら、w は行 2 が 0
  （行 2 が 1 なら RowJ で親ののりしろの子、BumpE2 で親も行 2 が 1、k まで登ると UAB に反する）で、w も k へ上げる。
- `v_le_unguarded`: r の子孫 d が守られず（r と d の間はガードの窓の中）、なら v(d) ≤ v(r)。
  P_1(d) は r の真の祖先で、r の P_1 の鎖をたどると P_1 が P_1(d) になる列 w に着く。
-/
import Ytosk.V3ExpT2X

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

theorem omega_psi_form (x : T) : ∃ s y, omega x = psi s y z := by
  unfold omega
  split
  · exact ⟨_, _, rfl⟩
  · split
    · exact ⟨z, z, rfl⟩
    · exact ⟨_, _, rfl⟩

section
variable {G : Mat} {ρ : Valn} (hC : Cons G ρ) (hG : Good3 G ρ)
include hC hG

/-- **The shape of `v`**: `v(c) = v(P_1 c) + X` with `X` a standard single summand; for row 2 equal to `0`
the increment is that of the upgrade. -/
theorem v_form {c m : Nat} (hc : c < G.length) (h1 : entry G 1 c ≠ 0) (hm : par G 1 c = some m) :
    ∃ X, (∃ s y, X = psi s y z) ∧ isOT X = true ∧ ρ.v c = add (ρ.v m) X ∧
      (entry G 2 c = 0 → X = (match upg G c with | some k => last (ρ.v k) | none => one)) := by
  have hml := par_lt G 1 c m hm
  have hmot := hG.ot_v m (by omega)
  have hv := (hC c hc).2
  unfold vRhs at hv
  rw [if_neg h1, hm] at hv
  by_cases h2 : entry G 2 c = 0
  · rw [if_pos h2] at hv
    have hX : (∃ s y, (match upg G c with | some k => last (ρ.v k) | none => one) = psi s y z) ∧
        isOT (match upg G c with | some k => last (ρ.v k) | none => one) = true := by
      cases hu : upg G c with
      | none => exact ⟨⟨z, z, rfl⟩, rfl⟩
      | some k =>
        simp only
        have hkl := upg_lt hc hu
        obtain ⟨_, _, _, he, _⟩ := upg_facts hu
        have hkz : ρ.v k ≠ z := v_ne_z_of_e1 hC hkl (by rw [he]; exact h1)
        exact ⟨last_psi_form hkz, isOT_last (hG.ot_v k hkl)⟩
    refine ⟨_, hX.1, hX.2, ?_, fun _ => rfl⟩
    rw [hv]; exact sf_ot (isOT_add hmot hX.2)
  · rw [if_neg h2] at hv
    have hXot : isOT (omega (sumN (one :: (children G c).map (bumpTerm G ρ c)))) = true := by
      apply isOT_omega; apply isOT_sumN
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG c j
    refine ⟨_, omega_psi_form _, hXot, ?_, fun h => absurd h h2⟩
    rw [hv]; exact sf_ot (isOT_add hmot hXot)

/-- `v` does not decrease along `P_1`. -/
theorem v_par1_le {c m : Nat} (hc : c < G.length) (h1 : entry G 1 c ≠ 0) (hm : par G 1 c = some m) :
    ρ.v m ≤ ρ.v c := by
  obtain ⟨X, hXs, _, hv, _⟩ := v_form hC hG hc h1 hm
  rw [hv]; exact le_add_of_single _ hXs

/-- **Same row-1 parent**: `v(d) ≤ v(w)` when `w` is an ancestor of `d` with `e1(d) ≤ e1(w)`,
`e2(d) = 0`, and `d + 1` is not a child of the common row-1 parent `m`. -/
theorem v_le_same_par1 (hR0 : R0P G) (hJ : RowJ G) (hBE : BumpE2 G) (hUAB : UAB G) (hZ2 : Z2 G)
    {m w d : Nat} (hw : par G 1 w = some m) (hd : par G 1 d = some m) (hwd : Anc0 G w d)
    (hwdne : w ≠ d) (he1 : entry G 1 d ≤ entry G 1 w) (he2d : entry G 2 d = 0) (hdl : d < G.length)
    (hnext : d + 1 < G.length → par G 0 (d + 1) ≠ some m) : ρ.v d ≤ ρ.v w := by
  obtain ⟨_, hmdlt, he1md, _⟩ := par1_facts hd
  obtain ⟨hmw, hmwlt, he1mw, hbetw⟩ := par1_facts hw
  have hwl : w < G.length := by have := hwd.le; omega
  have h1d : entry G 1 d ≠ 0 := by omega
  have h1w : entry G 1 w ≠ 0 := by omega
  obtain ⟨Xw, hXws, hXwot, hvw, hXw0⟩ := v_form hC hG hwl h1w hw
  have hmot := hG.ot_v m (by omega)
  have hvd := (hC d hdl).2
  unfold vRhs at hvd
  rw [if_neg h1d, if_pos he2d, hd] at hvd
  cases hu : upg G d with
  | none =>
    rw [hu] at hvd
    change ρ.v d = sf (add (ρ.v m) one) at hvd
    rw [hvd, sf_ot (isOT_add hmot rfl), hvw]
    obtain ⟨s, y, rfl⟩ := hXws
    exact add_le_add_left _ (one_le_of_ne_z (by simp))
  | some k =>
    rw [hu] at hvd
    change ρ.v d = sf (add (ρ.v m) (last (ρ.v k))) at hvd
    obtain ⟨m', hm1, hm2, hcol, hcase⟩ := upg_spec hu
    rw [hd] at hm1; cases hm1
    have hkl := upg_lt hdl hu
    have hkm' : par G 0 k = some m := by
      obtain ⟨m'', hm'', hkm'', _, _⟩ := upg_facts hu
      rw [hd] at hm''; cases hm''; exact hkm''
    rcases hcase with hk1 | ⟨hkd, hklt⟩
    · exfalso
      rw [hk1] at hkm' hkl
      exact hnext hkl hkm'
    · have hkw : Anc0 G k w := by
        rcases anc0_total hkd hwd with h | h
        · exact h
        · by_cases hwk : w = k
          · rw [hwk]; exact Anc0.refl k
          · exfalso
            have := (anc0_par h hwk hkm').le; omega
      by_cases hkw' : k = w
      · have e : ρ.v d = ρ.v w := by
          rw [hvd, hkw', hvw]
          obtain ⟨s, y, rfl⟩ := hXws
          rw [last_add_single, sf_ot (isOT_add hmot hXwot)]
        rw [e]
      · -- `k` strictly above `w`
        have hmk : Anc0 G m k := Anc0.step hkm' (Anc0.refl m)
        have hmklt := par_lt G 0 k m hkm'
        have he1k : entry G 1 k = entry G 1 d := e1_of_col hcol
        have he1w : entry G 1 w = entry G 1 d := by
          have := hbetw k hmk hkw (by omega) hkw'; omega
        -- `w` has row 2 equal to `0`
        have hchain : ∀ c, Anc0 G k c → c ≠ k → Anc0 G c w → entry G 2 c ≠ 0 →
            entry G 1 c = entry G 1 w → False := by
          intro c
          induction c using Nat.strong_induction_on with
          | _ c ih =>
            intro hkc hck hcw h2c h1c
            obtain ⟨p, hp, hkp⟩ := anc0_par_exists hkc (Ne.symm hck)
            have hpc := par_lt G 0 c p hp
            have hJc := hJ c p h2c hp
            have hpw : Anc0 G p w := Anc0.trans (Anc0.step hp (Anc0.refl p)) hcw
            have hmp : Anc0 G m p := Anc0.trans hmk hkp
            have hpl : p ≠ m := by have := hkp.le; omega
            have hpwne : p ≠ w := by have := hcw.le; omega
            have := hbetw p hmp hpw hpl hpwne
            have h1p : entry G 1 p = entry G 1 c := by omega
            have h0c := hR0 c p hp
            have h2c1 : entry G 2 c = 1 := by have := hZ2 c; omega
            have hcb : col G c = bump G p := by
              rw [col_eq_entries, h0c, h2c1, ← h1p]; rfl
            have hcch : c ∈ children G p := mem_children_iff.mpr ⟨by have := hcw.le; omega, hp⟩
            have h2p := hBE p c hcch hcb
            by_cases hpk : p = k
            · subst hpk
              exact hUAB d p hu (by omega) c hcch hcb (Anc0.trans hcw hwd)
            · exact ih p hpc hkp hpk hpw (by omega) (by omega)
        have h2w : entry G 2 w = 0 := by
          by_contra h2w
          exact hchain w hkw (Ne.symm hkw') (Anc0.refl w) h2w rfl
        -- `w` upgrades to `k`
        have hw1 : par G 0 (w + 1) = some w := by
          have hww1 : Anc0 G w (w + 1) := anc_between hwd (w + 1) (by omega)
            (by have := hwd.le; omega)
          obtain ⟨p, hp, hwp⟩ := anc0_par_exists hww1 (by omega)
          have := par_lt G 0 _ _ hp
          have := hwp.le
          rw [hp, show p = w by omega]
        have he0w1 := hR0 (w + 1) w hw1
        have he0k := hR0 k m hkm'
        have he0kw := anc0_e0_lt hkw hkw'
        have hupw : upg G w = some k := by
          have hc3 : ¬ (entry G 1 w = 0 ∨ entry G 2 w = 1 ∨ w + 1 = G.length) := by
            rintro (h | h | h)
            · exact h1w h
            · omega
            · have := hwd.le; omega
          unfold upg
          rw [if_neg hc3, hw]
          simp only
          rw [if_neg (by
            rintro ⟨_, hc'⟩
            have : entry G 0 (w + 1) = (col G (w + 1)).1 := rfl
            rw [hc'] at this; simp at this; omega)]
          rw [upgClimb_find, find?_dec (ancL_pairwise G w)]
          refine ⟨mem_ancL_of_anc hkw hkw', ?_, fun y hy hky => ?_⟩
          · simp only [decide_eq_true_eq]
            refine ⟨hm2, ?_, by omega⟩
            rw [hcol, he1w]
          · simp only [decide_eq_false_iff_not]
            rintro ⟨_, hcy, _⟩
            have hyw : Anc0 G y w := anc0_of_mem_ancL hy
            have hky' : Anc0 G k y := by
              rcases anc0_total hkw hyw with h | h
              · exact h
              · have := h.le; omega
            have := anc0_e0_lt hky' (by omega)
            have : entry G 0 y = (col G y).1 := rfl
            rw [hcy] at this; simp at this; omega
        have hXw : Xw = last (ρ.v k) := by rw [hXw0 h2w, hupw]
        have e : ρ.v d = ρ.v w := by
          rw [hvd, hvw, ← hXw, sf_ot (isOT_add hmot hXwot)]
        rw [e]

/-- **An unguarded descendant of `r` has `v` at most `v(r)`**: `d` below `r`, every column strictly between
`r` and `d` inside the guard window, `d` itself not guarded, and every column after `r` below `r`. -/
theorem v_le_unguarded (hR0 : R0P G) (hJ : RowJ G) (hBE : BumpE2 G) (hUAB : UAB G) (hZ2 : Z2 G)
    (hR01 : R01 G) (h00 : entry G 0 0 = 0) {r : Nat} (he2r : entry G 2 r = 0)
    (hsub : ∀ c, r ≤ c → c < G.length → Anc0 G r c) {d : Nat} (hrd : Anc0 G r d) (hdr : d ≠ r)
    (hdl : d < G.length)
    (hwin : ∀ y, Anc0 G r y → Anc0 G y d → y ≠ r → y ≠ d → entry G 1 r < entry G 1 y)
    (hng : ¬ TRIO.le1 G r d) : ρ.v d ≤ ρ.v r := by
  have hrdlt : r < d := by have := hrd.le; omega
  by_cases h1d : entry G 1 d = 0
  · rw [v_z_of_e1 hC hdl h1d]; exact z_le _
  obtain ⟨m, hm⟩ := par1_exists h00 hR01 (show 0 < entry G 1 d by omega)
  obtain ⟨hmd, hmdlt, he1md, hbetd⟩ := par1_facts hm
  have hrl : r < G.length := by omega
  have hle1rr : TRIO.le1 G r r := ⟨hrl, hrl, Relation.ReflTransGen.refl⟩
  -- `P_1(d)` is a proper ancestor of `r`
  have hmr : Anc0 G m r ∧ m ≠ r := by
    rcases anc0_total hmd hrd with h | h
    · refine ⟨h, fun hmr => hng ?_⟩
      rw [hmr] at hm
      exact le1_par1_up hle1rr hm hdl
    · exfalso
      by_cases hmr : m = r
      · rw [hmr] at hm; exact hng (le1_par1_up hle1rr hm hdl)
      · have hml : m < G.length := by omega
        have hgm : TRIO.le1 G r m := by
          apply (le1_window hml h).mpr
          intro y hy1 hy2 hy3
          by_cases hym : y = m
          · rw [hym]; exact hwin m h hmd hmr (by omega)
          · exact hwin y hy1 (Anc0.trans hy2 hmd) hy3 (by have := hy2.le; omega)
        exact hng (le1_par1_up hgm hm hdl)
  obtain ⟨hmr1, hmr2⟩ := hmr
  have hmrlt : m < r := by have := hmr1.le; omega
  -- `e2(d) = 0`
  have he2d : entry G 2 d = 0 := by
    by_contra h2d
    obtain ⟨p, hp, hrp⟩ := anc0_par_exists hrd (Ne.symm hdr)
    have hJd := hJ d p h2d hp
    have hpd := par_lt G 0 d p hp
    by_cases hpr : p = r
    · rw [hpr] at hp hJd
      have he1dr : entry G 1 d ≤ entry G 1 r := hbetd r hmr1 hrd (Ne.symm hmr2) (by omega)
      have h0d := hR0 d r hp
      have h2d1 : entry G 2 d = 1 := by have := hZ2 d; omega
      have hdb : col G d = bump G r := by
        rw [col_eq_entries, h0d, h2d1, show entry G 1 d = entry G 1 r by omega]; rfl
      have := hBE r d (mem_children_iff.mpr ⟨hdl, hp⟩) hdb
      omega
    · have h1 := hwin p hrp (Anc0.step hp (Anc0.refl p)) hpr (by omega)
      have he1dr : entry G 1 d ≤ entry G 1 r := hbetd r hmr1 hrd (Ne.symm hmr2) (by omega)
      omega
  -- `d + 1` is not a child of `m`
  have hnext : d + 1 < G.length → par G 0 (d + 1) ≠ some m := by
    intro hd1 h
    have := (anc0_par (hsub (d + 1) (by omega) hd1) (by omega) h).le
    omega
  -- along the row-1 chain of `r` down to `m`
  have key : ∀ c, Anc0 G m c → c ≠ m → Anc0 G c r → ρ.v d ≤ ρ.v c := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      intro hmc hcm hcr
      have hcd : Anc0 G c d := Anc0.trans hcr hrd
      have hcdlt : c < d := by have := hcr.le; omega
      have he1c : entry G 1 d ≤ entry G 1 c := hbetd c hmc hcd hcm (by omega)
      have hcl : c < G.length := by omega
      obtain ⟨c', hc'⟩ := par1_exists h00 hR01 (show 0 < entry G 1 c by omega)
      obtain ⟨hc'c, hc'lt, he1c', hbetc⟩ := par1_facts hc'
      have hmc' : Anc0 G m c' := by
        rcases anc0_total hmc hc'c with h | h
        · exact h
        · by_cases hc'm : c' = m
          · rw [hc'm]; exact Anc0.refl m
          · exfalso
            have := hbetc m h hmc (Ne.symm hc'm) (Ne.symm hcm)
            omega
      by_cases hc'm : c' = m
      · rw [hc'm] at hc'
        exact v_le_same_par1 hC hG hR0 hJ hBE hUAB hZ2 hc' hm hcd (by omega) he1c he2d hdl hnext
      · have h1 := ih c' hc'lt hmc' hc'm (Anc0.trans hc'c hcr)
        exact le_trans h1 (v_par1_le hC hG hcl (by omega) hc')
  exact key r hmr1 (Ne.symm hmr2) (Anc0.refl r)

end

end Ytosk
