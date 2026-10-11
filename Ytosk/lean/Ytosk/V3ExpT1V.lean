/-
**3 行・t = 1: VSFRes2（VSmallF の D の v の子の枠）を残りなしで。**

枠 (i, c)、c は i の数える子で v(c) が x に依る（D の v の列）、c < x。N = M[n] での成分
g ∈ comps_{v(i)}(v_N(c)) について g ≤ Ω_{v_N(c)} か g ≤ B（B = c より前の数える子の和の状態）。

- v_N(c) < v(i) なら成分はない（comps_nil_of_le）。
- c より前に数える子がない（B = 0）とき: c は i の最後の数える子（OShape）で、c は数える子を持たない
  （v(c) が D）ので o_N(c) = Ω_{v_N(c)}、o_N(i) = ψ_{v(i)}(Ω_{v_N(c)})。これが標準形なので g < Ω_{v_N(c)}。
- 前に数える子があるとき: 穴の ◁（lhd_fs・fsD_seed）から g は古い成分か 0 か添字 ζ = Z c の成分以下。
  古い成分は M の VSmallF で Ω_{v(c)} 以下か B 以下で、数える子の値は左から減る（Good3）ので
  Ω_{v(c)} ≤ B。添字の成分が効くのは共終数が通過する場合（cof W = Ω_{μ+1}）だけで、そのとき μ < v(i)
  （i の o の穴から）なので comps_{v(i)}(ζ) = []。
-/
import Ytosk.V3ExpT1Y

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem comps_last_sub1 (u t : T) : ∀ g ∈ comps u (last t), g ∈ comps u t := by
  intro g hg
  rw [← init_app_last t, comps_app]
  exact List.mem_append_right _ hg

/-- **The new components through the hole**: each is at most an old component, `0`, or (only when the
cofinality passes) a component of the index. -/
theorem hole_dom {μ br vr seed W : T} (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ)
    (hμ : ¬ lt μ vr = true)
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed)
    (hot : isOT W = true) (hH : HoleT μ br vr W) (m : Nat) (u : T) :
    ∀ g ∈ comps u (fsD W (gamS μ br seed m)), ∃ y, (y ∈ comps u W ∨ y = z ∨
      (cof W = .big μ ∧ y ∈ comps u (gamS μ br seed m))) ∧ g ≤ y := by
  have hSr := hS vr (lt_irrefl' vr) hrot
  rcases hH with hc | ⟨a', ha', hD⟩
  · rw [fsD_eq_fs hc]
    have hV : ValidLt W (gamS μ br seed m) := by
      unfold ValidLt; rw [hc]; exact gamS_lt_om hrot hcb hμ hSr m
    have hl := lhd_fs hot hV
    intro g hg
    obtain ⟨y, hy, hgy⟩ := hl.2 u W hl.1 (le_refl _) g hg
    refine ⟨y, ?_, hgy⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact Or.inl hy
    · simp only [Gc, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨hc, hy⟩)
  · have hnode := DiagAt.ot_node hD hot
    obtain ⟨_, hl⟩ := fsD_seed (hS a' ha' hnode) hD hot m
    intro g hg
    obtain ⟨y, hy, hgy⟩ := hl.2 u W hl.1 (le_refl _) g hg
    refine ⟨y, ?_, hgy⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact Or.inl hy
    · simp [Gc, comps] at hy; exact Or.inr (Or.inl hy)

/-- **The chain terms have no components above their level.** -/
theorem comps_gamS_nil {μ br seed u : T} (hseed : ∃ a X, seed = psi a X z)
    (hlt : seed < psi (succ μ) z z) (hμu : lt μ u = true) : ∀ m, comps u (gamS μ br seed m) = []
  | 0 => by
    obtain ⟨a, X, rfl⟩ := hseed
    have ha : a ≤ μ := by
      rcases psi_lt_psi.mp hlt with h | ⟨_, h⟩ | ⟨_, _, h⟩
      · exact lt_succ_iff.mp h
      · exact absurd h (T.not_lt_z _)
      · exact absurd h (T.not_lt_z _)
    have hau : lt a u = true := lt_of_le_of_lt ha hμu
    simp [gamS, comps, hau]
  | m + 1 => by simp [gamS, comps, hμu]



/-- **The hole of `ψ_a(F)` with a passing `F`**: either the cofinality passes `a` (`μ < a`) or `ψ_a(F)` is the
diagonal point itself (`F = b_r`, `a ≤ v(r)`). -/
theorem holeT_psi_pass {μ br vr a F : T} (hF : F ≠ z) (hc : cof F = .big μ)
    (hH : HoleT μ br vr (psi a F z)) : lt μ a = true ∨ (F = br ∧ ¬ lt vr a = true) := by
  by_cases hlt : lt μ a = true
  · exact Or.inl hlt
  right
  rcases hH with h | ⟨a', ha', hD⟩
  · exfalso
    unfold cof at h
    rw [if_neg hF, if_neg (by rw [not_succ_of_cof_big hc]; simp), hc] at h
    simp [hlt] at h
  · cases hD with
    | here _ _ _ => exact ⟨rfl, ha'⟩
    | arg _ _ hD' => exact absurd (hD'.cof_omega.symm.trans hc) (by simp)
    | sub hz _ _ => exact absurd rfl hF

/-- **The cofinality of a state ending with a leaf `Ω_v`** is that of `v`. -/
theorem cof_state_leaf {a S v : T} (hv : v ≠ z) (hvs : isSucc v = false) :
    cof (spArg a z (add S (psi v z z))) = cof v := by
  obtain ⟨P, hP, _⟩ := add_eq_app_prefix S (psi v z z)
  rw [hP, spArg_app, spArg_cons]
  unfold step
  rw [if_neg (fun h => T.not_lt_z _ h.1)]
  obtain ⟨P', hP', _⟩ := add_eq_app_prefix (spArg a z P) (psi v z z)
  show cof (spArg a (add (spArg a z P) (psi v z z)) z) = cof v
  rw [hP']
  show cof (app P' (psi v z z)) = cof v
  rw [cof_app P' (by simp)]
  conv => lhs; unfold cof
  rw [if_pos rfl, if_neg hv, if_neg (by simp [hvs])]

/-- The state before `c` is at least `Ω_{v(c)}` once there is an earlier counted child (the counted
values decrease, `Good3`). -/
theorem om_le_state {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {i : Nat} (hi : i < M.length)
    {Lc : List Nat} {c : Nat} (hCL : CL M i = Lc ++ [c]) (hoc : ρ.o c = psi (ρ.v c) z z) (hLc : Lc ≠ []) :
    psi (ρ.v c) z z ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) := by
  obtain ⟨hs, hp⟩ := cl_vals hC hG hi
  rw [hCL, List.map_append, List.map_singleton] at hs hp
  have hsL : ∀ t ∈ Lc.map ρ.o, Single t := fun t ht => hs t (List.mem_append_left _ ht)
  have hpL : (Lc.map ρ.o).Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp).1
  have hge : ∀ t ∈ Lc.map ρ.o, psi (ρ.v c) z z ≤ t := by
    intro t ht
    have := (List.pairwise_append.mp hp).2.2 t ht (ρ.o c) (by simp)
    rwa [hoc] at this
  have hSot : isOT (sumN (Lc.map ρ.o)) = true := isOT_sumN _ (fun t ht => (hsL t ht).1)
  have hS0 : sumN (Lc.map ρ.o) ≠ z := sumN_ne_z_of_single hsL hpL (by simpa using hLc)
  have hall := spArg_summands_ge (a := ρ.v i) (c := psi (ρ.v c) z z) ⟨_, _, rfl⟩ (sumN (Lc.map ρ.o)) z hSot
    (fun q hq => hge q (summands_sumN_sub hsL q hq)) (fun q hq => by simp [summands] at hq)
  have hB0 := spArg_ne_z (ρ.v i) (sumN (Lc.map ρ.o)) z (Or.inr hS0)
  revert hall hB0
  generalize spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = B
  intro hall hB0
  cases B with
  | z => exact absurd rfl hB0
  | psi a b d =>
    exact le_trans (hall _ (by simp [summands])) (le_psi_rest (z_le d))

/-- **Residual: a `D` child of `r` whose cofinality passes is the first counted child of `r`** (`t = 1`).
実測（t = 1 の行列: C′ 195711・T0Ext 由来 112277・d3s 9103・deep2・deep3）で、r の数える子 c が D の v の列で
cof(last v(c)) = Ω_{v(r)+1} 型なら、c の前に数える子はない（例外 0）。前に数える子を置いた形は bms で非標準。 -/
def PassRootRes (M : Mat) (r L : Nat) (ρ : Valn) : Prop :=
  ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M r = Lc ++ c :: R → DepX M (r + L) false c → c < r + L →
    cof (last (ρ.v c)) = .big (ρ.v r) → Lc = []

/-- **The passing cofinality is above the chain level at the parent** (with an earlier counted child). -/
theorem mu_lt_vi {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hPR : PassRootRes M r L ρ)
    {μ br vr seed : T} (hHD : HoleData M (r + L) ρ μ br vr seed) (hμv : μ = vr) (hro : ρ.o r = psi vr br z)
    {i : Nat} {Lc : List Nat} {c : Nat} {R : List Nat} (hi : i < r + L) (hCL : CL M i = Lc ++ c :: R)
    (hcd : DepX M (r + L) false c) (hcx : c < r + L)
    (hcof : cof (last (ρ.v c)) = .big μ) (hLc : Lc ≠ []) : lt μ (ρ.v i) = true := by
  have hrx : r < r + L := par_lt M 1 _ r h1
  have hrM : r < M.length := by omega
  have hvr : vr = ρ.v r := chain_level I.cons I.good hrM hro
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcch : c ∈ children M i := (List.mem_filter.mp hcCL).1
  have hccnt : Counted M i c := by simpa using (List.mem_filter.mp hcCL).2
  have h0 : par M 0 c = some i := (mem_children_iff.mp hcch).2
  have hcofv : cof (ρ.v c) = .big μ := by rw [← cof_last_g]; exact hcof
  have hrc : r < c := by
    by_contra hcr
    have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
    have hF1 : ∀ j, r < j → j < r + L → DepX M (r + L) true j → ¬ DepX M (r + L) false j →
        lt μ (ρ.v j) = true := by
      intro j h2 h3 h4 h5
      rw [hμv, hvr]
      exact hF1_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 I.cons I.good I.rank j h2 h3 h4 h5
    have hox : ρ.o (r + L) = psi (succ μ) z z := by
      rw [o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2, ← hvr, ← hμv]
    have hbr : br ≠ z := by
      intro h; have := hHD.cb; rw [h] at this; simp [cof] at this
    have hH := t1_hole0 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq I.cons I.good I.kd I.td I.ad hrx hA hro
      hHD.cb hμv hbr (Or.inl (by rw [hox]; exact cof_omega_succ μ)) hF1 hOS (hS2_t1 I.r0p hA (by omega))
      (hS3_t1 h1 hA (by omega) hlen I.r0p I.z2 I.sd I.z1) false c hcd (Or.inl hcx)
    obtain ⟨a', _, hD⟩ := hH.2.1 (by omega)
    simp only [valB, cond_false] at hD
    rw [hD.cof_omega] at hcofv
    cases hcofv
  have hri : r ≤ i := par0_ge_of_anc hA hrc (by omega) h0
  rcases Nat.eq_or_lt_of_le hri with h | h
  · subst h
    exact absurd (hPR Lc c R hCL hcd hcx (by rw [hcof, hμv, hvr])) hLc
  · have hdi : DepX M (r + L) true i := DepX.ochild hcch hccnt.1 hccnt.2 (DepX.ov hcd)
    have hvd : ¬ DepX M (r + L) false i := fun hv =>
      uncnt_of_depv hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq hi hv hcch hccnt
    rw [hμv, hvr]
    exact hF1_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 I.cons I.good I.rank i h hi hdi hvd

/-- **VSFRes2 at one frame** (`t = 1`): the frame `(i, c)` with `c` a `v` call of `D`. Residual `PassRootRes`. -/
theorem vsf_frame {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    {n : Nat} (hn : 2 ≤ n) {ρP : Valn} {Z : Nat → T} (hH : HoleInfo M r L n ρ ρP Z)
    (hCN : Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z))
    (hGN : Good3 (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z))
    {i : Nat} (hi : i < r + L) {Lc : List Nat} {c : Nat} {R : List Nat} (hCL : CL M i = Lc ++ c :: R)
    (hcd : DepX M (r + L) false c) (hcx : c < r + L)
    (hPR : PassRootRes M r L ρ) :
    ∀ g ∈ comps (ρ.v i) ((glueZ M (r + L) ρ (shiftV ρP L) Z).v c),
      g ≤ psi ((glueZ M (r + L) ρ (shiftV ρP L) Z).v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q0, hq0⟩ := par0_of_anc hA (by omega)
  have hpath := hpath_of_par1 h1 hA (by omega)
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
    (hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn)
    (hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn)
  have hiM : i < M.length := by omega
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcch : c ∈ children M i := (List.mem_filter.mp hcCL).1
  have hccnt : Counted M i c := by simpa using (List.mem_filter.mp hcCL).2
  have hcM := (mem_children hcch).2
  have h0 : par M 0 c = some i := (mem_children_iff.mp hcch).2
  have hCLeq : ∀ j, j < r + L → CL (TRIO.gexp M r L d0 0 n) j = CL M j := by
    intro j hj
    have hS := hSA j hj
    unfold CL; rw [hS.ch]
    apply List.filter_congr
    intro d hd
    exact decide_eq_decide.mpr (counted_iff_of_cnt (hS.cnt d hd))
  have hvd : ¬ DepX M (r + L) false i := fun hv =>
    uncnt_of_depv hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq0 hi hv hcch hccnt
  have hvi : σ.v i = ρ.v i := by rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z hi hvd]
  have hcN : c < (TRIO.gexp M r L d0 0 n).length := by rw [hlN]; omega
  have hvcot : isOT (σ.v c) = true := hGN.ot_v c hcN
  intro g hg
  by_cases hlt : σ.v c < ρ.v i
  · rw [comps_nil_of_le hvcot (le_of_lt hlt)] at hg; simp at hg
  have hge : ¬ lt (σ.v c) (ρ.v i) = true := hlt
  have hR : R = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro d hd
    have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
    have hdch : d ∈ children M i := (List.mem_filter.mp hdCL).1
    have hdcnt : Counted M i d := by simpa using (List.mem_filter.mp hdCL).2
    have hcd' : c < d := by
      have hs : (CL M i).Pairwise (· < ·) := (children_sorted M i).filter _
      rw [hCL] at hs
      exact List.rel_of_pairwise_cons (List.pairwise_append.mp hs).2.1 hd
    exact p1_dep hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq0 hi hcch hdch hcd' (DepX.ov hcd) hdcnt
  subst hR
  have hCLcM : CL M c = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro d hd
    exact uncnt_of_depv hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq0 hcx hcd (List.mem_filter.mp hd).1
      (by simpa using (List.mem_filter.mp hd).2)
  have hoc : σ.o c = psi (σ.v c) z z := by
    rw [o_cl_eq hCN hGN hcN, hCLeq c hcx, hCLcM]; rfl
  by_cases hLc : Lc = []
  · subst hLc
    left
    have hCLN : CL (TRIO.gexp M r L d0 0 n) i = [c] := by rw [hCLeq i hi, hCL]; rfl
    have hoi := o_cl_eq hCN hGN (show i < (TRIO.gexp M r L d0 0 n).length by rw [hlN]; omega)
    rw [hCLN, List.map_singleton, hoc] at hoi
    have hsum : sumN [psi (σ.v c) z z] = psi (σ.v c) z z := by
      show sf (add z (psi (σ.v c) z z)) = _
      exact sf_ot (by simp [isOT, hvcot, comps])
    have hsp : spArg (σ.v i) z (psi (σ.v c) z z) = psi (σ.v c) z z := by
      rw [spArg_cons]
      unfold step
      rw [if_neg (fun h => T.not_lt_z _ h.1)]
      rfl
    rw [hsum, hsp] at hoi
    have hot := hGN.ot_o i (by rw [hlN]; omega)
    rw [hoi] at hot
    have hall : ∀ g ∈ comps (σ.v i) (psi (σ.v c) z z), lt g (psi (σ.v c) z z) = true := by
      simp only [isOT, Bool.and_eq_true, List.all_eq_true] at hot
      exact hot.2
    rw [hvi] at hall
    exact le_of_lt (hall g (by simp [comps, hge, hg]))
  · right
    obtain ⟨μ, br, vr, seed, k0, hHD, hZk, _, _, hμv, hro⟩ := hH
    obtain ⟨k, _, hZe⟩ := hZk c
    have hvc0 : ρ.v c ≠ z := by
      intro h0'
      rw [hσ, glueZ_v_dep ρ (shiftV ρP L) Z hcx hcd, h0'] at hg
      simp [fsD, comps] at hg
    rw [hσ, glueZ_v_dep ρ (shiftV ρP L) Z hcx hcd, fsD_init_last hvc0, comps_app,
      comps_init_v_nil I.cons I.good I.rank hcM h0, List.nil_append, hZe] at hg
    have hHv := hHD.hole false c hcd hcx
    simp only [valB, cond_false] at hHv
    have hWot : isOT (last (ρ.v c)) = true := isOT_last (I.good.ot_v c hcM)
    obtain ⟨y, hy, hgy⟩ := hole_dom hHD.rot hHD.cb hHD.hμ hHD.S hWot (holeT_last hHv) k (ρ.v i) g hg
    have hocM : ρ.o c = psi (ρ.v c) z z := by
      rw [o_cl_eq I.cons I.good hcM, hCLcM]; rfl
    have hOmB := om_le_state I.cons I.good hiM hCL hocM hLc
    rcases hy with hy | rfl | ⟨hcof, hy⟩
    · rcases I.vs i hiM Lc c [] hCL y (comps_last_sub1 _ _ y hy) with h | h
      · exact le_trans hgy (le_trans h hOmB)
      · exact le_trans hgy h
    · exact le_trans hgy (z_le _)
    · have hSr := hHD.S vr (lt_irrefl' vr) hHD.rot
      rw [comps_gamS_nil hHD.seedS hSr.lt_om (mu_lt_vi I hlen h1 hx2 hPR hHD hμv hro hi hCL hcd hcx hcof hLc) k] at hy
      simp at hy



/-- **VSmallF is carried** (`t = 1`) with the frames of the `v` calls of `D` done by `vsf_frame`; residual
`PassRootRes` only. -/
theorem expStep_vsmallF2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hPR : PassRootRes M r L ρ) :
    ExpStepT1 (fun N σ => VrLe r ρ N σ ∧ VSmallF N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q0, hq0⟩ := par0_of_anc hA (by omega)
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq0
  intro n hn ρP Z hCP hGP hQP0 hCN hGN hoto hotv hle hlex hH
  refine ⟨expStep_vrle I hlen h1 hx2 n hn ρP Z hCP hGP hQP0.1 hCN hGN hoto hotv hle hlex hH, ?_⟩
  have hQP := hQP0.2
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
    (hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn)
    (hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn)
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
  intro i hi Lc c R hCL
  rcases Nat.lt_or_ge i (r + L) with h | h
  · have hS := hSA i h
    have hCLe : CL (TRIO.gexp M r L d0 0 n) i = CL M i := by
      unfold CL; rw [hS.ch]
      apply List.filter_congr
      intro c hc
      exact decide_eq_decide.mpr (counted_iff_of_cnt (hS.cnt c hc))
    rw [hCLe] at hCL
    have hcCL : c ∈ CL M i := by rw [hCL]; simp
    have hcch : c ∈ children M i := (List.mem_filter.mp hcCL).1
    have hccnt : Counted M i c := by simpa using (List.mem_filter.mp hcCL).2
    have hvd : ¬ DepX M (r + L) false i := by
      intro hv
      rcases hOS i h (DepX.ov hv) with ⟨_, hnc⟩ | ⟨hnv, _⟩
      · rcases hnc c hcch with h' | h'
        · exact hccnt.1 h'
        · exact hccnt.2 h'
      · exact hnv hv
    have hLd : ∀ d ∈ Lc, ¬ DepX M (r + L) true d := by
      intro d hd hdD
      have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
      have hdch : d ∈ children M i := (List.mem_filter.mp hdCL).1
      have hdcnt : Counted M i d := by simpa using (List.mem_filter.mp hdCL).2
      have hdc : d < c := by
        have hs : (CL M i).Pairwise (· < ·) := (children_sorted M i).filter _
        rw [hCL] at hs
        exact (List.pairwise_append.mp hs).2.2 d hd c List.mem_cons_self
      have hiD : DepX M (r + L) true i := DepX.ochild hdch hdcnt.1 hdcnt.2 hdD
      rcases hOS i h hiD with ⟨hv, _⟩ | ⟨_, L', c', R', hch, _, _, hR', hL'⟩
      · exact hvd hv
      · have hdc' : d = c' := by
          rw [hch] at hdch
          rcases List.mem_append.mp hdch with h' | h'
          · exact absurd hdD (hL' d h' hdcnt)
          · rcases List.mem_cons.mp h' with h' | h'
            · exact h'
            · rcases hR' d h' with h'' | h''
              · exact absurd h'' hdcnt.1
              · exact absurd h'' hdcnt.2
        subst hdc'
        have hsort := children_sorted M i
        rw [hch] at hsort hcch
        rcases List.mem_append.mp hcch with h' | h'
        · have := (List.pairwise_append.mp hsort).2.2 c h' d List.mem_cons_self
          omega
        · rcases List.mem_cons.mp h' with h' | h'
          · omega
          · rcases hR' c h' with h'' | h''
            · exact hccnt.1 h''
            · exact hccnt.2 h''
    have hLo : Lc.map σ.o = Lc.map ρ.o := by
      apply List.map_congr_left
      intro d hd
      have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
      have hdM := (mem_children (List.mem_filter.mp hdCL).1).2
      have hdx : d < r + L := by
        rcases Nat.lt_or_ge d (r + L) with h' | h'
        · exact h'
        · exfalso
          have : d = r + L := by omega
          exact hLd d hd (this ▸ DepX.leaf)
      rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hdx (hLd d hd)]
    rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z h hvd, ← hσ, hLo]
    have hcM := (mem_children hcch).2
    by_cases hcxe : c = r + L
    · -- the frame of `x`: `v_N(x) = v_P(r) ≤ v(r) ≤ v(q)`, no components at the level `v(q)`
      intro g hg
      exfalso
      have h0 : par M 0 c = some i := (mem_children_iff.mp hcch).2
      have hvx : σ.v c = ρP.v r := by
        rw [hcxe, hσ, glueZ_v_ge ρ (shiftV ρP L) Z (le_refl _)]
        show ρP.v (r + L - L) = ρP.v r; rw [Nat.add_sub_cancel]
      have hle' : ρP.v r ≤ ρ.v i :=
        le_trans hQP0.1 (v_par1_le_par0 I.cons I.good I.rank hcM h0 (by rw [hcxe]; exact h1))
      have hot : isOT (ρP.v r) = true := hGP.ot_v r (by rw [hlP]; have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega)
      rw [hvx, comps_nil_of_le hot hle'] at hg
      simp at hg
    · have hcx : c < r + L := by omega
      by_cases hcv : DepX M (r + L) false c
      · exact vsf_frame I hlen hL hd0e h1 hx2 hn hH hCN hGN h hCL hcv hcx hPR
      · rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z hcx hcv]
        exact I.vs i (by omega) Lc c R hCL
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    have hCLs : CL (TRIO.gexp M r L d0 0 n) (r + L + a) =
        (CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a)).map (· + L) := by
      unfold CL
      rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha, List.filter_map]
      congr 1
      apply List.filter_congr
      intro d hd
      have hdc := mem_children hd
      rw [hlP] at hdc
      show decide (Counted (TRIO.gexp M r L d0 0 n) (r + L + a) (d + L)) =
        decide (Counted (TRIO.gexp M r L d0 0 (n - 1)) (r + a) d)
      apply decide_eq_decide.mpr
      apply counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath (I.z2 r) (ρ := ρ) (Z := Z) ha hd)
      · have := hσo (d - r); rw [show r + L + (d - r) = d + L by omega,
          show r + (d - r) = d by omega] at this
        exact this
      · obtain ⟨s, y, he⟩ := o_psi_form hCP (i := d) (by rw [hlP]; omega)
        rw [he]; simp
    rw [hCLs] at hCL
    obtain ⟨Lc', T', hsplit, hLc, hT⟩ := List.map_eq_append_iff.mp hCL
    obtain ⟨c', R', hT', hc', hR'⟩ := List.map_eq_cons_iff.mp hT
    subst hLc hc' hR'
    rw [hT'] at hsplit
    have hLo : (Lc'.map (· + L)).map σ.o = Lc'.map ρP.o := by
      rw [List.map_map]
      apply List.map_congr_left
      intro d hd
      have hdCL : d ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp [hd]
      have hdc := mem_children (List.mem_filter.mp hdCL).1
      have := hσo (d - r)
      rw [show r + L + (d - r) = d + L by omega, show r + (d - r) = d by omega] at this
      exact this
    have hc'c := mem_children (List.mem_filter.mp (show c' ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) by
      rw [hsplit]; simp)).1
    rw [hlP] at hc'c
    have hvc : σ.v (c' + L) = ρP.v c' := by
      have := hσv (c' - r)
      rw [show r + L + (c' - r) = c' + L by omega, show r + (c' - r) = c' by omega] at this
      exact this
    rw [hσv, hLo, hvc]
    exact hQP (r + a) (by rw [hlP]; omega) Lc' c' R' hsplit

/-- **`t = 1`, `n ≥ 2`, in the `gexp` form** with VSmallF carried by `expStep_vsmallF2` (residual `PassRootRes`
in place of `VSFRes2`). -/
theorem inv3V_N_t1P {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 1 (r + L) = some r)
    (hx2 : entry M 2 (r + L) = 0)
    (hRT : RestT M rk)
    (hResL : TPLoRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResD : AbsDRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResU : AbsUWRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResDN : AbsDNRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hPR : PassRootRes M r L ρ)
    (hNG : NoGapP M ρ)
    (hFr : ∀ n σ rkN, 2 ≤ n → Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) rkN →
      Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      BumpKidsDec (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      BumpTermDec (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      AbsD (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      TPLo (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      TPLoW (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ ∧
      AbsDW (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ ∧ TPLoN (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN,
      Inv3V (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN rkN ∧
      NoGapP (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN < root M ρ := by
  intro n hn
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; have := par_lt M 1 _ r hr; omega
    · exact h
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hdr := R.drop
  have hsd := R.seed
  rw [show M.length - 1 = r + L by omega] at hdr hsd
  have hVI : ValInv M ρ := ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩
  have V1 := valInv_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank hVI hdr
  have hx0 : entry M 0 (r + L) ≠ 0 := by
    have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
  have hRP1 := rootP_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r01 I.r12 I.e00 hx0 I.cons I.rank hVI hdr
    I.rootP
  have hRT' := hRT
  simp only [RestT] at hRT'
  rw [show M.length - 1 = r + L by omega] at hRT'
  obtain ⟨ad, tp1, tplo, tp1w, tplow, auw, adw, trig, tplon, adn⟩ := hRT'
  have hcntG := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1' : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcntG
  have hC1' : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1'
  have hAg := agr_base hlen hL0 hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 I.cons I.good I.rank
  have hP1 : (fun N σ => (PT1C M r ρ N σ ∧ (AgrT1 M r ρ N σ ∧ NoGapP N σ)) ∧ (AgrT1 M r ρ N σ ∧ VP (InVKv M ρ) N σ))
      (M.take (r + L)) (drop1 M (r + L) rk) := ⟨⟨
    ⟨V1.fo, hRP1, ⟨V1.kd, V1.td⟩, V1.fc, trig, tp1, tp1w, tplo, ⟨hAg, ad⟩, ⟨hAg, auw⟩, ⟨hAg, adn⟩,
      ⟨vrle_base I R hlen hr, V1.vs⟩⟩, hAg,
      vP_take (show r + L + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1' hRk1' hNG⟩, hAg,
      vP_take (show r + L + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1' hRk1'
        (Q := InVKv M ρ) (fun c p hc hp => ⟨c, p, hc, hp, rfl⟩)⟩
  have hPs : ExpStepT1 (fun N σ => (PT1C M r ρ N σ ∧ (AgrT1 M r ρ N σ ∧ NoGapP N σ)) ∧
      (AgrT1 M r ρ N σ ∧ VP (InVKv M ρ) N σ)) M r L
      (entry M 0 (r + L) - entry M 0 r) ρ := expStep_and (expStep_and (
    expStep_and (expStep_frameOT_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.fo)
      (expStep_and (expStep_rootP_t1 hlen hL0 hd0e I.z2 I.uat I.r12 I.be I.r01 I.e00 hr hx2 I.rootP)
        (expStep_and (expStep_bumpDec_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.good
            ⟨I.kd, I.td⟩)
          (expStep_and (expStep_frameClosed_t1' I hlen hL0 hd0e hr hx2)
            (expStep_and (expStep_trigOmC I hlen hL0 hd0e hr hx2)
              (expStep_and (expStep_tp1C I hlen hL0 hd0e hr hx2)
                (expStep_and (expStep_tp1WC I hlen hL0 hd0e hr hx2)
                  (expStep_and (expStep_tplo I hlen hL0 hd0e hr hx2 hResL)
                    (expStep_and (expStep_absD I hlen hL0 hd0e hr hx2 hResD)
                      (expStep_and (expStep_absUW I hlen hL0 hd0e hr hx2 hResU)
                        (expStep_and (expStep_absDN I hlen hL0 hd0e hr hx2 hResDN)
                          (expStep_vsmallF2 I hlen hL0 hd0e hr hx2 hPR))))))))))))
    (expStep_VP NoGap I hlen hL0 hd0e hr hx2 hNG))
    (expStep_VP (InVKv M ρ) I hlen hL0 hd0e hr hx2 (fun c p hc hp => ⟨c, p, hc, hp, rfl⟩))
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩ :=
      qr_final4 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2 hq
        I.cons I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua I.ad I.tp1w
        I.tplow I.auw I.adw I.tp1 I.trig I.tplon I.adn I.rootS I.rootP (hsd q hr hq) (fun N σ => (PT1C M q ρ N σ ∧ (AgrT1 M q ρ N σ ∧ NoGapP N σ)) ∧ (AgrT1 M q ρ N σ ∧ VP (InVKv M ρ) N σ))
        hP1 hPs n hn
    exact ⟨ρN, rkN, inv3V_of_PT1C hCN hRN hGN hPN.1.1 (hFr n ρN rkN hn hRN hCN hGN hPN.1.1.2.2.1.1 hPN.1.1.2.2.1.2
      hPN.1.1.2.2.2.2.2.2.2.2.1.2 hPN.1.1.2.2.2.2.2.2.2.1), hPN.1.2.2,
      hot, hlt⟩
  · obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons (show r < M.length by omega)
    obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩ :=
      t1_main_final hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2
        (fun h' => hqr (Option.some.inj (hq.symm.trans h'))) I.cons I.good I.rank I.vs I.fc I.fo
        I.tp1 I.tplo I.ad I.au hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua rfl h0 I.rootS I.rootP
        V1.g (fun N σ => (PT1C M r ρ N σ ∧ (AgrT1 M r ρ N σ ∧ NoGapP N σ)) ∧ (AgrT1 M r ρ N σ ∧ VP (InVKv M ρ) N σ))
        hP1 hPs n hn
    exact ⟨ρN, rkN, inv3V_of_PT1C hCN hRN hGN hPN.1.1 (hFr n ρN rkN hn hRN hCN hGN hPN.1.1.2.2.1.1 hPN.1.1.2.2.1.2
      hPN.1.1.2.2.2.2.2.2.2.2.1.2 hPN.1.1.2.2.2.2.2.2.2.1), hPN.1.2.2,
      hot, hlt⟩

/-- **The `t = 1` part of `hExp` for `trio_terminates_main_GP`** (only `Inv3V` of `M[n]` is needed there; also
gives `NoGapP`). `LevLeafInv` (groupA, global) replaces the false `VKFree`; `PassRootRes` replaces `VSFRes2`.
Residuals: `hRT`, `hFrm`, `hResN` (the seed-below and level-0 parts, `TPLoLFRes`, `PassRootRes`), `hNGM`, `hLL`. -/
theorem hExp_t1GP
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hFrm : ∀ N σ, Std N → N ≠ SRO → FrameV N σ → LevLeafInv N σ →
      TPLoWLFRes N σ ∧ TPLoW0 N σ ∧ AbsDW0 N σ ∧ TPLoNSeed N σ ∧ TPLoN0 N σ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      (DegRes TPLoAt M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoLFRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
        TPLoSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      (AbsDSeedLow2 M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsDResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      (AbsUWSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsUWResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      (AbsDNSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsDNZero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ PassRootRes M r L ρ)
    (hNGM : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → NoGapP M ρ)
    (hLL : ∀ N σ, Std N → N ≠ SRO → Cons N σ → Good3 N σ → LevLeafInv N σ) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
      ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ NoGapP (expand M n) ρN := by
  intro M ρ rk hM hS hE I R hz h1t n hn _ _
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hlen2 : 2 ≤ M.length := by
    by_contra h
    have hx0 : M.length - 1 = 0 := by omega
    apply hz
    rw [hx0]
    have e0 := I.e00
    have e1 := I.r01 0 e0
    have e2 := I.r12 0 e1
    exact (col_zero_iff M 0).mpr ⟨e0, e1, e2⟩
  have hx2 : entry M 2 (M.length - 1) = 0 := by
    unfold TRIO.srow at h1t
    by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
    · rw [if_pos ha] at h1t; cases h1t
    · show TRIO.entry M 2 (M.length - 1) = 0; omega
  rw [h1t] at hr
  have hexp := expand_eq_gexp_t1 M n hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hexpA := fun n' => expand_eq_gexp_t1 M n' hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  rw [hL] at hexp hexpA hr hx2
  simp only [Nat.add_sub_cancel_left] at hexp hexpA
  have hlen : r + L + 1 = M.length := by omega
  have hVK := hLL M ρ hM hS I.cons I.good
  have hRN := hResN M ρ rk hM hS I R r L hlen hr hx2
  obtain ⟨ρN, rkN, V, NG, _, _⟩ :=
    inv3V_N_t1P I R hlen hr hx2 (hRT M ρ rk hM hS I R hz h1t)
      (tploRes_of_L ⟨hRN.1.1, tploResL_lf_of_leaf I hlen hr hx2 hVK hRN.1.2.1,
        tploResL_seed_of (tploResL_lf_of_leaf I hlen hr hx2 hVK hRN.1.2.1) hRN.1.2.2.1, hRN.1.2.2.2⟩)
      (absDRes_of_L I hlen hr hx2 ⟨absDResL_lf_of_leaf I hlen hr hx2 hVK,
        absDResL_seed_of (absDResL_lf_of_leaf I hlen hr hx2 hVK)
          (absDSeedLow_of_noGap hlen (hNGM M ρ rk hM hS I R) hRN.2.1.1), hRN.2.1.2⟩)
      (absUWRes_of_L hx2 ⟨absUWResL_lf_of_leaf I hlen hr hx2 hVK,
        absUWResL_seed_of (absUWResL_lf_of_leaf I hlen hr hx2 hVK) hRN.2.2.1.1, hRN.2.2.1.2⟩)
      (absDNRes_of_leaf I hlen hr hx2 hVK hRN.2.2.2.1.1 hRN.2.2.2.1.2) hRN.2.2.2.2 (hNGM M ρ rk hM hS I R)
      (fun n' σ rkN hn' hRk hC hG hkd htd had htplo => by
        have hexp' := hexpA n'
        rw [← hexp'] at hRk hC hG hkd htd had htplo ⊢
        have hvk := hLL _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) hC hG
        have hS' := sInv_std (Std.exp n' hM) (ne_SRO_of_rk hRk)
        obtain ⟨h1, h2, h4, h5, h6⟩ := hFrm _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) ⟨hS', hC, hG, hkd, htd, had, htplo⟩ hvk
        exact ⟨tplow_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (tploWLF_of_leaf hC hG hvk h1) h2,
          absDW_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (absDWLF_of_leaf hC hG hvk) h4,
          tplon_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (tploWLF_of_leaf hC hG hvk h1) h5 h6⟩) n hn
  rw [← hexp] at V NG
  exact ⟨ρN, rkN, V, NG⟩

end Ytosk
