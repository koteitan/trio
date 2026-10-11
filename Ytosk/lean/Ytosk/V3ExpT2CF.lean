/-
**3 行・t = 2: 写しの列の枠（数える子・値）を P の枠の σ 像で書く。**
-/
import Ytosk.V3ExpT2V

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **The facts of the copy frames** (`V = v_P(r)`, guard `g`): the counted children shift, and the values
move by `σ` on guarded frames (all counted children of `r` guarded), are equal on the others. -/
def CopyFacts (N P : Mat) (σ ρ : Valn) (r L : Nat) (V' : T) (g : Nat → Prop) : Prop :=
  ∀ i, r ≤ i → i < P.length →
    CL N (i + L) = (CL P i).map (· + L) ∧
    (g i → σ.v (i + L) = shf (ρ.v r) V' (ρ.v i) ∧ ρ.v r ≤ ρ.v i ∧ (r < i → ρ.v r < ρ.v i) ∧
      ∀ d ∈ CL P i, σ.o (d + L) = sh (ρ.v r) V' (ρ.o d) ∧ (i = r → ρ.v r < ρ.v d)) ∧
    (¬ g i → σ.v (i + L) = ρ.v i ∧ ∀ d ∈ CL P i, σ.o (d + L) = ρ.o d)

/-- **The bump structure of the copy frames**: row 2, children and bump children shift; the children of
a bump child move by `σ` under a guarded column, are equal under the others. -/
def BumpCopyFacts (N P : Mat) (σ ρ : Valn) (r L : Nat) (V' : T) (g : Nat → Prop) : Prop :=
  ∀ i, r ≤ i → i < P.length →
    entry N 2 (i + L) = entry P 2 i ∧ children N (i + L) = (children P i).map (· + L) ∧
    ∀ j ∈ children P i, (col N (j + L) = bump N (i + L) ↔ col P j = bump P i) ∧
      children N (j + L) = (children P j).map (· + L) ∧
      (r < i → col P j = bump P i → ∀ k ∈ children P j,
        (g i → σ.o (k + L) = sh (ρ.v r) V' (ρ.o k)) ∧ (¬ g i → σ.o (k + L) = ρ.o k))

section
variable {N P : Mat} {r L : Nat} {σ ρ : Valn} {g : Nat → Prop} {V' : T} {rk : Bool → Nat → Nat}
  (hCN : Cons N σ) (hCP : Cons P ρ) (hGP : Good3 P ρ) (hRP : Rk P rk)
  (hNl : N.length = P.length + L) (hrP : r < P.length)
  -- structure of the copies
  (hch : ∀ i, r ≤ i → i < P.length → children N (i + L) = (children P i).map (· + L))
  (hcnt : ∀ i d, r ≤ i → i < P.length → d ∈ children P i →
    (Counted N (i + L) (d + L) ↔ Counted P i d))
  (hbmp : ∀ i d, r ≤ i → i < P.length → d ∈ children P i →
    (col N (d + L) = bump N (i + L) ↔ col P d = bump P i))
  (he2 : ∀ i, r ≤ i → i < P.length → entry N 2 (i + L) = entry P 2 i)
  (he1 : ∀ i, r < i → i < P.length → (entry N 1 (i + L) = 0 ↔ entry P 1 i = 0))
  (hp1 : ∀ i, r < i → i < P.length → par N 1 (i + L) = (par P 1 i).map (sft r L))
  (hup : ∀ i, r < i → i < P.length → upg N (i + L) = (upg P i).map (sft r L))
  -- the guard
  (hg0 : g r)
  (hge1 : ∀ i, r < i → i < P.length → g i → entry P 1 i ≠ 0)
  (hgp : ∀ i, r < i → i < P.length → g i → ∃ t, par P 1 i = some t ∧ r ≤ t ∧ g t)
  (hgpn : ∀ i t, r < i → i < P.length → ¬ g i → par P 1 i = some t → r ≤ t → ¬ g t)
  (hgu : ∀ i k, r < i → i < P.length → g i → entry P 2 i = 0 → upg P i = some k → r < k ∧ g k)
  (hgun : ∀ i k, r < i → i < P.length → ¬ g i → upg P i = some k → r ≤ k → ¬ g k)
  (hgc : ∀ i d, r ≤ i → i < P.length → d ∈ children P i → Counted P i d → ¬ g i → ¬ g d)
  (hgb : ∀ i j k, r < i → i < P.length → j ∈ children P i → col P j = bump P i → k ∈ children P j →
    ¬ g i → ¬ g k)
  -- values
  (hgcV : ∀ i d, r ≤ i → i < P.length → d ∈ children P i → Counted P i d → g i → ¬ g d →
    ¬ ρ.v r < ρ.v d)
  (hgbV : ∀ i j k, r < i → i < P.length → j ∈ children P i → col P j = bump P i → k ∈ children P j →
    g i → ¬ g k → ¬ ρ.v r < ρ.v k)
  (hbase : ∀ i t, r < i → i < P.length → (par P 1 i = some t ∨ upg P i = some t) → t < r →
    σ.v t = ρ.v t)
  (hroot : σ.v (r + L) = V') (hV' : isOT V' = true) (hVV : ρ.v r < V')
  (hgcr : ∀ d ∈ children P r, Counted P r d → g d)

include hch hcnt in
/-- **The counted children of a copy column** are the shifted ones of `P`. -/
theorem copy_cl {i : Nat} (hri : r ≤ i) (hi : i < P.length) :
    CL N (i + L) = (CL P i).map (· + L) := by
  unfold CL
  rw [hch i hri hi, List.filter_map]
  congr 1
  apply List.filter_congr
  intro d hd
  simp only [Function.comp, hcnt i d hri hi hd]

include hCN hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0 hgpn hgun hgc hgb hgcV hgbV hbase hroot hV' hVV
  hgcr hCP hGP hRP hge1 hgp hgu in
/-- **The values at a copy frame**: guarded, `v` and the counted values move by `σ`; unguarded, equal. -/
theorem copy_vals {i : Nat} (hri : r ≤ i) (hi : i < P.length) :
    (g i → σ.v (i + L) = shf (ρ.v r) V' (ρ.v i) ∧ ρ.v r ≤ ρ.v i ∧
      ∀ d ∈ CL P i, σ.o (d + L) = sh (ρ.v r) V' (ρ.o d) ∧ (g d → ρ.v r < ρ.v d) ∧
        (¬ g d → ¬ ρ.v r < ρ.v d)) ∧
    (¬ g i → σ.v (i + L) = ρ.v i ∧ ∀ d ∈ CL P i, σ.o (d + L) = ρ.o d) := by
  set V := ρ.v r with hVdef
  have rel := fun b j (hrj : r ≤ j) (hj : j < P.length) =>
    copy_rel hCN hCP hGP hRP hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0 hge1 hgp hgpn hgu hgun hgc hgb hgcV
      hgbV hbase hroot hV' hVV hgcr _ b j (Nat.lt_succ_self _) hrj hj
  have hgv : ∀ j, r < j → j < P.length → g j → V < ρ.v j := fun j h1 h2 h3 =>
    gv_gt hCP hGP hRP hge1 hgp hgu _ j (Nat.lt_succ_self _) h1 h2 h3
  refine ⟨fun hg => ⟨(rel false i hri hi).1 hg, ?_, fun d hd => ?_⟩, fun hg => ⟨(rel false i hri hi).2 hg,
    fun d hd => ?_⟩⟩
  · rcases Nat.lt_or_ge r i with h | h
    · exact le_of_lt (hgv i h hi hg)
    · have : i = r := by omega
      subst this; exact le_refl _
  · have hdch := cl_mem_children hd
    have hcnt' : Counted P i d := by unfold CL at hd; simpa using (List.mem_filter.mp hd).2
    have hdl := (mem_children hdch).2
    have hrd : r < d := by have := (mem_children hdch).1; omega
    obtain ⟨y', hy'⟩ := o_form hCP hGP hdl
    by_cases hgd : g d
    · have e : σ.o (d + L) = shO V V' (ρ.o d) := (rel true d (le_of_lt hrd) hdl).1 hgd
      have hvd := hgv d hrd hdl hgd
      refine ⟨?_, fun _ => hvd, fun h => absurd hgd h⟩
      rw [e, hy']; exact shO_eq_sh hvd
    · have e : σ.o (d + L) = ρ.o d := (rel true d (le_of_lt hrd) hdl).2 hgd
      have hle := hgcV i d hri hi hdch hcnt' hg hgd
      refine ⟨?_, fun h => absurd h hgd, fun _ => hle⟩
      rw [e, hy']
      exact (sh_fix (hy' ▸ hGP.ot_o d hdl) (by simpa using hle)).symm
  · have hdch := cl_mem_children hd
    have hcnt' : Counted P i d := by unfold CL at hd; simpa using (List.mem_filter.mp hd).2
    have hdl := (mem_children hdch).2
    have hrd : r ≤ d := by have := (mem_children hdch).1; omega
    exact (rel true d hrd hdl).2 (hgc i d hri hi hdch hcnt' hg)

include hCN hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0 hgpn hgun hgc hgb hgcV hgbV hbase hroot hV' hVV
  hgcr hCP hGP hRP hge1 hgp hgu in
/-- **`FrameOT` at the copy frames** from that of `P` (`σ` commutes with `sp`, `isOT_shTop`). -/
theorem copy_frameOT (hFO : FrameOT P ρ) {i : Nat} (hri : r ≤ i) (hi : i < P.length) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N (i + L) = Lc ++ c :: R →
      isOT (psi (σ.v (i + L)) (spArg (σ.v (i + L)) z (sumN (Lc.map σ.o))) z) = true := by
  set V := ρ.v r with hVdef
  have hVo : isOT V = true := hGP.ot_v r hrP
  intro Lc c R h
  rw [copy_cl hch hcnt hri hi] at h
  obtain ⟨Lc0, rest, hsplit, hLc, hrest⟩ := List.map_eq_append_iff.mp h
  obtain ⟨c0, R0, hrest0, _, _⟩ := List.map_eq_cons_iff.mp hrest
  rw [hrest0] at hsplit
  have hF := hFO i hi Lc0 c0 R0 hsplit
  obtain ⟨hgc', hngc⟩ := copy_vals hCN hCP hGP hRP hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0 hge1 hgp hgpn hgu
    hgun hgc hgb hgcV hgbV hbase hroot hV' hVV hgcr hri hi
  subst hLc
  obtain ⟨hsM, hpM⟩ := cl_vals hCP hGP hi
  rw [hsplit] at hsM hpM
  have hLs : ∀ t ∈ Lc0.map ρ.o, Single t := fun t ht => hsM t (by
    rw [List.map_append]; exact List.mem_append_left _ ht)
  have hLp : (Lc0.map ρ.o).Pairwise (fun a b => b ≤ a) := by
    rw [List.map_append] at hpM; exact (List.pairwise_append.mp hpM).1
  obtain ⟨hSot, hSsum⟩ := sumN_dec _ hLs hLp
  have hLot : ∀ t ∈ Lc0.map ρ.o, isOT t = true := fun t ht => (hLs t ht).1
  have hmem : ∀ d ∈ Lc0, d ∈ CL P i := fun d hd => by rw [hsplit]; exact List.mem_append_left _ hd
  rw [List.map_map]
  by_cases hg : g i
  · obtain ⟨hv, hVi, hd⟩ := hgc' hg
    have hmap : Lc0.map (σ.o ∘ (· + L)) = (Lc0.map ρ.o).map (sh V V') := by
      rw [List.map_map]; apply List.map_congr_left; intro d hd'; exact (hd d (hmem d hd')).1
    have hai : isOT (ρ.v i) = true := hGP.ot_v i hi
    have hlev : V < ρ.v i ∨ ∀ q ∈ summands (sumN (Lc0.map ρ.o)), lev q ≠ V := by
      rcases Nat.lt_or_ge r i with h1 | h1
      · exact Or.inl (gv_gt hCP hGP hRP hge1 hgp hgu _ i (Nat.lt_succ_self _) h1 hi hg)
      · have hir : i = r := by omega
        right
        rw [hSsum]
        intro q hq
        obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hq
        have hdC := hmem d hd'
        have hdch := cl_mem_children hdC
        have hcnt' : Counted P i d := by unfold CL at hdC; simpa using (List.mem_filter.mp hdC).2
        rw [hir] at hdch hcnt'
        have hgd := hgcr d hdch hcnt'
        have hvd := ((hd d hdC).2.1) hgd
        obtain ⟨y', hy'⟩ := o_form hCP hGP (mem_children hdch).2
        rw [hy']; simp only [lev]
        exact ne_of_gt hvd
    rw [hv, hmap, ← sh_sumN hVo hV' hVV hLot]
    have hsp := sh_spArg hVo hV' hVV hai hVi (b := z) rfl hSot hlev
    rw [sh_z] at hsp
    rw [hsp]
    exact isOT_shTop hVo hV' hVV hF hVi
  · obtain ⟨hv, hd⟩ := hngc hg
    have hmap : Lc0.map (σ.o ∘ (· + L)) = Lc0.map ρ.o := by
      apply List.map_congr_left; intro d hd'; exact hd d (hmem d hd')
    rw [hv, hmap]; exact hF

include hCN hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0 hgpn hgun hgc hgb hgcV hgbV hbase hroot hV' hVV
  hgcr hCP hGP hRP hge1 hgp hgu in
/-- **`CopyFacts` hold.** -/
theorem copy_facts : CopyFacts N P σ ρ r L V' g := by
  intro i hri hi
  obtain ⟨hg, hng⟩ := copy_vals hCN hCP hGP hRP hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0 hge1 hgp hgpn hgu
    hgun hgc hgb hgcV hgbV hbase hroot hV' hVV hgcr hri hi
  refine ⟨copy_cl hch hcnt hri hi, fun h => ?_, hng⟩
  obtain ⟨h1, h2, h3⟩ := hg h
  refine ⟨h1, h2, fun hlt => gv_gt hCP hGP hRP hge1 hgp hgu _ i (Nat.lt_succ_self _) hlt hi h,
    fun d hd => ⟨(h3 d hd).1, fun hir => ?_⟩⟩
  have hdC := hd
  have hdch := cl_mem_children hdC
  have hcnt' : Counted P i d := by unfold CL at hdC; simpa using (List.mem_filter.mp hdC).2
  rw [hir] at hdch hcnt'
  exact (h3 d hd).2.1 (hgcr d hdch hcnt')

include hCN hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0 hgpn hgun hgc hgb hgcV hgbV hbase hroot hV' hVV
  hgcr hCP hGP hRP hge1 hgp hgu in
/-- **`BumpCopyFacts` hold.** -/
theorem bump_copy_facts : BumpCopyFacts N P σ ρ r L V' g := by
  set V := ρ.v r with hVdef
  have rel := fun b j (hrj : r ≤ j) (hj : j < P.length) =>
    copy_rel hCN hCP hGP hRP hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0 hge1 hgp hgpn hgu hgun hgc hgb hgcV
      hgbV hbase hroot hV' hVV hgcr _ b j (Nat.lt_succ_self _) hrj hj
  intro i hri hi
  refine ⟨he2 i hri hi, hch i hri hi, fun j hj => ?_⟩
  have hjl := (mem_children hj).2
  have hij := (mem_children hj).1
  refine ⟨hbmp i j hri hi hj, hch j (by omega) hjl, fun hri' hjb k hk => ?_⟩
  have hkl := (mem_children hk).2
  have hjk := (mem_children hk).1
  obtain ⟨y', hy'⟩ := o_form hCP hGP hkl
  refine ⟨fun hg => ?_, fun hg => (rel true k (by omega) hkl).2 (hgb i j k hri' hi hj hjb hk hg)⟩
  by_cases hgk : g k
  · have e : σ.o (k + L) = shO V V' (ρ.o k) := (rel true k (by omega) hkl).1 hgk
    have hvk := gv_gt hCP hGP hRP hge1 hgp hgu _ k (Nat.lt_succ_self _) (by omega) hkl hgk
    rw [e, hy']; exact shO_eq_sh hvk
  · have e : σ.o (k + L) = ρ.o k := (rel true k (by omega) hkl).2 hgk
    have hle := hgbV i j k hri' hi hj hjb hk hg hgk
    rw [e, hy']
    exact (sh_fix (hy' ▸ hGP.ot_o k hkl) (by simpa using hle)).symm

end

end Ytosk
