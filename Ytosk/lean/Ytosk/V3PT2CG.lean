/-
**t = 2: 写しの枠の PH3cG・FC3（closure、2026-10-11）。**

写しの列 i + L（r ≤ i）の枠は P = M[n − 1] の列 i の枠の写し（`CopyFacts`、V3ExpT2CF）。守られた列では v が f で、
数える子の値が σ で移り、状態は σ の像（`sh_spArg`）。守られない列では値が等しい。
- 子の添字 s が V より大きいとき: 書き換えは P の枠の書き換えに戻り（σ は順序の埋め込み）、種類は `ph3cKindG_sh`、
  FC3 の結論は `fc3c_sh` で移る。
- s ≤ V のとき: 子の値は動かず、v(i + L) = f(v(i)) ≥ V′ > s なので書き換えない。
実測（deepA の t = 2、n = 2, 3）: 写しの B ≠ 0 の書き換えの枠は 169/169 が σ の像で V < s。
-/
import Ytosk.V3ExpT2CF
import Ytosk.V3PSh
import Ytosk.V3PT0G
import Ytosk.V3PShG
import Ytosk.V3PKindG

namespace Ytosk.G

open T

set_option linter.unusedSectionVars false

section
variable {N P : Mat} {r L : Nat} {σ ρ : Valn} {g : Nat → Prop} {V' : T}
  (hCF : CopyFacts N P σ ρ r L V' g) (hCP : Cons P ρ) (hGP : Good3 P ρ) (hrP : r < P.length)
  (hV' : isOT V' = true) (hVV : ρ.v r < V')
include hCF hCP hGP hrP hV' hVV

/-- The frame of a copy column: the state and the child's value. -/
theorem copy_frame {i : Nat} (hri : r ≤ i) (hi : i < P.length) {Lc : List Nat} {c : Nat} {R : List Nat}
    (h : CL N (i + L) = Lc ++ c :: R) :
    ∃ Lc0 c0 R0, CL P i = Lc0 ++ c0 :: R0 ∧ Lc = Lc0.map (· + L) ∧ c = c0 + L ∧
      ((g i ∧ σ.v (i + L) = shf (ρ.v r) V' (ρ.v i) ∧ ρ.v r ≤ ρ.v i ∧
        spArg (σ.v (i + L)) z (sumN (Lc.map σ.o)) = sh (ρ.v r) V' (spArg (ρ.v i) z (sumN (Lc0.map ρ.o))) ∧
        σ.o c = sh (ρ.v r) V' (ρ.o c0)) ∨
       (σ.v (i + L) = ρ.v i ∧ Lc.map σ.o = Lc0.map ρ.o ∧ σ.o c = ρ.o c0)) := by
  set V := ρ.v r with hVdef
  have hVo : isOT V = true := hGP.ot_v r hrP
  obtain ⟨hcl, hg, hng⟩ := hCF i hri hi
  rw [hcl] at h
  obtain ⟨Lc0, rest, hsplit, hLc, hrest⟩ := List.map_eq_append_iff.mp h
  obtain ⟨c0, R0, hrest0, hc0, _⟩ := List.map_eq_cons_iff.mp hrest
  rw [hrest0] at hsplit
  refine ⟨Lc0, c0, R0, hsplit, hLc.symm, hc0.symm, ?_⟩
  subst hLc hc0
  have hmem : ∀ d ∈ Lc0, d ∈ CL P i := fun d hd => by rw [hsplit]; exact List.mem_append_left _ hd
  have hcmem : c0 ∈ CL P i := by rw [hsplit]; simp
  by_cases hgi : g i
  · obtain ⟨hv, hVi, hlt, hd⟩ := hg hgi
    left
    refine ⟨hgi, hv, hVi, ?_, (hd c0 hcmem).1⟩
    obtain ⟨hsM, hpM⟩ := cl_vals hCP hGP hi
    rw [hsplit] at hsM hpM
    have hLs : ∀ t ∈ Lc0.map ρ.o, Single t := fun t ht => hsM t (by
      rw [List.map_append]; exact List.mem_append_left _ ht)
    have hLp : (Lc0.map ρ.o).Pairwise (fun a b => b ≤ a) := by
      rw [List.map_append] at hpM; exact (List.pairwise_append.mp hpM).1
    obtain ⟨hSot, hSsum⟩ := sumN_dec _ hLs hLp
    have hLot : ∀ t ∈ Lc0.map ρ.o, isOT t = true := fun t ht => (hLs t ht).1
    have hmap : (Lc0.map (· + L)).map σ.o = (Lc0.map ρ.o).map (sh V V') := by
      rw [List.map_map, List.map_map]; apply List.map_congr_left; intro d hd'
      exact (hd d (hmem d hd')).1
    have hai : isOT (ρ.v i) = true := hGP.ot_v i hi
    have hlev : V < ρ.v i ∨ ∀ q ∈ summands (sumN (Lc0.map ρ.o)), lev q ≠ V := by
      rcases Nat.lt_or_ge r i with h1 | h1
      · exact Or.inl (hlt h1)
      · have hir : i = r := by omega
        right
        rw [hSsum]
        intro q hq
        obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hq
        have hvd := (hd d (hmem d hd')).2 hir
        obtain ⟨y', hy'⟩ := o_form hCP hGP (mem_children (cl_mem_children (hmem d hd'))).2
        rw [hy']; simp only [lev]
        exact ne_of_gt hvd
    rw [hv, hmap, ← sh_sumN hVo hV' hVV hLot]
    have hsp := sh_spArg hVo hV' hVV hai hVi (b := z) rfl hSot hlev
    rw [sh_z] at hsp
    exact hsp
  · obtain ⟨hv, hd⟩ := hng hgi
    right
    refine ⟨hv, ?_, hd c0 hcmem⟩
    rw [List.map_map]; apply List.map_congr_left; intro d hd'; exact hd d (hmem d hd')

/-- **PH3cG at a copy frame**, from that of `P`. -/
theorem copy_ph3c (hFO : FrameOT P ρ) (hP : PH3cG P ρ) {i : Nat} (hri : r ≤ i) (hi : i < P.length) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N (i + L) = Lc ++ c :: R →
      QPH (σ.v (i + L)) (Lc.map σ.o) (σ.o c) := by
  set V := ρ.v r with hVdef
  have hVo : isOT V = true := hGP.ot_v r hrP
  intro Lc c R h s' y' hc' ht' hB'
  obtain ⟨Lc0, c0, R0, hsplit, rfl, rfl, hcase⟩ := copy_frame hCF hCP hGP hrP hV' hVV hri hi h
  have hc0P : c0 < P.length := (mem_children (cl_mem_children (show c0 ∈ CL P i by rw [hsplit]; simp))).2
  obtain ⟨y, hy⟩ := o_form hCP hGP hc0P
  set s := ρ.v c0 with hsdef
  have hyot : isOT (psi s y z) = true := by rw [← hy]; exact hGP.ot_o c0 hc0P
  have hK := ph3c_iff.mp hP i hi Lc0 c0 R0 hsplit
  rcases hcase with ⟨hgi, hv, hVi, hB, hco⟩ | ⟨hv, hL, hco⟩
  · rw [hB] at ht' hB' ⊢
    rw [hco, hy] at hc'
    have hai : isOT (ρ.v i) = true := hGP.ot_v i hi
    obtain ⟨hsM, hpM⟩ := cl_vals hCP hGP hi
    rw [hsplit] at hsM hpM
    have hLs : ∀ t ∈ Lc0.map ρ.o, Single t := fun t ht => hsM t (by
      rw [List.map_append]; exact List.mem_append_left _ ht)
    have hLp : (Lc0.map ρ.o).Pairwise (fun a b => b ≤ a) := by
      rw [List.map_append] at hpM; exact (List.pairwise_append.mp hpM).1
    have hBot : isOT (spArg (ρ.v i) z (sumN (Lc0.map ρ.o))) = true :=
      isOT_arg (hFO i hi Lc0 c0 R0 hsplit)
    by_cases hVs : V < s
    · rw [sh_psi_gt hVs] at hc'
      obtain ⟨rfl, rfl, -⟩ := T.psi.inj hc'
      -- the frame of `P` rewrites
      have hyo := isOT_arg hyot
      have hso := isOT_sub hyot
      have h1 : lt (spArg (ρ.v i) z (sumN (Lc0.map ρ.o))) y = true :=
        (sh_lt_iff hVo hV' (le_of_lt hVV) hBot hyo).mp ht'.1
      have h2 : lt (psi (ρ.v i) z z) (psi s y z) = true := by
        rcases (le_iff _ _).mp hVi with hVi' | hVi'
        · have e1 : sh V V' (psi (ρ.v i) z z) = psi (shf V V' (ρ.v i)) z z := by rw [sh_psi_gt hVi', sh_z]
          have e2 : sh V V' (psi s y z) = psi (shf V V' s) (sh V V' y) z := by rw [sh_psi_gt hVs]; simp
          have := ht'.2; rw [hv] at this
          rw [← e1, ← e2] at this
          exact (sh_lt_iff hVo hV' (le_of_lt hVV) (isOT_om.mpr hai) hyot).mp this
        · rw [← hVi']; exact psi_lt_psi_z_iff.mpr (Or.inl hVs)
      have hBP : spArg (ρ.v i) z (sumN (Lc0.map ρ.o)) ≠ z := fun e => hB' (by rw [e, sh_z])
      exact ph3cKindG_sh hVo hV' hVV hso hVs hBot hyo (hK s y hy ⟨h1, h2⟩ hBP)
    · rw [sh_psi_le hVs] at hc'
      simp only [sh_z] at hc'
      obtain ⟨rfl, rfl, -⟩ := T.psi.inj hc'
      exfalso
      have h2 := ht'.2
      rw [hv] at h2
      have hV'v : V' ≤ shf V V' (ρ.v i) := le_shf hVo hV' (le_of_lt hVV) (hGP.ot_v i hi) hVi
      have hss : s < shf V V' (ρ.v i) := lt_of_le_of_lt (le_of_not_gt hVs) (lt_of_lt_of_le hVV hV'v)
      rcases psi_lt_psi_z_iff.mp (show psi _ z z < psi s y z from h2) with h | ⟨h, _⟩
      · exact lt_irrefl' _ (lt_trans h hss)
      · rw [h] at hss; exact lt_irrefl' _ hss
  · rw [hco] at hc'
    rw [hv, hL] at ht' hB'
    rw [hv, hL]
    exact hK s' y' hc' ht' hB'

/-- **FC3 at a copy frame**, from that of `P`. -/
theorem copy_fc3 (hP : FC3 P ρ) {i : Nat} (hri : r ≤ i) (hi : i < P.length) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N (i + L) = Lc ++ c :: R →
      QF3 (σ.v (i + L)) (Lc.map σ.o) (σ.o c) := by
  set V := ρ.v r with hVdef
  have hVo : isOT V = true := hGP.ot_v r hrP
  intro Lc c R h s' y' hc' ht' hL' hhi'
  obtain ⟨Lc0, c0, R0, hsplit, rfl, rfl, hcase⟩ := copy_frame hCF hCP hGP hrP hV' hVV hri hi h
  have hc0P : c0 < P.length := (mem_children (cl_mem_children (show c0 ∈ CL P i by rw [hsplit]; simp))).2
  obtain ⟨y, hy⟩ := o_form hCP hGP hc0P
  set s := ρ.v c0 with hsdef
  have hyot : isOT (psi s y z) = true := by rw [← hy]; exact hGP.ot_o c0 hc0P
  have hK := fc3_iff.mp hP i hi Lc0 c0 R0 hsplit
  have hL0 : Lc0 = [] := by
    have := List.map_eq_nil_iff.mp hL'; exact List.map_eq_nil_iff.mp this
  subst hL0
  rcases hcase with ⟨hgi, hv, hVi, hB, hco⟩ | ⟨hv, hL, hco⟩
  · rw [hco, hy] at hc'
    rw [hv]
    have hai : isOT (ρ.v i) = true := hGP.ot_v i hi
    by_cases hVs : V < s
    · rw [sh_psi_gt hVs] at hc'
      obtain ⟨rfl, rfl, -⟩ := T.psi.inj hc'
      have hyo := isOT_arg hyot
      have hso := isOT_sub hyot
      have hy0 : y ≠ z := fun e => by
        have := ht'.1; rw [e, sh_z] at this; exact T.not_lt_z _ this
      have h2 : lt (psi (ρ.v i) z z) (psi s y z) = true := by
        rcases (le_iff _ _).mp hVi with hVi' | hVi'
        · have e1 : sh V V' (psi (ρ.v i) z z) = psi (shf V V' (ρ.v i)) z z := by rw [sh_psi_gt hVi', sh_z]
          have e2 : sh V V' (psi s y z) = psi (shf V V' s) (sh V V' y) z := by rw [sh_psi_gt hVs]; simp
          have := ht'.2; rw [hv] at this
          rw [← e1, ← e2] at this
          exact (sh_lt_iff hVo hV' (le_of_lt hVV) (isOT_om.mpr hai) hyot).mp this
        · rw [← hVi']; exact psi_lt_psi_z_iff.mpr (Or.inl hVs)
      exact fc3c_sh hVo hV' hVV hai hVi hso hVs hyo
        (fun hhi => hK s y hy ⟨lt_z_of_ne hy0, h2⟩ rfl hhi) hhi'
    · rw [sh_psi_le hVs] at hc'
      simp only [sh_z] at hc'
      obtain ⟨rfl, rfl, -⟩ := T.psi.inj hc'
      exfalso
      have h2 := ht'.2
      rw [hv] at h2
      have hV'v : V' ≤ shf V V' (ρ.v i) := le_shf hVo hV' (le_of_lt hVV) (hGP.ot_v i hi) hVi
      have hss : s < shf V V' (ρ.v i) := lt_of_le_of_lt (le_of_not_gt hVs) (lt_of_lt_of_le hVV hV'v)
      rcases psi_lt_psi_z_iff.mp (show psi _ z z < psi s y z from h2) with h | ⟨h, _⟩
      · exact lt_irrefl' _ (lt_trans h hss)
      · rw [h] at hss; exact lt_irrefl' _ hss
  · rw [hco] at hc'
    rw [hv, hL] at ht'
    rw [hv]
    exact hK s' y' hc' ht' rfl hhi'

end

end Ytosk.G
