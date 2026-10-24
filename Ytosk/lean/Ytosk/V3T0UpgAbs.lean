/-
Weak-absorption consumers for t=0. Only new declarations; no global strong
absorption hypothesis is assumed or restated as a new residual.
-/
import Ytosk.V3T0Weak
import Ytosk.V3T0W
import Ytosk.V3InvJ

namespace Ytosk.T0UpgAbs
open T

/-- The weak alternative itself excludes a bump parent of the upgrade source.
The row-1/Easy conjunct is unnecessary for this local strong consumer. -/
theorem strong_of_not_nb {M : Mat} {ρ : Valn} {x : Nat}
    (hUA : UpgAbsXW0 M x ρ) (hp : par M 0 x = some (x - 1)) (hNB : ¬ NBPar M (x - 1)) :
    UpgAbsX M x ρ := by
  intro i k W hix hu hv hW
  rcases hUA i k W hix hu hv hW with hs | hw
  · exact hs
  · have hie : i = x - 1 := by omega
    subst hie
    exact False.elim (hNB (hw.2.2.nb_of_child hp))

/-- A child of a row-2-one ancestor of the final column cannot upgrade to
the next column: the upgrade target would have row0 at most that ancestor's. -/
theorem child_upgrade_ne_next {M : Mat} {x r c : Nat}
    (hx : x + 1 = M.length) (hZ1 : Z1C M)
    (hp : par M 0 x = some r) (hr2 : entry M 2 r = 1)
    (hc : c ∈ children M r) : upg M c ≠ some (c + 1) := by
  intro hu
  obtain ⟨m, hm, _, hcol, _⟩ := upg_spec hu
  have hmc := par_lt M 1 c m hm
  have hrc := (mem_children hc).1
  have hc1 := hZ1 r c hr2 hc
  have hm1 := par1_entry_lt hm
  have hmr : m ≠ r := by intro he; rw [he] at hm1; omega
  have hAmr : Anc0 M m r :=
    anc0_par (anc0_of_par M 1 m c hm) (by omega) (mem_children_iff.mp hc).2
  have hm0 := anc0_e0_lt hAmr hmr
  have hcx : c + 1 ≤ x := by have := upg_succ_lt hu; omega
  have hArc : Anc0 M r (c + 1) :=
    anc_between (Anc0.step hp (Anc0.refl r)) (c + 1) (by omega) hcx
  have hr0 := anc0_e0_lt hArc (by omega)
  have he0 := e0_of_col hcol
  omega

/-- The strong v relation actually needed by g0_drop_rel: only old children
of r=bump(g). RowJ/BumpLeaf are already structural facts of Std matrices. -/
theorem v_lhd_bump_children {M : Mat} {x r g : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hJ : RowJ M) (hBL : BumpLeaf M)
    (hp : par M 0 x = some r) (hg : par M 0 r = some g) (hrb : col M r = bump M g)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hUA : UpgAbsXW0 M x ρ)
    (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i) :
    ∀ d ∈ children M r, d < x → LhdE (ρ'.v d) (ρ.v d) := by
  intro d hd hdx
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : d < (M.take x).length := by omega
  have hiM : d < M.length := by omega
  have hrM : r < M.length := by have := par_lt M 0 x r hp; omega
  have hrg : r ∈ children M g := mem_children_iff.mpr ⟨hrM,hg⟩
  have hr2 : entry M 2 r = 1 := e2_of_col hrb
  have hr1 : entry M 1 r = entry M 1 g := e1_of_col hrb
  have hd2 : entry M 2 d = 0 := by
    by_contra hn
    have hj := hJ d r hn (mem_children_iff.mp hd).2
    have hb := hBL g r d hrg hrb hd (by rw [← hr1]; exact hj)
    exact hn hb.1
  have hoff := chg_off hx hC hG hC' hRk'
  by_cases hCv : ChgX M x false d
  swap
  · rw [(hoff d hdx).2 hCv]
    exact Or.inl rfl
  have h1 := chgx_e1 hCv
  have hV : vOpt ρ' (par (M.take x) 1 d) = vOpt ρ (par M 1 d) := by
    rw [par_take M 1 d hdx]
    cases hpm : par M 1 d with
    | none => rfl
    | some m =>
      apply (hoff m (by have := par_lt M 1 d m hpm; omega)).2
      intro hCm
      have hmd := par_lt M 1 d m hpm
      exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCm).1 rfl (by omega) |>.2.2 d hdx hpm
  have hVot : isOT (vOpt ρ (par M 1 d)) = true := by
    cases hpm : par M 1 d with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 d m hpm; omega)
  have hoot : ∀ k, ∀ j ∈ children M k, col M j = bump M k →
      ∀ k' ∈ children M j, isOT (ρ.o k') = true :=
    fun _ _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2
  have hv1 : upg (M.take x) d = none → ρ'.v d = sf (add (vOpt ρ (par M 1 d)) one) := by
    intro hu
    rw [(hC' d hiT).2]
    unfold vRhs
    rw [entry_take M 1 hdx,entry_take M 2 hdx,if_neg h1,if_pos hd2,hu,hV]
  by_cases hix : d + 1 < x
  · have hupT : upg (M.take x) d = upg M d := upg_take M hix
    cases hu : upg M d with
    | none =>
      have e1 := hv1 (by rw [hupT,hu])
      have e2 : ρ.v d = sf (add (vOpt ρ (par M 1 d)) one) := by
        rw [(hC d hiM).2]
        unfold vRhs
        rw [if_neg h1,if_pos hd2,hu]
      rw [e1,←e2]
      exact Or.inl rfl
    | some k =>
      have huT : upg (M.take x) d = some k := by rw [hupT,hu]
      have ek := v_upg_eq hC hiM h1 hd2 hu hVot (hoot k)
      have hkx : k < x := by have := upg_lt hiT huT; rw [hlenT] at this; exact this
      have ek' : ρ'.v d = ρ'.v k := v_upg_eq hC' hiT
        (by rw [entry_take M 1 hdx]; exact h1) (by rw [entry_take M 2 hdx]; exact hd2)
        huT (by rw [hV]; exact hVot)
        (fun _ _ _ k' hk' => (hdrop k' (by have := (mem_children hk').2; rw [hlenT] at this; exact this)).1.2.1)
      rw [ek,ek']
      obtain ⟨_,_,_,_,hcase⟩ := upg_spec hu
      rcases hcase with heq | ⟨hA,hki⟩
      · rw [heq] at hu
        exact False.elim (child_upgrade_ne_next hx hZ1 hp hr2 hd hu)
      · by_cases hCk : ChgX M x false k
        · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
            ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCk).1 rfl hkx) hkx hu hA hki).elim
        · rw [(hoff k hkx).2 hCk]
          exact Or.inl rfl
  · have hixe : d + 1 = x := by omega
    have huT : upg (M.take x) d = none := by
      rw [show d = x-1 by omega]
      exact upg_take_last M (by omega) (by omega)
    have e1 := hv1 huT
    have hot1 := isOT_add hVot isOT_one
    rw [e1,sf_ot hot1]
    cases hu : upg M d with
    | none =>
      have e2 : ρ.v d = sf (add (vOpt ρ (par M 1 d)) one) := by
        rw [(hC d hiM).2]
        unfold vRhs
        rw [if_neg h1,if_pos hd2,hu]
      rw [e2,sf_ot hot1]
      exact Or.inl rfl
    | some k =>
      have ek := v_upg_eq hC hiM h1 hd2 hu hVot (hoot k)
      have hk := upg_lt hiM hu
      obtain ⟨m,hm1,hm2,hcol,_⟩ := upg_spec hu
      have hk1 : entry M 1 k ≠ 0 := by rw [e1_of_col hcol]; exact h1
      have hk2 : entry M 2 k ≠ 0 := by rw [e2_of_col hcol]; omega
      have hVk : vOpt ρ (par M 1 k) = vOpt ρ (par M 1 d) := by rw [hm1,hm2]
      obtain ⟨sW,yW,hvk,hWot,hW1⟩ := v_bump_form hC hk hk1 hk2
        (by rw [hVk]; exact hVot) (hoot k)
      rw [hVk] at hvk
      rw [ek,hvk]
      have hs := (hUA d k _ hixe hu hvk (by simp)).resolve_right
        (fun hw => (hw.2.2 r g (mem_children_iff.mp hd).2 hg hrb).1
          (Anc0.step hp (Anc0.step hg (Anc0.refl g))))
      have hFrame := v_frame_xm1 hVot hWot hW1 (fun t ht _ hlt => hs t ht hlt)
      rw [sf_ot hot1] at hFrame
      exact hFrame

theorem lhd_t0_of {M : Mat} {x : Nat} {ρ ρ' : Valn} {r : Nat} (hx : x + 1 = M.length)
    (hUA : UpgAbsXW0 M x ρ) (hx1 : entry M 1 x = 0) (hp : par M 0 x = some r)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hrM : r < M.length) (hPO : PO ρ ρ' r) (hPV : PV M ρ ρ' r)
    (hnz : ∀ w, ρ.o r ≠ psi w z z) (hlt : ρ'.o r < ρ.o r) (h : r ≠ x - 1 ∨ ¬ NBPar M (x - 1))
    (h3 : NoBad3 M ρ) :
    Lhd z (ρ'.o r) (ρ.o r) := by
  have hE : LhdE (ρ'.o r) (ρ.o r) ∨ (WkOA (ρ'.o r) (ρ.o r) ∧ ∃ w, ρ.o r = psi w z z) := by
    by_cases hr : r = x - 1
    · have hnb := h.resolve_left (fun h' => h' hr)
      exact PO.zero_of_strong hx (strong_of_not_nb hUA (by rw [← hr]; exact hp) hnb) hC hG hrM hPO hPV
    · exact PO.zero_of_ne (by omega) hC hG hrM hPO hPV h3
  rcases hE with hE | ⟨_, w, hw⟩
  · exact lhd_of_lhdE_lt hE hlt
  · exact absurd hw (hnz w)

/-- **The drop at the parent `r` of a `t = 0` column `x`**: `◁`, or (when `r = x − 1` and its parent `g` is
not a bump child) a weak leaf whose components are dominated by `v(g)`. -/
theorem lhd_or_weak_t0 {M : Mat} {x : Nat} {ρ ρ' : Valn} {r g : Nat} (hx : x + 1 = M.length)
    (hUA : UpgAbsXW0 M x ρ) (hx1 : entry M 1 x = 0) (hp : par M 0 x = some r) (hg : par M 0 r = some g)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hrM : r < M.length)
    (hPO : PO ρ ρ' r) (hPV : PV M ρ ρ' r) (hnz : ∀ w, ρ.o r ≠ psi w z z) (hlt : ρ'.o r < ρ.o r)
    (h3 : NoBad3 M ρ) :
    Lhd z (ρ'.o r) (ρ.o r) ∨
      r = x - 1 ∧ NBPar M (x - 1) ∧ CntX M ρ r ∧
        ∃ w', ρ'.o r = psi w' z z ∧ WkVA w' (ρ.v r) ∧ WCS (ρ.v g) w' ∧ isOT (psi w' z z) = true := by
  by_cases h : r ≠ x - 1 ∨ ¬ NBPar M (x - 1)
  · exact Or.inl (lhd_t0_of hx hUA hx1 hp hC hG hrM hPO hPV hnz hlt h h3)
  · have hr : r = x - 1 := by by_contra h'; exact h (Or.inl h')
    have hnb : NBPar M (x - 1) := by by_contra h'; exact h (Or.inr h')
    rcases po_lhd_or_weak hC hG hC' hrM (by have := par_lt M 0 x r hp; omega) hPO hPV hg hnz hlt with
      h' | ⟨hCX, hw⟩
    · exact Or.inl h'
    · exact Or.inr ⟨hr, hnb, hCX, hw⟩
theorem po_zero_t0 {M : Mat} {x : Nat} {ρ ρ' : Valn} {r : Nat} (hx : x + 1 = M.length)
    (hUA : UpgAbsXW0 M x ρ) (hx1 : entry M 1 x = 0) (hp : par M 0 x = some r)
    (hS : par M 0 x = some (x - 1) → NBPar M (x - 1) → UpgAbsX M x ρ)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hrM : r < M.length) (hPO : PO ρ ρ' r) (hPV : PV M ρ ρ' r)
    (h3 : NoBad3 M ρ) :
    LhdE (ρ'.o r) (ρ.o r) ∨ (WkOA (ρ'.o r) (ρ.o r) ∧ ∃ w, ρ.o r = psi w z z) := by
  by_cases hr : r = x - 1
  · have hp' : par M 0 x = some (x - 1) := by rw [← hr]; exact hp
    by_cases hnb : NBPar M (x - 1)
    · exact PO.zero_of_strong hx (hS hp' hnb) hC hG hrM hPO hPV
    · exact PO.zero_of_strong hx (strong_of_not_nb hUA hp' hnb) hC hG hrM hPO hPV
  · exact PO.zero_of_ne (by omega) hC hG hrM hPO hPV h3

/-- **No counted child of a weak parent `r` of a `t = 0` column `x`** in the easy shape. -/
theorem cntx_nocnt_t0 {M : Mat} {x : Nat} {ρ : Valn} {r : Nat} (hx : x + 1 = M.length)
    (hUA : UpgAbsXW0 M x ρ) (hx1 : entry M 1 x = 0) (hp : par M 0 x = some r)
    (hS : par M 0 x = some (x - 1) → NBPar M (x - 1) → UpgAbsX M x ρ) (h : CntX M ρ r) (h3 : NoBad3 M ρ) :
    ∀ c ∈ children M r, ¬ Counted M r c := by
  by_cases hr : r = x - 1
  · have hp' : par M 0 x = some (x - 1) := by rw [← hr]; exact hp
    by_cases hnb : NBPar M (x - 1)
    · exact CntX.nocnt_of_strong hx (hS hp' hnb) h
    · exact CntX.nocnt_of_strong hx (strong_of_not_nb hUA hp' hnb) h
  · have hrx : r < x := par_lt M 0 x r hp
    exact CntX.nocnt_of_ne (by omega) h h3


#print axioms lhd_or_weak_t0
#print axioms po_zero_t0
#print axioms cntx_nocnt_t0
#print axioms strong_of_not_nb
#print axioms child_upgrade_ne_next
#print axioms v_lhd_bump_children
end Ytosk.T0UpgAbs
