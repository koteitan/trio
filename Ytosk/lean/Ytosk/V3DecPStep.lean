import Ytosk.V3DecPTop

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
open T2SrcLeaf

/-- One step of decP: a child of a bump child transfers the value bound to w. -/
theorem decP_step {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {τ : Valn} (hτ : Cons (M.take (r + L)) τ)
    {w b k : Nat} (hwx : w < r + L) (hp1 : par M 1 w = some r) (he1 : entry M 1 w ≠ 0)
    (he2 : entry M 2 w ≠ 0) (hb : b ∈ children M w) (hbx : b < r + L) (hbb : col M b = bump M w)
    (hk : k ∈ children M b) (hkx : k < r + L) (hvk : qnS M ρ r L q ≤ τ.v k) :
    qnS M ρ r L q < τ.v w := by
  have hx1 : M.length - 1 = r + L := by omega
  have hτ' : Cons (M.take (M.length - 1)) τ := by rw [hx1]; exact hτ
  have hG := good3_take_anyV3U I (Ctx.drop (by omega)) (by omega) hτ'
  rw [hx1] at hG
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hNlen : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hvr : τ.v r = ρ.v r :=
    v_take_of_untopped I hlen (by omega) (topP_C hM hS I hlen hr hq hqr) hτ
  let X0 := sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))
  let Y := sumN (one :: (children (M.take (r + L)) w).map (bumpTerm (M.take (r + L)) τ w))
  let G := sumN ((children (M.take (r + L)) b).map τ.o)
  have hXot : isOT X0 = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm I.good q d
  have hYlist : ∀ t ∈ one :: (children (M.take (r + L)) w).map (bumpTerm (M.take (r + L)) τ w),
      isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm hG w d
  have hYot : isOT Y = true := isOT_sumN _ hYlist
  have hGlist : ∀ t ∈ (children (M.take (r + L)) b).map τ.o, isOT t = true := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hG.ot_o d (mem_children hd).2
  have hGot : isOT G = true := isOT_sumN _ hGlist
  have hbN : b ∈ children (M.take (r + L)) w := by
    rw [children_take]
    exact List.mem_filter.mpr ⟨hb, by simpa using hbx⟩
  have hbt : bumpTerm (M.take (r + L)) τ w b = omega G := by
    unfold bumpTerm
    rw [if_pos (by rw [col_take M hbx, bump_take M hwx]; exact hbb)]
  have hGY : omega G ≤ Y := by
    rw [← hbt]
    exact mem_le_sumN hYlist (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b, hbN, rfl⟩))
  have hkN : k ∈ children (M.take (r + L)) b := by
    rw [children_take]
    exact List.mem_filter.mpr ⟨hk, by simpa using hkx⟩
  have hok : τ.o k = psi (τ.v k) (argT (M.take (r + L)) τ k) z :=
    o_cl_eq hτ hG (by rw [hNlen]; exact hkx)
  have hpG : psi (add (ρ.v r) (omega X0)) z z ≤ G := by
    have hp : psi (qnS M ρ r L q) z z ≤ τ.o k := by
      rw [hok]
      exact le_trans (le_psi_sub hvk) (le_psi_arg (z_le _))
    exact le_trans hp (mem_le_sumN hGlist (List.mem_map.mpr ⟨k, hkN, rfl⟩))
  have hV : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  have hvw : τ.v w = add (ρ.v r) (omega Y) := by
    rw [(hτ w (by rw [hNlen]; exact hwx)).2]
    unfold vRhs
    rw [entry_take M 1 hwx, entry_take M 2 hwx, if_neg he1, if_neg he2,
      par_take M 1 w hwx, hp1]
    change sf (add (τ.v r) (omega Y)) = add (ρ.v r) (omega Y)
    rw [hvr, sf_ot (isOT_add hV (isOT_omega hYot))]
  rw [hvw]
  exact decp_term hV hXot hYot hGot hGY hpG

#print axioms decP_step

end Ytosk.V3Main.SeedPF
