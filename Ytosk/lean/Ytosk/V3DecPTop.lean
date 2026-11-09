import Ytosk.V3C1Strict
import Ytosk.V3T2SrcLeaf

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
open T2SrcLeaf

/-- The term part of decP: the nested bump term forces the exponent to grow. -/
theorem decp_term {V X0 Y G y : T} (hV : isOT V = true) (hX0 : isOT X0 = true)
    (hY : isOT Y = true) (hG : isOT G = true)
    (hGY : omega G ≤ Y) (hpG : psi (add V (omega X0)) y z ≤ G) :
    add V (omega X0) < add V (omega Y) := by
  have hXQ : X0 ≤ add V (omega X0) :=
    le_trans (self_le_omega hX0) (le_add_left_self (isOT_omega hX0) V)
  have hQG : add V (omega X0) < G :=
    lt_of_lt_of_le (lt_Om_self _) (le_trans (le_psi_arg (z_le y)) hpG)
  have hXY : X0 < Y :=
    lt_of_lt_of_le (lt_of_le_of_lt hXQ hQG) (le_trans (self_le_omega hG) hGY)
  exact add_lt_add_left V (omega_lt_omega hX0 hY hXY)

/-- decP when c0 has a bump child containing q - 1. -/
theorem decP_of_shape {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hun : upg M (r + L - 1) = none)
    {τ : Valn} (hτ : Cons (M.take (r + L)) τ)
    {c0 b : Nat} (hc0x : c0 < r + L) (hp1 : par M 1 c0 = some r) (he1 : entry M 1 c0 ≠ 0)
    (he2 : entry M 2 c0 ≠ 0) (hb : b ∈ children M c0) (hbx : b < r + L)
    (hbb : col M b = bump M c0) (hqb : q - 1 ∈ children M b)
    (hupq : upg M (q - 1) = some q) : qnS M ρ r L q < τ.v c0 := by
  have hx1 : M.length - 1 = r + L := by omega
  have hτ' : Cons (M.take (M.length - 1)) τ := by rw [hx1]; exact hτ
  have hG := good3_take_anyV3U I (Ctx.drop (by omega)) (by omega) hτ'
  rw [hx1] at hG
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hqm : q - 1 < r + L := by omega
  have hNlen : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hvr : τ.v r = ρ.v r :=
    v_take_of_untopped I hlen (by omega) (topP_C hM hS I hlen hr hq hqr) hτ
  let X0 := sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))
  let Y := sumN (one :: (children (M.take (r + L)) c0).map (bumpTerm (M.take (r + L)) τ c0))
  let G := sumN ((children (M.take (r + L)) b).map τ.o)
  have hXot : isOT X0 = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm I.good q d
  have hYlist : ∀ t ∈ one :: (children (M.take (r + L)) c0).map (bumpTerm (M.take (r + L)) τ c0),
      isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm hG c0 d
  have hYot : isOT Y = true := isOT_sumN _ hYlist
  have hGlist : ∀ t ∈ (children (M.take (r + L)) b).map τ.o, isOT t = true := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hG.ot_o d (mem_children hd).2
  have hGot : isOT G = true := isOT_sumN _ hGlist
  have hbN : b ∈ children (M.take (r + L)) c0 := by
    rw [children_take]
    exact List.mem_filter.mpr ⟨hb, by simpa using hbx⟩
  have hbt : bumpTerm (M.take (r + L)) τ c0 b = omega G := by
    unfold bumpTerm
    rw [if_pos (by rw [col_take M hbx, bump_take M hc0x]; exact hbb)]
  have hGY : omega G ≤ Y := by
    rw [← hbt]
    exact mem_le_sumN hYlist (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b, hbN, rfl⟩))
  have hqbN : q - 1 ∈ children (M.take (r + L)) b := by
    rw [children_take]
    exact List.mem_filter.mpr ⟨hqb, by simpa using hqm⟩
  have hux : ∀ c, upg M (r + L - 1) = some c → c = r + L := by
    intro c hc
    rw [hun] at hc
    cases hc
  have hvqm : τ.v (q - 1) = qnS M ρ r L q := by
    rw [v_upg_takeG I hlen hτ hG hux hupq hqx]
    exact c_vqP_of_un hM hS I hlen hr hq hqr hun τ hτ
  have hoqm : τ.o (q - 1) = psi (add (ρ.v r) (omega X0))
      (argT (M.take (r + L)) τ (q - 1)) z := by
    rw [o_cl_eq hτ hG (by rw [hNlen]; exact hqm)]
    change psi (τ.v (q - 1)) (argT (M.take (r + L)) τ (q - 1)) z = _
    rw [hvqm]
    rfl
  have hpG : psi (add (ρ.v r) (omega X0)) (argT (M.take (r + L)) τ (q - 1)) z ≤ G := by
    rw [← hoqm]
    exact mem_le_sumN hGlist (List.mem_map.mpr ⟨q - 1, hqbN, rfl⟩)
  have hV : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  have hvc0 : τ.v c0 = add (ρ.v r) (omega Y) := by
    rw [(hτ c0 (by rw [hNlen]; exact hc0x)).2]
    unfold vRhs
    rw [entry_take M 1 hc0x, entry_take M 2 hc0x, if_neg he1, if_neg he2,
      par_take M 1 c0 hc0x, hp1]
    change sf (add (τ.v r) (omega Y)) = add (ρ.v r) (omega Y)
    rw [hvr, sf_ot (isOT_add hV (isOT_omega hYot))]
  rw [hvc0]
  exact decp_term hV hXot hYot hGot hGY hpG

#print axioms decp_term
#print axioms decP_of_shape

end Ytosk.V3Main.SeedPF
