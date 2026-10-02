/-
**t = 2・q ≠ r の構造の事実**（`T2QN` の xb・qb・e2pq・clq・clpq）を SInvX ∧ RowJ から。

x = r + L（最後の列）、r = P_2 x、q = r + qp = P_0 x（q ≠ r）、pq = P_0 q。
- xb: P_1 x = r ≠ q なので e1 x ≤ e1 q（`par1_between`）、RowJ で e1 q ≤ e1 x。R0P・Z2 と合わせて col x = bump q。
- e2 q = 1（BumpE2）。qb: col q = bump pq なら BumpLeaf で e2 x = 0 になり矛盾。
- e2pq: e2 pq = 1 なら Z1C と RowJ で e1 q = e1 pq、col q = bump pq になり矛盾。
- clq: x は q の最後の子で bump、e2 q = 1 なので q の子はすべて bump（`all_bump_of_last`）。
- clpq: pq + 1 は pq の最初の子で数えられる。bump なら兄弟の非増加で col q = bump pq。
  上げの先で topped なら UAT で upg pq = pq + 1、P_1 pq = m で e0 m = e0 pq となり矛盾。
-/
import Ytosk.V3InvJ
import Ytosk.V3DropAsm
import Ytosk.V3Chg
import Ytosk.V3ChgS

namespace Ytosk

open T Classical

theorem t2_qn_struct {M : Mat} {r L qp pq : Nat} (hX : SInvX M) (hJ : RowJ M)
    (hlen : r + L + 1 = M.length) (h2 : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some (r + qp)) (hqp : 0 < qp) (hpq : par M 0 (r + qp) = some pq) :
    col M (r + L) = bump M (r + qp) ∧ col M (r + qp) ≠ bump M pq ∧ entry M 2 pq = 0 ∧
      CL M (r + qp) = [] ∧ CL M pq ≠ [] := by
  have hR0 := hX.r0p
  have hZ2 := hX.z2
  obtain ⟨hSD, hZ1, hBE, hBL⟩ := hX.loc
  have hUAT := hX.toSInv.uat
  have hxM : r + L < M.length := by omega
  have hqx := par_lt M 0 _ _ hq
  have hpqq := par_lt M 0 _ _ hpq
  -- row 2 of x
  have he2x : entry M 2 (r + L) = 1 := by
    obtain ⟨_, _, _, he2, _⟩ := (par2_iff M hxM).mp h2
    have : entry M 2 r < entry M 2 (r + L) := he2
    have := hZ2 (r + L); omega
  have h1 := par1_of_par2 hZ2 hZ1 hxM h2
  -- row 1 of q equals row 1 of x
  have hAqx : Anc0 M (r + qp) (r + L) := Anc0.step hq (Anc0.refl _)
  have hge := par1_between h1 (r + qp) hAqx (by omega)
  have hle := hJ (r + L) (r + qp) (by omega) hq
  have he0x := hR0 _ _ hq
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨hxM, hq⟩
  -- xb
  have hxb : col M (r + L) = bump M (r + qp) := by
    rw [col_eq_entries]; unfold bump; rw [he0x, he2x, show entry M 1 (r + L) = entry M 1 (r + qp) by omega]
  have he2q : entry M 2 (r + qp) = 1 := hBE _ _ hxq hxb
  have hqM : r + qp < M.length := by omega
  have hqpq : r + qp ∈ children M pq := mem_children_iff.mpr ⟨hqM, hpq⟩
  have hJq := hJ (r + qp) pq (by omega) hpq
  have he0q := hR0 _ _ hpq
  -- qb
  have hqb : col M (r + qp) ≠ bump M pq := by
    intro hb
    have := (hBL pq (r + qp) (r + L) hqpq hb hxq (by omega)).1
    omega
  -- e2pq
  have he2pq : entry M 2 pq = 0 := by
    by_contra hne
    have h1pq : entry M 2 pq = 1 := by have := hZ2 pq; omega
    have := hZ1 pq (r + qp) h1pq hqpq
    apply hqb
    rw [col_eq_entries]; unfold bump; rw [he0q, he2q, show entry M 1 (r + qp) = entry M 1 pq by omega]
  refine ⟨hxb, hqb, he2pq, ?_, ?_⟩
  -- clq
  · have hall := all_bump_of_last hR0 hZ2 hSD hZ1 he2q (children_split_x hlen hxq) hxb
    unfold CL
    rw [List.filter_eq_nil_iff]
    intro c hc hcnt
    exact (of_decide_eq_true hcnt).1 (hall c hc)
  -- clpq
  · have hApq : Anc0 M pq (r + qp) := Anc0.step hpq (Anc0.refl _)
    have hA1 : Anc0 M pq (pq + 1) := anc_between hApq (pq + 1) (by omega) (by omega)
    obtain ⟨p1, hp1⟩ := par0_of_anc hA1 (by omega)
    have hp1ge := par0_ge_of_anc hApq (show pq < pq + 1 by omega) (by omega) hp1
    have hp1lt := par_lt M 0 _ _ hp1
    have hp1e : p1 = pq := by omega
    rw [hp1e] at hp1
    have hc1 : pq + 1 ∈ children M pq := mem_children_iff.mpr ⟨by omega, hp1⟩
    have hnb : col M (pq + 1) ≠ bump M pq := by
      intro hb
      by_cases he : pq + 1 = r + qp
      · rw [he] at hb; exact hqb hb
      · obtain ⟨l1, l2, hch⟩ := List.append_of_mem hc1
        have hql2 : r + qp ∈ l2 := by
          have hmem : r + qp ∈ l1 ++ (pq + 1) :: l2 := by rw [← hch]; exact hqpq
          rcases List.mem_append.mp hmem with h | h
          · have hs := children_sorted M pq
            rw [hch, List.pairwise_append] at hs
            have := hs.2.2 _ h (pq + 1) (by simp)
            omega
          · rcases List.mem_cons.mp h with h | h
            · exact absurd h.symm he
            · exact h
        have hcl := sib_le hSD l2 l1 (pq + 1) hch (r + qp) hql2
        rw [hb] at hcl
        unfold colLe bump at hcl
        have e0 : (col M (r + qp)).1 = entry M 0 (r + qp) := rfl
        have e1 : (col M (r + qp)).2.1 = entry M 1 (r + qp) := rfl
        have e2 : (col M (r + qp)).2.2 = entry M 2 (r + qp) := rfl
        simp only at hcl
        rw [e0, e1, e2] at hcl
        apply hqb
        rw [col_eq_entries]; unfold bump
        rw [he0q, he2q, show entry M 1 (r + qp) = entry M 1 pq by omega]
    have hnu : ¬ (isUpg M (pq + 1) = true ∧ topped M (pq + 1) = true) := by
      rintro ⟨hu, ht⟩
      unfold isUpg at hu
      obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hu
      have hk' : upg M k = some (pq + 1) := of_decide_eq_true hk
      have hkq : pq + 1 = k + 1 := by
        by_contra hne
        have := hUAT k (pq + 1) hk' hne
        rw [ht] at this; cases this
      have hkpq : k = pq := by omega
      rw [hkpq] at hk'
      obtain ⟨m, hm, _, hcol, _⟩ := upg_spec hk'
      have hmA := anc0_of_par M 1 m pq hm
      have hmlt := par_lt M 1 pq m hm
      have := anc0_e0_lt hmA (by omega)
      have h0 : entry M 0 (pq + 1) = entry M 0 m + 1 := by
        rw [col_eq_entries] at hcol; exact (Prod.mk.inj hcol).1
      have := hR0 _ _ hp1
      omega
    intro hnil
    have hin : pq + 1 ∈ CL M pq := by
      unfold CL; rw [List.mem_filter]
      exact ⟨hc1, decide_eq_true ⟨hnb, hnu⟩⟩
    rw [hnil] at hin; simp at hin

end Ytosk
