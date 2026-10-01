/-
**M の構造の不変条件を種 S = seedOf M r d0 d1 に移す。**

S と M は最後の列 x だけが違う。x より前の子・値・bump は同じ（`seed_mem_lt`）。
4 つの局所的な性質（SibDec・Z1C・BumpE2・BumpLeaf）は、x が関わる場合だけ個別の仮定（`hlast`・`hpx`）で
片づく（`sibDec_seed` など）。その仮定を t ごとに示す:
- t ≥ 1（行 0 の親は M と同じ qp）: col S x ≤ col M x。bump になる場合は par1 の議論（qp = r）と Z1C で矛盾。
- t = 0（x は g = r の親の子になる）: g の M での最後の子は r で、col S x = col r。
-/
import Ytosk.V3InvSeed

namespace Ytosk

open T Classical

/-! ## 一般の移し替え -/

section
variable {M : Mat} {r d0 d1 : Nat} {x : Nat} (hx : x + 1 = M.length)
include hx

theorem seed_mem_lt {v e : Nat} (he : e < x) :
    e ∈ children (seedOf M r d0 d1) v ↔ e ∈ children M v := by
  rw [mem_children_iff, mem_children_iff, seed_len hx, seed_par_lt hx 0 he]

theorem seed_mem_x {v : Nat} :
    x ∈ children (seedOf M r d0 d1) v ↔ par (seedOf M r d0 d1) 0 x = some v := by
  rw [mem_children_iff, seed_len hx]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

theorem seed_mem_le {v e : Nat} (he : e ∈ children (seedOf M r d0 d1) v) : e ≤ x := by
  have := (mem_children he).2; rw [seed_len hx] at this; omega

theorem seed_bump_lt {p : Nat} (hp : p < x) : bump (seedOf M r d0 d1) p = bump M p := by
  unfold bump; rw [seed_entry_lt hx 0 hp, seed_entry_lt hx 1 hp]

theorem sibDec_seed (hSD : SibDec M)
    (hlast : ∀ p a, par (seedOf M r d0 d1) 0 x = some p → a ∈ children M p → a < x →
      (∀ e, a < e → e < x → e ∉ children M p) → colLe (col (seedOf M r d0 d1) x) (col M a)) :
    SibDec (seedOf M r d0 d1) := by
  intro p l1 l2 a b hch
  obtain ⟨hab, ha, hb, hno⟩ := split_consec (children_sorted _ p) hch
  have hbx := seed_mem_le hx hb
  have hax : a < x := by omega
  have haM := (seed_mem_lt hx hax).mp ha
  rw [seed_col_lt hx hax]
  rcases Nat.lt_or_ge b x with hbx' | hbx'
  · have hbM := (seed_mem_lt hx hbx').mp hb
    obtain ⟨l1', l2', h'⟩ := consec_split (children_sorted M p) haM hbM hab
      (fun e he hh => hno e ((seed_mem_lt hx (by omega)).mpr he) hh)
    rw [seed_col_lt hx hbx']
    exact hSD p l1' l2' a b h'
  · have hbe : b = x := by omega
    rw [hbe] at hb hno ⊢
    exact hlast p a ((seed_mem_x hx).mp hb) haM hax
      (fun e h1 h2 he => hno e ((seed_mem_lt hx h2).mpr he) ⟨h1, h2⟩)

theorem z1c_seed (hZ1 : Z1C M)
    (hlast : ∀ p, par (seedOf M r d0 d1) 0 x = some p → entry M 2 p = 1 →
      entry (seedOf M r d0 d1) 1 x ≤ entry M 1 p) :
    Z1C (seedOf M r d0 d1) := by
  intro p c h2 hc
  have hpc := (mem_children hc).1
  have hcx := seed_mem_le hx hc
  have hpx : p < x := by omega
  rw [seed_entry_lt hx 2 hpx] at h2
  rw [seed_entry_lt hx 1 hpx]
  rcases Nat.lt_or_ge c x with h | h
  · rw [seed_entry_lt hx 1 h]; exact hZ1 p c h2 ((seed_mem_lt hx h).mp hc)
  · have hce : c = x := by omega
    rw [hce] at hc ⊢
    exact hlast p ((seed_mem_x hx).mp hc) h2

theorem bumpE2_seed (hBE : BumpE2 M)
    (hlast : ∀ p, par (seedOf M r d0 d1) 0 x = some p → col (seedOf M r d0 d1) x = bump M p →
      entry M 2 p = 1) :
    BumpE2 (seedOf M r d0 d1) := by
  intro p c hc hb
  have hpc := (mem_children hc).1
  have hcx := seed_mem_le hx hc
  have hpx : p < x := by omega
  rw [seed_entry_lt hx 2 hpx, ]
  rw [seed_bump_lt hx hpx] at hb
  rcases Nat.lt_or_ge c x with h | h
  · rw [seed_col_lt hx h] at hb; exact hBE p c ((seed_mem_lt hx h).mp hc) hb
  · have hce : c = x := by omega
    rw [hce] at hc hb
    exact hlast p ((seed_mem_x hx).mp hc) hb

theorem bumpLeaf_seed (hBL : BumpLeaf M)
    (hnoBL : ∀ K J, J ∈ children (seedOf M r d0 d1) K →
      col (seedOf M r d0 d1) J = bump (seedOf M r d0 d1) K → x ∈ children (seedOf M r d0 d1) J →
      entry (seedOf M r d0 d1) 1 K ≤ entry (seedOf M r d0 d1) 1 x → False)
    (hpx : ∀ k j c, j ∈ children M k → col M j = bump M k → c ∈ children M j →
      entry M 1 k ≤ entry M 1 c → c < x →
      par (seedOf M r d0 d1) 0 x ≠ some c ∧ par (seedOf M r d0 d1) 0 x ≠ some j ∧
        par (seedOf M r d0 d1) 0 x ≠ some k) :
    BumpLeaf (seedOf M r d0 d1) := by
  intro k j c hj hb hc h1
  have hjc := (mem_children hc).1
  have hkj := (mem_children hj).1
  have hcx := seed_mem_le hx hc
  rcases Nat.lt_or_ge c x with hcx' | hcx'
  · have hjx : j < x := by omega
    have hkx : k < x := by omega
    have hjM := (seed_mem_lt hx hjx).mp hj
    have hcM := (seed_mem_lt hx hcx').mp hc
    rw [seed_col_lt hx hjx, seed_bump_lt hx hkx] at hb
    rw [seed_entry_lt hx 1 hkx, seed_entry_lt hx 1 hcx'] at h1
    obtain ⟨e2, hleaf, hlj, hlk⟩ := hBL k j c hjM hb hcM h1
    obtain ⟨nc, nj, nk⟩ := hpx k j c hjM hb hcM h1 hcx'
    refine ⟨by rw [seed_entry_lt hx 2 hcx']; exact e2, ?_, ?_, ?_⟩
    · apply nil_of_none
      intro e he
      have hex := seed_mem_le hx he
      rcases Nat.lt_or_ge e x with h | h
      · rw [seed_mem_lt hx h, hleaf] at he; simp at he
      · have hee : e = x := by omega
        rw [hee, seed_mem_x hx] at he; exact nc he
    · apply getLast_of (children_sorted _ _) hc
      intro e he
      have hex := seed_mem_le hx he
      rcases Nat.lt_or_ge e x with h | h
      · exact last_le (children_sorted M j) hlj e ((seed_mem_lt hx h).mp he)
      · have hee : e = x := by omega
        rw [hee, seed_mem_x hx] at he; exact absurd he nj
    · apply getLast_of (children_sorted _ _) hj
      intro e he
      have hex := seed_mem_le hx he
      rcases Nat.lt_or_ge e x with h | h
      · exact last_le (children_sorted M k) hlk e ((seed_mem_lt hx h).mp he)
      · have hee : e = x := by omega
        rw [hee, seed_mem_x hx] at he; exact absurd he nk
  · have hce : c = x := by omega
    rw [hce] at hc h1
    exact (hnoBL k j hj hb hc h1).elim

end

end Ytosk
