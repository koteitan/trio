/-
**M の 4 つの局所的な性質（SibDec・Z1C・BumpE2・BumpLeaf）から展開 gexp M r (x - r) d0 d1 n（n ≥ 1）の同じ性質。**

種 S = seedOf M r d0 d1 を経由する（`loc_of_seed`: Seed・S の性質・noBL・nbs から）。t ごとに:
- t = 1（r = par1 x, d1 = 0）: col S x = (行 0 は x, 行 1 は r)。bump になると par1 の議論で親 = r、Z1C で矛盾。
- t = 2（r = par2 x, 行 2 は 0 と 1）: col S x の行 2 は 0。x が孫になると BumpLeaf M で行 2 が 0 になり矛盾。
- t = 0（r = par0 x, d0 = d1 = 0）: x は g = r の親の子になる。g の x より前の最後の子は r。
-/
import Ytosk.V3InvSeed2

namespace Ytosk

open T Classical

/-- The four local structural properties. -/
def LocInv (M : Mat) : Prop := SibDec M ∧ Z1C M ∧ BumpE2 M ∧ BumpLeaf M

theorem seed_col_x {M : Mat} {r d0 d1 x : Nat} (hx : x + 1 = M.length) :
    col (seedOf M r d0 d1) x = (entry M 0 r + d0, entry M 1 r + d1, entry M 2 r) := seed_getD_x hx

theorem colLe_refl (a : Nat × Nat × Nat) : colLe a a := by unfold colLe; omega

/-- **From the seed to the expansion.** -/
theorem loc_of_seed {M : Mat} {r d0 d1 x n : Nat} (hx : x + 1 = M.length) (hrx : r < x)
    (hS : Seed (seedOf M r d0 d1) r (x - r) d0 d1) (hL : LocInv (seedOf M r d0 d1))
    (hnoBL : ∀ K J, J ∈ children (seedOf M r d0 d1) K →
      col (seedOf M r d0 d1) J = bump (seedOf M r d0 d1) K → x ∈ children (seedOf M r d0 d1) J →
      entry (seedOf M r d0 d1) 1 K ≤ entry (seedOf M r d0 d1) 1 x → False)
    (hnbs : Anc0 (seedOf M r d0 d1) r x → ∀ P, par (seedOf M r d0 d1) 0 x = some P →
      col (seedOf M r d0 d1) x ≠ bump (seedOf M r d0 d1) P)
    (hn : 1 ≤ n) : LocInv (TRIO.gexp M r (x - r) d0 d1 n) := by
  have e : r + (x - r) = x := by omega
  have hc : TRIO.gexp (seedOf M r d0 d1) r (x - r) d0 d1 n = TRIO.gexp M r (x - r) d0 d1 n :=
    gexp_congr (by rw [seed_len hx]; omega) (by omega) (fun j hj => seed_getD_lt hx (by omega))
  rw [← hc]
  exact ⟨hS.sibDec hL.1 hn, hS.z1c hL.2.1 hn, hS.bumpE2 hL.2.2.1 hn,
    hS.bumpLeaf hL.2.2.2 (by rw [e]; exact hnoBL) (by rw [e]; exact hnbs) hn⟩

/-! ## t ≥ 1: 行 0 の親が変わらない -/

section
variable {M : Mat} {r d0 d1 : Nat} {x : Nat} (hx : x + 1 = M.length)
include hx

theorem seed_seed_ge1 (hrx : r < x) (hA : Anc0 M r x) (he0 : entry M 0 r + d0 = entry M 0 x)
    (hle : 0 < d1 → TRIO.le1 (seedOf M r d0 d1) r x) : Seed (seedOf M r d0 d1) r (x - r) d0 d1 := by
  have e : r + (x - r) = x := by omega
  refine ⟨by rw [seed_len hx]; omega, by omega, fun q hq => ?_, ?_, ?_⟩
  · exact (seed_anc0_lt hx (by omega)).mpr (anc_between hA (r + q) (by omega) (by omega))
  · rw [e, seed_col_x hx, seed_entry_lt hx 0 hrx, seed_entry_lt hx 1 hrx, seed_entry_lt hx 2 hrx]
  · left
    rw [e]
    refine ⟨?_, hle⟩
    obtain ⟨p, hp, hAp⟩ := anc0_par_exists hA (by omega)
    have hpx := par_lt M 0 x p hp
    exact Anc0.step (by rw [seed_par_x hx he0]; exact hp) ((seed_anc0_lt hx hpx).mpr hAp)

theorem seed_loc_ge1 (hSD : SibDec M) (hZ1 : Z1C M) (hBE : BumpE2 M) (hBL : BumpLeaf M)
    (he0 : entry M 0 r + d0 = entry M 0 x)
    (hcol : colLe (col (seedOf M r d0 d1) x) (col M x))
    (he1 : entry (seedOf M r d0 d1) 1 x ≤ entry M 1 x)
    (hnbs : ∀ P, par M 0 x = some P → col (seedOf M r d0 d1) x ≠ bump M P)
    (hnoBL : ∀ K J, J ∈ children M K → col M J = bump M K → par M 0 x = some J →
      entry M 1 K ≤ entry (seedOf M r d0 d1) 1 x → False) :
    LocInv (seedOf M r d0 d1) ∧
    (∀ K J, J ∈ children (seedOf M r d0 d1) K →
      col (seedOf M r d0 d1) J = bump (seedOf M r d0 d1) K → x ∈ children (seedOf M r d0 d1) J →
      entry (seedOf M r d0 d1) 1 K ≤ entry (seedOf M r d0 d1) 1 x → False) ∧
    (∀ P, par (seedOf M r d0 d1) 0 x = some P → col (seedOf M r d0 d1) x ≠ bump (seedOf M r d0 d1) P) := by
  have hpx := seed_par_x (d1 := d1) hx he0
  have hxM : x < M.length := by omega
  have hnoS : ∀ K J, J ∈ children (seedOf M r d0 d1) K →
      col (seedOf M r d0 d1) J = bump (seedOf M r d0 d1) K → x ∈ children (seedOf M r d0 d1) J →
      entry (seedOf M r d0 d1) 1 K ≤ entry (seedOf M r d0 d1) 1 x → False := by
    intro K J hJ hb hxJ h1
    rw [seed_mem_x hx, hpx] at hxJ
    have hJx := par_lt M 0 x J hxJ
    have hKx : K < x := by have := (mem_children hJ).1; omega
    rw [seed_mem_lt hx hJx] at hJ
    rw [seed_col_lt hx hJx, seed_bump_lt hx hKx] at hb
    rw [seed_entry_lt hx 1 hKx] at h1
    exact hnoBL K J hJ hb hxJ h1
  refine ⟨⟨sibDec_seed hx hSD ?_, z1c_seed hx hZ1 ?_, bumpE2_seed hx hBE ?_,
    bumpLeaf_seed hx hBL hnoS ?_⟩, hnoS, ?_⟩
  · intro p a hp ha hax hno
    rw [hpx] at hp
    have hxc : x ∈ children M p := mem_children_iff.mpr ⟨hxM, hp⟩
    obtain ⟨l1, l2, h⟩ := consec_split (children_sorted M p) ha hxc hax
      (fun e he hh => hno e hh.1 hh.2 he)
    exact colLe_trans hcol (hSD p l1 l2 a x h)
  · intro p hp h2
    rw [hpx] at hp
    exact le_trans he1 (hZ1 p x h2 (mem_children_iff.mpr ⟨hxM, hp⟩))
  · intro p hp hb
    rw [hpx] at hp
    exact absurd hb (hnbs p hp)
  · intro k j c hj hb hc h1 hcx
    rw [hpx]
    obtain ⟨_, hleaf, hlj, hlk⟩ := hBL k j c hj hb hc h1
    have hjc := (mem_children hc).1
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have hxc : x ∈ children M c := mem_children_iff.mpr ⟨hxM, h⟩
      rw [hleaf] at hxc; simp at hxc
    · have := last_le (children_sorted M j) hlj x (mem_children_iff.mpr ⟨hxM, h⟩); omega
    · have := last_le (children_sorted M k) hlk x (mem_children_iff.mpr ⟨hxM, h⟩); omega
  · intro P hP
    rw [hpx] at hP
    have hPx := par_lt M 0 x P hP
    rw [seed_bump_lt hx hPx]
    exact hnbs P hP

end

/-! ## t = 1 -/

/-- **The row-1 parent is the row-0 parent when the latter is below in row 1.** -/
theorem par1_eq_par0 {M : Mat} {x r P : Nat} (h1 : par M 1 x = some r) (hp : par M 0 x = some P)
    (hlt : entry M 1 P < entry M 1 x) : r = P := by
  have hA := anc0_of_par M 1 r x h1
  have hrx := par_lt M 1 x r h1
  have hrP := (anc0_par hA (by omega) hp).le
  by_contra hne
  have := par1_between h1 P (Anc0.step hp (Anc0.refl P)) (by omega)
  omega

theorem par1_not_z1 {M : Mat} {x r : Nat} (hZ1 : Z1C M) (hxM : x < M.length) (h1 : par M 1 x = some r)
    (hp : par M 0 x = some r) : entry M 2 r ≠ 1 := by
  intro h2
  have := hZ1 r x h2 (mem_children_iff.mpr ⟨hxM, hp⟩)
  have := par1_entry_lt h1
  omega

theorem colLe_entries {a0 a1 a2 b0 b1 b2 : Nat} (h0 : a0 = b0) (h1 : a1 ≤ b1) (h2 : a1 = b1 → a2 ≤ b2) :
    colLe (a0, a1, a2) (b0, b1, b2) := by
  unfold colLe
  simp only
  rcases Nat.lt_or_ge a1 b1 with h | h
  · omega
  · have := h2 (by omega); omega

theorem bump_eq {a : Nat × Nat × Nat} {M : Mat} {P : Nat} (h : a = bump M P) :
    a.1 = entry M 0 P + 1 ∧ a.2.1 = entry M 1 P ∧ a.2.2 = 1 := by
  subst h; exact ⟨rfl, rfl, rfl⟩

theorem loc_t1 {M : Mat} {r x n : Nat} (hx : x + 1 = M.length) (hL : LocInv M)
    (h1 : par M 1 x = some r) (hn : 1 ≤ n) :
    LocInv (TRIO.gexp M r (x - r) (entry M 0 x - entry M 0 r) 0 n) := by
  obtain ⟨hSD, hZ1, hBE, hBL⟩ := hL
  have hA := anc0_of_par M 1 r x h1
  have hrx := par_lt M 1 x r h1
  have hxM : x < M.length := by omega
  have h0lt := anc0_e0_lt hA (by omega)
  have h1lt := par1_entry_lt h1
  have he0 : entry M 0 r + (entry M 0 x - entry M 0 r) = entry M 0 x := by omega
  have hcx := seed_col_x (r := r) (d0 := entry M 0 x - entry M 0 r) (d1 := 0) hx
  obtain ⟨hLS, hnoS, hnbS⟩ := seed_loc_ge1 hx hSD hZ1 hBE hBL he0
    (by rw [hcx, col_eq_entries M x]; exact colLe_entries he0 (by omega) (fun h => by omega))
    (by rw [seed_e1x hx]; omega)
    (fun P hP hb => by
      rw [hcx] at hb
      obtain ⟨_, hb1, hb2⟩ := bump_eq hb
      simp only at hb1 hb2
      have hrP := par1_eq_par0 h1 hP (by omega)
      subst hrP
      exact par1_not_z1 hZ1 hxM h1 hP hb2)
    (fun K J hJ hb hp hle => by
      obtain ⟨_, hb1, hb2⟩ := bump_eq hb
      rw [col_eq_entries] at hb1 hb2
      simp only at hb1 hb2
      rw [seed_e1x hx] at hle
      have hrJ := par1_eq_par0 h1 hp (by omega)
      subst hrJ
      exact par1_not_z1 hZ1 hxM h1 hp hb2)
  exact loc_of_seed hx hrx (seed_seed_ge1 hx hrx hA he0 (fun h => absurd h (by omega))) hLS
    (fun K J a b c d => hnoS K J a b c d) (fun _ P hP => hnbS P hP) hn

/-! ## t = 2 -/

theorem loc_t2 {M : Mat} {r x n : Nat} (hx : x + 1 = M.length) (hL : LocInv M) (hZ2 : Z2 M)
    (h2 : par M 2 x = some r) (hn : 1 ≤ n) :
    LocInv (TRIO.gexp M r (x - r) (entry M 0 x - entry M 0 r) (entry M 1 x - entry M 1 r) n) := by
  obtain ⟨hSD, hZ1, hBE, hBL⟩ := hL
  have hxM : x < M.length := by omega
  obtain ⟨_, _, hrx, he2, hle, _⟩ := (par2_iff M hxM).mp h2
  have hA := anc0_of_par M 2 r x h2
  have hx2 := hZ2 x
  have he2' : entry M 2 r < entry M 2 x := he2
  have h0lt := anc0_e0_lt hA (by omega)
  have h1lt : entry M 1 r < entry M 1 x :=
    (le1_window hxM hA).mp hle x hA (Anc0.refl x) (by omega)
  have he0 : entry M 0 r + (entry M 0 x - entry M 0 r) = entry M 0 x := by omega
  have he1 : entry M 1 r + (entry M 1 x - entry M 1 r) = entry M 1 x := by omega
  have hcx := seed_col_x (r := r) (d0 := entry M 0 x - entry M 0 r)
    (d1 := entry M 1 x - entry M 1 r) hx
  obtain ⟨hLS, hnoS, hnbS⟩ := seed_loc_ge1 hx hSD hZ1 hBE hBL he0
    (by rw [hcx, col_eq_entries M x]; exact colLe_entries he0 (by omega) (fun _ => by omega))
    (by rw [seed_e1x hx]; omega)
    (fun P _ hb => by
      rw [hcx] at hb
      obtain ⟨_, _, hb2⟩ := bump_eq hb
      simp only at hb2; omega)
    (fun K J hJ hb hp hle => by
      rw [seed_e1x hx, he1] at hle
      have := (hBL K J x hJ hb (mem_children_iff.mpr ⟨hxM, hp⟩) hle).1
      omega)
  refine loc_of_seed hx hrx (seed_seed_ge1 hx hrx hA he0 (fun _ => ?_)) hLS
    (fun K J a b c d => hnoS K J a b c d) (fun _ P hP => hnbS P hP) hn
  refine TRIO.le1_of_agree_last (by rw [seed_len hx]; omega) hxM
    (fun j hj => seed_getD_lt hx hj) ?_ ?_ hle
  · rw [seed_getD_x hx]; simp only; rw [← entry0_getD]; exact he0
  · rw [seed_getD_x hx]; simp only; rw [← entry1_getD]; exact he1

end Ytosk
