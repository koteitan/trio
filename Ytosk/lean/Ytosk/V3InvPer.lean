/-
**周期的な種 S からの展開 N = gexp S r L d0 d1 n の構造の不変条件。**

S の最後の列 s = r + L は、展開でそこに来るコピーの根の列（col s = col r + (d0, d1, 0)）。
すると N の親子の組はすべて、S の親子の組をブロック単位でずらしたもの（`par0N_blk`・`par0N_root`）。
列は行 0 が一様に d0 ずつ、行 1 は le1 S r のガードつきで d1 ずつずれる（`e0N_blk`・`e1N_blk`）。
ガードの窓の性質（`le1_window`: le1 S r X ⇔ 道 (r, X] の行 1 が r の行 1 より大きい）から、
子・兄弟のガードの補題（`guard_par`・`guard_up`・`guard_sib`）。
-/
import Ytosk.V3InvPsi

namespace Ytosk

open T

/-! ## 行 0 の祖先と trio 本体の nextrel0 の鎖 -/

theorem rtg0_of_anc0 {M : Mat} {a b : Nat} (h : Anc0 M a b) (hb : b < M.length) :
    Relation.ReflTransGen (TRIO.nextrel0 M) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @step b c hp hA ih =>
    have hbc := par_lt M 0 c b hp
    exact Relation.ReflTransGen.tail (ih (by omega)) ((par0_iff M hb).mp hp)

theorem anc0_of_rtg0 {M : Mat} {a b : Nat} (h : Relation.ReflTransGen (TRIO.nextrel0 M) a b) :
    Anc0 M a b := by
  induction h with
  | refl => exact Anc0.refl _
  | @tail b c _ hbc ih => exact Anc0.step ((par0_iff M hbc.2.1).mpr hbc) ih

/-! ## ガードの窓 -/

/-- **The window of the guard**: `r` is on the row-1 chain of a descendant `b` iff every column of the
path `(r, b]` has row 1 above that of `r`. -/
theorem le1_window {M : Mat} {r b : Nat} (hb : b < M.length) (hA : Anc0 M r b) :
    TRIO.le1 M r b ↔ ∀ y, Anc0 M r y → Anc0 M y b → y ≠ r → entry M 1 r < entry M 1 y := by
  rw [TRIO.le1_iff_chain_window hb (rtg0_of_anc0 hA hb)]
  constructor
  · intro h y h1 h2 h3
    exact h y (rtg0_of_anc0 h1 (by have := h2.le; omega)) (rtg0_of_anc0 h2 hb) h3
  · intro h y h1 h2 h3
    exact h y (anc0_of_rtg0 h1) (anc0_of_rtg0 h2) h3

/-- **The guard goes up to the parent.** -/
theorem guard_par {M : Mat} {r P C : Nat} (hrP : Anc0 M r P) (hp : par M 0 C = some P)
    (hC : C < M.length) (hg : TRIO.le1 M r C) : TRIO.le1 M r P := by
  have hPC := par_lt M 0 C P hp
  have hrC : Anc0 M r C := Anc0.step hp hrP
  rw [le1_window hC hrC] at hg
  rw [le1_window (by omega) hrP]
  intro y h1 h2 h3
  exact hg y h1 (Anc0.step hp h2) h3

/-- **The guard goes down to a child with a larger row 1.** -/
theorem guard_up {M : Mat} {r P C : Nat} (hrP : Anc0 M r P) (hp : par M 0 C = some P)
    (hC : C < M.length) (hg : TRIO.le1 M r P) (h1 : entry M 1 P < entry M 1 C) : TRIO.le1 M r C := by
  have hPC := par_lt M 0 C P hp
  have hrC : Anc0 M r C := Anc0.step hp hrP
  have hgP := (le1_window (by omega) hrP).mp hg
  rw [le1_window hC hrC]
  intro y hy1 hy2 hy3
  by_cases hyC : y = C
  · subst hyC
    by_cases hPr : P = r
    · subst hPr; exact h1
    · exact lt_trans (hgP P hrP (Anc0.refl P) hPr) h1
  · exact hgP y hy1 (anc0_par hy2 hyC hp) hy3

/-- **The guard of a sibling**: a sibling with row 1 at least that of a guarded sibling is guarded. -/
theorem guard_sib {M : Mat} {r P C D : Nat} (hrP : Anc0 M r P) (hpC : par M 0 C = some P)
    (hpD : par M 0 D = some P) (hC : C < M.length) (hD : D < M.length) (hg : TRIO.le1 M r D)
    (h1 : entry M 1 D ≤ entry M 1 C) : TRIO.le1 M r C := by
  have hrC : Anc0 M r C := Anc0.step hpC hrP
  have hrD : Anc0 M r D := Anc0.step hpD hrP
  have hPD := par_lt M 0 D P hpD
  have hgD := (le1_window hD hrD).mp hg
  rw [le1_window hC hrC]
  intro y hy1 hy2 hy3
  by_cases hyC : y = C
  · subst hyC
    exact lt_of_lt_of_le (hgD D hrD (Anc0.refl D) (by
      intro h; subst h; have := par_lt M 0 D P hpD; have := hrP.le; omega)) h1
  · exact hgD y hy1 (Anc0.step hpD (anc0_par hy2 hyC hpC)) hy3

/-! ## N の列と行 0 の親 -/

section N
open Classical
variable {S : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = S.length) (hL : 0 < L)
include hlen

theorem lenN : (TRIO.gexp S r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen

theorem getDN_blk {c q : Nat} (hc : c < n) (hq : q < L) :
    (TRIO.gexp S r L d0 d1 n).getD (r + (c * L + q)) (0, 0, 0) =
      (entry S 0 (r + q) + c * d0, entry S 1 (r + q) + (if TRIO.le1 S r (r + q) then c * d1 else 0),
        entry S 2 (r + q)) :=
  TRIO.gexp_getD_mir hlen hc hq

theorem e0N_blk {c q : Nat} (hc : c < n) (hq : q < L) :
    entry (TRIO.gexp S r L d0 d1 n) 0 (r + (c * L + q)) = entry S 0 (r + q) + c * d0 := by
  rw [entry0_getD, getDN_blk hlen hc hq]

theorem e1N_blk {c q : Nat} (hc : c < n) (hq : q < L) :
    entry (TRIO.gexp S r L d0 d1 n) 1 (r + (c * L + q)) =
      entry S 1 (r + q) + (if TRIO.le1 S r (r + q) then c * d1 else 0) := by
  rw [entry1_getD, getDN_blk hlen hc hq]

theorem e2N_blk {c q : Nat} (hc : c < n) (hq : q < L) :
    entry (TRIO.gexp S r L d0 d1 n) 2 (r + (c * L + q)) = entry S 2 (r + q) := by
  rw [entry2_getD, getDN_blk hlen hc hq]

theorem eN_low (y : Nat) {i : Nat} (hi : i < r) :
    entry (TRIO.gexp S r L d0 d1 n) y i = entry S y i := by
  unfold entry; rw [TRIO.gexp_getD_low hlen hi]

theorem colN_low {i : Nat} (hi : i < r) : col (TRIO.gexp S r L d0 d1 n) i = col S i := by
  unfold col; rw [TRIO.gexp_getD_low hlen hi]

/-- Before `s`, the parents are those of `S`. -/
theorem par0N_low (hn : 1 ≤ n) {i : Nat} (hi : i < r + L) :
    par (TRIO.gexp S r L d0 d1 n) 0 i = par S 0 i := par_gexp_pre hlen hn 0 hi

omit hlen in
theorem par_ge_root {S : Mat} {r q P : Nat} (hB : Anc0 S r (r + q)) (hq : 0 < q)
    (hp : par S 0 (r + q) = some P) : Anc0 S r P :=
  anc0_par hB (by omega) hp

/-- **The parent inside a block.** -/
theorem par0N_blk (hB : ∀ q, q < L → Anc0 S r (r + q)) {c q P : Nat} (hc : c < n) (hq0 : 0 < q)
    (hq : q < L) (hp : par S 0 (r + q) = some P) :
    par (TRIO.gexp S r L d0 d1 n) 0 (r + (c * L + q)) = some (P + c * L) := by
  have hrP := (par_ge_root (hB q hq) hq0 hp).le
  have hPq := par_lt S 0 _ _ hp
  have hp' : par S 0 (r + q) = some (r + (P - r)) := by rw [hp]; congr 1; omega
  have := par0_gexp_mir (d0 := d0) (d1 := d1) hlen hc hq hp'
  rw [this]; congr 1; omega

/-- **The parent of a copy root** (`t ≥ 1`: the root hangs below the copy of the parent of `s`). -/
theorem par0N_root {c P : Nat} (hc1 : 1 ≤ c) (hc : c < n) (hrP : Anc0 S r P)
    (hps : par S 0 (r + L) = some P) (hd0e : entry S 0 (r + L) = entry S 0 r + d0) :
    par (TRIO.gexp S r L d0 d1 n) 0 (r + c * L) = some (P + (c - 1) * L) := by
  have hPs := par_lt S 0 _ _ hps
  have hrP' := hrP.le
  have hps' : par S 0 (r + L) = some (r + (P - r)) := by rw [hps]; congr 1; omega
  have := par0_gexp_root (d1 := d1) hlen hc hc1 (by omega) hd0e hps'
  rw [show r + (c * L + 0) = r + c * L by omega] at this
  rw [this]; congr 1; omega

include hL in
/-- Row 0 of the copies is at least that of `r`. -/
theorem e0N_ge (hB : ∀ q, q < L → Anc0 S r (r + q)) {p : Nat} (hp0 : r ≤ p) (hp : p < r + n * L) :
    entry S 0 r ≤ entry (TRIO.gexp S r L d0 d1 n) 0 p := by
  obtain ⟨c, q, hc, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL hp0 hp
  rw [e0N_blk hlen hc hq]
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp
  · have := anc0_e0_lt (hB q hq) (by omega); omega

include hL in
/-- **The parent of a copy root** (`t = 0`, `d0 = 0`: the roots are siblings of `r`). -/
theorem par0N_root0 (hB : ∀ q, q < L → Anc0 S r (r + q)) (hd0 : d0 = 0) {c : Nat} (hc : c < n) :
    par (TRIO.gexp S r L d0 d1 n) 0 (r + c * L) = par S 0 r := by
  subst hd0
  have hlN := lenN (d0 := 0) (d1 := d1) (n := n) hlen
  have hrc : r + c * L < r + n * L := by
    have := Nat.mul_lt_mul_of_pos_right hc hL; omega
  have he : entry (TRIO.gexp S r L 0 d1 n) 0 (r + c * L) = entry S 0 r := by
    have := e0N_blk (d0 := 0) (d1 := d1) hlen hc hL (q := 0)
    simpa using this
  cases hg : par S 0 r with
  | some g =>
    obtain ⟨hgr, hlt, hbet⟩ := (par0_spec S).mp hg
    rw [par0_spec]
    refine ⟨by omega, by rw [he, eN_low hlen 0 hgr]; exact hlt, fun j h1 h2 => ?_⟩
    rw [he]
    rcases Nat.lt_or_ge j r with hj | hj
    · rw [eN_low hlen 0 hj]; exact hbet j h1 hj
    · exact e0N_ge (d0 := 0) (d1 := d1) (n := n) hlen hL hB hj (by omega)
  | none =>
    by_contra hne
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨har, hlt, hbet⟩ := (par0_spec _).mp ha
    rw [he] at hlt
    rcases Nat.lt_or_ge a r with h | h
    · rw [eN_low hlen 0 h] at hlt
      obtain ⟨g, hg'⟩ := par0_some_of (M := S) (show a < r by omega) hlt
      rw [hg] at hg'; cases hg'
    · have := e0N_ge (d0 := 0) (d1 := d1) (n := n) hlen hL hB h (by omega); omega

end N

end Ytosk
