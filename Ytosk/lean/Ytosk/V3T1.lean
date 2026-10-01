/-
**3 行・t = 1・q ≠ r: 展開 M[n] の等式。**

N = M[n]（n ≥ 2）、P = M[n − 1]。x より前は M の値を D の上で fsD(·, ζ) に置き換え、x 以後は P の値を
1 写し分ずらした割り当て `glue M x ρ (shiftV ρP L) ζ` は N の等式を満たす（`cons_N_t1`）。
仮定は構造（`hpath` ほか、上げられることの一致 `hiu`・`hiux`）、写しが読む良い部分の v の一致 `hagree`、
D の枠の交換 `hF`。
-/
import Ytosk.V3Pre

namespace Ytosk

open T

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **The equations of `M[n]`** (`t = 1`, `q ≠ r`). -/
theorem cons_N_t1 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {Z : Nat → T} (hC : Cons M ρ) (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueZ M (r + L) ρ (shiftV ρP L) Z).v g = ρP.v g)
    (hF : ∀ i, i < r + L →
      (DepX M (r + L) true i → oRhs M (glueZ M (r + L) ρ (shiftV ρP L) Z) i = fsD (ρ.o i) (Z i)) ∧
      (DepX M (r + L) false i → vRhs M (glueZ M (r + L) ρ (shiftV ρP L) Z) i = fsD (ρ.v i) (Z i))) :
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) := by
  have hlN := len_N (d0 := d0) hlen hn
  intro i hi
  rcases Nat.lt_or_ge i (r + L) with h | h
  · exact cons_glue_lt (by omega) hC (sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux)
      (fun i hi _ m _ hm => reads_lt_x hlen hx2 hi hm) hF i h
  · have := cons_copy hlen hL hA hd0e hn hpath hz2 hCP hagree (i - (r + L)) (by omega)
    rw [show r + L + (i - (r + L)) = i by omega] at this
    exact this

end

end Ytosk
