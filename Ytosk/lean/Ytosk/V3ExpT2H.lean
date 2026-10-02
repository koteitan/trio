/-
**3 行・t = 2: M[n] の順位の残りの仮定 hF2・T2Tgt を背骨の補題で外す。**

- hF2（q ≠ r で o(q) は o(P_0 q) に依存しない）: o の呼び出しは真の祖先の o に依存しない（`not_depS_anc_o`）。
- T2Tgt（写しの列の v が読む x より前の列 g は o(q)・o(p2) に依存しない）: g は N で写しの列 p の
  P_1 か上げの行き先なので、g と p の間の列の行 1 は e1(g) 以上。その列のうち x の祖先は M の列と同じなので、
  M で g と x の間の背骨の行 1 は e1(g) 以上（`InvC M x g`）。背骨の補題で v(g) は x の真の祖先の o に依存しない。
-/
import Ytosk.V3Spine

namespace Ytosk

open T

/-- **An `o` call depends on no `o` of a proper ancestor.** -/
theorem not_depS_anc_o {M : Mat} (hBL : BumpLeaf M) {a y : Nat} (hy : Anc0 M y a) (hya : y ≠ a) :
    ∀ b, ¬ DepS M (SR y) b a := by
  intro b h
  apply spG_noreach hBL hy hya h
  exact ⟨fun _ h2 => absurd rfl h2, fun h1 _ => absurd (Anc0.refl a) h1⟩

/-- Ancestry agrees when the row-0 parents agree up to `B`. -/
theorem anc0_congr_le {M N : Mat} {B : Nat} (hp : ∀ j, j ≤ B → par N 0 j = par M 0 j) :
    ∀ {a b : Nat}, b ≤ B → (Anc0 N a b ↔ Anc0 M a b) := by
  have key : ∀ (P Q : Mat), (∀ j, j ≤ B → par P 0 j = par Q 0 j) → ∀ {a b : Nat}, b ≤ B → Anc0 P a b →
      Anc0 Q a b := by
    intro P Q hpq a b hb h
    induction h with
    | refl => exact Anc0.refl _
    | @step b' c hp' hA ih =>
      have hb' := par_lt P 0 c b' hp'
      exact Anc0.step (by rw [← hpq c hb]; exact hp') (ih (by omega))
  intro a b hb
  exact ⟨key N M hp hb, key M N (fun j hj => (hp j hj).symm) hb⟩

section
variable {M : Mat} {r L q d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hq : par M 0 (r + L) = some q)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hq hd0e hn

/-- The row-0 parents of `N` up to `x` are those of `M`. -/
theorem par0_N_le {j : Nat} (hj : j ≤ r + L) :
    par (TRIO.gexp M r L d0 d1 n) 0 j = par M 0 j := by
  rcases Nat.lt_or_ge j (r + L) with h | h
  · exact par_gexp_pre hlen (by omega) 0 h
  · have hjx : j = r + L := by omega
    subst hjx
    rcases par0_tail2g (d1 := d1) hlen hL hA hq hd0e hn (le_refl _) (by
        have := TRIO.gexp_length (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := n) hlen
        have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
        omega) with ⟨_, h'⟩ | ⟨p, _, h1, h2⟩
    · rw [h', hq]
    · omega

/-- Every column of `N` from `x` on is a descendant of `x`. -/
theorem anc0_N_x : ∀ p, r + L ≤ p → p < (TRIO.gexp M r L d0 d1 n).length →
    Anc0 (TRIO.gexp M r L d0 d1 n) (r + L) p := by
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    intro h1 h2
    have hlN := TRIO.gexp_length (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := n) hlen
    rcases par0_tail2g (d1 := d1) hlen hL hA hq hd0e hn h1 (by omega) with ⟨hp, _⟩ | ⟨p', hp', h3, h4⟩
    · rw [hp]; exact Anc0.refl _
    · exact Anc0.step hp' (ih p' h4 h3 (by omega))

/-- **`T2Tgt` from the spine lemma.** -/
theorem t2Tgt_spine (hBL : BumpLeaf M) {p2 : Nat} (hp2x : Anc0 M p2 (r + L)) (hp2x' : p2 ≠ r + L) :
    T2Tgt M r L q p2 (TRIO.gexp M r L d0 d1 n) := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hm1 : 1 ≤ n := by omega
  have hqx : Anc0 M q (r + L) := Anc0.step hq (Anc0.refl q)
  have hqx' : q ≠ r + L := by have := par_lt M 0 _ _ hq; omega
  intro g hg ⟨a, ha, _, hpu⟩
  set p := r + L + a with hpdef
  -- `g` is an upward step of `p` in `N`
  have hU : UpS N g p := by
    rcases hpu with h | ⟨_, h⟩
    · exact upS_par1 h
    · obtain ⟨m, hm, hkm, he, hcase⟩ := upg_facts h
      rcases hcase with hk1 | ⟨hA', hki⟩
      · omega
      · exact upS_upg hm hkm he hA' hki
  obtain ⟨hgp, hgp', _, hbw⟩ := hU
  have hxp := anc0_N_x hlen hL hA hq hd0e hn (d1 := d1) p (by omega) ha
  have hgxN : Anc0 N g (r + L) := by
    rcases anc0_total hgp hxp with h | h
    · exact h
    · have := h.le; omega
  have hcong : ∀ {u v : Nat}, v ≤ r + L → (Anc0 N u v ↔ Anc0 M u v) :=
    fun hv => anc0_congr_le (fun j hj => par0_N_le hlen hL hA hq hd0e hn hj) hv
  have hgx : Anc0 M g (r + L) := (hcong (le_refl _)).mp hgxN
  have hI : InvC M (r + L) g := by
    intro w hw1 hw2 hw3 hw4
    have hwx : w < r + L := by have := hw2.le; omega
    have hgw : Anc0 N g w := (hcong (by omega)).mpr hw1
    have hwxN : Anc0 N w (r + L) := (hcong (le_refl _)).mpr hw2
    have h := hbw w hgw (Anc0.trans hwxN hxp) hw3 (by omega)
    rwa [entry_gexp_pre hlen hm1 1 (by omega), entry_gexp_pre hlen hm1 1 hwx] at h
  exact ⟨not_depS_spine hBL hgx hI hqx hqx', not_depS_spine hBL hgx hI hp2x hp2x'⟩

end

/-- **The ranking of every `M[n]` (`n ≥ 1`), `t = 2`, from the structure of `M` only.** -/
theorem rk_gexp_t2_final {M : Mat} {r L q d0 d1 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hA : Anc0 M r (r + L)) (hq : par M 0 (r + L) = some q)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hd0 : 0 < d0) (hd1 : 0 < d1) (hgx : TRIO.le1 M r (r + L)) (he2r : entry M 2 r = 0)
    (h1x : entry M 1 r < entry M 1 (r + L))
    (hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUM : UAT M) (hBL : BumpLeaf M)
    (hUN : ∀ n, 2 ≤ n → UAT (TRIO.gexp M r L d0 d1 n))
    (hBE : ∀ n, 1 ≤ n → BumpE2 (TRIO.gexp M r L d0 d1 n))
    {rkM : Bool → Nat → Nat} (hRM : Rk M rkM) :
    ∀ n, 1 ≤ n → ∃ rk, Rk (TRIO.gexp M r L d0 d1 n) rk := by
  have hqx : Anc0 M q (r + L) := Anc0.step hq (Anc0.refl q)
  have hqlt := par_lt M 0 _ _ hq
  have hrq : Anc0 M r q := anc0_par hA (by omega) hq
  by_cases hqr : q = r
  · exact rk_gexp_t2_all (p2 := q) hlen hL hA hq hd0e hd0 hd1 hgx he2r h1x hqb
      (fun h => absurd hqr h) (fun h => absurd rfl h) hUM hR0 hZ2 hSD hZ1 hUN hBE
      (fun n hn => t2Tgt_spine hlen hL hA hq hd0e hn hBL hqx (by omega)) hRM
  · obtain ⟨pq, hpq⟩ := par0_of_anc hrq (Ne.symm hqr)
    have hpqq : Anc0 M pq q := Anc0.step hpq (Anc0.refl pq)
    have hpqlt := par_lt M 0 _ _ hpq
    exact rk_gexp_t2_all (p2 := pq) hlen hL hA hq hd0e hd0 hd1 hgx he2r h1x hqb
      (fun _ => hpq) (fun _ => not_depS_anc_o hBL hpqq (by omega) true) hUM hR0 hZ2 hSD hZ1 hUN hBE
      (fun n hn => t2Tgt_spine hlen hL hA hq hd0e hn hBL (Anc0.trans hpqq hqx) (by omega)) hRM

end Ytosk
