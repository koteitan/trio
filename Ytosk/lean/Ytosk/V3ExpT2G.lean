/-
**依存の閉包の門（gate）。**

列 s が「封じられている」（行 2 が 0 で、s + 1 へ上げない）とき、s の真部分木の外の呼び出しが部分木の中の種に
依存するなら、o(s) に依存する（`depS_gate`）。部分木へ外から入る辺は o(s) → o(子) だけだから
（のりしろの辺は s の行 2 が 0 で、上げの辺は s + 1 への上げがないので入らない）。
したがって v(s) は部分木の o の種に依存しない（`not_depS_sealed`、順位で o(s) → v(s) の循環を除く）。

t = 2 では r が封じられている（e2(r) = 0、r + 1 は r の子）。写しの根 x′ の v が読む v(r) は o(q)・o(p2) に
依存しない（`tgt_r_t2`）。
-/
import Ytosk.V3ExpT2E

namespace Ytosk

open T Classical

/-- The strict row-0 subtree of `s`. -/
def SubTr (M : Mat) (s c : Nat) : Prop := Anc0 M s c ∧ c ≠ s

/-- **The ranking grows along dependencies** from the seed `o(s)`. -/
theorem depS_rk {M : Mat} {rk : Bool → Nat → Nat} (hR : Rk M rk) {s : Nat} :
    ∀ {b i}, DepS M (SR s) b i → i < M.length → rk true s ≤ rk b i := by
  intro b i h
  induction h with
  | seed hs =>
    intro _
    rcases hs with ⟨hb, hi⟩
    subst hb; subst hi; exact le_refl _
  | ochild hc hcb hcu _ ih =>
    intro hi
    have := (hR _ hi).2.1 _ hc hcb hcu
    have := ih (mem_children hc).2
    omega
  | ov _ ih =>
    intro hi; have := (hR _ hi).1; have := ih hi; omega
  | vpar h1 hm _ ih =>
    intro hi
    have := ((hR _ hi).2.2 h1).1 _ hm
    have := ih (by have := par_lt _ 1 _ _ hm; omega)
    omega
  | vupg h1 h2 hk _ ih =>
    intro hi
    have := ((hR _ hi).2.2 h1).2.1 h2 _ hk
    have := ih (upg_lt hi hk)
    omega
  | vbump h1 h2 hj hjb hk _ ih =>
    intro hi
    have := ((hR _ hi).2.2 h1).2.2 h2 _ hj hjb _ hk
    have := ih (mem_children hk).2
    omega

/-- **The gate**: outside the strict subtree of a sealed column `s`, a dependency on a seed inside goes
through `o(s)`. -/
theorem depS_gate {M : Mat} {S : Bool → Nat → Prop} {s : Nat} (hs2 : entry M 2 s = 0)
    (hsu : upg M s ≠ some (s + 1)) (hS : ∀ b i, S b i → b = true ∧ (i = s ∨ SubTr M s i)) :
    ∀ {b i}, DepS M S b i → ¬ SubTr M s i → DepS M (SR s) b i := by
  intro b i h
  induction h with
  | @seed b i hs =>
    intro hni
    obtain ⟨hb, h⟩ := hS b i hs
    subst hb
    rcases h with h | h
    · exact DepS.seed ⟨rfl, h⟩
    · exact absurd h hni
  | @ochild i c hc hcb hcu _ ih =>
    intro hni
    by_cases hsc : SubTr M s c
    · have hpc := (mem_children_iff.mp hc).2
      have hsi : Anc0 M s i := anc0_par hsc.1 hsc.2.symm hpc
      by_cases his : i = s
      · exact DepS.seed ⟨rfl, his⟩
      · exact absurd ⟨hsi, his⟩ hni
    · exact DepS.ochild hc hcb hcu (ih hsc)
  | ov _ ih =>
    intro hni; exact DepS.ov (ih hni)
  | @vpar i m h1 hm _ ih =>
    intro hni
    have hmi := anc0_of_par M 1 _ _ hm
    have hmlt := par_lt M 1 _ _ hm
    have hsm : ¬ SubTr M s m := by
      rintro ⟨ha, hne⟩
      apply hni
      refine ⟨Anc0.trans ha hmi, fun his => ?_⟩
      have := ha.le; omega
    exact DepS.vpar h1 hm (ih hsm)
  | @vupg i k h1 h2 hk _ ih =>
    intro hni
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hk
    rcases hcase with hk1 | ⟨hA, hlt⟩
    · by_cases hsk : SubTr M s k
      · exfalso
        have hsi1 : Anc0 M s (i + 1) := by rw [← hk1]; exact hsk.1
        have hsle := hsi1.le
        have hne : i + 1 ≠ s := by rw [← hk1]; exact hsk.2
        have hsi : Anc0 M s i := anc_between hsi1 i (by omega) (by omega)
        by_cases his : i = s
        · subst his; exact hsu (by rw [hk, hk1])
        · exact hni ⟨hsi, his⟩
      · exact DepS.vupg h1 h2 hk (ih hsk)
    · have hsk : ¬ SubTr M s k := by
        rintro ⟨ha, hne⟩
        apply hni
        refine ⟨Anc0.trans ha hA, fun his => ?_⟩
        have := ha.le; omega
      exact DepS.vupg h1 h2 hk (ih hsk)
  | @vbump i j k h1 h2 hj hjb hk _ ih =>
    intro hni
    by_cases hsk : SubTr M s k
    · exfalso
      have hpk := (mem_children_iff.mp hk).2
      have hsj : Anc0 M s j := anc0_par hsk.1 hsk.2.symm hpk
      by_cases hjs : j = s
      · subst hjs
        have := (bump_eq hjb).2.2
        have h2' : (col M j).2.2 = entry M 2 j := rfl
        rw [h2', hs2] at this; omega
      · have hpj := (mem_children_iff.mp hj).2
        have hsi : Anc0 M s i := anc0_par hsj (Ne.symm hjs) hpj
        by_cases his : i = s
        · subst his; exact h2 hs2
        · exact hni ⟨hsi, his⟩
    · exact DepS.vbump h1 h2 hj hjb hk (ih hsk)

/-- `v(s)` does not depend on `o(s)` (ranking). -/
theorem not_depS_v_self {M : Mat} {rk : Bool → Nat → Nat} (hR : Rk M rk) {s : Nat} (hs : s < M.length) :
    ¬ DepS M (SR s) false s := fun h => by
  have := depS_rk hR h hs; have := (hR s hs).1; omega

/-- **`v` of a sealed column does not depend on a seed in its subtree.** -/
theorem not_depS_sealed {M : Mat} {S : Bool → Nat → Prop} {s : Nat} {rk : Bool → Nat → Nat}
    (hR : Rk M rk) (hs : s < M.length) (hs2 : entry M 2 s = 0) (hsu : upg M s ≠ some (s + 1))
    (hS : ∀ b i, S b i → b = true ∧ (i = s ∨ SubTr M s i)) : ¬ DepS M S false s := fun h =>
  not_depS_v_self hR hs (depS_gate hs2 hsu hS h (fun h' => h'.2 rfl))

/-- **`v(r)` (`t = 2`) depends neither on `o(q)` nor on `o(p2)`** (`q`, `p2` in the subtree of `r`). -/
theorem tgt_r_t2 {M : Mat} {r L q p2 : Nat} {rk : Bool → Nat → Nat} (hR : Rk M rk)
    (hlen : r + L + 1 = M.length) (hL : 0 < L) (hA : Anc0 M r (r + L))
    (he2r : entry M 2 r = 0) (hq : Anc0 M r q) (hp2 : Anc0 M r p2) :
    ¬ DepS M (SR q) false r ∧ ¬ DepS M (SR p2) false r := by
  have hr1 : Anc0 M r (r + 1) := anc_between hA (r + 1) (by omega) (by omega)
  have hsu : upg M r ≠ some (r + 1) := fun h => by have := upg_lt_of_child hr1 h; omega
  have hseed : ∀ p, Anc0 M r p → ∀ b i, SR p b i → b = true ∧ (i = r ∨ SubTr M r i) := by
    intro p hp b i h
    rcases h with ⟨hb, hi⟩
    subst i
    by_cases hpr : p = r
    · exact ⟨hb, Or.inl hpr⟩
    · exact ⟨hb, Or.inr ⟨hp, hpr⟩⟩
  exact ⟨not_depS_sealed hR (by omega) he2r hsu (hseed q hq),
    not_depS_sealed hR (by omega) he2r hsu (hseed p2 hp2)⟩

/-- **`T2Tgt` with the target `r` removed**: the target `r` (read by the copy root's `P_1`) is handled
by the gate (`tgt_r_t2`). -/
theorem t2Tgt_of_ne_r {M N : Mat} {r L q p2 : Nat} {rk : Bool → Nat → Nat} (hR : Rk M rk)
    (hlen : r + L + 1 = M.length) (hL : 0 < L) (hA : Anc0 M r (r + L))
    (he2r : entry M 2 r = 0) (hq : Anc0 M r q) (hp2 : Anc0 M r p2)
    (h : ∀ g, g < r + L → g ≠ r → (∃ a, r + L + a < N.length ∧ entry N 1 (r + L + a) ≠ 0 ∧
      (par N 1 (r + L + a) = some g ∨ (entry N 2 (r + L + a) = 0 ∧ upg N (r + L + a) = some g))) →
      ¬ DepS M (SR q) false g ∧ ¬ DepS M (SR p2) false g) :
    T2Tgt M r L q p2 N := by
  intro g hg hex
  by_cases hgr : g = r
  · subst hgr; exact tgt_r_t2 hR hlen hL hA he2r hq hp2
  · exact h g hg hgr hex

end Ytosk
