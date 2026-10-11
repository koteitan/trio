/-
**LevFree を運ぶ形: VKFree（行 1 の子を持つ列の v どうし）。**

VK(M) = {v(q) : q は行 1 の子を持つ列}。実測（C′、2026-10-11）:
- VKFree: 行 1 の子を持つ列 p, q（v(q) ≠ 0）について、v(p) は添字 v(q) の部分項を持たない（226 万件、例外 0）。
- 段の結び（LevLink）: どの列の o・v に現れる Ω_{μ+1}（μ ≠ 0）も μ ∈ VK（48 万件、例外 0）。のりしろの項の穴の段
  も、c の部分木の段もこれに入る。
VKFree は行 1 の子を持つ列の v だけの条件なので、1 列落とし（v は変わらない）と t = 0（v は M の値）で
そのまま運べる。LevLink ∧ VKFree ⇒ LevFree（t1-exp の種の条件の μ > 0）。
-/
import Ytosk.V3PhiGapBase
import Ytosk.V3PhiGapT0

namespace Ytosk

open T

/-- **VKFree**: no `v(p)` of a column with a row-1 child has a subterm with subscript `v(q)` of another such
column (`v(q) ≠ 0`). -/
def VKFree (M : Mat) (ρ : Valn) : Prop :=
  ∀ c p c' q, c < M.length → par M 1 c = some p → c' < M.length → par M 1 c' = some q →
    ρ.v q ≠ z → LevFree (ρ.v q) (ρ.v p)

/-- **The level link**: the level `μ ≠ 0` is the `v` of a column with a row-1 child. -/
def InVK (M : Mat) (ρ : Valn) (μ : T) : Prop :=
  ∃ c q, c < M.length ∧ par M 1 c = some q ∧ ρ.v q = μ

/-- **LevFree from VKFree** at a level in `VK`. -/
theorem levFree_of_vk {M : Mat} {ρ : Valn} (h : VKFree M ρ) {c p : Nat} (hc : c < M.length)
    (hp : par M 1 c = some p) {μ : T} (hμ : μ ≠ z) (hin : InVK M ρ μ) : LevFree μ (ρ.v p) := by
  obtain ⟨c', q, hc', hq, rfl⟩ := hin
  exact h c p c' q hc hp hc' hq hμ

/-- On the row-1 chain of a column. -/
theorem levFree_chain_of_vk {M : Mat} {ρ : Valn} (h : VKFree M ρ) {c p : Nat} (hc : c < M.length)
    (hch : P1Chain M p c) {μ : T} (hμ : μ ≠ z) (hin : InVK M ρ μ) : LevFree μ (ρ.v p) := by
  obtain ⟨c', hc', hp⟩ := hch.has_child hc
  exact levFree_of_vk h hc' hp hμ hin

/-! ## 基底 -/

theorem base_vKFree {L : Nat} {β : T} : VKFree (Mlen L) (bval L β) := by
  intro c p c' q _ _ _ hq hne
  exact absurd (base_v_par1 hq) hne

/-! ## 1 列落とし -/

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB

theorem vKFree_take {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hR' : Rk (M.take x) rk') (hV : VKFree M ρ) : VKFree (M.take x) ρ' := by
  intro c p c' q hc hp hc' hq hne
  have hlen : (M.take x).length = x := by rw [List.length_take]; omega
  rw [hlen] at hc hc'
  rw [par_take M 1 c hc] at hp
  rw [par_take M 1 c' hc'] at hq
  rw [v_take_of_par1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hR' hc hp,
    v_take_of_par1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hR' hc' hq] at *
  exact hV c p c' q (by omega) hp (by omega) hq hne

end

/-! ## t = 0 の M[n] -/

/-- The values of the columns with a row-1 child. -/
def InVKv (M : Mat) (ρ : Valn) (t : T) : Prop := ∃ d a, d < M.length ∧ par M 1 d = some a ∧ t = ρ.v a

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB

/-- **The t = 0 correspondence**: every column of `M[n]` with a row-1 child has the `v` of a column of
`M` with a row-1 child. -/
theorem corr_t0 {ρ ρ' σ : Valn} {oMid : T} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take (r + L)) ρ') (hR' : Rk (M.take (r + L)) rk')
    (hlow : ∀ i, i < r → ¬ DepX M (r + L) false i → σ.v i = ρ.v i)
    (hσBv : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length → σ.v i = (tauN r L n ρ ρ' oMid).v i) :
    VP (InVKv M ρ) (TRIO.gexp M r L 0 0 n) σ := by
  refine vP_t0 (Q := InVKv M ρ) hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB ?_ ?_ hlow hσBv
  · intro c p hc hp1; exact ⟨c, p, hc, hp1, rfl⟩
  · intro c p hc hp1
    have hcx : c < r + L := by rw [List.length_take] at hc; omega
    rw [par_take M 1 c hcx] at hp1
    refine ⟨c, p, by omega, hp1, ?_⟩
    exact v_take_of_par1 (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hR'
      hcx hp1

/-- **VKFree of the t = 0 expansion.** -/
theorem vKFree_t0 {ρ ρ' σ : Valn} {oMid : T} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take (r + L)) ρ') (hR' : Rk (M.take (r + L)) rk')
    (hlow : ∀ i, i < r → ¬ DepX M (r + L) false i → σ.v i = ρ.v i)
    (hσBv : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length → σ.v i = (tauN r L n ρ ρ' oMid).v i)
    (hV : VKFree M ρ) : VKFree (TRIO.gexp M r L 0 0 n) σ := by
  have hcorr := corr_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hR' hlow hσBv
  intro c p c' q hc hp1 hc' hq hne
  obtain ⟨d, a, hd, hda, ha⟩ := hcorr c p hc hp1
  obtain ⟨d', b, hd', hdb, hb⟩ := hcorr c' q hc' hq
  rw [ha, hb]
  exact hV d a d' b hd hda hd' hdb (by rw [← hb]; exact hne)

end

end Ytosk
