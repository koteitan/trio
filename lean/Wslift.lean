/-
Wslift.lean: **階段リフトは `W` 所属を段の押し上げつきで運ぶ**。

`slift_oper` (G2) により階段リフトは `oper` と**可換**なので、`Aop` の節 2 は
そのまま移る。節 3 は長さ 2 以上では節 2 に吸収される（`Wchar`）。残るのは
長さ 1 の根だけで、そこでは

```
slift [(d,b,c)] φ = [(d, φ b, c)]     （レベル 2b+c → 2 (φ b) + c）
```

なので**段を上げれば通る**。これが `CoreStairOm`（段を固定したままでは通らない
唯一の箇所）の正体で、段を `2 * φ m + m` まで緩めれば核なしで証明できる。

計測（`tools/probe_lift.py`）: 根リフトについては
`minstage (Lift1 X d) = minstage X + 2d` が 18300 例で**等号**で成立。
本補題はその階段リフト版（上界は緩め）。
-/
import Wchar
import Aexp

namespace TRIO

open Wset

theorem slift_of_length_one {X : TrioSeq} (h1 : X.length = 1) {φ : ℕ → ℕ}
    (hφ : Stair φ) :
    slift X φ = [((entry X 0 0, φ (entry X 1 0), entry X 2 0) : ℕ × ℕ × ℕ)] := by
  unfold slift
  rw [h1, show List.range 1 = [0] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [amin_zero]
  have hge := hφ.ge (entry X 1 0)
  rw [show entry X 1 0 + (φ (entry X 1 0) - entry X 1 0) = φ (entry X 1 0) from
    by omega]

/-- **The staircase lift transports `W`-membership**, at the cost of a stage
bump.  No cores: clause 2 rides on `slift_oper` (G2), clause 3 collapses into
clause 2 above length 1 (`aop_clause3_to_clause2`), and the one-column roots —
the only place where the stage genuinely has to rise — are discharged by
`singleton_mem_W` because the bumped stage `2 * φ m + m` dominates
`2 * φ b + c` whenever `2 * b + c ≤ m`. -/
theorem slift_mem_W {m : ℕ} {φ : ℕ → ℕ} (hφ : Stair φ) :
    ∀ X ∈ W m, slift X φ ∈ W (2 * φ m + m) := by
  have hsub : W m ⊆ {X : TrioSeq | slift X φ ∈ W (2 * φ m + m)} := by
    refine A2' ?_
    rintro X (⟨hl, hlev⟩ | hop | ⟨m', hm', hd, hgr⟩)
    · -- clause 1: short with a zero root
      rcases Nat.eq_zero_or_pos X.length with h0 | hpos
      · have hnil : X = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show slift ([] : TrioSeq) φ ∈ W (2 * φ m + m)
        simpa [slift] using W_nil (2 * φ m + m)
      · have h1 : X.length = 1 := by omega
        show slift X φ ∈ W (2 * φ m + m)
        rw [slift_of_length_one h1 hφ]
        have hb : entry X 1 0 = 0 ∧ entry X 2 0 = 0 := by
          unfold lev at hlev; omega
        rw [hb.1, hb.2, hφ.zero]
        exact singleton_mem_W (by omega)
    · -- clause 2: `slift` commutes with `oper`
      rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hres := hop 1 le_rfl
        rwa [oper_eq_self_of_short 1 (by omega)] at hres
      · show slift X φ ∈ W (2 * φ m + m)
        refine mem_of_oper_mem (fun n hn => ?_)
        rw [← slift_oper hφ]
        exact hop n hn
    · -- clause 3: absorbed above length 1; a stage bump at length 1
      rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hXne : X ≠ [] := by
          intro hc
          rw [hc] at hd
          exact not_domT_nil m' hd
        have h1 : X.length = 1 := by
          have : 0 < X.length := List.length_pos_iff.mpr hXne
          omega
        have hlev := hd.1
        rw [show X.length - 1 = 0 from by omega] at hlev
        unfold lev at hlev
        show slift X φ ∈ W (2 * φ m + m)
        rw [slift_of_length_one h1 hφ]
        refine singleton_mem_W ?_
        have hmono : φ (entry X 1 0) ≤ φ m :=
          hφ.mono (by omega)
        omega
      · show slift X φ ∈ W (2 * φ m + m)
        refine mem_of_oper_mem (fun n hn => ?_)
        rw [← slift_oper hφ]
        exact aop_clause3_to_clause2 hbig hd hgr n hn
  exact fun X hX => hsub hX

/-- **Tight form**: if the staircase never lifts by more than `d`, the stage
rises by exactly `2 * d` — the same law the root lift obeys with equality
(`tools/probe_lift.py`).  The bound is only used at the one-column roots, where
`2 * φ b + c ≤ (2 * b + c) + 2 * d ≤ m + 2 * d`. -/
theorem slift_mem_W_tight {m d : ℕ} {φ : ℕ → ℕ} (hφ : Stair φ)
    (hb : ∀ k, φ k ≤ k + d) : ∀ X ∈ W m, slift X φ ∈ W (m + 2 * d) := by
  have hsub : W m ⊆ {X : TrioSeq | slift X φ ∈ W (m + 2 * d)} := by
    refine A2' ?_
    rintro X (⟨hl, hlev⟩ | hop | ⟨m', hm', hd, hgr⟩)
    · rcases Nat.eq_zero_or_pos X.length with h0 | hpos
      · have hnil : X = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show slift ([] : TrioSeq) φ ∈ W (m + 2 * d)
        simpa [slift] using W_nil (m + 2 * d)
      · have h1 : X.length = 1 := by omega
        show slift X φ ∈ W (m + 2 * d)
        rw [slift_of_length_one h1 hφ]
        have hbc : entry X 1 0 = 0 ∧ entry X 2 0 = 0 := by
          unfold lev at hlev; omega
        rw [hbc.1, hbc.2, hφ.zero]
        exact singleton_mem_W (by omega)
    · rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hres := hop 1 le_rfl
        rwa [oper_eq_self_of_short 1 (by omega)] at hres
      · show slift X φ ∈ W (m + 2 * d)
        refine mem_of_oper_mem (fun n hn => ?_)
        rw [← slift_oper hφ]
        exact hop n hn
    · rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hXne : X ≠ [] := by
          intro hc
          rw [hc] at hd
          exact not_domT_nil m' hd
        have h1 : X.length = 1 := by
          have : 0 < X.length := List.length_pos_iff.mpr hXne
          omega
        have hlev := hd.1
        rw [show X.length - 1 = 0 from by omega] at hlev
        unfold lev at hlev
        show slift X φ ∈ W (m + 2 * d)
        rw [slift_of_length_one h1 hφ]
        refine singleton_mem_W ?_
        have hbk := hb (entry X 1 0)
        omega
      · show slift X φ ∈ W (m + 2 * d)
        refine mem_of_oper_mem (fun n hn => ?_)
        rw [← slift_oper hφ]
        exact aop_clause3_to_clause2 hbig hd hgr n hn
  exact fun X hX => hsub hX

/-- **The ambient mask lift costs exactly `2 * d` stages.**  `mlift` is the
staircase lift by the step function (`mlift_eq_slift`), which never lifts by
more than `d`. -/
theorem mlift_mem_W {m v d : ℕ} : ∀ X ∈ W m, mlift X v d ∈ W (m + 2 * d) := by
  intro X hX
  rw [mlift_eq_slift]
  exact slift_mem_W_tight (stair_step v d) (fun k => by split <;> omega) X hX

end TRIO

