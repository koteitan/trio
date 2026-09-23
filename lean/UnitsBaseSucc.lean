/-
UnitsBaseSucc.lean — units_base succ (multi-head far-word tower) in own scratch.
Goal: GTC CQ v (fh v (n+1)) from IH GTC CQ v (fh v n).  fh v n = [(1,v+1,1)]ⁿ.

CONSOLIDATED FINDING (rigorous, verified in Lean + bms):

1. units_base succ = a genuine h=2 far-word ASCENSION tower, NOT a flat/h=1 tower.
   • rword 0 u l = l.flatMap (rcol 0 u); rcol 0 u X = (1,u+1,1)::shiftr01 1 0 X.
     So ONE n-column word fh gives "1 head (1,u+1,1) + n shift-tails (2,u+1,1)ⁿ"
     (distinct from n separate far-words, which give n (head,tail) pairs).
   • bms: (0,0,0)(1,1,1)(2,1,1)(2,1,1) has delta=(2,1) — root ascends by (2,1) per
     copy (row0 += 2), i.e. the trailing (2,u+1,1) has h=2 (row0=2). Contrast the
     single flat head (0,0,0)(1,1,1): delta=(1,1) (h=1).

2. NAIVE hangv-iteration provably FAILS (concrete wall, not a gap):
   • oper_zcone (h=2) on the last (2,u+1,1) gives the flatMap
       (range k).flatMap (fun j => shiftr01 (j*2) 0 ((0,u+j,0)::mlift P u j)).
   • Each copy content is IH-closed: (0,u+j,0)::mlift P u j = the units_base(n)
     witness at level u+j (via mlift_rword+mlift_fh+map_CQ) ∈ Wstarv(u+j). GOOD.
   • But assembling the tower with hangv (GxD:27 / hang_Wg GwU:140) needs
       rsum A R := ∀p∈A++R, entry R 0 0 ≤ p.1   (Wset:1317).
     With R = shiftr01 2 0 (tower tail), entry R 0 0 = 2; but A (= copy content)
     contains the far-head (1,u+1,1) with row0 = 1. So rsum needs 2 ≤ 1 — FALSE.
     (hangv encodes this as the unused-looking `hhd : entry R 0 0 ≤ 1`, discharged
     by omega inside the hrs proof.) So Pz_Wg-style hangv iteration does NOT extend
     to h=2. This is the wall.

3. WHY Aj works but fh doesn't:  Aj v j = [(1,v+1,1),(2,v+1,0)] ++ [(1,v+1,1)]ʲ
   (GxF:138) closes via Pz_Wg (h=1, Aj_star GxF:166) BECAUSE the (2,v+1,0) SEPARATOR
   makes each tower level's trailing (1,v+1,1) (row0=1 → h=1 → hhd holds). fh has NO
   separator. Realizing the h=2 jump as two h=1 steps + a (1,r,0) separator is
   EXACTLY towWAQ (HaW:85): towWAQ ... (m+1) = (Q++farW) ++ (1,r,1)::shiftr01 1 0
   ((1,r,0)::shiftr01 1 0 (towWAQ (r+1) m)). So units_base succ = the n-head
   generalization of topCQ_Wg (HbB:140), which lives in the deep towWAQ/FarCAQ/GpT
   far-word layer (towWAQ_GpT has ~15 hypotheses). Substantial; = Climb's HbB/HaW.

4. SHORT + OPER-flat COLLAPSE INTO THE SAME BLOCKER:
   • SHORT content = [(1,u+1,1),(2,0,0)] = K ++ [(2,0,0)], K=[(1,u+1,1)]. The flat
     (2,0,0) has row0=2 > 1=head, so NOT GTC_flat (needs x ≤ min row0) and NOT a
     based load shiftr01 1 0 T (that gives head 1, not 2). Via GTC_oper / HdR.gtc_flat
     (oper_snoc00'') it reduces to hrep: ∀n, GTC C u (M^n), M=[(1,u+1,1)] ⟹ GTC C u
     (fh u n) = units_base. So SHORT ⟸ units_base (h=2 tower).
   • OPER-flat content = K ++ [(2,0,0)], K = content of Y.dropLast (GTC from hop:
     Y⟦1⟧=Y.dropLast); reduces the same way to GTC C u (Kⁿ) = generalized units_base.
   ⟹ SHORT, OPER-flat, units_base are ONE blocker (towWAQ n-gen), not 3 tasks.
   (ALT live route: ChildLoadAnchor renders the load via GoodChtX `ch` leaves —
   chZ_render: topT v (ch (shiftr01 1 0 Z)) = shiftr01 2 0 Z — the HdA-HdR tree
   layer; also deep. Either way SHORT/OPER need a deep far-word layer.)

Helpers below (fh, shiftr01_fh, mlift_fh, ...) are GREEN and reusable.
-/
import HbB
import GzD
import GxV

namespace TRIO
namespace UnitsBaseSucc

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxV GzD GzH GzJ HbB

noncomputable def fh (v : ℕ) : ℕ → TrioSeq
  | 0 => []
  | n + 1 => ((1, v + 1, 1) : ℕ × ℕ × ℕ) :: fh v n

theorem shiftr01_fh (v n : ℕ) :
    shiftr01 1 0 (fh v n) = List.replicate n ((2, v + 1, 1) : ℕ × ℕ × ℕ) := by
  induction n with
  | zero => simp [fh, shiftr01]
  | succ n ih => simp only [fh, shiftr01, List.map_cons, List.replicate_succ]; rw [← shiftr01, ih]

theorem fh_row0 (v n : ℕ) : ∀ y ∈ fh v n, 1 ≤ y.1 := by
  induction n with
  | zero => intro y hy; simp [fh] at hy
  | succ n ih =>
      intro y hy; simp only [fh, List.mem_cons] at hy
      rcases hy with rfl | hy
      · omega
      · exact ih y hy

theorem fh_replicate (v n : ℕ) : fh v n = List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ) := by
  induction n with
  | zero => simp [fh]
  | succ n ih => rw [fh, ih, List.replicate_succ]

theorem entry_repl0 (v n j : ℕ) (hj : j < n) :
    entry (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)) 0 j = 1 := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
    (show j < (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)).length by
      rw [List.length_replicate]; exact hj)]

theorem entry_repl1 (v n j : ℕ) (hj : j < n) :
    entry (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)) 1 j = v + 1 := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
    (show j < (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)).length by
      rw [List.length_replicate]; exact hj)]

theorem mlift_fh (v n d : ℕ) : mlift (fh v n) v d = fh (v + d) n := by
  rw [fh_replicate, fh_replicate, mlift, List.length_replicate]
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, List.length_replicate]
  · intro j hj1 _
    rw [List.length_map, List.length_range] at hj1
    have hj : j < n := hj1
    rw [List.getElem_map, List.getElem_range, List.getElem_replicate,
      entry_repl0 v n j hj, entry_repl1 v n j hj]
    have e2 : entry (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)) 2 j = 1 := by
      simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
        (show j < (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)).length by
          rw [List.length_replicate]; exact hj)]
    rw [e2]
    have hcone : coneV (List.replicate n ((1, v + 1, 1) : ℕ × ℕ × ℕ)) v j := by
      intro y hy
      have hyj : y = j := by
        rcases Relation.ReflTransGen.cases_tail hy with h1 | ⟨z, _, hzj⟩
        · exact h1.symm
        · exfalso
          obtain ⟨hzl, hjl, hzlt, hent, -⟩ := hzj
          rw [List.length_replicate] at hzl hjl
          rw [entry_repl0 v n z hzl, entry_repl0 v n j hjl] at hent; omega
      rw [hyj, entry_repl1 v n j hj]; omega
    rw [if_pos hcone]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    show v + 1 + d = v + d + 1; omega

/-- Probe: units_base succ, goal after simplification. -/
theorem units_base_succ (n : ℕ) (ih : ∀ v, GTC CQ v (fh v n)) :
    ∀ v, GTC CQ v (fh v (n + 1)) := by
  intro v L hC hL hB u hu _ a ha
  obtain ⟨bs, uss, hR, hNT, rfl⟩ := hC
  -- simplify the appended word
  rw [List.map_append, List.map_cons, List.map_nil, rword_append, rword_singleton,
    mlift_fh, show v + (u - v) = u from by omega]
  -- Goal: (0,u,0) :: (P ++ rcol 0 u (fh u (n+1))) ∈ Wg a,  P = rword 0 u (CQ-prefix lifted).
  -- rcol 0 u (fh u (n+1)) = (1,u+1,1) :: [(2,u+1,1)]ⁿ⁺¹  (shiftr01_fh).
  -- WALL (see header §2): oper_zcone (h=2) on the LAST (2,u+1,1) opens the tower;
  --   copies are IH-closed (∈ Wstarv(u+j)); but hangv/hang_Wg assembly needs
  --   rsum A R (entry R 0 0 ≤ every p.1) and R=shiftr01 2 0(tail) has head row0=2 >
  --   1=(1,u+1,1).1 ⟹ FALSE. Needs the towWAQ (1,r,0)-separator (Climb's HbB/HaW),
  --   the n-head generalization of topCQ_Wg. SHORT + OPER-flat reduce here too (§4).
  sorry

end UnitsBaseSucc
end TRIO
