/-
Clause3Reduce.lean — GREEN reduction of Clause3 to its REVIVAL/overflow atom.

`substFree_of_clauses : Clause2 → Clause3 → SubstFree` (L7Subst) reduces the whole
z<2 termination to Clause2 ∧ Clause3.  This file discharges, from Clause3's own
datum `hgr_S : ∀ z ∈ W m, based z → SubstProp (graft S z)`, EVERY case of Clause3
except one, giving `clause3_of_atom : Clause3Atom → Clause3`:

  • D = []  (p = |S|-1):  `clause3_last` — substitute C into `graft S [(0,0,0)]`
    at the last position.  No tower.
  • D ≠ [] with (m < lev R 0 ∧ domT R m):  `clause3_interior_of` — clause-3
    introduction for R, graft obligation discharged by the commutation
    `graft R w = subst (graft S w) p C` + the datum.
  • D ≠ [] with ¬(m < lev R 0 ∧ domT R m) = `Clause3Atom`: the RESIDUE.  Its
    ¬domT R m half is precisely the REVIVAL case (C revives S's trailing orphan).

`Clause3`/`SubstProp` are inlined identically to `TRIO.L7` (L7Subst.lean is not a
lakefile root, so it has no olean to import).
-/
import Wtower2
import Final

namespace TRIO
namespace Clause3Reduce

open Wset Three

/-- Inlined identical to `TRIO.L7.SubstProp`. -/
def SubstProp (S : TrioSeq) : Prop :=
  ∀ (p : ℕ) (C : TrioSeq), p < S.length → C ≠ [] → C ∈ Wself →
    (S.take p ++ C ++ S.drop (p + 1)) ∈ Wself

/-- Inlined identical to `TRIO.L7.Clause3`. -/
def Clause3 : Prop :=
  ∀ (u m : ℕ) (S : TrioSeq), m < u → domT S m →
    (∀ z ∈ W m, based z → SubstProp (graft S z)) → SubstProp S

/-- The residue of Clause3: the interior (`D ≠ []`) substitution in the case
where R's trailing column is NOT a fitting orphan — i.e. it is revived
(`¬ domT R m`) or overflows the root (`¬ m < lev R 0`). -/
def Clause3Atom : Prop :=
  ∀ (m p : ℕ) (S C : TrioSeq), domT S m →
    (∀ z ∈ W m, based z → SubstProp (graft S z)) →
    p < S.length → S.drop (p + 1) ≠ [] → C ≠ [] → C ∈ Wself →
    ¬ (m < lev (S.take p ++ C ++ S.drop (p + 1)) 0 ∧
        domT (S.take p ++ C ++ S.drop (p + 1)) m) →
    (S.take p ++ C ++ S.drop (p + 1)) ∈ Wself

/-- **D = [] atom** — closed directly from the datum (no tower). -/
theorem clause3_last (m : ℕ) (S C : TrioSeq)
    (hd : domT S m)
    (hgr_S : ∀ z ∈ W m, based z → SubstProp (graft S z))
    (hCne : C ≠ []) (hCW : C ∈ Wself) :
    S.dropLast ++ C ∈ Wself := by
  have hSne : S ≠ [] := by
    rintro rfl; obtain ⟨hlev, -⟩ := hd; simp [lev, entry] at hlev
  have hSlen : 0 < S.length := List.length_pos_iff.mpr hSne
  set w : TrioSeq := [((0, 0, 0) : ℕ × ℕ × ℕ)] with hw
  have hwW : w ∈ W m := singleton_mem_W (by omega)
  have hwb : based w := by simp [based, entry, hw]
  have hsp := hgr_S w hwW hwb
  set g : TrioSeq := graft S w with hg
  have hglen : g.length = S.length := by rw [hg, graft_length]; simp [hw]; omega
  set e : ℕ := entry S 0 (S.length - 1) with he
  have hgeq : g = S.dropLast ++ [((e, 0, 0) : ℕ × ℕ × ℕ)] := by
    rw [hg]; unfold graft; simp [hw, he]
  set p' : ℕ := g.length - 1 with hp'
  have hp'lt : p' < g.length := by rw [hp']; omega
  have hres := hsp p' C hp'lt hCne hCW
  have htake : g.take p' = S.dropLast := by
    rw [hgeq, hp', hglen,
      show S.length - 1 = S.dropLast.length from by rw [List.length_dropLast]]
    exact List.take_left
  have hdrop : g.drop (p' + 1) = [] := by
    apply List.drop_eq_nil_of_le; rw [hp']; omega
  rw [htake, hdrop, List.append_nil] at hres
  exact hres

/-- **D ≠ [] interior, non-revival + fitting** — closed from the datum via the
commutation `graft R w = subst (graft S w) p C`. -/
theorem clause3_interior_of (m p : ℕ) (S C : TrioSeq)
    (hd : domT S m)
    (hgr_S : ∀ z ∈ W m, based z → SubstProp (graft S z))
    (hDne : S.drop (p + 1) ≠ [])
    (hCne : C ≠ []) (hCW : C ∈ Wself)
    (h1 : m < lev (S.take p ++ C ++ S.drop (p + 1)) 0)
    (h2 : domT (S.take p ++ C ++ S.drop (p + 1)) m) :
    (S.take p ++ C ++ S.drop (p + 1)) ∈ Wself := by
  set R : TrioSeq := S.take p ++ C ++ S.drop (p + 1) with hRdef
  have hSpos : 0 < S.length := by
    obtain ⟨hlev, -⟩ := hd
    rcases Nat.eq_zero_or_pos S.length with h0 | h
    · simp [h0, lev, entry] at hlev
    · exact h
  have hpS : p + 1 < S.length := by
    by_contra hc; exact hDne (List.drop_eq_nil_of_le (by omega))
  have hDlen : (S.drop (p + 1)).length = S.length - (p + 1) := by simp
  have hDpos : 0 < (S.drop (p + 1)).length := by rw [hDlen]; omega
  have hACpos : 0 < (S.take p ++ C).length := by
    rw [List.length_append]; have := List.length_pos_iff.mpr hCne; omega
  have hRlenEq : R.length = (S.take p ++ C).length + (S.drop (p + 1)).length := by
    rw [hRdef]; simp only [List.length_append]
  have hRlen2 : 2 ≤ R.length := by rw [hRlenEq]; omega
  set e : ℕ := entry S 0 (S.length - 1) with he
  have hRlast : entry R 0 (R.length - 1) = e := by
    have hidx : R.length - 1
        = (S.take p ++ C).length + ((S.drop (p + 1)).length - 1) := by
      rw [hRlenEq]; omega
    rw [hidx, hRdef]
    rw [show S.take p ++ C ++ S.drop (p + 1)
          = (S.take p ++ C) ++ S.drop (p + 1) from rfl, entry_append_right,
        entry_drop]
    congr 1; omega
  show R ∈ W (lev R 0)
  refine A1_intro (Or.inr (Or.inr ⟨m, h1, h2, ?_⟩))
  intro w hwW hwb
  have hsp := hgr_S w hwW hwb
  set f : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun q => (q.1 + e, q.2.1, q.2.2) with hf
  set wf : TrioSeq := w.map f with hwf
  have hgraftR : graft R w = R.dropLast ++ wf := by
    unfold graft; rw [hRlast, hwf, hf]
  have hgraftS : graft S w = S.dropLast ++ wf := by
    unfold graft; rw [← he, hwf, hf]
  have hp_le : p ≤ S.dropLast.length := by rw [List.length_dropLast]; omega
  have hp1_le : p + 1 ≤ S.dropLast.length := by rw [List.length_dropLast]; omega
  have hDdrop : (S.drop (p + 1)).dropLast = S.dropLast.drop (p + 1) := by
    rw [List.dropLast_eq_take, List.dropLast_eq_take, List.drop_take, hDlen,
      show S.length - (p + 1) - 1 = S.length - 1 - (p + 1) from by omega]
  have hRdropLast : R.dropLast = S.take p ++ C ++ S.dropLast.drop (p + 1) := by
    rw [hRdef,
      show S.take p ++ C ++ S.drop (p + 1)
        = (S.take p ++ C) ++ S.drop (p + 1) from rfl,
      List.dropLast_append_of_ne_nil hDne, hDdrop, List.append_assoc]
  have htakeRHS : (S.dropLast ++ wf).take p = S.take p := by
    rw [List.take_append_of_le_length hp_le, List.dropLast_eq_take,
      List.take_take, show min p (S.length - 1) = p from by omega]
  have hdropRHS : (S.dropLast ++ wf).drop (p + 1) = S.dropLast.drop (p + 1) ++ wf := by
    rw [List.drop_append_of_le_length hp1_le]
  have hcomm : graft R w
      = (graft S w).take p ++ C ++ (graft S w).drop (p + 1) := by
    rw [hgraftR, hgraftS, htakeRHS, hdropRHS, hRdropLast, List.append_assoc]
  have hp' : p < (graft S w).length := by rw [graft_length]; omega
  have hres : (graft S w).take p ++ C ++ (graft S w).drop (p + 1) ∈ Wself :=
    hsp p C hp' hCne hCW
  rw [← hcomm] at hres
  have hlev : lev (graft R w) 0 = lev R 0 := by
    rw [hgraftR]
    have h0 : ∀ i, entry (R.dropLast ++ wf) i 0 = entry R i 0 := by
      intro i
      rw [entry_append_left _ _ (by rw [List.length_dropLast]; omega),
        List.dropLast_eq_take, entry_take (by omega)]
    unfold lev; rw [h0 1, h0 2]
  have hmem : graft R w ∈ W (lev (graft R w) 0) := hres
  rwa [hlev] at hmem

/-- **★ GREEN: Clause3 reduces to exactly the revival/overflow atom.**  The other
three cases (D=[], and D≠[] non-revival-and-fitting) are discharged by the
Clause3 datum. -/
theorem clause3_of_atom (h_atom : Clause3Atom) : Clause3 := by
  intro u m S _hmu hd hgr_S p C hp hCne hCW
  by_cases hDnil : S.drop (p + 1) = []
  · -- D = [] : p = |S|-1, result = S.dropLast ++ C
    have hle : S.length ≤ p + 1 := List.drop_eq_nil_iff.mp hDnil
    have hpe : p = S.length - 1 := by omega
    rw [hDnil, List.append_nil,
      show S.take p = S.dropLast from by rw [List.dropLast_eq_take, hpe]]
    exact clause3_last m S C hd hgr_S hCne hCW
  · -- D ≠ []
    by_cases hfit : m < lev (S.take p ++ C ++ S.drop (p + 1)) 0 ∧
        domT (S.take p ++ C ++ S.drop (p + 1)) m
    · exact clause3_interior_of m p S C hd hgr_S hDnil hCne hCW hfit.1 hfit.2
    · exact h_atom m p S C hd hgr_S hp hDnil hCne hCW hfit

end Clause3Reduce
end TRIO
