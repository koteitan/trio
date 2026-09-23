/-
SubstAttempt4.lean — Clause3 D≠[] interior case: the datum discharges the graft
obligation; the wall is exactly (m < lev R 0) ∧ (domT R m = non-revival).

`clause3_interior_of` proves `R := S.take p ++ C ++ D ∈ Wself` for D ≠ [] from
the Clause3 datum, GIVEN the two clause-3-introduction side conditions
  h1 : m < lev R 0        (the trailing orphan's level fits under the root)
  h2 : domT R m           (R's trailing is still an orphan — NON-revival)
The graft obligation `∀ w ∈ W m based, graft R w ∈ W(lev R 0)` is closed by the
commutation `graft R w = subst (graft S w) p C` + the datum `SubstProp(graft S w)`.
So Clause3-D≠[] is missing only h1 ∧ h2; ¬h2 is precisely the REVIVAL case.
-/
import Wtower2
import Final

namespace TRIO
namespace SubstAttempt4

open Wset Three

def SubstProp (S : TrioSeq) : Prop :=
  ∀ (p : ℕ) (C : TrioSeq), p < S.length → C ≠ [] → C ∈ Wself →
    (S.take p ++ C ++ S.drop (p + 1)) ∈ Wself

theorem clause3_interior_of (m p : ℕ) (S C : TrioSeq)
    (hd : domT S m)
    (hgr_S : ∀ z ∈ W m, based z → SubstProp (graft S z))
    (hDne : S.drop (p + 1) ≠ [])
    (hCne : C ≠ []) (hCW : C ∈ Wself)
    (h1 : m < lev (S.take p ++ C ++ S.drop (p + 1)) 0)
    (h2 : domT (S.take p ++ C ++ S.drop (p + 1)) m) :
    (S.take p ++ C ++ S.drop (p + 1)) ∈ Wself := by
  set R : TrioSeq := S.take p ++ C ++ S.drop (p + 1) with hRdef
  -- lengths
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
  -- R's trailing column IS S's trailing column (D ≠ []): entry R 0 (|R|-1) = e
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
  -- graft R w  and  graft S w  in terms of the SAME map f
  have hgraftR : graft R w = R.dropLast ++ wf := by
    unfold graft; rw [hRlast, hwf, hf]
  have hgraftS : graft S w = S.dropLast ++ wf := by
    unfold graft; rw [← he, hwf, hf]
  -- commutation: graft R w = subst (graft S w) p C
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
  -- apply the datum
  have hp' : p < (graft S w).length := by rw [graft_length]; omega
  have hres : (graft S w).take p ++ C ++ (graft S w).drop (p + 1) ∈ Wself :=
    hsp p C hp' hCne hCW
  rw [← hcomm] at hres
  -- convert Wself (= W (lev · 0)) membership to W (lev R 0)
  have hlev : lev (graft R w) 0 = lev R 0 := by
    rw [hgraftR]
    have h0 : ∀ i, entry (R.dropLast ++ wf) i 0 = entry R i 0 := by
      intro i
      rw [entry_append_left _ _ (by rw [List.length_dropLast]; omega),
        List.dropLast_eq_take, entry_take (by omega)]
    unfold lev; rw [h0 1, h0 2]
  have hmem : graft R w ∈ W (lev (graft R w) 0) := hres
  rwa [hlev] at hmem

end SubstAttempt4
end TRIO
