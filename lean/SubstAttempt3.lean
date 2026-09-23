/-
SubstAttempt3.lean — scratch (team-lead Clause3 plan).

Test: does the Clause3 datum close the D = [] atom (substitution at the LAST
position, p = |S|-1)?  Clause3 gives
    hgr_S : ∀ z ∈ W m, based z → SubstProp (graft S z).
Goal (D=[]): `S.dropLast ++ C ∈ Wself`.

KEY IDEA (different from the L7 doc's "relate graft R z to graft S z" strategy):
pick z = [(0,0,0)] ∈ W m (based).  Then graft S z = S.dropLast ++ [(e,0,0)]
(e = entry S 0 (|S|-1)), and SubstProp (graft S z) at the LAST position with the
block C yields exactly `S.dropLast ++ C ∈ Wself`.
-/
import Wtower2
import Final

namespace TRIO
namespace SubstAttempt3

open Wset Three

/-- Inlined identical to `TRIO.L7.SubstProp` (L7Subst.lean is not a lakefile
root, so it has no olean to import). -/
def SubstProp (S : TrioSeq) : Prop :=
  ∀ (p : ℕ) (C : TrioSeq), p < S.length → C ≠ [] → C ∈ Wself →
    (S.take p ++ C ++ S.drop (p + 1)) ∈ Wself

/-- The D = [] atom of Clause3, closed directly from the Clause3 datum. -/
theorem clause3_last (u m : ℕ) (S C : TrioSeq)
    (hmu : m < u) (hd : domT S m)
    (hgr_S : ∀ z ∈ W m, based z → SubstProp (graft S z))
    (hCne : C ≠ []) (hCW : C ∈ Wself) :
    S.dropLast ++ C ∈ Wself := by
  -- S is nonempty (domT gives a trailing column)
  have hSne : S ≠ [] := by
    rintro rfl
    obtain ⟨hlev, -⟩ := hd
    simp [lev, entry] at hlev
  have hSlen : 0 < S.length := List.length_pos_iff.mpr hSne
  set w : TrioSeq := [((0, 0, 0) : ℕ × ℕ × ℕ)] with hw
  have hwW : w ∈ W m := singleton_mem_W (by omega)
  have hwb : based w := by simp [based, entry, hw]
  have hsp := hgr_S w hwW hwb
  set g : TrioSeq := graft S w with hg
  -- length of g
  have hglen : g.length = S.length := by
    rw [hg, graft_length]; simp [hw]; omega
  -- g = S.dropLast ++ [(e,0,0)]
  set e : ℕ := entry S 0 (S.length - 1) with he
  have hgeq : g = S.dropLast ++ [((e, 0, 0) : ℕ × ℕ × ℕ)] := by
    rw [hg]; unfold graft; simp [hw, he]
  -- apply SubstProp at the last position
  set p' : ℕ := g.length - 1 with hp'
  have hp'lt : p' < g.length := by rw [hp']; omega
  have hres := hsp p' C hp'lt hCne hCW
  -- g.take p' = S.dropLast
  have htake : g.take p' = S.dropLast := by
    rw [hgeq, hp', hglen]
    rw [show S.length - 1 = S.dropLast.length from by rw [List.length_dropLast]]
    exact List.take_left
  -- g.drop (p'+1) = []
  have hdrop : g.drop (p' + 1) = [] := by
    apply List.drop_eq_nil_of_le
    rw [hp']; omega
  rw [htake, hdrop, List.append_nil] at hres
  exact hres

end SubstAttempt3
end TRIO
