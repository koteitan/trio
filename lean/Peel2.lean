/-
Peel2.lean: srow = 2 のガード付き剥離（the guarded peel）。

コアの自己言及的な hshift 上界を、ホスト橋（hshift_gseg）でホスト
N-係留のガード付き写像形（gmap）に変換し、カスケード前置のガード輸送
（Gtrans.gexp_guard_transport）で mapF_1 ∘ F_k = F_{k+1} と合成して、
ガード付きコピー塔（gtow）に展開する。塔は q = F_1(root) を消去すると
ちょうど M⟦m⟧ の尾部（gcopiesFrom）に一致する。
-/
import ArgDom
import Gtrans

namespace TRIO

open Classical

/-- Position-anchored guarded map (an offset form of `gcopy`). -/
noncomputable def gmap (N : TrioSeq) (r d0 d1 j a l : ℕ) : TrioSeq :=
  (List.range' a l).map fun p =>
    (entry N 0 p + j * d0,
     entry N 1 p + (if le1 N r p then j * d1 else 0),
     entry N 2 p)

/-- The guarded tower over the shifted block `(r, r+Lb]`. -/
noncomputable def gtow (N : TrioSeq) (r d0 d1 Lb k m : ℕ) : TrioSeq :=
  (List.range' k m).flatMap fun j => gmap N r d0 d1 j (r + 1) Lb

@[simp] theorem gmap_length (N : TrioSeq) (r d0 d1 j a l : ℕ) :
    (gmap N r d0 d1 j a l).length = l := by
  unfold gmap
  simp

theorem gmap_getD {N : TrioSeq} {r d0 d1 j a l i : ℕ} (hi : i < l) :
    (gmap N r d0 d1 j a l).getD i (0, 0, 0)
      = (entry N 0 (a + i) + j * d0,
         entry N 1 (a + i) + (if le1 N r (a + i) then j * d1 else 0),
         entry N 2 (a + i)) := by
  unfold gmap
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range' (by simpa using hi)]
  rw [Nat.one_mul]
  rfl

theorem gmap_append (N : TrioSeq) (r d0 d1 j a l1 l2 : ℕ) :
    gmap N r d0 d1 j a (l1 + l2)
      = gmap N r d0 d1 j a l1 ++ gmap N r d0 d1 j (a + l1) l2 := by
  unfold gmap
  rw [← List.map_append, ← List.range'_append_1]

theorem seg_getD {N : TrioSeq} {a l i : ℕ} (hi : i < l) :
    (seg N a l).getD i (0, 0, 0)
      = (entry N 0 (a + i), entry N 1 (a + i), entry N 2 (a + i)) := by
  unfold seg
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range' (by simpa using hi)]
  rw [Nat.one_mul]
  rfl

theorem seg_append (N : TrioSeq) (a l1 l2 : ℕ) :
    seg N a (l1 + l2) = seg N a l1 ++ seg N (a + l1) l2 := by
  unfold seg
  rw [← List.map_append, ← List.range'_append_1]

theorem gtow_succ (N : TrioSeq) (r d0 d1 Lb k m : ℕ) :
    gtow N r d0 d1 Lb k (m + 1)
      = gmap N r d0 d1 k (r + 1) Lb ++ gtow N r d0 d1 Lb (k + 1) m := by
  unfold gtow
  rw [List.range'_succ, List.flatMap_cons]

@[simp] theorem gtow_zero (N : TrioSeq) (r d0 d1 Lb k : ℕ) :
    gtow N r d0 d1 Lb k 0 = [] := by
  unfold gtow
  rfl

theorem gmap_ne_nil (N : TrioSeq) (r d0 d1 j a : ℕ) {l : ℕ} (hl : 0 < l) :
    gmap N r d0 d1 j a l ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [gmap_length] at this
  simp at this
  omega

/-- Expansion prefixes are stable in the copy count. -/
theorem gexp_getD_mono {M : TrioSeq} {j0 Lb d0 d1 n p : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
    (hp : p < j0 + n * Lb) :
    (gexp M j0 Lb d0 d1 (n + 1)).getD p (0, 0, 0)
      = (gexp M j0 Lb d0 d1 n).getD p (0, 0, 0) := by
  rcases Nat.lt_or_ge p j0 with hlow | hhigh
  · rw [gexp_getD_low hlen hlow, gexp_getD_low hlen hlow]
  · obtain ⟨k, q, hk, hq, rfl⟩ := gexp_pos_decomp hLb hhigh hp
    rw [gexp_getD_mir hlen (by omega) hq, gexp_getD_mir hlen hk hq]

theorem getD_triple (N : TrioSeq) (p : ℕ) :
    N.getD p (0, 0, 0) = (entry N 0 p, entry N 1 p, entry N 2 p) := rfl

theorem entry_take {N : TrioSeq} {t y x : ℕ} (hx : x < t) :
    entry (N.take t) y x = entry N y x := by
  unfold entry
  rw [getD_take hx]

/-! ## カスケード上のガード合成 -/

/-- **Cascade guard composition**: on a cascade prefix (agreement with the
`take`-anchored expansion), the `le1` guard at a mirror position equals the
guard at the original block position. -/
theorem cascade_le1 {N : TrioSeq} {r Lb d0 d1 k' q' n' : ℕ}
    (hNlen : r + Lb + 1 ≤ N.length)
    (hup : ∀ l, r < l → l ≤ r + Lb → entry N 0 r < entry N 0 l)
    (hd0pos : 0 < d0) (hd0e : entry N 0 (r + Lb) = entry N 0 r + d0)
    (hd1pos : 0 < d1) (hle1q : le1 N r (r + Lb))
    (hk : k' < n') (hq : q' < Lb)
    (hposb : r + (k' * Lb + q') < N.length)
    (hcas : ∀ p, p ≤ r + (k' * Lb + q') → N.getD p (0, 0, 0)
      = (gexp (N.take (r + Lb + 1)) r Lb d0 d1 n').getD p (0, 0, 0)) :
    (le1 N r (r + (k' * Lb + q')) ↔ le1 N r (r + q')) := by
  have hLb : 0 < Lb := by omega
  set Mv := N.take (r + Lb + 1) with hMv
  have hlenv : r + Lb + 1 = Mv.length := by
    rw [hMv, List.length_take]
    omega
  have hagv : ∀ x, x ≤ r + Lb → Mv.getD x (0, 0, 0) = N.getD x (0, 0, 0) := by
    intro x hx
    rw [hMv, getD_take (by omega)]
  have hupv' : ∀ l, r < l → l ≤ r + Lb → entry Mv 0 r < entry Mv 0 l := by
    intro l h1 h2
    rw [hMv, entry_take (by omega), entry_take (by omega)]
    exact hup l h1 h2
  have hd0ev : entry Mv 0 (r + Lb) = entry Mv 0 r + d0 := by
    rw [hMv, entry_take (by omega), entry_take (by omega)]
    exact hd0e
  have hle1v : le1 Mv r (r + Lb) := by
    refine le1_of_agree (X := Mv) (M := N) (by omega) (by omega) ?_ hle1q
    intro x hx
    exact hagv x hx
  have hbnd : k' * Lb + q' < n' * Lb := by
    have h1 : (k' + 1) * Lb ≤ n' * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k' + 1) * Lb = k' * Lb + Lb := Nat.succ_mul k' Lb
    omega
  have hglen : (gexp Mv r Lb d0 d1 n').length = r + n' * Lb :=
    gexp_length hlenv
  have h1 : le1 N r (r + (k' * Lb + q'))
      ↔ le1 (gexp Mv r Lb d0 d1 n') r (r + (k' * Lb + q')) := by
    constructor
    · intro h
      refine le1_of_agree (X := gexp Mv r Lb d0 d1 n') (M := N)
        (by rw [hglen]; omega) (by omega) ?_ h
      intro x hx
      exact (hcas x hx).symm
    · intro h
      refine le1_of_agree (X := N) (M := gexp Mv r Lb d0 d1 n')
        (by omega) (by rw [hglen]; omega) ?_ h
      intro x hx
      exact hcas x hx
  have h2 := gexp_guard_transport (n := n') (k := k') (q := q') hlenv hk hq
    hupv' hd0pos hd0ev hd1pos hle1v
  have h3 : le1 Mv r (r + q') ↔ le1 N r (r + q') := by
    constructor
    · intro h
      refine le1_of_agree (X := N) (M := Mv) (by omega) (by omega) ?_ h
      intro x hx
      exact (hagv x (by omega)).symm
    · intro h
      refine le1_of_agree (X := Mv) (M := N) (by omega) (by omega) ?_ h
      intro x hx
      exact hagv x (by omega)
  rw [h1]
  constructor
  · intro h
    exact (h3.1 (h2.1 h))
  · intro h
    exact h2.2 (h3.2 h)

theorem list_ext_getD {A B : TrioSeq} (hlen : A.length = B.length)
    (h : ∀ i, i < A.length → A.getD i (0, 0, 0) = B.getD i (0, 0, 0)) :
    A = B := by
  refine List.ext_getElem hlen ?_
  intro i h1 h2
  have hh := h i h1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at hh
  simpa using hh

@[simp] theorem seg_length (N : TrioSeq) (a l : ℕ) :
    (seg N a l).length = l := by
  unfold seg
  simp

/-! ## 剥離本体 -/

set_option maxHeartbeats 2000000 in
/-- **The guarded peel**: a self-referential guarded-map bound on a segment
unfolds into the guarded tower. -/
theorem peel2 {N : TrioSeq} {r Lb d0 d1 zl : ℕ}
    (hNlen : r + Lb + 1 ≤ N.length)
    (hLb : 0 < Lb) (hd0pos : 0 < d0) (hd1pos : 0 < d1)
    (hup : ∀ l, r < l → l ≤ r + Lb → entry N 0 r < entry N 0 l)
    (hd0e : entry N 0 (r + Lb) = entry N 0 r + d0)
    (hd1e : entry N 1 (r + Lb) = entry N 1 r + d1)
    (hz2 : entry N 2 (r + Lb) = entry N 2 r)
    (hle1q : le1 N r (r + Lb)) :
    ∀ (fuel k xa xl : ℕ), xl ≤ fuel → 1 ≤ k →
    xa = r + k * Lb + 1 →
    xa + xl ≤ N.length →
    (∀ p, p < xa → N.getD p (0, 0, 0)
      = (gexp (N.take (r + Lb + 1)) r Lb d0 d1 (k + 1)).getD p (0, 0, 0)) →
    sle (seg N xa xl)
      (gmap N r d0 d1 k (r + 1) Lb
        ++ (gmap N r d0 d1 1 xa xl ++ gmap N r d0 d1 1 (xa + xl) zl)) →
    ∃ m, 1 ≤ m ∧ sle (seg N xa xl) (gtow N r d0 d1 Lb k m) := by
  have hlenv : r + Lb + 1 = (N.take (r + Lb + 1)).length := by
    rw [List.length_take]
    omega
  intro fuel
  induction fuel with
  | zero =>
    intro k xa xl hxl _ _ _ _ _
    have hxl0 : xl = 0 := by omega
    subst hxl0
    refine ⟨1, le_rfl, Or.inr ?_⟩
    show seqlex (seg N xa 0) (gtow N r d0 d1 Lb k 1)
    rw [show seg N xa 0 = [] from rfl, gtow_succ, gtow_zero, List.append_nil]
    exact gmap_ne_nil N r d0 d1 k (r + 1) hLb
  | succ fuel ih =>
    intro k xa xl hxl hk1 hxa hxrange hcas hinv
    by_cases hpre : ∃ X', seg N xa xl = gmap N r d0 d1 k (r + 1) Lb ++ X'
    case neg =>
      push Not at hpre
      refine ⟨1, le_rfl, Or.inr ?_⟩
      rw [gtow_succ, gtow_zero, List.append_nil]
      have h := seqlex_of_sle_not_prefix hinv hpre []
      rwa [List.append_nil] at h
    case pos =>
      obtain ⟨X', hX'⟩ := hpre
      have hlen1 : xl = Lb + X'.length := by
        have h := congrArg List.length hX'
        rw [seg_length, List.length_append, gmap_length] at h
        omega
      have hsplit : seg N xa xl = seg N xa Lb ++ seg N (xa + Lb) X'.length := by
        rw [show xl = Lb + X'.length from hlen1, seg_append]
      have hfirst : seg N xa Lb = gmap N r d0 d1 k (r + 1) Lb
          ∧ seg N (xa + Lb) X'.length = X' := by
        rw [hsplit] at hX'
        exact List.append_inj hX' (by rw [seg_length, gmap_length])
      -- the newly learned cascade values
      have hcasX : ∀ i, i < Lb → N.getD (xa + i) (0, 0, 0)
          = (entry N 0 (r + 1 + i) + k * d0,
             entry N 1 (r + 1 + i)
               + (if le1 N r (r + 1 + i) then k * d1 else 0),
             entry N 2 (r + 1 + i)) := by
        intro i hi
        have h := congrArg (fun l => l.getD i (0, 0, 0)) hfirst.1
        dsimp only at h
        rw [seg_getD hi, gmap_getD hi] at h
        rw [getD_triple]
        exact h
      -- take-agreement helpers
      have hMvag : ∀ x, x ≤ r + Lb →
          (N.take (r + Lb + 1)).getD x (0, 0, 0) = N.getD x (0, 0, 0) := by
        intro x hx
        exact getD_take (by omega)
      have hle1iff : ∀ x, x ≤ r + Lb →
          (le1 (N.take (r + Lb + 1)) r x ↔ le1 N r x) := by
        intro x hx
        constructor
        · intro h
          exact le1_of_agree (X := N) (M := N.take (r + Lb + 1)) (by omega)
            (by omega) (fun y hy => (hMvag y (by omega)).symm) h
        · intro h
          exact le1_of_agree (X := N.take (r + Lb + 1)) (M := N) (by omega)
            (by omega) (fun y hy => hMvag y (by omega)) h
      -- extend the cascade to the freshly matched copy
      have hcas' : ∀ p, p < xa + Lb → N.getD p (0, 0, 0)
          = (gexp (N.take (r + Lb + 1)) r Lb d0 d1 (k + 2)).getD p (0, 0, 0) := by
        intro p hp
        rcases Nat.lt_or_ge p xa with hlow | hhigh
        · rw [hcas p hlow]
          have hmono := gexp_getD_mono (M := N.take (r + Lb + 1)) (j0 := r)
            (Lb := Lb) (d0 := d0) (d1 := d1) (n := k + 1) (p := p) hlenv hLb (by
            have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
            omega)
          exact hmono.symm
        · have hiLb : p - xa < Lb := by omega
          have hpe : p = xa + (p - xa) := by omega
          set i := p - xa with hidef
          rw [hpe, hcasX i hiLb]
          rcases Nat.lt_or_ge (1 + i) Lb with hcase | hcase
          · -- mirror (k, 1+i) of copy k
            rw [show xa + i = r + (k * Lb + (1 + i)) from by omega,
              gexp_getD_mir hlenv (show k < k + 2 from by omega) hcase,
              show r + (1 + i) = r + 1 + i from by omega]
            have e0 : entry (N.take (r + Lb + 1)) 0 (r + 1 + i)
                = entry N 0 (r + 1 + i) := entry_take (by omega)
            have e1 : entry (N.take (r + Lb + 1)) 1 (r + 1 + i)
                = entry N 1 (r + 1 + i) := entry_take (by omega)
            have e2 : entry (N.take (r + Lb + 1)) 2 (r + 1 + i)
                = entry N 2 (r + 1 + i) := entry_take (by omega)
            rw [e0, e1, e2]
            by_cases hg : le1 N r (r + 1 + i)
            · rw [if_pos hg, if_pos ((hle1iff (r + 1 + i) (by omega)).2 hg)]
            · rw [if_neg hg, if_neg (fun hc =>
                hg ((hle1iff (r + 1 + i) (by omega)).1 hc))]
          · -- the head of copy k+1
            have hie : 1 + i = Lb := by omega
            rw [show xa + i = r + ((k + 1) * Lb + 0) from by
                have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
                omega,
              gexp_getD_mir hlenv (show k + 1 < k + 2 from by omega) hLb]
            simp only [Nat.add_zero]
            have e0 : entry (N.take (r + Lb + 1)) 0 r = entry N 0 r :=
              entry_take (by omega)
            have e1 : entry (N.take (r + Lb + 1)) 1 r = entry N 1 r :=
              entry_take (by omega)
            have e2 : entry (N.take (r + Lb + 1)) 2 r = entry N 2 r :=
              entry_take (by omega)
            rw [e0, e1, e2, if_pos (le1_refl (by omega)),
              show r + 1 + i = r + Lb from by omega,
              if_pos hle1q]
            have hsd : (k + 1) * d0 = k * d0 + d0 := Nat.succ_mul k d0
            have hsd1 : (k + 1) * d1 = k * d1 + d1 := Nat.succ_mul k d1
            refine Prod.ext ?_ (Prod.ext ?_ ?_)
            · dsimp only
              omega
            · dsimp only
              omega
            · dsimp only
              omega
      -- the guard identity on the matched copy
      have hguard : ∀ i, i < Lb →
          (le1 N r (xa + i) ↔ le1 N r (r + 1 + i)) := by
        intro i hi
        rcases Nat.lt_or_ge (1 + i) Lb with hcase | hcase
        · have h := cascade_le1 (n' := k + 2) (k' := k) (q' := 1 + i)
            hNlen hup hd0pos hd0e hd1pos hle1q (by omega) hcase
            (by omega)
            (fun p hp => hcas' p (by omega))
          rw [show r + (k * Lb + (1 + i)) = xa + i from by omega,
            show r + (1 + i) = r + 1 + i from by omega] at h
          exact h
        · have hie : 1 + i = Lb := by omega
          have h := cascade_le1 (n' := k + 2) (k' := k + 1) (q' := 0)
            hNlen hup hd0pos hd0e hd1pos hle1q (by omega) hLb
            (by
              have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
              omega)
            (by
              intro p hp
              refine hcas' p ?_
              have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
              omega)
          rw [show r + ((k + 1) * Lb + 0) = xa + i from by
              have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
              omega,
            Nat.add_zero] at h
          constructor
          · intro _
            rw [show r + 1 + i = r + Lb from by omega]
            exact hle1q
          · intro _
            exact h.2 (le1_refl (by omega))
      -- THE COMPOSITION: shifting the matched copy once more
      have hcomp : gmap N r d0 d1 1 xa Lb
          = gmap N r d0 d1 (k + 1) (r + 1) Lb := by
        refine list_ext_getD (by rw [gmap_length, gmap_length]) ?_
        intro i h1
        rw [gmap_length] at h1
        rw [gmap_getD h1, gmap_getD h1]
        have h0 : entry N 0 (xa + i) = entry N 0 (r + 1 + i) + k * d0 := by
          show (N.getD (xa + i) (0, 0, 0)).1 = _
          rw [hcasX i h1]
        have h1' : entry N 1 (xa + i) = entry N 1 (r + 1 + i)
            + (if le1 N r (r + 1 + i) then k * d1 else 0) := by
          show (N.getD (xa + i) (0, 0, 0)).2.1 = _
          rw [hcasX i h1]
        have h2' : entry N 2 (xa + i) = entry N 2 (r + 1 + i) := by
          show (N.getD (xa + i) (0, 0, 0)).2.2 = _
          rw [hcasX i h1]
        have hsd : (k + 1) * d0 = k * d0 + d0 := Nat.succ_mul k d0
        have hsd1 : (k + 1) * d1 = k * d1 + d1 := Nat.succ_mul k d1
        by_cases hg : le1 N r (r + 1 + i)
        · rw [if_pos ((hguard i h1).2 hg), if_pos hg]
          rw [if_pos hg] at h1'
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · dsimp only
            omega
          · dsimp only
            omega
          · dsimp only
            omega
        · rw [if_neg (fun hc => hg ((hguard i h1).1 hc)), if_neg hg]
          rw [if_neg hg] at h1'
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · dsimp only
            omega
          · dsimp only
            omega
          · dsimp only
            omega
      -- strip and recurse
      have hinv' : sle X' (gmap N r d0 d1 1 xa xl
          ++ gmap N r d0 d1 1 (xa + xl) zl) := by
        rw [hX'] at hinv
        exact (sle_append_cancel _).1 hinv
      have hinv2 : sle (seg N (xa + Lb) X'.length)
          (gmap N r d0 d1 (k + 1) (r + 1) Lb
            ++ (gmap N r d0 d1 1 (xa + Lb) X'.length
              ++ gmap N r d0 d1 1 ((xa + Lb) + X'.length) zl)) := by
        rw [hfirst.2]
        rw [show xl = Lb + X'.length from hlen1, gmap_append, hcomp,
          List.append_assoc,
          show xa + (Lb + X'.length) = xa + Lb + X'.length from by omega]
          at hinv'
        exact hinv'
      obtain ⟨m, hm1, hm⟩ := ih (k + 1) (xa + Lb) X'.length
        (by omega) (by omega)
        (by
          have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
          omega)
        (by omega)
        (by
          intro p hp
          exact hcas' p hp)
        hinv2
      refine ⟨m + 1, by omega, ?_⟩
      rw [gtow_succ, hX']
      refine (sle_append_cancel _).2 ?_
      rw [← hfirst.2]
      exact hm

end TRIO
