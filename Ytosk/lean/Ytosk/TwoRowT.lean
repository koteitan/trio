/-
**2 行で最後の列を落とすと値が下がる（先頭部分の降下 (T)、行 2 が 0 の場合）。**

正規形（すべての値が標準形）と、兄弟の値が降順であること（和が連結になる）を仮定に置く。
経路の子は最後の子（`children_le_of_anc_last`）なので、q では打ち切りの段（`spArg_frame_prefix`）、
その上では経路の子の値が真に下がる添字の同じ段（`spArg_frame_same`）になる。
-/
import Ytosk.Path
import Ytosk.SP

namespace Ytosk

open T

/-! ## 和 -/

theorem sumN_snoc (l : List T) (c : T) : sumN (l ++ [c]) = sf (add (sumN l) c) := by
  unfold sumN; rw [List.foldl_append]; rfl

/-- A single summand. -/
def Single (t : T) : Prop := isOT t = true ∧ ∃ s y, t = psi s y z

/-- The fold of `sumN` from an accumulator over a non-increasing list of single summands concatenates. -/
theorem foldl_dec : ∀ (l : List T) (acc : T), isOT acc = true → (∀ t ∈ l, Single t) →
    (summands acc ++ l).Pairwise (fun a b => b ≤ a) →
    isOT (l.foldl (fun a b => sf (add a b)) acc) = true ∧
      summands (l.foldl (fun a b => sf (add a b)) acc) = summands acc ++ l
  | [], acc, hacc, _, _ => by simpa using hacc
  | c :: l, acc, hacc, hs, hp => by
    obtain ⟨hc, s, y, rfl⟩ := hs _ (List.mem_cons_self)
    have hp' := List.pairwise_append.mp hp
    have happ : isOT (app acc (psi s y z)) = true := by
      apply isOT_app_of hacc hc
      intro q hq
      exact hp'.2.2 q hq _ (List.mem_cons_self)
    have hstep : sf (add acc (psi s y z)) = app acc (psi s y z) := by
      rw [add_eq_app happ, sf_ot happ]
    have hsum : summands (app acc (psi s y z)) = summands acc ++ [psi s y z] := by
      rw [summands_app]; rfl
    simp only [List.foldl_cons, hstep]
    have := foldl_dec l (app acc (psi s y z)) happ (fun t ht => hs t (List.mem_cons_of_mem _ ht))
      (by rw [hsum, List.append_assoc]; exact hp)
    rw [this.2, hsum, List.append_assoc] at *
    exact ⟨this.1, rfl⟩

/-- **A non-increasing sum of single summands is their concatenation.** -/
theorem sumN_dec (l : List T) (hs : ∀ t ∈ l, Single t) (hp : l.Pairwise (fun a b => b ≤ a)) :
    isOT (sumN l) = true ∧ summands (sumN l) = l := by
  have := foldl_dec l z rfl hs (by simpa [summands] using hp)
  simpa [sumN, summands] using this

/-! ## 2 行の評価器の補題 -/

theorem vr_take (M : Mat) {k : Nat} : ∀ i, i < k → vr (M.take k) i = vr M i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    rw [vr, vr]
    rw [entry_take M 1 hi]
    split
    · rfl
    · have e := par_take M 1 i hi
      split <;> split
      · rfl
      · next h1 m h2 => rw [e, h2] at h1; cases h1
      · next m h1 h2 => rw [e, h2] at h1; cases h1
      · next m h1 m' h2 =>
        rw [e, h2] at h1; cases h1
        rw [ih m (par_lt M 1 i m h2) (by have := par_lt M 1 i m h2; omega)]

theorem isOT_nT : ∀ k, isOT (nT k) = true
  | 0 => rfl
  | k + 1 => by
    show isOT (sf (add (nT k) one)) = true
    have h := isOT_add (isOT_nT k) isOT_one
    rw [sf_ot h]; exact h

theorem anc0_up {M : Mat} {c j x : Nat} (hp : par M 0 c = some j) (h : Anc0 M c x) : Anc0 M j x := by
  induction h with
  | refl => exact Anc0.step hp (Anc0.refl j)
  | step hq _ ih => exact Anc0.step hq ih

/-- Below an ancestor `h ≠ b` of `b` there is the child of `h` on the way to `b`. -/
theorem anc0_child {M : Mat} {h b : Nat} (hA : Anc0 M h b) (hne : h ≠ b) :
    ∃ p, par M 0 p = some h ∧ Anc0 M p b := by
  induction hA with
  | refl => exact absurd rfl hne
  | @step b' c hq hA' ih =>
    by_cases hh : h = b'
    · subst hh; exact ⟨c, hq, Anc0.refl c⟩
    · obtain ⟨p, hp, hpb⟩ := ih hh
      exact ⟨p, hp, Anc0.step hq hpb⟩

/-- **Locality.** A column that is not an ancestor of `x` keeps its value in `M.take x`. -/
theorem o2r_take_off {M : Mat} {x : Nat} (hx : x + 1 = M.length) :
    ∀ j, j < x → ¬ Anc0 M j x → o2r (M.take x) j = o2r M j := by
  have key : ∀ m j, x - j ≤ m → j < x → ¬ Anc0 M j x → o2r (M.take x) j = o2r M j := by
    intro m
    induction m with
    | zero => intro j h1 h2; omega
    | succ m ih =>
      intro j hm hj hA
      apply o2r_congr (vr_take M j hj)
      have hch : ∀ c ∈ children M j, c < x ∧ ¬ Anc0 M c x := by
        intro c hc
        have hpc : par M 0 c = some j := by
          unfold children at hc; rw [List.mem_filter] at hc; simpa using hc.2
        have hcl := (mem_children hc).2
        refine ⟨?_, fun hcA => hA (anc0_up hpc hcA)⟩
        rcases Nat.lt_or_ge c x with h | h
        · exact h
        · have : c = x := by omega
          subst this; exact absurd (anc0_up hpc (Anc0.refl c)) hA
      rw [children_take, List.filter_eq_self.mpr (fun c hc => by simpa using (hch c hc).1)]
      apply List.map_congr_left
      intro c hc
      have hjc := (mem_children hc).1
      exact ih c (by omega) (hch c hc).1 (hch c hc).2
  exact fun j => key _ j (Nat.le_refl _)

/-! ## 経路 -/

theorem anc0_par {M : Mat} {b c b' : Nat} (h : Anc0 M b c) (hne : b ≠ c) (hp : par M 0 c = some b') :
    Anc0 M b b' := by
  cases h with
  | refl => exact absurd rfl hne
  | step hq hA => rw [hp] at hq; cases hq; exact hA

/-- Ancestors of a column are comparable. -/
theorem anc0_total {M : Mat} {a b x : Nat} (ha : Anc0 M a x) (hb : Anc0 M b x) :
    Anc0 M a b ∨ Anc0 M b a := by
  induction ha with
  | refl => exact Or.inr hb
  | @step b' c hq hA ih =>
    by_cases hbc : b = c
    · subst hbc; exact Or.inl (Anc0.step hq hA)
    · exact ih (anc0_par hb hbc hq)

/-- A sorted list whose largest element is `c` ends with `c`. -/
theorem split_last_max : ∀ (l : List Nat) (c : Nat), l.Pairwise (· < ·) → c ∈ l → (∀ d ∈ l, d ≤ c) →
    l = l.filter (fun d => decide (d < c)) ++ [c]
  | [], _, _, h, _ => absurd h (by simp)
  | a :: l, c, hp, hc, hle => by
    rw [List.pairwise_cons] at hp
    by_cases hac : a = c
    · subst hac
      have : l = [] := by
        cases l with
        | nil => rfl
        | cons d l' =>
          have h1 := hp.1 d (List.mem_cons_self)
          have h2 := hle d (List.mem_cons_of_mem _ List.mem_cons_self)
          omega
      subst this; simp
    · have hcl : c ∈ l := by
        rcases List.mem_cons.mp hc with h | h
        · exact absurd h.symm hac
        · exact h
      have ih := split_last_max l c hp.2 hcl (fun d hd => hle d (List.mem_cons_of_mem _ hd))
      have hlt : a < c := by have := hle a List.mem_cons_self; omega
      rw [List.filter_cons, if_pos (by simpa using hlt)]
      conv => lhs; rw [ih]
      rfl

theorem children_sorted (M : Mat) (h : Nat) : (children M h).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem mem_children_iff {M : Mat} {h c : Nat} : c ∈ children M h ↔ c < M.length ∧ par M 0 c = some h := by
  unfold children; rw [List.mem_filter, List.mem_range]; simp

/-- `o2r` as `ψ_v(spArg)`. -/
theorem o2r_spArg {M : Mat} {n : Nat} (hv : isOT (vr M n) = true)
    (hS : isOT (sumN ((children M n).map (o2r M))) = true) :
    o2r M n = psi (vr M n) (spArg (vr M n) z (sumN ((children M n).map (o2r M)))) z := by
  rw [o2r_eq]
  show add (sp (sf (vr M n)) z (sf _)) (sf z) = _
  rw [sf_ot hv, sf_ot hS, sp_eq_spArg]
  rfl

/-- Two-row matrices with `F1`, standard values and non-increasing siblings. -/
structure Good2 (M : Mat) : Prop where
  f1 : F1 M
  ot : ∀ i, isOT (o2r M i) = true
  dec : ∀ h, ((children M h).map (o2r M)).Pairwise (fun a b => b ≤ a)

theorem single_o2r {M : Mat} (hG : Good2 M) (i : Nat) : Single (o2r M i) := by
  refine ⟨hG.ot i, ?_⟩
  rw [o2r_eq]
  show ∃ s y, add (sp (sf (vr M i)) z (sf _)) (sf z) = psi s y z
  rw [sp_eq_spArg]; exact ⟨_, _, rfl⟩

theorem isOT_vr {M : Mat} (hF : F1 M) (i : Nat) : isOT (vr M i) = true := by
  rw [vr_eq_nT hF]; exact isOT_nT _

theorem sumN_children {M : Mat} (hG : Good2 M) (h : Nat) :
    isOT (sumN ((children M h).map (o2r M))) = true ∧
      summands (sumN ((children M h).map (o2r M))) = (children M h).map (o2r M) :=
  sumN_dec _ (fun t ht => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hG i) (hG.dec h)

/-- The subscript of `o2r` is `vr`. -/
theorem o2r_sub {M : Mat} (hG : Good2 M) (i : Nat) : ∃ y, o2r M i = psi (vr M i) y z :=
  ⟨_, o2r_spArg (isOT_vr hG.f1 i) (sumN_children hG i).1⟩

theorem sumN_snoc_dec {l : List T} {c : T} (hs : ∀ t ∈ l ++ [c], Single t)
    (hp : (l ++ [c]).Pairwise (fun a b => b ≤ a)) : sumN (l ++ [c]) = app (sumN l) c := by
  have hp' := List.pairwise_append.mp hp
  obtain ⟨hS, hsum⟩ := sumN_dec l (fun t ht => hs t (List.mem_append_left _ ht)) hp'.1
  obtain ⟨hc, s, y, rfl⟩ := hs _ (List.mem_append_right _ (List.mem_singleton_self _))
  have happ : isOT (app (sumN l) (psi s y z)) = true := by
    apply isOT_app_of hS hc
    intro q hq
    rw [hsum] at hq
    exact hp'.2.2 q hq _ (List.mem_singleton_self _)
  rw [sumN_snoc, add_eq_app happ, sf_ot happ]

/-- **Truncation lowers the path (two rows).** -/
theorem o2r_take_anc {M : Mat} {x : Nat} (hx : x + 1 = M.length) (hG : Good2 M)
    (hG' : Good2 (M.take x)) :
    ∀ p, Anc0 M p x → p < x → o2r (M.take x) p < o2r M p := by
  have key : ∀ m p, x - p ≤ m → Anc0 M p x → p < x → o2r (M.take x) p < o2r M p := by
    intro m
    induction m with
    | zero => intro p h1 _ h3; omega
    | succ m ih =>
      intro p hm hA hpx
      obtain ⟨c, hc, hcA⟩ := anc0_child hA (by omega)
      have hcx := hcA.le
      have hpc := par_lt M 0 c p hc
      have hle := children_le_of_anc_last hcA hx hc
      have hcmem : c ∈ children M p := mem_children_iff.mpr ⟨by omega, hc⟩
      have hsplit := split_last_max _ c (children_sorted M p) hcmem hle
      -- the earlier children keep their values
      have hoff : ∀ d ∈ (children M p).filter (fun d => decide (d < c)),
          o2r (M.take x) d = o2r M d := by
        intro d hd
        rw [List.mem_filter] at hd
        have hdc : d < c := by simpa using hd.2
        have hdp := mem_children_iff.mp hd.1
        apply o2r_take_off hx d (by omega)
        intro hdA
        rcases anc0_total hdA hcA with h | h
        · have := (anc0_par h (by omega) hc).le; have := par_lt M 0 d p hdp.2; omega
        · have := h.le; omega
      have hv : vr (M.take x) p = vr M p := vr_take M p hpx
      have hvot := isOT_vr hG.f1 p
      rw [o2r_spArg (isOT_vr hG'.f1 p) (sumN_children hG' p).1,
        o2r_spArg hvot (sumN_children hG p).1, hv]
      rw [psi_lt_psi_z_iff]; right; refine ⟨rfl, ?_⟩
      -- the children lists
      set C := (children M p).filter (fun d => decide (d < c)) with hCdef
      have hCv : C.map (o2r (M.take x)) = C.map (o2r M) := List.map_congr_left hoff
      have hsing : ∀ (N : Mat), Good2 N → ∀ (l : List Nat), ∀ t ∈ l.map (o2r N), Single t := by
        intro N hN l t ht
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hN i
      have hsumM : sumN ((children M p).map (o2r M)) = app (sumN (C.map (o2r M))) (o2r M c) := by
        have hd := hG.dec p
        simp only [hsplit, List.map_append, List.map_cons, List.map_nil] at hd ⊢
        refine sumN_snoc_dec ?_ hd
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact hsing M hG C t ht
        · rw [List.mem_singleton] at ht; subst ht; exact single_o2r hG c
      have hch' : children (M.take x) p = (C ++ [c]).filter (fun d => decide (d < x)) := by
        rw [children_take, ← hsplit]
      rw [hsumM, spArg_app]
      obtain ⟨yw, hyw⟩ := o2r_sub hG c
      have hw : isOT (psi (vr M c) yw z) = true := by rw [← hyw]; exact hG.ot c
      rcases Nat.lt_or_ge c x with hcx' | hcx'
      · -- the path child stays, with a smaller value
        have hfil : (C ++ [c]).filter (fun d => decide (d < x)) = C ++ [c] := by
          apply List.filter_eq_self.mpr
          intro d hd
          rcases List.mem_append.mp hd with hd | hd
          · rw [hCdef, List.mem_filter] at hd
            have : d < c := by simpa using hd.2
            simpa using (show d < x by omega)
          · rw [List.mem_singleton] at hd; subst hd; simpa using hcx'
        simp only [hch', hfil, List.map_append, List.map_cons, List.map_nil, hCv]
        have hlt := ih c (by omega) hcA hcx'
        obtain ⟨yu, hyu⟩ := o2r_sub hG' c
        rw [vr_take M c hcx'] at hyu
        have hu : isOT (psi (vr M c) yu z) = true := by rw [← hyu]; exact hG'.ot c
        have hd' := hG'.dec p
        simp only [hch', hfil, List.map_append, List.map_cons, List.map_nil, hCv] at hd'
        rw [sumN_snoc_dec (by
          intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · rw [← hCv] at ht; exact hsing _ hG' _ t ht
          · rw [List.mem_singleton] at ht; subst ht; exact single_o2r hG' c) hd', spArg_app]
        rw [hyu, hyw]
        rw [hyu, hyw, psi_lt_psi_z_iff] at hlt
        rcases hlt with h | ⟨_, hlt⟩
        · exact absurd h (lt_irrefl' _)
        · exact spArg_frame_same hu hw hlt (z_le _) (by rw [app_z_right]; rfl) (by rw [app_z_right]; rfl)
      · -- the path child is the last column, removed
        have hcx2 : c = x := by omega
        have hfil : (C ++ [c]).filter (fun d => decide (d < x)) = C := by
          rw [List.filter_append, List.filter_eq_self.mpr, hcx2]
          · simp
          · intro d hd
            rw [hCdef, List.mem_filter] at hd
            have : d < c := by simpa using hd.2
            simpa using (show d < x by omega)
        rw [hch', hfil, hCv, hyw]
        exact spArg_frame_prefix hw (by rw [app_z_right]; rfl)
  exact fun p => key _ p (Nat.le_refl _)

end Ytosk
