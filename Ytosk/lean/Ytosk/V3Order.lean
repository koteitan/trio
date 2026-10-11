/-
**翻訳は順序を保つ（段 1 を仮定して）。**

段 1 `Desc3`（SRO 以外の標準形の値は標準形で、展開で下がる）を仮定すると、SRO より小さい 2 つの標準形
B < A（列の辞書式 `seqlex`）について、B の値 < A の値。

- 整礎性は段 1 から（`terminates_of_desc3`）。
- 届くこと（`reach_of_seqlex`）: B < A なら B は A から 1 回以上の展開で届く。trio の共終性
  `trio_cofinality`（`ST_TS` の上で）と、Ytosk の `expand` と trio の `oper` の一致 `expand_eq_oper` から。
  Ytosk の標準形は trio の `ST_TS` に入る（`std_stts`: SRO は対角 D_2 から 26 回の展開で届く）。
- 値の比較（`order_pres`）: 届く道に沿って段 1 の降下をつなぐ。
-/
import Ytosk.V3Top
import Ytosk.Bridge
import Wset
import Seqlex

namespace Ytosk

open Relation

/-! ## Ytosk の標準形は trio の標準形 -/

theorem expand_nil' (n : Nat) : expand [] n = [] := by simp [expand]

theorem foldl_expand_nil : ∀ ns : List Nat, ns.foldl expand [] = []
  | [] => rfl
  | n :: ns => by simp only [List.foldl_cons, expand_nil']; exact foldl_expand_nil ns

/-- Ytosk's expansion of a one-column matrix is empty. -/
theorem expand_len_one {M : Mat} (h : M.length = 1) (n : Nat) : expand M n = [] := by
  obtain ⟨c, rfl⟩ : ∃ c, M = [c] := by
    match M, h with
    | [c], _ => exact ⟨c, rfl⟩
  unfold expand
  simp only [List.length_singleton, Nat.sub_self, List.take_zero]
  split
  · rfl
  · split
    · rfl
    · rename_i r hr
      exact absurd (par_lt _ _ _ _ hr) (Nat.not_lt_zero _)

theorem pred_prefix (X : TRIO.TrioSeq) : ∃ m, TRIO.Pred X = X.take m := by
  unfold TRIO.Pred
  split
  · exact ⟨X.length, by simp⟩
  · exact ⟨X.length - 1, List.dropLast_eq_take⟩

open Classical in
/-- `X⟦0⟧` is a prefix of `X`. -/
theorem oper_zero_prefix (X : TRIO.TrioSeq) : ∃ m, X⟦0⟧ = X.take m := by
  unfold TRIO.oper
  simp only
  split
  · exact ⟨X.length, by simp⟩
  split
  · exact pred_prefix X
  split
  · exact pred_prefix X
  · exact ⟨TRIO.parent X (TRIO.srow X (X.length - 1)) (X.length - 1), by simp⟩

theorem stts_dropLast {X : TRIO.TrioSeq} (h : TRIO.ST_TS X) (hl : 1 < X.length) :
    TRIO.ST_TS X.dropLast := by
  rw [← TRIO.Wset.oper_one_eq_dropLast hl]; exact TRIO.ST_TS.oper h le_rfl

/-- `ST_TS` is closed under nonempty prefixes. -/
theorem stts_take {X : TRIO.TrioSeq} (h : TRIO.ST_TS X) :
    ∀ k, 1 ≤ k → k ≤ X.length → TRIO.ST_TS (X.take k) := by
  have key : ∀ m k, X.length - k ≤ m → 1 ≤ k → k ≤ X.length → TRIO.ST_TS (X.take k) := by
    intro m
    induction m with
    | zero =>
      intro k hm hk1 hk
      rw [show k = X.length by omega, List.take_length]; exact h
    | succ m ih =>
      intro k hm hk1 hk
      rcases Nat.eq_or_lt_of_le hk with hkx | hkx
      · rw [hkx, List.take_length]; exact h
      · have hN := ih (k + 1) (by omega) (by omega) hkx
        have hl : (X.take (k + 1)).length = k + 1 := by rw [List.length_take]; omega
        have := stts_dropLast hN (by omega)
        rwa [List.dropLast_eq_take, hl, List.take_take, show min (k + 1 - 1) (k + 1) = k by omega]
          at this
  exact fun k hk1 hk => key (X.length - k) k (le_refl _) hk1 hk

/-- One Ytosk expansion of a trio standard form is empty or a trio standard form. -/
theorem stts_exp_or {X : Mat} (h : TRIO.ST_TS X) (n : Nat) :
    expand X n = [] ∨ TRIO.ST_TS (expand X n) := by
  have h1 := TRIO.stps_len_pos h
  by_cases hl : 2 ≤ X.length
  · rw [expand_eq_oper X n hl]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨m, hm⟩ := oper_zero_prefix X
      rw [hm]
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · left; simp
      · right
        by_cases hmX : m ≤ X.length
        · exact stts_take h m hm0 hmX
        · rw [List.take_of_length_le (by omega)]; exact h
    · right; exact TRIO.ST_TS.oper h hn
  · left; exact expand_len_one (by omega) n

theorem stts_foldl : ∀ (ns : List Nat) (X : Mat), TRIO.ST_TS X →
    ns.foldl expand X = [] ∨ TRIO.ST_TS (ns.foldl expand X)
  | [], _, h => Or.inr h
  | n :: ns, X, h => by
    simp only [List.foldl_cons]
    rcases stts_exp_or h n with he | h'
    · left; rw [he]; exact foldl_expand_nil ns
    · exact stts_foldl ns _ h'

/-- A path from the capped diagonal `D_2 = (0,0,0)(1,1,1)(2,2,1)` to SRO (copy counts). -/
def sroPathY : List Nat := [2,1,3,2,1,2,2,2,1,1,1,2,2,1,1,1,2,1,2,1,1,1,2,1,1,1]

theorem sroPathY_run : sroPathY.foldl expand (TRIO.diagSeqT 0 2) = SRO := by decide

/-- **Every Ytosk standard form is empty or a trio standard form.** -/
theorem std_stts {M : Mat} (hM : Std M) : M = [] ∨ TRIO.ST_TS M := by
  induction hM with
  | sro =>
    have := stts_foldl sroPathY _ (TRIO.ST_TS.diag 2)
    rwa [sroPathY_run] at this
  | exp n _ ih =>
    rcases ih with rfl | h
    · left; exact expand_nil' n
    · exact stts_exp_or h n

/-! ## 届くこと -/

theorem seqlex_irrefl : ∀ X : TRIO.TrioSeq, ¬ TRIO.seqlex X X
  | [] => by simp [TRIO.seqlex]
  | p :: X => by
    rw [TRIO.seqlex_cons_cons]
    rintro (h | ⟨_, h⟩)
    · simp [TRIO.collt] at h
    · exact seqlex_irrefl X h

theorem eq_of_translate_eq {B C : TRIO.TrioSeq} (hB : TRIO.ST_TS B) (hC : TRIO.ST_TS C)
    (e : TRIO.translate B = TRIO.translate C) : B = C := by
  by_contra hne
  rcases TRIO.seqlex_total B C with h | h | h
  · exact hne h
  · have := (TRIO.olt_ST_iff_seqlex hB hC hne).mpr h
    rw [e] at this; exact TRIO.Three.olt_irrefl _ this
  · have := (TRIO.olt_ST_iff_seqlex hC hB (Ne.symm hne)).mpr h
    rw [e] at this; exact TRIO.Three.olt_irrefl _ this

theorem acc_not_self {α : Type _} {r : α → α → Prop} {a : α} (h : Acc r a) : ¬ r a a := by
  induction h with
  | intro a _ ih => exact fun haa => ih a haa haa

/-- **Below a standard form, every smaller standard form is reached by expansion** (given step 1). -/
theorem reach_of_seqlex (hD : Desc3) :
    ∀ A, Std A → ∀ B, Std B → B ≠ [] → TRIO.seqlex B A → TransGen Step' B A := by
  intro A
  induction A using (terminates_of_desc3 hD).induction with
  | _ A ih =>
  intro hA B hB hBE hlt
  have hAE : A ≠ [] := by
    rintro rfl
    match B, hBE with
    | _ :: _, _ => simp [TRIO.seqlex] at hlt
  have hAs : TRIO.ST_TS A := (std_stts hA).resolve_left hAE
  have hBs : TRIO.ST_TS B := (std_stts hB).resolve_left hBE
  have hne : B ≠ A := by rintro rfl; exact seqlex_irrefl _ hlt
  have holt := (TRIO.olt_ST_iff_seqlex hBs hAs hne).mpr hlt
  obtain ⟨n, hn, hle⟩ := TRIO.trio_cofinality hAs hBs holt
  have hl : 2 ≤ A.length := by
    by_contra hl
    have h1 : A = [(0, 0, 0)] :=
      TRIO.Wset.stts_len_one hAs (by have := TRIO.stps_len_pos hAs; omega)
    have hh := TRIO.stps_head hBs
    subst h1
    match B, hBE, hh with
    | b :: B', _, hh =>
      simp only [List.headD_cons] at hh
      subst hh
      rw [TRIO.seqlex_cons_cons] at hlt
      rcases hlt with h | ⟨_, h⟩
      · simp [TRIO.collt] at h
      · cases B' with
        | nil => exact h rfl
        | cons _ _ => exact h
  have hC : Step' (expand A n) A := ⟨hA, hAE, n, rfl⟩
  have hCs : TRIO.ST_TS (expand A n) := by
    rw [expand_eq_oper A n hl]; exact TRIO.ST_TS.oper hAs hn
  rw [← expand_eq_oper A n hl] at hle
  rcases hle with hlt' | heq
  · have hneC : B ≠ expand A n := by rintro rfl; exact TRIO.Three.olt_irrefl _ hlt'
    have := (TRIO.olt_ST_iff_seqlex hBs hCs hneC).mp hlt'
    exact TransGen.tail (ih _ hC (Std.exp n hA) B hB hBE this) hC
  · rw [eq_of_translate_eq hBs hCs heq]
    exact TransGen.single hC

/-! ## 値の比較 -/

/-- Every standard form is empty or reached from SRO. -/
theorem std_reach {A : Mat} (hA : Std A) : A = [] ∨ ReflTransGen Step' A SRO := by
  induction hA with
  | sro => exact Or.inr ReflTransGen.refl
  | @exp M n hM ih =>
    by_cases hME : M = []
    · left; rw [hME]; exact expand_nil' n
    · rcases ih with h | h
      · exact absurd h hME
      · right; exact ReflTransGen.head ⟨hM, hME, n, rfl⟩ h

/-- No expansion step lands on SRO (given step 1). -/
theorem step_ne_sro (hD : Desc3) {C D : Mat} (h : Step' D C) : D ≠ SRO := by
  rintro rfl
  rcases std_reach h.1 with hE | hR
  · exact h.2.1 hE
  · exact acc_not_self ((terminates_of_desc3 hD).transGen.apply SRO) (TransGen.head' h hR)

/-- **The translation preserves the order below SRO** (given step 1): for standard forms `B < A`
(`A ≠ SRO`, `B ≠ []`), the value of `B` is below the value of `A`, and both are standard. -/
theorem order_pres (hD : Desc3) {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA := by
  have hR := reach_of_seqlex hD A hA B hB hBE hlt
  have claim : ∀ C, TransGen Step' B C → C ≠ SRO → ∃ tC tB, Val C tC ∧ Val B tB ∧ tB < tC := by
    intro C hBC
    induction hBC with
    | single h =>
      intro hCS
      obtain ⟨hCs, hCE, n, rfl⟩ := h
      obtain ⟨t, t', hv, hv', _, hlt⟩ := hD _ n hCs hCS hCE
      exact ⟨t, t', hv, hv', hlt⟩
    | @tail C' C _ h ih =>
      intro hCS
      obtain ⟨tC', tB, hv1, hvB, hlt1⟩ := ih (step_ne_sro hD h)
      obtain ⟨hCs, hCE, n, rfl⟩ := h
      obtain ⟨t, t', hv, hv', _, hlt⟩ := hD _ n hCs hCS hCE
      rw [val_unique hv1 hv'] at hlt1
      exact ⟨t, tB, hv, hvB, lt_trans hlt1 hlt⟩
  obtain ⟨tA, tB, hvA, hvB, hlt⟩ := claim A hR hAS
  have hAE : A ≠ [] := by
    rintro rfl
    match B, hBE with
    | _ :: _, _ => simp [TRIO.seqlex] at hlt
  obtain ⟨b, hb, _⟩ := TransGen.head'_iff.mp hR
  have hBS := step_ne_sro hD hb
  obtain ⟨t1, _, hv1, _, hot1, _⟩ := hD A 0 hA hAS hAE
  obtain ⟨t2, _, hv2, _, hot2, _⟩ := hD B 0 hB hBS hBE
  rw [val_unique hvA hv1, val_unique hvB hv2] at *
  exact ⟨t1, t2, hv1, hv2, hot1, hot2, hlt⟩

end Ytosk
