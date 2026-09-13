/-
GwY.lean: 台座の吊るし（BH）。W 0 の Aok な台座 `A` の後ろに、高さ 1 から始まる `Wg 2` の木を継げる。

    Aok A → T ∈ Wg 2 → (T の列は高さ ≥ 1) → Mono T → entry T 0 0 ≤ 1 → A ++ T ∈ W 0

T の列の行 0 の祖先は T の中と A の根だけ（T の先頭の高さ 1 が A の他の列を隠す）。
`GwS.GOKR_of_Wg2` と同じ `Wg 2` の帰納で、場合は 3 つ:
- 末尾の親が T の中: `oper_shift A T 0`。
- 最上位の平らな列 `(1,0,0)`: 親は A の根、展開は `(A ++ T')` の最上位の複製（`flat_mem''`）。
- 1 の列の孤児 `(h,1,0)`: A の根が生き返らせる。`snocd_gen`（荷は T の graft の分岐）。
-/
import GwX

namespace TRIO
namespace GwY

open Wset
open Small
open GwS
open Gw

/-- ★★★ 台座の吊るし。 -/
theorem base_hang : ∀ T ∈ Wg 2, (∀ x ∈ T, 1 ≤ x.1) → Mono T → entry T 0 0 ≤ 1 →
    ∀ A : TrioSeq, Aok A → A ++ T ∈ W 0 := by
  have key : Wg 2 ⊆ {T : TrioSeq | T ∈ Wg 2 ∧ ((∀ x ∈ T, 1 ≤ x.1) → Mono T →
      entry T 0 0 ≤ 1 → ∀ A : TrioSeq, Aok A → A ++ T ∈ W 0)} := by
    refine A2g' ?_
    intro T hA
    have hTW : T ∈ Wg 2 := A1g_intro (Aopg_mono_X hA (fun U hU => hU.1))
    refine ⟨hTW, ?_⟩
    intro hge hmo hhd A hAok
    by_cases hTnil : T = []
    · subst hTnil; simpa using hAok.mem
    have hTlen : 0 < T.length := List.length_pos_iff.mpr hTnil
    have hAlen : 0 < A.length := List.length_pos_iff.mpr hAok.ne
    set c := T.getLast hTnil with hc
    have hsplit : T = T.dropLast ++ [c] := (List.dropLast_append_getLast hTnil).symm
    have hclast : ∀ r, entry T r (T.length - 1) = entry [c] r 0 := by
      intro r
      have h := entry_append_right T.dropLast [c] r 0
      rw [← hsplit] at h
      rw [show T.length - 1 = T.dropLast.length + 0 by simp]
      exact h
    have eT : ∀ r i, i < T.dropLast.length → entry T r i = entry T.dropLast r i := by
      intro r i hi
      have h := Small.entry_append_left (P := T.dropLast) (B := [c]) (i := r) hi
      rw [← hsplit] at h
      exact h
    have hcmem : c ∈ T := List.getLast_mem hTnil
    have hc1 : 1 ≤ c.1 := hge c hcmem
    have hdlge : ∀ x ∈ T.dropLast, 1 ≤ x.1 := fun x hx => hge x (List.dropLast_subset _ hx)
    have hdlmo : Mono T.dropLast := fun x hx => hmo x (List.dropLast_subset _ hx)
    have hdlhd : entry T.dropLast 0 0 ≤ 1 := by
      by_cases h0 : T.dropLast = []
      · rw [h0]; simp [entry]
      · have := eT 0 0 (List.length_pos_iff.mpr h0); omega
    have hcT : T.dropLast = [] → c.1 ≤ 1 := by
      intro h0
      have hT1 : T.length = 1 := by rw [hsplit, h0]; simp
      have e1 : entry T 0 (T.length - 1) = entry T 0 0 := by rw [hT1]
      rw [hclast 0] at e1
      have e2 : entry [c] 0 0 = c.1 := rfl
      omega
    have htailA : ∀ r, 1 ≤ r → r < (A ++ T.dropLast).length →
        1 ≤ entry (A ++ T.dropLast) 0 r := by
      intro r hr1 hrl
      rcases Nat.lt_or_ge r A.length with hrA | hrA
      · rw [Small.entry_append_left hrA]; exact hAok.deep.2 r hr1 hrA
      · obtain ⟨t, rfl⟩ : ∃ t, r = A.length + t := ⟨r - A.length, by omega⟩
        rw [entry_append_right]
        have ht : t < T.dropLast.length := by simp only [List.length_append] at hrl; omega
        have hmem : T.dropLast.getD t (0, 0, 0) ∈ T.dropLast := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
          exact List.getElem_mem _
        exact hdlge _ hmem
    have hflat : c.2.1 = 0 → c.2.2 = 0 → (∀ y ∈ T.dropLast, c.1 ≤ y.1) →
        A ++ T.dropLast ∈ W 0 → A ++ T ∈ W 0 := by
      intro hc10 hc20 hTx hdl
      have hx1 : c.1 = 1 := by
        by_cases h0 : T.dropLast = []
        · have := hcT h0; omega
        · have hmem : T.dropLast.getD 0 (0, 0, 0) ∈ T.dropLast := by
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (List.length_pos_iff.mpr h0)]
            exact List.getElem_mem _
          have h3 := hTx _ hmem
          have h2 : entry T.dropLast 0 0 = (T.dropLast.getD 0 (0, 0, 0)).1 := rfl
          omega
      have hceq : c = ((1, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hx1 (Prod.ext hc10 hc20)
      have hne : A ++ T.dropLast ≠ [] := by simp [hAok.ne]
      have hhead : entry (A ++ T.dropLast) 0 0 < 1 := by
        rw [Small.entry_append_left hAlen, hAok.deep.1]; omega
      have htw : ∀ n, ([] : TrioSeq) ++ (List.range n).flatMap (fun _ => A ++ T.dropLast)
          ∈ W 0 := by
        intro n
        have h := W_flatMap_copies hdl (fun p _ => by
          rw [Small.entry_append_left hAlen, hAok.deep.1]; omega) n
        simpa using h
      have h := flat_mem'' (Y0 := []) (d := 1) hne hhead htailA htw
      rw [hsplit, hceq]
      simpa [List.append_assoc] using h
    have hlev0 : lev T (T.length - 1) = 0 → c.2.1 = 0 ∧ c.2.2 = 0 := by
      intro hz
      unfold lev at hz
      rw [hclast 1, hclast 2] at hz
      have e1 : entry [c] 1 0 = c.2.1 := rfl
      have e2 : entry [c] 2 0 = c.2.2 := rfl
      rw [e1, e2] at hz
      omega
    rcases hA with ⟨hl, hw0⟩ | ⟨hnat, hop⟩ | ⟨m, hm, hd, h20, hgr⟩
    · have hT1 : T.length = 1 := by omega
      have hdl : T.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      have hz : lev T (T.length - 1) = 0 := by rw [hT1]; exact hw0
      exact hflat (hlev0 hz).1 (hlev0 hz).2 (by rw [hdl]; simp)
        (by rw [hdl]; simpa using hAok.mem)
    · by_cases hlen2 : 2 ≤ T.length
      · by_cases hp : hasParent T (srow T (T.length - 1)) (T.length - 1)
        · refine A1_intro (Or.inr (Or.inl ?_))
          intro n hn
          have h := oper_shift A T 0 n hlen2 hp
          rw [shiftr01_zero, shiftr01_zero] at h
          rw [h]
          exact (hop n hn).2 (fun x hx => oper_mem_ge (c := 1) hge x hx) (Mono_oper hmo n)
            (by rw [oper_head_eq hn]; exact hhd) A hAok
        · have hz : lev T (T.length - 1) = 0 := by
            rcases natDom_iff.mp hnat with h | h
            · exact h
            · exact absurd h hp
          have hsr : srow T (T.length - 1) = 0 := by
            have := hz
            unfold srow
            unfold lev at this
            rw [if_neg (by omega), if_neg (by omega)]
          rw [hsr] at hp
          have hTx : ∀ y ∈ T.dropLast, c.1 ≤ y.1 := by
            intro y hy
            by_contra hlt
            push Not at hlt
            obtain ⟨k, hk, hky⟩ := List.getElem_of_mem hy
            apply hp
            refine (Wset.hasParent_zero_iff (by omega)).mpr ⟨k, by simp at hk; omega, ?_⟩
            have e1 : entry T 0 k = y.1 := by
              rw [eT 0 k hk]
              show (T.dropLast.getD k (0, 0, 0)).1 = y.1
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hky]
            rw [e1, hclast 0]
            exact hlt
          have hdl : A ++ T.dropLast ∈ W 0 := by
            have h1 := (hop 1 le_rfl).2 (fun x hx => oper_mem_ge (c := 1) hge x hx)
              (Mono_oper hmo 1) (by rw [oper_head_eq le_rfl]; exact hhd) A hAok
            rwa [oper_one_eq_dropLast (by omega)] at h1
          exact hflat (hlev0 hz).1 (hlev0 hz).2 hTx hdl
      · have hT1 : T.length = 1 := by omega
        have hdl : T.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
        have hz : lev T (T.length - 1) = 0 := by
          rcases natDom_iff.mp hnat with h | h
          · exact h
          · exfalso
            rw [hT1] at h
            obtain ⟨j0, hj0, -⟩ := h
            exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
        exact hflat (hlev0 hz).1 (hlev0 hz).2 (by rw [hdl]; simp)
          (by rw [hdl]; simpa using hAok.mem)
    · have hlev := hd.1
      unfold lev at hlev
      have h20' : entry T 2 (T.length - 1) = 0 := h20
      have hw1 : entry T 1 (T.length - 1) = 1 := by omega
      have hsr : srow T (T.length - 1) = 1 := by
        unfold srow; rw [if_neg (by omega), if_pos (by omega)]
      have hnp : ¬ hasParent T 1 (T.length - 1) := fun hh => hd.2 (by rw [hsr]; exact hh)
      have hc11 : c.2.1 = 1 := by
        have := hclast 1; rw [hw1] at this; exact this.symm
      have hc20 : c.2.2 = 0 := by
        have := hclast 2; rw [h20'] at this; exact this.symm
      have hceq : c = ((c.1, 1, 0) : ℕ × ℕ × ℕ) := Prod.ext rfl (Prod.ext hc11 hc20)
      have hTeq : T = T.dropLast ++ [((c.1, 1, 0) : ℕ × ℕ × ℕ)] := by
        rw [← hceq]; exact hsplit
      have hsp : ∀ j, j < T.dropLast.length → entry T.dropLast 0 j < c.1 →
          (∀ i, j < i → i < T.dropLast.length → entry T.dropLast 0 j < entry T.dropLast 0 i) →
          1 ≤ entry T.dropLast 1 j := by
        intro j hj hjh hvis
        by_contra h0
        push Not at h0
        apply hnp
        have hjT : j < T.length - 1 := by simpa using hj
        have hle : le0 T j (T.length - 1) := by
          refine le0_of_between (a := entry T 0 j) rfl (T.length - 1) (by omega) (by omega) ?_
          intro j' h1 h2
          rcases Nat.lt_or_ge j' (T.length - 1) with h3 | h3
          · have hj' : j' < T.dropLast.length := by simpa using h3
            rw [eT 0 j hj, eT 0 j' hj']
            have := hvis j' h1 hj'
            omega
          · have : j' = T.length - 1 := by omega
            subst this
            rw [hclast 0, eT 0 j hj]
            show entry T.dropLast 0 j + 1 ≤ c.1
            omega
        refine H12Export.hasParent1_of_le0_witness (by omega) hle.2.2 ?_
        rw [eT 1 j hj, hw1]; omega
      have hAokY : Aok (A ++ T.dropLast) := by
        have hmem : A ++ T.dropLast ∈ W 0 := by
          have h1 := (hgr [] (Wg_nil m) based_nil).2
          rw [graft_nil] at h1
          exact h1 hdlge hdlmo hdlhd A hAok
        refine ⟨hmem, by simp [hAok.ne], ⟨?_, htailA⟩, ?_, ?_⟩
        · rw [Small.entry_append_left hAlen]; exact hAok.deep.1
        · intro x hx hx0
          rcases List.mem_append.mp hx with hx | hx
          · exact hAok.zroot x hx hx0
          · have := hdlge x hx; omega
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hAok.mono x hx
          · exact hdlmo x hx
      have hAncd : Ancd c.1 (A ++ T.dropLast) := by
        intro j hj0 hjl hlt hvis
        rcases Nat.lt_or_ge j A.length with hjA | hjA
        · exfalso
          have hdj := hAok.deep.2 j hj0 hjA
          rw [Small.entry_append_left hjA] at hlt
          by_cases h0 : T.dropLast = []
          · have := hcT h0; omega
          · have hv := hvis A.length hjA (by
              simp only [List.length_append]
              have := List.length_pos_iff.mpr h0; omega)
            rw [Small.entry_append_left hjA, entry_append_at] at hv
            omega
        · obtain ⟨t, rfl⟩ : ∃ t, j = A.length + t := ⟨j - A.length, by omega⟩
          have ht : t < T.dropLast.length := by simp only [List.length_append] at hjl; omega
          rw [entry_append_right] at hlt ⊢
          refine hsp t ht hlt ?_
          intro i hi hil
          have := hvis (A.length + i) (by omega) (by simp only [List.length_append]; omega)
          rwa [entry_append_right, entry_append_right] at this
      have hang : ∀ B : TrioSeq, Bok B → (A ++ T.dropLast) ++ shiftr01 c.1 0 B ∈ W 0 := by
        intro B hB
        have hBW : B ∈ Wg m := Wg_mono (Nat.zero_le m) (Bok_mem_Wg0 B hB)
        have h1 := (hgr B hBW hB.root).2
        have e : graft T B = T.dropLast ++ shiftr01 c.1 0 B := by
          rw [graft_eq_shift, hclast 0]
          rfl
        rw [e] at h1
        have hgeB : ∀ x ∈ T.dropLast ++ shiftr01 c.1 0 B, 1 ≤ x.1 := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hdlge x hx
          · simp only [shiftr01, List.mem_map] at hx
            obtain ⟨p, -, rfl⟩ := hx
            dsimp only; omega
        have hmoB : Mono (T.dropLast ++ shiftr01 c.1 0 B) := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hdlmo x hx
          · simp only [shiftr01, List.mem_map] at hx
            obtain ⟨p, hp, rfl⟩ := hx
            have := hB.mono p hp
            dsimp only; omega
        have hhdB : entry (T.dropLast ++ shiftr01 c.1 0 B) 0 0 ≤ 1 := by
          by_cases h0 : T.dropLast = []
          · rw [h0, List.nil_append]
            have h3 := hcT h0
            by_cases hBn : B = []
            · rw [hBn]; simp [entry, shiftr01]
            · rw [entry0_shiftr01 (List.length_pos_iff.mpr hBn)]
              have := hB.root; omega
          · rw [Small.entry_append_left (List.length_pos_iff.mpr h0)]; exact hdlhd
        have := h1 hgeB hmoB hhdB A hAok
        simpa [List.append_assoc] using this
      rw [hTeq]
      have h := snocd_gen (Y := A ++ T.dropLast) (d := c.1) hc1 hAokY hAncd hang
      simpa [List.append_assoc] using h
  intro T hT hge hmo hhd A hA
  exact (key hT).2 hge hmo hhd A hA

#print axioms base_hang

end GwY
end TRIO
