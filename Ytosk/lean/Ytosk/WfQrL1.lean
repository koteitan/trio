/-
**WfQrL1 (2026-11-01): the q = r engine with given values on `D` (`glueQ`, `qr_pathQ`).**

The old engine glues `fsD(ρ.o i, Zf i)` on `D` (`glueZ`). With re-exposed summands (WfQrE1, `DQ`) the new value
of a `D` call is not a function of the old one, so the glue takes the `D` values as data: `glueQ M x ρ ρN oq vq`
is `oq i` / `vq i` on `D` below `x`, `ρ` off `D` below `x`, `ρN` from `x` on (`glueZ` is the case
`oq i = fsD (ρ.o i) (Zf i)`, `glueZ_eq_glueQ`).

* `cons_glueQ_lt` : the equations of `N` below `x` from the local equations on `D` (copy of `cons_glue_lt`).
* `OLocQ` / `VLocQ` : local conditions with the `D` values as data; the frame equations are the raw right sides
  (no absorption, no `fsD`).  `qr_pathQ`: they give `oRhs (glueQ) i = oq i`, `vRhs (glueQ) i = vq i`.
* `bumpW_glueQ` : the bump term of the glue at a bump frame, the input of `v_bumpDQ` (WfQrE1).
* `add_exchangeQS`, `exchangeQ_nil`, `v_bumpQ_nil` : `Q` is made of summands of `v(P₁ i)`; a bump call that is
  not `WfBad.BadCall` (with `W = o(r)`, or with `AbsDSX` giving the absorption) has `Q = 0`.
-/
import Ytosk.WfBad
import Ytosk.WfQrE1
import Ytosk.V3QRPath

namespace Ytosk.WfQrL1
open T Ytosk

/-! ## `Q` is made of summands of `v(P₁ i)` -/

/-- The summands of a right part of a sum are summands of the sum. -/
theorem summands_right {B X q : T} (h : q ∈ summands X) : q ∈ summands (app B X) := by
  rw [summands_app]; exact List.mem_append_right _ h

/-- **`add_exchangeQ` with the source of `Q`**: every summand of `Q` is a summand of `A`. -/
theorem add_exchangeQS {A W' s y : T} (hAot : isOT A = true) (hW' : Single W') (hle : W' ≤ psi s y z) :
    ∃ B Q, add A (psi s y z) = app B (psi s y z) ∧ add A W' = app B (app Q W') ∧
      (∀ q ∈ summands Q, W' ≤ q ∧ q < psi s y z) ∧ ∀ q ∈ summands Q, q ∈ summands A := by
  obtain ⟨_, s', y', rfl⟩ := hW'
  obtain ⟨B, X, hAB, hX, hadd⟩ := add_prefix s y A
  have hBge : ∀ q ∈ summands B, ¬ q < psi s y z := by
    intro q hq hlt
    have hq' : q ∈ summands (add A (psi s y z)) := by
      rw [hadd, summands_app]; exact List.mem_append_left _ hq
    exact lt_irrefl' _ (lt_of_le_of_lt (add_summands_ge A q hq') hlt)
  refine ⟨B, (split X (psi s' y' z)).1, hadd, ?_, ?_, ?_⟩
  · rw [hAB, add_app_keep X (fun q hq hlt => hBge q hq (lt_of_lt_of_le hlt hle)),
      add_eq_app_split s' y' X]
  · intro q hq
    obtain ⟨hqX, hnq⟩ := split_fst_mem _ X q hq
    refine ⟨not_lt.mp hnq, ?_⟩
    have hXot : isOT X = true := by rw [hAB] at hAot; exact isOT_app_right hAot
    exact lt_of_le_of_lt (summands_le_head hXot q hqX) (head_lt_of_lt_single hX)
  · intro q hq
    obtain ⟨hqX, _⟩ := split_fst_mem _ X q hq
    rw [hAB]; exact summands_right hqX

/-- A term with no summands is `0`. -/
theorem eq_z_of_no_summands : ∀ {Q : T}, (∀ q, q ∈ summands Q → False) → Q = z
  | z, _ => rfl
  | psi a b c, h => absurd (h (psi a b z) (by simp [summands])) id

/-- **No summand of `A` in the window: `Q = 0`.** -/
theorem exchangeQ_nil {A W' W Q : T} (hQ : ∀ q ∈ summands Q, W' ≤ q ∧ q < W)
    (hS : ∀ q ∈ summands Q, q ∈ summands A)
    (hno : ∀ q ∈ summands A, q < W → q < W') : Q = z :=
  eq_z_of_no_summands (fun q hq =>
    lt_irrefl' _ (lt_of_lt_of_le (hno q (hS q hq) (hQ q hq).2) (hQ q hq).1))

/-- **A bump call with the absorption keeps the old form** `v_σ(i) = B ++ W_σ` (`Q = 0`). -/
theorem v_bumpQ_nil {M : Mat} {ρ σ : Valn} (hC : Cons M ρ) {i : Nat} (hiM : i < M.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hA : vOpt σ (par M 1 i) = vOpt ρ (par M 1 i)) (hAot : isOT (vOpt ρ (par M 1 i)) = true)
    (hW : Single (bumpW M ρ i)) (hW' : Single (bumpW M σ i)) (hle : bumpW M σ i ≤ bumpW M ρ i)
    (hno : ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i → q < bumpW M σ i) :
    ∃ B, ρ.v i = app B (bumpW M ρ i) ∧ vRhs M σ i = app B (bumpW M σ i) := by
  obtain ⟨hWot, s, y, hsy⟩ := hW
  rw [hsy] at hle hno ⊢
  obtain ⟨B, Q, hB, hB', hQ, hS⟩ := add_exchangeQS hAot hW' hle
  have hQz : Q = z := exchangeQ_nil hQ hS hno
  subst hQz
  refine ⟨B, ?_, ?_⟩
  · rw [(hC i hiM).2]
    unfold vRhs
    rw [if_neg h1, if_neg h2]
    have e : omega (sumN (one :: (children M i).map (bumpTerm M ρ i))) = psi s y z := hsy
    rw [e, sf_ot (isOT_add hAot (by rw [← hsy]; exact hWot)), hB]
  · unfold vRhs
    rw [if_neg h1, if_neg h2, hA]
    have e : omega (sumN (one :: (children M i).map (bumpTerm M σ i))) = bumpW M σ i := rfl
    rw [e, sf_ot (isOT_add hAot hW'.1), hB']
    rfl

/-- **Only bad calls re-expose** (with `WfBad.BadCall`): at a bump call where every summand of `v(P₁ i)` below
`W = o(r)`… is absorbed by `W[ζ]` unless the call is bad, a non-bad call has the absorption. -/
theorem absorbed_of_not_badCall {M : Mat} {ρ : Valn} {r : Nat} {ζ : T} {i : Nat}
    (hX : ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
      q < fsD (bumpW M ρ i) ζ ∨ (WfQnE2.BadShape1 M i ∧ bumpW M ρ i = ρ.o r))
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (hnb : ¬ WfBad.BadCall M ρ r ζ i) :
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i → q < fsD (bumpW M ρ i) ζ :=
  WfBad.absorbed_of_not_bad hX h1 h2 hnb

/-! ## The glue with given values on `D` -/

open Classical in
/-- Below `x`: `oq i` / `vq i` on `D`, `ρ` off `D`.  From `x` on: `ρN`. -/
noncomputable def glueQ (M : Mat) (x : Nat) (ρ ρN : Valn) (oq vq : Nat → T) : Valn :=
  ⟨fun i => if i < x then (if DepX M x true i then oq i else ρ.o i) else ρN.o i,
   fun i => if i < x then (if DepX M x false i then vq i else ρ.v i) else ρN.v i⟩

theorem glueZ_eq_glueQ (M : Mat) (x : Nat) (ρ ρN : Valn) (Z : Nat → T) :
    glueZ M x ρ ρN Z = glueQ M x ρ ρN (fun i => fsD (ρ.o i) (Z i)) (fun i => fsD (ρ.v i) (Z i)) := rfl

section
variable {M : Mat} {x : Nat} {ρ ρN : Valn} {oq vq : Nat → T}

theorem glueQ_o_lt {i : Nat} (hi : i < x) (hd : ¬ DepX M x true i) : (glueQ M x ρ ρN oq vq).o i = ρ.o i := by
  simp only [glueQ, if_pos hi, if_neg hd]

theorem glueQ_v_lt {i : Nat} (hi : i < x) (hd : ¬ DepX M x false i) : (glueQ M x ρ ρN oq vq).v i = ρ.v i := by
  simp only [glueQ, if_pos hi, if_neg hd]

theorem glueQ_o_dep {i : Nat} (hi : i < x) (hd : DepX M x true i) : (glueQ M x ρ ρN oq vq).o i = oq i := by
  simp only [glueQ, if_pos hi, if_pos hd]

theorem glueQ_v_dep {i : Nat} (hi : i < x) (hd : DepX M x false i) : (glueQ M x ρ ρN oq vq).v i = vq i := by
  simp only [glueQ, if_pos hi, if_pos hd]

theorem glueQ_o_ge {i : Nat} (hi : x ≤ i) : (glueQ M x ρ ρN oq vq).o i = ρN.o i := by
  simp only [glueQ, if_neg (Nat.not_lt.mpr hi)]

theorem glueQ_v_ge {i : Nat} (hi : x ≤ i) : (glueQ M x ρ ρN oq vq).v i = ρN.v i := by
  simp only [glueQ, if_neg (Nat.not_lt.mpr hi)]

/-- The glued `o` value of a `D` column at or below `x`. -/
theorem glueQ_o_D (hxN : ρN.o x = oq x) {c : Nat} (hc : c ≤ x) (hd : DepX M x true c) :
    (glueQ M x ρ ρN oq vq).o c = oq c := by
  rcases Nat.lt_or_ge c x with h | h
  · exact glueQ_o_dep h hd
  · have : c = x := by omega
    subst this; rw [glueQ_o_ge (le_refl _)]; exact hxN

theorem vOpt_glueQ {i : Nat} (hi : i < x) (hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m) :
    vOpt (glueQ M x ρ ρN oq vq) (par M 1 i) = vOpt ρ (par M 1 i) := by
  cases hp : par M 1 i with
  | none => rfl
  | some m =>
    have hm : m < i := par_lt M 1 i m hp
    exact glueQ_v_lt (by omega) (hpd m hp)

/-- **Gluing with given values** (copy of `cons_glue_lt`). -/
theorem cons_glueQ_lt {N : Mat} (hx : x + 1 = M.length) (hC : Cons M ρ) (hS : ∀ i, i < x → SameAt M N i)
    (hvx : ∀ i, i < x → ¬ DepX M x false i → ∀ m, entry M 1 i ≠ 0 →
      (par M 1 i = some m ∨ (entry M 2 i = 0 ∧ upg M i = some m)) → m < x)
    (hF : ∀ i, i < x →
      (DepX M x true i → oRhs M (glueQ M x ρ ρN oq vq) i = oq i) ∧
      (DepX M x false i → vRhs M (glueQ M x ρ ρN oq vq) i = vq i)) :
    ∀ i, i < x → (glueQ M x ρ ρN oq vq).o i = oRhs N (glueQ M x ρ ρN oq vq) i ∧
      (glueQ M x ρ ρN oq vq).v i = vRhs N (glueQ M x ρ ρN oq vq) i := by
  intro i hi
  have hiM : i < M.length := by omega
  rw [oRhs_same (hS i hi), vRhs_same (hS i hi)]
  refine ⟨?_, ?_⟩
  · by_cases hd : DepX M x true i
    · rw [glueQ_o_dep hi hd, (hF i hi).1 hd]
    · rw [glueQ_o_lt hi hd, (hC i hiM).1]
      apply oRhs_congr
      · have hv : ¬ DepX M x false i := fun hv => hd (DepX.ov hv)
        rw [glueQ_v_lt hi hv]
      · intro c hc hb hu
        have hcd : ¬ DepX M x true c := fun h => hd (DepX.ochild hc hb hu h)
        have hcl := (mem_children hc).2
        have hcx : c < x := by
          rcases Nat.lt_or_ge c x with h | h
          · exact h
          · have : c = x := by omega
            subst this; exact absurd DepX.leaf hcd
        rw [glueQ_o_lt hcx hcd]
  · by_cases hd : DepX M x false i
    · rw [glueQ_v_dep hi hd, (hF i hi).2 hd]
    · rw [glueQ_v_lt hi hd, (hC i hiM).2]
      apply vRhs_congr
      · intro m h1 hm
        have hmd : ¬ DepX M x false m := fun h => hd (DepX.vpar h1 hm h)
        rw [glueQ_v_lt (hvx i hi hd m h1 (Or.inl hm)) hmd]
      · intro k h1 h2 hk
        have hkd : ¬ DepX M x false k := fun h => hd (DepX.vupg h1 h2 hk h)
        rw [glueQ_v_lt (hvx i hi hd k h1 (Or.inr ⟨h2, hk⟩)) hkd]
      · intro j hj h1 h2 hb k hk
        have hkd : ¬ DepX M x true k := fun h => hd (DepX.vbump h1 h2 hj hb hk h)
        have hkl := (mem_children hk).2
        have hkx : k < x := by
          rcases Nat.lt_or_ge k x with h | h
          · exact h
          · have : k = x := by omega
            subst this; exact absurd DepX.leaf hkd
        rw [glueQ_o_lt hkx hkd]

/-! ## Local conditions with given values -/

/-- Local conditions at an `o` call: only the subscript changes (`oq i = Ω_{vq i}`), or the last counted child
`c` is in `D` and the frame equation links `oq c` and `oq i`. -/
def OLocQ (M : Mat) (x : Nat) (ρ : Valn) (oq vq : Nat → T) (i : Nat) : Prop :=
  (DepX M x false i ∧
    (∀ d ∈ children M i, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) ∧
    oq i = sf (psi (vq i) z z)) ∨
  (¬ DepX M x false i ∧ ∃ L c R, children M i = L ++ c :: R ∧ col M c ≠ bump M i ∧
    ¬ (isUpg M c = true ∧ topped M c = true) ∧
    (∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) ∧
    (∀ d ∈ L, Counted M i d → ¬ DepX M x true d) ∧ DepX M x true c ∧
    Single (oq c) ∧ oq c ≤ ρ.o c ∧
    oq i = psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (oq c)) z)

/-- The bump term at a bump frame with the new value `oK` of the last child `k` of `j`. -/
noncomputable def bumpWQ (M : Mat) (ρ : Valn) (i : Nat) (L K : List Nat) (oK : T) : T :=
  omega (sumN (one :: (L.map (bumpTerm M ρ i) ++ [omega (sumN (K.map ρ.o ++ [oK]))])))

/-- Local conditions at a `v` call: an upgrade frame or a bump frame, with the raw right side. -/
def VLocQ (M : Mat) (x : Nat) (ρ : Valn) (oq vq : Nat → T) (i : Nat) : Prop :=
  entry M 1 i ≠ 0 ∧ (∀ m, par M 1 i = some m → ¬ DepX M x false m) ∧
  ((∃ k, entry M 2 i = 0 ∧ upg M i = some k ∧ k < x ∧ DepX M x false k ∧
      vq i = sf (add (vOpt ρ (par M 1 i)) (last (vq k)))) ∨
   (∃ L K j k, entry M 2 i ≠ 0 ∧ children M i = L ++ [j] ∧ col M j = bump M i ∧
      children M j = K ++ [k] ∧ DepX M x true k ∧ (∀ d ∈ K, ¬ DepX M x true d) ∧
      (∀ d ∈ L, ∀ e ∈ children M d, e < x ∧ ¬ DepX M x true e) ∧
      vq i = sf (add (vOpt ρ (par M 1 i)) (bumpWQ M ρ i L K (oq k)))))

/-- **The bump term of the glue** at a bump frame. -/
theorem bumpW_glueQ (hx : x + 1 = M.length) (hxN : ρN.o x = oq x) {i j k : Nat} {L K : List Nat}
    (hch : children M i = L ++ [j]) (hjb : col M j = bump M i) (hchj : children M j = K ++ [k])
    (hkd : DepX M x true k) (hKnd : ∀ d ∈ K, ¬ DepX M x true d)
    (hLnd : ∀ d ∈ L, ∀ e ∈ children M d, e < x ∧ ¬ DepX M x true e) :
    bumpW M (glueQ M x ρ ρN oq vq) i = bumpWQ M ρ i L K (oq k) := by
  have hk : k ∈ children M j := by rw [hchj]; simp
  have hkx : k ≤ x := by have := (mem_children hk).2; omega
  have hK : ∀ d ∈ K, (glueQ M x ρ ρN oq vq).o d = ρ.o d := by
    intro d hd'
    have hsort := children_sorted M j
    rw [hchj] at hsort
    have hdk : d < k := (List.pairwise_append.mp hsort).2.2 d hd' k (List.mem_singleton_self _)
    exact glueQ_o_lt (by omega) (hKnd d hd')
  have hL : ∀ d ∈ L, bumpTerm M (glueQ M x ρ ρN oq vq) i d = bumpTerm M ρ i d := by
    intro d hd'
    unfold bumpTerm
    split
    · congr 2
      apply List.map_congr_left
      intro e he
      exact glueQ_o_lt (hLnd d hd' e he).1 (hLnd d hd' e he).2
    · rfl
  unfold bumpW bumpWQ
  rw [hch, List.map_append, List.map_congr_left hL, List.map_singleton]
  unfold bumpTerm
  rw [if_pos hjb, hchj, List.map_append, List.map_congr_left hK, List.map_singleton,
    glueQ_o_D hxN hkx hkd]

/-- **Only the subscript changes**, given value. -/
theorem qr_o_subQ (hx : x + 1 = M.length) {i : Nat} (hi : i < x)
    (hnc : ∀ d ∈ children M i, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hv : DepX M x false i) (hF : oq i = sf (psi (vq i) z z)) :
    oRhs M (glueQ M x ρ ρN oq vq) i = oq i := by
  have hzero : ∀ σ : Valn, sumN ((children M i).map (cnt M σ i)) = z := by
    intro σ
    have : (children M i).map (cnt M σ i) = (children M i).map (fun _ => z) :=
      List.map_congr_left (fun d hd => cnt_unc σ (hnc d hd))
    rw [this, sumN_skip_z (fun t ht => by
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; exact Or.inl rfl)
      (by rw [nzs_zeros _ (fun t ht => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; rfl)]; simp),
      nzs_zeros _ (fun t ht => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; rfl)]
    rfl
  unfold oRhs
  rw [hzero, glueQ_v_dep hi hv, hF]

/-- **One `o` frame at the last counted child**, given value. -/
theorem qr_o_lastQ (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hxN : ρN.o x = oq x) {i : Nat} (hi : i < x) {L R : List Nat} {c : Nat}
    (hch : children M i = L ++ c :: R) (hcb : col M c ≠ bump M i)
    (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
    (hR : ∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hLnd : ∀ d ∈ L, Counted M i d → ¬ DepX M x true d) (hcd : DepX M x true c)
    (hv : ¬ DepX M x false i)
    (hcS' : Single (oq c)) (hle : oq c ≤ ρ.o c)
    (hF : oq i = psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (oq c)) z) :
    oRhs M (glueQ M x ρ ρN oq vq) i = oq i := by
  have hiM : i < M.length := by omega
  have hc : c ∈ children M i := by rw [hch]; simp
  have hcM := (mem_children hc).2
  have hic := (mem_children hc).1
  have hcx : c ≤ x := by omega
  have hsplit := cvals_split hch hcb hcu hR (single_ne_z (single_o hC hG hcM))
  have hdec := hG.dec i hiM
  rw [hsplit] at hdec
  have hp' : (nzs (L.map (cnt M ρ i)) ++ [oq c]).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_append] at hdec ⊢
    refine ⟨hdec.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    exact le_trans hle (hdec.2.2 a ha _ (List.mem_singleton_self _))
  rw [hF]
  apply oRhs_frame_gen hiM hch hcb hcu hR (glueQ_v_lt hi hv) ?_ (glueQ_o_D hxN hcx hcd)
    (hG.ot_v i hiM) ?_ hcS' hp'
  · intro d hd
    by_cases hcd' : Counted M i d
    · have hdc : d < c := by
        have hsort := children_sorted M i
        rw [hch] at hsort
        exact (List.pairwise_append.mp hsort).2.2 d hd c List.mem_cons_self
      rw [cnt_cnt _ hcd'.1 hcd'.2, cnt_cnt _ hcd'.1 hcd'.2]
      exact glueQ_o_lt (by omega) (hLnd d hd hcd')
    · have : col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true) := by
        by_cases h1 : col M d = bump M i
        · exact Or.inl h1
        · right; by_contra h2; exact hcd' ⟨h1, h2⟩
      rw [cnt_unc _ this, cnt_unc _ this]
  · intro t ht
    exact cnt_single hC hG i t (by rw [hch, List.map_append]; exact List.mem_append_left _ ht)

/-- **The path theorem with given values** (`t = 1`, `q = r`): the local conditions give the local equations of
the glue.  No absorption and no `fsD`: the `D` values are data (`DQ` of the old values in the intended use). -/
theorem qr_pathQ (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hxN : ρN.o x = oq x)
    (hO : ∀ i, i < x → DepX M x true i → OLocQ M x ρ oq vq i)
    (hV : ∀ i, i < x → DepX M x false i → VLocQ M x ρ oq vq i) :
    ∀ i, i < x →
      (DepX M x true i → oRhs M (glueQ M x ρ ρN oq vq) i = oq i) ∧
      (DepX M x false i → vRhs M (glueQ M x ρ ρN oq vq) i = vq i) := by
  intro i hi
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rcases hO i hi hd with ⟨hv, hnc, hF⟩ | ⟨hv, L, c, R, hch, hcb, hcu, hR, hLnd, hcd, hcS', hle, hF⟩
    · exact qr_o_subQ hx hi hnc hv hF
    · exact qr_o_lastQ hC hG hx hxN hi hch hcb hcu hR hLnd hcd hv hcS' hle hF
  · obtain ⟨h1, hpd, hcase⟩ := hV i hi hd
    rcases hcase with ⟨k, h2, hu, hk, hkd, hF⟩ | ⟨L, K, j, k, h2, hch, hjb, hchj, hkd, hKnd, hLnd, hF⟩
    · unfold vRhs
      rw [if_neg h1, if_pos h2, hu, vOpt_glueQ hi hpd]
      simp only
      rw [glueQ_v_dep hk hkd, hF]
    · have e : bumpW M (glueQ M x ρ ρN oq vq) i = bumpWQ M ρ i L K (oq k) :=
        bumpW_glueQ hx hxN hch hjb hchj hkd hKnd hLnd
      unfold vRhs
      rw [if_neg h1, if_neg h2, vOpt_glueQ hi hpd]
      have e' : omega (sumN (one :: (children M i).map (bumpTerm M (glueQ M x ρ ρN oq vq) i))) =
          bumpW M (glueQ M x ρ ρN oq vq) i := rfl
      rw [e', e, hF]

/-- **The `v` value of a bump frame of the glue is a `DQ` of the old one** (`v_bumpDQ` on the glue): the only
input is the `DQ` relation of the bump terms (the `ω` exchange). -/
theorem v_bumpDQ_glueQ (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length) (hxN : ρN.o x = oq x)
    {η : T} {i j k : Nat} {L K : List Nat} (hi : i < x)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m)
    (hch : children M i = L ++ [j]) (hjb : col M j = bump M i) (hchj : children M j = K ++ [k])
    (hkd : DepX M x true k) (hKnd : ∀ d ∈ K, ¬ DepX M x true d)
    (hLnd : ∀ d ∈ L, ∀ e ∈ children M d, e < x ∧ ¬ DepX M x true e)
    (hW : Single (bumpW M ρ i)) (hW' : Single (bumpWQ M ρ i L K (oq k)))
    (hD : DQ η false (bumpW M ρ i) (bumpWQ M ρ i L K (oq k))) :
    DQ η true (ρ.v i) (sf (add (vOpt ρ (par M 1 i)) (bumpWQ M ρ i L K (oq k)))) := by
  have hiM : i < M.length := by omega
  have e := bumpW_glueQ (ρ := ρ) (vq := fun _ => z) hx hxN hch hjb hchj hkd hKnd hLnd
  rw [← e] at hW' hD
  have h := v_bumpDQ hC hiM h1 h2 (vOpt_glueQ (vq := fun _ => z) hi hpd) (vOpt_ot hG hiM) hW hW' hD
  unfold vRhs at h
  rw [if_neg h1, if_neg h2, vOpt_glueQ hi hpd] at h
  have e' : omega (sumN (one :: (children M i).map
      (bumpTerm M (glueQ M x ρ ρN oq (fun _ => z)) i))) =
      bumpW M (glueQ M x ρ ρN oq (fun _ => z)) i := rfl
  rw [e', e] at h
  exact h

/-- **The `v` value of an upgrade frame of the glue is a `DQ` of the old one** (`v_upgDQ` on the glue). -/
theorem v_upgDQ_glueQ (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length) {η : T} {i k : Nat}
    (hi : i < x) (hk : k < x) (hkd : DepX M x false k)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i = 0) (hu : upg M i = some k)
    (hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m)
    (hV : Single (last (ρ.v k))) (hV' : Single (last (vq k)))
    (hD : DQ η false (last (ρ.v k)) (last (vq k))) :
    DQ η true (ρ.v i) (sf (add (vOpt ρ (par M 1 i)) (last (vq k)))) := by
  have hiM : i < M.length := by omega
  have ek : (glueQ M x ρ ρ (fun _ => z) vq).v k = vq k := glueQ_v_dep hk hkd
  rw [← ek] at hV' hD
  have h := v_upgDQ hC hiM h1 h2 hu (vOpt_glueQ (ρN := ρ) (oq := fun _ => z) (vq := vq) hi hpd)
    (vOpt_ot hG hiM) hV hV' hD
  unfold vRhs at h
  rw [if_neg h1, if_pos h2, hu, vOpt_glueQ hi hpd] at h
  simpa only [ek] using h

end

end Ytosk.WfQrL1
