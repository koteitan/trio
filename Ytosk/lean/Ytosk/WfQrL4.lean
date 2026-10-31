/-
**WfQrL4 (2026-11-01): the last-child `o` frame for `DQ`** (step (3) of tmp/wf/WfQrE/notes.md).

At an `o` call `i` whose last counted child `c` is in `D`:
  `o(i) = ψ_{v(i)}(spArg(v(i), pre, o(c)))`,   `o_N(i) = ψ_{v(i)}(spArg(v(i), pre, o_N(c)))`
(`o_frame_eq`, `pre = preState M ρ i L`).  With `o(c) = ψ_s(y)` the one `sp` step either adds (`pre + o(c)`) or
triggers (`H(s, y)`, which is `y` when `y` has no low part).
  * `frame_DQ_add`  : no trigger in `M` and in `N`: `pre + o(c) = B ++ o(c)`, `pre + o_N(c) = B ++ Q ++ o_N(c)`
    (`add_exchangeQ`), a `DQ` step (re-exposed summands of `pre`!);
  * `frame_DQ_trig` : trigger in both, no low part in `y` and `y_N` (`lo_keep_DQ` + `TPLoQ`): `y → y_N`, `DQ.arg`.
The mixed case (trigger in `M` only) is the persistence condition (`TP1W` in the old engine): kept as a hypothesis.
-/
import Ytosk.WfQrL3

namespace Ytosk.WfQrL4
open T Ytosk Ytosk.WfQrL2

/-- One `sp` step on a single summand. -/
theorem spArg_single (v pre s y : T) : spArg v pre (psi s y z) = step v pre s y z := rfl

/-- **`H(s, y) = y` without a low part.** -/
theorem H_nolo {s y : T} (hy : isOT (psi s y z) = true) (hlo : (split y (psi (succ s) z z)).2 = z) :
    H s y = y := by
  rw [H_eq hy, if_pos hlo, app_z_right]
  have e := split_app (psi (succ s) z z) y
  rw [hlo, app_z_right] at e
  exact e

/-- **No trigger: the frame adds, `DQ` with the re-exposed summands of `pre`.** -/
theorem frame_DQ_add {η v pre s y lN : T} (hpre : isOT pre = true) (hlN : Single lN)
    (hd : DQ η false (psi s y z) lN)
    (hnt : ¬ (lt pre y = true ∧ lt (psi v z z) (psi s y z) = true))
    (hntN : ∀ s' y', lN = psi s' y' z → ¬ (lt pre y' = true ∧ lt (psi v z z) (psi s' y' z) = true)) :
    DQ η false (psi v (spArg v pre (psi s y z)) z) (psi v (spArg v pre lN) z) := by
  obtain ⟨hlNot, s', y', rfl⟩ := hlN
  rw [spArg_single, spArg_single]
  unfold step
  rw [if_neg hnt, if_neg (hntN s' y' rfl)]
  obtain ⟨B, Q, hB, hB', hQ⟩ := add_exchangeQ hpre ⟨hlNot, s', y', rfl⟩ (le_of_lt hd.lt)
  rw [hB, hB']
  exact DQ.arg (DQ.mk rfl hd hQ)

/-- **Trigger in both, no low part: the frame is `y → y_N`.** -/
theorem frame_DQ_trig {η v pre s y yN : T} (hy : isOT (psi s y z) = true) (hyN : isOT (psi s yN z) = true)
    (hd : DQ η true y yN)
    (ht : lt pre y = true ∧ lt (psi v z z) (psi s y z) = true)
    (htN : lt pre yN = true ∧ lt (psi v z z) (psi s yN z) = true)
    (hlo : (split y (psi (succ s) z z)).2 = z) (hloN : (split yN (psi (succ s) z z)).2 = z) :
    DQ η false (psi v (spArg v pre (psi s y z)) z) (psi v (spArg v pre (psi s yN z)) z) := by
  rw [spArg_single, spArg_single]
  unfold step
  rw [if_pos ht, if_pos htN, H_nolo hy hlo, H_nolo hyN hloN]
  exact DQ.arg hd

/-- **The frame equation of `M` at the last counted child.** -/
theorem o_frame_eq {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {i : Nat} (hiM : i < M.length)
    {L R : List Nat} {c : Nat} (hch : children M i = L ++ c :: R) (hcb : col M c ≠ bump M i)
    (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
    (hR : ∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) :
    ρ.o i = psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (ρ.o c)) z := by
  have hc : c ∈ children M i := by rw [hch]; simp
  have hcM := (mem_children hc).2
  have hsplit := cvals_split hch hcb hcu hR (single_ne_z (single_o hC hG hcM))
  have hdec := hG.dec i hiM
  rw [hsplit] at hdec
  rw [(hC i hiM).1]
  exact oRhs_frame_gen hiM hch hcb hcu hR rfl (fun _ _ => rfl) rfl (hG.ot_v i hiM)
    (fun t ht => cnt_single hC hG i t (by rw [hch, List.map_append]; exact List.mem_append_left _ ht))
    (single_o hC hG hcM) hdec

/-- **The `o` frame of `D` carries `DQ`** (both cases): if `o_N(c)` is a `DQ` of `o(c) = ψ_s(y)` and the trigger
of the `sp` step is the same in `M` and `N` (with no low part in the trigger case), then
`ψ_{v(i)}(spArg(v(i), pre, o_N(c)))` is a `DQ` of `o(i)`. -/
theorem o_frame_DQ {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {i : Nat} (hiM : i < M.length)
    {L R : List Nat} {c : Nat} (hch : children M i = L ++ c :: R) (hcb : col M c ≠ bump M i)
    (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
    (hR : ∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    {η s y oN : T} (hoc : ρ.o c = psi s y z) (hoN : Single oN) (hoNot : isOT oN = true)
    (hd : DQ η false (ρ.o c) oN) (hpre : isOT (preState M ρ i L) = true)
    (hcase : (¬ (lt (preState M ρ i L) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) ∧
        ∀ s' y', oN = psi s' y' z →
          ¬ (lt (preState M ρ i L) y' = true ∧ lt (psi (ρ.v i) z z) (psi s' y' z) = true)) ∨
      (∃ yN, oN = psi s yN z ∧ DQ η true y yN ∧
        (lt (preState M ρ i L) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) ∧
        (lt (preState M ρ i L) yN = true ∧ lt (psi (ρ.v i) z z) (psi s yN z) = true) ∧
        (split y (psi (succ s) z z)).2 = z ∧ (split yN (psi (succ s) z z)).2 = z)) :
    DQ η false (ρ.o i) (psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) oN) z) := by
  have hc : c ∈ children M i := by rw [hch]; simp
  have hcM := (mem_children hc).2
  rw [o_frame_eq hC hG hiM hch hcb hcu hR, hoc]
  rw [hoc] at hd
  rcases hcase with ⟨hnt, hntN⟩ | ⟨yN, rfl, hdy, ht, htN, hlo, hloN⟩
  · exact frame_DQ_add hpre hoN hd hnt hntN
  · have hy : isOT (psi s y z) = true := by rw [← hoc]; exact hG.ot_o c hcM
    exact frame_DQ_trig hy hoNot hdy ht htN hlo hloN

end Ytosk.WfQrL4
