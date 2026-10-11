/-
**3 行・t = 2・C（q ≠ r で q − 1 が q へ上げ、q は r で数えられない）: 種 r の ◁ を M と M.take x だけの残りから。**

- `agree_by_rank`: agree_off_at の一般形。各呼び出しの一致を「依存先が一致していれば一致」の形で受け取る
  （v(q) は右辺が M[n] でだけ末尾に 0 の項を持つので、値の式で直接合わせる）。
- C では M.take x と M[n] で x より前の右辺が違うのは o(r)・o(q)・v(q) だけ。M.take x の順位で o(r) より下で
  o(q) を通らない呼び出しは同じ値。CL_N(r) = CL_{M.take x}(r) ++ [q]、o_N(q) は q ≠ r の主の場合と同じ形。
-/
import Ytosk.V3T2SeedSV

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- **Agreement by rank**: if every call off `E` agrees as soon as the calls it reads agree, all calls off `E`
agree (`E` closed under the dependencies of `M'`). -/
theorem agree_by_rank {M' : Mat} {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (E : Bool → Nat → Prop)
    (hR' : Rk M' rk')
    (ho : ∀ i, i < M'.length → ¬ E true i → ρ'.v i = ρ.v i →
      (∀ c ∈ children M' i, Counted M' i c → ρ'.o c = ρ.o c) → ρ'.o i = ρ.o i)
    (hv : ∀ i, i < M'.length → ¬ E false i →
      (∀ m, entry M' 1 i ≠ 0 → par M' 1 i = some m → ρ'.v m = ρ.v m) →
      (∀ k, entry M' 1 i ≠ 0 → entry M' 2 i = 0 → upg M' i = some k → ρ'.v k = ρ.v k) →
      (∀ j ∈ children M' i, entry M' 1 i ≠ 0 → entry M' 2 i ≠ 0 → col M' j = bump M' i →
        ∀ k ∈ children M' j, ρ'.o k = ρ.o k) → ρ'.v i = ρ.v i)
    (hdo : ∀ i, i < M'.length → ¬ E true i →
      ¬ E false i ∧ ∀ c ∈ children M' i, Counted M' i c → ¬ E true c)
    (hdv : ∀ i, i < M'.length → ¬ E false i → entry M' 1 i ≠ 0 →
      (∀ m, par M' 1 i = some m → ¬ E false m) ∧
      (entry M' 2 i = 0 → ∀ k, upg M' i = some k → ¬ E false k) ∧
      (entry M' 2 i ≠ 0 → ∀ j ∈ children M' i, col M' j = bump M' i → ∀ k ∈ children M' j,
        ¬ E true k)) :
    ∀ i, i < M'.length → (¬ E true i → ρ'.o i = ρ.o i) ∧ (¬ E false i → ρ'.v i = ρ.v i) := by
  have key : ∀ N, ∀ i, i < M'.length → (rk' true i ≤ N → ¬ E true i → ρ'.o i = ρ.o i) ∧
      (rk' false i ≤ N → ¬ E false i → ρ'.v i = ρ.v i) := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      have hvv : ∀ i, i < M'.length → rk' false i ≤ N → ¬ E false i → ρ'.v i = ρ.v i := by
        intro i hi hN hE
        obtain ⟨_, _, hR⟩ := hR' i hi
        apply hv i hi hE
        · intro m h1 hm
          have hlt := (hR h1).1 m hm
          exact (ih _ (by omega) m (by have := par_lt M' 1 i m hm; omega)).2 (Nat.le_refl _)
            ((hdv i hi hE h1).1 m hm)
        · intro k h1 h2 hk
          have hlt := (hR h1).2.1 h2 k hk
          exact (ih _ (by omega) k (upg_lt hi hk)).2 (Nat.le_refl _) ((hdv i hi hE h1).2.1 h2 k hk)
        · intro j hj h1 h2 hb k hk
          have hlt := (hR h1).2.2 h2 j hj hb k hk
          exact (ih _ (by omega) k (mem_children hk).2).1 (Nat.le_refl _)
            ((hdv i hi hE h1).2.2 h2 j hj hb k hk)
      refine fun i hi => ⟨fun hN hE => ?_, hvv i hi⟩
      obtain ⟨hvo, hc, _⟩ := hR' i hi
      obtain ⟨hEv, hEc⟩ := hdo i hi hE
      apply ho i hi hE (hvv i hi (by omega) hEv)
      intro c hcm hcnt
      have hlt := hc c hcm hcnt.1 hcnt.2
      exact (ih _ (by omega) c (mem_children hcm).2).1 (Nat.le_refl _) (hEc c hcm hcnt)
  intro i hi
  exact ⟨fun hE => (key _ i hi).1 (Nat.le_refl _) hE, fun hE => (key _ i hi).2 (Nat.le_refl _) hE⟩

/-- **`P_0(q) = r`** for `t = 2`, `q ≠ r`. -/
theorem par0_q_t2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) : par M 0 q = some r := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrx0 : r < r + L := par_lt M 2 _ _ hr
  have hA0 : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hrq0 : Anc0 M r q := anc0_par hA0 (by have := par_lt M 0 _ _ hq; omega) hq
  obtain ⟨pq, hpq0⟩ := par0_of_anc hrq0 (fun h => hqr h.symm)
  have hrq : r < q := by have := hrq0.le; omega
  obtain ⟨qp, rfl⟩ : ∃ qp, q = r + qp := ⟨q - r, by omega⟩
  obtain ⟨Txb0, Tqb0, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq0
  have he0lt' := anc0_e0_lt hA0 (by omega)
  obtain ⟨he2r', h1lt'⟩ := par2_facts hX.z2 (by omega) hr
  have hqb' : ∀ i, par M 0 (r + qp) = some i → col M (r + qp) ≠ bump M i := by
    intro i hi; rw [hpq0] at hi; cases hi; exact Tqb0
  exact qn_par0_q hlen (by omega) hA0 hq (d0 := entry M 0 (r + L) - entry M 0 r) (by omega) (le_refl 2)
    (d1 := entry M 1 (r + L) - entry M 1 r) (by omega) he2r' h1lt' hqb'
    (par1_x_r (by omega) I.z2 I.z1 hr) hqr Txb0 hJ hX.r0p I.be

/-- **The value of the seed `r` in `M[n]`** (C case, `n ≥ 2`): the counted children of `r` are those of
`M.take x` with the values of `M.take x`, then `q` with `o_N(q)` as in the main `q ≠ r` case. -/
theorem o_r_level_C {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    (hqP : ¬ Counted (M.take (r + L)) r q) (hun : upg M (r + L - 1) = none)
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hG0 : Good3 (M.take (r + L)) τ0)
    (hR0 : Rk (M.take (r + L)) rk0) (hv0 : τ0.v r = ρ.v r) (hvq0 : τ0.v q = σ.v q)
    (hqOT : isOT (σ.o q) = true)
    (hdecN : ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
      σ.o).Pairwise (fun a b => b ≤ a)) :
    σ.v (r + L) = add (ρ.v r) (last (σ.v q)) ∧
    σ.o r = psi (ρ.v r) (step (ρ.v r) (t2X1 M r L τ0) (σ.v q)
      (step (σ.v q) z (σ.v (r + L)) (sh (ρP.v r) (σ.v (r + L)) (spArg (ρP.v r) z
        (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1))
          r).map ρP.o)))) z) z) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrx0 : r < r + L := par_lt M 2 _ _ hr
  have hA0 : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hrq0 : Anc0 M r q := anc0_par hA0 (by have := par_lt M 0 _ _ hq; omega) hq
  obtain ⟨pq, hpq0⟩ := par0_of_anc hrq0 (fun h => hqr h.symm)
  have hrq : r < q := by have := hrq0.le; omega
  obtain ⟨qp, rfl⟩ : ∃ qp, q = r + qp := ⟨q - r, by omega⟩
  have hpq' := hpq0
  obtain ⟨Txb0, Tqb0, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq'
  have hpq : par M 0 (r + qp) = some r := by
    have he0lt' := anc0_e0_lt hA0 (by omega)
    obtain ⟨he2r', h1lt'⟩ := par2_facts hX.z2 (by omega) hr
    have hqb' : ∀ i, par M 0 (r + qp) = some i → col M (r + qp) ≠ bump M i := by
      intro i hi; rw [hpq0] at hi; cases hi; exact Tqb0
    exact qn_par0_q hlen (by omega) hA0 hq (d0 := entry M 0 (r + L) - entry M 0 r) (by omega) (le_refl 2)
      (d1 := entry M 1 (r + L) - entry M 1 r) (by omega) he2r' h1lt' hqb'
      (par1_x_r (by omega) I.z2 I.z1 hr) hqr Txb0 hJ hX.r0p I.be
  rw [hpq] at hpq0; cases hpq0
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hqx : r + qp < r + L := par_lt M 0 _ _ hq
  have hqp : qp < L := by omega
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
  obtain ⟨Txb, Tqb, _, Tclq, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq
  have hqb : ∀ i, par M 0 (r + qp) = some i → col M (r + qp) ≠ bump M i := by
    intro i hi; rw [hpq] at hi; cases hi; exact Tqb
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hm1 : 1 ≤ n := by omega
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hqN : r + qp < N.length := by omega
  have hrM : r < M.length := by omega
  have hqM : r + qp < M.length := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hcolN : ∀ i, i < r + L → col N i = col M i := fun i hi => col_gexp_pre hlen hm1 hi
  have hbN : ∀ c, c < r + L → bump N c = bump M c := fun c hc => by
    unfold bump; rw [entry_gexp_pre hlen hm1 0 hc, entry_gexp_pre hlen hm1 1 hc]
  have hchN : ∀ i, i < r + L → children N i = children M i :=
    fun i hi => children_N2Q hlen hL0 hA hq hqp hd0e (by omega) hn hi
  have hIUt : ∀ c, c < r + L → c ≠ r + qp → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc hcq htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_eq_of (hchN c hc) (fun d hd => hcolN d (by
      have := (mem_children hd).2
      by_contra h'
      have hdx : d = r + L := by omega
      have := (mem_children_iff.mp hd).2; rw [hdx, hq] at this; exact hcq (Option.some.inj this).symm))
      (hbN c hc)]
    exact htM
  have hcntN : ∀ i c, i < r + L → c < r + L → c ≠ r + qp → (Counted N i c ↔ Counted M i c) :=
    fun i c hi hc hcq => counted_NQ hlen hL0 hA hq hqp hd0e hn Txb hIUt hi hc hcq
  -- `x′` counts at `q`, `q` counts at `r`
  have hx2N : entry N 2 (r + L) = 0 := by
    rw [(entry_xprimeQ hlen hL0 hA hq hqp hd0e (by omega) hn).1, he2r]
  have hxcnt : Counted N (r + qp) (r + L) := by
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col N (r + L) = (entry N 0 (r + qp) + 1, entry N 1 (r + qp), 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hq⟩
  have hsplitq := children_split_x hlen hxq
  have hCLNq : CL N (r + qp) = [r + L] := by
    unfold CL
    rw [hchN _ hqx, hsplitq, List.filter_append]
    have h1 : List.filter (fun c => decide (Counted N (r + qp) c))
        (List.filter (fun d => decide (d < r + L)) (children M (r + qp))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hcn
      have hc' := List.mem_filter.mp hc
      have hcx : c < r + L := by simpa using hc'.2
      have hcq : c ≠ r + qp := by have := (mem_children hc'.1).1; omega
      have hcntM : Counted M (r + qp) c := (hcntN _ c hqx hcx hcq).mp (by simpa using hcn)
      have hin : c ∈ CL M (r + qp) := by unfold CL; exact List.mem_filter.mpr ⟨hc'.1, by simpa using hcntM⟩
      rw [Tclq] at hin; simp at hin
    rw [h1]; simp [hxcnt]
  have hqcntN : Counted N r (r + qp) := by
    refine ⟨by rw [hcolN _ hqx, hbN r (by omega)]; exact Tqb, fun ⟨_, ht⟩ => ?_⟩
    unfold topped at ht
    rw [hchN _ hqx, hsplitq] at ht
    simp at ht
    exact hxcnt.1 ht
  have hnu : upg M (r + L - 1) ≠ some (r + L) := by rw [hun]; intro h; cases h
  have hupgN : ∀ i, i < r + L → upg N i = upg M i := fun i hi =>
    upg_NQ hlen hL0 hA hq hqp hd0e hn he2r hnu hi
  -- `M.take x` and `N` before `x`
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hrT : r < (M.take (r + L)).length := by omega
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hq] at h'; exact (Option.some.inj h').symm
  have hcntP : ∀ i c, i < r + L → c < r + L → c ≠ r + qp →
      (Counted (M.take (r + L)) i c ↔ Counted M i c) := by
    intro i c hi hc hcq
    unfold Counted
    have hu' : upg M (r + L - 1) ≠ some c := by rw [hun]; intro h; cases h
    rw [col_take M hc, bump_take M hi, isUpg_take_eq hlen hu' hc,
      topped_take_eq hlen hc (fun h => hcq (hxc c (r + L) h (le_refl _)).2)]
  have hrbP : ∀ i, r ∈ children (M.take (r + L)) i → col (M.take (r + L)) r ≠ bump (M.take (r + L)) i := by
    intro i hi hb
    have hi' : r ∈ children M i := by rw [children_take] at hi; exact (List.mem_filter.mp hi).1
    have hil : i < r := (mem_children hi').1
    rw [col_take M hrx0, bump_take M (by omega)] at hb
    have := e2_of_col (show col M r = (entry M 0 i + 1, entry M 1 i, 1) from hb); omega
  have hag := agree_by_rank (M' := M.take (r + L)) (ρ := σ) (ρ' := τ0)
    (fun b i => rk0 true r ≤ rk0 b i ∨ (b = true ∧ i = r + qp)) hR0
    (by
      intro i hi hE hvi hci
      rw [hlT] at hi
      have hir : i ≠ r := by intro e; rw [e] at hE; exact hE (Or.inl (le_refl _))
      have hiq : i ≠ r + qp := by intro e; exact hE (Or.inr ⟨rfl, e⟩)
      rw [(hC0 i (by rw [hlT]; exact hi)).1, (hCN i (by omega)).1]
      rw [oRhs_congr (ρ₂ := σ) hvi (fun c hc hb hu => hci c hc ⟨hb, hu⟩), ← hT]
      apply oRhs_takeX
      · intro c hc
        rw [hchN i hi] at hc
        by_contra h'
        exact hiq (hxc i c hc (by omega)).2
      · intro c hc
        rw [hchN i hi] at hc
        have hcx : c < r + L := by
          by_contra h'
          exact hiq (hxc i c hc (by omega)).2
        have hcq : c ≠ r + qp := by
          intro e; rw [e] at hc; rw [(mem_children_iff.mp hc).2] at hpq; cases hpq; exact hir rfl
        rw [hT]
        exact (hcntP i c hi hcx hcq).trans (hcntN i c hi hcx hcq).symm)
    (by
      intro i hi hE hp1 hup hbk
      rw [hlT] at hi
      by_cases hiq : i = r + qp
      · rw [hiq]; exact hvq0
      rw [(hC0 i (by rw [hlT]; exact hi)).2, (hCN i (by omega)).2]
      rw [vRhs_congr (ρ₂ := σ) (fun m h1 hm => hp1 m h1 hm) (fun k h1 h2 hk => hup k h1 h2 hk)
        (fun j hj h1 h2 hb k hk => hbk j hj h1 h2 hb k hk), ← hT]
      apply vRhs_takeX hi
      · by_cases hi1 : i + 1 < r + L
        · exact upg_take N hi1
        · have hix : i = r + L - 1 := by omega
          rw [hix, upg_take_last N (by omega) (by omega), hupgN _ (by omega), hun]
      · intro h2'
        rw [hchN i hi]
        refine ⟨fun c hc => ?_, fun j hj hjb c hc => ?_⟩
        · by_contra h'
          exact hiq (hxc i c hc (by omega)).2
        · have hjx : j < r + L := by
            by_contra h'
            exact hiq (hxc i j hj (by omega)).2
          have hjq : j ≠ r + qp := by
            intro e
            rw [e] at hjb hj
            have hpi := (mem_children_iff.mp hj).2
            rw [hpq] at hpi; cases hpi
            rw [hcolN _ hqx, hbN r (by omega)] at hjb
            exact Tqb hjb
          rw [hchN j hjx] at hc
          by_contra h'
          exact hjq (hxc j c hc (by omega)).2)
    (by
      intro i hi hE
      refine ⟨fun h => ?_, fun c hc hcnt h => ?_⟩
      · rcases h with h | ⟨h, _⟩
        · exact hE (Or.inl (le_trans h (le_of_lt (hR0 i hi).1)))
        · cases h
      · rcases h with h | ⟨_, hcq⟩
        · exact hE (Or.inl (le_trans h (le_of_lt ((hR0 i hi).2.1 c hc hcnt.1 hcnt.2))))
        · rw [hcq] at hc
          have hpi := (mem_children_iff.mp hc).2
          rw [par_take M 0 _ (by omega), hpq] at hpi; cases hpi
          exact hE (Or.inl (le_refl _)))
    (by
      intro i hi hE h1
      obtain ⟨hp1, hup, hbk⟩ := (hR0 i hi).2.2 h1
      have hE' : ¬ rk0 true r ≤ rk0 false i := fun h => hE (Or.inl h)
      refine ⟨fun m hm h => ?_, fun h2' k hk h => ?_, fun h2' j hj hjb k hk h => ?_⟩
      · rcases h with h | ⟨h, _⟩
        · exact hE' (le_trans h (le_of_lt (hp1 m hm)))
        · cases h
      · rcases h with h | ⟨h, _⟩
        · exact hE' (le_trans h (le_of_lt (hup h2' k hk)))
        · cases h
      · rcases h with h | ⟨_, hkq⟩
        · exact hE' (le_trans h (le_of_lt (hbk h2' j hj hjb k hk)))
        · rw [hkq] at hk
          have hpj := (mem_children_iff.mp hk).2
          rw [par_take M 0 _ (by omega), hpq] at hpj; cases hpj
          exact hrbP i hj hjb)
  have hval : ∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d := by
    intro d hd
    have hdc := cl_mem_children hd
    have hcnt : Counted (M.take (r + L)) r d := by simpa using (List.mem_filter.mp hd).2
    have hdq : d ≠ r + qp := by intro e; rw [e] at hcnt; exact hqP hcnt
    refine ((hag d (mem_children hdc).2).1 ?_).symm
    rintro (h | ⟨_, h⟩)
    · have := (hR0 r hrT).2.1 d hdc hcnt.1 hcnt.2; omega
    · exact hdq h
  have hvr : σ.v r = ρ.v r := by
    rw [← hv0]
    refine ((hag r hrT).2 ?_).symm
    rintro (h | ⟨h, _⟩)
    · have := (hR0 r hrT).1; omega
    · cases h
  -- the counted children of `r` in `N`
  have hqc : r + qp ∈ children M r := mem_children_iff.mpr ⟨by omega, hpq⟩
  have hqlast : children M r = (children M r).filter (fun d => decide (d < r + qp)) ++ [r + qp] := by
    apply split_last_max _ _ (children_sorted M r) hqc
    intro d hd
    by_contra hlt
    have hdx : d < r + L := by
      have := (mem_children hd).2
      by_contra h'
      have hd' : d = r + L := by omega
      rw [hd'] at hd; have h' := (mem_children_iff.mp hd).2; rw [hq] at h'; have := Option.some.inj h'; omega
    have hAq : Anc0 M (r + qp) (r + L) := Anc0.step hq (Anc0.refl _)
    have hAd : Anc0 M (r + qp) d := anc_between hAq d (by omega) (by omega)
    have hAr := anc0_par hAd (by omega) (mem_children_iff.mp hd).2
    have := hAr.le; omega
  have hCLN : CL N r = CL (M.take (r + L)) r ++ [r + qp] := by
    unfold CL
    have hall : ∀ d ∈ children M r, d < r + L := by
      intro d hd
      by_contra h'
      have := (hxc r d hd (by omega)).2; omega
    rw [hchN r (by omega), children_take, show (children M r).filter (fun d => decide (d < r + L)) = children M r
      from List.filter_eq_self.mpr (fun d hd => by simpa using hall d hd)]
    conv_lhs => rw [hqlast, List.filter_append]
    conv_rhs => rw [hqlast, List.filter_append]
    rw [show List.filter (fun c => decide (Counted N r c)) [r + qp] = [r + qp] by simp [hqcntN],
      show List.filter (fun c => decide (Counted (M.take (r + L)) r c)) [r + qp] = [] by simp [hqP],
      List.append_nil]
    congr 1
    apply List.filter_congr
    intro c hc
    have hc' := List.mem_filter.mp hc
    have hcq : c < r + qp := by simpa using hc'.2
    simp only [decide_eq_decide]
    exact (hcntN r c (by omega) (by omega) (by omega)).trans (hcntP r c (by omega) (by omega) (by omega)).symm
  -- the copy root `x′`
  have hCR := t2CopyResAll_holds M ρ rk hM hS I R hz h2 r L hlen hr
  have hBEP : BumpE2 P := by rw [hP, ← hexp (n - 1)]; exact (sInvX_expand hX (n - 1)).loc.2.2.1
  obtain ⟨hKV, hB', hV', hVV⟩ := hCR n hn σ ρP hCN hCP hGP
  have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP
  have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hX.r0p hX.loc.1
  have hF := copy_facts_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP hCN hCP hGP hRP hK hKV hRK hB' hV' hVV
  have hox := o_copy_root hCN hCP hGP hF hrP hxN hV' hVV rfl
  -- `v(x′) = a + last(v_N(q))`
  have hvq := vq_N hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 (by omega) Txb I.be I.uat hUN I.cons I.good hCN hRN
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hvx : σ.v (r + L) = add (ρ.v r) (last (σ.v (r + qp))) := by
    rw [(hCN (r + L) hxN).2]; unfold vRhs
    have he1 : entry N 1 (r + L) ≠ 0 := by
      have := entry1_xN hlen hL0 hA hq hd0e hn hd1e
      rw [← hN] at this; rw [this]; omega
    rw [if_neg he1, if_pos hx2N]
    have hp1 := par1_xN hlen hL0 hA hq hd0e hn hd1e
    rw [hr1, ← hN] at hp1
    have hu := upg_N_x_q hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 (by omega) Txb hJ hX.r0p I.be
    rw [← hN] at hu
    rw [hp1, hu]
    show sf (add (σ.v r) (last (σ.v (r + qp)))) = _
    rw [hvr, sf_ot (isOT_add hVot (isOT_last hvq.1))]
  refine ⟨hvx, ?_⟩
  -- the frame of `q`: only `x′`
  have hPo : isOT (psi (ρP.v r) (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o))) z) = true := by
    rw [← o_cl_eq hCP hGP hrP]; exact hGP.ot_o r hrP
  have hxOT : isOT (psi (σ.v (r + L)) (sh (ρP.v r) (σ.v (r + L))
      (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o)))) z) = true := by
    have := isOT_shTop (V' := σ.v (r + L)) (hGP.ot_v r hrP) hV' hVV hPo (le_refl _)
    rwa [shf_self] at this
  have hoq := o_last_form (Lc := []) hCN hqN hvq.1 (by rw [hCLNq]; rfl)
    (fun c hc => by rw [hCLNq] at hc; simp at hc; rw [hc, hox]; exact ⟨hxOT, _, _, rfl⟩)
    (by rw [hCLNq]; simp) hox
  -- the frame of `r`
  -- the frame of `r`
  have hoqf : ∃ s y, σ.o (r + qp) = psi s y z := ⟨_, _, hoq⟩
  have hsN : ∀ c ∈ CL N r, Single (σ.o c) := by
    intro c hc
    rw [hCLN] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [hval c hc]
      exact single_o hC0 hG0 (mem_children (cl_mem_children hc)).2
    · simp at hc; rw [hc]; exact ⟨hqOT, hoqf⟩
  have hor := o_last_form hCN hrN (by rw [hvr]; exact hVot) hCLN hsN hdecN hoq
  rw [hor, hvr, List.map_congr_left hval]
  unfold t2X1; rw [hv0]
  rfl

/-- **The residual of the seed `r` in the C case** (`q ≠ r`, `q` not counted at `r`): properties of `M` and
`M.take x`. With `X₁` the argument of `r` in `M.take x` and `s′ = v_N(q)`: every level rewrites to `σ(X)`, and
`ψ_V(σ^k X₁) ◁ o_M(r)` for `k ≥ 1`. -/
structure T2SeedCRes (M : Mat) (ρ : Valn) (r L q : Nat) : Prop where
  qP : ¬ Counted (M.take (r + L)) r q
  un : upg M (r + L - 1) = none
  vP : ∀ τ, Cons (M.take (r + L)) τ → τ.v r = ρ.v r
  vqP : ∀ τ, Cons (M.take (r + L)) τ → τ.v q = qnS M ρ r L q
  rw : ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
    step (ρ.v r) (t2X1 M r L τ) (qnS M ρ r L q) (step (qnS M ρ r L q) z (qnS M ρ r L q)
      (sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)) z) z =
    sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)
  lhd : ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k →
    Lhd z (psi (ρ.v r) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k) z) (ρ.o r)

/-- **The value of the seed `r` in every `M[n]`** (C case, `n ≥ 2`): `ψ_V(σ^{n−1} X₁)`. -/
theorem seed_r_value_C {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hRes : T2SeedCRes M ρ r L q)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : Rk (M.take (r + L)) rk0) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      isOT (σ.o q) = true →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
        σ.o r = psi (ρ.v r) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ0) (n - 1)) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hRk : ∀ m, 1 ≤ m → ∃ rk', Rk (TRIO.gexp M r L d0 d1 m) rk' := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
  have hv0 := hRes.vP τ0 hC0
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ihs =>
  intro hGlow σ hCN hqOT hdecN
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  have hG0 : Good3 (M.take (r + L)) τ0 := by
    have h := hGlow 1 (le_refl 1) (by omega) τ0 (by rw [hP1]; exact hC0)
    rwa [hP1] at h
  have hvq : σ.v q = qnS M ρ r L q := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  have hvq0 : τ0.v q = σ.v q := by rw [hvq]; exact hRes.vqP τ0 hC0
  have key : ∀ (ρP : Valn) (rkP : Bool → Nat → Nat), Cons (TRIO.gexp M r L d0 d1 (n - 1)) ρP →
      Good3 (TRIO.gexp M r L d0 d1 (n - 1)) ρP → Rk (TRIO.gexp M r L d0 d1 (n - 1)) rkP → ρP.v r = ρ.v r →
      spArg (ρP.v r) z (sumN ((CL (TRIO.gexp M r L d0 d1 (n - 1)) r).map ρP.o)) =
        shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ0) (n - 2) →
      σ.o r = psi (ρ.v r) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ0) (n - 1)) z := by
    intro ρP rkP hCP hGP hRP hvP hXP
    obtain ⟨hvx, hor⟩ := o_r_level_C hM hS I R hz h2 hlen hr hq hqr hRes.qP hRes.un hn hCN hRN hCP hGP hRP
      hC0 hG0 hR0 hv0 hvq0 hqOT hdecN
    have hvx' : σ.v (r + L) = qnS M ρ r L q := by rw [hvx, hvq]; exact qnS_vxs M ρ r L q
    rw [hor, hvx', hvq, hXP, hvP, show n - 1 = (n - 2) + 1 by omega, hRes.rw τ0 hC0 (n - 2)]
    rfl
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have hn2 : n = 2 := by omega
    subst hn2
    have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show 2 - 1 = 1 from rfl, hP1]; exact hC0
    have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show 2 - 1 = 1 from rfl, hP1]; exact hG0
    have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show 2 - 1 = 1 from rfl, hP1]; exact hR0
    exact key τ0 rk0 hCP hGP hRP hv0 (by rw [show 2 - 1 = 1 from rfl, hP1]; rfl)
  · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
    have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
    have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
    have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
    have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
    have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by omega
    have hqP' : q < (TRIO.gexp M r L d0 d1 (n - 1)).length := by omega
    have hP := ihs (n - 1) (by omega) (by omega) (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP
      (hGP.ot_o q hqP') (by rw [← cvals_eq_mapC hCP]; exact hGP.dec r hrP)
    have hform := o_cl_eq hCP hGP hrP
    rw [hP] at hform
    simp only [psi.injEq] at hform
    refine key _ rkP hCP hGP hRP hform.1.symm ?_
    rw [← hform.2.1, show n - 1 - 1 = n - 2 by omega]

/-- **SeedL in the C case**: `o_N(r) ◁ o_M(r)` for every `M[n]` (`n ≥ 2`). -/
theorem seedL_C {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hRes : T2SeedCRes M ρ r L q) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      isOT (σ.o q) = true →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
        Lhd z (σ.o r) (ρ.o r) := by
  intro n hn hGlow σ hCN hqOT hdecN
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  rw [seed_r_value_C hM hS I R hz h2 hlen hr hq hqr hRes hC0 hRk1 n hn hGlow σ hCN hqOT hdecN]
  exact hRes.lhd _ hC0 (n - 1) (by omega)

end Ytosk
