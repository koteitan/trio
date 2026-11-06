/-
**t = 2, C2, shape 2 with a path of length 1 (2026-11-06, in progress).**

In C2 the last counted child `c₀` of `r` has a counted child; in 170 of the 174 measured frames `w = q − 1` is the last
counted child of `c₀` and a leaf, `e2 w = 0`, `upg w = q`.  Step 1: the closure of the calls whose equations differ
between `M` and `N = M[n]` (the subtree of `q`, `o(r)`) is the subtree of `q`, the calls of rank at least `o(r)`, and
`v(w)`, `o(w)`, `o(c₀)` (`depS_C2_inv`, with the template `depS_SQ_inv`).
-/
import Ytosk.V3CanonBump

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The seeds: the subtree of `q` and `o(r)`. -/
def SC2 (M : Mat) (q r : Nat) : Bool → Nat → Prop := fun b i => Anc0 M q i ∨ (b = true ∧ i = r)

theorem depS_C2_inv {M : Mat} {rk : Bool → Nat → Nat} (hR : Rk M rk) {q r c0 w : Nat}
    (hpq : par M 0 q = some r) (hqb : col M q ≠ bump M r) (he2r : entry M 2 r = 0)
    (hpc0 : par M 0 c0 = some r) (hc0b : col M c0 ≠ bump M r)
    (hpw : par M 0 w = some c0) (hwq : w + 1 = q) (hwleaf : children M w = []) (he2w : entry M 2 w = 0) :
    ∀ {b i}, DepS M (SC2 M q r) b i → i < M.length →
      Anc0 M q i ∨ rk true r ≤ rk b i ∨ (b = false ∧ i = w) ∨ (b = true ∧ (i = w ∨ i = c0)) := by
  intro b i h
  induction h with
  | @seed b i hs =>
    intro _
    rcases hs with hA | ⟨rfl, rfl⟩
    · exact Or.inl hA
    · exact Or.inr (Or.inl (le_refl _))
  | @ochild i c hc hcb hcu _ ih =>
    intro hi
    have hrk := (hR _ hi).2.1 _ hc hcb hcu
    have hpc := (mem_children_iff.mp hc).2
    rcases ih (mem_children hc).2 with hA | hle | ⟨h1, _⟩ | ⟨_, hcw | hcc⟩
    · by_cases hcq : c = q
      · subst hcq
        have : i = r := by rw [hpc] at hpq; exact Option.some.inj hpq
        subst this; exact Or.inr (Or.inl (le_refl _))
      · exact Or.inl (anc0_par hA (Ne.symm hcq) hpc)
    · exact Or.inr (Or.inl (by omega))
    · cases h1
    · subst hcw
      have : i = c0 := by rw [hpc] at hpw; exact Option.some.inj hpw
      subst this; exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩))
    · subst hcc
      have : i = r := by rw [hpc] at hpc0; exact Option.some.inj hpc0
      subst this; exact Or.inr (Or.inl (le_refl _))
  | @ov i _ ih =>
    intro hi
    have := (hR _ hi).1
    rcases ih hi with hA | hle | ⟨_, hiw⟩ | ⟨h1, _⟩
    · exact Or.inl hA
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl hiw⟩))
    · cases h1
  | @vpar i m h1 hm _ ih =>
    intro hi
    have hrk := ((hR _ hi).2.2 h1).1 _ hm
    rcases ih (by have := par_lt _ 1 _ _ hm; omega) with hA | hle | ⟨_, hmw⟩ | ⟨h2, _⟩
    · exact Or.inl (Anc0.trans hA (anc0_of_par M 1 m i hm))
    · exact Or.inr (Or.inl (by omega))
    · exfalso
      subst hmw
      have hAi := anc0_of_par M 1 m i hm
      have hne : m ≠ i := by have := par_lt M 1 i m hm; omega
      obtain ⟨c, hcw, hAc⟩ := anc0_child hAi hne
      have hcM : c ∈ children M m := mem_children_iff.mpr ⟨by have := hAc.le; omega, hcw⟩
      rw [hwleaf] at hcM; simp at hcM
    · cases h2
  | @vupg i k h1 h2 hk _ ih =>
    intro hi
    have hrk := ((hR _ hi).2.2 h1).2.1 h2 _ hk
    rcases ih (upg_lt hi hk) with hA | hle | ⟨_, hkw⟩ | ⟨h3, _⟩
    · obtain ⟨_, _, _, _, hcase⟩ := upg_spec hk
      rcases hcase with hk1 | ⟨hAk, _⟩
      · by_cases hkq : k = q
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
        · have hqk := hA.le
          exact Or.inl (anc_between hA i (by omega) (by omega))
      · exact Or.inl (Anc0.trans hA hAk)
    · exact Or.inr (Or.inl (by omega))
    · exfalso
      subst hkw
      have := upg_target_e2 hk; omega
    · cases h3
  | @vbump i j k h1 h2 hj hjb hk _ ih =>
    intro hi
    have hrk := ((hR _ hi).2.2 h1).2.2 h2 _ hj hjb _ hk
    have hkl := (mem_children hk).2
    have hpk := (mem_children_iff.mp hk).2
    have hpj := (mem_children_iff.mp hj).2
    rcases ih hkl with hA | hle | ⟨h3, _⟩ | ⟨_, hkw | hkc⟩
    · by_cases hkq : k = q
      · subst hkq
        have hjr : j = r := by rw [hpk] at hpq; exact Option.some.inj hpq
        subst hjr
        exfalso
        have := e2_of_col (show col M j = (entry M 0 i + 1, entry M 1 i, 1) from hjb); omega
      · have hAj : Anc0 M q j := anc0_par hA (Ne.symm hkq) hpk
        by_cases hjq : j = q
        · subst hjq
          have hir : i = r := by rw [hpj] at hpq; exact Option.some.inj hpq
          subst hir
          exact absurd hjb hqb
        · exact Or.inl (anc0_par hAj (Ne.symm hjq) hpj)
    · exact Or.inr (Or.inl (by omega))
    · cases h3
    · subst hkw
      have hjc : j = c0 := by rw [hpk] at hpw; exact Option.some.inj hpw
      subst hjc
      have hir : i = r := by rw [hpj] at hpc0; exact Option.some.inj hpc0
      subst hir
      exact absurd hjb hc0b
    · subst hkc
      have hjr : j = r := by rw [hpk] at hpc0; exact Option.some.inj hpc0
      subst hjr
      exfalso
      have := e2_of_col (show col M j = (entry M 0 i + 1, entry M 1 i, 1) from hjb); omega

#print axioms depS_C2_inv

/-- **Step 2: off the closure `DepS M (SC2 M q r)`, `N` and `M` have the same values** (`q ≠ r`, `n ≥ 2`).  The calls
whose equations differ (`o(r)`, the subtree of `q`, the column `x`) are seeds, so `agree_by_rank` applies with the
closure as exception set. -/
theorem C_dep_agree {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {n : Nat} (hn : 2 ≤ n) {σ : Valn}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ) :
    ∀ i, i < M.length → (¬ DepS M (SC2 M q r) true i → σ.o i = ρ.o i) ∧
      (¬ DepS M (SC2 M q r) false i → σ.v i = ρ.v i) := by
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
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hq] at h'; exact (Option.some.inj h').symm
  have hAqx : Anc0 M (r + qp) (r + L) := Anc0.step hq (Anc0.refl _)
  have hag := agree_by_rank (M' := M) (ρ := σ) (ρ' := ρ) (fun b i => DepS M (SC2 M (r + qp) r) b i) I.rank
    (by
      intro i hi hE hvi hci
      have hir : i ≠ r := fun e => hE (DepS.seed (Or.inr ⟨rfl, e⟩))
      have hiq : i ≠ r + qp := fun e => hE (DepS.seed (Or.inl (by rw [e]; exact Anc0.refl _)))
      have hix : i ≠ r + L := fun e => hE (DepS.seed (Or.inl (by rw [e]; exact hAqx)))
      have hix' : i < r + L := by omega
      rw [(I.cons i hi).1, (hCN i (by omega)).1]
      unfold oRhs
      rw [hvi, hchN i hix']
      have hmap : (children M i).map (cnt M ρ i) = (children M i).map (cnt N σ i) := by
        apply List.map_congr_left
        intro c hc
        have hcx : c < r + L := by
          by_contra h'
          exact hiq (hxc i c hc (by omega)).2
        have hcq : c ≠ r + qp := by
          intro e; rw [e] at hc; rw [(mem_children_iff.mp hc).2] at hpq; cases hpq; exact hir rfl
        rw [cnt_eq_ite, cnt_eq_ite]
        by_cases hcnt : Counted M i c
        · rw [if_pos hcnt, if_pos ((hcntN i c hix' hcx hcq).mpr hcnt)]
          exact hci c hc hcnt
        · rw [if_neg hcnt, if_neg (fun h => hcnt ((hcntN i c hix' hcx hcq).mp h))]
      rw [hmap])
    (by
      intro i hi hE hp1 hup hbk
      have hiq : i ≠ r + qp := fun e => hE (DepS.seed (Or.inl (by rw [e]; exact Anc0.refl _)))
      have hix : i ≠ r + L := fun e => hE (DepS.seed (Or.inl (by rw [e]; exact hAqx)))
      have hix' : i < r + L := by omega
      rw [(I.cons i hi).2, (hCN i (by omega)).2]
      unfold vRhs
      rw [entry_gexp_pre hlen hm1 1 hix', entry_gexp_pre hlen hm1 2 hix']
      have hpar : par N 1 i = par M 1 i := by rw [← par_take N 1 i hix', hT, par_take M 1 i hix']
      rw [hpar]
      by_cases h1 : entry M 1 i = 0
      · simp only [h1, if_true]
      rw [if_neg h1, if_neg h1]
      have hvo : vOpt ρ (par M 1 i) = vOpt σ (par M 1 i) := by
        cases hm : par M 1 i with
        | none => rfl
        | some m => exact hp1 m h1 hm
      by_cases h2' : entry M 2 i = 0
      · rw [if_pos h2', if_pos h2']
        have hupg : upg N i = upg M i := by
          rcases Nat.lt_or_ge (i + 1) (r + L) with h | h
          · rw [← upg_take _ h, hT, upg_take M h]
          · have hi1 : i = r + L - 1 := by omega
            have hnu : upg M (r + L - 1) ≠ some (r + L) := by
              intro hu
              exact hE (DepS.vupg h1 h2' (by rw [hi1]; exact hu) (DepS.seed (Or.inl hAqx)))
            rw [hi1]
            exact upg_NQ hlen hL0 hA hq hqp hd0e hn he2r hnu (by omega)
        rw [hupg, hvo]
        cases hk : upg M i with
        | none => rfl
        | some k =>
          show sf (add (vOpt σ (par M 1 i)) (last (ρ.v k))) = sf (add (vOpt σ (par M 1 i)) (last (σ.v k)))
          rw [hup k h1 h2' hk]
      · rw [if_neg h2', if_neg h2', hvo, hchN i hix']
        have hbt : (children M i).map (bumpTerm M ρ i) = (children M i).map (bumpTerm N σ i) := by
          apply List.map_congr_left
          intro j hj
          have hjx : j < r + L := by
            by_contra h'
            exact hiq (hxc i j hj (by omega)).2
          unfold bumpTerm
          rw [hcolN j hjx, hbN i hix']
          by_cases hjb : col M j = bump M i
          · rw [if_pos hjb, if_pos hjb, hchN j hjx]
            rw [List.map_congr_left (fun k hk => hbk j hj h1 h2' hjb k hk)]
          · rw [if_neg hjb, if_neg hjb]
        rw [hbt])
    (fun i hi hE => ⟨fun h => hE (DepS.ov h), fun c hc hcnt h => hE (DepS.ochild hc hcnt.1 hcnt.2 h)⟩)
    (fun i hi hE h1 => ⟨fun m hm h => hE (DepS.vpar h1 hm h), fun h2' k hk h => hE (DepS.vupg h1 h2' hk h),
      fun h2' j hj hjb k hk h => hE (DepS.vbump h1 h2' hj hjb hk h)⟩)
  intro i hi
  exact ⟨fun h => ((hag i hi).1 h).symm, fun h => ((hag i hi).2 h).symm⟩

#print axioms C_dep_agree

/-- **Step 3: `v_N(w) ≤ v_M(w)` for `w = q − 1` upgraded to `q`.**  `v(w) = v(r) + last(v(q))` in both (`P_1 w = P_1 q = r`),
`v_N(q) = v(r) + ω^S` (`vq_eq_gexp`) and `v_M(q) = v(r) + ω^{S+1}` (the bump term `1` of `x`, as in `qn_vqlt`). -/
theorem C2_vw_le {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {n : Nat} (hn : 2 ≤ n) {σ : Valn}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    {w : Nat} (hwq : w + 1 = q) (hu : upg M w = some q) : σ.v w ≤ ρ.v w := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 q r hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, _, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he2q : entry M 2 q = 1 := I.be q (r + L) hxq Txb
  have he1q : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  have h1lt := (par2_facts I.z2 (show r + L < M.length by omega) hr).2
  have hp1q : par M 1 q = some r := par1_of_child hpq (by omega)
  have hsplit := split_last_max _ _ (children_sorted M q) hxq
    (fun d hd => by have := (mem_children hd).2; omega)
  set Lq := (children M q).filter (fun d => decide (d < r + L)) with hLqd
  have hbx : bumpTerm M ρ q (r + L) = one := by
    unfold bumpTerm; rw [if_pos Txb, children_last (by omega)]; rfl
  have hqM : q < M.length := by omega
  have hv := (I.cons q hqM).2
  unfold vRhs at hv
  rw [if_neg (by omega), if_neg (by omega), hp1q, hsplit, List.map_append, List.map_singleton, hbx] at hv
  change ρ.v q = sf (add (ρ.v r) (omega (sumN (one :: (Lq.map (bumpTerm M ρ q) ++ [one]))))) at hv
  set S := sumN (one :: Lq.map (bumpTerm M ρ q)) with hSdef
  have hOT : ∀ t ∈ one :: Lq.map (bumpTerm M ρ q), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm I.good q d
  have hSot : isOT S = true := isOT_sumN _ hOT
  have hS1 : sumN (one :: (Lq.map (bumpTerm M ρ q) ++ [one])) = sf (add S one) := by
    simp only [hSdef, sumN, List.foldl_cons, List.foldl_append, List.foldl_nil]
  rw [hS1] at hv
  have hA1 : isOT (add S one) = true := isOT_add hSot rfl
  rw [sf_ot hA1] at hv
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  have hW : isOT (add (ρ.v r) (omega (add S one))) = true := isOT_add hVot (isOT_omega hA1)
  rw [sf_ot hW] at hv
  -- the last summands of `v(q)`
  have hvqN : σ.v q = qnS M ρ r L q := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  have hlastN : last (σ.v q) = omega S := by
    rw [hvqN]; unfold qnS
    obtain ⟨s0, y0, hw0⟩ := omega_psi_form S
    rw [show sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q)) = S from rfl,
      hw0, last_add_single]
  have hlastM : last (ρ.v q) = omega (add S one) := by
    rw [hv]
    obtain ⟨s0, y0, hw0⟩ := omega_psi_form (add S one)
    rw [hw0, last_add_single]
  have hlast : last (σ.v q) ≤ last (ρ.v q) := by
    rw [hlastN, hlastM]
    apply le_of_lt
    apply omega_lt_omega hSot hA1
    have := add_lt_add_left S (show z < one from rfl)
    rwa [add_z_right] at this
  -- `v(w)` in `N` and `M`
  have hwx : w + 1 < r + L := by omega
  have hwM : w < M.length := by omega
  obtain ⟨he1w, he2w'⟩ := upg_e12 hu
  have he2w : entry M 2 w = 0 := by have := I.z2 w; omega
  obtain ⟨m, hm1, hmq, _, _⟩ := upg_spec hu
  rw [hp1q] at hmq; cases hmq
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hm1n : 1 ≤ n := by omega
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen hm1n
  have hvr : σ.v r = ρ.v r := (C_root hM hS I hz h2 hlen hr hq hqr hn hCN).1
  have hpar : par N 1 w = par M 1 w := by
    rw [← par_take N 1 w (show w < r + L by omega), hT, par_take M 1 w (show w < r + L by omega)]
  have hupg : upg N w = upg M w := by rw [← upg_take _ hwx, hT, upg_take M hwx]
  have hvN : σ.v w = sf (add (σ.v r) (last (σ.v q))) := by
    rw [(hCN w (by omega)).2]; unfold vRhs
    rw [entry_gexp_pre hlen hm1n 1 (by omega), entry_gexp_pre hlen hm1n 2 (by omega), if_neg he1w, if_pos he2w,
      hpar, hupg, hm1, hu]
    rfl
  have hvM : ρ.v w = sf (add (ρ.v r) (last (ρ.v q))) := by
    rw [(I.cons w hwM).2]; unfold vRhs
    rw [if_neg he1w, if_pos he2w, hm1, hu]
    rfl
  have hlqN : isOT (last (σ.v q)) = true := by rw [hlastN]; exact isOT_omega hSot
  have hlqM : isOT (last (ρ.v q)) = true := by rw [hlastM]; exact isOT_omega hA1
  rw [hvN, hvM, hvr, sf_ot (isOT_add hVot hlqN), sf_ot (isOT_add hVot hlqM)]
  exact add_le_add_left _ hlast

#print axioms C2_vw_le

/-- **Step 4: the C2 frames of shape 2 with a path of length 1.**  `w = q − 1` is the last counted child of `c₀`,
a leaf, upgraded to `q`.  The earlier counted children of `r` keep their `o`; `o(c₀)` keeps its subscript and its
argument `B + Ω_{v(w)}` does not grow. -/
theorem C2_len1 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc0 : List Nat} {c0 : Nat} (hT : CL M r = Lc0 ++ [c0])
    {w : Nat} {Le : List Nat} (hwq : w + 1 = q) (hpw : par M 0 w = some c0) (hwleaf : children M w = [])
    (hu : upg M w = some q) (hLe : CL M c0 = Le ++ [w])
    {n : Nat} (hn : 2 ≤ n) {σ : Valn} (hCN : Cons (G2 M r L n) σ) (hGN : Good3 (G2 M r L n) σ) :
    (∀ d ∈ Lc0, σ.o d = ρ.o d) ∧
      ∀ s y, σ.o c0 = psi s y z → y ≠ z → ∃ yM, ρ.o c0 = psi s yM z ∧ y ≤ yM := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 q r hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨_, Tqb, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Tqb
  have he2r : entry M 2 r = 0 := (par2_facts I.z2 (show r + L < M.length by omega) hr).1
  obtain ⟨he1w, he2w'⟩ := upg_e12 hu
  have he2w : entry M 2 w = 0 := by have := I.z2 w; omega
  have hc0CL : c0 ∈ CL M r := by rw [hT]; simp
  have hc0c := cl_mem_children hc0CL
  have hpc0 : par M 0 c0 = some r := (mem_children_iff.mp hc0c).2
  have hc0cnt : Counted M r c0 := by simpa using (List.mem_filter.mp hc0CL).2
  have hrc0 : r < c0 := par_lt M 0 c0 r hpc0
  have hc0w : c0 < w := par_lt M 0 w c0 hpw
  have hwM : w < M.length := by omega
  have hc0M : c0 < M.length := by omega
  have hag := C_dep_agree hM hS I hz h2 hlen hr hq hqr hn hCN
  have hnd : ∀ b i, i < M.length → i < q → rk b i < rk true r → ¬ (b = false ∧ i = w) →
      ¬ (b = true ∧ (i = w ∨ i = c0)) → ¬ DepS M (SC2 M q r) b i := by
    intro b i hi hiq hrk h3 h4 hD
    rcases depS_C2_inv I.rank hpq Tqb he2r hpc0 hc0cnt.1 hpw hwq hwleaf he2w hD hi with h | h | h | h
    · have := h.le; omega
    · omega
    · exact h3 h
    · exact h4 h
  -- the order of the counted children
  have hsortR : (CL M r).Pairwise (· < ·) := (children_sorted M r).filter _
  have hsortC : (CL M c0).Pairwise (· < ·) := (children_sorted M c0).filter _
  rw [hT] at hsortR
  rw [hLe] at hsortC
  have hRc0 := (I.rank r hrM).2.1 c0 hc0c hc0cnt.1 hc0cnt.2
  refine ⟨fun d hd => ?_, fun s y hsy _ => ?_⟩
  · have hdc0 : d < c0 := (List.pairwise_append.mp hsortR).2.2 d hd c0 (by simp)
    have hdCL : d ∈ CL M r := by rw [hT]; exact List.mem_append_left _ hd
    have hdcnt : Counted M r d := by simpa using (List.mem_filter.mp hdCL).2
    have hRd := (I.rank r hrM).2.1 d (cl_mem_children hdCL) hdcnt.1 hdcnt.2
    have hdM : d < M.length := by omega
    exact (hag d hdM).1 (hnd true d hdM (by omega) hRd (fun h => by cases h.1)
      (fun ⟨_, h⟩ => by rcases h with h | h <;> omega))
  · -- `v(c₀)` and the earlier children of `c₀` agree
    have hvc0 : σ.v c0 = ρ.v c0 := (hag c0 hc0M).2 (hnd false c0 hc0M (by omega)
      (lt_trans (I.rank c0 hc0M).1 hRc0) (fun ⟨_, h⟩ => by omega) (fun ⟨h, _⟩ => by cases h))
    have hLeo : ∀ e ∈ Le, σ.o e = ρ.o e := by
      intro e he
      have hew : e < w := (List.pairwise_append.mp hsortC).2.2 e he w (by simp)
      have heCL : e ∈ CL M c0 := by rw [hLe]; exact List.mem_append_left _ he
      have hecnt : Counted M c0 e := by simpa using (List.mem_filter.mp heCL).2
      have hpe : par M 0 e = some c0 := (mem_children_iff.mp (cl_mem_children heCL)).2
      have hc0e : c0 < e := par_lt M 0 e c0 hpe
      have hRe := (I.rank c0 hc0M).2.1 e (cl_mem_children heCL) hecnt.1 hecnt.2
      have heM : e < M.length := by omega
      exact (hag e heM).1 (hnd true e heM (by omega) (lt_trans hRe hRc0) (fun h => by cases h.1)
        (fun ⟨_, h⟩ => by rcases h with h | h <;> omega))
    -- the leaf `w`
    have hlN : (G2 M r L n).length = r + n * L := TRIO.gexp_length hlen
    have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
    have hwN : w < (G2 M r L n).length := by omega
    have hc0N : c0 < (G2 M r L n).length := by omega
    have hCLw : CL M w = [] := by unfold CL; rw [hwleaf]; rfl
    have hCLNw : CL (G2 M r L n) w = [] := by
      rw [C_cl_eq hM hS I hz h2 hlen hr hq hqr hn (show w < r + L by omega) (by omega) (by omega), hCLw]
    have hCLNc0 : CL (G2 M r L n) c0 = Le ++ [w] := by
      rw [C_cl_eq hM hS I hz h2 hlen hr hq hqr hn (show c0 < r + L by omega) (by omega) (by omega), hLe]
    have howN : σ.o w = psi (σ.v w) z z := by
      have := o_cl_eq hCN hGN hwN; rw [hCLNw] at this; exact this
    have howM : ρ.o w = psi (ρ.v w) z z := by
      have := o_cl_eq I.cons I.good hwM; rw [hCLw] at this; exact this
    obtain ⟨hsN, hpN⟩ := cl_vals hCN hGN hc0N
    obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hc0M
    have hoN := o_last_form hCN hc0N (hGN.ot_v c0 hc0N) hCLNc0
      (fun c hc => hsN _ (List.mem_map_of_mem hc)) hpN howN
    have hoM := o_last_form I.cons hc0M (I.good.ot_v c0 hc0M) hLe
      (fun c hc => hsM _ (List.mem_map_of_mem hc)) hpM howM
    rw [step_leaf] at hoN hoM
    rw [hoN] at hsy
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, rfl, -⟩ := hsy
    have hmap : Le.map σ.o = Le.map ρ.o := List.map_congr_left hLeo
    refine ⟨add (spArg (ρ.v c0) z (sumN (Le.map ρ.o))) (psi (ρ.v w) z z), by rw [hoM, hvc0], ?_⟩
    rw [hvc0, hmap]
    apply add_le_add_left
    have hvw := C2_vw_le hM hS I hz h2 hlen hr hq hqr hn hCN hwq hu
    rcases (le_iff _ _).mp hvw with h | h
    · exact psi_le_psi_of (Or.inl h)
    · rw [h]

#print axioms C2_len1

/-- The shape of `C2_len1`: `q − 1` is a leaf, the last counted child of `c₀`, upgraded to `q`. -/
def C2Len1 (M : Mat) (q c0 : Nat) : Prop :=
  ∃ w Le, w + 1 = q ∧ par M 0 w = some c0 ∧ children M w = [] ∧ upg M w = some q ∧ CL M c0 = Le ++ [w]

/-- `T2C2Kids4` off the shape `C2Len1`. -/
def T2C2Kids5 (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ n, 2 ≤ n → ∀ σ, Cons (G2 M r L n) σ → Good3 (G2 M r L n) σ →
    ∀ Lc0 c0, CL M r = Lc0 ++ [c0] → ¬ C2Len1 M q c0 → (∀ d ∈ Lc0, σ.o d = ρ.o d) ∧
      (CL M c0 ≠ [] → ∀ s y, σ.o c0 = psi s y z → y ≠ z → ∃ yM, ρ.o c0 = psi s yM z ∧ y ≤ yM)

theorem t2C2Kids4_of5 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (h : T2C2Kids5 M ρ r L q) : T2C2Kids4 M ρ r L q := by
  intro n hn σ hCN hGN Lc0 c0 hT
  by_cases hc : C2Len1 M q c0
  · obtain ⟨w, Le, hwq, hpw, hwleaf, hu, hLe⟩ := hc
    obtain ⟨h1, h2'⟩ := C2_len1 hM hS I hz h2 hlen hr hq hqr hT hwq hpw hwleaf hu hLe hn hCN hGN
    exact ⟨h1, fun _ => h2'⟩
  · exact h n hn σ hCN hGN Lc0 c0 hT hc

def C2Kids5 (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → T2C2Kids5 M ρ r L q

theorem c2Kids4_of5 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (h : C2Kids5 M ρ) : C2Kids4 M ρ := fun r L q k hlen hr hq hqr hncl hu =>
  t2C2Kids4_of5 hM hS I hz h2 hlen hr hq hqr (h r L q k hlen hr hq hqr hncl hu)

section
variable (hDI : HDropInputsV3) (hF : HFrameV3)
    (hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ))
    (hSeeds : T0AtV3 (fun M ρ r L => ∀ n, 2 ≤ n → ∀ σ,
      Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ))
    (hQR : HQRInputsStepV3) (hQN : HQNInputsV3)
    (hBXU2 : T2AtV3 (fun M ρ => T2BelowAtV3U2 M ρ))
    (hCanH2 : HCanonHard2)
    (hVF : T2AtV3 (fun M ρ => SeedVFResV3R3 M ρ))
    (hK5 : T2AtV3 (fun M ρ => C2Kids5 M ρ))
    (hC2R4 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → T2C2RootRel4 M ρ r L q))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M))
    (hQNd : T2AtV3 (fun M ρ => ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc))
    (hSC : T2AtV3 (fun M _ => T2VRASeedC M))
    (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc2 M))
    (hVD : T2AtV3 (fun M _ => T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M))
    (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M))

include hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2 hVF hK5 hC2R4 hFD hQNd hSC hCopy hVD hAG

/-- **Order preservation of the translation below SRO** from the current residuals (`C2Kids5`). -/
theorem translation_order_res8
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  translation_order_res7 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2 hVF
    (fun M ρ rk C hz h2 => c2Kids4_of5 C.std C.ne (coreW C.S C.I) hz h2 (hK5 M ρ rk C hz h2))
    hC2R4 hFD hQNd hSC hCopy hVD hAG hA hB hAS hBE hlt

/-- **Surjectivity of the translation below SRO** from the current residuals and `EvalFSNZ 2`. -/
theorem translation_surj_res8 (hFS : EvalFSNZ 2)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  translation_surj_res7 hDI hF hAbsU hSeeds hQR hQN hBXU2 hCanH2 hVF
    (fun M ρ rk C hz h2 => c2Kids4_of5 C.std C.ne (coreW C.S C.I) hz h2 (hK5 M ρ rk C hz h2))
    hC2R4 hFD hQNd hSC hCopy hVD hAG hFS hot hvN hlt

end

#print axioms translation_order_res8
#print axioms translation_surj_res8

end Ytosk.V3Main.SeedPF
