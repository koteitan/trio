/- QFO-only seed frames. The old Res3W bundle and the sequence residuals
are not required. C's upgrade condition is kept explicitly. -/
import Ytosk.V3TranslationAllUV3
import Ytosk.V3T2SeedFr2
import Ytosk.V3T2CVq

namespace Ytosk.V3Main.SeedFO
open T Classical WfExQ1 WfExQ2 G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem data_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L])
    {n : Nat} (hn : 2 ≤ n) {σ : Valn} {rkN : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    
    
     :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = Lc ++ [r + L] ∧ σ.v r = ρ.v r ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hrx : r < r + L := par_lt M 0 _ _ hq
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
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hxbr : col M (r + L) ≠ bump M r := fun h => by
    have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hIU : ∀ c, c < r + L → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_N2 (d1 := d1) hlen hL0 hq hd0e hn hXu hxbr he2r hc]
    exact htM
  have hxcN : Counted N r (r + L) := by
    have hx2 := (entry_xprime (d1 := d1) hlen hL0 hq hd0e (by omega) hn).1
    rw [← hN] at hx2
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col _ (r + L) = (_, _, 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hCLN : CL N r = Lc ++ [r + L] := by
    rw [CL_N2 hlen hL0 hq hd0e hn hXu hxbr he2r hIU hxcN hrx, hCLM]
  -- `D = DepS M {o(r)}` misses the counted children of `r` and `v(r)`
  have hoff := t2_off hlen hL0 hq hd0e hn hXu hxbr hrb he2r hIU I.cons hCN hRN
  have hnoD : ∀ b i, DepS M (fun b i => b = true ∧ i = r) b i → i < M.length → rk true r ≤ rk b i := by
    intro b i hD hi
    obtain ⟨b', i', ⟨rfl, rfl⟩, hle⟩ := depS_rk_ex I.rank hD hi
    exact hle
  have hrM : r < M.length := by omega
  have hvr : σ.v r = ρ.v r := (hoff r hrx).2 (fun hD => by
    have h1 := hnoD false r hD hrM
    have h2' := (I.rank r hrM).1
    omega)
  have hLc : ∀ d ∈ Lc, d < r + L ∧ σ.o d = ρ.o d := by
    intro d hd
    have hdCL : d ∈ CL M r := by rw [hCLM]; simp [hd]
    have hdc := cl_mem_children hdCL
    have hcnt : Counted M r d := by simpa using (List.mem_filter.mp hdCL).2
    have hdx : d < r + L := by
      have hsort := cl_sorted M r
      rw [hCLM] at hsort
      exact (List.pairwise_append.mp hsort).2.2 d hd (r + L) (by simp)
    refine ⟨hdx, (hoff d hdx).1 (fun hD => ?_)⟩
    have h1 := hnoD true d hD (by omega)
    have h2' := (I.rank r hrM).2.1 d hdc hcnt.1 hcnt.2
    omega
  exact ⟨hCLN, hvr, fun d hd => (hLc d hd).2⟩

theorem data_qn {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q])
    {n : Nat} (hn : 2 ≤ n) {σ : Valn} {rkN : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    
    
     :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = Lc ++ [q] ∧ CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) q = [r + L] ∧ σ.v r = ρ.v r ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hqc := cl_mem_children hqcl
  have hpq : par M 0 q = some r := (mem_children_iff.mp hqc).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  obtain ⟨qp, rfl⟩ : ∃ qp, q = r + qp := ⟨q - r, by omega⟩
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hqcnt : Counted M r (r + qp) := by simpa using (List.mem_filter.mp hqcl).2
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
    refine ⟨by rw [hcolN _ hqx, hbN r (by omega)]; exact hqcnt.1, fun ⟨_, ht⟩ => ?_⟩
    unfold topped at ht
    rw [hchN _ hqx, hsplitq] at ht
    simp at ht
    exact hxcnt.1 ht
  have hCLN : CL N r = Lc ++ [r + qp] := by
    rw [← hCLM]; unfold CL
    rw [hchN r (by omega)]
    apply List.filter_congr
    intro c hc
    by_cases hcq : c = r + qp
    · rw [hcq]; simp [hqcntN, hqcnt]
    · have hcx : c < r + L := by
        have hcl := (mem_children hc).2
        by_contra h'
        have hcx' : c = r + L := by omega
        rw [hcx'] at hc
        have := (mem_children_iff.mp hc).2; rw [hq] at this
        have := Option.some.inj this; omega
      simp only [decide_eq_decide]
      exact hcntN r c (by omega) hcx hcq
  -- `N` agrees with `M` outside `D = DepS M {v(q), o(r)}`
  have hnu : upg M (r + L - 1) ≠ some (r + L) := fun h =>
    upg_not_x hlen hA hq Txb I.be h (le_refl _) (by omega)
  have hupgN : ∀ i, i < r + L → upg N i = upg M i := fun i hi =>
    upg_NQ hlen hL0 hA hq hqp hd0e hn he2r hnu hi
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hq] at h'; exact (Option.some.inj h').symm
  have hbjN : ∀ i j, i < r + L → j ∈ children N i → r + L ≤ j → col N j ≠ bump N i := by
    intro i j hi hj hjx hb
    have hjl := (mem_children hj).2
    rw [hlN] at hjl
    rcases par0_tail2Q hlen hL0 hA hq hqp hd0e (by omega) hjx hjl with ⟨hjx', _⟩ | ⟨p', hp', hp'1, _⟩
    · rw [hjx'] at hb
      have := e2_of_col (show col N (r + L) = (entry N 0 i + 1, entry N 1 i, 1) from hb)
      omega
    · rw [(mem_children_iff.mp hj).2] at hp'; cases hp'; omega
  have hoff := t2_off_gen (S := SQ (r + qp) r) (bnd := r + L) I.cons hCN hRN (by omega) (by rw [hlN]; omega)
    (fun i hi _ => hchN i hi) (DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (Or.inr (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i hqi hb => by have h' := (mem_children_iff.mp hqi).2; rw [hpq] at h'; cases h'; exact Tqb hb)
    (fun y i hi => entry_gexp_pre hlen (by omega) y hi) (fun i hi => par_gexp_pre hlen (by omega) 1 hi)
    (fun i hi _ => hupgN i hi)
    (fun i c hi hd hc hcx => hcntN i c hi hcx (by
      intro hcq; apply hd; apply DepS.seed; right; refine ⟨rfl, ?_⟩
      have h' := (mem_children_iff.mp hc).2; rw [hcq, hpq] at h'; exact (Option.some.inj h').symm))
    (fun i c hi hc hcx => by
      obtain ⟨_, rfl⟩ := hxc i c hc hcx
      exact DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i k hi hk hkx => (upg_not_x hlen hA hq Txb I.be hk hkx hi).elim)
    hbjN
    (fun i j hi hj hjx _ => by
      obtain ⟨_, rfl⟩ := hxc i j hj hjx
      exact DepS.seed (Or.inl ⟨rfl, rfl⟩))
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc j k hk hkx
      have h' := (mem_children_iff.mp hj).2; rw [hpq] at h'; cases h'
      exact absurd hjb Tqb)
  have htq : topped M (r + qp) = true := by
    unfold topped; rw [hsplitq]; simp [Txb]
  have hinv : ∀ {b i}, DepS M (SQ (r + qp) r) b i → i < M.length → Anc0 M (r + qp) i ∨ rk true r ≤ rk b i :=
    fun h hi => depS_SQ_inv I.rank hpq Tqb hqcnt.2 htq he2r h hi
  have hvr : σ.v r = ρ.v r := (hoff r (by omega)).2 (fun hD => by
    rcases hinv hD hrM with hAq | hle
    · have := hAq.le; omega
    · have := (I.rank r hrM).1; omega)
  have hLc : ∀ d ∈ Lc, σ.o d = ρ.o d := by
    intro d hd
    have hdCL : d ∈ CL M r := by rw [hCLM]; simp [hd]
    have hdc := cl_mem_children hdCL
    have hcnt : Counted M r d := by simpa using (List.mem_filter.mp hdCL).2
    have hdq : d < r + qp := by
      have hsort := cl_sorted M r
      rw [hCLM] at hsort
      exact (List.pairwise_append.mp hsort).2.2 d hd (r + qp) (by simp)
    refine (hoff d (by omega)).1 (fun hD => ?_)
    rcases hinv hD (by omega) with hAq | hle
    · have := hAq.le; omega
    · have := (I.rank r hrM).2.1 d hdc hcnt.1 hcnt.2; omega
  exact ⟨hCLN, hCLNq, hvr, hLc⟩

theorem data_sv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (htP : topped (M.take (r + L)) r = false)
    {n : Nat} (hn : 2 ≤ n) {σ : Valn} {rkN : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    
    
    
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hG0 : Good3 (M.take (r + L)) τ0)
    (hR0 : Rk (M.take (r + L)) rk0) :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = CL (M.take (r + L)) r ++ [r + L] ∧ σ.v r = τ0.v r ∧ (∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨hcntN, hcntP⟩ := sv_cnt hM hS I hz h2 hlen hr hq hux htP hn
  have hag := sv_agree hM hS I hz h2 hlen hr hq hux htP hn hCN hC0 hR0
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hrx : r < r + L := par_lt M 0 _ _ hq
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
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hrM : r < M.length := by omega
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hrT : r < (M.take (r + L)).length := by omega
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  -- the counted children of `r` in `N`
  have hxcN : Counted N r (r + L) := by
    have hx2 := (entry_xprime (d1 := d1) hlen hL0 hq hd0e (by omega) hn).1
    rw [← hN] at hx2
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col _ (r + L) = (_, _, 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hxrc : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have hCLN : CL N r = CL (M.take (r + L)) r ++ [r + L] := by
    unfold CL
    rw [children_N2 hlen hL0 hq hd0e (by omega) hn hrx, children_take]
    conv_lhs => rw [children_split_x hlen hxrc, List.filter_append]
    rw [show List.filter (fun c => decide (Counted N r c)) [r + L] = [r + L] by simp [hxcN]]
    congr 1
    apply List.filter_congr
    intro c hc
    have hcx : c < r + L := by simpa using (List.mem_filter.mp hc).2
    simp only [decide_eq_decide]
    exact (hcntN r c hrx hcx).trans (hcntP r c hrx hcx).symm
  -- the values of the earlier children are those of `M.take x`
  have hval : ∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d := by
    intro d hd
    have hdc := cl_mem_children hd
    have hcnt : Counted (M.take (r + L)) r d := by simpa using (List.mem_filter.mp hd).2
    exact ((hag d (by have := (mem_children hdc).2; omega)).1
      ((hR0 r hrT).2.1 d hdc hcnt.1 hcnt.2)).symm
  have hvr : σ.v r = τ0.v r := ((hag r hrx).2 (hR0 r hrT).1).symm
  exact ⟨hCLN, hvr, hval⟩

theorem data_C {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    (hqP : ¬ Counted (M.take (r + L)) r q) (hun : upg M (r + L - 1) = none)
    {n : Nat} (hn : 2 ≤ n) {σ : Valn} {rkN : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    
    
    
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hG0 : Good3 (M.take (r + L)) τ0)
    (hR0 : Rk (M.take (r + L)) rk0) (hv0 : τ0.v r = ρ.v r) (hvq0 : τ0.v q = σ.v q) :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = CL (M.take (r + L)) r ++ [q] ∧ (∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d) ∧ σ.v r = ρ.v r ∧ CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) q = [r + L] := by
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
  exact ⟨hCLN, hval, hvr, hCLNq⟩

/-- Only the two C fields read by the QFO frame data. -/
structure T2SeedCUnVq (M : Mat) (ρ : Valn) (r L q : Nat) : Prop where
  un : upg M (r + L - 1) = none
  vqP : ∀ τ, Cons (M.take (r + L)) τ → τ.v q = qnS M ρ r L q

section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
  (C : StepCtx3 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
  (h2 : TRIO.srow M (M.length - 1) = 2)
include C hz h2

 theorem rank_gexp {r L n : Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hn : 1 ≤ n) :
    ∃ rkN, Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n) rkN := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
  have hrx := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have he := expand_eq_gexp M n hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
  rw [h2, show M.length - 1 = r + L by omega] at he
  simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true, Nat.add_sub_cancel_left] at he
  obtain ⟨rkN, hRN⟩ := rk_expand_t2 hX hJ hz h2 C.I.rank n hn
  rw [he] at hRN
  exact ⟨rkN, hRN⟩

 theorem prefix_ctx {r L : Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) {τ : Valn} (hτ : Cons (M.take (r + L)) τ) :
    Rk (M.take (r + L)) rk ∧ Good3 (M.take (r + L)) τ ∧ FrameOT (M.take (r + L)) τ := by
  have := par_lt M 2 _ r hr
  have J := C.pre (r + L) (by omega) (by omega)
  have hA := agree_of_cons J.cons hτ J.rank
  exact ⟨J.rank, good3_congr J.good hA, clField_congr (Q := QFO) J.fo hA⟩

 theorem seedFO_qr {r L : Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some r)
    (hXu : ∀ i, upg M i ≠ some (r + L)) {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) :
    SeedFr QFO M r L r := by
  have I := coreW C.S C.I
  have hrx := par_lt M 2 _ r hr
  have hrM : r < M.length := by omega
  intro n hn hGlow σ hCN hGN
  obtain ⟨rkN, hRN⟩ := rank_gexp C hz h2 hlen hr (show 1 ≤ n by omega)
  obtain ⟨hCLN, hvr, hLc⟩ := data_qr C.std C.ne I hz h2 hlen hr hq hXu hCLM hn hCN hRN
  exact seed_frames_lift hCLM hCLN hvr hLc
    (fun Lc' c R' h => I.fo r hrM Lc' c R' h) (I.fo r hrM Lc (r + L) [] hCLM)

 theorem seedFO_qn {r L q : Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) :
    ∀ i, i = r ∨ i = q → SeedFr QFO M r L i := by
  have I := coreW C.S C.I
  have hrx := par_lt M 2 _ r hr
  have hrM : r < M.length := by omega
  intro i hi n hn hGlow σ hCN hGN
  obtain ⟨rkN, hRN⟩ := rank_gexp C hz h2 hlen hr (show 1 ≤ n by omega)
  obtain ⟨hCLN, hCLNq, hvr, hLc⟩ := data_qn C.std C.ne I hz h2 hlen hr hq hqr hCLM hn hCN hRN
  rcases hi with hi | hi <;> subst i
  · exact seed_frames_lift hCLM hCLN hvr hLc
      (fun Lc' c R' h => I.fo r hrM Lc' c R' h) (I.fo r hrM Lc q [] hCLM)
  · intro Lc' c R' hCL
    have hqcN := mem_children (cl_mem_children (show c ∈ CL _ q by rw [hCL]; simp))
    have hqN := hqcN.1.trans hqcN.2
    have hLc0 : Lc' = [] := by
      rw [hCLNq] at hCL
      cases Lc' with
      | nil => rfl
      | cons d ds => simp at hCL
    subst hLc0
    show isOT (psi (σ.v q) z z) = true
    exact isOT_psi_zz (hGN.ot_v q hqN)

 theorem seedFO_sv {r L : Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some r)
    (hux : upg M (r + L - 1) = some (r + L)) : SeedFr QFO M r L r := by
  have I := coreW C.S C.I
  have hrx := par_lt M 2 _ r hr
  have J := C.pre (r + L) (by omega) (by omega)
  intro n hn hGlow σ hCN hGN
  obtain ⟨rkN, hRN⟩ := rank_gexp C hz h2 hlen hr (show 1 ≤ n by omega)
  obtain ⟨hCLN, hvr, hval⟩ := data_sv C.std C.ne I hz h2 hlen hr hq hux
    (topP_sv hlen I.z2 I.z1 hr hq hux) hn hCN hRN J.cons J.good J.rank
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  refine seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr hval
    (fun Lc' c R' h => J.fo r hrT Lc' c R' h) ?_
  show isOT (psi ((drop1 M (r + L) rk).v r)
    (spArg ((drop1 M (r + L) rk).v r) z
      (sumN ((CL (M.take (r + L)) r).map (drop1 M (r + L) rk).o))) z) = true
  rw [← o_cl_eq J.cons J.good hrT]
  exact J.good.ot_o r hrT

 theorem cUnVq_of_un {r L q : Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    (hun : upg M (r + L - 1) = none) : T2SeedCUnVq M ρ r L q :=
  ⟨hun, c_vqP_of_un C.std C.ne (coreW C.S C.I) hlen hr hq hqr hun⟩

 theorem seedFO_C {r L q : Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q]) (hCres : T2SeedCUnVq M ρ r L q) :
    ∀ i, i = r ∨ i = q → SeedFr QFO M r L i := by
  have I := coreW C.S C.I
  have hrx := par_lt M 2 _ r hr
  have J := C.pre (r + L) (by omega) (by omega)
  have hv0 := v_take_of_untopped I hlen hrx (topP_C C.std C.ne I hlen hr hq hqr) J.cons
  intro i hi n hn hGlow σ hCN hGN
  obtain ⟨rkN, hRN⟩ := rank_gexp C hz h2 hlen hr (show 1 ≤ n by omega)
  have hvq := vq_eq_gexp C.std C.ne I hz h2 hlen hr hn hCN hq hqr
  have hvq0 : (drop1 M (r + L) rk).v q = σ.v q := by
    rw [hvq]; exact hCres.vqP _ J.cons
  obtain ⟨hCLN, hval, hvr, hCLNq⟩ := data_C C.std C.ne I hz h2 hlen hr hq hqr
    (qP_C C.std C.ne I hlen hr hq hqr hncl hCres.un) hCres.un hn hCN hRN
    J.cons J.good J.rank hv0 hvq0
  rcases hi with hi | hi <;> subst i
  · have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
    have hvr' : σ.v r = (drop1 M (r + L) rk).v r := hvr.trans hv0.symm
    refine seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr' hval
      (fun Lc' c R' h => J.fo r hrT Lc' c R' h) ?_
    show isOT (psi ((drop1 M (r + L) rk).v r)
      (spArg ((drop1 M (r + L) rk).v r) z
        (sumN ((CL (M.take (r + L)) r).map (drop1 M (r + L) rk).o))) z) = true
    rw [← o_cl_eq J.cons J.good hrT]
    exact J.good.ot_o r hrT
  · intro Lc' c R' hCL
    have hqcN := mem_children (cl_mem_children (show c ∈ CL _ q by rw [hCL]; simp))
    have hqN := hqcN.1.trans hqcN.2
    have hLc0 : Lc' = [] := by
      rw [hCLNq] at hCL
      cases Lc' with
      | nil => rfl
      | cons d ds => simp at hCL
    subst hLc0
    show isOT (psi (σ.v q) z z) = true
    exact isOT_psi_zz (hGN.ot_v q hqN)

end

/-- Global assembly with only the C fields, restricted to actual C frames. -/
theorem hFO_of (hC : T2AtV3 (fun M ρ => ∀ r L q, r + L + 1 = M.length →
    par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCUnVq M ρ r L q)) :
    T2AtV3 (fun M _ => T2SeedFrames QFO M) := by
  intro M ρ rk C hz h2
  refine t2_seed_frames_of (Q := QFO) C.std C.ne (coreW C.S C.I) ?_ ?_ ?_ ?_
  · intro r L hlen hr hq hXu Lc hCL
    exact seedFO_qr C hz h2 hlen hr hq hXu hCL
  · intro r L hlen hr hq hux
    exact seedFO_sv C hz h2 hlen hr hq hux
  · intro r L q hlen hr hq hqr Lc hCL
    exact seedFO_qn C hz h2 hlen hr hq hqr hCL
  · intro r L q hlen hr hq hqr hncl
    exact seedFO_C C hz h2 hlen hr hq hqr hncl (hC M ρ rk C hz h2 r L q hlen hr hq hqr hncl)

/-- The second C field follows from the first, so only the upgrade condition remains. -/
theorem hFO_of_un (hC : T2AtV3 (fun M _ => ∀ r L q, r + L + 1 = M.length →
    par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none)) :
    T2AtV3 (fun M _ => T2SeedFrames QFO M) := by
  refine hFO_of ?_
  intro M ρ rk C hz h2 r L q hlen hr hq hqr hncl
  exact cUnVq_of_un C hz h2 hlen hr hq hqr (hC M ρ rk C hz h2 r L q hlen hr hq hqr hncl)

end Ytosk.V3Main.SeedFO
