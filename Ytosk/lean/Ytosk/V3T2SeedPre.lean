/-
**3 行・t = 2: 種の列の枠の形 T2SeedPreShape を、qr・qn では証明し、sv・C は残りにする（2026-10-17、t2）。**

qr・qn では M[n] の r の数える子は M と同じ Lc に最後の 1 つを足したもので、Lc の o は M と同じ、v(r) も同じ
（`qr_frame_pre`・`qn_frame_pre`。qr_frame・qn_frame の前半で、M[n − 1] の Good3 は使わない）。
x より前で q でない子 c は Lc の中にあるので、M の枠がそのまま同じ値で書き換える。
-/
import Ytosk.V3T2SeedQR
import Ytosk.V3T2SeedQN
import Ytosk.V3T2VRAPre
import Ytosk.V3T2SeedWire

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

theorem qr_frame_pre {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
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

theorem qn_frame_pre {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q])
    {n : Nat} (hn : 2 ≤ n) {σ : Valn} {rkN : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = Lc ++ [q] ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧ σ.v r = ρ.v r := by
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
  exact ⟨hCLN, hLc, hvr⟩

/-- **A frame of `N` before its last counted child**, when `N` and `M` share the counted children `Lc₀` before
the last and their values: the same frame in `M`. -/
theorem frame_of_prefix {M N : Mat} {ρ σ : Valn} {i : Nat} {Lc0 : List Nat} {a b : Nat}
    (hclM : CL M i = Lc0 ++ [a]) (hclN : CL N i = Lc0 ++ [b]) (hv : σ.v i = ρ.v i)
    (hsame : ∀ d ∈ Lc0, σ.o d = ρ.o d) {Lc : List Nat} {c : Nat} {R : List Nat}
    (hCL : CL N i = Lc ++ c :: R) (hcb : c ≠ b) {s y : T} (hsy : σ.o c = psi s y z)
    (ht : lt (spArg (σ.v i) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v i) z z) (psi s y z) = true) :
    ∃ (Lc' R' : List Nat) (yM : T), CL M i = Lc' ++ c :: R' ∧ σ.v i = ρ.v i ∧ Lc'.map ρ.o = Lc.map σ.o ∧
      ρ.o c = psi s yM z ∧ y ≤ yM ∧
      (lt (spArg (ρ.v i) z (sumN (Lc'.map ρ.o))) yM = true ∧ lt (psi (ρ.v i) z z) (psi s yM z) = true) := by
  rw [hclN] at hCL
  have hR : R ≠ [] := by
    rintro rfl
    obtain ⟨_, h2⟩ := List.append_inj' hCL rfl
    simp only [List.cons.injEq, and_true] at h2
    exact hcb h2.symm
  have hdl : (Lc ++ c :: R).dropLast = Lc0 := by rw [← hCL]; simp
  rw [List.dropLast_append_of_ne_nil (by simp)] at hdl
  have hLs : ∀ d ∈ Lc, d ∈ Lc0 := fun d hd => by rw [← hdl]; exact List.mem_append_left _ hd
  have hcs : c ∈ Lc0 := by
    rw [← hdl]
    apply List.mem_append_right
    obtain ⟨r0, rs, rfl⟩ := List.exists_cons_of_ne_nil hR
    simp
  have hclM' : CL M i = Lc ++ c :: (R.dropLast ++ [a]) := by
    rw [hclM, ← hdl]
    obtain ⟨r0, rs, rfl⟩ := List.exists_cons_of_ne_nil hR
    simp
  have hLo : Lc.map ρ.o = Lc.map σ.o := List.map_congr_left (fun d hd => (hsame d (hLs d hd)).symm)
  have hoc : ρ.o c = psi s y z := by rw [← hsame c hcs]; exact hsy
  refine ⟨Lc, _, y, hclM', hv, hLo, hoc, le_refl _, ?_⟩
  rw [← hv, hLo]; exact ht

/-- **The residual of `T2SeedPreShape` in the sv and C cases.** -/
def T2SeedPreShapeSVC (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → (T2SVCase M r L ∨ T2CCase M r L) → ∀ n, 2 ≤ n →
    ∀ σ, Cons (G2 M r L n) σ → Good3 (G2 M r L n) σ →
    ∀ p, T2Seed M r L p → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL (G2 M r L n) p = Lc ++ c :: R →
      c < r + L → (∀ q, par M 0 (r + L) = some q → c ≠ q) → ∀ s y, σ.o c = psi s y z →
      (lt (spArg (σ.v p) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v p) z z) (psi s y z) = true) →
      ∃ (Lc' R' : List Nat) (yM : T), CL M p = Lc' ++ c :: R' ∧ σ.v p = ρ.v p ∧ Lc'.map ρ.o = Lc.map σ.o ∧
        ρ.o c = psi s yM z ∧ y ≤ yM ∧
        (lt (spArg (ρ.v p) z (sumN (Lc'.map ρ.o))) yM = true ∧ lt (psi (ρ.v p) z z) (psi s yM z) = true)

/-- **`T2SeedPreShape` from its sv・C part** (qr・qn are proved). -/
theorem t2SeedPreShape_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hSVC : T2SeedPreShapeSVC M ρ) : T2SeedPreShape M ρ := by
  intro r L hlen hr n hn σ hCN hGN p hp Lc c Rl hCL hcx hcq s y hsy ht
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hlen2 : 2 ≤ M.length := by have := par_lt M 2 _ _ hr; omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : expand M n = TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n := by
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  obtain ⟨rkN, hRN⟩ : ∃ rk', Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rk' := by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank n (by omega)
    rw [hexp] at h'; exact ⟨rk', h'⟩
  have hpr : p = r := by
    rcases hp with ⟨_, h⟩ | ⟨q, hq, hqr, hpq⟩
    · exact h
    · rw [par0_q_t2 hM hS I hlen hr hq hqr] at hpq; cases hpq; rfl
  rcases t2_seed_cases hlen hr with hc | hc | hc | hc
  · obtain ⟨hq, hXu⟩ := hc
    obtain ⟨_, h1lt⟩ := par2_facts I.z2 (by omega) hr
    have hxb : col M (r + L) ≠ bump M r := fun h => by
      have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
    obtain ⟨Lc0, hCLM⟩ := cl_r_split hlen hq hXu hxb
    obtain ⟨hCLN, hvr, hLc⟩ := qr_frame_pre hM hS I R hz h2 hlen hr hq hXu hCLM hn hCN hRN
    rw [hpr] at ht hCL ⊢
    exact frame_of_prefix hCLM hCLN hvr hLc hCL (by omega) hsy ht
  · obtain ⟨q, Lc0, hq, hqr, hCLM⟩ := hc
    obtain ⟨hCLN, hLc, hvr⟩ := qn_frame_pre hM hS I R hz h2 hlen hr hq hqr hCLM hn hCN hRN
    rw [hpr] at ht hCL ⊢
    exact frame_of_prefix hCLM hCLN hvr hLc hCL (hcq q hq) hsy ht
  · exact hSVC r L hlen hr (Or.inl hc) n hn σ hCN hGN p hp Lc c Rl hCL hcx hcq s y hsy ht
  · exact hSVC r L hlen hr (Or.inr hc) n hn σ hCN hGN p hp Lc c Rl hCL hcx hcq s y hsy ht

end Ytosk
