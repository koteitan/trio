/-
**t = 2・q ≠ r（q が r で数えられる）の種の列 r と q の枠の PH3cG・FC3（closure、2026-10-12）。**

N = M[n] で CL_N(r) = Lc ++ [q]、CL_N(q) = [x′]（t2 の `o_r_level_qn`）。
- q の枠は最初の枠だけ（状態 0）。FC3 は v_N(x′) = v_N(q) = V + ω^W（極限）から。
- r の q より前の枠は M の枠。q の枠は t2 の残り `T2SeedQNRes` から y = B + Ω_{f t}（pre 型）。
-/
import Ytosk.V3PSeedSVG
import Ytosk.V3T2SeedQNV

namespace Ytosk.G

open T

set_option linter.unusedSectionVars false

open Classical in
/-- **The data of the seed frames of `r` and `q` in `N = M[n]`** (`q ≠ r` counted at `r`). -/
theorem seed_frame_data_qn {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q])
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP) :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = Lc ++ [q] ∧
      CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) q = [r + L] ∧
      σ.v r = ρ.v r ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧
      σ.v (r + L) = add (ρ.v r) (last (σ.v q)) ∧
      σ.o q = psi (σ.v q) (step (σ.v q) (spArg (σ.v q) z (sumN ([] : List T))) (σ.v (r + L))
        (sh (ρP.v r) (σ.v (r + L)) (spArg (ρP.v r) z
          (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1))
            r).map ρP.o)))) z) z := by
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
  exact ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩

/-- **The residual for FC3 at the seed frame `(r, q)`** when `q` is the only counted child of `r`: the subscripts
`t_{k+1} = f(t_k)` keep `s′ = v_N(q)` as a prefix. 実測: 5 集合のうち deepA・d3s・deep3 の 6125 件で
X₁ = Ω_{s′}（t₁ = s′）、hi の先頭の添字はいつも s′ + X。 -/
def T2SeedQNFC (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop :=
  Lc = [] → ∀ τ, Cons (M.take (r + L)) τ → ∀ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) →
    ∀ k, ∃ X, X ≠ z ∧ tqN (ρ.v r) (qnS M ρ r L q) t1 (k + 1) = app (qnS M ρ r L q) X

theorem spArg_nil (a : T) : spArg a z (sumN ([] : List T)) = z := rfl

open Classical in
/-- **PH3cG and FC3 at the frames of the seeds `r` and `q` of `M[n]`** (`q ≠ r` counted at `r`), from PH3cG・FC3
of `M`, t2 の残り `T2SeedQNRes`, and `T2SeedQNFC`. -/
theorem seed_frames_qn {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) (hRes : T2SeedQNRes M ρ r L q Lc)
    (hFC : T2SeedQNFC M ρ r L q Lc)
    {τ0 : Valn} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : ∃ rk0, Rk (M.take (r + L)) rk0)
    (hP : PH3cG M ρ) (hF : FC3 M ρ) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ∀ i, (i = r ∨ i = q) → ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat),
        CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) i =
          Lc' ++ c :: R' →
        QPHs (σ.v i) (Lc'.map σ.o) (σ.o c) ∧ QF3s (σ.v i) (Lc'.map σ.o) (σ.o c) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set V := ρ.v r with hVdef
  set B := t2B V ρ Lc with hBdef
  set s' := qnS M ρ r L q with hs'def
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hpq : par M 0 q = some r := (mem_children_iff.mp (cl_mem_children hqcl)).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
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
  have hVot : isOT V = true := I.good.ot_v r hrM
  have hs'ot : isOT s' = true := qnS_ot I hrM L q
  have hVs' : V < s' := qnS_gt M ρ r L q
  have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
  have hv0 := v_take_of_untopped I hlen (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hC0
  obtain ⟨t1, ht1, hch⟩ := hRes.base τ0 hC0
  have hQM1 := clField_qT2P I.cons I.fo hP r hrM
  have hQM2 := clField_qT2F I.cons I.fo hF r hrM
  intro n hn hGlow σ hCN hGN i hi Lc' c R' hCL
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  have hvq : σ.v q = s' := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  -- the argument of `r` in `P = M[n − 1]` is `B + Ω_{t_{n−2}}`
  obtain ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩ : CL (TRIO.gexp M r L d0 d1 n) r = Lc ++ [q] ∧
      CL (TRIO.gexp M r L d0 d1 n) q = [r + L] ∧ σ.v r = V ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧
      σ.v (r + L) = s' ∧
      σ.o q = psi s' (step s' z s' (sh V s' (app B (psi (tqN V s' t1 (n - 2)) z z))) z) z := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn2 : n = 2 := by omega
      subst hn2
      have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hC0
      have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := hGlow 1 (le_refl 1) (by omega) τ0 hCP
      obtain ⟨rk0, hRk0⟩ := hR0
      have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hRk0
      obtain ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩ :=
        seed_frame_data_qn hM hS I R hz h2 hlen hr hq hqr hCLM (le_refl 2) hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hCLNq hoq
      rw [show (2 - 1 : Nat) = 1 from rfl, hP1, ht1, hv0] at hoq
      rw [hvq, qnS_vxs] at hvx
      rw [hvq, hvx, spArg_nil] at hoq
      exact ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      obtain ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩ :=
        seed_frame_data_qn hM hS I R hz h2 hlen hr hq hqr hCLM hn hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hCLNq hoq
      have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
      have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hqP : q < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hval := seed_r_value_qn hM hS I R hz h2 hlen hr hq hqr hCLM hRes hC0 hR0 hv0 ht1
        (fun k => ⟨(hch k).1, (hch k).2.1⟩) (n - 1) (by omega)
        (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP (hGP.ot_o q hqP) (cl_vals hCP hGP hrP).2
      have hform := o_cl_eq hCP hGP hrP
      rw [hval] at hform
      simp only [psi.injEq] at hform
      have h21 := hform.2.1
      rw [← hform.1] at h21
      rw [← hform.1, ← h21, show n - 1 - 1 = n - 2 by omega] at hoq
      rw [hvq, qnS_vxs] at hvx
      rw [hvq, hvx, spArg_nil] at hoq
      exact ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩
  -- the child of `r`'s last frame
  set t := tqN V s' t1 (n - 2) with htdef
  have hat : V < t := (hch (n - 2)).1
  have hts : ¬ shf V s' t < succ s' := (hch (n - 2)).2.1
  have hσB := hRes.σB
  have hBc := hRes.Bc
  have hhigh : ∀ g ∈ summands (app B (psi (shf V s' t) z z)), ¬ g < psi (succ s') z z := by
    intro g hg
    rw [summands_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hBc g hg
    · simp [summands] at hg; rw [hg]
      intro hlt
      rw [psi_lt_psi_z_iff] at hlt
      rcases hlt with h | ⟨_, h⟩
      · exact hts h
      · exact T.not_lt_z _ h
  have hinner : step s' z s' (sh V s' (app B (psi t z z))) z = app B (psi (shf V s' t) z z) := by
    rw [sh_app, hσB, sh_psi_gt hat, sh_z]
    have hne : app B (psi (shf V s' t) z z) ≠ z := by
      intro h; cases hB : B with
      | z => rw [hB] at h; simp at h
      | psi _ _ _ => rw [hB] at h; simp at h
    have hzlt : z < app B (psi (shf V s' t) z z) := by
      cases h : app B (psi (shf V s' t) z z) with
      | z => exact absurd h hne
      | psi _ _ _ => exact T.z_lt_psi _ _ _
    unfold step
    rw [if_pos ⟨hzlt, psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hzlt⟩)⟩]
    exact H_of_high hs'ot hhigh
  rw [hinner] at hoq
  rcases hi with hi | hi
  · -- the frames of `r`
    rw [hi] at hCL ⊢
    refine ⟨seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => (hQM1 Lc' c R' h).2) ?_ Lc' c R' hCL,
      seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => (hQM2 Lc' c R' h).2) ?_ Lc' c R' hCL⟩
    · rw [hoq]
      intro s y c0 hc _ _
      simp only [psi.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      rw [split_all_ge hhigh]
      refine Or.inr ⟨fun h => ?_, Or.inl ⟨_, by simp, rfl⟩⟩
      have := app_eq_self_iff h; simp at this
    · rw [hoq]
      intro s y c0 hc _ hL _
      simp only [psi.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      have hLc0 : Lc = [] := List.map_eq_nil_iff.mp hL
      obtain ⟨X, hX0, hXe⟩ := hFC hLc0 τ0 hC0 t1 ht1 (n - 2)
      refine ⟨fun h => absurd h (ne_of_gt hVs'), fun _ => ⟨X, hX0, ?_⟩⟩
      rw [split_all_ge hhigh, show B = z by rw [hBdef, hLc0]; rfl, app_z, lev_psi]
      exact hXe
  · -- the frame of `q`: only `x′`, the first frame
    rw [hi] at hCL ⊢
    rw [hCLNq] at hCL
    have hc : c = r + L ∧ Lc' = [] := by
      rcases Lc' with _ | ⟨a, l⟩
      · simp at hCL; exact ⟨hCL.1.symm, rfl⟩
      · simp at hCL
    obtain ⟨rfl, rfl⟩ := hc
    have hxN : r + L < (TRIO.gexp M r L d0 d1 n).length := by
      have := TRIO.gexp_length (d0 := d0) (d1 := d1) (n := n) hlen
      have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
      omega
    obtain ⟨y0, hy0⟩ := o_psi_sub hCN hxN
    rw [sf_ot (hGN.ot_v _ hxN), hvx] at hy0
    refine ⟨fun s y c0 _ _ hB => absurd (spArg_nil _) (by simpa using hB), fun s y c0 hc _ _ _ => ?_⟩
    rw [hy0] at hc
    simp only [psi.injEq] at hc
    obtain ⟨rfl, _, _⟩ := hc
    rw [hvq]
    refine ⟨fun _ => ⟨ne_of_gt (lt_of_le_of_lt (z_le V) hVs'), ?_⟩, fun h => absurd rfl h⟩
    -- `last s′ = ω^W ≠ 1`
    have hlW : ∀ u ∈ ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q),
        isOT u = true := by
      intro u hu; obtain ⟨d, _, rfl⟩ := List.mem_map.mp hu; exact isOT_bumpTerm I.good q d
    have hWne : sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q)) ≠ z := by
      intro h0
      have hle := le_foldl_sf (((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))
        one rfl hlW
      have : sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q)) =
          (((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q)).foldl
            (fun a b => sf (add a b)) one := rfl
      rw [← this, h0] at hle
      exact absurd hle (not_le_of_gt (T.z_lt_psi z z z))
    obtain ⟨s0, y0, hW⟩ := omega_psi_form (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
      (bumpTerm M ρ q)))
    have hne1 := omega_ne_one hWne
    rw [hW] at hne1
    rw [hs'def]; unfold qnS; rw [hW]
    obtain ⟨P0, hP0, _⟩ := add_eq_app_prefix (ρ.v r) (psi s0 y0 z)
    rw [hP0, last_app P0 (by simp)]
    exact hne1

end Ytosk.G
