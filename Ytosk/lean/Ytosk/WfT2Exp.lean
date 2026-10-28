/-
**3 行・t = 2・Bad2: 展開側の評価 `T2AbsNExp` を、使う側にある標準形の事実だけで証明する（2026-10-29、WfT2Exp）。**

形 L = 1・p = P0 r・i = P0 p（Bad2 で p は i の bump 子）で、N = M[n]（n ≥ 2）の評価 σ について
  B(v(r)) ≤ bumpW_N(i)、B(v) = ψ_v(Ω_{v+1})。

- 辞書式の順序だけの補題（標準形を仮定しない）: head(sf(acc + t)) ≥ head(sf t)、
  head S ≥ B(v) ⇒ ω^S ≥ B(v)。
- o_N(r) = ψ_V(step_V(0, V + 1, y)) で、引数は Ω_{V+1} 以上（V = v(r)、o_N(r + 1) = ψ_{V+1}(y)）。
- p の r 以外の子 c は o(r) に依存しない（ゲート: o(r) への依存は v(i) を通るので順位で矛盾）。
  よって σ.o c = ρ.o c は標準形、bump 項 ω^{Σ o(c)} は標準形。
- 使う側（T2BelowRV2）にある標準形の事実: σ.o r と r + 1 以降の列。これを仮定にした版 `T2AbsNExpOT` を証明し、
  `T2AbsNBad` の同じ仮定つきの版 `T2AbsNBadOT` を `T2AbsNSrc` だけから出す。
-/
import Ytosk.WfT2AbsSrc
import Ytosk.V3T2SeedQR
import Ytosk.V3ExpT2I
import Ytosk.V3T2BelowR

namespace Ytosk.WfT2Exp

open T WfT2Abs

set_option linter.unusedSectionVars false

/-! ## 辞書式の順序だけの補題 -/

theorem head_le_self : ∀ t : T, head t ≤ t
  | z => le_refl _
  | psi _ _ c => psi_le_psi_rest (z_le c)

theorem head_add_right : ∀ x y : T, head y ≤ head (add x y)
  | z, y => by simp
  | psi a b c, z => z_le _
  | psi a b c, psi d e f => by
    by_cases h : lt (psi a b z) (psi d e z) = true
    · simp only [add, h, if_true]; exact le_refl _
    · simp only [add, h]
      exact not_lt.mp h

theorem head_add_left : ∀ x y : T, head x ≤ head (add x y)
  | z, y => z_le _
  | psi a b c, z => le_refl _
  | psi a b c, psi d e f => by
    by_cases h : lt (psi a b z) (psi d e z) = true
    · simp only [add, h, if_true]; exact le_of_lt h
    · simp only [add, h]
      exact le_refl _

/-- **The head of `sf(acc + t)` is at least that of `sf t`** (no standard form needed). -/
theorem head_sf_add : ∀ acc t : T, head (sf t) ≤ head (sf (add acc t))
  | z, t => by simp
  | psi a b c, z => z_le _
  | psi a b c, psi d e f => by
    by_cases h : lt (psi a b z) (psi d e z) = true
    · simp only [add, h, if_true]; exact le_refl _
    · simp only [add, h]
      exact le_trans (head_sf_add c (psi d e f)) (head_add_right _ _)

theorem head_omega (x : T) : head (omega x) = omega x := by
  unfold omega
  split_ifs
  · rfl
  · cases x <;> rfl

theorem om_le_head {w x : T} (h : psi w z z ≤ x) : psi w z z ≤ head x := by
  cases x with
  | z => exact absurd h (not_le.mpr (T.z_lt_psi _ _ _))
  | psi a b c =>
    show psi w z z ≤ psi a b z
    rcases lt_or_eq_of_le h with h | h
    · rcases T.psi_lt_psi.mp h with h1 | ⟨h1, h2⟩ | ⟨h1, h2, _⟩
      · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h1))
      · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨h1, h2⟩))
      · subst h1; subst h2; exact le_refl _
    · cases h; exact le_refl _

theorem eps_le_bnd (v : T) : psi z (psi one z z) z ≤ Bnd v := by
  unfold Bnd
  cases v with
  | z => exact le_refl _
  | psi a b c => exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl (T.z_lt_psi _ _ _)))

theorem om_le_split {w b : T} (hb : psi w z z ≤ head b) : psi w z z ≤ head (split b (psi w z z)).1 := by
  cases b with
  | z => exact absurd hb (not_le.mpr (T.z_lt_psi _ _ _))
  | psi a b c =>
    have hn : ¬ lt (psi a b z) (psi w z z) = true := fun h' => absurd hb (not_le.mpr h')
    simp only [split, hn]
    exact hb

/-- **`B(v) ≤ head S ⇒ B(v) ≤ ω^S`** (no standard form needed). -/
theorem bnd_le_omega {v S : T} (h : Bnd v ≤ head S) : Bnd v ≤ omega S := by
  cases S with
  | z => exact absurd h (not_le.mpr (by unfold Bnd; exact T.z_lt_psi _ _ _))
  | psi s b c =>
    have hS : Bnd v ≤ psi s b c := le_trans h (head_le_self _)
    have hne : ¬ lt (psi s b c) (psi z (psi one z z) z) = true := fun h' =>
      absurd (lt_of_lt_of_le (show psi s b c < psi z (psi one z z) z from h')
        (le_trans (eps_le_bnd v) hS)) (lt_irrefl _)
    unfold omega
    rw [if_neg hne]
    simp only
    have h' : psi v (psi (add v one) z z) z ≤ psi s b z := h
    have key : v < s ∨ (v = s ∧ psi (add v one) z z ≤ head b) := by
      rcases lt_or_eq_of_le h' with hl | hl
      · rcases psi_lt_psi_z_iff.mp hl with h1 | ⟨h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, om_le_head (le_of_lt h2)⟩
      · simp only [psi.injEq] at hl
        exact Or.inr ⟨hl.1, om_le_head (le_of_eq hl.2.1)⟩
    show psi v (psi (add v one) z z) z ≤ _
    rcases key with h1 | ⟨rfl, hb⟩
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h1))
    · have hp := om_le_split hb
      have harg := le_trans hp (le_trans (head_add_left _ (sub (psi v b c)
        (psi v (split b (psi (add v one) z z)).1 z))) (head_le_self _))
      rcases lt_or_eq_of_le harg with h3 | h3
      · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h3⟩))
      · exact le_of_eq (congrArg (fun t => psi v t z) h3)

/-! ## ゲート: o(r) への依存 -/

theorem upg_not_last {M : Mat} {n k : Nat} (h : upg M n = some k) : n + 1 ≠ M.length := by
  unfold upg at h
  split at h
  · cases h
  · rename_i hc; exact fun e => hc (Or.inr (Or.inr e))

/-- **The gate** (`L = 1`, `p = P_0 r` the bump child of `i = P_0 p`): a dependency on `o(r)` in `M` is `r`, `x = r + 1`,
`o(p)`, or ranks at least `v(i)`. -/
theorem gate {M : Mat} {rk : Bool → Nat → Nat} (hR : Rk M rk) {r p i : Nat} (hlen : r + 2 = M.length)
    (hx : par M 0 (r + 1) = some r) (hpr : par M 0 r = some p) (hpi : par M 0 p = some i)
    (hbump : col M p = bump M i) (he2r : entry M 2 r = 0) (hBL : BumpLeaf M) :
    ∀ {b j}, DepS M (SR r) b j → j < M.length →
      j = r ∨ j = r + 1 ∨ (b = true ∧ j = p) ∨ rk false i ≤ rk b j := by
  intro b j h
  induction h with
  | seed hs => intro _; rcases hs with ⟨_, h⟩; exact Or.inl h
  | @ochild i0 c hc hcb hcu hD ih =>
    intro hi0
    have hcl := (mem_children_iff.mp hc).1
    have hpc := (mem_children_iff.mp hc).2
    rcases ih hcl with h | h | ⟨_, h⟩ | hrk
    · rw [h, hpr] at hpc; cases hpc; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · rw [h, hx] at hpc; cases hpc; exact Or.inl rfl
    · rw [h, hpi] at hpc; cases hpc; rw [h] at hcb; exact absurd hbump hcb
    · exact Or.inr (Or.inr (Or.inr (le_trans hrk (le_of_lt ((hR i0 hi0).2.1 c hc hcb hcu)))))
  | @ov i0 hD ih =>
    intro hi0
    rcases ih hi0 with h | h | ⟨h, _⟩ | hrk
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · cases h
    · exact Or.inr (Or.inr (Or.inr (le_trans hrk (le_of_lt (hR i0 hi0).1))))
  | @vpar i0 m h1 hm hD ih =>
    intro hi0
    have hmi := par_lt M 1 _ _ hm
    rcases ih (by omega) with h | h | ⟨h, _⟩ | hrk
    · exact Or.inr (Or.inl (by omega))
    · omega
    · cases h
    · exact Or.inr (Or.inr (Or.inr (le_trans hrk (le_of_lt (((hR i0 hi0).2.2 h1).1 m hm)))))
  | @vupg i0 k h1 h2 hk hD ih =>
    intro hi0
    obtain ⟨m, _, _, _, hcase⟩ := upg_spec hk
    have hnl := upg_not_last hk
    have hkl : k < M.length := by rcases hcase with h | ⟨_, h⟩ <;> omega
    rcases ih hkl with h | h | ⟨h, _⟩ | hrk
    · rw [h] at hD; exact absurd hD (not_depS_v_self hR (by omega))
    · rcases hcase with h' | ⟨_, h'⟩
      · exact Or.inl (by omega)
      · omega
    · cases h
    · exact Or.inr (Or.inr (Or.inr (le_trans hrk (le_of_lt (((hR i0 hi0).2.2 h1).2.1 h2 k hk)))))
  | @vbump i0 j k h1 h2 hj hjb hk hD ih =>
    intro hi0
    have hkl := (mem_children_iff.mp hk).1
    have hpk := (mem_children_iff.mp hk).2
    have hpj := (mem_children_iff.mp hj).2
    rcases ih hkl with h | h | ⟨_, h⟩ | hrk
    · rw [h, hpr] at hpk; cases hpk; rw [hpi] at hpj; cases hpj
      exact Or.inr (Or.inr (Or.inr (le_refl _)))
    · rw [h, hx] at hpk; cases hpk
      have := e2_of_col (show col M r = (entry M 0 i0 + 1, entry M 1 i0, 1) from hjb)
      omega
    · rw [h, hpi] at hpk; cases hpk
      have hpc : p ∈ children M i := mem_children_iff.mpr ⟨by
        have := par_lt M 0 _ _ hpr; omega, hpi⟩
      have he1 : entry M 1 i0 ≤ entry M 1 p := by
        rw [e1_of_col (show col M p = (entry M 0 i + 1, entry M 1 i, 1) from hbump),
          e1_of_col (show col M i = (entry M 0 i0 + 1, entry M 1 i0, 1) from hjb)]
      obtain ⟨_, hnil, _, _⟩ := hBL i0 i p hj hjb hpc he1
      have hrc : r ∈ children M p := mem_children_iff.mpr ⟨by omega, hpr⟩
      rw [hnil] at hrc; simp at hrc
    · exact Or.inr (Or.inr (Or.inr (le_trans hrk (le_of_lt
        (((hR i0 hi0).2.2 h1).2.2 h2 j hj hjb k hk)))))

/-! ## 展開側の評価 -/

theorem psi_le_psi_arg {a b b' : T} (h : b ≤ b') : psi a b z ≤ psi a b' z := by
  rcases lt_or_eq_of_le h with h | h
  · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h⟩))
  · rw [h]

/-- One step of `sp` from `0` is at least the summand. -/
theorem le_step_z {a s y : T} (hy : isOT (psi s y z) = true) : psi s y z ≤ step a z s y z := by
  unfold step
  split_ifs with h
  · have hyz : z < y := h.1
    have hHz : H s y ≠ z := fun e => by
      have := le_H hy; rw [e] at this
      exact absurd (lt_of_lt_of_le hyz this) (lt_irrefl _)
    exact le_trans (H_summands_ge hy _ (head_mem_summands hHz)) (head_le_self _)
  · simp

/-- **The new bump term of `i` in `M[n]` is at least `ψ_{v(r)}(Ω_{v(r)+1})`** (`L = 1`, `i = P_0(P_0 r)`), from the standard
forms of `o_N(r)` and of the columns after `r`. -/
theorem bnd_le_bumpW {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) (hB2 : Bad2 M)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r : Nat} (hlen : r + 2 = M.length) (hr : par M 2 (r + 1) = some r) {p i : Nat}
    (hp : par M 0 r = some p) (hpi : par M 0 p = some i) (h1i : entry M 1 i ≠ 0) (h2i : entry M 2 i ≠ 0)
    {n : Nat} (hn : 2 ≤ n) {σ : Valn}
    (hCN : Cons (TRIO.gexp M r 1 (entry M 0 (r + 1) - entry M 0 r) (entry M 1 (r + 1) - entry M 1 r) n) σ)
    (hOT : ∀ b j, r + 1 ≤ j → j < (TRIO.gexp M r 1 (entry M 0 (r + 1) - entry M 0 r)
      (entry M 1 (r + 1) - entry M 1 r) n).length → isOT (valB σ b j) = true)
    (hOr : isOT (σ.o r) = true) :
    Bnd (ρ.v r) ≤
      bumpW (TRIO.gexp M r 1 (entry M 0 (r + 1) - entry M 0 r) (entry M 1 (r + 1) - entry M 1 r) n) σ i := by
  have I := C.I
  obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
  obtain ⟨hSD, hZ1, hBE, hBL⟩ := hX.loc
  have hUM : UAT M := hX.toSInv.uat
  set d0 := entry M 0 (r + 1) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + 1) - entry M 1 r with hd1def
  set N := TRIO.gexp M r 1 d0 d1 n with hN
  have hlen' : r + 1 + 1 = M.length := by omega
  have hA : Anc0 M r (r + 1) := anc0_of_par M 2 r (r + 1) hr
  have hq : par M 0 (r + 1) = some r := by
    obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
    have hrq := (anc0_par hA (by omega) hq).le
    have := par_lt M 0 _ _ hq
    rw [show q = r by omega] at hq; exact hq
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + 1) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + 1) = entry M 1 r + d1 := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r 1 d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + 1 by omega]; exact hr)
    rw [h2, show M.length - 1 = r + 1 by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hlN : N.length = r + n * 1 := TRIO.gexp_length hlen'
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  obtain ⟨rkN, hRN⟩ := rk_expand_t2 hX hJ hz h2 I.rank n (by omega)
  rw [hexp n] at hRN
  have hxbr : col M (r + 1) ≠ bump M r := fun h => by
    have := e1_of_col (show col M (r + 1) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  have hXu : ∀ k, upg M k ≠ some (r + 1) := by
    intro k hk
    obtain ⟨m, _, _, _, hcase⟩ := upg_spec hk
    rcases hcase with h | ⟨_, h⟩
    · have hkr : k = r := by omega
      rw [hkr] at hk
      have := upg_lt_of_child hA hk; omega
    · have := upg_ge_len (M := M) (k := k) (by omega); rw [this] at hk; cases hk
  have hT : N.take (r + 1) = M.take (r + 1) := gexp_take_x hlen' (by omega)
  have hIU : ∀ c, c < r + 1 → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc htM
    apply isUpg_topped_take (by omega) (by omega) hT hUM hUN hc _ htM
    rw [topped_N2 (d1 := d1) hlen' (by omega) hq hd0e hn hXu hxbr he2r hc]
    exact htM
  have hxcN : Counted N r (r + 1) := by
    have hx2 := (entry_xprime (d1 := d1) hlen' (by omega) hq hd0e (by omega) hn).1
    rw [← hN] at hx2
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col _ (r + 1) = (_, _, 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  -- the values off the dependency on `o(r)` are those of `M`
  have hoff := t2_off hlen' (by omega) hq hd0e hn hXu hxbr hrb he2r hIU I.cons hCN hRN
  have hr1 : par M 1 (r + 1) = some r := par1_x_r (by omega) hX.z2 hZ1 hr
  have hvr : σ.v r = ρ.v r :=
    vr_N hlen' (by omega) hA hq hd0e hn hd1e he2r h1lt hrb hr1 hUM hUN I.cons hCN hRN
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  have hvx : σ.v (r + 1) = add (ρ.v r) one := by
    rcases vx_eq hlen' (by omega) hA hq hd0e hn hd1e he2r h1lt hrb hr1 (fun h => absurd rfl h) hBE hJ hX.r0p
      hUM hUN I.cons I.good hCN hRN with h | ⟨h, _⟩
    · exact h
    · exact absurd rfl h
  have hW : isOT (add (ρ.v r) one) = true := isOT_add hVot isOT_one
  -- `o_N(r + 1) = ψ_{V+1}(Y)`
  have hr1N : r + 1 < N.length := by rw [hlN]; omega
  have hor1 : σ.o (r + 1) = psi (add (ρ.v r) one) (spArg (sf (σ.v (r + 1))) z
      (sf (sumN ((children N (r + 1)).map (cnt N σ (r + 1)))))) z := by
    rw [(hCN (r + 1) hr1N).1]; unfold oRhs
    show add (sp _ z _) (sf z) = _
    rw [sp_eq_spArg, hvx, sf_ot hW]; rfl
  set Y := spArg (sf (σ.v (r + 1))) z (sf (sumN ((children N (r + 1)).map (cnt N σ (r + 1))))) with hY
  have hor1OT : isOT (psi (add (ρ.v r) one) Y z) = true := by
    rw [← hor1]; exact hOT true (r + 1) (le_refl _) hr1N
  -- `o_N(r) = ψ_V(step_V(0, V + 1, Y))`
  obtain ⟨Lc, hCLM⟩ := cl_r_split hlen' hq hXu hxbr
  have hLc : Lc = [] := by
    cases Lc with
    | nil => rfl
    | cons d Lc' =>
      exfalso
      have hsort := cl_sorted M r
      rw [hCLM] at hsort
      have hdx := (List.pairwise_append.mp hsort).2.2 d (by simp) (r + 1) (by simp)
      have hdCL : d ∈ CL M r := by rw [hCLM]; simp
      have := par_lt M 0 _ _ (mem_children_iff.mp (cl_mem_children hdCL)).2
      omega
  rw [hLc, List.nil_append] at hCLM
  have hCLN : CL N r = [r + 1] := by
    rw [CL_N2 hlen' (by omega) hq hd0e hn hXu hxbr he2r hIU hxcN (by omega), hCLM]
  have hrN : r < N.length := by rw [hlN]; omega
  have hor : σ.o r = psi (ρ.v r) (step (ρ.v r) z (add (ρ.v r) one) Y z) z := by
    have h := o_last_form (Lc := []) hCN hrN (by rw [hvr]; exact hVot) hCLN
      (by rw [hCLN]; intro c hc; simp at hc; rw [hc, hor1]; exact ⟨hor1OT, _, _, rfl⟩)
      (by rw [hCLN]; simp) hor1
    rw [h, hvr]; rfl
  have hBo : Bnd (ρ.v r) ≤ σ.o r := by
    rw [hor]; unfold Bnd
    exact psi_le_psi_arg (le_trans (psi_le_psi_arg (z_le Y)) (le_step_z hor1OT))
  -- `p` is the bump child of `i`
  have hbump : col M p = bump M i := by
    obtain ⟨_, p', g, hp', hg, hcol, _⟩ := hB2
    rw [show M.length - 2 = r by omega, hp] at hp'
    cases hp'
    rw [hpi] at hg; cases hg; exact hcol
  have hpr : p < r := par_lt M 0 _ _ hp
  have hip : i < p := par_lt M 0 _ _ hpi
  have hpc : p ∈ children M i := mem_children_iff.mpr ⟨by omega, hpi⟩
  have hrc : r ∈ children M p := mem_children_iff.mpr ⟨by omega, hp⟩
  -- the children of `p` and `i` end with `r` and `p`
  have hchp : children M p = (children M p).filter (fun d => decide (d < r)) ++ [r] :=
    split_last_max _ r (children_sorted M p) hrc
      (fun d hd => children_le_r (L := 1) hlen' (by omega) hA hpr hd)
  have hApr : Anc0 M p r := anc0_of_par M 0 p r hp
  have hchi : children M i = (children M i).filter (fun d => decide (d < p)) ++ [p] := by
    apply split_last_max _ p (children_sorted M i) hpc
    intro d hd
    have hdr := children_le_r (L := 1) hlen' (by omega) hA (by omega) hd
    by_contra hdp
    have hApd : Anc0 M p d := anc_between hApr d (by omega) hdr
    have := (anc0_par hApd (by omega) (mem_children_iff.mp hd).2).le
    omega
  have hchpN : children N p = children M p := children_gexp_lt_r hlen' (by omega) hA hd0e (by omega) hpr
  have hchiN : children N i = children M i := children_gexp_lt_r hlen' (by omega) hA hd0e (by omega) (by omega)
  -- the other children of `p` keep their values
  have hsib : ∀ c ∈ children M p, isOT (σ.o c) = true := by
    intro c hc
    by_cases hcr : c = r
    · rw [hcr]; exact hOr
    have hcr' : c < r := lt_of_le_of_ne (children_le_r (L := 1) hlen' (by omega) hA hpr hc) hcr
    have hpcl := par_lt M 0 _ _ (mem_children_iff.mp hc).2
    have hnD : ¬ DepS M (fun b i => b = true ∧ i = r) true c := by
      intro hD
      rcases gate I.rank hlen hq hp hpi hbump he2r hBL hD (by omega) with h | h | ⟨_, h⟩ | hrk
      · exact hcr h
      · omega
      · omega
      · have := ((I.rank i (by omega)).2.2 h1i).2.2 h2i p hpc hbump c hc
        omega
    rw [(hoff c (by omega)).1 hnD]
    exact I.good.ot_o c (by omega)
  -- the bump term of `p`
  have hbumpN : col N p = bump N i := by
    rw [col_gexp_pre hlen' (by omega) (by omega)]
    unfold bump
    rw [entry_gexp_pre hlen' (by omega) 0 (by omega), entry_gexp_pre hlen' (by omega) 1 (by omega)]
    exact hbump
  have hbt : bumpTerm N σ i p = omega (sumN ((children M p).map σ.o)) := by
    unfold bumpTerm; rw [if_pos hbumpN, hchpN]
  have hbtOT : isOT (bumpTerm N σ i p) = true := by
    rw [hbt]
    apply isOT_omega
    apply isOT_sumN
    intro t ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    exact hsib c hc
  have hbtB : Bnd (ρ.v r) ≤ bumpTerm N σ i p := by
    rw [hbt]
    apply bnd_le_omega
    rw [hchp, List.map_append, List.map_singleton, sumN_snoc]
    refine le_trans ?_ (head_sf_add _ _)
    rw [sf_ot hOr, show head (σ.o r) = σ.o r by rw [hor]; rfl]
    exact hBo
  -- the bump term of `i`
  unfold bumpW
  apply bnd_le_omega
  rw [hchiN, hchi, List.map_append, List.map_singleton, ← List.cons_append, sumN_snoc]
  refine le_trans ?_ (head_sf_add _ _)
  rw [sf_ot hbtOT, hbt, head_omega, ← hbt]
  exact hbtB

/-! ## 残りの形と橋 -/

/-- **`T2AbsNExp` with the standard forms that `T2BelowRV2` provides** (`o_N(r)` and the columns from `r + 1`).
Proved (`t2AbsNExpOT_holds`). -/
def T2AbsNExpOT : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r, r + 2 = M.length → par M 2 (r + 1) = some r → ∀ p i, par M 0 r = some p → par M 0 p = some i →
      entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      ∀ n, 2 ≤ n → ∀ σ,
        Cons (TRIO.gexp M r 1 (entry M 0 (r + 1) - entry M 0 r) (entry M 1 (r + 1) - entry M 1 r) n) σ →
        (∀ b j, r + 1 ≤ j → j < (TRIO.gexp M r 1 (entry M 0 (r + 1) - entry M 0 r)
          (entry M 1 (r + 1) - entry M 1 r) n).length → isOT (valB σ b j) = true) →
        isOT (σ.o r) = true →
        Bnd (ρ.v r) ≤
          bumpW (TRIO.gexp M r 1 (entry M 0 (r + 1) - entry M 0 r) (entry M 1 (r + 1) - entry M 1 r) n) σ i

theorem t2AbsNExpOT_holds : T2AbsNExpOT :=
  fun _ _ _ C hB2 hz h2 _ hlen hr _ _ hp hpi h1 h2' _ hn _ hCN hOT hOr =>
    bnd_le_bumpW C hB2 hz h2 hlen hr hp hpi h1 h2' hn hCN hOT hOr

/-- **`T2AbsNBad` with the standard-form premises of `T2BelowRV2`** (`o_N(r)` and the columns from `x`). -/
def T2AbsNBadOT : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ τ, Cons (M.take (r + L)) τ →
      ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      ¬ (∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z → ¬ s < bumpW (M.take (r + L)) τ i →
          s < bumpW M ρ i → Lhd z s (bumpW M ρ i)) →
      ∀ n, 2 ≤ n → ∀ σ,
        Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
        (∀ b j, r + L ≤ j → j < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
          (entry M 1 (r + L) - entry M 1 r) n).length → isOT (valB σ b j) = true) →
        isOT (σ.o r) = true →
        ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z →
          ¬ s < bumpW (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ i →
          s < bumpW M ρ i → Lhd z s (bumpW M ρ i)

/-- **Bridge**: `T2AbsNBadOT` from the M-side residual `T2AbsNSrc` alone (the expansion side is `bnd_le_bumpW`). -/
theorem t2AbsNBadOT_of (hS : T2AbsNSrc) : T2AbsNBadOT := by
  intro M ρ rk C hB2 hz h2 r L hlen hr τ hτ i hi h1 h2' hfail n hn σ hCN hOT hOr s hs hs2 hnN hlt
  obtain ⟨hL, ⟨p, hp, hpi⟩, hsrc⟩ := hS M ρ rk C hB2 hz h2 r L hlen hr τ hτ i hi h1 h2' hfail
  subst hL
  have hB := bnd_le_bumpW C hB2 hz h2 (by omega) hr hp hpi h1 h2' hn hCN hOT hOr
  by_contra hlhd
  exact hnN (lt_of_lt_of_le (hsrc s hs hs2 hlt hlhd) hB)

/-- **`AbsWN M M[n]` on `Bad2`** with `T2AbsNBadOT` (the standard forms of `T2BelowRV2`). -/
theorem t2_absWN_badOT (hAB : T2AbsNBadOT) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk)
    (hB2 : Bad2 M) (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) {r L : Nat}
    (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) (hm : T2BumpMono M r L) {n : Nat} (hn : 2 ≤ n)
    {σ : Valn}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hOT : ∀ b j, r + L ≤ j → j < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n).length → isOT (valB σ b j) = true)
    (hOr : isOT (σ.o r) = true) :
    AbsWN M (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n)
      (r + L) ρ σ := by
  have I := C.I
  have hcnt := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  intro i hi h1 h2' s hs hs2 hnN hlt
  by_cases hT : ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z →
      ¬ s < bumpW (M.take (r + L)) (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rk)) i →
      s < bumpW M ρ i → Lhd z s (bumpW M ρ i)
  · exact hT s hs hs2 (fun h => hnN (lt_of_lt_of_le h (hm _ hC0 n hn σ hCN i hi h1 h2'))) hlt
  · exact hAB M ρ rk C hB2 hz h2 r L hlen hr _ hC0 i hi h1 h2' hT n hn σ hCN hOT hOr s hs hs2 hnN hlt

/-- **`T2BelowRV2` with the M-side residual `T2AbsNSrc` in place of `T2AbsNBad`** (splice for the top: replace
`t2BelowRV2_of hP hCl hBM hAB` by `t2BelowRV2_of_src hP hCl hBM hS`). -/
theorem t2BelowRV2_of_src (hP : T2SeedPResV2) (hCl : T2SeedClV2) (hBM : T2BumpMonoV2) (hS : T2AbsNSrc) :
    T2BelowRV2 := by
  intro M ρ rk C hz h2 r L hlen hr n hn hG σ hCN hOTj hor hoq hdec
  have IW := Inv3W.ofV2 C.S C.I
  have RW : Res3W M ρ rk := C.toW
  have hPR := hP M ρ rk C hz h2
  obtain ⟨hQN, hSV, hCC⟩ := hCl M ρ rk C hz h2 r L hlen hr
  refine ⟨fun p hp => ?_, ?_⟩
  swap
  · by_cases hB2 : Bad2 M
    · exact t2_absWN_badOT (t2AbsNBadOT_of hS) C hB2 hz h2 hlen hr (hBM M ρ rk C hz h2 r L hlen hr) hn hCN
        hOTj hor
    · exact t2_absWN C.std C.ne IW RW hB2 hlen hr (hBM M ρ rk C hz h2 r L hlen hr) hn hCN
  have hpr : p = r := by
    rcases hp with ⟨_, h⟩ | ⟨q, hq, hqr, hpq⟩
    · exact h
    · rw [par0_q_t2 C.std C.ne IW hlen hr hq hqr] at hpq; cases hpq; rfl
  rw [hpr]
  rcases t2_seed_cases hlen hr with hc | hc | hc | hc
  · obtain ⟨hq, hXu⟩ := hc
    obtain ⟨_, h1lt⟩ := par2_facts IW.z2 (by omega) hr
    have hxb : col M (r + L) ≠ bump M r := fun h => by
      have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
    obtain ⟨Lc, hCLM⟩ := cl_r_split hlen hq hXu hxb
    exact seedRR_qr C.std C.ne IW RW hz h2 hlen hr hq hXu hCLM (hPR.qr r L hlen hr hq hXu Lc hCLM)
      n hn hG σ hCN hor
  · obtain ⟨q, Lc, hq, hqr, hCLM⟩ := hc
    exact seedRR_qn C.std C.ne IW RW hz h2 hlen hr hq hqr hCLM (hPR.qn r L q hlen hr hq hqr Lc hCLM)
      (hQN q Lc hq hqr hCLM) n hn hG σ hCN (hoq q hq hqr) hdec hor
  · obtain ⟨hq, hux⟩ := hc
    exact seedRR_sv C.std C.ne IW RW hz h2 hlen hr hq hux (hPR.sv r L hlen hr hq hux) (hSV ⟨hq, hux⟩)
      n hn hG σ hCN hdec hor
  · obtain ⟨q, hq, hqr, hncl⟩ := hc
    exact seedRR_C C.std C.ne IW RW hz h2 hlen hr hq hqr hncl (hPR.C r L q hlen hr hq hqr hncl).1
      (hCC q hq hqr hncl) n hn hG σ hCN (hoq q hq hqr) hdec hor

end Ytosk.WfT2Exp
