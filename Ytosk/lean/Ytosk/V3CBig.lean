/-
**t = 2・C の残り `T2SeedCBig` を構造の残り `T2SeedCNext` に帰着（closure、2026-10-12）。**

`T2SeedCBig`: M.take x で r の q より前の数えない子 d は v(d) > s′。
- 数えない子 d（上げの的で topped）の次の兄弟 dn が dn − 1 から上げられるなら v(dn) < v(d)（`upg_next_lt`）:
  dn − 1 は d の部分木の最後の列で P_1 = r・行 1 = e1 r + 1・行 2 = 0。d の最後の子 jl は bump 子（topped）、
  jl の最後の子 kl は行 1 = e1 r + 1 なので BumpLeaf で葉、kl = dn − 1。o(kl) = Ω_{v(dn)}（上げで v(kl) = v(dn)）
  なので v(d) ≥ ω^{W_d} ≥ Ω_{v(dn)} > v(dn)。
- dn = q や dn が数えない子なら dn は dn − 1 から上げられる（上げの的で topped、UAT）。dn が数える子のときだけ
  名前つきの構造の残り `T2SeedCNext`。
- 兄弟を右から帰納: q は v = s′（vqP）、数える子は decP と o の減少で v > s′。
-/
import Ytosk.V3CFix
import Ytosk.V3InvW

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The next sibling is below**: an uncounted (topped) child `d` of `r` whose next sibling `dn` is upgraded from
`dn − 1` has `v(dn) < v(d)`. -/
theorem upg_next_lt {N : Mat} {τ : Valn} (hX : SInvX N) (hC : Cons N τ) (hG : Good3 N τ) {r d dn : Nat}
    (hd : d ∈ children N r) (hdn : dn ∈ children N r) (hddn : d < dn)
    (hcons : ∀ e ∈ children N r, d < e → dn ≤ e)
    (he1d : entry N 1 d = entry N 1 r + 1) (he2d : entry N 2 d = 1) (hP1d : par N 1 d = some r)
    (he2dn : entry N 2 dn = 1) (hP1dn : par N 1 dn = some r)
    (htop : topped N d = true) (hu : upg N (dn - 1) = some dn) : τ.v dn < τ.v d := by
  have hpd : par N 0 d = some r := (mem_children_iff.mp hd).2
  have hpdn : par N 0 dn = some r := (mem_children_iff.mp hdn).2
  have hdnL : dn < N.length := (mem_children hdn).2
  have hdL : d < N.length := (mem_children hd).2
  have hrd := par_lt N 0 d r hpd
  -- `dn − 1`
  obtain ⟨m, hm1, hm0, he1eq, _⟩ := upg_facts hu
  rw [hpdn] at hm0; cases hm0
  obtain ⟨he1e, he2e⟩ := upg_e12 hu
  have he2e0 : entry N 2 (dn - 1) = 0 := by have := hX.z2 (dn - 1); omega
  obtain ⟨hAre, hre, hlt1, hbet⟩ := par1_facts hm1
  have he1dn : entry N 1 dn = entry N 1 (dn - 1) := he1eq
  -- `dn − 1` is below `d`
  obtain ⟨c, hpc, hce⟩ := anc0_child hAre (by omega)
  have hcd : c = d := by
    have hcl : c < N.length := lt_of_le_of_lt hce.le (by omega)
    have hcc : c ∈ children N r := mem_children_iff.mpr ⟨hcl, hpc⟩
    rcases lt_trichotomy c d with h | h | h
    · exfalso
      have hAcd : Anc0 N c d := anc_between hce d (le_of_lt h) (by omega)
      have := (anc0_par hAcd (by omega) hpd).le
      have := par_lt N 0 c r hpc; omega
    · exact h
    · exfalso
      have := hcons c hcc h
      have := hce.le; omega
  subst hcd
  have hde : c ≠ dn - 1 := by intro h; rw [h] at he2d; omega
  -- the last child `jl` of `d`
  obtain ⟨jl, hpjl, hjle⟩ := anc0_child hce hde
  have hjlL : jl < N.length := lt_of_le_of_lt hjle.le (by omega)
  have hjl : jl ∈ children N c := mem_children_iff.mpr ⟨hjlL, hpjl⟩
  have hjlast : ∀ j' ∈ children N c, j' ≤ jl := by
    intro j' hj'
    by_contra hlt
    have hpj' : par N 0 j' = some c := (mem_children_iff.mp hj').2
    rcases Nat.lt_or_ge j' (dn - 1 + 1) with h | h
    · have hA : Anc0 N jl j' := anc_between hjle j' (by omega) (by omega)
      have := (anc0_par hA (by omega) hpj').le
      have := par_lt N 0 jl c hpjl; omega
    · -- `j'` is after `dn`, so `dn` is below `c`
      have hcj : Anc0 N c j' := anc0_of_par N 0 c j' hpj'
      have hjn : j' ≠ dn := fun h' => by rw [h'] at hpj'; rw [hpdn] at hpj'; cases hpj'; omega
      have hA : Anc0 N c dn := anc_between hcj dn (by omega) (by omega)
      have := (anc0_par hA (by omega) hpdn).le; omega
  have hgl : (children N c).getLast? = some jl := by
    rcases (children N c).eq_nil_or_concat with hnil | ⟨L', jj, hL⟩
    · rw [hnil] at hjl; simp at hjl
    rw [List.concat_eq_append] at hL
    have hjj : jj ∈ children N c := by rw [hL]; simp
    have h1 := hjlast jj hjj
    have hsorted := children_sorted N c
    rw [hL] at hsorted hjl
    have h2 : jl = jj := by
      rcases List.mem_append.mp hjl with h | h
      · have := (List.pairwise_append.mp hsorted).2.2 jl h jj (by simp); omega
      · simpa using h
    rw [hL, h2]; simp
  have hjlb : col N jl = bump N c := by
    unfold topped at htop; rw [hgl] at htop; simpa using htop
  have he1jl : entry N 1 jl = entry N 1 c := by
    have : entry N 1 jl = (col N jl).2.1 := rfl; rw [this, hjlb]; rfl
  have he2jl : entry N 2 jl = 1 := by
    have : entry N 2 jl = (col N jl).2.2 := rfl; rw [this, hjlb]; rfl
  have hjle' : jl ≠ dn - 1 := by intro h; rw [h] at he2jl; omega
  -- the last child `kl` of `jl` is `dn − 1`
  obtain ⟨kl, hpkl, hkle⟩ := anc0_child hjle hjle'
  have hklL : kl < N.length := lt_of_le_of_lt hkle.le (by omega)
  have hkl : kl ∈ children N jl := mem_children_iff.mpr ⟨hklL, hpkl⟩
  have hz1 := hX.loc.2.1 jl kl he2jl hkl
  have hge : entry N 1 (dn - 1) ≤ entry N 1 kl := by
    by_cases hk : kl = dn - 1
    · rw [hk]
    · have hArk : Anc0 N r kl :=
        Anc0.trans (anc0_of_par N 0 r c hpd) (Anc0.trans (anc0_of_par N 0 c jl hpjl) (anc0_of_par N 0 jl kl hpkl))
      exact hbet kl hArk hkle (by have := par_lt N 0 kl jl hpkl; have := par_lt N 0 jl c hpjl; omega) hk
  obtain ⟨_, hleaf, hlastk, _⟩ := hX.loc.2.2.2 c jl kl hjl hjlb hkl (by omega)
  have hkle2 : kl = dn - 1 := by
    by_contra hne
    obtain ⟨k2, hpk2, hk2e⟩ := anc0_child hkle hne
    have : k2 ∈ children N kl := mem_children_iff.mpr ⟨by have := hk2e.le; omega, hpk2⟩
    rw [hleaf] at this; simp at this
  -- values
  have hrL : r < N.length := by omega
  have hvro := hG.ot_v r hrL
  have hbot : ∀ i j, isOT (bumpTerm N τ i j) = true := fun i j => isOT_bumpTerm hG i j
  have hWot : ∀ i, isOT (sumN (one :: (children N i).map (bumpTerm N τ i))) = true := by
    intro i; apply isOT_sumN; intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact hbot i j
  have he1dn0 : entry N 1 dn ≠ 0 := by rw [he1dn]; exact he1e
  have hvdn : τ.v dn = add (τ.v r) (omega (sumN (one :: (children N dn).map (bumpTerm N τ dn)))) := by
    rw [(hC dn hdnL).2]; unfold vRhs; rw [if_neg he1dn0, if_neg (by omega), hP1dn]
    exact sf_ot (isOT_add hvro (isOT_omega (hWot dn)))
  have hvdnz : τ.v dn ≠ z := by
    rw [hvdn]; obtain ⟨a, b, hab⟩ := omega_psi_form (sumN (one :: (children N dn).map (bumpTerm N τ dn)))
    rw [hab]
    cases h : τ.v r with
    | z => simp
    | psi a1 b1 c1 =>
      show (if lt (psi a1 b1 z) (psi a b z) then psi a b z else psi a1 b1 (add c1 (psi a b z))) ≠ z
      split <;> simp
  have hOm : ¬ lt (psi (τ.v dn) z z) (psi z (psi one z z) z) = true := by
    intro h
    have h' : psi (τ.v dn) z z < psi z (psi one z z) z := h
    rw [psi_lt_psi_z_iff] at h'
    rcases h' with h | ⟨h, _⟩
    · exact T.not_lt_z _ h
    · exact hvdnz h
  -- `o(kl) = Ω_{v(dn)}`
  have hu' : upg N kl = some dn := by rw [hkle2]; exact hu
  have he1k : entry N 1 kl ≠ 0 := by rw [hkle2]; exact he1e
  have he2k : entry N 2 kl = 0 := by rw [hkle2]; exact he2e0
  have hvkl : τ.v kl = τ.v dn := v_upg_eq hC hklL he1k he2k hu' (vOpt_ot hG hklL)
    (fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
  have hvdno := hG.ot_v dn hdnL
  have hOmo : isOT (psi (τ.v dn) z z) = true := isOT_psi_zz hvdno
  have hokl : τ.o kl = psi (τ.v dn) z z := by
    have hCLk : CL N kl = [] := by unfold CL; rw [hleaf]; rfl
    rw [o_cl_eq hC hG hklL, hCLk, hvkl]; rfl
  obtain ⟨Lk, hLk⟩ : ∃ Lk, children N jl = Lk ++ [kl] := ⟨_, (List.dropLast_append_getLast? _ hlastk).symm⟩
  have hko : ∀ t ∈ Lk.map τ.o, isOT t = true := by
    intro t ht; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
    exact hG.ot_o k (mem_children (show k ∈ children N jl by rw [hLk]; simp [hk])).2
  have hko' : ∀ t ∈ (children N jl).map τ.o, isOT t = true := by
    intro t ht; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o k (mem_children hk).2
  have hbt : bumpTerm N τ c jl = omega (sumN ((children N jl).map τ.o)) := by
    unfold bumpTerm; rw [if_pos hjlb]
  have hsum : psi (τ.v dn) z z ≤ sumN ((children N jl).map τ.o) := by
    rw [hLk, List.map_append, List.map_singleton, sumN_snoc_add hko (hG.ot_o kl hklL), hokl]
    exact le_add_left_self hOmo _
  have hbtge : psi (τ.v dn) z z ≤ bumpTerm N τ c jl := by
    rw [hbt]
    have := omega_le_omega hOmo (isOT_sumN _ hko') hsum
    rwa [G.omega_Om hOm] at this
  obtain ⟨Lc, hLc⟩ : ∃ Lc, children N c = Lc ++ [jl] := ⟨_, (List.dropLast_append_getLast? _ hgl).symm⟩
  have hLco : ∀ t ∈ one :: Lc.map (bumpTerm N τ c), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact hbot c j
  have hWge : bumpTerm N τ c jl ≤ sumN (one :: (children N c).map (bumpTerm N τ c)) := by
    rw [hLc, List.map_append, List.map_singleton, ← List.cons_append, sumN_snoc_add hLco (hbot c jl)]
    exact le_add_left_self (hbot c jl) _
  have hW := le_trans hbtge hWge
  have hWo := hWot c
  have hωW : sumN (one :: (children N c).map (bumpTerm N τ c)) ≤
      omega (sumN (one :: (children N c).map (bumpTerm N τ c))) := by
    cases hWc : sumN (one :: (children N c).map (bumpTerm N τ c)) with
    | z => rw [hWc] at hW; exact absurd hW (not_le.mpr (T.z_lt_psi _ _ _))
    | psi s b c' =>
      rw [hWc] at hWo hW
      apply le_omega_big hWo
      intro hlt
      apply hOm
      exact lt_of_le_of_lt hW hlt
  have hvd : τ.v c = add (τ.v r) (omega (sumN (one :: (children N c).map (bumpTerm N τ c)))) := by
    rw [(hC c hdL).2]; unfold vRhs; rw [if_neg (by omega), if_neg (by omega), hP1d]
    exact sf_ot (isOT_add hvro (isOT_omega hWo))
  rw [hvd]
  calc τ.v dn < psi (τ.v dn) z z := lt_Om_self _
    _ ≤ sumN (one :: (children N c).map (bumpTerm N τ c)) := hW
    _ ≤ omega (sumN (one :: (children N c).map (bumpTerm N τ c))) := hωW
    _ ≤ add (τ.v r) (omega (sumN (one :: (children N c).map (bumpTerm N τ c)))) :=
      le_add_left_self (isOT_omega hWo) _

namespace G

/-- **The structural residual of the C seed**: an uncounted child `d < q` of `r` (in `M.take x`) whose next
sibling `dn < q` is counted has `dn` upgraded from `dn − 1`. -/
structure T2SeedCNext (M : Mat) (r L q : Nat) : Prop where
  next : ∀ d dn, d ∈ children (M.take (r + L)) r → dn ∈ children (M.take (r + L)) r → d < dn →
    (∀ e ∈ children (M.take (r + L)) r, d < e → dn ≤ e) → dn < q →
    ¬ Counted (M.take (r + L)) r d → Counted (M.take (r + L)) r dn →
    upg (M.take (r + L)) (dn - 1) = some dn

open Classical in
/-- **`T2SeedCBig` from `T2SeedCNext`** (C, with t2's `T2SeedCRes`). -/
theorem t2SeedCBig_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hRes : T2SeedCRes M ρ r L q) (hN : T2SeedCNext M r L q) : T2SeedCBig M ρ r L q := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 q r hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, _, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have hqnc := qP_C hM hS I hlen hr hq hqr hncl hRes.un
  -- the drop and `M.take x`
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := drop_all hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs R.drop.vst
    I.fc I.fo R.drop.argT
    (bump_drop hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td R.drop.ab R.drop.ws)
    R.drop.ua
  have hG1 := good3_take hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop
  rw [show M.length - 1 = r + L by omega] at hRk1 hC1 hG1
  have hTS : M.take (r + L) ≠ SRO := ne_SRO_of_rk hRk1
  obtain ⟨hXT, hJT⟩ := sInvXJ_std (std_take hM (r + L) (by omega)) hTS
  have hTlen : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  -- the columns of the children of `r`
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he2q : entry M 2 q = 1 := hX.loc.2.2.1 q (r + L) hxq Txb
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have he1x : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  have hcolr : ∀ c ∈ children (M.take (r + L)) r, entry (M.take (r + L)) 1 c = entry (M.take (r + L)) 1 r + 1 ∧
      entry (M.take (r + L)) 2 c = 1 ∧ par (M.take (r + L)) 1 c = some r := by
    intro c hc
    have hcx : c < r + L := by have := (mem_children hc).2; omega
    have hpcT := (mem_children_iff.mp hc).2
    have hpc : par M 0 c = some r := by rwa [par_take M 0 c hcx] at hpcT
    have hcq : c ≤ q := by
      by_contra hlt
      have hA : Anc0 M q c := anc_between (anc0_of_par M 0 q (r + L) hq) c (by omega) (le_of_lt hcx)
      have := (anc0_par hA (by omega) hpc).le; omega
    have hcol := t_child_col hX hpq (by omega) he2q (by omega) (mem_children_iff.mpr ⟨by omega, hpc⟩) hcq
    have hcqx := t_col_x hX hpq (by omega) he2q (by omega)
    have h1 : entry M 1 c = entry M 1 r + 1 := by
      have : entry M 1 c = (col M c).2.1 := rfl; rw [this, hcol, hcqx]
    have h2 : entry M 2 c = 1 := by
      have : entry M 2 c = (col M c).2.2 := rfl; rw [this, hcol, hcqx]
    refine ⟨by rw [entry_take M 1 hcx, entry_take M 1 (by omega)]; exact h1,
      by rw [entry_take M 2 hcx]; exact h2, ?_⟩
    rw [par_take M 1 c hcx]; exact par1_of_child hpc (by omega)
  have hqT : q ∈ children (M.take (r + L)) r := by
    rw [children_take, List.mem_filter]
    exact ⟨mem_children_iff.mpr ⟨by omega, hpq⟩, by simpa using hqx⟩
  -- an uncounted child is topped and upgraded from the previous column
  have huncnt : ∀ c ∈ children (M.take (r + L)) r, ¬ Counted (M.take (r + L)) r c →
      topped (M.take (r + L)) c = true ∧ upg (M.take (r + L)) (c - 1) = some c := by
    intro c hc hnc
    have hb : col (M.take (r + L)) c ≠ bump (M.take (r + L)) r := by
      intro h
      have : entry (M.take (r + L)) 1 c = (col (M.take (r + L)) c).2.1 := rfl
      rw [h] at this; simp [bump] at this; have := (hcolr c hc).1; omega
    have hut : isUpg (M.take (r + L)) c = true ∧ topped (M.take (r + L)) c = true := by
      by_contra hn; exact hnc ⟨hb, hn⟩
    refine ⟨hut.2, ?_⟩
    unfold isUpg at hut
    obtain ⟨i, _, hi⟩ := List.any_eq_true.mp hut.1
    have hu : upg (M.take (r + L)) i = some c := of_decide_eq_true hi
    by_cases hci : c = i + 1
    · rw [hci, Nat.add_sub_cancel]; rw [hci] at hu; exact hu
    · have := hXT.toSInv.uat i c hu hci; rw [this] at hut; simp at hut
  refine ⟨fun τ hτ => ?_⟩
  have hG : Good3 (M.take (r + L)) τ := good3_congr hG1 (agree_of_cons hC1 hτ hRk1)
  have hrT : r < (M.take (r + L)).length := by omega
  -- counted children are above `s′`
  have hcntd : ∀ d ∈ children (M.take (r + L)) r, Counted (M.take (r + L)) r d → qnS M ρ r L q < τ.v d := by
    intro d hd hcnt
    have hdCL : d ∈ CL (M.take (r + L)) r := List.mem_filter.mpr ⟨hd, decide_eq_true hcnt⟩
    obtain ⟨hsing, hdec⟩ := cl_vals hτ hG hrT
    rcases (CL (M.take (r + L)) r).eq_nil_or_concat with hnil | ⟨Lc, c0, hLc⟩
    · rw [hnil] at hdCL; simp at hdCL
    rw [List.concat_eq_append] at hLc
    obtain ⟨s, y, hc0, hs⟩ := hRes.decP τ hτ Lc c0 hLc
    have hc0T : c0 < (M.take (r + L)).length :=
      (mem_children (cl_mem_children (show c0 ∈ CL (M.take (r + L)) r by rw [hLc]; simp))).2
    have hdT := (mem_children hd).2
    have hvc0 : τ.v c0 = s := by
      rw [o_cl_eq hτ hG hc0T] at hc0; simp only [psi.injEq] at hc0; exact hc0.1
    have hle : τ.o c0 ≤ τ.o d := by
      rw [hLc] at hdCL hdec
      rcases List.mem_append.mp hdCL with h | h
      · exact (List.pairwise_append.mp (List.pairwise_map.mp hdec)).2.2 d h c0 (by simp)
      · simp at h; rw [h]
    have hl := lev_le_of_le hle
    rw [o_cl_eq hτ hG hc0T, o_cl_eq hτ hG hdT] at hl
    simp only [lev_psi] at hl
    rw [hvc0] at hl
    exact lt_of_lt_of_le hs hl
  -- induction from the right
  have key : ∀ n d, q - d ≤ n → d ∈ children (M.take (r + L)) r → d < q → qnS M ρ r L q < τ.v d := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro d hn hd hdq
    by_cases hcnt : Counted (M.take (r + L)) r d
    · exact hcntd d hd hcnt
    -- the next sibling
    have hex : ∃ e, e ∈ children (M.take (r + L)) r ∧ d < e := ⟨q, hqT, hdq⟩
    let dn := Nat.find hex
    obtain ⟨hdn, hddn⟩ := Nat.find_spec hex
    have hcons : ∀ e ∈ children (M.take (r + L)) r, d < e → dn ≤ e :=
      fun e he hde => Nat.find_min' hex ⟨he, hde⟩
    have hdnq : dn ≤ q := hcons q hqT hdq
    have hu : upg (M.take (r + L)) (dn - 1) = some dn := by
      by_cases hdnc : Counted (M.take (r + L)) r dn
      · have hdnq' : dn < q := by
          rcases Nat.eq_or_lt_of_le hdnq with h | h
          · exfalso; rw [h] at hdnc; exact hqnc hdnc
          · exact h
        exact hN.next d dn hd hdn hddn hcons hdnq' hcnt hdnc
      · exact (huncnt dn hdn hdnc).2
    have hlt := upg_next_lt hXT hτ hG hd hdn hddn hcons (hcolr d hd).1 (hcolr d hd).2.1 (hcolr d hd).2.2
      (hcolr dn hdn).2.1 (hcolr dn hdn).2.2 (huncnt d hd hcnt).1 hu
    have hlt' : τ.v dn < τ.v d := hlt
    rcases Nat.eq_or_lt_of_le hdnq with h | h
    · rw [h] at hlt'; rw [← hRes.vqP τ hτ]; exact hlt'
    · exact lt_trans (ih (q - dn) (by omega) dn le_rfl hdn h) hlt'
  intro d hd hdq _
  exact key (q - d) d le_rfl hd hdq

end G

end Ytosk
