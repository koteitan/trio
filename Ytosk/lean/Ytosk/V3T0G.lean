/-
**3 行・t = 0: 種 S2 の最後のコピー（M.take x で r の子の値が変わる場合）。**

x = r + L（最後の列、P_0(x) = r、行 1 が 0）、r は g = P_0(r) ののりしろの子。N の最後のコピーの和は
G0′ = Σ_{r の子} o′（M.take x の値）。以前の仮定 hG′（G0′ = G0）は Std で偽:
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,1,0)(5,0,0)（標準形、SRO 未満）では
x − 1 = 8 が祖先 4 に上げ、M.take x でその上げが消えて o(8) が Ω_ω から Ω_1 に下がる。
- x − 1 に上げがなければ (r, x) の列は C に入らない（`no_chg_B`、`children_r_take_same`）。
- 一般には `g_level`（落とす補題ののりしろの枠）で G0′ と G0 + 1 が強い関係、それを G0 に縮める
  （`brelS_untail`、G0′ ≤ G0 は子ごとの ⊴）。弱い場合（o が変わる子で v′ ⋪ v）は仮定 hWk で除く
  （`g0_drop_rel`）。
- 種: ψ が ω^{G0}·(n − 1) + ω^{G0′} ⊴ ω^{G0}·n ◁ ω^{G0+1}（`s2_p2`、`t0_S2G`）。
実測（A・B・C の全接頭辞で前件 8097 個）: G0′ = G0 が 8095 個、G0′ ◁ G0 が 2 個、v_N(g) ◁ v_M(g) は全部。
-/
import Ytosk.V3T0S3

namespace Ytosk

open T

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB

/-- **Nothing strictly between the parent `r` of `x` and `x` changes** when `x − 1` has no upgrade. -/
theorem no_chg_B {r : Nat} (hp : par M 0 x = some r) (he1 : entry M 1 x = 0)
    (hU : r < x - 1 → upg M (x - 1) = none) :
    ∀ b d, ChgX M x b d → r < d → d < x → False := by
  have hrx : r < x := par_lt M 0 x r hp
  have hparx : ∀ i, x ∈ children M i → i = r := fun i h => by
    have := (mem_children_iff.mp h).2; rw [hp] at this; exact (Option.some.inj this).symm
  intro b d h
  induction h with
  | leaf => intro _ h; omega
  | supg hne =>
    intro h1 _
    exact hne (hU h1)
  | @scnt i c hc hcx hnot =>
    intro h1 h2
    have hic := (mem_children hc).1
    rcases cnt_change hx h2 hcx hnot with h | h
    · have := hparx c h; omega
    · exact absurd h (by rw [hU (by omega)]; simp)
  | @snb i _ _ hxi _ =>
    intro h1 _
    have := hparx i hxi; omega
  | @ochild i c hc _ _ _ ih =>
    intro h1 h2
    have hic := (mem_children hc).1
    have hcl := (mem_children hc).2
    by_cases hcx : c < x
    · exact ih (by omega) hcx
    · have hce : c = x := by omega
      subst hce
      have := hparx i hc; omega
  | ov _ ih => exact ih
  | @vpar i m _ hpm hm ih =>
    intro h1 h2
    have hmi := par_lt M 1 i m hpm
    by_cases hrm : r < m
    · exact ih hrm (by omega)
    · have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hm).1 rfl (by omega)
      exact hT.2.2 i h2 hpm
  | @vupg i k h1 _ hu hk ih =>
    intro hri hix
    obtain ⟨m, _, _, hcol, hcase⟩ := upg_spec hu
    rcases hcase with hki | ⟨hA, hki⟩
    · by_cases hkx : k < x
      · exact ih (by omega) hkx
      · -- `k = x` would give row 1 of `x` equal to that of `i`
        have hke : k = x := by have := upg_succ_lt hu; omega
        subst hke
        have : entry M 1 k = entry M 1 i := by
          have e : entry M 1 k = (col M k).2.1 := rfl
          rw [e, hcol]
        exact h1 (this ▸ he1)
    · by_cases hrk : r < k
      · exact ih hrk (by omega)
      · have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hk).1 rfl (by omega)
        exact no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB hT (by omega) hu hA hki
  | @vbump i j k _ _ hj _ hk _ ih =>
    intro h1 h2
    have hij := (mem_children hj).1
    have hjk := (mem_children hk).1
    have hkl := (mem_children hk).2
    by_cases hkx : k < x
    · exact ih (by omega) hkx
    · have hke : k = x := by omega
      subst hke
      have := hparx j hk; omega

end

/-- **The children of `r` keep their values in `M.take x`** (hence their sum: `hG′` of `t0_main′`). -/
theorem children_r_take_same {M : Mat} {x r : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hp : par M 0 x = some r) (he1 : entry M 1 x = 0) (hU : r < x - 1 → upg M (x - 1) = none)
    {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hR' : Rk (M.take x) rk') :
    (children (M.take x) r).map ρ'.o = (children (M.take x) r).map ρ.o := by
  apply List.map_congr_left
  intro c hc
  rw [children_take, List.mem_filter] at hc
  have hcx : c < x := by simpa using hc.2
  have hrc := (mem_children hc.1).1
  exact (chg_off hx hC hG hC' hR' c hcx).1
    (fun h => no_chg_B hx hR0 hZ2 hSD hZ1 hUAT hUAB hp he1 hU true c h hrc hcx)

/-! ## 最後のコピーの和が下がる場合（x − 1 の上げが消える） -/

/-- **Removing the tail `+ 1`**: `BRelS X′ (G + 1)` and `X′ ≤ G` give `BRelS X′ G`. -/
theorem brelS_untail {X' G : T} (h : BRelS X' (app G one)) (hle : X' ≤ G) : BRelS X' G := by
  rcases (le_iff _ _).mp hle with hlt | rfl
  swap
  · exact brelS_refl
  have hGz : G ≠ z := by rintro rfl; exact T.not_lt_z _ hlt
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, G = psi a b c := by
    cases G with
    | z => exact absurd rfl hGz
    | psi a b c => exact ⟨a, b, c, rfl⟩
  have hres : ∀ {Y : T}, LhdE X' (app (psi a b c) one) → LhdE X' (psi a b c) := by
    intro _ hl
    rcases hl with heq | hl
    · exfalso; rw [heq] at hlt
      exact lt_irrefl' _ (lt_trans hlt (lt_app_one _))
    · exact Or.inr (lhd_restrict hl hlt (le_of_lt (lt_app_one _)))
  simp only [app_psi] at h
  rcases h with ⟨hl, hE⟩ | ⟨hl, hE', s, b', c', b2, c2, rfl, he⟩ | ⟨hl, hE', hcl, hE, b2, c2, he⟩ |
      ⟨w', w, Y, c2, rfl, he, hw, h1⟩
  · exact Or.inl ⟨hres (Y := z) (by simpa [app_psi] using hl), lt_E0_rest hE⟩
  · simp only [psi.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    exact Or.inr (Or.inl ⟨hres (Y := z) (by simpa [app_psi] using hl), hE', _, _, _, _, _, rfl, rfl⟩)
  · simp only [psi.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    exact Or.inr (Or.inr (Or.inl ⟨hres (Y := z) (by simpa [app_psi] using hl), hE', hcl,
      fun h' => hE (lt_E0_rest h'), _, _, rfl⟩))
  · simp only [psi.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    exact Or.inr (Or.inr (Or.inr ⟨w', a, b, c, rfl, rfl, hw, h1⟩))

/-- **The `p` level of seed S2 with a dropped last copy**: `1 + P + O·(n − 1) + O′` against `1 + P + X`
with `O′ ⊴ O`. -/
theorem s2_p2 {Pl : List T} {O O' X : T} {n : Nat} (hn : 2 ≤ n)
    (hsP : ∀ q ∈ Pl, Single q) (hpP : Pl.Pairwise (fun a b => b ≤ a)) (hPt : ∀ q ∈ Pl, X ≤ q)
    (hO : Single O) (hO' : Single O') (hX : Single X) (hOX : O < X)
    (hlm : ∀ k, Lhd z (mulT O k) X)
    (hsh : ∃ s b', O = psi s b' z ∧ X = psi s (app b' one) z) (hO'O : LhdE O' O) :
    BRelS (sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O']))) (sumN (one :: Pl ++ [X])) ∧
      sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O'])) < sumN (one :: Pl ++ [X]) := by
  rcases hO'O with rfl | hl
  · have : List.replicate (n - 1) O' ++ [O'] = List.replicate n O' := by
      rw [← List.replicate_succ']; congr 1; omega
    rw [this]
    exact s2_p (by omega) hsP hpP hPt hO hX hOX hlm hsh
  obtain ⟨s, b', rfl, rfl⟩ := hsh
  set O := psi s b' z with hOdef
  set X := psi s (app b' one) z with hXdef
  have hRs : ∀ t ∈ List.replicate (n - 1) O ++ [O'], Single t := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · rw [(List.mem_replicate.mp h).2]; exact hO
    · simp at h; rw [h]; exact hO'
  have hRp : (List.replicate (n - 1) O ++ [O']).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_append.mpr ⟨List.pairwise_replicate.mpr (Or.inr (le_refl _)), by simp,
      fun a ha b hb => by
        simp at hb; rw [hb, (List.mem_replicate.mp ha).2]; exact le_of_lt hl.1⟩
  have hsumR : sumN (List.replicate (n - 1) O ++ [O']) = app (mulT O (n - 1)) O' := by
    rw [sumN_snoc_dec hRs hRp, sumN_replicate hO]
  have hT : Lhd z (app (mulT O (n - 1)) O') X := by
    have h1 : LhdE (app (mulT O (n - 1)) O') (mulT O n) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [mulT_succ', show m + 1 - 1 = m by omega]
      exact lhdE_app _ (Or.inr hl)
    exact lhd_of_lhdE_lt (LhdE.trans h1 (Or.inr (hlm n))) (lt_of_le_of_lt h1.le (hlm n).1)
  obtain ⟨m, hm⟩ : ∃ m, n - 1 = m + 1 := ⟨n - 2, by omega⟩
  have hTf : app (mulT O (n - 1)) O' = psi s b' (app (mulT O m) O') := by
    rw [hm, show mulT O (m + 1) = app O (mulT O m) from rfl, app_assoc, hOdef, app_psi, app_z]
  have hone : one < X := by
    unfold one; rw [hXdef, psi_lt_psi]
    rcases lt_or_ge z s with h | h
    · exact Or.inl h
    · have hs : s = z := le_antisymm h (z_le _)
      subst hs
      exact Or.inr (Or.inl ⟨rfl, lt_of_le_of_lt (z_le b') (lt_app_one b')⟩)
  have hO1 : one < O := lt_of_le_of_lt (one_le_of_ne_z (single_ne_z hO')) hl.1
  cases Pl with
  | nil =>
    simp only [List.cons_append, List.nil_append]
    rw [onep_self hX hone]
    rw [show List.replicate (n - 1) O ++ [O'] = O :: (List.replicate m O ++ [O']) by
      rw [hm, List.replicate_succ, List.cons_append]]
    rw [sumN_one_cons_gt hO hO1, ← List.cons_append, ← List.replicate_succ, ← hm, hsumR]
    refine ⟨?_, hT.1⟩
    by_cases hE : X < E0
    · exact Or.inl ⟨Or.inr hT, hE⟩
    · rw [hTf] at hT ⊢
      refine Or.inr (Or.inl ⟨Or.inr hT, ?_, s, b', app (mulT O m) O', app b' one, z, rfl, rfl⟩)
      intro hlt
      obtain ⟨hv, hb⟩ := lt_E0_iff.mp hlt
      exact hE (lt_E0_iff.mpr ⟨hv, app_one_lt_Om hb⟩)
  | cons q Pr =>
    have hq := hsP q (by simp)
    have hq1 : one < q := lt_of_lt_of_le hone (hPt q (by simp))
    simp only [List.cons_append]
    rw [sumN_one_cons_gt hq hq1, sumN_one_cons_gt hq hq1, ← List.cons_append, ← List.cons_append]
    have hall : ∀ t ∈ (q :: Pr) ++ [X], Single t := fun t ht => by
      rcases List.mem_append.mp ht with h | h
      · exact hsP t h
      · simp at h; rw [h]; exact hX
    have hpall : ((q :: Pr) ++ [X]).Pairwise (fun a b => b ≤ a) :=
      List.pairwise_append.mpr ⟨hpP, by simp, fun a ha b hb => by simp at hb; rw [hb]; exact hPt a ha⟩
    have hall' : ∀ t ∈ (q :: Pr) ++ (List.replicate (n - 1) O ++ [O']), Single t := fun t ht => by
      rcases List.mem_append.mp ht with h | h
      · exact hsP t h
      · exact hRs t h
    have hpall' : ((q :: Pr) ++ (List.replicate (n - 1) O ++ [O'])).Pairwise (fun a b => b ≤ a) :=
      List.pairwise_append.mpr ⟨hpP, hRp, fun a ha b hb => by
        have hb' : b ≤ O := by
          rcases List.mem_append.mp hb with h | h
          · rw [(List.mem_replicate.mp h).2]
          · simp at h; rw [h]; exact le_of_lt hl.1
        exact le_trans hb' (le_trans (le_of_lt hOX) (hPt a ha))⟩
    rw [sumN_append_dec hall hpall, sumN_append_dec hall' hpall', hsumR, sumN_singleton hX]
    have hS : sumN (q :: Pr) ≠ z := sumN_ne_z hsP hpP (by simp)
    refine ⟨?_, app_lt_app_left _ hT.1⟩
    have := brelS_app_same hS (Or.inr hT) z
    simpa using this

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : Good3 (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

/-- **Seed S2, with a dropped last copy**: when `r` is a bump child of its parent `g` (rows 1 and 2 of `g` nonzero), `v(g)`
drops by `◁` in `N`. -/
theorem t0_S2G {g : Nat} (hg : par M 0 r = some g) (hjb : col M r = bump M g)
    (h1 : entry M 1 g ≠ 0) (h2 : entry M 2 g ≠ 0)
    (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ)
    (hbF : ∀ d, d ∈ children M g → d < r →
      bumpTerm (TRIO.gexp M r L 0 0 n) σ g d = bumpTerm M ρ g d)
    (hbroot : ∀ k, k + 1 < n → bumpTerm (TRIO.gexp M r L 0 0 n) σ g (r + k * L) =
      omega (sumN ((children (M.take (r + L)) r).map ρ.o)))
    {O' : T} (hblast : bumpTerm (TRIO.gexp M r L 0 0 n) σ g (r + (n - 1) * L) = O') (hO'S : Single O')
    (hO'O : LhdE O' (omega (sumN ((children (M.take (r + L)) r).map ρ.o))))
    (hV : vOpt σ (par (TRIO.gexp M r L 0 0 n) 1 g) = vOpt ρ (par M 1 g)) :
    Lhd z (σ.v g) (ρ.v g) := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hgr : g < r := par_lt M 0 r g hg
  have hgM : g < M.length := by omega
  have hgN : g < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  set G0 := sumN ((children (M.take (r + L)) r).map ρ.o) with hG0
  have hG0ot : isOT G0 = true := isOT_sumN _ (fun t ht => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    rw [children_take, List.mem_filter] at hc
    exact hG.ot_o c (mem_children hc.1).2)
  -- the bump term of `r` in `M`
  have hbr : bumpTerm M ρ g r = omega (app G0 one) := by
    unfold bumpTerm
    rw [if_pos hjb]
    have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
    rw [children_split_x (x := r + L) hlen hxr, List.map_append, List.map_singleton,
      o_x_one hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN, sumN_snoc,
      ← children_take, ← hG0, sf_ot (isOT_add hG0ot rfl), add_one_eq_app]
  -- the children of `g`
  set F := (children M g).filter (fun d => decide (d < r)) with hFdef
  have hchM : children M g = F ++ [r] := children_g_last hlen hL hp hg
  set f : Nat → Nat := fun k => r + k * L with hfdef
  have hchN : children (TRIO.gexp M r L 0 0 n) g = F ++ (List.range n).map f := by
    rw [children_g0 hlen hL hp hn hg, hchM, List.append_assoc]
    congr 1
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [hfdef]
  set Lb := F.map (bumpTerm M ρ g) with hLb
  set O := omega G0 with hOdef
  set X := omega (app G0 one) with hXdef
  have hmapM : (children M g).map (bumpTerm M ρ g) = Lb ++ [X] := by
    rw [hchM, List.map_append, List.map_singleton, hbr]
  have hmapN : (children (TRIO.gexp M r L 0 0 n) g).map (bumpTerm (TRIO.gexp M r L 0 0 n) σ g) =
      Lb ++ (List.replicate (n - 1) O ++ [O']) := by
    rw [hchN, List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro d hd
      have := List.mem_filter.mp hd
      exact hbF d this.1 (by simpa using this.2)
    · have hr : List.range n = List.range (n - 1) ++ [n - 1] := by
        rw [← List.range_succ]; congr 1; omega
      rw [hr, List.map_append]
      congr 1
      · rw [List.eq_replicate_iff]
        refine ⟨by simp, fun b hb => ?_⟩
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
        exact hbroot k (by have := List.mem_range.mp hk; omega)
      · simp only [List.map_cons, List.map_nil]
        exact congrArg (fun t => [t]) hblast
  -- the shapes
  obtain ⟨sO, bO, hOf, hXf⟩ := omega_succ_form hG0ot
  have hO : Single O := single_omega hG0ot
  have hXot : isOT (app G0 one) = true := by have := isOT_succ hG0ot; simpa [succ] using this
  have hX : Single X := single_omega hXot
  have hOX : O < X := omega_lt_omega hG0ot hXot (lt_app_one G0)
  have hlm : ∀ k, Lhd z (mulT O k) X := by
    intro k; rw [hOdef, hXdef, hOf, hXf]; exact lhd_mulT k
  -- the `p` level
  set V := vOpt ρ (par M 1 g) with hVdef
  have hVot : isOT V = true := by
    rw [hVdef]
    cases hpp : par M 1 g with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 g m hpp; omega)
  have hLbot : ∀ t ∈ Lb, isOT t = true := fun t ht => by
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG g d
  set Pl := nzs Lb with hPl
  have hnzT : ∀ (T0 : List T), (∀ t ∈ T0, Single t) →
      sumN (one :: (Lb ++ T0)) = sumN (one :: Pl ++ T0) := by
    intro T0 hT0
    rw [sumN_nzs (l := one :: (Lb ++ T0)) (fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · rcases List.mem_append.mp ht with ht | ht
        · exact hLbot t ht
        · exact (hT0 t ht).1)]
    have hT : T0.filter (fun t => !decide (t = z)) = T0 := by
      rw [List.filter_eq_self]; intro t ht; simpa using single_ne_z (hT0 t ht)
    simp only [nzs, List.filter_cons, List.filter_append]
    simp [one]
    rw [hT, hPl, nzs]; simp
  have hsP : ∀ q ∈ Pl, Single q := by
    intro q hq
    rw [hPl, nzs, List.mem_filter] at hq
    obtain ⟨hq, hqz⟩ := hq
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
    unfold bumpTerm at hqz ⊢
    by_cases hb : col M d = bump M g
    · rw [if_pos hb]
      exact single_omega (by
        apply isOT_sumN; intro t ht
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o k (mem_children hk).2)
    · rw [if_neg hb] at hqz; simp at hqz
  have hdecP := hTD g h1 h2
  rw [hmapM, nzs_append, nzs_single (single_ne_z hX)] at hdecP
  have hpre := List.pairwise_append.mp hdecP
  have hpP : Pl.Pairwise (fun a b => b ≤ a) := hpre.1
  have hPt : ∀ q ∈ Pl, X ≤ q := fun q hq => hpre.2.2 q hq _ (by simp)
  have hT0s : ∀ t ∈ List.replicate (n - 1) O ++ [O'], Single t := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · rw [(List.mem_replicate.mp h).2]; exact hO
    · simp at h; rw [h]; exact hO'S
  obtain ⟨hS, hlt⟩ := s2_p2 hn2 hsP hpP hPt hO hO'S hX hOX hlm ⟨sO, bO, hOf, hXf⟩ hO'O
  have hPot : ∀ t ∈ one :: Pl, isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · exact (hsP t ht).1
  have hp'ot : isOT (sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O']))) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPot t h
    · exact (hT0s t h).1)
  have hpot : isOT (sumN (one :: Pl ++ [X])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPot t h
    · simp at h; rw [h]; exact hX.1)
  have ev : ρ.v g = add V (omega (sumN (one :: Pl ++ [X]))) := by
    rw [(hC g hgM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, hmapM, hnzT [X] (by simp [hX]),
      sf_ot (isOT_add hVot (isOT_omega hpot))]
  have ev' : σ.v g = add V (omega (sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O'])))) := by
    rw [(hCN g hgN).2]; unfold vRhs
    rw [entry_pre0 hlen hn 1 (by omega), entry_pre0 hlen hn 2 (by omega), if_neg h1, if_neg h2, hV,
      hmapN, hnzT (List.replicate (n - 1) O ++ [O']) hT0s,
      sf_ot (isOT_add hVot (isOT_omega hp'ot))]
  have hW := brelS_lhdE (brelS_omega hp'ot hpot hS)
  have hbW : bumpW M ρ g = omega (sumN (one :: Pl ++ [X])) := by
    unfold bumpW; rw [hmapM, hnzT [X] (by simp [hX])]
  have hE : LhdE (σ.v g) (ρ.v g) := by
    rw [ev', ev]
    apply v_strong hVot (single_omega hp'ot) (single_omega hpot) hW
    intro q hq hn' hlt'
    by_cases hWE : omega (sumN (one :: Pl ++ [X])) < E0
    · exact lhd_lt_small (isOT_mem_summands hVot hq) hWE hlt'
    · rw [← hbW]
      apply hAbs g h1 h2 (fun _ _ _ _ => v_z_of_e1 hC (by omega) he1) q hq _ (by rw [hbW]; exact hlt')
      intro hq2
      apply hn'
      have h2le : two ≤ sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O'])) :=
        two_le_sumN_one_cons (by simp) (fun t ht => by
          rcases List.mem_append.mp ht with h | h
          · exact hsP t h
          · exact hT0s t h)
      have hom : psi z two z ≤ omega (sumN (one :: Pl ++ (List.replicate (n - 1) O ++ [O']))) := by
        rw [← omega_small two_lt_E0]
        rcases (le_iff _ _).mp h2le with h' | h'
        · exact le_of_lt (omega_lt_omega isOT_two hp'ot h')
        · rw [h']
      exact lt_of_lt_of_le hq2 hom
  apply lhd_of_lhdE_lt hE
  rw [ev', ev]
  exact add_lt_add_left _ (omega_lt_omega hp'ot hpot hlt)

end


/-- **The children sum of the bump child `r` in `M.take x`** against the old one without `x`: the strong
relation, unless a child of `r` changes `o` with a non-`⊴` change of `v` (`hWk` excludes it). -/
theorem g0_drop_rel {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    (hKD : BumpKidsDec M ρ) (hWS : BumpWeakSrc M x ρ ρ')
    {g r : Nat} (h1 : entry M 1 g ≠ 0) (h2 : entry M 2 g ≠ 0)
    (hrM : r ∈ children M g) (hrb : col M r = bump M g) (hxr : x ∈ children M r)
    (hox : ρ.o x = one)
    (hIH : ∀ k ∈ children M r, k < x → PO ρ ρ' k ∧ PV M ρ ρ' k)
    (hWk : ∀ k ∈ children M r, k < x → ρ'.o k ≠ ρ.o k → LhdE (ρ'.v k) (ρ.v k)) :
    isOT (sumN ((children (M.take x) r).map ρ'.o)) = true ∧
      BRelS (sumN ((children (M.take x) r).map ρ'.o)) (sumN ((children (M.take x) r).map ρ.o)) := by
  obtain ⟨hs', hrel⟩ := g_level hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hKD hWS h1 h2 hrM hrb hIH
  have hot' : isOT (sumN ((children (M.take x) r).map ρ'.o)) = true :=
    isOT_sumN _ (fun t ht => (hs' t ht).1)
  refine ⟨hot', ?_⟩
  set l := children (M.take x) r with hl
  have hlM : ∀ c ∈ l, c ∈ children M r ∧ c < x := fun c hc => by
    rw [hl, children_take, List.mem_filter] at hc; exact ⟨hc.1, by simpa using hc.2⟩
  have hot : ∀ t ∈ l.map ρ.o, isOT t = true := fun t ht => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    exact hG.ot_o c (by have := (hlM c hc).2; omega)
  have hG0ot := isOT_sumN _ hot
  -- the full sum is `G0 + 1`
  have hfull : sumN ((children M r).map ρ.o) = app (sumN (l.map ρ.o)) one := by
    rw [children_split_x hx hxr, ← children_take, ← hl, List.map_append, List.map_singleton, hox, sumN_snoc,
      add_one_eq_app, sf_ot (by rw [← add_one_eq_app]; exact isOT_add hG0ot rfl)]
  -- `G0′ ≤ G0`
  have hle : sumN (l.map ρ'.o) ≤ sumN (l.map ρ.o) := by
    apply sumN_le2 _ (fun t ht => (hs' t ht).1) hot
    apply forall2_map_le
    intro c hc
    rcases (hIH c (hlM c hc).1 (hlM c hc).2).1.1 with h | ⟨⟨w', w, X, he', he, hw⟩, _⟩
    · exact h.le
    · rw [he', he]; exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl hw.1))
  rcases hrel with h | ⟨_, k, hk, w, _, _, hcase⟩
  · rw [hfull] at h
    exact brelS_untail h hle
  · rcases hcase with ⟨rfl, hxonly⟩ | ⟨hkx, hne, hnl⟩
    · have hnil : l = [] := by
        rw [hl, children_take, hxonly]; simp
      rw [hnil]; exact brelS_refl
    · exact absurd (hWk k hk hkx hne) hnl

end Ytosk
