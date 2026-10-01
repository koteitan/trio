/-
**3 行・t = 1・q ≠ r: v の枠の局所条件 VLocal と始点の下限を不変条件から。**

- 値の不変条件: TPLo（すべての o で低い部分が空のまま、TPL より強い）、AbsD（のりしろの枠で v(P_1 i) が
  W と fsD(W, ψ_μ(Ω_{μ+1})) に吸収される）、AbsU（上げの枠の吸収）。SRO より下の L9 網羅で例外 0。
- D の v の列の形（`dv_shape`、構造だけから）。のりしろの枠の ζ によらないデータ（`bump_data`）。
- VLocal を使わない穴・共終数の追跡（`t1_hole0`・`t1_cof0`）、b_r（`hcb_of_cof`・`last_br_of_cof`）。
- ζ の鎖は ω 冪の不動点（`gamS_fix`）。ω 冪と fsD の交換（`omega_fsD_hole`）。
- VLocal（`vlocal_t1`）。始点 ψ_μ(σ)（M.take x で r の子の v′ は μ より大きいので σ の加数は Ω_{μ+1} 以上、
  `seed_arg_ge`・`seed_fix`）。
- まとめ `t1_main_vloc`（`t1_main_tpl` から hV と始点の下限を外す）。
-/
import Ytosk.V3FrameT1

namespace Ytosk

open T

/-! ## 値の不変条件 -/

/-- The lower index `ψ_μ(Ω_{μ+1})` for the level `μ`. -/
def etaOm (μ : T) : T := psi μ (psi (succ μ) z z) z

/-- **Value invariant TPLo**: for every `o(c) = ψ_s(y)` whose argument has no part below `Ω_{s+1}` and ends
with `Ω_a` (`a` a limit with a hole), `Ω_{fsD(a, ψ_μ(Ω_{μ+1}))} ≥ Ω_{s+1}`
(SRO より下の L9 網羅で 2080 件、例外 0). -/
def TPLo (M : Mat) (ρ : Valn) : Prop :=
  ∀ c, c < M.length → ∀ s y, ρ.o c = psi s y z → (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a →
    ¬ psi (fsD a (etaOm (holeLev y))) z z < psi (succ s) z z

theorem TPL_of_TPLo {M : Mat} {ρ : Valn} (h : TPLo M ρ) : TPL M ρ := by
  intro i L c R hch s y hcv _ _ hl a hla hs hOa
  have hc : c ∈ children M i := by rw [hch]; simp
  exact h c (mem_children hc).2 s y hcv hl a hla hs hOa

/-- **Value invariant AbsD**: at a bump frame whose bump term `W` has a hole, `v(P_1 i)` is absorbed by
`W` and by `fsD(W, ψ_μ(Ω_{μ+1}))` (SRO より下の L9 網羅で 4861 枠、例外 0。SRO より上では崩れる例がある). -/
def AbsD (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → OHole (bumpW M ρ i) →
    add (vOpt ρ (par M 1 i)) (bumpW M ρ i) = bumpW M ρ i ∧
    add (vOpt ρ (par M 1 i)) (fsD (bumpW M ρ i) (etaOm (holeLev (bumpW M ρ i)))) =
      fsD (bumpW M ρ i) (etaOm (holeLev (bumpW M ρ i)))

/-- **Value invariant AbsU**: at an upgrade `i → k` with a hole in `v(k)`, the summands of `v(P_1 i)` below
`v(k)` stay below `fsD(v(k), ψ_μ(Ω_{μ+1}))` (SRO より下の L9 網羅で 161 件、例外 0). -/
def AbsU (M : Mat) (ρ : Valn) : Prop :=
  ∀ i k, upg M i = some k → OHole (ρ.v k) → ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < ρ.v k →
    q < fsD (ρ.v k) (etaOm (holeLev (ρ.v k)))

/-! ## D の v の列の形 -/

theorem mem_take_children {M : Mat} {x i c : Nat} (hc : c ∈ children M i) (hcx : c < x) :
    c ∈ children (M.take x) i := by
  rw [children_take, List.mem_filter]; exact ⟨hc, by simpa using hcx⟩

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) {q : Nat} (hq : par M 0 x = some q)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq

/-- No `o` in `D` below a child of `p` (a column with row 2 nonzero) that has a later child,
counting `x` as a later child of `q`. -/
theorem nodep_not_last {p d d' : Nat} (h2 : entry M 2 p ≠ 0) (hd : d ∈ children M p)
    (hd' : d' ∈ children M p) (hdd : d < d') {b : Bool} {e : Nat} (hD : DepX M x b e)
    (hde : Anc0 M d e) : False := by
  have hd'l := (mem_children hd').2
  rcases Nat.lt_or_ge d' x with hd'x | hd'x
  · exact chg_only_last hx hR0 hZ2 hSD hZ1 hUAT hUAB h2 hd (mem_take_children hd' hd'x) hdd
      (depX_chgX hD) hde
  · have hd'e : d' = x := by omega
    subst hd'e
    have hpq : p = q := by
      rw [(mem_children_iff.mp hd').2] at hq; exact Option.some.inj hq
    subst hpq
    exact nodep_sib hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq (Anc0.refl d') (fun h => absurd h (lt_irrefl _))
      _ d (Nat.le_refl _) hd hdd b e hD hde

/-- **The shape of a `v` call in `D`.** -/
theorem dv_shape {i : Nat} (hi : i < x) (hv : DepX M x false i) :
    entry M 1 i ≠ 0 ∧ (∀ m, par M 1 i = some m → ¬ DepX M x false m) ∧
    ((entry M 2 i = 0 ∧ upg M i = some (i + 1) ∧ i + 1 < x ∧ DepX M x false (i + 1)) ∨
     (entry M 2 i ≠ 0 ∧ ∃ L K j k, children M i = L ++ [j] ∧ col M j = bump M i ∧
        children M j = K ++ [k] ∧ DepX M x true k ∧ (∀ d ∈ K, ¬ DepX M x true d) ∧
        (∀ d ∈ L, ∀ e ∈ children M d, e < x ∧ ¬ DepX M x true e))) := by
  have hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m := by
    intro m hp hdm
    have hmi := par_lt M 1 i m hp
    exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdm)).1 rfl (by omega) |>.2.2 i hi hp
  cases hv with
  | vpar h1 hp hdm => exact absurd hdm (hpd _ hp)
  | @vupg _ k h1 h2 hu hdk =>
    refine ⟨h1, hpd, Or.inl ⟨h2, ?_⟩⟩
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    rcases hcase with rfl | ⟨hA, hki⟩
    · refine ⟨hu, ?_, hdk⟩
      have := upg_succ_lt hu
      rcases Nat.lt_or_ge (i + 1) x with h | h
      · exact h
      · exfalso
        have hix : i + 1 = x := by omega
        rw [hix] at hu; exact upg_ne_e2z hu hx2
    · exact (no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB
        ((chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdk)).1 rfl (by omega)) (by omega)
        hu hA hki).elim
  | @vbump _ j k h1 h2 hj hjb hk hdk =>
    refine ⟨h1, hpd, Or.inr ⟨h2, ?_⟩⟩
    have hj2 : entry M 2 j ≠ 0 := by
      have := e2_of_col (show col M j = (entry M 0 i + 1, entry M 1 i, 1) from hjb); omega
    have hAjk : Anc0 M j k := Anc0.step (mem_children_iff.mp hk).2 (Anc0.refl j)
    -- `j` is the last child of `i`
    have hjmax : ∀ j' ∈ children M i, j' ≤ j := by
      intro j' hj'; by_contra hlt
      exact nodep_not_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq h2 hj hj' (by omega) hdk hAjk
    have hchi := split_last_max _ _ (children_sorted M i) hj hjmax
    -- `k` is the last child of `j`
    have hkmax : ∀ k' ∈ children M j, k' ≤ k := by
      intro k' hk'; by_contra hlt
      exact nodep_not_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hj2 hk hk' (by omega) hdk (Anc0.refl k)
    have hchj := split_last_max _ _ (children_sorted M j) hk hkmax
    refine ⟨_, _, j, k, hchi, hjb, hchj, hdk, ?_, ?_⟩
    · intro d hd hdD
      have hdM : d ∈ children M j := (List.mem_filter.mp hd).1
      have hdk' : d < k := by simpa using (List.mem_filter.mp hd).2
      exact nodep_not_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hj2 hdM hk hdk' hdD (Anc0.refl d)
    · intro d hd e he
      have hdM : d ∈ children M i := (List.mem_filter.mp hd).1
      have hdj : d < j := by simpa using (List.mem_filter.mp hd).2
      have hpe : par M 0 e = some d := (mem_children_iff.mp he).2
      have hAde : Anc0 M d e := Anc0.step hpe (Anc0.refl d)
      have hpj : par M 0 j = some i := (mem_children_iff.mp hj).2
      have hjx : j < x := by
        rcases Nat.lt_or_ge j x with h | h
        · exact h
        · exfalso
          have : j = x := by have := (mem_children hj).2; omega
          subst this
          have := e2_of_col (show col M j = (entry M 0 i + 1, entry M 1 i, 1) from hjb); omega
      have hej : e < j := by
        by_contra hge
        have hA := anc_between hAde j (by omega) (by omega)
        have := (anc0_par hA (by omega) hpj).le
        have := (mem_children hdM).1
        omega
      exact ⟨by omega, fun hD =>
        nodep_not_last hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq h2 hdM hj hdj hD hAde⟩

end

/-! ## のりしろの枠の ζ によらないデータ -/

/-- A single term with cofinality `Ω_{μ+1}` has subscript above `μ`. -/
theorem single_cof_big {s y μ : T} (hot : isOT (psi s y z) = true) (h : cof (psi s y z) = .big μ) :
    lt μ s = true := by
  by_cases hy : y = z
  · subst hy
    unfold cof at h
    rw [if_pos rfl] at h
    by_cases hs : s = z
    · rw [if_pos hs] at h; cases h
    · rw [if_neg hs] at h
      by_cases hss : isSucc s = true
      · rw [if_pos hss] at h; cases h; exact init_lt hs
      · rw [if_neg hss] at h; exact lt_of_cof_big (isOT_sub hot) h
  · exact (cof_psi_inv hy h).2

/-- **The head subscript of a standard term with cofinality `Ω_{μ+1}` is above `μ`.** -/
theorem head_sub_of_cof : ∀ {s b c μ : T}, isOT (psi s b c) = true → cof (psi s b c) = .big μ →
    lt μ s = true
  | s, b, z, μ, hot, h => single_cof_big hot h
  | s, b, psi c1 c2 c3, μ, hot, h => by
    have h' : cof (psi c1 c2 c3) = .big μ := by simpa [cof] using h
    have ih := head_sub_of_cof (isOT_rest hot) h'
    have h4 : psi c1 c2 z ≤ psi s b z := (isOT_psi_iff.mp hot).2.2.2.1
    show μ < s
    rcases (le_iff _ _).mp h4 with hl | he
    · rw [psi_lt_psi_z_iff] at hl
      rcases hl with hl | ⟨he, _⟩
      · exact lt_trans' ih hl
      · rw [← he]; exact ih
    · cases he; exact ih

theorem omega_z : omega z = one := by
  unfold omega; split <;> rfl

/-- The `ζ`-free data of a bump frame. -/
structure BumpData (M : Mat) (ρ : Valn) (μ : T) (i : Nat) (L K : List Nat) (j k : Nat) : Prop where
  sK : ∀ t ∈ K.map ρ.o ++ [ρ.o k], Single t
  pK : (K.map ρ.o ++ [ρ.o k]).Pairwise (fun a b => b ≤ a)
  sL : ∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t
  pp : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))]).Pairwise
      (fun a b => b ≤ a)
  gt : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))], one < t
  passG : ∀ s b c, sumN (K.map ρ.o ++ [ρ.o k]) = psi s b c →
      cof (sumN (K.map ρ.o ++ [ρ.o k])) = .big μ → lt μ s = true
  passP : ∀ s b c, app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [ρ.o k]))) =
        psi s b c →
      cof (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [ρ.o k])))) =
        .big μ → lt μ s = true
  W : bumpW M ρ i = omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
      (omega (sumN (K.map ρ.o ++ [ρ.o k]))))
  potW : isOT (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [ρ.o k])))) = true

/-- **The `ζ`-free data of a bump frame** from BumpKidsDec and BumpTermDec. -/
theorem bump_data {M : Mat} {ρ : Valn} {μ : T} {i j k : Nat} {L K : List Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hch : children M i = L ++ [j]) (hjb : col M j = bump M i) (hchj : children M j = K ++ [k]) :
    BumpData M ρ μ i L K j k := by
  have hj : j ∈ children M i := by rw [hch]; simp
  have hsK : ∀ t ∈ K.map ρ.o ++ [ρ.o k], Single t := by
    intro t ht
    have : t ∈ (children M j).map ρ.o := by rw [hchj, List.map_append]; simpa using ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp this
    exact single_o hC hG (mem_children hd).2
  have hpK : (K.map ρ.o ++ [ρ.o k]).Pairwise (fun a b => b ≤ a) := by
    have := hKD i h1 h2 j hj hjb
    rw [hchj, List.map_append] at this; simpa using this
  set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
  set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
  have hGot : isOT G = true := (sumN_dec _ hsK hpK).1
  have hGz : G ≠ z := by
    rw [hGdef, sumN_snoc_dec hsK hpK]
    intro he
    exact single_ne_z (hsK _ (List.mem_append_right _ (List.mem_singleton_self _))) (app_eq_z he).2
  have hsL : ∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t := by
    intro t ht
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp ht
    unfold bumpTerm
    split
    · right; apply single_omega; apply isOT_sumN
      intro u hu; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu; exact hG.ot_o d (mem_children hd).2
    · left; rfl
  have hbj : bumpTerm M ρ i j = omega G := by
    unfold bumpTerm; rw [if_pos hjb, hGdef, hchj, List.map_append]; rfl
  have hl : (children M i).map (bumpTerm M ρ i) = L.map (bumpTerm M ρ i) ++ [omega G] := by
    rw [hch, List.map_append, List.map_singleton, hbj]
  have hωG : Single (omega G) := single_omega hGot
  have hnz : nzs (L.map (bumpTerm M ρ i) ++ [omega G]) = P ++ [omega G] := by
    rw [nzs_append, nzs_single (single_ne_z hωG)]
  have hpp : (P ++ [omega G]).Pairwise (fun a b => b ≤ a) := by
    have := hTD i h1 h2; rw [hl, hnz] at this; exact this
  have hone : one < omega G := by
    rw [← omega_z]; exact omega_lt_omega rfl hGot (lt_of_le_of_ne (z_le G) (Ne.symm hGz))
  have hgt : ∀ t ∈ P ++ [omega G], one < t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact lt_of_lt_of_le hone ((List.pairwise_append.mp hpp).2.2 t ht _ (List.mem_singleton_self _))
    · rw [List.mem_singleton] at ht; rw [ht]; exact hone
  have hsP : ∀ t ∈ P ++ [omega G], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · simp only [hPdef, nzs, List.mem_filter] at ht
      rcases hsL t ht.1 with h | h
      · exact absurd h (by simpa using ht.2)
      · exact h
    · rw [List.mem_singleton] at ht; rw [ht]; exact hωG
  have hpot : isOT (app (sumN P) (omega G)) = true := by
    rw [← sumN_snoc_dec hsP hpp]; exact (sumN_dec _ hsP hpp).1
  have hsl : ∀ t ∈ L.map (bumpTerm M ρ i) ++ [omega G], t = z ∨ Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsL t ht
    · rw [List.mem_singleton] at ht; rw [ht]; exact Or.inr hωG
  refine ⟨hsK, hpK, hsL, hpp, hgt, ?_, ?_, ?_, hpot⟩
  · intro s b c he hc
    rw [← hGdef] at he hc
    rw [he] at hGot hc
    exact head_sub_of_cof hGot hc
  · intro s b c he hc
    rw [he] at hpot hc
    exact head_sub_of_cof hpot hc
  · unfold bumpW
    rw [hl, sumN_one_cons hsl (by rw [hnz]; exact hpp) (by rw [hnz]; exact hgt) (by rw [hnz]; simp),
      hnz, sumN_snoc_dec hsP hpp]

/-! ## VLocal を使わない穴の追跡 -/

/-- The hole of the bump term from the hole of `o(k)`. -/
theorem holeT_bumpW {M : Mat} {ρ : Valn} {μ br vr : T} {i j k : Nat} {L K : List Nat}
    (hBD : BumpData M ρ μ i L K j k) (hHk : HoleT μ br vr (ρ.o k)) :
    HoleT μ br vr (omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
      (omega (sumN (K.map ρ.o ++ [ρ.o k]))))) := by
  have hGot := (sumN_dec _ hBD.sK hBD.pK).1
  have hkS : Single (ρ.o k) := hBD.sK _ (List.mem_append_right _ (List.mem_singleton_self _))
  have hHG : HoleT μ br vr (sumN (K.map ρ.o ++ [ρ.o k])) := by
    rw [sumN_snoc_dec hBD.sK hBD.pK]; exact holeT_app _ (single_ne_z hkS) hHk
  have hHωG := holeT_omega hGot hHG hBD.passG
  exact holeT_omega hBD.potW (holeT_app _ (holeT_ne_z hHωG) hHωG) hBD.passP

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ br vr : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) {q : Nat} (hq : par M 0 x = some q)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAD : AbsD M ρ)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hAD

/-- **At a bump frame of `D`, `v(i)` is the bump term** (given the hole of `o(k)`). -/
theorem v_bump_D {i j k : Nat} {L K : List Nat} (hi : i < x) (h1 : entry M 1 i ≠ 0)
    (h2 : entry M 2 i ≠ 0) (hch : children M i = L ++ [j]) (hjb : col M j = bump M i)
    (hchj : children M j = K ++ [k]) (hHk : HoleT μ br vr (ρ.o k)) :
    BumpData M ρ μ i L K j k ∧
    ρ.v i = omega (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (sumN (K.map ρ.o ++ [ρ.o k])))) ∧
    HoleT μ br vr (ρ.v i) := by
  have hBD : BumpData M ρ μ i L K j k := bump_data hC hG hKD hTD h1 h2 hch hjb hchj
  have hHW := holeT_bumpW hBD hHk
  have hAbs := (hAD i (by omega) h1 h2 (by rw [hBD.W]; exact ohole_of_holeT hHW)).1
  rw [hBD.W] at hAbs
  have hvi := v_bump_value hC (by omega) h1 h2 hch hjb hchj hBD.sK hBD.pK hBD.sL hBD.pp hBD.gt hAbs
  exact ⟨hBD, hvi, by rw [hvi]; exact hHW⟩

variable (hrx : r < x) (hAr : Anc0 M r x) (hro : ρ.o r = psi vr br z)
  (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
  (hHx : HoleT μ br vr (ρ.o x))
  (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hS2 : ∀ i k, i ≤ r → DepX M x false i → entry M 2 i = 0 → upg M i = some k → k ≤ r)
  (hS3 : ∀ i j k, i ≤ r → j ∈ children M i → col M j = bump M i → k ∈ children M j →
    DepX M x true k → k ≤ r)
include hrx hAr hro hcb hμr hbr hHx hF1 hOS hS2 hS3

/-- **Hole and position without `VLocal`** (`t = 1`, `q ≠ r`). -/
theorem t1_hole0 :
    ∀ b i, DepX M x b i → (i < x ∨ (i = x ∧ b = true)) →
      HoleT μ br vr (valB ρ b i) ∧ DiagLe μ br vr r i (valB ρ b i) ∧
      (b = false → entry M 2 i ≠ 0 → Single (ρ.v i)) := by
  have hμ : ¬ lt μ vr = true := by rw [hμr]; exact lt_irrefl' _
  intro b i hD
  induction hD with
  | leaf =>
    intro _
    exact ⟨hHx, fun h => absurd h (by omega), fun h => nomatch h⟩
  | @ochild i c hc hcb' hcu hdc ih =>
    intro hix
    have hcM := (mem_children hc).2
    have hic := (mem_children hc).1
    have hi : i < x := by
      rcases hix with h | ⟨h, _⟩
      · exact h
      · omega
    have hcx : c ≤ x := by omega
    have hcpos : c < x ∨ (c = x ∧ true = true) := by
      rcases Nat.lt_or_ge c x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, rfl⟩
    obtain ⟨ihH, ihD, _⟩ := ih hcpos
    simp only [valB, cond_true] at ihH ihD
    refine ⟨?_, ?_, fun h => nomatch h⟩ <;>
    rcases hOS i hi (DepX.ochild hc hcb' hcu hdc) with ⟨_, hnc⟩ | ⟨hv, L, c', R, hch, hcb2, hcu2, hR, hLnd⟩
    all_goals first
      | exact absurd (hnc c hc) (by
          rintro (h | h)
          · exact hcb' h
          · exact hcu h)
      | skip
    all_goals
      have hcc : c = c' := by
        rw [hch] at hc
        rcases List.mem_append.mp hc with h | h
        · exact absurd hdc (hLnd c h ⟨hcb', hcu⟩)
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · rcases hR c h with h' | h'
            · exact absurd h' hcb'
            · exact absurd h' hcu
      subst hcc
      have hiM : i < M.length := by omega
      obtain ⟨s, y, hcv⟩ := o_psi_form hC hcM
      have hcot : isOT (psi s y z) = true := by rw [← hcv]; exact hG.ot_o c hcM
      have hframe := o_frame hC hG hiM hch hcb2 hcu2 hR hcM
      rw [hcv, spArg_single] at hframe
      rw [hcv] at ihH ihD
      have hpar : r < c → r ≤ i := fun h =>
        par0_ge_of_anc hAr h hcx (mem_children_iff.mp hc).2
      have hatr : i = r → ρ.v i = vr ∧ step (ρ.v i) (preState M ρ i L) s y z = br := by
        intro hir
        have h := hframe
        rw [hir, hro] at h
        rw [hir]
        exact ⟨(T.psi.inj h).1.symm, (T.psi.inj h).2.1.symm⟩
    · have hpass : cof (psi s y z) = .big μ →
          lt μ (ρ.v i) = true ∨ (ρ.v i = vr ∧ step (ρ.v i) (preState M ρ i L) s y z = br) := by
        intro hcof
        have hrc : r < c := by
          by_contra h
          obtain ⟨a', _, hDc⟩ := ihD (by omega)
          exact DiagAt.cof_ne hDc hcof
        rcases Nat.eq_or_lt_of_le (hpar hrc) with h | h
        · exact Or.inr (hatr h.symm)
        · exact Or.inl (hF1 i h hi (DepX.ochild hc hcb' hcu hdc) hv)
      show HoleT μ br vr (ρ.o i)
      rw [hframe]
      exact holeT_oframe hcot ihH hμr hbr hcb hpass
    · intro hir
      show ∃ a', ¬ lt vr a' = true ∧ DiagAt a' br μ (ρ.o i)
      by_cases hcr : c ≤ r
      · rw [hframe]
        exact diag_oframe hcot (ihD hcr) hμr hbr hcb
      · have hir' : i = r := le_antisymm hir (hpar (by omega))
        rw [hir', hro]
        exact ⟨vr, lt_irrefl' _, DiagAt.here hbr hcb hμ⟩
  | @ov i hv ih =>
    intro hix
    rcases hix with hi | ⟨rfl, _⟩
    · obtain ⟨ihH, ihD, _⟩ := ih (Or.inl hi)
      simp only [valB, cond_false] at ihH ihD
      rcases hOS i hi (DepX.ov hv) with ⟨_, hnc⟩ | ⟨hv', _⟩
      · have hoi := o_nocnt hC hG (by omega) hnc
        have hvz := holeT_ne_z ihH
        have hvs := holeT_not_succ ihH
        refine ⟨?_, ?_, fun h => nomatch h⟩
        · show HoleT μ br vr (ρ.o i)
          rw [hoi]; exact holeT_sub hvz hvs ihH
        · intro hir
          show ∃ a', ¬ lt vr a' = true ∧ DiagAt a' br μ (ρ.o i)
          obtain ⟨a', ha', hDv⟩ := ihD hir
          rw [hoi]; exact ⟨a', ha', DiagAt.sub (DiagAt.ne_z hDv) (DiagAt.not_succ hDv) hDv⟩
      · exact absurd hv hv'
    · exact ⟨hHx, fun h => absurd h (by omega), fun h => nomatch h⟩
  | @vpar i m' h1 hp hdm _ =>
    intro hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    exact absurd hdm ((dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi (DepX.vpar h1 hp hdm)).2.1 m' hp)
  | @vupg i k h1 h2 hu hdk ih =>
    intro hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    obtain ⟨_, _, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi (DepX.vupg h1 h2 hu hdk)
    rcases hcase with ⟨_, hu', hk, _⟩ | ⟨h2', _⟩
    · have hkk : k = i + 1 := by rw [hu] at hu'; exact Option.some.inj hu'
      obtain ⟨ihH, ihD, ihS⟩ := ih (Or.inl (by omega))
      simp only [valB, cond_false] at ihH ihD
      have hk2 : entry M 2 k ≠ 0 := by have := upg_target_e2 hu; omega
      have hVs := ihS rfl hk2
      obtain ⟨B, hvi⟩ := upg_val hC (by omega) h1 h2 hu hVs (vOpt_ot hG (by omega))
      have hkz := holeT_ne_z ihH
      refine ⟨?_, ?_, fun _ h => absurd h2 h⟩
      · show HoleT μ br vr (ρ.v i)
        rw [hvi]; exact holeT_app B hkz ihH
      · intro hir
        show ∃ a', ¬ lt vr a' = true ∧ DiagAt a' br μ (ρ.v i)
        obtain ⟨a', ha', hDk⟩ := ihD (hS2 i k hir (DepX.vupg h1 h2 hu hdk) h2 hu)
        rw [hvi]; exact ⟨a', ha', DiagAt.append B hkz hDk⟩
    · exact absurd h2 h2'
  | @vbump i j k h1 h2 hj hjb hk hdk ih =>
    intro hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    obtain ⟨_, _, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi (DepX.vbump h1 h2 hj hjb hk hdk)
    rcases hcase with ⟨h2', _⟩ | ⟨_, L, K, j', k', hch, hjb', hchj, _, hKnd, hLnd⟩
    · exact absurd h2' h2
    · have hjj : j = j' := by
        rw [hch] at hj
        rcases List.mem_append.mp hj with h | h
        · exact absurd hdk (hLnd j h k hk).2
        · exact List.mem_singleton.mp h
      subst hjj
      have hkk : k = k' := by
        rw [hchj] at hk
        rcases List.mem_append.mp hk with h | h
        · exact absurd hdk (hKnd k h)
        · exact List.mem_singleton.mp h
      subst hkk
      have hkpos : k < x ∨ (k = x ∧ true = true) := by
        have := (mem_children hk).2
        rcases Nat.lt_or_ge k x with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, rfl⟩
      obtain ⟨ihH, ihD, _⟩ := ih hkpos
      simp only [valB, cond_true] at ihH ihD
      obtain ⟨hBD, hvi, hHv⟩ := v_bump_D hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hAD hi h1 h2
        hch hjb hchj ihH
      refine ⟨hHv, ?_, fun _ _ => by rw [hvi]; exact single_omega hBD.potW⟩
      intro hir
      show ∃ a', ¬ lt vr a' = true ∧ DiagAt a' br μ (ρ.v i)
      obtain ⟨a', ha', hDk⟩ := ihD (hS3 i j k hir hj hjb hk hdk)
      rw [hvi]
      have hGot := (sumN_dec _ hBD.sK hBD.pK).1
      have hkS : Single (ρ.o k) := hBD.sK _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hDG : DiagAt a' br μ (sumN (K.map ρ.o ++ [ρ.o k])) := by
        rw [sumN_snoc_dec hBD.sK hBD.pK]; exact DiagAt.append _ (single_ne_z hkS) hDk
      have hωGz : omega (sumN (K.map ρ.o ++ [ρ.o k])) ≠ z := single_ne_z (single_omega hGot)
      exact ⟨a', ha', diag_omega hBD.potW (DiagAt.append _ hωGz (diag_omega hGot hDG))⟩

end

/-! ## ζ の鎖は ω 冪の不動点 -/

theorem summ_ge_of_cof : ∀ {t μ : T}, isOT t = true → cof t = .big μ →
    ∀ q ∈ summands t, ¬ q < psi (succ μ) z z
  | z, _, _, h => by simp [cof] at h
  | psi a b (psi c d e), μ, hot, h => by
    intro q hq
    simp only [summands, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact not_lt_of_ge (om_le_head_of_cof hot h)
    · exact summ_ge_of_cof (isOT_rest hot) (by simpa [cof] using h) q (by simpa [summands] using hq)
  | psi a b z, μ, hot, h => by
    intro q hq
    simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
    subst hq
    exact not_lt_of_ge (om_le_head_of_cof hot h)

/-- **Every summand of `fs t η` is at least `Ω_{μ+1}`** (unless `t` ends with `Ω_{μ+1}`). -/
theorem summ_fs_ge : ∀ {t μ η : T}, isOT t = true → cof t = .big μ → last t ≠ psi (succ μ) z z →
    μ < η → ∀ q ∈ summands (fs t η), ¬ q < psi (succ μ) z z
  | z, _, _, _, h, _, _ => by simp [cof] at h
  | psi a b (psi c d e), μ, η, hot, h, hl, hη => by
    intro q hq
    have hfs : fs (psi a b (psi c d e)) η = psi a b (fs (psi c d e) η) := rfl
    rw [hfs] at hq
    simp only [summands, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact not_lt_of_ge (om_le_head_of_cof hot h)
    · exact summ_fs_ge (isOT_rest hot) (by simpa [cof] using h) hl hη q hq
  | psi a b z, μ, η, hot, h, hl, hη => by
    have hge := om_le_fs hot h hl hη
    have hsingle : ∃ s y, fs (psi a b z) η = psi s y z := by
      unfold cof at h
      by_cases hb : b = z
      · subst hb
        rw [if_pos rfl] at h
        by_cases ha : a = z
        · rw [if_pos ha] at h; cases h
        · rw [if_neg ha] at h
          by_cases hs : isSucc a = true
          · rw [if_pos hs] at h; cases h
            exfalso; apply hl
            show psi a z z = _
            have : succ (init a) = a := by unfold succ; exact init_app_one hs
            rw [this]
          · unfold fs; rw [if_pos rfl, if_neg ha, if_neg hs]; exact ⟨_, _, rfl⟩
      · rw [if_neg hb] at h
        by_cases hs : isSucc b = true
        · rw [if_pos hs] at h; cases h
        · rw [if_neg hs] at h
          cases hcb : cof b with
          | big μ' =>
            rw [hcb] at h; simp only at h
            split at h
            · rename_i hlt
              unfold fs; rw [if_neg hb, if_neg hs, hcb]; simp only; rw [if_pos hlt]; exact ⟨_, _, rfl⟩
            · cases h
          | zero => rw [hcb] at h; cases h
          | succ => rw [hcb] at h; cases h
          | omega => rw [hcb] at h; cases h
    obtain ⟨s', y', he⟩ := hsingle
    intro q hq
    rw [he] at hq hge
    simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
    subst hq
    exact not_lt_of_ge hge

/-- **The terms of the chain are fixed points of `ω`** (given the seed is). -/
theorem gamS_fix {μ br vr seed : T} (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ)
    (hμ : ¬ lt μ vr = true) (hS : SeedOK vr br μ seed) (hbrl : last br ≠ psi (succ μ) z z)
    (hseedfix : omega seed = seed) (hseedΩ : etaOm μ ≤ seed) :
    ∀ m, omega (gamS μ br seed m) = gamS μ br seed m
  | 0 => hseedfix
  | m + 1 => by
    have hot := gamS_ot hrot hcb hμ hS (m + 1)
    have hΩ := gamS_ge_omfix (isOT_arg hrot) hcb hbrl hseedΩ (m + 1)
    have hlt : μ < gamS μ br seed m :=
      lt_of_lt_of_le (sub_lt μ _ z) (gamS_ge_omfix (isOT_arg hrot) hcb hbrl hseedΩ m)
    show omega (psi μ (fs br (gamS μ br seed m)) z) = psi μ (fs br (gamS μ br seed m)) z
    apply omega_fix_nolo hot
    · intro hE
      have h1 : psi μ (psi (succ μ) z z) z ≤ psi μ (fs br (gamS μ br seed m)) z := hΩ
      have h2 : psi (succ μ) z z ≤ fs br (gamS μ br seed m) := by
        rcases (le_iff _ _).mp h1 with h | h
        · rw [psi_lt_psi_z_iff] at h
          rcases h with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact le_of_lt h
        · rw [(T.psi.inj h).2.1]
      obtain ⟨hμz, hX⟩ := below_E0 hE
      have h3 : psi (succ μ) z z = Om one := by rw [hμz]; rfl
      rw [h3] at h2
      exact lt_irrefl' _ (lt_of_le_of_lt h2 hX)
    · unfold loOf
      apply split_snd_z_of_ge
      exact summ_fs_ge (isOT_arg hrot) hcb hbrl hlt

/-! ## ω 冪と fsD の交換 -/

theorem isSucc_psi_z {u v : T} (h : u ≠ z ∨ v ≠ z) : isSucc (psi u v z) = false := by
  unfold isSucc last one
  rcases h with h | h
  · simp [h]
  · simp [h]

theorem holeT_sub_inv {μ br vr a : T} (ha : isSucc a = false) (h : HoleT μ br vr (psi a z z)) :
    HoleT μ br vr a := by
  rcases h with h | ⟨a', ha', hD⟩
  · left
    have haz : a ≠ z := by intro he; subst he; simp [cof] at h
    unfold cof at h; rw [if_pos rfl, if_neg haz, if_neg (by rw [ha]; simp)] at h; exact h
  · right; refine ⟨a', ha', ?_⟩
    cases hD with
    | here hb _ _ => exact absurd rfl hb
    | arg hb _ _ => exact absurd rfl hb
    | sub _ _ h => exact h

/-- **`fsD` of a term with a hole is not a successor** (for `ζ = ψ_μ(X)`, `X ≠ 0`). -/
theorem fsD_not_succ_of_holeT {μ br vr ζ X : T} (hcb : cof br = .big μ) (hζ : ζ = psi μ X z)
    (hX : X ≠ z) : ∀ {t : T}, HoleT μ br vr t → isSucc (fsD t ζ) = false
  | z, h => absurd rfl (holeT_ne_z h)
  | psi a b (psi c d e), h => by
    have hr := holeT_rest (by simp) h
    show isSucc (psi a b (fsD (psi c d e) ζ)) = false
    have hζz : ζ ≠ z := by rw [hζ]; simp
    rw [isSucc_psi_rest _ _ _ (fsD_ne_z_of_holeT hζz hr)]
    exact fsD_not_succ_of_holeT hcb hζ hX hr
  | psi a b z, h => by
    have hζz : ζ ≠ z := by rw [hζ]; simp
    by_cases hb : b = z
    · subst hb
      have haz : a ≠ z := by
        intro he; subst he
        have := holeT_not_succ h; rw [show isSucc (psi z z z) = true from rfl] at this; cases this
      by_cases hs : isSucc a = true
      · rw [fsD_leaf hs haz, hζ]; exact isSucc_psi_z (Or.inr hX)
      · have hns : isSucc a = false := by simpa using hs
        rw [fsD_sub haz hns]
        exact isSucc_psi_z (Or.inl (fsD_ne_z_of_holeT hζz (holeT_sub_inv hns h)))
    · rw [fsD_psi hb (not_succ_arg_of_holeT hb h)]
      exact isSucc_psi_z (Or.inr (fsD_ne_z_of_holeT hζz (holeT_arg hb h hcb)))

/-- A nonzero term with no part below the single `θ` is not below `θ`. -/
theorem not_lt_of_lo_z {t θ : T} (ht : t ≠ z) (hl : (split t θ).2 = z) : ¬ t < θ := by
  have e := split_app θ t
  rw [hl, app_z_right] at e
  have hh : head t ∈ summands (split t θ).1 := by
    rw [e]; cases t with
    | z => exact absurd rfl ht
    | psi a b c => simp [head, summands]
  have h1 := split_fst_ge θ t _ hh
  intro hlt
  exact h1 (lt_of_le_of_lt (head_le_self t) hlt)

/-- **`ω` commutes with `fsD`** for a standard term with a hole, when `ζ` is a fixed point of `ω` at
least `ψ_μ(Ω_{μ+1})` and the low part of a single term stays empty (TPL). -/
theorem omega_fsD_hole {μ br vr Y ζ X : T} (hY : isOT Y = true) (hH : HoleT μ br vr Y)
    (hcb : cof br = .big μ) (hbrl : last br ≠ psi (succ μ) z z)
    (hζ : ζ = psi μ X z) (hXz : X ≠ z) (hζfix : omega ζ = ζ) (hζΩ : etaOm μ ≤ ζ)
    (hok : ∀ t, isOT t = true → HoleT μ br vr t → isOT (fsD t ζ) = true ∧ fsD t ζ < t)
    (hTPLY : ∀ s b, Y = psi s b z → (split b (psi (succ s) z z)).2 = z → ∀ a, last b = psi a z z →
      isSucc a = false → OHole a → ¬ psi (fsD a (etaOm μ)) z z < psi (succ s) z z) :
    fsD (omega Y) ζ = omega (fsD Y ζ) := by
  have hζz : ζ ≠ z := by rw [hζ]; simp
  have hYz := holeT_ne_z hH
  have hYs := holeT_not_succ hH
  obtain ⟨hYot', hYlt⟩ := hok Y hY hH
  by_cases hE : Y < E0
  · rw [omega_small hE, fsD_psi hYz hYs, omega_small (lt_trans hYlt hE)]
  cases Y with
  | z => exact absurd rfl hYz
  | psi s b c =>
    by_cases hc : c = z
    · subst hc
      have hθ : psi (succ s) z z = psi (succ s) z z := rfl
      by_cases hlo : loOf s b = z
      · rw [omega_fix_nolo hY hE hlo]
        symm
        by_cases hb : b = z
        · subst hb
          have hsz : s ≠ z := by
            intro he; subst he; rw [show isSucc (psi z z z) = true from rfl] at hYs; cases hYs
          by_cases hs : isSucc s = true
          · rw [fsD_leaf hs hsz]; exact hζfix
          · have hns : isSucc s = false := by simpa using hs
            have hHs := holeT_sub_inv hns hH
            rw [fsD_sub hsz hns] at hYot' ⊢
            apply omega_fix_nolo hYot'
            · intro hE'; exact fsD_ne_z_of_holeT hζz hHs (below_E0 hE').1
            · rfl
        · have hHb := holeT_arg hb hH hcb
          have hbs := not_succ_arg_of_holeT hb hH
          rw [fsD_psi hb hbs] at hYot' ⊢
          have hlo' := lo_keep_of_TPL (hTPLY s b rfl) hb hH hcb hbrl hζΩ hlo
          apply omega_fix_nolo hYot'
          · intro hE'
            obtain ⟨hsz, hlt⟩ := below_E0 hE'
            subst hsz
            exact not_lt_of_lo_z (fsD_ne_z_of_holeT hζz hHb) hlo' hlt
          · exact hlo'
      · -- the low part survives
        have hb : b ≠ z := by intro he; subst he; exact hlo rfl
        have hHb := holeT_arg hb hH hcb
        have hbs := not_succ_arg_of_holeT hb hH
        have hfx : fsD (psi s b z) ζ = psi s (fsD b ζ) z := fsD_psi hb hbs ζ
        have e := split_app (psi (succ s) z z) b
        set hi := (split b (psi (succ s) z z)).1 with hhi
        set lo := (split b (psi (succ s) z z)).2 with hlodef
        have hlo0 : lo ≠ z := hlo
        have hbot : isOT b = true := isOT_arg hY
        have hloot : isOT lo = true := isOT_app_right (by rw [e]; exact hbot)
        have hHlo : HoleT μ br vr lo := holeT_app_inv hlo0 (by rw [e]; exact hHb)
        have hfb : fsD b ζ = app hi (fsD lo ζ) := by
          conv => lhs; rw [← e]
          exact fsD_app hi hlo0 ζ
        have hflt : head (fsD lo ζ) < psi (succ s) z z := by
          have h1 := (hok lo hloot hHlo).2
          have h2 : head lo < psi (succ s) z z := split_snd_head_lt hlo0
          have h3 : lo < psi (succ s) z z := by
            cases hlc : lo with
            | z => exact absurd hlc hlo0
            | psi a' b' c' =>
              rw [hlc] at h2
              exact lt_of_head_lt h2
          exact lt_of_le_of_lt (head_le_self _) (lt_trans h1 h3)
        have hsplit : split (fsD b ζ) (psi (succ s) z z) = (hi, fsD lo ζ) := by
          rw [hfb]; exact split_app_of (split_fst_ge _ b) (Or.inr hflt)
        apply omega_fsD_lo hY hE hlo hfx (by rw [← hfx]; exact hYot')
        · intro hE'
          obtain ⟨hsz, hlt⟩ := below_E0 hE'
          subst hsz
          apply hE
          -- `Y ≥ E0` forces a summand of `b` at least `Ω_1`, which `fsD b ζ` keeps
          exfalso
          have hhiz : hi ≠ z := by
            intro hz
            rw [hz] at e
            simp only [app] at e
            have h3 : b < psi (succ z) z z := by
              rw [← e]
              cases hlc : lo with
              | z => exact absurd hlc hlo0
              | psi a' b' c' =>
                have h2 : head lo < psi (succ z) z z := split_snd_head_lt hlo0
                rw [hlc] at h2
                exact lt_of_head_lt h2
            apply hE
            unfold E0; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h3⟩
          have hhi1 : ¬ hi < psi (succ z) z z := not_lt_of_lo_z hhiz (by
            rw [hhi]
            have := split_app_of (t := psi (succ z) z z) (B := hi) (X := z) (split_fst_ge _ b)
              (Or.inl rfl)
            rw [app_z_right] at this
            rw [this])
          apply hhi1
          exact lt_of_le_of_lt (le_app_self hi _) (by rw [← hfb]; exact hlt)
        · unfold hiOf; rw [hsplit]
        · unfold loOf; rw [hsplit]; exact fsD_ne_z_of_holeT hζz hHlo
        · exact hYs
    · have hHc := holeT_rest hc hH
      have hfx : fsD (psi s b c) ζ = psi s b (fsD c ζ) := by
        cases c with
        | z => exact absurd rfl hc
        | psi => rfl
      rw [hfx] at hYot'
      exact omega_fsD_rest hY hE hc (holeT_not_succ hHc) hYot' (fsD_ne_z_of_holeT hζz hHc)
        (fsD_not_succ_of_holeT hcb hζ hXz hHc)

/-! ## 組み立ての部品 -/

theorem add_absorb_mono {v Y Y' : T} (h : add v Y = Y) (hle : Y ≤ Y') (hY : ∃ s y, Y = psi s y z)
    (hY' : ∃ s y, Y' = psi s y z) : add v Y' = Y' := by
  obtain ⟨s, y, rfl⟩ := hY
  obtain ⟨s', y', rfl⟩ := hY'
  cases v with
  | z => rfl
  | psi a b c =>
    simp only [add] at h ⊢
    split at h
    · rename_i hlt
      have : lt (psi a b z) (psi s' y' z) = true := lt_of_lt_of_le hlt hle
      rw [if_pos this]
    · exfalso
      have h3 := (T.psi.inj h).2.2
      exact add_ne_z_right c (by simp) h3

theorem app_single_ne {P c s b : T} (hP : P ≠ z) (hc : c ≠ z) : app P c ≠ psi s b z := by
  cases P with
  | z => exact absurd rfl hP
  | psi a b' c' =>
    rw [app_psi]; intro h
    exact hc (app_eq_z (T.psi.inj h).2.2).2

/-- **A single `ω^G` with no low part is `G` itself.** -/
theorem omega_single_nolo {G s b : T} (hG : isOT G = true) (hGz : G ≠ z) (h : omega G = psi s b z)
    (hl : (split b (psi (succ s) z z)).2 = z) : omega G = G := by
  by_cases hE : G < E0
  · exfalso
    rw [omega_small hE] at h
    obtain ⟨rfl, rfl, _⟩ := T.psi.inj h
    have hlt : head G < psi (succ z) z z := by
      have h1 := lt_of_le_of_lt (head_le_self G) hE
      exact lt_trans h1 (by unfold E0; rw [T.psi_lt_psi]; exact Or.inl (T.z_lt_psi _ _ _))
    have := split_app_of (t := psi (succ z) z z) (B := z) (X := G)
      (fun q hq => by simp [summands] at hq) (Or.inr hlt)
    simp only [app] at this
    rw [this] at hl; exact hGz hl
  · cases G with
    | z => exact absurd rfl hGz
    | psi s0 b0 c0 =>
      have hθ : head (psi s0 b0 c0) < psi (succ s0) z z := by
        show psi s0 b0 z < psi (succ s0) z z
        rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self s0)
      rw [omega_big' hG hE] at h
      obtain ⟨rfl, rfl, _⟩ := T.psi.inj h
      by_cases hlo : loOf s0 b0 = z
      · rw [if_pos hlo] at hl
        by_cases hc : c0 = z
        · subst hc; exact omega_fix_nolo hG hE hlo
        · exfalso
          have hc0 : head c0 < psi (succ s0) z z := by
            have h4 : head c0 ≤ psi s0 b0 z := (isOT_psi_iff.mp hG).2.2.2.1
            exact lt_of_le_of_lt h4 hθ
          have := split_app_of (t := psi (succ s0) z z) (split_fst_ge _ b0) (Or.inr hc0)
          unfold hiOf at hl; rw [this] at hl; exact hc hl
      · exfalso
        rw [if_neg hlo] at hl
        have := split_app_of (t := psi (succ s0) z z) (split_fst_ge _ b0) (Or.inr hθ)
        unfold hiOf at hl; rw [this] at hl; cases hl

/-- `fsD` of a single term with a hole is single (for a single index). -/
theorem fsD_single_of_holeT {μ br vr t η : T} (hH : HoleT μ br vr t) (ht : ∃ s y, t = psi s y z)
    (hη : ∃ s y, η = psi s y z) : ∃ s y, fsD t η = psi s y z := by
  obtain ⟨a, b, rfl⟩ := ht
  by_cases hb : b = z
  · subst hb
    have haz : a ≠ z := by
      intro he; subst he
      have := holeT_not_succ hH; rw [show isSucc (psi z z z) = true from rfl] at this; cases this
    by_cases hs : isSucc a = true
    · rw [fsD_leaf hs haz]; exact hη
    · rw [fsD_sub haz (by simpa using hs)]; exact ⟨_, _, rfl⟩
  · rw [fsD_psi hb (not_succ_arg_of_holeT hb hH)]; exact ⟨_, _, rfl⟩

/-! ## VLocal -/

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ br vr ζ X : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) {q : Nat} (hq : par M 0 x = some q)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAD : AbsD M ρ)
  (hrx : r < x) (hAr : Anc0 M r x) (hro : ρ.o r = psi vr br z)
  (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
  (hHx : HoleT μ br vr (ρ.o x))
  (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hS2 : ∀ i k, i ≤ r → DepX M x false i → entry M 2 i = 0 → upg M i = some k → k ≤ r)
  (hS3 : ∀ i j k, i ≤ r → j ∈ children M i → col M j = bump M i → k ∈ children M j →
    DepX M x true k → k ≤ r)
  (hTPLo : TPLo M ρ) (hAU : AbsU M ρ) (hbrl : last br ≠ psi (succ μ) z z)
  (hζ : ζ = psi μ X z) (hXz : X ≠ z) (hζfix : omega ζ = ζ) (hζΩ : etaOm μ ≤ ζ)
  (hok : ∀ t, isOT t = true → HoleT μ br vr t → isOT (fsD t ζ) = true ∧ fsD t ζ < t)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hAD hrx hAr hro hcb hμr hbr hHx hF1 hOS hS2 hS3
  hTPLo hAU hbrl hζ hXz hζfix hζΩ hok

/-- **`VLocal` on `D`** from the invariants. -/
theorem vlocal_t1 : ∀ i, i < x → DepX M x false i → VLocal M x ρ ζ μ i := by
  have hH := t1_hole0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hAD hrx hAr hro hcb hμr hbr hHx
    hF1 hOS hS2 hS3
  have hζz : ζ ≠ z := by rw [hζ]; simp
  intro i hi hv
  obtain ⟨h1, hpd, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hv
  refine ⟨h1, hpd, ?_⟩
  rcases hcase with ⟨h2, hu, hk, hdk⟩ | ⟨h2, L, K, j, k, hch, hjb, hchj, hdk, hKnd, hLnd⟩
  · -- the upgrade frame
    left
    obtain ⟨hHk, _, hSk⟩ := hH false (i + 1) hdk (Or.inl hk)
    simp only [valB, cond_false] at hHk
    have hk2 : entry M 2 (i + 1) ≠ 0 := by have := upg_target_e2 hu; omega
    have hVs := hSk rfl hk2
    have hkM : i + 1 < M.length := by omega
    refine ⟨i + 1, h2, hu, hk, hVs, ?_, ?_⟩
    · apply single_fsD hVs.2 (holeT_not_succ hHk)
        (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHk)) ⟨μ, X, hζ⟩
      exact (hok _ (hG.ot_v _ hkM) hHk).1
    · intro t ht hlt
      have hOk := ohole_of_holeT hHk
      have h0 := hAU i (i + 1) hu hOk t ht hlt
      rw [holeLev_holeT hHk] at h0
      exact lt_of_lt_of_le h0 (fsD_mono_eta hOk hζΩ)
  · -- the bump frame
    right
    have hkM : k < M.length := by
      have : k ∈ children M j := by rw [hchj]; simp
      exact (mem_children this).2
    obtain ⟨hHk, _, _⟩ := hH true k hdk (by
      rcases Nat.lt_or_ge k x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, rfl⟩)
    simp only [valB, cond_true] at hHk
    obtain ⟨hBD, _, _⟩ := v_bump_D hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hAD hi h1 h2
      hch hjb hchj hHk
    set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
    set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
    have hkS : Single (ρ.o k) := hBD.sK _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hGot : isOT G = true := (sumN_dec _ hBD.sK hBD.pK).1
    have hGe : G = app (sumN (K.map ρ.o)) (ρ.o k) := sumN_snoc_dec hBD.sK hBD.pK
    have hHG : HoleT μ br vr G := by rw [hGe]; exact holeT_app _ (single_ne_z hkS) hHk
    have hHωG := holeT_omega hGot hHG hBD.passG
    have hωGz : omega G ≠ z := holeT_ne_z hHωG
    have hHY2 : HoleT μ br vr (app (sumN P) (omega G)) := holeT_app _ hωGz hHωG
    have hHW := holeT_omega hBD.potW hHY2 hBD.passP
    -- `fsD(o(k), ζ)`
    obtain ⟨hfkot, hfklt⟩ := hok _ (hG.ot_o k hkM) hHk
    have hfkS : Single (fsD (ρ.o k) ζ) := by
      apply single_fsD (o_psi_form hC hkM) (holeT_not_succ hHk)
        (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHk)) ⟨μ, X, hζ⟩ hfkot
    have hfkz : fsD (ρ.o k) ζ ≠ z := single_ne_z hfkS
    set G' := sumN (K.map ρ.o ++ [fsD (ρ.o k) ζ]) with hG'def
    have hsK' : ∀ t ∈ K.map ρ.o ++ [fsD (ρ.o k) ζ], Single t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hBD.sK t (List.mem_append_left _ ht)
      · rw [List.mem_singleton] at ht; rw [ht]; exact hfkS
    have hpK' : (K.map ρ.o ++ [fsD (ρ.o k) ζ]).Pairwise (fun a b => b ≤ a) := by
      have hpK := hBD.pK
      rw [List.pairwise_append] at hpK ⊢
      refine ⟨hpK.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb; rw [hb]
      exact le_trans (le_of_lt hfklt) (hpK.2.2 a ha _ (List.mem_singleton_self _))
    have hG'ot : isOT G' = true := (sumN_dec _ hsK' hpK').1
    have hG'e : G' = app (sumN (K.map ρ.o)) (fsD (ρ.o k) ζ) := sumN_snoc_dec hsK' hpK'
    have hG'z : G' ≠ z := by rw [hG'e]; intro he; exact hfkz (app_eq_z he).2
    have hG'lt : G' < G := by rw [hG'e, hGe]; exact app_lt_app_left _ hfklt
    have hωle : omega G' ≤ omega G := le_of_lt (omega_lt_omega hG'ot hGot hG'lt)
    have hfG : fsD G ζ = G' := by rw [hGe, hG'e]; exact fsD_app _ (single_ne_z hkS) ζ
    -- TPL for `G` and for `P + ω^G`
    have hTG : ∀ s b, G = psi s b z → (split b (psi (succ s) z z)).2 = z → ∀ a, last b = psi a z z →
        isSucc a = false → OHole a → ¬ psi (fsD a (etaOm μ)) z z < psi (succ s) z z := by
      intro s b hGsb hl a hla has hOa
      have hK0 : sumN (K.map ρ.o) = z := by
        by_contra hK
        exact app_single_ne hK (single_ne_z hkS) (by rw [← hGe]; exact hGsb)
      have hok' : ρ.o k = psi s b z := by rw [← hGsb, hGe, hK0]; rfl
      have hb : b ≠ z := by
        intro hb0; rw [hb0] at hla; simp [last] at hla
      have hHb := holeT_arg hb (by rw [← hok']; exact hHk) hcb
      have := hTPLo k hkM s b hok' hl a hla has hOa
      rwa [holeLev_holeT hHb] at this
    have hTY2 : ∀ s b, app (sumN P) (omega G) = psi s b z → (split b (psi (succ s) z z)).2 = z →
        ∀ a, last b = psi a z z → isSucc a = false → OHole a →
        ¬ psi (fsD a (etaOm μ)) z z < psi (succ s) z z := by
      intro s b hY hl
      have hP0 : sumN P = z := by
        by_contra hP; exact app_single_ne hP hωGz hY
      rw [hP0] at hY
      have hY' : omega G = psi s b z := hY
      have hfix := omega_single_nolo hGot (holeT_ne_z hHG) hY' hl
      exact hTG s b (by rw [← hfix]; exact hY') hl
    have hωGfs : fsD (omega G) ζ = omega G' := by
      rw [omega_fsD_hole hGot hHG hcb hbrl hζ hXz hζfix hζΩ hok hTG, hfG]
    have hωp : fsD (omega (app (sumN P) (omega G))) ζ = omega (app (sumN P) (omega G')) := by
      rw [omega_fsD_hole hBD.potW hHY2 hcb hbrl hζ hXz hζfix hζΩ hok hTY2,
        fsD_app _ hωGz ζ, hωGfs]
    -- absorption
    have hOW : OHole (bumpW M ρ i) := by rw [hBD.W]; exact ohole_of_holeT hHW
    obtain ⟨hA1, hA2⟩ := hAD i (by omega) h1 h2 hOW
    rw [hBD.W] at hA1 hA2
    rw [holeLev_holeT hHW] at hA2
    have hsW' : ∃ s y, omega (app (sumN P) (omega G')) = psi s y z := omega_single _
    refine ⟨L, K, j, k, h2, hch, hjb, hchj, hKnd, hLnd, hfkS, hBD.sK, hBD.pK, hBD.sL, hBD.pp, ?_,
      hBD.gt, ?_, hωp, ?_, hBD.passG, hBD.passP⟩
    · -- pairwise with `ω^{G'}`
      have hpp := hBD.pp
      rw [List.pairwise_append] at hpp ⊢
      refine ⟨hpp.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb; rw [hb]
      exact le_trans hωle (hpp.2.2 a ha _ (List.mem_singleton_self _))
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hBD.gt t (List.mem_append_left _ ht)
      · rw [List.mem_singleton] at ht; rw [ht, ← omega_z]
        exact omega_lt_omega rfl hG'ot (lt_of_le_of_ne (z_le _) (Ne.symm hG'z))
    · intro Y hY
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hY
      rcases hY with rfl | rfl
      · exact hA1
      · rw [← hωp]
        exact add_absorb_mono hA2 (fsD_mono_eta (ohole_of_holeT hHW) hζΩ)
          (fsD_single_of_holeT hHW (omega_single _) ⟨μ, _, rfl⟩)
          (by rw [hωp]; exact hsW')

end

/-! ## 始点: 引数の加数はどれも Ω_{μ+1} 以上 -/

/-- Every summand is at least `θ`. -/
def AllGeT (θ t : T) : Prop := ∀ q ∈ summands t, ¬ q < θ

theorem allGeT_z (θ : T) : AllGeT θ z := fun q hq => by simp [summands] at hq

theorem allGeT_add {θ : T} : ∀ {a b : T}, AllGeT θ a → AllGeT θ b → AllGeT θ (add a b)
  | z, b, _, hb => by simpa using hb
  | psi a1 b1 c1, b, ha, hb => by
    cases b with
    | z => simpa [add] using ha
    | psi d e f =>
      simp only [add]
      split
      · exact hb
      · intro q hq
        simp only [summands, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact ha _ (by simp [summands])
        · exact allGeT_add (a := c1) (fun q' hq' => ha q' (by simp [summands, hq'])) hb q hq

theorem allGeT_foldl {θ : T} : ∀ (l : List T) (acc : T), isOT acc = true → AllGeT θ acc →
    (∀ t ∈ l, isOT t = true ∧ AllGeT θ t) → AllGeT θ (l.foldl (fun a b => sf (add a b)) acc)
  | [], _, _, h, _ => h
  | t :: l, acc, hot, h, hl => by
    simp only [List.foldl_cons]
    have ht := hl t List.mem_cons_self
    have hot' : isOT (add acc t) = true := isOT_add hot ht.1
    apply allGeT_foldl l _ (by rw [sf_ot hot']; exact hot') (by rw [sf_ot hot']; exact allGeT_add h ht.2)
    exact fun u hu => hl u (List.mem_cons_of_mem _ hu)

theorem allGeT_cut {θ w y : T} (hot : isOT y = true) (hw : ¬ psi w z z < θ) :
    AllGeT θ (cut w y) := by
  rw [cut_eq_split w hot]
  intro q hq hlt
  exact split_fst_ge (psi w z z) y q hq (lt_of_lt_of_le hlt (le_of_not_gt hw))


theorem allGeT_H {θ s y : T} (hy : isOT y = true) (hsθ : ¬ psi s y z < θ) (hθ : ∃ m, θ = psi m z z) :
    AllGeT θ (H s y) := by
  unfold H
  obtain ⟨m, rfl⟩ := hθ
  have hs : ¬ s < m := by
    intro h; apply hsθ; rw [psi_lt_psi_z_iff]; exact Or.inl h
  have hw : ¬ psi (add s one) z z < psi m z z := by
    rw [psi_lt_psi_z_iff]
    rintro (h | ⟨h, _⟩)
    · exact hs (lt_trans (lt_add_principal z z s) h)
    · rw [← h] at hs; exact hs (lt_add_principal z z s)
  apply allGeT_add (allGeT_cut hy hw)
  simp only [sub]
  split
  · intro q hq
    simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rw [hq]; exact hsθ
  · exact allGeT_z _

theorem allGeT_step {θ a b s y c : T} (hb : AllGeT θ b) (hy : isOT y = true)
    (hsθ : ¬ psi s y z < θ) (hθ : ∃ m, θ = psi m z z) : AllGeT θ (step a b s y c) := by
  unfold step
  split
  · exact allGeT_H hy hsθ hθ
  · apply allGeT_add hb
    intro q hq
    simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rw [hq]; exact hsθ

theorem allGeT_spArg {θ a : T} (hθ : ∃ m, θ = psi m z z) : ∀ (c b : T), isOT c = true →
    AllGeT θ c → AllGeT θ b → AllGeT θ (spArg a b c)
  | z, b, _, _, hb => hb
  | psi s y c, b, hot, hc, hb => by
    rw [spArg_cons]
    apply allGeT_spArg hθ c _ (isOT_rest hot) (fun q hq => hc q (by simp [summands, hq]))
    exact allGeT_step hb (isOT_arg hot) (hc _ (by simp [summands])) hθ

theorem isOT_bumpTerm_of {M : Mat} {ρ : Valn} (hG : ∀ i, i < M.length → isOT (ρ.o i) = true)
    (i j : Nat) : isOT (bumpTerm M ρ i j) = true := by
  unfold bumpTerm
  split
  · apply isOT_omega; apply isOT_sumN
    intro t ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    exact hG c (mem_children hc).2
  · rfl

/-- `v` grows along `P_1` (standardness given only for the values). -/
theorem v_par1_lt_ot {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ)
    (hot : ∀ i, i < M.length → isOT (ρ.v i) = true) (hG : ∀ i, i < M.length → isOT (ρ.o i) = true)
    (hR : Rk M rk) : ∀ n i m, rk false i ≤ n → i < M.length → entry M 1 i ≠ 0 →
      par M 1 i = some m → ρ.v m < ρ.v i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i m hn hi h1 hp
  have hmi := par_lt M 1 i m hp
  have hvm := hot m (by omega)
  rw [(hC i hi).2]
  unfold vRhs
  rw [if_neg h1, hp]
  show ρ.v m < (if entry M 2 i = 0 then _ else _)
  split
  · rename_i h2
    cases hu : upg M i with
    | none => exact lt_sf_add_single hvm rfl ⟨z, z, rfl⟩
    | some k =>
      simp only
      obtain ⟨m', hm1, hm2, hcol, _⟩ := upg_spec hu
      rw [hp] at hm1
      cases hm1
      have hk := upg_lt_len hu
      have hkl : k < M.length := by have := upg_le hu; omega
      have he1 : entry M 1 k ≠ 0 := by rw [e1_of_col hcol]; exact h1
      have hrk := ((hR i hi).2.2 h1).2.1 h2 k hu
      have hvk := ih (rk false k) (by omega) k m (Nat.le_refl _) hkl he1 hm2
      have hkz : ρ.v k ≠ z := by
        intro h; rw [h] at hvk; exact T.not_lt_z _ hvk
      obtain ⟨s, y, hl⟩ := last_psi_form hkz
      exact lt_sf_add_single hvm (isOT_last (hot k hkl)) ⟨s, y, hl⟩
  · exact lt_sf_add_single hvm
      (isOT_omega (isOT_sumN _ (by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · rfl
        · obtain ⟨c, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm_of hG i c)))
      (omega_single _)


/-! ## 始点の性質 -/

/-- **Every child of `r` has a larger row 1 than `r`.** -/
theorem e1_child_r {M : Mat} {x r : Nat} (hx : x + 1 = M.length) (hR0 : R0P M) (hSD : SibDec M)
    (h1 : par M 1 x = some r) {c : Nat} (hc : c ∈ children M r) : entry M 1 r < entry M 1 c := by
  have hA := anc0_of_par M 1 r x h1
  have hrx : r ≠ x := by have := par_lt M 1 x r h1; omega
  obtain ⟨p, hpr, hpx⟩ := anc0_child hA hrx
  have hpl : p < M.length := by have := hpx.le; omega
  have hpM : p ∈ children M r := mem_children_iff.mpr ⟨hpl, hpr⟩
  have hp1 := e1_path_child h1 hA hrx hpr hpx
  have hpc : par M 0 c = some r := (mem_children_iff.mp hc).2
  have hrp := par_lt M 0 p r hpr
  have hcl := (mem_children hc).2
  rcases Nat.lt_trichotomy c p with hcp | rfl | hpc'
  · obtain ⟨L, R, hLR⟩ := List.append_of_mem hc
    obtain ⟨hL, _⟩ := sib_order (children_sorted M r) hLR
    have hpR : p ∈ R := by
      have : p ∈ L ++ c :: R := hLR ▸ hpM
      rcases List.mem_append.mp this with h | h
      · have := hL p h; omega
      · rcases List.mem_cons.mp h with h | h
        · omega
        · exact h
    have hle := sib_le hSD R L c hLR p hpR
    unfold colLe at hle
    have e0p : (col M p).1 = entry M 0 p := rfl
    have e1p : (col M p).2.1 = entry M 1 p := rfl
    have e0c : (col M c).1 = entry M 0 c := rfl
    have e1c : (col M c).2.1 = entry M 1 c := rfl
    rw [e0p, e1p, e0c, e1c] at hle
    have := hR0 p r hpr
    have := hR0 c r hpc
    omega
  · exact hp1
  · have hA' := anc_between hpx c (by omega) (by omega)
    have := (anc0_par hA' (by omega) hpc).le
    omega

/-- **The seed `ψ_μ(σ)`: `σ ≠ 0` and every summand of `σ` is at least `Ω_{μ+1}`.** -/
theorem seed_arg_ge {M : Mat} {x r : Nat} {ρ1 : Valn} {rk : Bool → Nat → Nat} {μ : T}
    (hx : x + 1 = M.length) (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAB : UAB M)
    (h1 : par M 1 x = some r) (hqr : par M 0 x ≠ some r)
    (hC1 : Cons (M.take x) ρ1) (hRk1 : Rk (M.take x) rk)
    (hotv : ∀ i, i < x → isOT (ρ1.v i) = true) (hoto : ∀ i, i < x → isOT (ρ1.o i) = true)
    (hv : ρ1.v r = μ) :
    ∃ σ, ρ1.o r = psi μ σ z ∧ σ ≠ z ∧ AllGeT (psi (succ μ) z z) σ := by
  have hrx : r < x := par_lt M 1 x r h1
  have hlen : (M.take x).length = x := by rw [List.length_take]; omega
  have hrT : r < (M.take x).length := by omega
  have hμot : isOT μ = true := by rw [← hv]; exact hotv r hrx
  -- the children of `r` in `M.take x` have subscripts above `μ`
  have hgt : ∀ c ∈ children (M.take x) r, μ < ρ1.v c := by
    intro c hc
    have hcM : c ∈ children M r := (List.mem_filter.mp (by rw [← children_take]; exact hc)).1
    have hcx : c < x := by
      have := (mem_children hc).2; omega
    have he := e1_child_r hx hR0 hSD h1 hcM
    have hpT : par (M.take x) 0 c = some r := by
      rw [par_take M 0 c hcx]; exact (mem_children_iff.mp hcM).2
    have he' : entry (M.take x) 1 r < entry (M.take x) 1 c := by
      rw [entry_take M 1 hrx, entry_take M 1 hcx]; exact he
    have hp1 := par1_of_child hpT he'
    rw [← hv]
    exact v_par1_lt_ot hC1 (fun i hi => hotv i (by omega)) (fun i hi => hoto i (by omega)) hRk1 _ c r
      (Nat.le_refl _) (by omega) (by omega) hp1
  -- the sum of the counted values
  set S := sumN ((children (M.take x) r).map (cnt (M.take x) ρ1 r)) with hSdef
  have hel : ∀ t ∈ (children (M.take x) r).map (cnt (M.take x) ρ1 r),
      isOT t = true ∧ AllGeT (psi (succ μ) z z) t := by
    intro t ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    have hcx : c < x := by have := (mem_children hc).2; omega
    rw [cnt_eq_ite]
    split
    · refine ⟨hoto c hcx, ?_⟩
      obtain ⟨σc, hσc⟩ := o_psi_sub hC1 (by omega : c < (M.take x).length)
      rw [hσc, sf_ot (hotv c hcx)]
      intro q hq
      simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rw [hq, psi_lt_psi_z_iff]
      rintro (h | ⟨_, h⟩)
      · exact lt_irrefl' _ (lt_of_lt_of_le (hgt c hc) (lt_succ_iff.mp h))
      · exact T.not_lt_z _ h
    · exact ⟨rfl, allGeT_z _⟩
  have hSot : isOT S = true := isOT_sumN _ (fun t ht => (hel t ht).1)
  have hSge : AllGeT (psi (succ μ) z z) S := allGeT_foldl _ z rfl (allGeT_z _) hel
  have hform : ρ1.o r = psi μ (spArg μ z S) z := by
    rw [(hC1 r hrT).1]
    unfold oRhs
    show add (sp (sf (ρ1.v r)) z (sf S)) (sf z) = _
    rw [sp_eq_spArg, hv, sf_ot hμot, sf_ot hSot]
    rfl
  obtain ⟨hmem, hcnt⟩ := first_child_counted_take hx hR0 hZ2 hSD hZ1 hUAB h1 hqr
  obtain ⟨σ', hσ', hσ'z⟩ := o_arg_ne_z hC1 hrT hmem hcnt
  refine ⟨spArg μ z S, hform, ?_, allGeT_spArg ⟨_, rfl⟩ S z hSot hSge (allGeT_z _)⟩
  rw [hform] at hσ'
  rw [(T.psi.inj hσ').2.1]; exact hσ'z

/-- From the seed form: `ψ_μ(Ω_{μ+1}) ≤ seed` and `seed` is a fixed point of `ω`. -/
theorem seed_fix {μ σ : T} (hot : isOT (psi μ σ z) = true) (hσz : σ ≠ z)
    (hσ : AllGeT (psi (succ μ) z z) σ) :
    etaOm μ ≤ psi μ σ z ∧ omega (psi μ σ z) = psi μ σ z := by
  have hΩ : psi (succ μ) z z ≤ σ := by
    have hh : head σ ∈ summands σ := by
      cases σ with
      | z => exact absurd rfl hσz
      | psi a b c => simp [head, summands]
    exact le_trans (le_of_not_gt (hσ _ hh)) (head_le_self σ)
  refine ⟨le_psi_arg hΩ, ?_⟩
  apply omega_fix_nolo hot
  · intro hE
    obtain ⟨hμz, hlt⟩ := below_E0 hE
    have h3 : psi (succ μ) z z = Om one := by rw [hμz]; rfl
    rw [h3] at hΩ
    exact lt_irrefl' _ (lt_of_le_of_lt hΩ hlt)
  · unfold loOf; exact split_snd_z_of_ge hσ


/-! ## VLocal を使わない共終数の追跡と b_r -/

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) {q : Nat} (hq : par M 0 x = some q)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAD : AbsD M ρ)
  (hox : ρ.o x = psi (succ μ) z z)
  (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hAD hox hF1 hOS

/-- **After `r`, the values on `D` have cofinality `Ω_{μ+1}`** (without `VLocal`). -/
theorem t1_cof0 : ∀ b i, DepX M x b i → r < i → (i < x ∨ (i = x ∧ b = true)) →
    cof (valB ρ b i) = .big μ ∧ (b = false → entry M 2 i ≠ 0 → Single (ρ.v i)) := by
  intro b i hD
  induction hD with
  | leaf =>
    intro _ _
    refine ⟨?_, fun h => nomatch h⟩
    show cof (ρ.o x) = _
    rw [hox]; exact cof_omega_succ μ
  | @ochild i c hc hcb' hcu hdc ih =>
    intro hri hix
    have hcM := (mem_children hc).2
    have hic := (mem_children hc).1
    have hi : i < x := by
      rcases hix with h | ⟨h, _⟩
      · exact h
      · omega
    have hcpos : c < x ∨ (c = x ∧ true = true) := by
      rcases Nat.lt_or_ge c x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, rfl⟩
    have ihc := (ih (by omega) hcpos).1
    simp only [valB, cond_true] at ihc
    rcases hOS i hi (DepX.ochild hc hcb' hcu hdc) with ⟨_, hnc⟩ | ⟨hv, L, c', R, hch, hcb2, hcu2, hR, hLnd⟩
    · exact absurd (hnc c hc) (by
        rintro (h | h)
        · exact hcb' h
        · exact hcu h)
    · have hcc : c = c' := by
        rw [hch] at hc
        rcases List.mem_append.mp hc with h | h
        · exact absurd hdc (hLnd c h ⟨hcb', hcu⟩)
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · rcases hR c h with h' | h'
            · exact absurd h' hcb'
            · exact absurd h' hcu
      subst hcc
      have hiM : i < M.length := by omega
      obtain ⟨s, y, hcv⟩ := o_psi_form hC hcM
      have hcot : isOT (psi s y z) = true := by rw [← hcv]; exact hG.ot_o c hcM
      have hframe := o_frame hC hG hiM hch hcb2 hcu2 hR hcM
      rw [hcv, spArg_single] at hframe
      rw [hcv] at ihc
      have hstep := cof_step (a := ρ.v i) (b := preState M ρ i L) hcot ihc
      refine ⟨?_, fun h => nomatch h⟩
      show cof (ρ.o i) = _
      rw [hframe]
      exact cof_psi_pass (cof_big_ne_z hstep) hstep (hF1 i hri hi (DepX.ochild hc hcb' hcu hdc) hv)
  | @ov i hv ih =>
    intro hri hix
    rcases hix with hi | ⟨rfl, _⟩
    · have ihv := (ih hri (Or.inl hi)).1
      simp only [valB, cond_false] at ihv
      rcases hOS i hi (DepX.ov hv) with ⟨_, hnc⟩ | ⟨hv', _⟩
      · have hoi := o_nocnt hC hG (by omega) hnc
        refine ⟨?_, fun h => nomatch h⟩
        show cof (ρ.o i) = _
        rw [hoi]
        have hvz := cof_big_ne_z ihv
        have hvs := not_succ_of_cof_big ihv
        unfold cof
        rw [if_pos rfl, if_neg hvz, if_neg (by rw [hvs]; simp), ihv]
      · exact absurd hv hv'
    · refine ⟨?_, fun h => nomatch h⟩
      show cof (ρ.o _) = _
      rw [hox]; exact cof_omega_succ μ
  | @vpar i m' h1 hp hdm _ =>
    intro _ hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    exact absurd hdm ((dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi (DepX.vpar h1 hp hdm)).2.1 m' hp)
  | @vupg i k h1 h2 hu hdk ih =>
    intro hri hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    obtain ⟨_, _, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi (DepX.vupg h1 h2 hu hdk)
    rcases hcase with ⟨_, hu', hk, _⟩ | ⟨h2', _⟩
    · have hkk : k = i + 1 := by rw [hu] at hu'; exact Option.some.inj hu'
      obtain ⟨ihk, ihS⟩ := ih (by omega) (Or.inl (by omega))
      simp only [valB, cond_false] at ihk
      have hk2 : entry M 2 k ≠ 0 := by have := upg_target_e2 hu; omega
      have hVs := ihS rfl hk2
      obtain ⟨B, hvi⟩ := upg_val hC (by omega) h1 h2 hu hVs (vOpt_ot hG (by omega))
      refine ⟨?_, fun _ h => absurd h2 h⟩
      show cof (ρ.v i) = _
      rw [hvi, cof_app B (cof_big_ne_z ihk), ihk]
    · exact absurd h2 h2'
  | @vbump i j k h1 h2 hj hjb hk hdk ih =>
    intro hri hix
    have hi : i < x := by
      rcases hix with h | ⟨_, h⟩
      · exact h
      · cases h
    have hiM : i < M.length := by omega
    obtain ⟨_, _, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi (DepX.vbump h1 h2 hj hjb hk hdk)
    rcases hcase with ⟨h2', _⟩ | ⟨_, L, K, j', k', hch, hjb', hchj, _, hKnd, hLnd⟩
    · exact absurd h2' h2
    · have hjj : j = j' := by
        rw [hch] at hj
        rcases List.mem_append.mp hj with h | h
        · exact absurd hdk (hLnd j h k hk).2
        · exact List.mem_singleton.mp h
      subst hjj
      have hkk : k = k' := by
        rw [hchj] at hk
        rcases List.mem_append.mp hk with h | h
        · exact absurd hdk (hKnd k h)
        · exact List.mem_singleton.mp h
      subst hkk
      have hjk := (mem_children hk).1
      have hij := (mem_children hj).1
      have hkpos : k < x ∨ (k = x ∧ true = true) := by
        have := (mem_children hk).2
        rcases Nat.lt_or_ge k x with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, rfl⟩
      obtain ⟨ihk, _⟩ := ih (by omega) hkpos
      simp only [valB, cond_true] at ihk
      obtain ⟨hBD, hvi, _⟩ := v_bump_D (br := z) (vr := z) hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD
        hTD hAD hi h1 h2 hch hjb hchj (Or.inl ihk)
      have hGot := (sumN_dec _ hBD.sK hBD.pK).1
      have hkS : Single (ρ.o k) := hBD.sK _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hcG : cof (sumN (K.map ρ.o ++ [ρ.o k])) = .big μ := by
        rw [sumN_snoc_dec hBD.sK hBD.pK, cof_app _ (single_ne_z hkS)]; exact ihk
      have hcω := cof_omega_pass hGot hcG hBD.passG
      have hωGz := cof_big_ne_z hcω
      refine ⟨?_, fun _ _ => by rw [hvi]; exact single_omega hBD.potW⟩
      show cof (ρ.v i) = _
      rw [hvi]
      exact cof_omega_pass hBD.potW (by rw [cof_app _ hωGz]; exact hcω) hBD.passP

end

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hC : Cons M ρ) (hG : Good3 M ρ)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hcof : ∀ b i, DepX M x b i → r < i → (i < x ∨ (i = x ∧ b = true)) → cof (valB ρ b i) = .big μ)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hOS hcof

theorem hcb_of_cof (h1 : par M 1 x = some r) (hx2 : entry M 2 x = 0) (hqr : par M 0 x ≠ some r)
    (hR12 : R12 M) (hBE : BumpE2 M) {vr br : T} (hro : ρ.o r = psi vr br z) :
    cof br = .big μ ∧ br ≠ z := by
  have hAr := anc0_of_par M 1 r x h1
  have hrx : r < x := par_lt M 1 x r h1
  have hpath := hpath_of_par1 h1 hAr (by omega)
  have hDr : DepX M x true r := dep_anc_x hUAT hZ2 hR12 hBE hx hx2 hAr
  have hnv : ¬ DepX M x false r := fun h =>
    v_r_not_chg hx hR0 hZ2 hSD hZ1 hUAT hUAB hAr (by omega) hqr hpath (depX_chgX h)
  rcases hOS r hrx hDr with ⟨hv, _⟩ | ⟨_, L, c, R, hch, hcb2, hcu2, hR, hLnd⟩
  · exact absurd hv hnv
  · have hc : c ∈ children M r := by rw [hch]; simp
    -- the child through which `o(r)` is in `D` is `c`
    have hcD : DepX M x true c := by
      cases hDr with
      | leaf => omega
      | @ochild _ c0 hc0 hcb0 hcu0 hdc0 =>
        have : c0 = c := by
          rw [hch] at hc0
          rcases List.mem_append.mp hc0 with h | h
          · exact absurd hdc0 (hLnd c0 h ⟨hcb0, hcu0⟩)
          · rcases List.mem_cons.mp h with h | h
            · exact h
            · rcases hR c0 h with h' | h'
              · exact absurd h' hcb0
              · exact absurd h' hcu0
        rw [← this]; exact hdc0
      | ov h => exact absurd h hnv
    have hcM := (mem_children hc).2
    have hrc := (mem_children hc).1
    obtain ⟨s, y, hcv⟩ := o_psi_form hC hcM
    have hcot : isOT (psi s y z) = true := by rw [← hcv]; exact hG.ot_o c hcM
    have hframe := o_frame hC hG (by omega) hch hcb2 hcu2 hR hcM
    rw [hcv, spArg_single] at hframe
    have hcc := hcof true c hcD hrc (by
      rcases Nat.lt_or_ge c x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, rfl⟩)
    simp only [valB, cond_true] at hcc
    rw [hcv] at hcc
    have hstep := cof_step (a := ρ.v r) (b := preState M ρ r L) hcot hcc
    rw [hro] at hframe
    obtain ⟨_, hb, _⟩ := T.psi.inj hframe
    rw [hb]
    exact ⟨hstep, cof_big_ne_z hstep⟩


theorem last_br_of_cof (h1 : par M 1 x = some r) (hx2 : entry M 2 x = 0) (hqr : par M 0 x ≠ some r)
    (hR12 : R12 M) (hBE : BumpE2 M) {vr br : T} (hro : ρ.o r = psi vr br z) :
    last br ≠ psi (succ μ) z z := by
  have hAr := anc0_of_par M 1 r x h1
  have hrx : r < x := par_lt M 1 x r h1
  have hpath := hpath_of_par1 h1 hAr (by omega)
  have hDr : DepX M x true r := dep_anc_x hUAT hZ2 hR12 hBE hx hx2 hAr
  have hnv : ¬ DepX M x false r := fun h =>
    v_r_not_chg hx hR0 hZ2 hSD hZ1 hUAT hUAB hAr (by omega) hqr hpath (depX_chgX h)
  rcases hOS r hrx hDr with ⟨hv, _⟩ | ⟨_, L, c, R, hch, hcb2, hcu2, hR, hLnd⟩
  · exact absurd hv hnv
  · have hc : c ∈ children M r := by rw [hch]; simp
    have hcD : DepX M x true c := by
      cases hDr with
      | leaf => omega
      | @ochild _ c0 hc0 hcb0 hcu0 hdc0 =>
        have : c0 = c := by
          rw [hch] at hc0
          rcases List.mem_append.mp hc0 with h | h
          · exact absurd hdc0 (hLnd c0 h ⟨hcb0, hcu0⟩)
          · rcases List.mem_cons.mp h with h | h
            · exact h
            · rcases hR c0 h with h' | h'
              · exact absurd h' hcb0
              · exact absurd h' hcu0
        rw [← this]; exact hdc0
      | ov h => exact absurd h hnv
    have hcM := (mem_children hc).2
    have hrc := (mem_children hc).1
    have hpc : par M 0 c = some r := (mem_children_iff.mp hc).2
    obtain ⟨s, y, hcv⟩ := o_psi_form hC hcM
    have hcot : isOT (psi s y z) = true := by rw [← hcv]; exact hG.ot_o c hcM
    have hframe := o_frame hC hG (by omega) hch hcb2 hcu2 hR hcM
    rw [hcv, spArg_single] at hframe
    have hcx : c < x := by
      rcases Nat.lt_or_ge c x with h | h
      · exact h
      · exfalso
        have : c = x := by omega
        subst this; exact hqr hpc
    have hcc := hcof true c hcD hrc (Or.inl hcx)
    simp only [valB, cond_true] at hcc
    rw [hcv] at hcc
    rw [hro] at hframe
    obtain ⟨_, hb, _⟩ := T.psi.inj hframe
    rw [hb]
    by_cases hy : y = z
    · -- `o(c) = Ω_{μ+1}` is impossible
      subst hy
      unfold step
      rw [if_neg (by intro h; exact T.not_lt_z _ h.1), last_add_single]
      intro he
      have hs : s = succ μ := (T.psi.inj he).1
      cases hcD with
      | leaf => omega
      | @ochild _ d hd hdb hdu _ =>
        obtain ⟨σ, hσ, hσz⟩ := o_arg_ne_z hC hcM hd ⟨hdb, hdu⟩
        rw [hcv] at hσ; exact hσz (T.psi.inj hσ).2.1.symm
      | ov hvc =>
        have hvv := hcof false c hvc hrc (Or.inl hcx)
        simp only [valB, cond_false] at hvv
        obtain ⟨σ, hσ⟩ := o_psi_sub hC hcM
        rw [hcv, sf_ot (hG.ot_v c hcM)] at hσ
        have hsv : s = ρ.v c := (T.psi.inj hσ).1
        rw [← hsv, hs, cof_of_isSucc (isSucc_succ μ)] at hvv
        cases hvv
    · have hμs := (cof_psi_inv hy hcc).2
      have hyot : isOT y = true := isOT_arg hcot
      unfold step
      split
      · rcases last_H (s := s) hy hyot (isOT_sub hcot) with h | ⟨h, hlo⟩
        · rw [h]; intro he; exact hy (T.psi.inj he).2.1
        · rw [h]
          intro he
          have hyall : ∀ q ∈ summands y, ¬ q < psi (succ s) z z := by
            intro q hq
            have e := split_app (psi (succ s) z z) y
            rw [hlo, app_z_right] at e
            rw [← e] at hq
            exact split_fst_ge _ y q hq
          apply hyall _ (last_mem hy)
          rw [he, psi_lt_psi_z_iff]
          left
          rw [lt_succ_iff]; exact succ_le_of_lt (show μ < s from hμs)
      · rw [last_add_single]; intro he; exact hy (T.psi.inj he).2.1


end

/-! ## まとめ: VLocal と始点の下限を外す -/

/-- **`t = 1`, `q ≠ r`, all `n ≥ 2`**: `t1_main_tpl` without `hV` and without the seed bound, from the value
invariants TPLo, AbsD, AbsU. -/
theorem t1_main_vloc {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmall M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hTP : TP1 M ρ) (hTPLo : TPLo M ρ) (hAD : AbsD M ρ) (hAU : AbsU M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbs M ρ) (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : BumpVSmallTake M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbs M ρ)
    (hne : (drop1 M (r + L) rkM).o r ≠ ρ.o r)
    {μ br vr : T} (hμr : μ = vr) (hro : ρ.o r = psi vr br z)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r < r + L := by omega
  have hrM : r < M.length := by omega
  have hvr : ρ.v r = vr := by
    obtain ⟨y0, hy0⟩ := o_psi_sub hC hrM
    rw [hro] at hy0; simp only [psi.injEq] at hy0
    rw [hy0.1, sf_ot (hG.ot_v r hrM)]
  have hF1 : ∀ i, r < i → i < r + L → DepX M (r + L) true i → ¬ DepX M (r + L) false i →
      lt μ (ρ.v i) = true := by
    intro i h2 h3 h4 h5
    rw [hμr, ← hvr]
    exact hF1_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hC hG hRM i h2 h3 h4 h5
  have hox : ρ.o (r + L) = psi (succ μ) z z := by
    rw [o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2, hvr, hμr]
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq
  -- the base `M.take x`
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hv1r : (drop1 M (r + L) rkM).v r = ρ.v r :=
    base_v_r hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hA (by omega) hqr hpath
  have hv1 : (drop1 M (r + L) rkM).v r = μ := by rw [hv1r, hvr, hμr]
  have hdrop := drop_all (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hF hFO hArgT
    (bump_drop (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hKD hTD hAbs hWS hVSt)
    (fun i k W _ hu hv hW => hUA i k W hu hv hW)
  have hotv : ∀ i, i < r + L → isOT ((drop1 M (r + L) rkM).v i) = true :=
    fun i hi => (hdrop i hi).2.2.1
  have hoto : ∀ i, i < r + L → isOT ((drop1 M (r + L) rkM).o i) = true :=
    fun i hi => (hdrop i hi).1.2.1
  -- the seed
  obtain ⟨σ, hs, hσz, hσge⟩ := seed_arg_ge hlen hR0 hZ2 hSD hZ1 hUAB h1 hqr hC1 hRk1 hotv hoto hv1
  have hsot : isOT (psi μ σ z) = true := by rw [← hs]; exact hoto r hrx
  obtain ⟨hseedΩ, hseedfix⟩ := seed_fix hsot hσz hσge
  rw [← hs] at hseedΩ hseedfix
  -- `b_r`
  have hcof0 := t1_cof0 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hAD hox hF1 hOS
  have hcof : ∀ b i, DepX M (r + L) b i → r < i → (i < r + L ∨ (i = r + L ∧ b = true)) →
      cof (valB ρ b i) = .big μ := fun b i hD hri hp => (hcof0 b i hD hri hp).1
  obtain ⟨hcb, hbr⟩ := hcb_of_cof hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hOS hcof h1 hx2 hqr hR12 hBE hro
  have hbrl := last_br_of_cof hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hOS hcof h1 hx2 hqr hR12 hBE hro
  have hrot : isOT (psi vr br z) = true := by rw [← hro]; exact hG.ot_o r hrM
  have hμ : ¬ lt μ vr = true := by rw [hμr]; exact lt_irrefl' _
  -- the seed condition
  obtain ⟨hlhd0, _⟩ := base_seed hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hrx (hdrop r hrx).1 hv1r hne
  have hlhd : Lhd z (psi μ σ z) (psi μ br z) := by
    rw [← hs]; rw [hro, ← hμr] at hlhd0; exact hlhd0
  have hσb : σ < br := by
    have := hlhd.1; rw [psi_lt_psi_z_iff] at this
    rcases this with h | ⟨_, h⟩
    · exact absurd h (lt_irrefl' _)
    · exact h
  have hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true →
      SeedOK a' br μ ((drop1 M (r + L) rkM).o r) := by
    intro a' ha' hot'
    rw [hs]
    exact seedOK_of_lhd_top hot' hcb (by rw [hμr]; exact ha') hsot hσb hlhd
  have hHx : HoleT μ br vr (ρ.o (r + L)) := Or.inl (by rw [hox]; exact cof_omega_succ μ)
  have hS2 := hS2_t1 hR0 hA (by omega)
  have hS3 := hS3_t1 h1 hA (by omega) hlen hR0 hZ2 hSD hZ1
  -- `VLocal` on the whole chain
  have hV : ∀ m i, i < r + L → DepX M (r + L) false i →
      VLocal M (r + L) ρ (gamS μ br ((drop1 M (r + L) rkM).o r) m) μ i := by
    intro m
    have hζfix := gamS_fix hrot hcb hμ (hS vr (lt_irrefl' _) hrot) hbrl hseedfix hseedΩ m
    have hζΩ := gamS_ge_omfix (isOT_arg hrot) hcb hbrl hseedΩ m
    have hok : ∀ t, isOT t = true → HoleT μ br vr t →
        isOT (fsD t (gamS μ br ((drop1 M (r + L) rkM).o r) m)) = true ∧
        fsD t (gamS μ br ((drop1 M (r + L) rkM).o r) m) < t :=
      fun t hot hH => hok_of_holeT hrot hcb hμ hS hot hH m
    cases m with
    | zero =>
      exact vlocal_t1 (X := σ) hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hAD hrx hA hro hcb hμr
        hbr hHx hF1 hOS hS2 hS3 hTPLo hAU hbrl hs hσz hζfix hζΩ hok
    | succ m =>
      have hne' : gamS μ br ((drop1 M (r + L) rkM).o r) m ≠ z := by
        intro h
        have := gamS_ge_omfix (isOT_arg hrot) hcb hbrl hseedΩ m
        rw [h] at this
        exact T.not_lt_z _ (lt_of_lt_of_le (T.z_lt_psi _ _ _) this)
      exact vlocal_t1 (X := fs br (gamS μ br ((drop1 M (r + L) rkM).o r) m)) hlen hR0 hZ2 hSD hZ1 hUAT
        hUAB hx2 hq hC hG hKD hTD hAD hrx hA hro hcb hμr hbr hHx hF1 hOS hS2 hS3 hTPLo hAU hbrl rfl
        (fs_ne_z_big hcb hne') hζfix hζΩ hok
  exact t1_main_tpl hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hqr hC hG hRM
    hVS hF hFO hTP (TPL_of_TPLo hTPLo) hArgT hKD hTD hAbs hWS hVSt hUA hne hμr hro hseedΩ hV hsM hpM

end Ytosk
