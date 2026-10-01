/-
**3 行・t = 1・q ≠ r: v の枠の局所条件 VLocal を不変条件から。**

- 値の不変条件: TPLo（すべての o で低い部分が空のまま、TPL より強い）、AbsD（のりしろの枠で v(P_1 i) が
  W と fsD(W, ψ_μ(Ω_{μ+1})) に吸収される）、AbsU（上げの枠の吸収）。
- D の v の列の形（`dv_shape`、構造だけから）: 上げなら次の列へ、のりしろなら最後の子 j の最後の子 k だけが D。
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

end Ytosk
