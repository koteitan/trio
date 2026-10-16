/-
**RwClosed を t = 2 の M[n] へ運ぶ（2026-10-17、t0）。**

t2 の FrameClosed（V3T2FC）と同じ組み立て: 枠の性質 `QRCo`（子が標準形で `QRC`）を t = 2 の骨組み
`clField_expand_t2S` で運ぶ。
- 写し: 書き換えの条件と状態は σ と交換（qFCo_sh と同じ）。前提 B < hi(y) も σ と交換（sh_split・sh_lt_iff）。
  閉じていることの σ 不変性は項だけの主張 `ClSh`（名前つきの残り）。
- 子を ◁ で下げる: `qrc_drop`（添字が下がれば引数は 0 で書き換えない、同じなら hi は単調）。
- 種の列の枠: 名前つきの残り `T2SeedFrames QRC M`。
-/
import Ytosk.V3RwClT0
import Ytosk.V3T2FC

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **`σ`-invariance of closedness** (named residual; a statement about terms only). -/
def ClSh : Prop :=
  ∀ V V' a B : T, isOT V = true → isOT V' = true → V < V' → isOT a = true → V ≤ a →
    isOT B = true → (∀ q ∈ summands B, V < lev q) → ClosedA a B → ClosedA (shf V V' a) (sh V V' B)

/-- `QRC` with the standard form of the child. -/
def QRCo (a : T) (Lv : List T) (cv : T) : Prop := isOT cv = true ∧ QRC a Lv cv

theorem clField_QRCo {N : Mat} {σ : Valn} (hG : Good3 N σ) (h : RwClosed N σ) : CLField QRCo N σ := by
  intro i hi Lc c R hCL
  have hcN : c < N.length := (mem_children (cl_mem_children (show c ∈ CL N i by rw [hCL]; simp))).2
  exact ⟨hG.ot_o c hcN, rwClosed_iff.mp h i hi Lc c R hCL⟩

theorem rwClosed_of_QRCo {N : Mat} {σ : Valn} (h : CLField QRCo N σ) : RwClosed N σ :=
  rwClosed_iff.mpr (fun i hi Lc c R hCL => (h i hi Lc c R hCL).2)

/-- **`QRCo` moves with `σ`**, given `ClSh`. -/
theorem qRCo_sh (hCl : ClSh) (V V' a : T) (Lv : List T) (cv : T) (hV : isOT V = true)
    (hV' : isOT V' = true) (hVV : V < V') (ha : isOT a = true) (hVa : V ≤ a)
    (hs : ∀ t ∈ Lv ++ [cv], Single t) (hp : (Lv ++ [cv]).Pairwise (fun a b => b ≤ a))
    (hlev : V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) (hQ : QRCo a Lv cv) :
    QRCo (shf V V' a) (Lv.map (sh V V')) (sh V V' cv) := by
  have hLs : ∀ t ∈ Lv, Single t := fun t ht => hs t (List.mem_append_left _ ht)
  have hLp : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp).1
  obtain ⟨hSot, hSsum⟩ := sumN_dec Lv hLs hLp
  have hlev' : V < a ∨ ∀ q ∈ summands (sumN Lv), lev q ≠ V := by
    rcases hlev with h | h
    · exact Or.inl h
    · right; rw [hSsum]; intro q hq; exact ne_of_gt (h q (List.mem_append_left _ hq))
  have hBot : isOT (spArg a z (sumN Lv)) = true := isOT_spArg a (sumN Lv) z rfl hSot
  have hB : spArg (shf V V' a) z (sumN (Lv.map (sh V V'))) = sh V V' (spArg a z (sumN Lv)) := by
    rw [← sh_sumN hV hV' hVV (fun t ht => (hLs t ht).1)]
    have hsp := sh_spArg hV hV' hVV ha hVa (b := z) rfl hSot hlev'
    rw [sh_z] at hsp
    exact hsp
  obtain ⟨hcvot, s, y, hcv⟩ := hs cv (by simp)
  subst hcv
  refine ⟨isOT_sh hV hV' hVV hcvot, ?_⟩
  intro s' y' hcv' ht' hhi'
  rw [hB] at ht' hhi' ⊢
  have hVV' : V ≤ V' := le_of_lt hVV
  have hsot : isOT s = true := isOT_sub hcvot
  have hyot : isOT y = true := isOT_arg hcvot
  by_cases hVs : V < s
  · rw [sh_psi_gt hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    have h1 : lt (spArg a z (sumN Lv)) y = true :=
      (sh_lt_iff hV hV' hVV' hBot hyot).mp ht'.1
    have hfa : shf V V' a ≤ shf V V' s := le_of_trig ht'.2
    have has : a ≤ s := by
      rcases (le_iff _ _).mp hfa with h | h
      · exact le_of_lt ((shf_lt_iff hV hV' hVV' ha hsot hVa (le_of_lt hVs)).mp h)
      · rcases lt_trichotomy' a s with h' | h' | h'
        · exact le_of_lt h'
        · rw [h']
        · exact absurd h (ne_of_gt (shf_lt_shf hV hV' hVV' hsot ha (le_of_lt hVs) h'))
    have hyz : y ≠ z := fun h => by rw [h] at h1; exact T.not_lt_z _ h1
    have h2 : lt (psi a z z) (psi s y z) = true := by
      show psi a z z < psi s y z
      rcases (le_iff _ _).mp has with h | h
      · exact psi_lt_psi_z_iff.mpr (Or.inl h)
      · subst h
        exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hyz)⟩)
    -- the premise `B < hi(y)` moves back
    have hsplit := sh_split hV hV' hVV (sh_lt_om_succ hV hV' hVV hsot hVs) hyot
    rw [hsplit] at hhi'
    have hhiot : isOT (split y (psi (succ s) z z)).1 = true :=
      isOT_app_left (by rw [split_app]; exact hyot)
    have hhi : spArg a z (sumN Lv) < (split y (psi (succ s) z z)).1 :=
      (sh_lt_iff hV hV' hVV' hBot hhiot).mp hhi'
    have hBc : ∀ q ∈ summands (spArg a z (sumN Lv)), psi s y z ≤ q := by
      apply spArg_summands_ge ⟨s, y, rfl⟩ (sumN Lv) z hSot
      · rw [hSsum]; intro q hq
        exact (List.pairwise_append.mp hp).2.2 q hq _ (by simp)
      · simp [summands]
    have hBV : ∀ q ∈ summands (spArg a z (sumN Lv)), V < lev q := by
      intro q hq
      exact lt_of_lt_of_le hVs (lev_le_of_le (hBc q hq))
    exact hCl V V' a _ hV hV' hVV ha hVa hBot hBV (hQ.2 s y rfl ⟨h1, h2⟩ hhi)
  · rw [sh_psi_le hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    exfalso
    have hlt : s < shf V V' a :=
      lt_of_le_of_lt (le_of_not_gt hVs) (lt_of_lt_of_le hVV (le_shf hV hV' hVV' ha hVa))
    have := le_of_trig ht'.2
    exact lt_irrefl' _ (lt_of_lt_of_le hlt this)

/-- **`QRCo` survives lowering the child.** -/
theorem qRCo_low : ∀ a Lv cv cv', QRCo a Lv cv → Lhd z cv' cv → isOT cv' = true → (∃ s y, cv = psi s y z) →
    (∀ s y s' y', cv = psi s y z → cv' = psi s' y' z → s' ≠ s → y' = z) → QRCo a Lv cv' := by
  intro a Lv cv cv' hQ hl hot' hcv hss
  refine ⟨hot', ?_⟩
  obtain ⟨s, y, rfl⟩ := hcv
  intro s' y' hcv' ht' hhi'
  subst hcv'
  have hss' : y' ≠ z → s' = s := fun hy => by
    by_contra hne; exact hy (hss s y s' y' rfl rfl hne)
  exact qrc_drop (le_of_lt hl.1) hss' hQ.2 s' y' rfl ht' hhi'

/-- **RwClosed of every `M[n]`** (`t = 2`, `n ≥ 1`), with `ClSh` and the seed frames as the named residuals. -/
theorem rwClosed_expand_t2 (hCl : ClSh) (hB : T2BelowXRes) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hRM : RwClosed M ρ)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → RwClosed (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QRC M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → RwClosed (expand M n) σ := by
  have hl : 1 ≤ M.length := by
    rcases Nat.eq_zero_or_pos M.length with h | h
    · exfalso; apply hz; rw [h]
      have : M = [] := List.eq_nil_of_length_eq_zero h
      subst this; rfl
    · exact h
  have hSeed' : T2SeedFrames QRCo M := by
    intro r L hlen hr n hn hGm σ hCN hGN i hsc Lc c R hCL
    have hcN := (mem_children (cl_mem_children (show c ∈ CL _ i by rw [hCL]; simp))).2
    exact ⟨hGN.ot_o c hcN, hSeed r L hlen hr n hn hGm σ hCN hGN i hsc Lc c R hCL⟩
  have key := clField_expand_t2S (qRCo_sh hCl) qRCo_low hB hM hS I R hz h2 (clField_QRCo I.good hRM)
    (fun τ hτ => clField_QRCo (good3_take_any I R hl hτ) (hT τ hτ)) hSeed'
  exact fun n hn σ hσ => rwClosed_of_QRCo (key n hn σ hσ)

end Ytosk
