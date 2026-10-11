/-
**3 行・t = 2: x より前の残り T2BelowXRes から、証明済みの種の ◁ を外す（`t2BelowXRes_of_L`）。**

T2BelowResL は T2BelowRes から種と q の欄（◁・標準形・数える子の減少）を外し、M[n] 側の T2HardA（T2Hard・T2VSN の代わり、V3DepRWU）・AbsWN（弱い吸収）だけにしたもの。種と q の欄は 4 つの場合ごとに M と M.take x だけの残りから出る。
- q = r で x への上げがない: seedL_qr（V3T2SeedQRL）、M と M.take x だけの残り T2SeedQRRes から。
- q ≠ r で q が r の最後の数える子: seedL_qn（V3T2SeedQNV）、残り T2SeedQNRes から。
- sv（q = r で x − 1 が x へ上げる）: seedL_sv（V3T2SeedSV）、残り T2SeedSVRes から。
- C（q ≠ r で q が r で数えられない）: seedL_C（V3T2SeedC）、残り T2SeedCRes から。
4 つで t = 2 のすべての場合を尽くす（`t2_seed_cases`）。
-/
import Ytosk.V3T2SeedOT

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- `q = r` and nothing upgrades into `x`. -/
def T2QRNoUpg (M : Mat) (r L : Nat) : Prop := par M 0 (r + L) = some r ∧ ∀ i, upg M i ≠ some (r + L)

/-- `q ≠ r` and `q` is the last counted child of `r`. -/
def T2QNLast (M : Mat) (r L : Nat) : Prop :=
  ∃ q Lc, par M 0 (r + L) = some q ∧ q ≠ r ∧ CL M r = Lc ++ [q]

/-- `q = r` and `x − 1` upgrades to `x` (the sv case). -/
def T2SVCase (M : Mat) (r L : Nat) : Prop := par M 0 (r + L) = some r ∧ upg M (r + L - 1) = some (r + L)

/-- `q ≠ r` and `q` is not the last counted child of `r` (the C case). -/
def T2CCase (M : Mat) (r L : Nat) : Prop :=
  ∃ q, par M 0 (r + L) = some q ∧ q ≠ r ∧ ¬ ∃ Lc, CL M r = Lc ++ [q]

/-- **The four seed cases cover `t = 2`.** -/
theorem t2_seed_cases {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) :
    T2QRNoUpg M r L ∨ T2QNLast M r L ∨ T2SVCase M r L ∨ T2CCase M r L := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hrx : r < r + L := par_lt M 2 _ _ hr
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  by_cases hqr : q = r
  · rw [hqr] at hq
    by_cases hux : upg M (r + L - 1) = some (r + L)
    · exact Or.inr (Or.inr (Or.inl ⟨hq, hux⟩))
    · refine Or.inl ⟨hq, fun i hi => ?_⟩
      have hle := upg_le hi
      have hil := upg_lt_len hi
      have hix : i = r + L - 1 := by omega
      rw [hix] at hi; exact hux hi
  · by_cases hqn : ∃ Lc, CL M r = Lc ++ [q]
    · obtain ⟨Lc, h⟩ := hqn; exact Or.inr (Or.inl ⟨q, Lc, hq, hqr, h⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨q, hq, hqr, hqn⟩))

/-- **`T2BelowRes` without the ◁ of the seed.** -/
def T2BelowResL (M : Mat) (ρ : Valn) (r L d0 d1 : Nat) : Prop :=
  ∀ n, 2 ≤ n → (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L d0 d1 m) τ → Good3 (TRIO.gexp M r L d0 d1 m) τ) →
    ∀ σ, Cons (TRIO.gexp M r L d0 d1 n) σ →
    (∀ b j, r + L ≤ j → j < (TRIO.gexp M r L d0 d1 n).length → isOT (valB σ b j) = true) →
    (∀ p, T2Seed M r L p → T2HardA M (TRIO.gexp M r L d0 d1 n) (r + L) p ρ σ) ∧
    AbsWN M (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ

/-- `T2BelowResL` for every standard `M` of type `t = 2`. -/
def T2BelowXResL : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      T2BelowResL M ρ r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r)

/-- The seed residual of `q = r` without an upgrade into `x`, for every standard `M` of type `t = 2`. -/
def T2SeedQRAll : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      T2QRNoUpg M r L → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQRRes M ρ r L Lc

/-- The seed residual of `q ≠ r` with `q` the last counted child of `r`, for every standard `M` of type `t = 2`. -/
def T2SeedQNAll : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      ∀ q Lc, par M 0 (r + L) = some q → q ≠ r → CL M r = Lc ++ [q] → T2SeedQNRes M ρ r L q Lc

/-- The seed residual of the sv case, for every standard `M` of type `t = 2`. -/
def T2SeedSVAll : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      T2SVCase M r L → T2SeedSVRes M ρ r L

/-- The seed residual of the C case, for every standard `M` of type `t = 2`. -/
def T2SeedCAll : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      ∀ q, par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCRes M ρ r L q

/-- `x` is the last counted child of `r` (`q = r`, nothing upgrades into `x`). -/
theorem cl_r_split {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hq : par M 0 (r + L) = some r)
    (hXu : ∀ i, upg M i ≠ some (r + L)) (hxb : col M (r + L) ≠ bump M r) :
    ∃ Lc, CL M r = Lc ++ [r + L] := by
  have hxc : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have hcnt : Counted M r (r + L) := ⟨hxb, by
    have : isUpg M (r + L) = false := by
      unfold isUpg; rw [List.any_eq_false]; intro k _ hk; exact hXu k (of_decide_eq_true hk)
    rw [this]; simp⟩
  have hsplit := children_split_x hlen hxc
  refine ⟨(children M r).filter (fun d => decide (d < r + L)) |>.filter (fun c => decide (Counted M r c)), ?_⟩
  unfold CL
  rw [hsplit, List.filter_append]
  simp [hcnt]

/-- The standard-form residual of the closed forms, for every standard `M` of type `t = 2`, in the four cases. -/
def T2SeedOTAll : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      (T2QRNoUpg M r L → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQROT M ρ r L Lc) ∧
      (∀ q Lc, par M 0 (r + L) = some q → q ≠ r → CL M r = Lc ++ [q] → T2SeedQNOT M ρ r L q Lc) ∧
      (T2SVCase M r L → T2SeedSVOT M ρ r L) ∧
      (∀ q, par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCOT M ρ r L q)

/-- **`T2BelowXRes` from `T2BelowXResL` and the seed residuals of the four cases.** -/
theorem t2BelowXRes_of_L (hL : T2BelowXResL) (hQR : T2SeedQRAll) (hQN : T2SeedQNAll) (hSV : T2SeedSVAll)
    (hCC : T2SeedCAll) (hOTs : T2SeedOTAll) : T2BelowXRes := by
  intro M ρ rk hM hS I R hz h2 r L hlen hr n hn hGlow σ hCN hOT
  obtain ⟨h2', h3⟩ := hL M ρ rk hM hS I R hz h2 r L hlen hr n hn hGlow σ hCN hOT
  obtain ⟨hO1, hO2, hO3, hO4⟩ := hOTs M ρ rk hM hS I R hz h2 r L hlen hr
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hRk : ∀ m, 1 ≤ m → ∃ rk', Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) m) rk' := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
  have hCP := cons_of_rk hRP
  have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  have hP1 : TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) 1 =
      M.take (r + L) := gexp_one_gen hlen
  have hG0 : Good3 (M.take (r + L)) (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rk)) := by
    have h := hGlow 1 (le_refl 1) (by omega) _ (by rw [hP1]; exact hC0)
    rwa [hP1] at h
  -- the seed is `r`
  have hpr : ∀ p, T2Seed M r L p → p = r := by
    intro p hp
    rcases hp with ⟨_, rfl⟩ | ⟨q, hq, hqr, hpq⟩
    · rfl
    · rw [par0_q_t2 hM hS I hlen hr hq hqr] at hpq; cases hpq; rfl
  -- the decrease of the counted children of the seed and of `q`
  have hD : (cvals (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n)
      σ r).Pairwise (fun a b => b ≤ a) ∧
      (∀ q, par M 0 (r + L) = some q → q ≠ r → (cvals (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n) σ q).Pairwise (fun a b => b ≤ a)) := by
    rw [cvals_eq_mapC hCN]
    rcases t2_seed_cases hlen hr with hc | hc | hc | hc
    · obtain ⟨hq, hXu⟩ := hc
      obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (by omega) hr
      have hxb : col M (r + L) ≠ bump M r := fun h => by
        have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
      obtain ⟨Lc, hCLM⟩ := cl_r_split hlen hq hXu hxb
      have hRes := hQR M ρ rk hM hS I R hz h2 r L hlen hr ⟨hq, hXu⟩ Lc hCLM
      have hks1 : succ (ρ.v r) < ρ.v (r + L) := by rw [succ_eq_addN_one]; exact hRes.ks 1
      refine ⟨seed_dec_qr hM hS I R hz h2 hlen hr hq hXu hCLM hn hCN hRN hCP hGP hRP hks1, ?_⟩
      intro q hq' hqr; rw [hq] at hq'; cases hq'; exact absurd rfl hqr
    · obtain ⟨q, Lc, hq, hqr, hCLM⟩ := hc
      have hRes := hQN M ρ rk hM hS I R hz h2 r L hlen hr q Lc hq hqr hCLM
      have hvq := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
      obtain ⟨hd1, hd2⟩ := seed_dec_qn hM hS I R hz h2 hlen hr hq hqr hCLM hn hCN hRN hCP hGP hRP
        (by rw [hvq]; exact hRes.vqlt)
      refine ⟨hd1, fun q' hq' _ => ?_⟩
      rw [hq] at hq'; cases hq'
      rw [cvals_eq_mapC hCN]; exact hd2
    · obtain ⟨hq, hux⟩ := hc
      have hRes := hSV M ρ rk hM hS I R hz h2 r L hlen hr ⟨hq, hux⟩
      refine ⟨seed_dec_sv hM hS I R hz h2 hlen hr hq hux (topP_sv hlen I.z2 I.z1 hr hq hux) hn hCN hRN hCP hGP hRP hC0 hG0 hRk1
        (hRes.decP _ hC0), ?_⟩
      intro q hq' hqr; rw [hq] at hq'; cases hq'; exact absurd rfl hqr
    · obtain ⟨q, hq, hqr, hncl⟩ := hc
      have hRes := hCC M ρ rk hM hS I R hz h2 r L hlen hr q hq hqr hncl
      have hvq := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
      obtain ⟨hd1, hd2⟩ := seed_dec_C hM hS I R hz h2 hlen hr hq hqr (qP_C hM hS I hlen hr hq hqr hncl hRes.un) hRes.un hn hCN hRN hCP hGP hRP
        hC0 hG0 hRk1 (v_take_of_untopped I hlen hrx (topP_C hM hS I hlen hr hq hqr) hC0) (by rw [hvq]; exact hRes.vqP _ hC0)
        (fun Lc c0 h => by rw [hvq]; exact hRes.decP _ hC0 Lc c0 h)
      refine ⟨hd1, fun q' hq' _ => ?_⟩
      rw [hq] at hq'; cases hq'
      rw [cvals_eq_mapC hCN]; exact hd2
  have hdecr : ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
      σ.o).Pairwise (fun a b => b ≤ a) := by rw [← cvals_eq_mapC hCN]; exact hD.1
  -- the standard form of the seed and of `q`
  have hOTr : isOT (σ.o r) = true ∧ ∀ q, par M 0 (r + L) = some q → q ≠ r → isOT (σ.o q) = true := by
    rcases t2_seed_cases hlen hr with hc | hc | hc | hc
    · obtain ⟨hq, hXu⟩ := hc
      obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (by omega) hr
      have hxb : col M (r + L) ≠ bump M r := fun h => by
        have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
      obtain ⟨Lc, hCLM⟩ := cl_r_split hlen hq hXu hxb
      refine ⟨seed_ot_qr hM hS I R hz h2 hlen hr hq hXu hCLM
        (hQR M ρ rk hM hS I R hz h2 r L hlen hr ⟨hq, hXu⟩ Lc hCLM) (hO1 ⟨hq, hXu⟩ Lc hCLM) n hn hGlow σ hCN, ?_⟩
      intro q hq' hqr; rw [hq] at hq'; cases hq'; exact absurd rfl hqr
    · obtain ⟨q, Lc, hq, hqr, hCLM⟩ := hc
      obtain ⟨hqo, hro⟩ := seed_ot_qn hM hS I R hz h2 hlen hr hq hqr hCLM
        (hQN M ρ rk hM hS I R hz h2 r L hlen hr q Lc hq hqr hCLM) (hO2 q Lc hq hqr hCLM) n hn hGlow σ hCN hdecr
      refine ⟨hro, fun q' hq' _ => ?_⟩
      rw [hq] at hq'; cases hq'; exact hqo
    · obtain ⟨hq, hux⟩ := hc
      refine ⟨seed_ot_sv hM hS I R hz h2 hlen hr hq hux (hSV M ρ rk hM hS I R hz h2 r L hlen hr ⟨hq, hux⟩)
        (hO3 ⟨hq, hux⟩) n hn hGlow σ hCN hdecr, ?_⟩
      intro q hq' hqr; rw [hq] at hq'; cases hq'; exact absurd rfl hqr
    · obtain ⟨q, hq, hqr, hncl⟩ := hc
      obtain ⟨hqo, hro⟩ := seed_ot_C hM hS I R hz h2 hlen hr hq hqr hncl
        (hCC M ρ rk hM hS I R hz h2 r L hlen hr q hq hqr hncl) (hO4 q hq hqr hncl) n hn hGlow σ hCN hdecr
      refine ⟨hro, fun q' hq' _ => ?_⟩
      rw [hq] at hq'; cases hq'; exact hqo
  refine ⟨h2', fun p hp => ?_, fun q hq hqr => ⟨hOTr.2 q hq hqr, hD.2 q hq hqr⟩, h3⟩
  have hp' := hpr p hp
  subst p
  have hot := hOTr.1
  have hdec := hD.1
  refine ⟨?_, hot, hdec⟩
  rcases t2_seed_cases hlen hr with hc | hc | hc | hc
  · obtain ⟨hq, hXu⟩ := hc
    obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (by omega) hr
    have hxb : col M (r + L) ≠ bump M r := fun h => by
      have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
    obtain ⟨Lc, hCLM⟩ := cl_r_split hlen hq hXu hxb
    exact seedL_qr hM hS I R hz h2 hlen hr hq hXu hCLM
      (hQR M ρ rk hM hS I R hz h2 r L hlen hr ⟨hq, hXu⟩ Lc hCLM) n hn hGlow σ hCN
  · obtain ⟨q, Lc, hq, hqr, hCLM⟩ := hc
    exact seedL_qn hM hS I R hz h2 hlen hr hq hqr hCLM (hQN M ρ rk hM hS I R hz h2 r L hlen hr q Lc hq hqr hCLM)
      n hn hGlow σ hCN (hOTr.2 q hq hqr) (by rw [← cvals_eq_mapC hCN]; exact hdec)
  · obtain ⟨hq, hux⟩ := hc
    exact seedL_sv hM hS I R hz h2 hlen hr hq hux (hSV M ρ rk hM hS I R hz h2 r L hlen hr ⟨hq, hux⟩)
      n hn hGlow σ hCN (by rw [← cvals_eq_mapC hCN]; exact hdec)
  · obtain ⟨q, hq, hqr, hncl⟩ := hc
    exact seedL_C hM hS I R hz h2 hlen hr hq hqr hncl (hCC M ρ rk hM hS I R hz h2 r L hlen hr q hq hqr hncl)
      n hn hGlow σ hCN (hOTr.2 q hq hqr) (by rw [← cvals_eq_mapC hCN]; exact hdec)

end Ytosk
