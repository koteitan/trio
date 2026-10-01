/-
**3 行・t = 1・q = r: v の局所条件 `VLocZ` をすべての D の呼び出しで（`qr_vloc`）。**

値の不変条件（大域、cof ω の穴に限る）:
- **AbsUW**: 上げ i → k で、v(P_1 i) の加数で last v(k) より小さいものは fsD(last v(k), 1) より小さい。
- **AbsDW**: のりしろの項 W について同じ（fsD(W, 1)）。
補題:
- `qr_lkeep`: D の列 c（c < x、o(c) ≠ A）の (L)(ii) を鎖の添字 gamS(m + d_c) で（y = b_r なら引き上げの数 ≥ 1、
  y ≠ b_r なら TPLoW か始点の仮定 hLs）。
- のりしろの ω の交換: 引き上げ 2（`omega_lift2`）、1（`omega_lift1`）、0（`omega_fsD_hole_Q` を 2 回）。
-/
import Ytosk.V3QROmega

namespace Ytosk

open T

/-- **Value invariant AbsUW** (`η = 1`, holes with cofinality `ω`). -/
def AbsUW (M : Mat) (ρ : Valn) : Prop :=
  ∀ i k, upg M i = some k → OHole (last (ρ.v k)) → cof (last (ρ.v k)) = .omega →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) → q < fsD (last (ρ.v k)) one

/-- **Value invariant AbsDW** (`η = 1`, holes with cofinality `ω`). -/
def AbsDW (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → OHole (bumpW M ρ i) →
    cof (bumpW M ρ i) = .omega →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i → q < fsD (bumpW M ρ i) one

/-- In a standard `P ++ X`, every summand of `P` is at least the head of `X`. -/
theorem summands_ge_of_app : ∀ {P X : T}, isOT (app P X) = true → ∀ q ∈ summands P, head X ≤ q
  | z, _, _, q, hq => by simp [summands] at hq
  | psi a b c, X, h, q, hq => by
    rw [app_psi, isOT_psi_iff] at h
    obtain ⟨_, _, h3, h4, _⟩ := h
    have ih := summands_ge_of_app h3
    have hhd : head X ≤ head (app c X) := by
      cases c with
      | z => exact le_refl _
      | psi c1 c2 c3 =>
        rw [app_psi]
        show head X ≤ psi c1 c2 z
        exact ih _ (by simp [summands])
    simp only [summands, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact le_trans hhd h4
    · exact ih q hq

/-- `A = ψ_μ(b + Ω_{μ+1})` is not below `ε_0`. -/
theorem A_not_lt_E0 {μ b : T} (hb : AllGeT (psi (succ μ) z z) b) :
    ¬ psi μ (app b (psi (succ μ) z z)) z < E0 := by
  have hall : AllGeT (psi (succ μ) z z) (app b (psi (succ μ) z z)) := by
    intro q hq
    rw [summands_app] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hb q hq
    · simp [summands] at hq; rw [hq]; exact lt_irrefl' _
  intro hE
  obtain ⟨hμz, hlt⟩ := below_E0 hE
  have h3 : psi (succ μ) z z = Om one := by rw [hμz]; rfl
  exact not_lt_of_lo_z (by intro h; exact absurd (app_eq_z h).2 (by simp))
    (split_snd_z_of_ge hall) (by rw [h3]; rw [h3] at hlt; exact hlt)

/-- A nonempty decreasing list of single summands has a nonzero sum. -/
theorem sumN_ne_z_of_single {l : List T} (hs : ∀ t ∈ l, Single t)
    (hp : l.Pairwise (fun a b => b ≤ a)) (hne : l ≠ []) : sumN l ≠ z := by
  obtain ⟨l', t, rfl⟩ : ∃ l' t, l = l' ++ [t] := by
    rcases List.eq_nil_or_concat l with h | ⟨l', t, h⟩
    · exact absurd h hne
    · exact ⟨l', t, by rw [h, List.concat_eq_append]⟩
  rw [sumN_snoc_dec hs hp]
  intro h
  exact single_ne_z (hs t (List.mem_append_right _ (List.mem_singleton_self _))) (app_eq_z h).2

/-- A chain term `next η` with `η < Ω_{μ+1}` is below `A`. -/
theorem qnext_lt_A {μ b η : T} (hη : η < psi (succ μ) z z) :
    qnext μ b η < psi μ (app b (psi (succ μ) z z)) z := by
  unfold qnext
  rw [psi_lt_psi_z_iff]
  exact Or.inr ⟨rfl, app_lt_app_left b hη⟩

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ b seed : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) (h1 : par M 1 x = some r) (hq : par M 0 x = some r)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAD : AbsD M ρ)
  (hro : ρ.o r = psi μ (app b (psi (succ μ) z z)) z)
  (hox : ρ.o x = psi (succ μ) z z)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro hox hOS

/-- **Every `D` value below `x` has a hole and a diagonal point** (`q = r`). -/
theorem qr_holeD : ∀ bb i, DepX M x bb i → i < x →
    HoleT μ (app b (psi (succ μ) z z)) μ (valB ρ bb i) ∧
    ∃ a', ¬ lt μ a' = true ∧ DiagAt a' (app b (psi (succ μ) z z)) μ (valB ρ bb i) := by
  have hbr : app b (psi (succ μ) z z) ≠ z := fun h => absurd (app_eq_z h).2 (by simp)
  have hrx : r < x := par_lt M 1 x r h1
  have hA : Anc0 M r x := anc0_of_par M 1 r x h1
  have hdep := qr_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq
  have hHx : HoleT μ (app b (psi (succ μ) z z)) μ (ρ.o x) :=
    Or.inl (by rw [hox]; exact cof_omega_succ μ)
  have hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true :=
    fun i h2 h3 h4 _ => absurd h4 (hdep.2.2 true i h2 h3)
  have hHole := t1_hole0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hAD hrx hA hro
    cof_br rfl hbr hHx hF1 hOS (hS2_t1 hR0 hA (by omega)) (hS3_t1 h1 hA (by omega) hx hR0 hZ2 hSD hZ1)
  intro bb i hD hi
  have hir : i ≤ r := by
    by_contra h
    exact hdep.2.2 bb i (by omega) hi hD
  obtain ⟨hH, hDL, _⟩ := hHole bb i hD (Or.inl hi)
  exact ⟨hH, hDL hir⟩

variable (hb : AllGeT (psi (succ μ) z z) b)
  (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
  (hBk : ∀ i j k, i < x → DepX M x false i → j ∈ children M i → col M j = bump M i →
    k ∈ children M j → DepX M x true k → k < x)
  (hxv : ¬ DepX M x false x)
  (hseedS : ∃ a X, seed = psi a X z)
  (hTPL : TPLoW M ρ)
  (hLs : ∀ c, c < x → DepX M x true c → dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
    ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ μ) z z) →
    (split y (psi (succ s) z z)).2 = z → (split (fsD y seed) (psi (succ s) z z)).2 = z)
include hb hVS hBk hxv hseedS hTPL hLs

/-- **(L)(ii) at a `D` column** (not `A`) with its own index. -/
theorem qr_lkeep (m : Nat) {c : Nat} (hc : c < x) (hdc : DepX M x true c) {s y : T}
    (hcv : ρ.o c = psi s y z) (hyz : y ≠ z) (hnA : ¬ (s = μ ∧ y = app b (psi (succ μ) z z)))
    (hl : (split y (psi (succ s) z z)).2 = z) :
    (split (fsD y (gamS μ (app b (psi (succ μ) z z)) seed
      (m + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c))) (psi (succ s) z z)).2 = z := by
  have hseedz : seed ≠ z := by obtain ⟨a, X, he⟩ := hseedS; rw [he]; simp
  obtain ⟨_, a', _, hDc⟩ := qr_holeD hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro hox hOS
    true c hdc hc
  simp only [valB, cond_true] at hDc
  rw [hcv] at hDc
  by_cases hyb : y = app b (psi (succ μ) z z)
  · subst hyb
    have hsμ : s ≠ μ := fun h => hnA ⟨h, rfl⟩
    have hsle := diag_here_inv hDc
    have hslt : lt s μ = true := by
      rcases lt_trichotomy' s μ with h | h | h
      · exact h
      · exact absurd h hsμ
      · exact absurd h hsle
    have hdpos := qr_d_pos hx hC hG hKD hTD hq hro hOS hVS hBk hxv hc hdc hcv hsμ
    obtain ⟨k', hk'⟩ : ∃ k', m + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c = k' + 1 :=
      ⟨m + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c - 1, by omega⟩
    rw [hk', gamS_succ_q]
    exact lo_keep_br hb hslt rfl
  · rcases Nat.eq_zero_or_pos (m + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c) with hk0 | hkpos
    · rw [hk0]
      exact hLs c hc hdc (by omega) s y hcv hyb hl
    · obtain ⟨k', hk'⟩ : ∃ k', m + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c = k' + 1 :=
      ⟨m + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c - 1, by omega⟩
      have hDy : DiagAt a' _ μ y := DiagAt.arg_inv hDc hyz (fun h => hyb h.2)
      have hlev : holeLev y = μ := DiagAt.holeLev_eq hDy
      rw [hk']
      refine lo_keep_Q hDc hyz hyb ?_ (gamS_ge_psi1 hseedz k') hl
      intro hl' a hla hns hOa hca
      have := hTPL c (by omega) s y hcv hl' a hla hns hOa hca
      rw [hlev] at this; exact this

variable (hS : ∀ a', ¬ lt μ a' = true → isOT (psi a' (app b (psi (succ μ) z z)) z) = true →
    SeedOK a' (app b (psi (succ μ) z z)) μ seed)
  (hAU' : AbsUW M ρ) (hAD' : AbsDW M ρ)
include hS hAU' hAD'

/-- **`VLocZ` on all `v` calls of `D`** (`t = 1`, `q = r`). -/
theorem qr_vloc (m : Nat) : ∀ i, i < x → DepX M x false i →
    VLocZ M x ρ (zfQ M x (loQ M ρ μ b) (lbQ M ρ μ b) μ (app b (psi (succ μ) z z)) seed m) i := by
  set br := app b (psi (succ μ) z z) with hbrdef
  set lo := loQ M ρ μ b with hlodef
  set lb := lbQ M ρ μ b with hlbdef
  have hrx : r < x := par_lt M 1 x r h1
  have hrM : r < M.length := by omega
  have hrot : isOT (psi μ br z) = true := by rw [← hro]; exact hG.ot_o r hrM
  have hμ : ¬ lt μ μ = true := lt_irrefl' μ
  have hSμ := hS μ hμ hrot
  have hHD := qr_holeD hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro hox hOS
  have hok : ∀ t k, isOT t = true → HoleT μ br μ t →
      isOT (fsD t (gamS μ br seed k)) = true ∧ fsD t (gamS μ br seed k) < t :=
    fun t k hot hH => hok_of_holeT hrot cof_br hμ hS hot hH k
  have hseedz : seed ≠ z := by obtain ⟨a, X, he⟩ := hseedS; rw [he]; simp
  have hgS : ∀ k, ∃ a X, gamS μ br seed k = psi a X z := by
    intro k; cases k with
    | zero => exact hseedS
    | succ k => exact ⟨μ, _, rfl⟩
  have hgot : ∀ k, isOT (gamS μ br seed k) = true := gamS_ot hrot cof_br hμ hSμ
  have hglt : ∀ k, gamS μ br seed k < psi (succ μ) z z := gamS_lt_om hrot cof_br hμ hSμ
  have hgz : ∀ k, gamS μ br seed k ≠ z := gamS_ne_z_q hseedz
  intro i hi hv
  have hiM : i < M.length := by omega
  obtain ⟨h1', hpd, hcase⟩ := hVS i hi hv
  refine ⟨h1', hpd, ?_⟩
  rcases hcase with ⟨h2, hu, hk, hdk⟩ | ⟨h2, L, K, j, k, hch, hjb, hchj, hdk, hKnd, hLnd⟩
  · -- the upgrade frame
    left
    obtain ⟨hHk, a', _, hDk⟩ := hHD false (i + 1) hdk hk
    simp only [valB, cond_false] at hHk hDk
    have hkM : i + 1 < M.length := by omega
    have hVs : Single (last (ρ.v (i + 1))) :=
      ⟨isOT_last (hG.ot_v _ hkM), last_psi_form (holeT_ne_z hHk)⟩
    have hHl := holeT_last_g hHk
    have hDl := hDk.last_g
    have hokl := hok _ (m + dOf M x lo lb (i + 1)) hVs.1 hHl
    refine ⟨i + 1, h2, hu, hk, hdk, ?_, hVs, ?_, le_of_lt hokl.2, ?_⟩
    · unfold zfQ; rw [dOf_upg hx hxv hOS hVS hi h1' h2 hu (by omega) hdk]
    · exact single_fsD hVs.2 (holeT_not_succ hHl)
        (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHl)) (hgS _) hokl.1
    · intro q hq hlt
      have hOl := ohole_of_diag hDl
      have h0 := hAU' i (i + 1) hu hOl (DiagAt.cof_omega hDl) q hq hlt
      exact lt_of_lt_of_le h0 (fsD_mono_eta hOl (one_le_of_ne_z (hgz _)))
  · -- the bump frame
    right
    have hj : j ∈ children M i := by rw [hch]; simp
    have hkj : k ∈ children M j := by rw [hchj]; simp
    have hkx : k < x := hBk i j k hi hv hj hjb hkj hdk
    have hkM : k < M.length := by omega
    obtain ⟨hHk, a', ha', hDk⟩ := hHD true k hdk hkx
    simp only [valB, cond_true] at hHk hDk
    have hBD : BumpData M ρ μ i L K j k := bump_data hC hG hKD hTD h1' h2 hch hjb hchj
    set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
    set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
    set kk := m + dOf M x lo lb k with hkk
    set ζ := gamS μ br seed kk with hζdef
    have hζz : ζ ≠ z := hgz kk
    have hokζ : ∀ t, isOT t = true → HoleT μ br μ t → isOT (fsD t ζ) = true ∧ fsD t ζ < t :=
      fun t hot hH => hok t kk hot hH
    obtain ⟨hfkot, hfklt⟩ := hokζ _ (hG.ot_o k hkM) hHk
    have hfkS : Single (fsD (ρ.o k) ζ) :=
      single_fsD (o_psi_form hC hkM) (holeT_not_succ hHk)
        (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHk)) (hgS kk) hfkot
    have hfkz : fsD (ρ.o k) ζ ≠ z := single_ne_z hfkS
    have hkS : Single (ρ.o k) := hBD.sK _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hGot : isOT G = true := (sumN_dec _ hBD.sK hBD.pK).1
    have hGe : G = app (sumN (K.map ρ.o)) (ρ.o k) := sumN_snoc_dec hBD.sK hBD.pK
    have hDG : DiagAt a' br μ G := by rw [hGe]; exact DiagAt.append _ (single_ne_z hkS) hDk
    have hHG : HoleT μ br μ G := Or.inr ⟨a', ha', hDG⟩
    have hDωG := diag_omega hGot hDG
    have hωGz : omega G ≠ z := single_ne_z (single_omega hGot)
    have hDY2 : DiagAt a' br μ (app (sumN P) (omega G)) := DiagAt.append _ hωGz hDωG
    have hHY2 : HoleT μ br μ (app (sumN P) (omega G)) := Or.inr ⟨a', ha', hDY2⟩
    have hDW := diag_omega hBD.potW hDY2
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
    -- the index of `i`
    have hdb : dOf M x lo lb i = dOf M x lo lb k + lb i j k :=
      dOf_bump hx hxv hOS hVS hi h1' h2 hj hjb hkj hdk
    have hfl : (children M i).filter (fun d => decide (d < j)) = L :=
      filter_lt_split (children_sorted M i) (show children M i = L ++ j :: [] from hch)
    -- the `ω` exchange
    have hωp : fsD (omega (app (sumN P) (omega G))) (zfQ M x lo lb μ br seed m i) =
        omega (app (sumN P) (omega G')) := by
      unfold zfQ
      rw [hdb, ← Nat.add_assoc]
      show fsD _ (gamS μ br seed (kk + lb i j k)) = _
      by_cases hlift : children M j = [k] ∧ ρ.o k = psi μ br z
      · have hK0 : K = [] := by
          have h3 : K ++ [k] = [k] := hchj.symm.trans hlift.1
          have hl := congrArg List.length h3
          simp at hl
          exact hl
        rw [hK0] at hGe hG'e
        have hGA : G = psi μ br z := by rw [hGe, ← hlift.2]; rfl
        have hG'A : G' = fsD (psi μ br z) ζ := by rw [hG'e, hlift.2]; rfl
        rw [hGA, hG'A]
        by_cases hP : sumN P = z
        · have h2' : lb i j k = 2 := by
            rw [hlbdef]; unfold lbQ; rw [if_pos hlift, hfl, if_pos hP]
          rw [h2', hP]
          show fsD (omega (omega (psi μ br z))) (gamS μ br seed (kk + 1 + 1)) =
            omega (omega (fsD (psi μ br z) ζ))
          rw [gamS_succ_q, gamS_succ_q]
          exact omega_lift2 hb hrot hζz (hglt kk) (by rw [← gamS_succ_q]; exact hgot _)
            (by rw [← gamS_succ_q, ← gamS_succ_q]; exact hgot _) (by rw [← gamS_succ_q]; exact hglt _)
        · have h1'' : lb i j k = 1 := by
            rw [hlbdef]; unfold lbQ; rw [if_pos hlift, hfl, if_neg hP]
          rw [h1'', gamS_succ_q]
          have hPA : isOT (app (sumN P) (psi μ br z)) = true := by
            have := hBD.potW
            rw [← hPdef, ← hGdef, hGA, omega_A hb hrot] at this
            exact this
          have hn2 : qnext μ b (qnext μ b ζ) < psi μ br z :=
            qnext_lt_A (by rw [← gamS_succ_q]; exact hglt _)
          apply omega_lift1 hb hP hrot hPA
            (fun h => A_not_lt_E0 hb (lt_trans (lt_app_right hPA hP) h)) hζz (hglt kk)
            (by rw [← gamS_succ_q]; exact hgot _)
          apply isOT_app_of (isOT_app_left hPA) (by rw [← gamS_succ_q, ← gamS_succ_q]; exact hgot _)
          intro q hq
          exact le_trans (le_of_lt hn2) (summands_ge_of_app hPA q hq)
      · have h0 : lb i j k = 0 := by
          rw [hlbdef]; unfold lbQ; rw [if_neg hlift]
        rw [h0, Nat.add_zero]
        have hLG : ∀ s b', G = psi s b' z → b' ≠ z → (split b' (psi (succ s) z z)).2 = z →
            (split (fsD b' ζ) (psi (succ s) z z)).2 = z := by
          intro s b' hGs hb' hl
          have hK0 : sumN (K.map ρ.o) = z := by
            by_contra hK
            exact app_single_ne hK (single_ne_z hkS) (by rw [← hGe]; exact hGs)
          have hok' : ρ.o k = psi s b' z := by rw [← hGs, hGe, hK0]; rfl
          have hnA : ¬ (s = μ ∧ b' = br) := by
            rintro ⟨hs, hbb⟩
            apply hlift
            refine ⟨?_, by rw [hok', hs, hbb]⟩
            have hKn : K = [] := by
              by_contra hKne
              exact sumN_ne_z_of_single (fun t ht => hBD.sK t (List.mem_append_left _ ht))
                (List.pairwise_append.mp hBD.pK).1 (by simpa using hKne) hK0
            rw [hchj, hKn]; rfl
          exact qr_lkeep hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro hox hOS hb hVS
            hBk hxv hseedS hTPL hLs m hkx hdk hok' hb' hnA hl
        have hLY2 : ∀ s b', app (sumN P) (omega G) = psi s b' z → b' ≠ z →
            (split b' (psi (succ s) z z)).2 = z → (split (fsD b' ζ) (psi (succ s) z z)).2 = z := by
          intro s b' hY hb' hl
          have hP0 : sumN P = z := by
            by_contra hP; exact app_single_ne hP hωGz hY
          rw [hP0] at hY
          have hY' : omega G = psi s b' z := hY
          have hfix := omega_single_nolo hGot (DiagAt.ne_z hDG) hY' hl
          exact hLG s b' (by rw [← hfix]; exact hY') hb' hl
        have hωGfs : fsD (omega G) ζ = omega G' := by
          rw [omega_fsD_hole_Q hGot hHG hDG cof_br hζz hokζ hLG, hfG]
        rw [omega_fsD_hole_Q hBD.potW hHY2 hDY2 cof_br hζz hokζ hLY2, fsD_app _ hωGz ζ, hωGfs]
    refine ⟨L, K, j, k, h2, hch, hjb, hchj, hdk, hKnd, hLnd, hfkS, le_of_lt hfklt, hBD.sK, hBD.pK,
      hBD.sL, hBD.pp, ?_, hBD.gt, ?_, hωp, ?_⟩
    · have hpp := hBD.pp
      rw [List.pairwise_append] at hpp ⊢
      refine ⟨hpp.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb; rw [hb]
      exact le_trans hωle (hpp.2.2 a ha _ (List.mem_singleton_self _))
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hBD.gt t (List.mem_append_left _ ht)
      · rw [List.mem_singleton] at ht; rw [ht, ← omega_z]
        exact omega_lt_omega rfl hG'ot (lt_of_le_of_ne (z_le _) (Ne.symm hG'z))
    · intro q hq hlt
      show q < omega (app (sumN P) (omega G'))
      rw [← hωp]
      have hOW : OHole (bumpW M ρ i) := by rw [hBD.W]; exact ohole_of_diag hDW
      have hcW : cof (bumpW M ρ i) = .omega := by rw [hBD.W]; exact DiagAt.cof_omega hDW
      have h0 := hAD' i hiM h1' h2 hOW hcW q hq (by rw [hBD.W]; exact hlt)
      rw [hBD.W] at h0
      exact lt_of_lt_of_le h0 (fsD_mono_eta (ohole_of_diag hDW) (one_le_of_ne_z (hgz _)))

end

end Ytosk
