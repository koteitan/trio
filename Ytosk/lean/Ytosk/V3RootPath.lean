/-
**1 列落としの根の真の減少を、x から根への登り道で直接示す（2026-10-25）。**

`root_drop_X` は DepX の形の補題（x は bump 子でも上がり先でもない、hXu・hXb）を使う。ここでは
`path_upG` と同じ帰納法で、登り道の各列で「o′ < o」を直接示す。登り道の子はその列の最後の子なので、
D のすべての列の形（OShape・dv_shape）は要らない。x の辺は 3 通り:
- x が数える子: `o_strict_frame`。
- x が bump 子: `v_strict_bump_x`（bumpW の末尾の項 1 が消える）。
- x が上がり先: `v_strict_supx`（v(x − 1) = V + ω から V + 1）、そこから x − 1 で登り直す。
上げの迂回の底では、登り道の子のあとに数えない・bump でない子が残るので、`v_strict_bumpT` で扱う。
-/
import Ytosk.V3T2Seed1
import Ytosk.V3T2D
import Ytosk.V3QRWeak

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- Trailing zeros do not change the sum. -/
theorem sumN_append_zs {l : List T} (hl : ∀ t ∈ l, isOT t = true) :
    ∀ zs : List T, (∀ t ∈ zs, t = z) → sumN (l ++ zs) = sumN l
  | [], _ => by simp
  | t :: zs, h => by
    have ht : t = z := h t (by simp)
    subst ht
    rw [show l ++ z :: zs = (l ++ [z]) ++ zs by simp]
    rw [sumN_append_zs (l := l ++ [z]) (fun u hu => by
      rcases List.mem_append.mp hu with hu | hu
      · exact hl u hu
      · simp at hu; rw [hu]; rfl) zs (fun u hu => h u (by simp [hu])), sumN_snoc_z hl]

/-- A later sibling of a column on the path to `d` lies after `d`. -/
theorem sib_after_gt {M : Mat} {t p e d : Nat} (hpt : par M 0 p = some t) (hpd : Anc0 M p d)
    (he : e ∈ children M t) (hpe : p < e) : d < e := by
  by_contra hle
  have hA := anc_between hpd e (by omega) (by omega)
  have hpe' : par M 0 e = some t := (mem_children_iff.mp he).2
  have := (anc0_par hA (by omega) hpe').le
  have := par_lt M 0 p t hpt
  omega

/-- The subtree of an earlier sibling ends before the column. -/
theorem sib_before_lt {M : Mat} {t p d' e : Nat} (hpt : par M 0 p = some t) (hd' : d' ∈ children M t)
    (hdp : d' < p) (he : e ∈ children M d') : e < p := by
  by_contra hle
  have hAe : Anc0 M d' e := Anc0.step (mem_children_iff.mp he).2 (Anc0.refl d')
  have hA := anc_between hAe p (by omega) (by omega)
  have := (anc0_par hA (by omega) hpt).le
  have := par_lt M 0 d' t (mem_children_iff.mp hd').2
  omega

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop

/-- **A strict `v` gives a strict `o`.** -/
theorem o_lt_of_v_lt {i : Nat} (hi : i < x) (h : ρ'.v i < ρ.v i) : ρ'.o i < ρ.o i := by
  have hiT : i < (M.take x).length := by rw [List.length_take]; omega
  have hiM : i < M.length := by omega
  obtain ⟨y', hy'⟩ := o_psi_sub hC' hiT
  obtain ⟨y, hy⟩ := o_psi_sub hC hiM
  rw [hy', hy, sf_ot (hdrop i hi).2.2, sf_ot (hG.ot_v i hiM)]
  exact psi_lt_psi_z_iff.mpr (Or.inl h)

/-- **`v_strict_bump` with trailing non-bump children** after `j`. -/
theorem v_strict_bumpT {i j k : Nat} (hi : i < x) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    {L K R : List Nat} (hch : children M i = L ++ [j] ++ R) (hjb : col M j = bump M i)
    (hR : ∀ e ∈ R, col M e ≠ bump M i)
    (hchj : children M j = K ++ [k]) (hLx : ∀ d ∈ L, ∀ e ∈ children M d, e < x)
    (hIH : k < x → ρ'.o k < ρ.o k) : ρ'.v i < ρ.v i := by
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hiT : i < (M.take x).length := by omega
  have hiM : i < M.length := by omega
  have hoff := chg_off hx hC hG hC' hRk'
  have hjM : j ∈ children M i := by rw [hch]; simp
  have hkM : k ∈ children M j := by rw [hchj]; simp
  have hij := (mem_children hjM).1
  have hjk := (mem_children hkM).1
  have hkl := (mem_children hkM).2
  have hjx : j < x := by omega
  have hV : vOpt ρ' (par (M.take x) 1 i) = vOpt ρ (par M 1 i) := by
    rw [par_take M 1 i hi]
    cases hp : par M 1 i with
    | none => rfl
    | some m =>
      show ρ'.v m = ρ.v m
      have hm := par_lt M 1 i m hp
      apply (hoff m (by omega)).2
      intro hCm
      exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCm).1 rfl (by omega) |>.2.2 i hi hp
  have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  have hLj : ∀ d ∈ L, d < j := (sib_order (children_sorted M i) (R := R) (by rw [hch]; simp)).1
  have hchT : children (M.take x) i = L ++ [j] ++ R.filter (fun d => decide (d < x)) := by
    rw [children_take, hch, List.filter_append, List.filter_append]
    congr 2
    · rw [List.filter_eq_self]
      intro d hd; have := hLj d hd; simp only [decide_eq_true_eq]; omega
    · simp [hjx]
  have hbtL : ∀ d ∈ L, bumpTerm (M.take x) ρ' i d = bumpTerm M ρ i d := by
    intro d hd
    have hdx : d < x := by have := hLj d hd; omega
    have hdM : d ∈ children M i := by rw [hch]; simp [hd]
    have hjT : j ∈ children (M.take x) i := by rw [hchT]; simp
    unfold bumpTerm
    rw [col_take M hdx, bump_take M hi]
    split
    · have hchd : children (M.take x) d = children M d := by
        rw [children_take, List.filter_eq_self]
        intro e he; simp only [decide_eq_true_eq]; exact hLx d hd e he
      rw [hchd]
      congr 2
      apply List.map_congr_left
      intro e he
      have hex := hLx d hd e he
      apply (hoff e hex).1
      intro hCe
      exact chg_only_last hx hR0 hZ2 hSD hZ1 hUAT hUAB h2 hdM hjT (hLj d hd) hCe
        (Anc0.step (mem_children_iff.mp he).2 (Anc0.refl d))
    · rfl
  have hbtR : ∀ t ∈ R.map (bumpTerm M ρ i), t = z := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
    unfold bumpTerm; rw [if_neg (hR e he)]
  have hbtR' : ∀ t ∈ (R.filter (fun d => decide (d < x))).map (bumpTerm (M.take x) ρ' i), t = z := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
    rw [List.mem_filter] at he
    have hex : e < x := by simpa using he.2
    unfold bumpTerm; rw [col_take M hex, bump_take M hi, if_neg (hR e he.1)]
  -- the bump term of `j` drops strictly (as in `v_strict_bump`)
  set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
  have hKk : ∀ d ∈ K, d < k := (sib_order (children_sorted M j) (R := []) (by rw [hchj])).1
  have hKx : ∀ d ∈ K, d < x := fun d hd => by have := hKk d hd; omega
  have hKot : ∀ t ∈ K.map ρ.o, isOT t = true := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o d (by have := hKx d hd; omega)
  have hKot' : ∀ t ∈ K.map ρ'.o, isOT t = true := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact (hdrop d (hKx d hd)).1.2.1
  have hKle : sumN (K.map ρ'.o) ≤ sumN (K.map ρ.o) :=
    sumN_le2 (forall2_map_le (fun d hd => (hdrop d (hKx d hd)).1.le)) hKot' hKot
  have hkot : isOT (ρ.o k) = true := hG.ot_o k hkl
  have hGot : isOT G = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hKot t h
    · simp at h; rw [h]; exact hkot)
  obtain ⟨G', hG'ot, hG'lt, hbtj⟩ : ∃ G', isOT G' = true ∧ G' < G ∧
      bumpTerm (M.take x) ρ' i j = omega G' := by
    have hbt : bumpTerm (M.take x) ρ' i j = omega (sumN ((children (M.take x) j).map ρ'.o)) := by
      unfold bumpTerm; rw [col_take M hjx, bump_take M hi, if_pos hjb]
    rw [hbt]
    by_cases hkx : k < x
    · have hchjT : children (M.take x) j = K ++ [k] := by
        rw [children_take, hchj, List.filter_eq_self]
        intro d hd
        rcases List.mem_append.mp hd with h | h
        · simp only [decide_eq_true_eq]; exact hKx d h
        · simp at h; subst h; simp only [decide_eq_true_eq]; exact hkx
      have hk' : isOT (ρ'.o k) = true := (hdrop k hkx).1.2.1
      refine ⟨_, ?_, ?_, rfl⟩
      · rw [hchjT, List.map_append, List.map_singleton]
        exact isOT_sumN _ (fun t ht => by
          rcases List.mem_append.mp ht with h | h
          · exact hKot' t h
          · simp at h; rw [h]; exact hk')
      · rw [hchjT, List.map_append, List.map_singleton]
        exact sumN_snoc_lt hKot' hKot hk' hkot hKle (hIH hkx)
    · have hkx' : k = x := by omega
      have hchjT : children (M.take x) j = K := by
        rw [children_take, hchj, List.filter_append, List.filter_eq_self.mpr
          (fun d hd => by simp only [decide_eq_true_eq]; exact hKx d hd)]
        simp [hkx']
      refine ⟨_, ?_, ?_, rfl⟩
      · rw [hchjT]; exact isOT_sumN _ hKot'
      · rw [hchjT]
        exact sumN_lt_snoc hKot hkot hKle (by
          obtain ⟨s0, y0, h0⟩ := o_psi_form hC hkl; rw [h0]; exact T.z_lt_psi _ _ _)
  -- assemble
  set Pl := one :: L.map (bumpTerm M ρ i) with hPl
  have hPlot : ∀ t ∈ Pl, isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i d
  have hbtjM : bumpTerm M ρ i j = omega G := by
    unfold bumpTerm; rw [if_pos hjb, hchj, List.map_append, List.map_singleton]
  have hPGot : ∀ t ∈ Pl ++ [omega G], isOT t = true := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPlot t h
    · simp at h; rw [h]; exact isOT_omega hGot
  have hPG'ot : ∀ t ∈ Pl ++ [omega G'], isOT t = true := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPlot t h
    · simp at h; rw [h]; exact isOT_omega hG'ot
  have hvM : ρ.v i = sf (add (vOpt ρ (par M 1 i)) (omega (sumN (Pl ++ [omega G])))) := by
    rw [(hC i hiM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, hch, List.map_append, List.map_append, List.map_singleton, hbtjM,
      ← List.cons_append, ← List.cons_append, sumN_append_zs hPGot _ hbtR]
  have hvT : ρ'.v i = sf (add (vOpt ρ (par M 1 i)) (omega (sumN (Pl ++ [omega G'])))) := by
    rw [(hC' i hiT).2]; unfold vRhs
    rw [entry_take M 1 hi, entry_take M 2 hi, if_neg h1, if_neg h2, hV, hchT, List.map_append, List.map_append,
      List.map_singleton, hbtj, List.map_congr_left hbtL, ← List.cons_append, ← List.cons_append,
      sumN_append_zs hPG'ot _ hbtR']
  have hP'ot : isOT (sumN (Pl ++ [omega G'])) = true := isOT_sumN _ hPG'ot
  have hPot : isOT (sumN (Pl ++ [omega G])) = true := isOT_sumN _ hPGot
  have hP : sumN (Pl ++ [omega G']) < sumN (Pl ++ [omega G]) :=
    sumN_snoc_lt hPlot hPlot (isOT_omega hG'ot) (isOT_omega hGot) (le_refl _)
      (omega_lt_omega hG'ot hGot hG'lt)
  rw [hvM, hvT, sf_ot (isOT_add hVot (isOT_omega hP'ot)), sf_ot (isOT_add hVot (isOT_omega hPot))]
  exact add_lt_add_left _ (omega_lt_omega hP'ot hPot hP)

/-- **`x − 1` loses its upgrade to `x`**: `v(x − 1) = v(x) = V + ω` and `v′(x − 1) = V + 1`. -/
theorem v_strict_supx (hu : upg M (x - 1) = some x) : ρ'.v (x - 1) < ρ.v (x - 1) := by
  have hx1 : 0 < x := by have := upg_succ_lt hu; omega
  have hiM : x - 1 < M.length := by omega
  have hxM : x < M.length := by omega
  obtain ⟨he1, he2'⟩ := upg_e12 hu
  have he2 : entry M 2 (x - 1) = 0 := by have := hZ2 (x - 1); omega
  obtain ⟨m, hm1, hm2, hcol, _⟩ := upg_spec hu
  have hVot : isOT (vOpt ρ (par M 1 (x - 1))) = true := by
    rw [hm1]; exact hG.ot_v m (by have := par_lt M 1 (x - 1) m hm1; omega)
  have hxc : children M x = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro c hc; have := mem_children hc; omega
  have ev : ρ.v (x - 1) = ρ.v x :=
    v_upg_eq hC hiM he1 he2 hu hVot (fun _ hj _ _ _ => by rw [hxc] at hj; simp at hj)
  have hx1e : entry M 1 x ≠ 0 := by
    have : entry M 1 x = (col M x).2.1 := rfl
    rw [this, hcol]; exact he1
  have hx2e : entry M 2 x ≠ 0 := by have := upg_target_e2 hu; omega
  have evx : ρ.v x = add (vOpt ρ (par M 1 (x - 1))) (psi z one z) := by
    rw [(hC x hxM).2]; unfold vRhs
    rw [if_neg hx1e, if_neg hx2e, hxc, hm2, ← hm1]
    simp only [List.map_nil]
    rw [sumN_singleton (t := one) ⟨rfl, z, z, rfl⟩, omega_small one_lt_E0]
    exact sf_ot (isOT_add hVot rfl)
  have ev' := v_last_take (x := x) hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' (r := x - 1) (by omega) he1 he2
  rw [sf_ot (isOT_add hVot isOT_one)] at ev'
  rw [ev', ev, evx]
  exact add_lt_add_left _ (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, T.z_lt_psi _ _ _⟩))

/-- **Up the path to `d`, `o` drops strictly** (the strict form of `path_upG`, with any last column `x`). The children
of `a` after the path are neither counted nor bump children (`htr`); above `a` the subtrees end at `d`. -/
theorem path_strict (hR12 : R12 M) (hBE : BumpE2 M) (n : Nat) : ∀ a d, d - a ≤ n → d ≤ x → Anc0 M a d →
    (d < x → ∀ p, ((∃ t, par M 0 p = some t ∧ col M p = bump M t) ∨ isUpg M p = true) → p ≠ d) →
    (d < x → ρ'.o d < ρ.o d) →
    (∀ t, a < t → Anc0 M t d → ¬ Anc0 M t (d + 1)) →
    (∀ e ∈ children M a, d < e → ¬ Counted M a e ∧ col M e ≠ bump M a) →
    a < x → ρ'.o a < ρ.o a := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro a d hn hdx had hd2 hD hend htr
  have hdl : d < M.length := by omega
  have key : ∀ m t, d - t ≤ m → Anc0 M a t → Anc0 M t d → t < x → ρ'.o t < ρ.o t := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
    intro t hm hat htd htx
    by_cases htd' : t = d
    · subst htd'; exact hD htx
    obtain ⟨p, hpt, hpd⟩ := anc0_child htd htd'
    have htp := par_lt M 0 p t hpt
    have hpdl := hpd.le
    have hpl : p < M.length := by omega
    have hpM : p ∈ children M t := mem_children_iff.mpr ⟨hpl, hpt⟩
    have hat' := hat.le
    have hap : Anc0 M a p := Anc0.trans hat (Anc0.step hpt (Anc0.refl t))
    have ihp : ∀ q, Anc0 M a q → Anc0 M q d → p ≤ q → q < x → ρ'.o q < ρ.o q :=
      fun q haq hqd hpq hqx => ihm (d - q) (by omega) q (Nat.le_refl _) haq hqd hqx
    -- the children of `t` after `p` are neither counted nor bump children
    have hT : ∀ e ∈ children M t, p < e → ¬ Counted M t e ∧ col M e ≠ bump M t := by
      intro e he hpe
      have hde := sib_after_gt hpt hpd he hpe
      rcases Nat.eq_or_lt_of_le hat' with heq | hlt
      · subst heq; exact htr e he hde
      · exfalso
        have hAe : Anc0 M t e := Anc0.step (mem_children_iff.mp he).2 (Anc0.refl t)
        exact hend t hlt htd (anc_between hAe (d + 1) (by omega) (by omega))
    obtain ⟨L, R, hLR⟩ := List.append_of_mem hpM
    obtain ⟨hLp, hRp⟩ := sib_order (children_sorted M t) hLR
    have hchT : children M t = L ++ [p] ++ R := by rw [hLR]; simp
    have hLx : ∀ d' ∈ L, ∀ e ∈ children M d', e < x := fun d' hd' e he => by
      have hd'M : d' ∈ children M t := by rw [hLR]; simp [hd']
      have := sib_before_lt hpt hd'M (hLp d' hd') he
      omega
    by_cases hc : Counted M t p
    · -- a counted edge: `p` is the last counted child
      have hpCL : p ∈ CL M t := by unfold CL; exact List.mem_filter.mpr ⟨hpM, by simpa using hc⟩
      refine o_strict_frame hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop htx hpCL (fun e he => ?_)
        (fun hpx => ihp p hap hpd (le_refl _) hpx)
      have heM : e ∈ children M t := (List.mem_filter.mp he).1
      have hec : Counted M t e := by simpa using (List.mem_filter.mp he).2
      by_contra hlt
      exact (hT e heM (by omega)).1 hec
    by_cases hb : col M p = bump M t
    · -- a bump edge
      have hp2 : entry M 2 p = 1 := e2_of_col (show col M p = (entry M 0 t + 1, entry M 1 t, 1) from hb)
      have he1 : entry M 1 t ≠ 0 := by
        have h1 : entry M 1 p = entry M 1 t :=
          e1_of_col (show col M p = (entry M 0 t + 1, entry M 1 t, 1) from hb)
        intro h0
        rw [← h1] at h0
        have := hR12 p h0
        omega
      have he2 : entry M 2 t ≠ 0 := by rw [hBE t p hpM hb]; omega
      apply o_lt_of_v_lt hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop htx
      by_cases hpd' : p = d
      · -- `p = x` is the bump child
        have hdx' : d = x := by
          rcases Nat.lt_or_ge d x with h | h
          · exact absurd hpd' (hd2 h p (Or.inl ⟨t, hpt, hb⟩))
          · omega
        subst hpd'
        rw [hdx'] at hpM hb
        exact v_strict_bump_x hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop htx he1 he2
          (children_split_x hx hpM) hb
      obtain ⟨p', hpp', hp'd⟩ := anc0_child hpd hpd'
      have hp'dl := hp'd.le
      have hpp'lt := par_lt M 0 p' p hpp'
      obtain ⟨K, hK⟩ := List.getLast?_eq_some_iff.mp (last_child_path hdl hpp' hp'd (hend p (by omega) hpd))
      exact v_strict_bumpT hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop htx he1 he2 hchT hb
        (fun e he => (hT e (by rw [hLR] at hpM ⊢; simp [he]) (hRp e he)).2) hK hLx
        (fun hp'x => ihp p' (Anc0.trans hap (Anc0.step hpp' (Anc0.refl p))) hp'd (by omega) hp'x)
    -- an upgraded, topped child: around through `p − 1`
    obtain ⟨hiu, htop⟩ := (not_counted_iff hc).resolve_left hb
    have hiu0 := hiu
    unfold isUpg at hiu
    rw [List.any_eq_true] at hiu
    obtain ⟨k0, _, hk0⟩ := hiu
    have hu : upg M k0 = some p := of_decide_eq_true hk0
    have hk0p : k0 = p - 1 := by
      obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
      rcases hcase with h | ⟨hA, hlt⟩
      · omega
      · exfalso
        have := hUAT k0 p hu (by have := hA.le; omega)
        rw [this] at htop; cases htop
    rw [hk0p] at hu
    have hp0 : 0 < p := by omega
    obtain ⟨he1u, he2u⟩ := upg_e12 hu
    have he2z : entry M 2 (p - 1) = 0 := by have := hZ2 (p - 1); omega
    -- `o′(p − 1) < o(p − 1)`
    have hs1 : ρ'.o (p - 1) < ρ.o (p - 1) := by
      by_cases hpd' : p = d
      · have hdx' : d = x := by
          rcases Nat.lt_or_ge d x with h | h
          · exact absurd hpd' (hd2 h p (Or.inr hiu0))
          · omega
        subst hpd'
        rw [hdx'] at hu ⊢
        exact o_lt_of_v_lt hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop (by omega)
          (v_strict_supx hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hu)
      have hpx : p < x := by omega
      obtain ⟨m0, hm1, hm2, hcol, _⟩ := upg_spec hu
      have hp2 : entry M 2 p ≠ 0 := by have := upg_target_e2 hu; omega
      have hp1 : entry M 1 p ≠ 0 := by
        have : entry M 1 p = (col M p).2.1 := rfl
        rw [this, hcol]; exact he1u
      obtain ⟨p', hpp', hp'd⟩ := anc0_child hpd hpd'
      have hp'dl := hp'd.le
      have hpp'lt := par_lt M 0 p' p hpp'
      have hlast := last_child_path hdl hpp' hp'd (hend p (by omega) hpd)
      have htop' := htop
      unfold topped at htop'
      rw [hlast] at htop'
      have hb' : col M p' = bump M p := by simpa using htop'
      obtain ⟨K', hK'⟩ := List.getLast?_eq_some_iff.mp hlast
      have hK'x : ∀ d' ∈ K', ∀ e ∈ children M d', e < x := fun d' hd' e he => by
        have hd'M : d' ∈ children M p := by rw [hK']; simp [hd']
        have hd'p' : d' < p' := (sib_order (children_sorted M p) (R := []) (by rw [hK'])).1 d' hd'
        have := sib_before_lt hpp' hd'M hd'p' he
        omega
      have hvp : ρ'.v p < ρ.v p := by
        by_cases hp'd' : p' = d
        · have hdx' : d = x := by
            rcases Nat.lt_or_ge d x with h | h
            · exact absurd hp'd' (hd2 h p' (Or.inl ⟨p, hpp', hb'⟩))
            · omega
          rw [hp'd', hdx'] at hK' hb'
          exact v_strict_bump_x hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hpx hp1 hp2 hK' hb'
        obtain ⟨p'', hpp'', hp''d⟩ := anc0_child hp'd hp'd'
        have hp''dl := hp''d.le
        have hpp''lt := par_lt M 0 p'' p' hpp''
        obtain ⟨K, hK⟩ := List.getLast?_eq_some_iff.mp
          (last_child_path hdl hpp'' hp''d (hend p' (by omega) hp'd))
        exact v_strict_bump hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hpx hp1 hp2 hK' hb' hK hK'x
          (fun hp''x => ihp p'' (Anc0.trans hap (Anc0.step hpp'' (Anc0.step hpp' (Anc0.refl p))))
            hp''d (by omega) hp''x)
      -- `v(p − 1) = v(p)` in `M` and in `M.take x`
      have hiM : p - 1 < M.length := by omega
      have hiT : p - 1 < (M.take x).length := by rw [List.length_take]; omega
      have hmi := par_lt M 1 (p - 1) m0 hm1
      have hVot : isOT (vOpt ρ (par M 1 (p - 1))) = true := by rw [hm1]; exact hG.ot_v m0 (by omega)
      have ek : ρ.v (p - 1) = ρ.v p :=
        v_upg_eq hC hiM he1u he2z hu hVot (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
      have huT : upg (M.take x) (p - 1) = some p := by rw [upg_take M (by omega)]; exact hu
      have ek' : ρ'.v (p - 1) = ρ'.v p := v_upg_eq hC' hiT (by rw [entry_take M 1 (by omega)]; exact he1u)
        (by rw [entry_take M 2 (by omega)]; exact he2z) huT
        (by rw [par_take M 1 (p - 1) (by omega), hm1]; exact (hdrop m0 (by omega)).2.2)
        (fun _ _ _ k' hk' => (hdrop k' (by have := (mem_children hk').2; rw [List.length_take] at this; omega)).1.2.1)
      apply o_lt_of_v_lt hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop (by omega)
      rw [ek, ek']; exact hvp
    by_cases ht1 : t = p - 1
    · rw [ht1]; exact hs1
    have hpd2 : p ≤ d := hpdl
    have hAt : Anc0 M t (p - 1) :=
      anc_between (Anc0.step hpt (Anc0.refl t)) (p - 1) (by omega) (by omega)
    refine ihn ((p - 1) - t) (by omega) t (p - 1) (Nat.le_refl _) (by omega) hAt
      (fun _ => ne_of_e2z he2z) (fun _ => hs1) ?_ ?_ htx
    · intro u htu hup hup'
      rw [show p - 1 + 1 = p by omega] at hup'
      by_cases hup2 : u = p
      · have := hup.le; omega
      · have := (anc0_par hup' hup2 hpt).le; omega
    · intro e he hpe
      rcases Nat.eq_or_lt_of_le (show p ≤ e by omega) with heq | hlt
      · subst heq; exact ⟨hc, hb⟩
      · exact hT e he hlt
  exact key (d - a) a (Nat.le_refl _) (Anc0.refl a) had

end

end Ytosk
