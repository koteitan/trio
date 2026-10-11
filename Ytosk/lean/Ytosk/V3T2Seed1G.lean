/-
**3 行・t = 2: 部分木の右端で v が真に下がると、その祖先の o も真に下がる（seed1 の残り sv・C）。**

x = M.length − 1、M′ = M.take x、ρ′ = drop1 M x rk。e < x で v′(e) < v(e)、e の行 2 は 0。
c が a の子で e が c の部分木の最後の列、c より後の a の子は数えず bump でもないとき、o′(a) < o(a)
（`strict_up`、e − a についての強い帰納法）。段 (a, c) の種類で分ける（C′ 6 万行列の実測: 鎖の中は (i)・(ii)、
(iii) は最上段だけで、そのとき直前の兄弟は数える子）:
- (i) c が数える子: o′(c) < o(c) から o_strict_frame。
- (ii) c が bump 子: c の最後の子 k の o′(k) < o(k) から v′(a) < v(a)（`v_strict_bump_R`）、よって o′(a) < o(a)。
- (iii) c が上げの的（isUpg ∧ topped）: upg(c − 1) = c（UAT）。c の最後の子 j は bump 子なので v′(c) < v(c)、
  v(c − 1) = v(c)（v_upg_eq）で v′(c − 1) < v(c − 1)。c − 1 は c の直前の兄弟 d の部分木の最後の列なので、
  (a, d, c − 1) に帰納法を使う。
-/
import Ytosk.V3T2Seed1
import Ytosk.V3T0V

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- `e` is the last column of the subtree of `c`. -/
def SubLast (M : Mat) (c e : Nat) : Prop := Anc0 M c e ∧ ∀ j, Anc0 M c j → j ≤ e

theorem subLast_child {M : Mat} {c e : Nat} (h : SubLast M c e) (hce : c ≠ e) :
    ∃ L c', children M c = L ++ [c'] ∧ SubLast M c' e := by
  obtain ⟨c1, hp1, hA1⟩ := anc0_child h.1 hce
  have hc1 : c1 ∈ children M c := mem_children_iff.mpr
    ⟨anc0_lt_len (Anc0.step hp1 (Anc0.refl c)) (by have := par_lt M 0 c1 c hp1; omega), hp1⟩
  obtain ⟨L, R, hch⟩ := List.append_of_mem hc1
  have hR : R = [] := by
    rcases List.eq_nil_or_concat R with h0 | ⟨R', d, hd⟩
    · exact h0
    · exfalso
      have hdM : d ∈ children M c := by rw [hch, hd]; simp
      have hc1d : c1 < d := (sib_order (children_sorted M c) hch).2 d (by rw [hd]; simp)
      have hde : d ≤ e := h.2 d (Anc0.step (mem_children_iff.mp hdM).2 (Anc0.refl c))
      have hA1d : Anc0 M c1 d := anc_between hA1 d (by omega) (by
        rcases Nat.lt_or_ge e d with h' | h'
        · omega
        · exact h')
      have := par0_ge_of_anc hA1d hc1d (le_refl d) (mem_children_iff.mp hdM).2
      have := (mem_children hc1).1; omega
  subst hR
  exact ⟨L, c1, hch, hA1, fun j hj => h.2 j (Anc0.trans (Anc0.step hp1 (Anc0.refl c)) hj)⟩

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop

/-- **The `v` frame of a bump column is strict**, with non-bump children after the bump child `j`. -/
theorem v_strict_bump_R {i j k : Nat} (hi : i < x) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    {L R K : List Nat} (hch : children M i = L ++ j :: R) (hjb : col M j = bump M i)
    (hRb : ∀ d ∈ R, col M d ≠ bump M i)
    (hchj : children M j = K ++ [k]) (hkx : k < x) (hLx : ∀ d ∈ L, ∀ e ∈ children M d, e < x)
    (hIH : ρ'.o k < ρ.o k) : ρ'.v i < ρ.v i := by
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
  have hLj : ∀ d ∈ L, d < j := (sib_order (children_sorted M i) hch).1
  have hjT : j ∈ children (M.take x) i := by
    rw [children_take, List.mem_filter]; exact ⟨hjM, by simpa using hjx⟩
  have hchT : children (M.take x) i = L ++ j :: R.filter (fun d => decide (d < x)) := by
    rw [children_take, hch, List.filter_append, List.filter_cons]
    rw [List.filter_eq_self.mpr (fun d hd => by have := hLj d hd; simp only [decide_eq_true_eq]; omega)]
    simp [hjx]
  have hbtL : ∀ d ∈ L, bumpTerm (M.take x) ρ' i d = bumpTerm M ρ i d := by
    intro d hd
    have hdx : d < x := by have := hLj d hd; omega
    have hdM : d ∈ children M i := by rw [hch]; simp [hd]
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
  have hRz : ∀ t ∈ R.map (bumpTerm M ρ i), t = z := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    unfold bumpTerm; rw [if_neg (hRb d hd)]
  have hRz' : ∀ t ∈ (R.filter (fun d => decide (d < x))).map (bumpTerm (M.take x) ρ' i), t = z := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    have hd' := List.mem_filter.mp hd
    have hdx : d < x := by simpa using hd'.2
    unfold bumpTerm; rw [col_take M hdx, bump_take M hi, if_neg (hRb d hd'.1)]
  set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
  have hKk : ∀ d ∈ K, d < k := (sib_order (children_sorted M j) (R := []) (by rw [hchj])).1
  have hKx : ∀ d ∈ K, d < x := fun d hd => by have := hKk d hd; omega
  have hKot : ∀ t ∈ K.map ρ.o, isOT t = true := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact hG.ot_o d (by have := hKx d hd; omega)
  have hKot' : ∀ t ∈ K.map ρ'.o, isOT t = true := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact (hdrop d (hKx d hd)).1.2.1
  have hKle : sumN (K.map ρ'.o) ≤ sumN (K.map ρ.o) := by
    exact sumN_le2 (forall2_map_le (fun d hd => (hdrop d (hKx d hd)).1.le)) hKot' hKot
  have hkot : isOT (ρ.o k) = true := hG.ot_o k hkl
  have hGot : isOT G = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hKot t h
    · simp at h; rw [h]; exact hkot)
  have hchjT : children (M.take x) j = K ++ [k] := by
    rw [children_take, hchj, List.filter_eq_self]
    intro d hd
    rcases List.mem_append.mp hd with h | h
    · simp only [decide_eq_true_eq]; exact hKx d h
    · simp at h; subst h; simp only [decide_eq_true_eq]; exact hkx
  have hk' : isOT (ρ'.o k) = true := (hdrop k hkx).1.2.1
  set G' := sumN (K.map ρ'.o ++ [ρ'.o k]) with hG'def
  have hG'ot : isOT G' = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hKot' t h
    · simp at h; rw [h]; exact hk')
  have hG'lt : G' < G := sumN_snoc_lt hKot' hKot hk' hkot hKle hIH
  have hbtj : bumpTerm (M.take x) ρ' i j = omega G' := by
    unfold bumpTerm; rw [col_take M hjx, bump_take M hi, if_pos hjb, hchjT, List.map_append,
      List.map_singleton]
  have hbtjM : bumpTerm M ρ i j = omega G := by
    unfold bumpTerm; rw [if_pos hjb, hchj, List.map_append, List.map_singleton]
  set Pl := one :: L.map (bumpTerm M ρ i) with hPl
  have hPlot : ∀ t ∈ Pl, isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i d
  have hP'ot : isOT (sumN (Pl ++ [omega G'])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPlot t h
    · simp at h; rw [h]; exact isOT_omega hG'ot)
  have hPot : isOT (sumN (Pl ++ [omega G])) = true := isOT_sumN _ (fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPlot t h
    · simp at h; rw [h]; exact isOT_omega hGot)
  have hPlGot : ∀ t ∈ Pl ++ [omega G], isOT t = true := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPlot t h
    · simp at h; rw [h]; exact isOT_omega hGot
  have hPlG'ot : ∀ t ∈ Pl ++ [omega G'], isOT t = true := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hPlot t h
    · simp at h; rw [h]; exact isOT_omega hG'ot
  have hvM : ρ.v i = sf (add (vOpt ρ (par M 1 i)) (omega (sumN (Pl ++ [omega G])))) := by
    rw [(hC i hiM).2]; unfold vRhs
    rw [if_neg h1, if_neg h2, hch, List.map_append, List.map_cons, hbtjM]
    rw [show one :: (L.map (bumpTerm M ρ i) ++ omega G :: R.map (bumpTerm M ρ i)) =
      (Pl ++ [omega G]) ++ R.map (bumpTerm M ρ i) by simp [hPl]]
    rw [sumN_append_zeros hPlGot _ hRz]
  have hvT : ρ'.v i = sf (add (vOpt ρ (par M 1 i)) (omega (sumN (Pl ++ [omega G'])))) := by
    rw [(hC' i hiT).2]; unfold vRhs
    rw [entry_take M 1 hi, entry_take M 2 hi, if_neg h1, if_neg h2, hV, hchT, List.map_append, List.map_cons,
      hbtj, List.map_congr_left hbtL]
    rw [show one :: (L.map (bumpTerm M ρ i) ++ omega G' ::
        (R.filter (fun d => decide (d < x))).map (bumpTerm (M.take x) ρ' i)) =
      (Pl ++ [omega G']) ++ (R.filter (fun d => decide (d < x))).map (bumpTerm (M.take x) ρ' i) by simp [hPl]]
    rw [sumN_append_zeros hPlG'ot _ hRz']
  have hP : sumN (Pl ++ [omega G']) < sumN (Pl ++ [omega G]) :=
    sumN_snoc_lt hPlot hPlot (isOT_omega hG'ot) (isOT_omega hGot) (le_refl _)
      (omega_lt_omega hG'ot hGot hG'lt)
  rw [hvM, hvT, sf_ot (isOT_add hVot (isOT_omega hP'ot)), sf_ot (isOT_add hVot (isOT_omega hPot))]
  exact add_lt_add_left _ (omega_lt_omega hP'ot hPot hP)

/-- A drop of `v` gives a drop of `o`. -/
theorem ov_strict (hG' : Good3 (M.take x) ρ') {a : Nat} (ha : a < x) (hv : ρ'.v a < ρ.v a) :
    ρ'.o a < ρ.o a := by
  rw [o_cl_eq hC' hG' (by rw [List.length_take]; omega), o_cl_eq hC hG (by omega)]
  exact psi_lt_psi_z_iff.mpr (Or.inl hv)

/-- **Strictness up the right end of a subtree.** -/
theorem strict_up (hG' : Good3 (M.take x) ρ') (hBE : BumpE2 M) (hR12 : R12 M) :
    ∀ m a c e, e - a < m → e < x → entry M 2 e = 0 → ρ'.v e < ρ.v e → c ∈ children M a →
      SubLast M c e → (∀ d ∈ children M a, c < d → ¬ Counted M a d ∧ col M d ≠ bump M a) →
      (∀ t, par M 0 x = some t → ¬ (a < t ∧ t ≤ e)) → ρ'.o a < ρ.o a := by
  intro m
  induction m with
  | zero => intro a c e h; omega
  | succ m ih =>
    intro a c e hm hex he2 hve hc hSL hafter hxo
    have hac : a < c := (mem_children hc).1
    have hce : c ≤ e := hSL.2 c (Anc0.refl c)
    have hax : a < x := by omega
    have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
    have hlx : ∀ d e', a < d → d ≤ e → e' ∈ children M d → e' < x := by
      intro d e' h1 h2 he'
      have := (mem_children he').2
      rcases Nat.lt_or_ge e' x with h | h
      · exact h
      · exfalso
        have hx' : e' = x := by omega
        rw [hx'] at he'
        exact hxo d (mem_children_iff.mp he').2 ⟨h1, h2⟩
    -- columns in `(a, e]` whose subtree ends at `e`
    have FC : ∀ c', a < c' → SubLast M c' e → ρ'.o c' < ρ.o c' := by
      intro c' hac' hSL'
      have hc'e : c' ≤ e := hSL'.2 c' (Anc0.refl c')
      by_cases hce' : c' = e
      · rw [hce']; exact ov_strict hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hG' hex hve
      · obtain ⟨L', c'', hch', hSL''⟩ := subLast_child hSL' hce'
        apply ih c' c'' e (by omega) hex he2 hve (by rw [hch']; simp) hSL''
        · intro d hd hlt
          exfalso
          rw [hch'] at hd
          rcases List.mem_append.mp hd with h | h
          · have := (sib_order (children_sorted M c') (R := []) (by rw [hch'])).1 d h; omega
          · simp at h; omega
        · intro t ht ⟨h1, h2⟩; exact hxo t ht ⟨by omega, h2⟩
    by_cases hcnt : Counted M a c
    · -- (i) a counted child
      have hcCL : c ∈ CL M a := by unfold CL; exact List.mem_filter.mpr ⟨hc, by simpa using hcnt⟩
      apply o_strict_frame hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hax hcCL
      · intro d hd
        by_contra hlt
        have hdc := cl_mem_children hd
        have hcd : Counted M a d := by simpa using (List.mem_filter.mp hd).2
        exact (hafter d hdc (by omega)).1 hcd
      · exact fun _ => FC c hac hSL
    · by_cases hcb : col M c = bump M a
      · -- (ii) a bump child
        have he2c : entry M 2 c = 1 := e2_of_col (show col M c = (entry M 0 a + 1, entry M 1 a, 1) from hcb)
        have hce' : c ≠ e := fun h => by rw [h] at he2c; omega
        obtain ⟨K, k, hchc, hSLk⟩ := subLast_child hSL hce'
        have hkc : k ∈ children M c := by rw [hchc]; simp
        have hFk := FC k (by have := (mem_children hkc).1; omega) hSLk
        have h2a : entry M 2 a ≠ 0 := by have := hBE a c hc hcb; omega
        have h1a : entry M 1 a ≠ 0 := fun h => h2a (hR12 a h)
        obtain ⟨L, R, hch⟩ := List.append_of_mem hc
        have hv := v_strict_bump_R hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hax h1a h2a hch hcb
          (fun d hd => (hafter d (by rw [hch]; simp [hd]) ((sib_order (children_sorted M a) hch).2 d hd)).2)
          hchc (by have := hSLk.2 k (Anc0.refl k); omega)
          (fun d hd e' he' => hlx d e' (mem_children (show d ∈ children M a by rw [hch]; simp [hd])).1
            (by have := (sib_order (children_sorted M a) hch).1 d hd; omega) he') hFk
        exact ov_strict hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hG' hax hv
      · -- (iii) an upgrade target: `c − 1` upgrades to `c`
        have hupT : isUpg M c = true ∧ topped M c = true := by
          by_contra hn; exact hcnt ⟨hcb, hn⟩
        have hup := hupT.1
        unfold isUpg at hup
        obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hup
        have hk0' : upg M k0 = some c := of_decide_eq_true hk0
        have hck : c = k0 + 1 := by
          by_contra hne
          have := hUAT k0 c hk0' hne; rw [hupT.2] at this; cases this
        have he2c : 1 ≤ entry M 2 c := upg_target_e2 hk0'
        have hce' : c ≠ e := fun h => by rw [h] at he2c; omega
        obtain ⟨Lc, j, hchc, hSLj⟩ := subLast_child hSL hce'
        have hjc : j ∈ children M c := by rw [hchc]; simp
        have hjb : col M j = bump M c := by
          have ht := hupT.2
          unfold topped at ht
          rw [hchc, List.getLast?_append] at ht
          simpa using ht
        have he2j : entry M 2 j = 1 := e2_of_col (show col M j = (entry M 0 c + 1, entry M 1 c, 1) from hjb)
        have hje : j ≠ e := fun h => by rw [h] at he2j; omega
        obtain ⟨K, k, hchj, hSLk⟩ := subLast_child hSLj hje
        have hkj : k ∈ children M j := by rw [hchj]; simp
        have hcj := (mem_children hjc).1
        have hjk := (mem_children hkj).1
        have hFk := FC k (by omega) hSLk
        have h2c : entry M 2 c ≠ 0 := by have := hBE c j hjc hjb; omega
        have h1c : entry M 1 c ≠ 0 := fun h => h2c (hR12 c h)
        have hvc : ρ'.v c < ρ.v c :=
          v_strict_bump_R hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop (by omega) h1c h2c (R := [])
            (by rw [hchc]) hjb (by simp) hchj (by have := hSLk.2 k (Anc0.refl k); omega)
            (fun d hd e' he' => hlx d e'
              (by have := (mem_children (show d ∈ children M c by rw [hchc]; simp [hd])).1; omega)
              (by have := (sib_order (children_sorted M c) (R := []) (by rw [hchc])).1 d hd
                  have := hSLj.2 j (Anc0.refl j); omega) he') hFk
        -- `v(c − 1) = v(c)` on both sides
        have hk0x : k0 + 1 < x := by omega
        obtain ⟨h1s, h2s'⟩ := upg_e12 hk0'
        have h2s : entry M 2 k0 = 0 := by have := hZ2 k0; omega
        have hVot : isOT (vOpt ρ (par M 1 k0)) = true := by
          cases hp : par M 1 k0 with
          | none => rfl
          | some m' => exact hG.ot_v m' (by have := par_lt M 1 k0 m' hp; omega)
        have ek : ρ.v k0 = ρ.v c := v_upg_eq hC (by omega) h1s h2s hk0' hVot
          (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
        have hk0T : k0 < (M.take x).length := by omega
        have huT : upg (M.take x) k0 = some c := by rw [upg_take M hk0x]; exact hk0'
        have hVot' : isOT (vOpt ρ' (par (M.take x) 1 k0)) = true := by
          cases hp : par (M.take x) 1 k0 with
          | none => rfl
          | some m' => exact hG'.ot_v m' (by have := par_lt (M.take x) 1 k0 m' hp; omega)
        have ek' : ρ'.v k0 = ρ'.v c := v_upg_eq hC' hk0T (by rw [entry_take M 1 (by omega)]; exact h1s)
          (by rw [entry_take M 2 (by omega)]; exact h2s) huT hVot'
          (fun _ _ _ k' hk' => hG'.ot_o k' (mem_children hk').2)
        have hvs : ρ'.v k0 < ρ.v k0 := by rw [ek, ek']; exact hvc
        -- `c − 1` is not `a`
        have hpc : par M 0 c = some a := (mem_children_iff.mp hc).2
        have hk0a : k0 ≠ a := by
          intro h
          obtain ⟨m', hm1, _, hcol, _⟩ := upg_spec hk0'
          have hmA := anc0_of_par M 1 m' k0 hm1
          have hmlt := par_lt M 1 k0 m' hm1
          have hme := anc0_e0_lt hmA (by omega)
          have h0 : entry M 0 c = entry M 0 m' + 1 := by
            rw [col_eq_entries] at hcol; exact (Prod.mk.inj hcol).1
          have h0' := hR0 _ _ hpc
          rw [h] at hme
          omega
        have hak0 : a < k0 := by omega
        have hAac : Anc0 M a c := Anc0.step hpc (Anc0.refl a)
        have hAak0 : Anc0 M a k0 := anc_between hAac k0 (by omega) (by omega)
        obtain ⟨dd, hpdd, hAdd⟩ := anc0_child hAak0 (Ne.symm hk0a)
        have hddc : dd ∈ children M a := mem_children_iff.mpr ⟨by
          have := hAdd.le; have := par_lt M 0 c a hpc; omega, hpdd⟩
        have hadd : a < dd := (mem_children hddc).1
        have hddk0 : dd ≤ k0 := hAdd.le
        have hSLdd : SubLast M dd k0 := by
          refine ⟨hAdd, fun j' hj' => ?_⟩
          by_contra hlt
          have hAddc : Anc0 M dd c := anc_between hj' c (by omega) (by omega)
          have := par0_ge_of_anc hAddc (by omega) (le_refl c) hpc
          omega
        apply ih a dd k0 (by omega) (by omega) h2s hvs hddc hSLdd
        · intro d hd hlt
          by_cases hdc : d = c
          · rw [hdc]; exact ⟨hcnt, hcb⟩
          · rcases Nat.lt_or_ge d c with h | h
            · exfalso
              have hAddd : Anc0 M dd d := anc_between hAdd d (by omega) (by omega)
              have := par0_ge_of_anc hAddd hlt (le_refl d) (mem_children_iff.mp hd).2
              omega
            · exact hafter d hd (by omega)
        · intro t ht ⟨h1, h2⟩; exact hxo t ht ⟨h1, by omega⟩

/-- **The top step**: `s` is the last column below `a` before `s + 1` (whose parent is at most `a`), `v` drops
at `s`, and the children of `a` after `s` are neither counted nor bump children. -/
theorem strict_top (hG' : Good3 (M.take x) ρ') (hBE : BumpE2 M) (hR12 : R12 M) {a s : Nat}
    (hsx : s < x) (he2 : entry M 2 s = 0) (hvs : ρ'.v s < ρ.v s) (hA : Anc0 M a s) (has : a ≠ s)
    (hs1 : ∃ t, par M 0 (s + 1) = some t ∧ t ≤ a)
    (hafter : ∀ d ∈ children M a, s < d → ¬ Counted M a d ∧ col M d ≠ bump M a)
    (hxo : ∀ t, par M 0 x = some t → ¬ (a < t ∧ t ≤ s)) : ρ'.o a < ρ.o a := by
  obtain ⟨c0, hp0, hA0⟩ := anc0_child hA has
  have hc0 : c0 ∈ children M a := mem_children_iff.mpr ⟨by have := hA0.le; omega, hp0⟩
  have hac0 : a < c0 := (mem_children hc0).1
  obtain ⟨t, ht, hta⟩ := hs1
  have hnot : ∀ j, s < j → ¬ Anc0 M c0 j := by
    intro j hj hAj
    have hA1 : Anc0 M c0 (s + 1) := anc_between hAj (s + 1) (by have := hA0.le; omega) (by omega)
    have := par0_ge_of_anc hA1 (by have := hA0.le; omega) (le_refl _) ht
    omega
  have hSL : SubLast M c0 s := ⟨hA0, fun j hj => by
    by_contra h; exact hnot j (by omega) hj⟩
  apply strict_up hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hG' hBE hR12 (s - a + 1) a c0 s (by omega)
    hsx he2 hvs hc0 hSL
  · intro d hd hlt
    apply hafter d hd
    by_contra hle
    have hAd : Anc0 M c0 d := anc_between hA0 d (by omega) (by omega)
    have := par0_ge_of_anc hAd hlt (le_refl d) (mem_children_iff.mp hd).2
    omega
  · exact hxo

end

end Ytosk
