/-
**3 行・t = 2: M[n] の写しの値は M[n − 1] の値の置き換え σ（`copy_rel`）、写しの列の Good3（`copy_good3`）。**

N の列 i + L（i ≥ r）は P の列 i の写し。ガード g（P で行 1 の祖先に r がある列）。V = v_P(r)、V′ = v_N(r + L)。
- g の列: v_N = f(v_P)、o_N = ψ_{f(v)}(σ y)（o_P = ψ_v(y)、`shO`）。g でない列: 値は等しい。
- 証明は P の順位についての帰納法。構造の対応（子・数える・のりしろ・行 1・行 2・P_1・上げ）は仮定、
  ガードの閉じ方（g の列の P_1・上げの先は g、g でない列の読む先は g でないか r より前）も仮定。
- 値の仮定: g の列が読む g でない子の v は V 以下（σ が動かさない）、r より前の読む先の v は N と P で等しい、
  r の数える子は g。
-/
import Ytosk.V3SubstC
import Ytosk.V3Chg
import Ytosk.V3ValT1R
import Ytosk.V3PathT
import Ytosk.V3TP1
import Ytosk.V3T0D

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **The root form of `σ`**: the subscript `v` (with `V ≤ v`) becomes `f(v)`. -/
def shO (V V' : T) : T → T
  | z => z
  | psi s y c => psi (shf V V' s) (sh V V' y) (sh V V' c)

theorem shO_eq_sh {V V' s y c : T} (h : V < s) : shO V V' (psi s y c) = sh V V' (psi s y c) := by
  rw [shO, sh_psi_gt h]

/-- The copy shift of a column index. -/
def sft (r L t : Nat) : Nat := if r ≤ t then t + L else t

theorem cnt_list (M : Mat) (ρ : Valn) (i : Nat) :
    (children M i).map (cnt M ρ i) = (children M i).map (fun d => if Counted M i d then ρ.o d else z) := by
  apply List.map_congr_left; intro d _; exact cnt_eq_ite M ρ i d

theorem o_form {P : Mat} {ρ : Valn} (hCP : Cons P ρ) (hGP : Good3 P ρ) {d : Nat} (hd : d < P.length) :
    ∃ y, ρ.o d = psi (ρ.v d) y z := ⟨_, o_spArg hCP hGP hd⟩

section
variable {N P : Mat} {r L : Nat} {σ ρ : Valn} {g : Nat → Prop} {V' : T} {rk : Bool → Nat → Nat}
  (hCN : Cons N σ) (hCP : Cons P ρ) (hGP : Good3 P ρ) (hRP : Rk P rk)
  (hNl : N.length = P.length + L) (hrP : r < P.length)
  -- structure of the copies
  (hch : ∀ i, r ≤ i → i < P.length → children N (i + L) = (children P i).map (· + L))
  (hcnt : ∀ i d, r ≤ i → i < P.length → d ∈ children P i →
    (Counted N (i + L) (d + L) ↔ Counted P i d))
  (hbmp : ∀ i d, r ≤ i → i < P.length → d ∈ children P i →
    (col N (d + L) = bump N (i + L) ↔ col P d = bump P i))
  (he2 : ∀ i, r ≤ i → i < P.length → entry N 2 (i + L) = entry P 2 i)
  (he1 : ∀ i, r < i → i < P.length → (entry N 1 (i + L) = 0 ↔ entry P 1 i = 0))
  (hp1 : ∀ i, r < i → i < P.length → par N 1 (i + L) = (par P 1 i).map (sft r L))
  (hup : ∀ i, r < i → i < P.length → upg N (i + L) = (upg P i).map (sft r L))
  -- the guard
  (hg0 : g r)
  (hge1 : ∀ i, r < i → i < P.length → g i → entry P 1 i ≠ 0)
  (hgp : ∀ i, r < i → i < P.length → g i → ∃ t, par P 1 i = some t ∧ r ≤ t ∧ g t)
  (hgpn : ∀ i t, r < i → i < P.length → ¬ g i → par P 1 i = some t → r ≤ t → ¬ g t)
  (hgu : ∀ i k, r < i → i < P.length → g i → entry P 2 i = 0 → upg P i = some k → r < k ∧ g k)
  (hgun : ∀ i k, r < i → i < P.length → ¬ g i → upg P i = some k → r ≤ k → ¬ g k)
  (hgc : ∀ i d, r ≤ i → i < P.length → d ∈ children P i → Counted P i d → ¬ g i → ¬ g d)
  (hgb : ∀ i j k, r < i → i < P.length → j ∈ children P i → col P j = bump P i → k ∈ children P j →
    ¬ g i → ¬ g k)
  -- values
  (hgcV : ∀ i d, r ≤ i → i < P.length → d ∈ children P i → Counted P i d → g i → ¬ g d →
    ¬ ρ.v r < ρ.v d)
  (hgbV : ∀ i j k, r < i → i < P.length → j ∈ children P i → col P j = bump P i → k ∈ children P j →
    g i → ¬ g k → ¬ ρ.v r < ρ.v k)
  (hbase : ∀ i t, r < i → i < P.length → (par P 1 i = some t ∨ upg P i = some t) → t < r →
    σ.v t = ρ.v t)
  (hroot : σ.v (r + L) = V') (hV' : isOT V' = true) (hVV : ρ.v r < V')
  (hgcr : ∀ d ∈ children P r, Counted P r d → g d)

include hCP hGP hRP hge1 hgp hgu

/-- **A guarded column above `r` has `v > V`.** -/
theorem gv_gt : ∀ n i, rk false i < n → r < i → i < P.length → g i → ρ.v r < ρ.v i
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, i, hn, hri, hi, hg => by
    obtain ⟨t, ht, hrt, hgt⟩ := hgp i hri hi hg
    have h1 := hge1 i hri hi hg
    obtain ⟨_, _, hR3⟩ := hRP i hi
    obtain ⟨hRp, hRu, hRb⟩ := hR3 h1
    have htl : t < P.length := by have := par_lt P 1 i t ht; omega
    have hVt : ρ.v r ≤ ρ.v t := by
      rcases Nat.lt_or_ge r t with h | h
      · exact le_of_lt (gv_gt n t (by have := hRp t ht; omega) h htl hgt)
      · have : t = r := by omega
        subst this; exact le_refl _
    have hA : isOT (ρ.v t) = true := hGP.ot_v t htl
    -- `v(i) = v(t) + δ` with `δ ≠ 0`
    have key : ∀ δ, isOT δ = true → δ ≠ z → ρ.v i = sf (add (ρ.v t) δ) → ρ.v r < ρ.v i := by
      intro δ hδ hδz he
      rw [he, sf_ot (isOT_add hA hδ)]
      refine lt_of_le_of_lt hVt ?_
      have := add_lt_add_left (ρ.v t) (show z < δ from lt_of_le_of_ne (z_le _) (Ne.symm hδz))
      simpa using this
    have hv := (hCP i hi).2
    unfold vRhs at hv
    rw [if_neg h1, ht] at hv
    simp only [vOpt] at hv
    split at hv
    · rename_i h2
      split at hv
      · rename_i k hk
        obtain ⟨hrk, hgk⟩ := hgu i k hri hi hg h2 hk
        have hkl : k < P.length := upg_lt hi hk
        have hVk := gv_gt n k (by have := hRu h2 k hk; omega) hrk hkl hgk
        have hkz : ρ.v k ≠ z := fun h => absurd (h ▸ hVk) (T.not_lt_z _)
        exact key _ (isOT_last (hGP.ot_v k hkl)) (last_ne_z' hkz) hv
      · exact key one isOT_one (by simp [one]) hv
    · exact key _ (isOT_omega (isOT_sumN _ (fun u hu => by
        simp only [List.mem_cons, List.mem_map] at hu
        rcases hu with rfl | ⟨j, hj, rfl⟩
        · exact isOT_one
        · unfold bumpTerm; split
          · exact isOT_omega (isOT_sumN _ (fun w hw => by
              obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
              exact hGP.ot_o k (mem_children hk).2))
          · rfl))) (omega_ne_z _) hv
where
  omega_ne_z (x : T) : omega x ≠ z := by
    unfold omega; split
    · simp
    · split <;> simp [one]

include hCN hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0 hgpn hgun hgc hgb hgcV hgbV hbase hroot hV' hVV
  hgcr in
/-- **The copy relation** (by induction on the rank of `P`). -/
theorem copy_rel : ∀ n b i, rk b i < n → r ≤ i → i < P.length →
    (g i → valB σ b (i + L) = cond b (shO (ρ.v r) V' (ρ.o i)) (shf (ρ.v r) V' (ρ.v i))) ∧
    (¬ g i → valB σ b (i + L) = valB ρ b i)
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, b, i, hn, hri, hi => by
    set V := ρ.v r with hVdef
    have hVo : isOT V = true := hGP.ot_v r hrP
    have hVV' : V ≤ V' := le_of_lt hVV
    have hgv : ∀ j, r < j → j < P.length → g j → V < ρ.v j := fun j h1 h2 h3 =>
      gv_gt hCP hGP hRP hge1 hgp hgu _ j (Nat.lt_succ_self _) h1 h2 h3
    have hfix : ∀ d, d < P.length → ¬ V < ρ.v d → sh V V' (ρ.o d) = ρ.o d := by
      intro d hd hle
      obtain ⟨y, hy⟩ := o_form hCP hGP hd
      rw [hy]; exact sh_fix (hy ▸ hGP.ot_o d hd) (by simpa using hle)
    have hsho : ∀ d, d < P.length → V < ρ.v d → shO V V' (ρ.o d) = sh V V' (ρ.o d) := by
      intro d hd hlt
      obtain ⟨y, hy⟩ := o_form hCP hGP hd
      rw [hy]; exact shO_eq_sh hlt
    have hiN : i + L < N.length := by omega
    obtain ⟨hR1, hR2, hR3⟩ := hRP i hi
    cases b with
    | true =>
      have ihv := copy_rel n false i (by have := hR1; omega) hri hi
      -- the counted children
      have ihc : ∀ d ∈ children P i, Counted P i d →
          (g d → σ.o (d + L) = shO V V' (ρ.o d)) ∧ (¬ g d → σ.o (d + L) = ρ.o d) := by
        intro d hd hcd
        have := copy_rel n true d (by have := hR2 d hd hcd.1 hcd.2; omega)
          (by have := (mem_children hd).1; omega) (mem_children hd).2
        exact this
      have hlistN : (children N (i + L)).map (cnt N σ (i + L)) =
          (children P i).map (fun d => if Counted P i d then σ.o (d + L) else z) := by
        rw [hch i hri hi, List.map_map]
        apply List.map_congr_left
        intro d hd
        simp only [Function.comp]
        rw [cnt_eq_ite]
        by_cases hc : Counted P i d
        · rw [if_pos ((hcnt i d hri hi hd).mpr hc), if_pos hc]
        · rw [if_neg (fun h => hc ((hcnt i d hri hi hd).mp h)), if_neg hc]
      have hcntOT : ∀ t ∈ (children P i).map (cnt P ρ i), isOT t = true := by
        intro t ht
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
        rw [cnt_eq_ite]; split
        · exact hGP.ot_o d (mem_children hd).2
        · rfl
      have hvi : isOT (ρ.v i) = true := hGP.ot_v i hi
      have hS : isOT (sumN ((children P i).map (cnt P ρ i))) = true := isOT_sumN _ hcntOT
      have hoP : ρ.o i = psi (ρ.v i) (spArg (ρ.v i) z (sumN ((children P i).map (cnt P ρ i)))) z := by
        rw [(hCP i hi).1]; unfold oRhs; exact sf_psi_spArg hvi hS
      refine ⟨fun hg => ?_, fun hg => ?_⟩
      · -- guarded
        have hlist : (children N (i + L)).map (cnt N σ (i + L)) =
            ((children P i).map (cnt P ρ i)).map (sh V V') := by
          rw [hlistN, cnt_list P ρ i, List.map_map]
          apply List.map_congr_left
          intro d hd
          simp only [Function.comp]
          by_cases hc : Counted P i d
          · rw [if_pos hc, if_pos hc]
            have hdl := (mem_children hd).2
            have hrd : r < d := by have := (mem_children hd).1; omega
            by_cases hgd : g d
            · rw [(ihc d hd hc).1 hgd, hsho d hdl (hgv d hrd hdl hgd)]
            · rw [(ihc d hd hc).2 hgd, hfix d hdl (hgcV i d hri hi hd hc hg hgd)]
          · rw [if_neg hc, if_neg hc, sh_z]
        show σ.o (i + L) = shO V V' (ρ.o i)
        rw [(hCN (i + L) hiN).1]
        unfold oRhs
        have hv' : σ.v (i + L) = shf V V' (ρ.v i) := ihv.1 hg
        rw [hlist, ← sh_sumN hVo hV' hVV hcntOT, hv']
        have hVi : V ≤ ρ.v i := by
          rcases Nat.lt_or_ge r i with h | h
          · exact le_of_lt (hgv i h hi hg)
          · have : i = r := by omega
            subst this; exact le_refl _
        have hlev : V < ρ.v i ∨ ∀ q ∈ summands (sumN ((children P i).map (cnt P ρ i))), lev q ≠ V := by
          rcases Nat.lt_or_ge r i with h | h
          · exact Or.inl (hgv i h hi hg)
          · have hir : i = r := by omega
            subst hir
            right
            intro q hq
            rw [sumN_nzs hcntOT] at hq
            have hsg : ∀ t ∈ nzs ((children P i).map (cnt P ρ i)), Single t := by
              intro t ht
              have := cvals_single hCP hGP i
              exact this t ht
            have hq' := summands_sumN_sub hsg q hq
            simp only [nzs, List.mem_filter, List.mem_map] at hq'
            obtain ⟨⟨d, hd, hdq⟩, hqz⟩ := hq'
            rw [cnt_eq_ite] at hdq
            split at hdq
            · rename_i hc
              subst hdq
              have hdl := (mem_children hd).2
              have hrd := (mem_children hd).1
              obtain ⟨y, hy⟩ := o_form hCP hGP hdl
              rw [hy, lev_psi]
              exact ne_of_gt (hgv d hrd hdl (hgcr d hd hc))
            · subst hdq; simp at hqz
        rw [sf_psi_sh hVo hV' hVV hvi hS hVi hlev, hoP, shO, sh_z]
      · -- not guarded
        have hir : r < i := by
          rcases Nat.lt_or_ge r i with h | h
          · exact h
          · exact absurd (show i = r by omega ▸ hg0) hg
        have hlist : (children N (i + L)).map (cnt N σ (i + L)) = (children P i).map (cnt P ρ i) := by
          rw [hlistN, cnt_list P ρ i]
          apply List.map_congr_left
          intro d hd
          by_cases hc : Counted P i d
          · rw [if_pos hc, if_pos hc, (ihc d hd hc).2 (hgc i d hri hi hd hc hg)]
          · rw [if_neg hc, if_neg hc]
        show σ.o (i + L) = ρ.o i
        rw [(hCN (i + L) hiN).1, (hCP i hi).1]
        unfold oRhs
        have hv' : σ.v (i + L) = ρ.v i := ihv.2 hg
        rw [hlist, hv']
    | false =>
      rcases Nat.lt_or_ge r i with hir | hir
      swap
      · have hir' : i = r := by omega
        subst hir'
        refine ⟨fun _ => ?_, fun hg => absurd hg0 hg⟩
        show σ.v (i + L) = shf V V' V
        rw [hroot, shf_self]
      have hbOT : ∀ j, isOT (bumpTerm P ρ i j) = true := by
        intro j; unfold bumpTerm; split
        · exact isOT_omega (isOT_sumN _ (fun w hw => by
            obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
            exact hGP.ot_o k (mem_children hk).2))
        · rfl
      have hlOT : ∀ t ∈ one :: (children P i).map (bumpTerm P ρ i), isOT t = true := by
        intro t ht
        simp only [List.mem_cons, List.mem_map] at ht
        rcases ht with rfl | ⟨j, _, rfl⟩
        · exact isOT_one
        · exact hbOT j
      -- the bump grandchildren
      have hbump : ∀ (f : T → T), (∀ j ∈ children P i, col P j = bump P i → ∀ k ∈ children P j,
          σ.o (k + L) = f (ρ.o k)) → (∀ x, f (omega (sumN x)) = omega (sumN x) ∨ True) →
          ∀ j ∈ children P i, bumpTerm N σ (i + L) (j + L) =
            if col P j = bump P i then omega (sumN ((children P j).map (fun k => f (ρ.o k)))) else z := by
        intro f hf _ j hj
        unfold bumpTerm
        by_cases hb : col P j = bump P i
        · have hrj : r ≤ j := by have := (mem_children hj).1; omega
          rw [if_pos ((hbmp i j hri hi hj).mpr hb), if_pos hb, hch j hrj (mem_children hj).2, List.map_map]
          congr 2
          apply List.map_congr_left
          intro k hk
          exact hf j hj hb k hk
        · rw [if_neg (fun h => hb ((hbmp i j hri hi hj).mp h)), if_neg hb]
      have hiv : ρ.v i = vRhs P ρ i := (hCP i hi).2
      have hivN : σ.v (i + L) = vRhs N σ (i + L) := (hCN (i + L) hiN).2
      refine ⟨fun hg => ?_, fun hg => ?_⟩
      · -- guarded
        show σ.v (i + L) = shf V V' (ρ.v i)
        have h1 := hge1 i hir hi hg
        have h1N : entry N 1 (i + L) ≠ 0 := fun h => h1 ((he1 i hir hi).mp h)
        obtain ⟨hRp, hRu, hRb⟩ := hR3 h1
        obtain ⟨t, ht, hrt, hgt⟩ := hgp i hir hi hg
        have htl : t < P.length := by have := par_lt P 1 i t ht; omega
        have ihp : σ.v (t + L) = shf V V' (ρ.v t) :=
          (copy_rel n false t (by have := hRp t ht; omega) hrt htl).1 hgt
        have hVt : V ≤ ρ.v t := by
          rcases Nat.lt_or_ge r t with h | h
          · exact le_of_lt (hgv t h htl hgt)
          · have : t = r := by omega
            subst this; exact le_refl _
        have htO := hGP.ot_v t htl
        rw [hivN, hiv]
        unfold vRhs
        rw [if_neg h1N, if_neg h1, he2 i hri hi, hp1 i hir hi, ht]
        simp only [Option.map_some, sft, if_pos hrt, vOpt]
        rw [ihp]
        by_cases h2 : entry P 2 i = 0
        · rw [if_pos h2, if_pos h2, hup i hir hi]
          cases hu : upg P i with
          | none =>
            simp only [Option.map_none]
            exact shf_add_one hVo hV' hVV htO hVt
          | some k =>
            obtain ⟨hrk, hgk⟩ := hgu i k hir hi hg h2 hu
            have hkl : k < P.length := upg_lt hi hu
            have ihk : σ.v (k + L) = shf V V' (ρ.v k) :=
              (copy_rel n false k (by have := hRu h2 k hu; omega) (le_of_lt hrk) hkl).1 hgk
            simp only [Option.map_some, sft, if_pos (le_of_lt hrk)]
            rw [ihk]
            exact shf_add_last hVo hV' hVV htO (hGP.ot_v k hkl) hVt (hgv k hrk hkl hgk)
        · rw [if_neg h2, if_neg h2, hch i hri hi, List.map_map]
          have hgk : ∀ j ∈ children P i, col P j = bump P i → ∀ k ∈ children P j,
              σ.o (k + L) = sh V V' (ρ.o k) := by
            intro j hj hb k hk
            have hkl := (mem_children hk).2
            have hrk : r < k := by have := (mem_children hk).1; have := (mem_children hj).1; omega
            have ihk := copy_rel n true k (by have := hRb h2 j hj hb k hk; omega) (le_of_lt hrk) hkl
            by_cases hgk : g k
            · have e : σ.o (k + L) = shO V V' (ρ.o k) := ihk.1 hgk
              rw [e]; exact hsho k hkl (hgv k hrk hkl hgk)
            · have e : σ.o (k + L) = ρ.o k := ihk.2 hgk
              rw [e]; exact (hfix k hkl (hgbV i j k hir hi hj hb hk hg hgk)).symm
          have hlist : (children P i).map (bumpTerm N σ (i + L) ∘ (· + L)) =
              ((children P i).map (bumpTerm P ρ i)).map (sh V V') := by
            rw [List.map_map]
            apply List.map_congr_left
            intro j hj
            simp only [Function.comp]
            rw [hbump (sh V V') hgk (fun _ => Or.inr trivial) j hj]
            unfold bumpTerm
            split
            · have em : List.map (fun k => sh V V' (ρ.o k)) (children P j) =
                  List.map (sh V V') (List.map ρ.o (children P j)) := by rw [List.map_map]; rfl
              rw [em, sh_omega hVo hV' hVV (isOT_sumN _ (fun w hw => by
                  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
                  exact hGP.ot_o k (mem_children hk).2)),
                sh_sumN hVo hV' hVV (fun w hw => by
                  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
                  exact hGP.ot_o k (mem_children hk).2)]
            · exact sh_z.symm
          rw [hlist]
          have e1 : one :: ((children P i).map (bumpTerm P ρ i)).map (sh V V') =
              (one :: (children P i).map (bumpTerm P ρ i)).map (sh V V') := by
            simp [sh_one]
          rw [e1, ← sh_sumN hVo hV' hVV hlOT]
          exact shf_add_omega hVo hV' hVV htO (isOT_sumN _ hlOT) hVt
      · -- not guarded
        show σ.v (i + L) = ρ.v i
        rw [hivN, hiv]
        unfold vRhs
        by_cases h1 : entry P 1 i = 0
        · rw [if_pos ((he1 i hir hi).mpr h1), if_pos h1]
        have h1N : entry N 1 (i + L) ≠ 0 := fun h => h1 ((he1 i hir hi).mp h)
        obtain ⟨hRp, hRu, hRb⟩ := hR3 h1
        rw [if_neg h1N, if_neg h1, he2 i hri hi, hp1 i hir hi]
        have hpar : vOpt σ ((par P 1 i).map (sft r L)) = vOpt ρ (par P 1 i) := by
          cases hp : par P 1 i with
          | none => rfl
          | some t =>
            simp only [Option.map_some, vOpt, sft]
            have htl : t < P.length := by have := par_lt P 1 i t hp; omega
            split
            · rename_i hrt
              exact (copy_rel n false t (by have := hRp t hp; omega) hrt htl).2
                (hgpn i t hir hi hg hp hrt)
            · rename_i hrt
              exact hbase i t hir hi (Or.inl hp) (by omega)
        rw [hpar]
        by_cases h2 : entry P 2 i = 0
        · rw [if_pos h2, if_pos h2, hup i hir hi]
          cases hu : upg P i with
          | none => rfl
          | some k =>
            have hkl : k < P.length := upg_lt hi hu
            simp only [Option.map_some, sft]
            split
            · rename_i hrk
              have e : σ.v (k + L) = ρ.v k :=
                (copy_rel n false k (by have := hRu h2 k hu; omega) hrk hkl).2 (hgun i k hir hi hg hu hrk)
              rw [e]
            · rename_i hrk
              rw [hbase i k hir hi (Or.inr hu) (by omega)]
        · rw [if_neg h2, if_neg h2, hch i hri hi, List.map_map]
          have hgk : ∀ j ∈ children P i, col P j = bump P i → ∀ k ∈ children P j,
              σ.o (k + L) = id (ρ.o k) := by
            intro j hj hb k hk
            have hkl := (mem_children hk).2
            have hrk : r ≤ k := by have := (mem_children hk).1; have := (mem_children hj).1; omega
            exact (copy_rel n true k (by have := hRb h2 j hj hb k hk; omega) hrk hkl).2
              (hgb i j k hir hi hj hb hk hg)
          have hlist : (children P i).map (bumpTerm N σ (i + L) ∘ (· + L)) =
              (children P i).map (bumpTerm P ρ i) := by
            apply List.map_congr_left
            intro j hj
            simp only [Function.comp]
            rw [hbump id hgk (fun _ => Or.inr trivial) j hj]
            unfold bumpTerm
            simp
          rw [hlist]

include hCN hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0 hgpn hgun hgc hgb hgcV hgbV hbase hroot hV' hVV
  hgcr in
/-- **Good3 at the copy columns.** -/
theorem copy_good3 {i : Nat} (hri : r ≤ i) (hi : i < P.length) :
    isOT (σ.o (i + L)) = true ∧ isOT (σ.v (i + L)) = true ∧
      (cvals N σ (i + L)).Pairwise (fun a b => b ≤ a) := by
  set V := ρ.v r with hVdef
  have hVo : isOT V = true := hGP.ot_v r hrP
  have hVV' : V ≤ V' := le_of_lt hVV
  have rel := fun b j (hrj : r ≤ j) (hj : j < P.length) =>
    copy_rel hCN hCP hGP hRP hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0 hge1 hgp hgpn hgu hgun hgc hgb hgcV
      hgbV hbase hroot hV' hVV hgcr _ b j (Nat.lt_succ_self _) hrj hj
  have hgv : ∀ j, r < j → j < P.length → g j → V < ρ.v j := fun j h1 h2 h3 =>
    gv_gt hCP hGP hRP hge1 hgp hgu _ j (Nat.lt_succ_self _) h1 h2 h3
  have hVi : g i → V ≤ ρ.v i := by
    intro hg
    rcases Nat.lt_or_ge r i with h | h
    · exact le_of_lt (hgv i h hi hg)
    · have : i = r := by omega
      subst this; exact le_refl _
  -- the counted values of `N` at `i + L`
  have hlistN : (children N (i + L)).map (cnt N σ (i + L)) =
      (children P i).map (fun d => if Counted P i d then σ.o (d + L) else z) := by
    rw [hch i hri hi, List.map_map]
    apply List.map_congr_left
    intro d hd
    simp only [Function.comp]
    rw [cnt_eq_ite]
    by_cases hc : Counted P i d
    · rw [if_pos ((hcnt i d hri hi hd).mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc ((hcnt i d hri hi hd).mp h)), if_neg hc]
  have hcv : cvals P ρ i = nzs ((children P i).map (fun d => if Counted P i d then ρ.o d else z)) := by
    unfold cvals; rw [cnt_list]
  have hcvOT : ∀ t ∈ cvals P ρ i, isOT t = true := by
    intro t ht
    exact (cvals_single hCP hGP i t ht).1
  by_cases hg : g i
  · have ho : σ.o (i + L) = shO V V' (ρ.o i) := (rel true i hri hi).1 hg
    have hv : σ.v (i + L) = shf V V' (ρ.v i) := (rel false i hri hi).1 hg
    obtain ⟨y, hy⟩ := o_form hCP hGP hi
    refine ⟨?_, ?_, ?_⟩
    · rw [ho, hy, shO, sh_z]
      exact isOT_shTop hVo hV' hVV (hy ▸ hGP.ot_o i hi) (hVi hg)
    · rw [hv]; exact isOT_shf hVo hV' hVV (hGP.ot_v i hi)
    · have hlist : (children P i).map (fun d => if Counted P i d then σ.o (d + L) else z) =
          ((children P i).map (fun d => if Counted P i d then ρ.o d else z)).map (sh V V') := by
        rw [List.map_map]
        apply List.map_congr_left
        intro d hd
        simp only [Function.comp]
        by_cases hc : Counted P i d
        · rw [if_pos hc, if_pos hc]
          have hdl := (mem_children hd).2
          have hrd : r < d := by have := (mem_children hd).1; omega
          by_cases hgd : g d
          · have e : σ.o (d + L) = shO V V' (ρ.o d) := (rel true d (le_of_lt hrd) hdl).1 hgd
            rw [e]
            obtain ⟨y', hy'⟩ := o_form hCP hGP hdl
            rw [hy']; exact shO_eq_sh (hgv d hrd hdl hgd)
          · have e : σ.o (d + L) = ρ.o d := (rel true d (le_of_lt hrd) hdl).2 hgd
            rw [e]
            obtain ⟨y', hy'⟩ := o_form hCP hGP hdl
            rw [hy']
            exact (sh_fix (hy' ▸ hGP.ot_o d hdl) (by simpa using hgcV i d hri hi hd hc hg hgd)).symm
        · rw [if_neg hc, if_neg hc, sh_z]
      have hnz : ∀ l : List T, nzs (l.map (sh V V')) = (nzs l).map (sh V V') := by
        intro l
        unfold nzs
        rw [List.filter_map]
        congr 1
        apply List.filter_congr
        intro t _
        simp [Function.comp, sh_eq_z_iff]
      unfold cvals
      rw [hlistN, hlist, hnz, ← hcv]
      exact pairwise_sh hVo hV' hVV hcvOT (hGP.dec i hi)
  · have ho : σ.o (i + L) = ρ.o i := (rel true i hri hi).2 hg
    have hv : σ.v (i + L) = ρ.v i := (rel false i hri hi).2 hg
    refine ⟨ho ▸ hGP.ot_o i hi, hv ▸ hGP.ot_v i hi, ?_⟩
    have hlist : (children P i).map (fun d => if Counted P i d then σ.o (d + L) else z) =
        (children P i).map (fun d => if Counted P i d then ρ.o d else z) := by
      apply List.map_congr_left
      intro d hd
      by_cases hc : Counted P i d
      · rw [if_pos hc, if_pos hc]
        have hdl := (mem_children hd).2
        have hrd : r ≤ d := by have := (mem_children hd).1; omega
        exact (rel true d hrd hdl).2 (hgc i d hri hi hd hc hg)
      · rw [if_neg hc, if_neg hc]
    unfold cvals
    rw [hlistN, hlist, ← hcv]
    exact hGP.dec i hi

end

end Ytosk
