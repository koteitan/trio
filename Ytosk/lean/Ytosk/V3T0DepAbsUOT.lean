/- The t=0 upgrade-aware dependency engine without assuming GoodOT of the target. -/
import Ytosk.V3T0DepAbsU

namespace Ytosk
open T Ytosk.WfAbsW Ytosk.WfT2X
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN

theorem t0_dep_otSU0 {g : Nat} (hg : par M 0 r = some g) {rk : Bool → Nat → Nat} (hRM : Rk M rk)
    {ρ' : Valn} (hC1 : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i)
    (hσBv : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i)
    (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hVR : VSmallRP M (r + L) r ρ)
    (hFO : FrameOT M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    {Bd : Nat → Prop}
    (hAbsX : ∀ i, i < r → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → AbsAt M (TRIO.gexp M r L 0 0 n) ρ σ i ∨ Bd i)
    (hBdUp : ∀ i k, upg M i = some k → Bd k → Bd i)
    (hBdF : ∀ i c, Bd c → c ∈ CL M i → CL M c = [] ∧ CL (TRIO.gexp M r L 0 0 n) c = [] ∧
      (par M 1 c = some i ∨ ∀ u, ∀ g ∈ comps u (vOpt ρ (par M 1 c)), g < σ.o c))
    (hBdCL : ∀ c, Bd c → CL M c = [] ∧ CL (TRIO.gexp M r L 0 0 n) c = [])
    (hBdK : ∀ i m p, Bd i → par M 0 i = some m → par M 0 m = some p → col M m ≠ bump M p)
    (hlt : ρ'.o r < ρ.o r)
    (hS1N : Counted M g r → ∃ X X', ρ.o g = psi (ρ.v g) X z ∧ σ.o g = psi (ρ.v g) X' z ∧
      isOT (psi (ρ.v g) X' z) = true ∧ Lhd z (psi (ρ.v g) X' z) (psi (ρ.v g) X z) ∧
      ∀ U : T → Prop, RClaimU U ρ σ g)
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hLastC : Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hS3 : ∀ p, par M 0 g = some p → entry M 1 p ≠ 0 → entry M 2 p ≠ 0 → col M g = bump M p →
      Lhd z (σ.v p) (ρ.v p))
    (hS2 : col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → Lhd z (σ.v g) (ρ.v g))
    (hPH : PH3cG M ρ)
    (hVchgR : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r →
      ¬ psi (ρ.v r) z z < psi (succ (ρ.v g)) z z → ¬ psi s' z z < psi (succ (ρ.v g)) z z)
    (hG0 : Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      ∀ Lc0 : List Nat, CL M g = Lc0 ++ [r] → ∀ s y, ρ.o r = psi s y z →
        ¬ (lt (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true)) :
    ∀ b i, i < r → isOT (valB σ b i) = true ∧
      (DepX M (r + L) b i → PX M Bd ρ σ b i) ∧
      (b = true → DepX M (r + L) true i → (∀ U : T → Prop, (∀ u, U u → PathLv M (r + L) r ρ i u) → RClaimU U ρ σ i)) ∧
      (b = true → DepX M (r + L) true i → σ.v i = ρ.v i → ∀ X X', ρ.o i = psi (ρ.v i) X z →
        σ.o i = psi (ρ.v i) X' z → X' ≠ X → REr X X') := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hiN : ∀ i, i < r → i < (TRIO.gexp M r L 0 0 n).length := fun i hi => by rw [hlN]; omega
  have hAgx : Anc0 M g (r + L) := Anc0.step hp (Anc0.step hg (Anc0.refl g))
  have hgr : g < r := par_lt M 0 r g hg
  -- the copies are standard
  have hOTc : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      isOT (σ.o i) = true ∧ isOT (σ.v i) = true := by
    intro i hri hiN'
    have hph : phi0 r L i < r + L := by
      unfold phi0; rw [if_neg (by omega)]; have := Nat.mod_lt (i - r) hL; omega
    rw [hσB i hri hiN', hσBv i hri hiN']
    unfold tauN
    simp only [if_neg (show ¬ i < r by omega)]
    refine ⟨?_, ?_⟩
    · split_ifs
      · exact isOT_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN
      · exact hG.ot_o _ (by omega)
      · exact hGT.ot_o _ (by rw [List.length_take]; omega)
    · split_ifs
      · exact hG.ot_v _ (by omega)
      · exact hGT.ot_v _ (by rw [List.length_take]; omega)
  -- the claim, by the ranking
  have key : ∀ K, ∀ b i, rk b i ≤ K → i < r →
      isOT (valB σ b i) = true ∧ (DepX M (r + L) b i → PX M Bd ρ σ b i) ∧
      (b = true → DepX M (r + L) true i → (∀ U : T → Prop, (∀ u, U u → PathLv M (r + L) r ρ i u) → RClaimU U ρ σ i)) ∧
      (b = true → DepX M (r + L) true i → σ.v i = ρ.v i → ∀ X X', ρ.o i = psi (ρ.v i) X z →
        σ.o i = psi (ρ.v i) X' z → X' ≠ X → REr X X') := by
    intro K
    induction K using Nat.strongRecOn with
    | _ K ih =>
      intro b i hK hi
      have hiM : i < M.length := by omega
      obtain ⟨hRv, hRc, hRr⟩ := hRM i hiM
      -- standard values of lower rank
      have hOTo : ∀ j, j < (TRIO.gexp M r L 0 0 n).length → (j < r → rk true j < K) →
          isOT (σ.o j) = true := by
        intro j hj hjK
        rcases Nat.lt_or_ge j r with hjr | hjr
        · exact (ih _ (hjK hjr) true j (le_refl _) hjr).1
        · exact (hOTc j hjr hj).1
      have hOTv : ∀ j, j < (TRIO.gexp M r L 0 0 n).length → (j < r → rk false j < K) →
          isOT (σ.v j) = true := by
        intro j hj hjK
        rcases Nat.lt_or_ge j r with hjr | hjr
        · exact (ih _ (hjK hjr) false j (le_refl _) hjr).1
        · exact (hOTc j hjr hj).2
      cases b with
      | false =>
        -- `v` calls
        have hot : isOT (σ.v i) = true := by
          apply ot_v_at hCN (hiN i hi)
          · intro h1
            rw [entry_pre0 hlen hn 1 (by omega)] at h1
            rw [par1_pre0 hlen hL hp hn hi]
            cases hpm : par M 1 i with
            | none => rfl
            | some m =>
              have hmi := par_lt M 1 i m hpm
              exact hOTv m (by rw [hlN]; omega) (fun _ => by have := (hRr h1).1 m hpm; omega)
          · intro h1 h2 k hu
            rw [entry_pre0 hlen hn 1 (by omega)] at h1
            rw [entry_pre0 hlen hn 2 (by omega)] at h2
            rw [upg_pre0 hlen hL hp hn (by omega)] at hu
            have hkN := upg_lt (hiN i hi) (by rw [upg_pre0 hlen hL hp hn (by omega)]; exact hu)
            exact hOTv k hkN (fun _ => by have := (hRr h1).2.1 h2 k hu; omega)
          · intro h1 h2 j hj hjb k hk
            rw [entry_pre0 hlen hn 1 (by omega)] at h1
            rw [entry_pre0 hlen hn 2 (by omega)] at h2
            have hkN := (mem_children hk).2
            apply hOTo k hkN
            intro hkr
            have hjk := (mem_children hk).1
            have hjr : j < r := by omega
            have hjM : j ∈ children M i := child_lt_r hlen hL hp hn hi hj hjr
            have hkM : k ∈ children M j := child_lt_r hlen hL hp hn hjr hk hkr
            have hjb' : col M j = bump M i := by
              rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)] at hjb; exact hjb
            have := (hRr h1).2.2 h2 j hjM hjb' k hkM; omega
        refine ⟨hot, ?_, fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
        intro hD
        change (Lhd z (σ.v i) (ρ.v i) ∨
          (Bd i ∧ Lhd (vOpt ρ (par M 1 i)) (σ.v i) (ρ.v i))) ∧ isOT (σ.v i) = true
        cases hD with
        | vpar h1 hpm hdm =>
          exfalso
          have hm := par_lt M 1 i _ hpm
          exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdm)).1 rfl (by omega) |>.2.2 i
            (by omega) hpm
        | @vupg _ k h1 h2 hu hdk =>
          obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
          have hkr : k < r := by
            have hkle : k ≤ r := by rcases hcase with h | ⟨_, h⟩ <;> omega
            rcases Nat.lt_or_ge k r with h | h
            · exact h
            · exfalso
              have : k = r := by omega
              rw [this] at hdk
              exact not_depX_v_r hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB he1 hdk
          have hkK : rk false k < K := by have := (hRr h1).2.1 h2 k hu; omega
          have hIHpair : PX M Bd ρ σ false k := (ih _ hkK false k (le_refl _) hkr).2.1 hdk
          have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
            cases hpp : par M 1 i with
            | none => rfl
            | some m => exact hG.ot_v m (by have := par_lt M 1 i m hpp; omega)
          have hVot' : isOT (vOpt σ (par (TRIO.gexp M r L 0 0 n) 1 i)) = true := by
            rw [par1_pre0 hlen hL hp hn hi]
            cases hpp : par M 1 i with
            | none => rfl
            | some m =>
              have hmi := par_lt M 1 i m hpp
              exact hOTv m (by rw [hlN]; omega) (fun _ => by have := (hRr h1).1 m hpp; omega)
          have ek : ρ.v i = ρ.v k :=
            v_upg_eq hC hiM h1 h2 hu hVot (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
          have huN : upg (TRIO.gexp M r L 0 0 n) i = some k := by
            rw [upg_pre0 hlen hL hp hn (by omega)]; exact hu
          have hkM : k < M.length := by omega
          obtain ⟨_, _, hRrk⟩ := hRM k hkM
          have ek' : σ.v i = σ.v k :=
            v_upg_eq hCN (hiN i hi) (by rw [entry_pre0 hlen hn 1 (by omega)]; exact h1)
              (by rw [entry_pre0 hlen hn 2 (by omega)]; exact h2) huN hVot'
              (fun j hj hjb k' hk' => by
                apply hOTo k' (mem_children hk').2
                intro hk'r
                have hjk := (mem_children hk').1
                have hjr : j < r := by omega
                have hjM : j ∈ children M k := child_lt_r hlen hL hp hn hkr hj hjr
                have hk'M : k' ∈ children M j := child_lt_r hlen hL hp hn hjr hk' hk'r
                have hjb' : col M j = bump M k := by
                  rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)] at hjb
                  exact hjb
                obtain ⟨m, _, _, hcol, _⟩ := upg_spec hu
                have h1k : entry M 1 k ≠ 0 := by rw [e1_of_col hcol]; exact (upg_e12 hu).1
                have h2k : entry M 2 k ≠ 0 := by rw [e2_of_col hcol]; omega
                have := (hRrk h1k).2.2 h2k j hjM hjb' k' hk'M
                omega)
          rw [ek, ek']
          rcases hIHpair.1 with hIHL | ⟨hBk, hIHV⟩
          · exact ⟨Or.inl hIHL, hIHpair.2⟩
          · obtain ⟨m, hm1, hm2, -, -⟩ := upg_spec hu
            refine ⟨Or.inr ⟨hBdUp i k hu hBk, ?_⟩, hIHpair.2⟩
            change Lhd (vOpt ρ (par M 1 k)) (σ.v k) (ρ.v k) at hIHV
            rw [hm2] at hIHV
            rw [hm1]
            exact hIHV
        | @vbump _ j k h1 h2 hj hjb hk hdk =>
          have hij := (mem_children hj).1
          have hjk := (mem_children hk).1
          have hkl := (mem_children hk).2
          by_cases hkr : r ≤ k
          · by_cases hjr : r ≤ j
            · have hjr' : j = r := by
                by_contra hne
                by_cases hig : par M 0 r = some i
                · have := children_g_le hlen hL hp hig hj; omega
                · have := children_lt_r hlen hL hp hi hig hj; omega
              have hig : par M 0 r = some i := by rw [← hjr']; exact (mem_children_iff.mp hj).2
              have hgi : g = i := Option.some.inj (hg.symm.trans hig)
              have hkx : k = r + L := by
                by_contra hne
                have := nodep_B hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB he1 true k hdk (by omega) (by omega)
                omega
              rw [hjr'] at hjb
              rw [← hgi] at hjb h1 h2 ⊢
              refine ⟨Or.inl (hS2 hjb h1 h2), ?_⟩
              simpa [hgi] using hot
            · have hjg : par M 0 r = some j := by
                by_contra hne
                have := children_lt_r hlen hL hp (by omega) hne hk; omega
              have hgj : g = j := Option.some.inj (hg.symm.trans hjg)
              subst hgj
              exact ⟨Or.inl (hS3 i (mem_children_iff.mp hj).2 h1 h2 hjb), hot⟩
          · have hkr' : k < r := by omega
            obtain ⟨_, hpnd, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega)
              (DepX.vbump h1 h2 hj hjb hk hdk)
            rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j', k', hch, _, hchj, _, hKnd, hLnd⟩
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
              have hLj : ∀ d ∈ Lb, d < j := (sib_order (children_sorted M i) (R := []) (by rw [hch])).1
              have hKk : ∀ d ∈ Kb, d < k := (sib_order (children_sorted M j) (R := []) (by rw [hchj])).1
              have hig : par M 0 r ≠ some i := by
                intro hig
                have hri : r ∈ children M i := mem_children_iff.mpr ⟨by omega, hig⟩
                rw [hch] at hri
                rcases List.mem_append.mp hri with h | h
                · have := hLj r h; omega
                · simp at h; omega
              have hjg : par M 0 r ≠ some j := by
                intro hjg
                -- the last child of `P_0(r)` is `r`, not `k < r`
                have hl := children_g_last hlen hL hp hjg
                rw [hchj] at hl
                have := congrArg List.getLast? hl
                simp at this
                omega
              have hchN : children (TRIO.gexp M r L 0 0 n) i = Lb ++ [j] := by
                rw [children_pre0 hlen hL hp hn hi hig, hch]
              have hchjN : children (TRIO.gexp M r L 0 0 n) j = Kb ++ [k] := by
                rw [children_pre0 hlen hL hp hn (by omega) hjg, hchj]
              have hbL : ∀ d ∈ Lb, bumpTerm (TRIO.gexp M r L 0 0 n) σ i d = bumpTerm M ρ i d := by
                intro d hd
                have hdj := hLj d hd
                have hdM : d ∈ children M i := by rw [hch]; simp [hd]
                have hdg : par M 0 r ≠ some d := by
                  intro hdg
                  have hgd : g = d := Option.some.inj (hg.symm.trans hdg)
                  have hAj : Anc0 M g j := anc_between hAgx j (by omega) (by omega)
                  have hAi := anc0_par hAj (by omega) (mem_children_iff.mp (show j ∈ children M i by
                    rw [hch]; simp)).2
                  have := hAi.le
                  have := (mem_children hdM).1
                  omega
                apply bumpTerm_eq_of
                · rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
                · intro _
                  rw [children_pre0 hlen hL hp hn (by omega) hdg]
                  apply List.map_congr_left
                  intro e he
                  have her := children_lt_r hlen hL hp (by omega) hdg he
                  exact (hoffD e her).1 (hLnd d hd e he).2
              have hKv : Kb.map σ.o = Kb.map ρ.o := List.map_congr_left (fun d hd => by
                have := hKk d hd; exact (hoffD d (by omega)).1 (hKnd d hd))
              have hbjM : bumpTerm M ρ i j = omega (sumN (Kb.map ρ.o ++ [ρ.o k])) := by
                unfold bumpTerm; rw [if_pos hjb, hchj, List.map_append, List.map_singleton]
              have hbjN : bumpTerm (TRIO.gexp M r L 0 0 n) σ i j = omega (sumN (Kb.map ρ.o ++ [σ.o k])) := by
                unfold bumpTerm
                rw [if_pos (by rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]; exact hjb),
                  hchjN, List.map_append, List.map_singleton, hKv]
              have hNotBdK : ¬ Bd k := by
                intro hBk
                exact hBdK k j i hBk (mem_children_iff.mp hk).2 (mem_children_iff.mp hj).2 hjb
              have hIHpair : PX M Bd ρ σ true k :=
                (ih _ (by have := (hRr h1).2.2 h2 j hj hjb k hk; omega) true k (le_refl _) hkr').2.1 hdk
              have hIH : Lhd z (σ.o k) (ρ.o k) :=
                hIHpair.1.resolve_right (fun h => hNotBdK h.1)
              have hdec := hKD i h1 h2 j hj hjb
              rw [hchj, List.map_append, List.map_singleton] at hdec
              have hsK : ∀ u ∈ Kb.map ρ.o, Single u := fun u hu => by
                obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
                exact single_o hC hG (by have := hKk d hd; omega)
              have hform : (∃ s y y', ρ.o k = psi s y z ∧ σ.o k = psi s y' z) ∨
                  (∃ w' w Y, σ.o k = psi w' z z ∧ ρ.o k = psi w Y z ∧ LhdE w' w ∧ one ≤ w') := by
                obtain ⟨y1, hy1⟩ := o_psi_sub hC (show k < M.length by omega)
                rw [sf_ot (hG.ot_v k (by omega))] at hy1
                by_cases hvk : σ.v k = ρ.v k
                · obtain ⟨y0, hy0⟩ := o_psi_sub hCN (hiN k hkr')
                  rw [sf_ot (hOTv k (hiN k hkr') (fun _ => by
                  have := (hRM k (by omega)).1; have := (hRr h1).2.2 h2 j hj hjb k hk; omega)), hvk] at hy0
                  exact Or.inl ⟨_, _, _, hy1, hy0⟩
                · have hdv : DepX M (r + L) false k := by
                    by_contra hn'; exact hvk ((hoffD k hkr').2 hn')
                  have ho0 := o_N_noc' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hkr'
                    (cl_nil_of_depv' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hkr' hdv)
                    (hOTv k (hiN k hkr') (fun _ => by
                      have := (hRM k (by omega)).1; have := (hRr h1).2.2 h2 j hj hjb k hk; omega))
                  have hvIHpair : PX M Bd ρ σ false k :=
                    (ih _ (by have := (hRM k (by omega)).1; have := (hRr h1).2.2 h2 j hj hjb k hk; omega)
                      false k (le_refl _) hkr').2.1 hdv
                  have hvIH : Lhd z (σ.v k) (ρ.v k) :=
                    hvIHpair.1.resolve_right (fun h => hNotBdK h.1)
                  have he1k : entry M 1 k ≠ 0 := by
                    intro he; apply hvk
                    rw [v_z_of_e1 hC (by omega) he, v_z_of_e1 hCN (hiN k hkr')
                      (by rw [entry_pre0 hlen hn 1 (by omega)]; exact he)]
                  have hv0 : σ.v k ≠ z := v_ne_z_of_e1 hCN (hiN k hkr')
                    (by rw [entry_pre0 hlen hn 1 (by omega)]; exact he1k)
                  exact Or.inr ⟨_, _, _, ho0, hy1, Or.inr hvIH, one_le_of_ne_z hv0⟩
              obtain ⟨hS, hlt, hG'ot⟩ := g_brel hsK hdec (single_o hC hG (by omega))
                ⟨hOTo k (hiN k hkr') (fun _ => by have := (hRr h1).2.2 h2 j hj hjb k hk; omega),
                o_psi_form hCN (hiN k hkr')⟩ hIH hform
              have hGot : isOT (sumN (Kb.map ρ.o ++ [ρ.o k])) = true := isOT_sumN _ (fun u hu => by
                rcases List.mem_append.mp hu with h | h
                · exact (hsK u h).1
                · simp at h; rw [h]; exact hG.ot_o k (by omega))
              have hV : vOpt σ (par (TRIO.gexp M r L 0 0 n) 1 i) = vOpt ρ (par M 1 i) := by
                rw [par1_pre0 hlen hL hp hn hi]
                cases hpp : par M 1 i with
                | none => rfl
                | some m =>
                  have := par_lt M 1 i m hpp
                  exact (hoffD m (by omega)).2 (hpnd m hpp)
              refine ⟨?_, hot⟩
              by_cases hA : AbsAt M (TRIO.gexp M r L 0 0 n) ρ σ i
              · exact Or.inl (v_bump_lhdW hC hG hCN hiM (hiN i hi) h1 h2 (entry_pre0 hlen hn 1 (by omega))
                  (entry_pre0 hlen hn 2 (by omega)) hV hch hchN hbL hbjM hbjN hGot hG'ot hS hlt hTD hA)
              · exact Or.inr ⟨(hAbsX i hi h1 h2).resolve_left hA,
                  v_bump_lhdV hC hG hCN hiM (hiN i hi) h1 h2 (entry_pre0 hlen hn 1 (by omega))
                    (entry_pre0 hlen hn 2 (by omega)) hV hch hchN hbL hbjM hbjN hGot hG'ot hS hlt hTD⟩
      | true =>
        by_cases hD : DepX M (r + L) true i
        swap
        · have he := (hoffD i hi).1 hD
          exact ⟨by show isOT (σ.o i) = true; rw [he]; exact hG.ot_o i hiM, fun h => absurd h hD,
            fun _ h => absurd h hD, fun _ h => absurd h hD⟩
        suffices hmain : isOT (σ.o i) = true ∧ PX M Bd ρ σ true i ∧ (∀ U : T → Prop, (∀ u, U u → PathLv M (r + L) r ρ i u) → RClaimU U ρ σ i) ∧
            (σ.v i = ρ.v i → ∀ X X', ρ.o i = psi (ρ.v i) X z → σ.o i = psi (ρ.v i) X' z → X' ≠ X → REr X X') by
          exact ⟨hmain.1, fun _ => hmain.2.1, fun _ _ => hmain.2.2.1, fun _ _ => hmain.2.2.2⟩
        have hvot : isOT (ρ.v i) = true := hG.ot_v i hiM
        cases hD with
        | leaf => omega
        | ov hv =>
          have hvIH := ih _ (by omega) false i (le_refl _) hi
          have hclM := cl_nil_of_depv' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hi hv
          have hoN := o_N_noc' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hi hclM hvIH.1
          have hoM := o_of_no_counted hC hiM hvot (no_cnt_of_cl_nil hclM)
          have hvPX : PX M Bd ρ σ false i := hvIH.2.1 hv
          have hparentPX : PX M Bd ρ σ true i := by
            have hstd : isOT (σ.o i) = true := by rw [hoN]; exact isOT_psi_zz hvIH.1
            refine ⟨?_, hstd⟩
            rcases hvPX.1 with hl' | ⟨hBi, hl'⟩
            · apply Or.inl
              change Lhd z (σ.o i) (ρ.o i)
              rw [hoN, hoM]
              change Lhd z (σ.v i) (ρ.v i) at hl'
              exact lhd_psi_sub hl'
            · exact Or.inr ⟨hBi, o_noarg_lhdV hl' hoM hoN⟩
          refine ⟨hparentPX.2, hparentPX, fun _ _ => rclaim_zeroU hoN, ?_⟩
          intro hve X X' hX hX' hne
          rw [hoM] at hX; rw [hoN, hve] at hX'
          simp only [psi.injEq] at hX hX'
          exact absurd (hX'.2.1.symm.trans hX.2.1) hne
        | @ochild _ c hc hcb hcu hdc =>
          have hcnt : Counted M i c := ⟨hcb, hcu⟩
          have hvD : ¬ DepX M (r + L) false i := fun hv =>
            uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hv hc hcnt
          have hv' := (hoffD i hi).2 hvD
          have hci := (mem_children hc).1
          have hcl := (mem_children hc).2
          by_cases hcr : r ≤ c
          · have hcr' : c = r := by
              by_contra hne
              by_cases hig : par M 0 r = some i
              · have := children_g_le hlen hL hp hig hc; omega
              · have := children_lt_r hlen hL hp hi hig hc; omega
            rw [hcr'] at hc hcnt
            have hig : par M 0 r = some i := (mem_children_iff.mp hc).2
            have hgi : g = i := Option.some.inj (hg.symm.trans hig)
            rw [← hgi] at hcnt hv' ⊢
            have hm1 : (∃ k, k + 1 < n ∧ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) ∨
                ∀ Lc0 : List Nat, CL M g = Lc0 ++ [r] → ∀ s y, ρ.o r = psi s y z →
                  ¬ (lt (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) y = true ∧
                    lt (psi (ρ.v g) z z) (psi s y z) = true) := by
              by_cases h : ∃ k, k + 1 < n ∧ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)
              · exact Or.inl h
              · exact Or.inr (hG0 hcnt (fun k hk hk' => h ⟨k, hk, hk'⟩))
            obtain ⟨X, X', hX, hX', hot', hlNode, hRC⟩ := hS1N hcnt
            have hNodeL : Lhd z (σ.o g) (ρ.o g) := by rw [hX, hX']; exact hlNode
            have hNodePX : PX M Bd ρ σ true g := ⟨Or.inl hNodeL, by change isOT (σ.o g) = true; rw [hX']; exact hot'⟩
            refine ⟨by rw [hX']; exact hot', hNodePX, fun U _ => hRC U, ?_⟩
            intro _ X1 X1' h1 h1' _
            obtain ⟨X2, X2', h2, h2', hre⟩ := t0_S1A_RE hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC
              hG hCN hg hcnt (fun c hc hd => (hoffD c hc).1 hd) hv' hσmid hσlast (hLastC hcnt) hlt hy' hC1 hGT hm1
            rw [h2] at h1; rw [h2'] at h1'
            simp only [psi.injEq] at h1 h1'
            rw [← h1.2.1, ← h1'.2.1]; exact hre
          · have hcr : c < r := by omega
            rcases hOS_t1 hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp i (by omega) (DepX.ochild hc hcb hcu hdc) with
              ⟨hv, _⟩ | ⟨_, Lp, c0, R, hch, _, _, hR, hLnd⟩
            · exact absurd hv hvD
            · have hcR : ∀ d ∈ R, ¬ Counted M i d := fun d h hd => by
                rcases hR d h with h' | h'
                · exact hd.1 h'
                · exact hd.2 h'
              have hcc0 : c = c0 := by
                have hc' := hc
                rw [hch] at hc'
                rcases List.mem_append.mp hc' with h | h
                · exact absurd hdc (hLnd c h hcnt)
                · rcases List.mem_cons.mp h with h | h
                  · exact h
                  · exact absurd hcnt (hcR c h)
              rw [← hcc0] at hch
              obtain ⟨hLs, hRs⟩ := sib_order (children_sorted M i) hch
              have hclM : CL M i = Lp.filter (fun d => decide (Counted M i d)) ++ [c] := by
                unfold CL
                rw [hch, List.filter_append, List.filter_cons, if_pos (by simpa using hcnt)]
                have : R.filter (fun d => decide (Counted M i d)) = [] := by
                  rw [List.filter_eq_nil_iff]; intro d hd; simpa using hcR d hd
                rw [this]
              set Lc := Lp.filter (fun d => decide (Counted M i d)) with hLc
              have hb : par M 0 r = some i → col M r = bump M i := by
                intro hig
                have hri : r ∈ children M i := mem_children_iff.mpr ⟨by omega, hig⟩
                have hrR : r ∈ R := by
                  rw [hch] at hri
                  rcases List.mem_append.mp hri with h | h
                  · have := hLs r h; omega
                  · rcases List.mem_cons.mp h with h | h
                    · omega
                    · exact h
                by_contra hb
                exact hcR r hrR ⟨hb, by rw [not_topped_r hlen hL hp he2]; simp⟩
              have hclN : CL (TRIO.gexp M r L 0 0 n) i = Lc ++ [c] := by
                rw [cl_N_eq hlen hL hp hn hR0 hZ2 he2 hn2 hi hb, hclM]
              have hsame : ∀ d ∈ Lc, σ.o d = ρ.o d := fun d hd => by
                have hd' := List.mem_filter.mp hd
                have hdc : Counted M i d := by simpa using hd'.2
                have := hLs d hd'.1
                exact (hoffD d (by omega)).1 (hLnd d hd'.1 hdc)
              have hcK : rk true c < K := by have := hRc c hc hcb hcu; omega
              have hIH := ih _ hcK true c (le_refl _) hcr
              have hcM : c < M.length := by omega
              have hcN := hiN c hcr
              have hIHchildPX : PX M Bd ρ σ true c := hIH.2.1 hdc
              by_cases hBdc : Bd c
              · have hcCL : c ∈ CL M i := by rw [hclM]; simp
                obtain ⟨hclMc, hclNc, hshape⟩ := hBdF i c hBdc hcCL
                have hIHW : Lhd (vOpt ρ (par M 1 c)) (σ.o c) (ρ.o c) := by
                  rcases hIHchildPX.1 with h | ⟨_, h⟩
                  · exact lhd_mono_eta h
                  · exact h
                have hcM : c < M.length := by omega
                have hcN := hiN c hcr
                have hvotc : isOT (σ.v c) = true :=
                  (ih _ (by have := (hRM c hcM).1; omega) false c (le_refl _) hcr).1
                have hs0 : ρ.o c = psi (ρ.v c) z z :=
                  o_of_no_counted hC hcM (hG.ot_v c hcM) (no_cnt_of_cl_nil hclMc)
                have hs0' : σ.o c = psi (σ.v c) z z :=
                  o_of_no_counted hCN hcN hvotc (no_cnt_of_cl_nil hclNc)
                have hsMc : ∀ d ∈ CL M i, Single (ρ.o d) := fun d hd => single_o hC hG
                  (mem_children (cl_mem_children hd)).2
                have hsN : ∀ d ∈ CL (TRIO.gexp M r L 0 0 n) i, Single (σ.o d) := by
                  intro d hd
                  rw [hclN] at hd
                  rcases List.mem_append.mp hd with hd | hd
                  · rw [hsame d hd]
                    exact hsMc d (by rw [hclM]; exact List.mem_append_left _ hd)
                  · simp at hd
                    rw [hd]
                    exact ⟨hIH.1, o_psi_form hCN hcN⟩
                have hpN0 : ((CL (TRIO.gexp M r L 0 0 n) i).map σ.o).Pairwise (fun a b => b ≤ a) := by
                  obtain ⟨_, hpM⟩ := cl_vals hC hG hiM
                  have hpM' := hpM
                  rw [hclM] at hpM'
                  rw [hclN, List.map_append, List.map_singleton, List.map_congr_left hsame]
                  rw [List.map_append, List.map_singleton] at hpM'
                  exact pairwise_snoc_le hpM' (le_of_lt hIHW.1)
                have hBot : isOT (psi (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) z) = true :=
                  hFO i hiM Lc c [] (by rw [hclM])
                have hparent : Lhd z (σ.o i) (ρ.o i) ∧ isOT (σ.o i) = true ∧
                    (∀ U : T → Prop, RClaimU U ρ σ i) ∧
                    (∀ X X', ρ.o i = psi (ρ.v i) X z → σ.o i = psi (ρ.v i) X' z → X' ≠ X → REr X X') := by
                  rcases hshape with hp1 | hsmS
                  · have hIHV : Lhd (ρ.v i) (σ.o c) (ρ.o c) := by
                      have h := hIHW
                      rw [hp1] at h
                      exact h
                    exact bad_frame hC hG hCN hiM (hiN i hi) hv' hclN hclM hsame hIHV hs0 hs0'
                      hsN hpN0 hBot
                  · exact bad_frameG hC hG hCN hiM (hiN i hi) hv' hclN hclM hsame hIHW hsmS hs0 hs0'
                      hsN hpN0 hBot
                exact ⟨hparent.2.1, ⟨Or.inl hparent.1, hparent.2.1⟩,
                  (fun U _ => hparent.2.2.1 U), (fun _ X X' hX hX' hne => hparent.2.2.2 X X' hX hX' hne)⟩
              · have hOTc' : isOT (σ.o c) = true := hIH.1
                have hlc : Lhd z (σ.o c) (ρ.o c) := hIHchildPX.1.resolve_right (fun hb => hBdc hb.1)
                -- the singles and the decrease at `i` in both
                obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
                have hsMc : ∀ d ∈ CL M i, Single (ρ.o d) := fun d hd => single_o hC hG
                  (mem_children (cl_mem_children hd)).2
                have hsNc : ∀ d ∈ CL (TRIO.gexp M r L 0 0 n) i, Single (σ.o d) := by
                  intro d hd
                  rw [hclN] at hd
                  rcases List.mem_append.mp hd with hd | hd
                  · rw [hsame d hd]; exact hsMc d (by rw [hclM]; exact List.mem_append_left _ hd)
                  · simp at hd; rw [hd]; exact ⟨hOTc', o_psi_form hCN hcN⟩
                have hpN0 : ((CL (TRIO.gexp M r L 0 0 n) i).map σ.o).Pairwise (fun a b => b ≤ a) := by
                  have hpM' := hpM
                  rw [hclM] at hpM'
                  rw [hclN, List.map_append, List.map_singleton, List.map_congr_left hsame]
                  rw [List.map_append, List.map_singleton] at hpM'
                  exact pairwise_snoc_le hpM' (le_of_lt hlc.1)
                obtain ⟨s, y, hsy⟩ := (single_o hC hG hcM).2
                obtain ⟨s', y', hs'y'⟩ := (show Single (σ.o c) from ⟨hOTc', o_psi_form hCN hcN⟩).2
                have hformM := o_last_form hC hiM hvot hclM hsMc hpM hsy
                have hformN := o_last_form hCN (hiN i hi) (by rw [hv']; exact hvot) hclN hsNc hpN0 hs'y'
                rw [List.map_congr_left hsame, hv'] at hformN
                set a := ρ.v i with ha
                set B := spArg a z (sumN (Lc.map ρ.o)) with hB
                have hBot : isOT B = true := isOT_arg (hFO i hiM Lc c [] (by rw [hclM]))
                have hc0 : isOT (psi s y z) = true := by rw [← hsy]; exact hG.ot_o c hcM
                have hc0' : isOT (psi s' y' z) = true := by rw [← hs'y']; exact hOTc'
                have hpL : ((Lc.map ρ.o) ++ [ρ.o c]).Pairwise (fun a b => b ≤ a) := by
                  have := hpM; rw [hclM, List.map_append, List.map_singleton] at this; exact this
                have hBc : ∀ q ∈ summands B, psi s y z ≤ q := by
                  have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => by
                    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
                    exact hsMc d (by rw [hclM]; exact List.mem_append_left _ hd))
                    (List.pairwise_append.mp hpL).1
                  apply spArg_summands_ge ⟨s, y, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
                  · rw [hLs.2]; intro q hq
                    have := (List.pairwise_append.mp hpL).2.2 q hq (ρ.o c) (by simp)
                    rwa [hsy] at this
                  · simp [summands]
                -- the child: same `v` (argument relation) or a bare changed `v`
                -- the `RClaim` scheme: `◁` from FrameClosed, the standard form from `node_ot_hard`
                have hIHR : ∀ U : T → Prop, (∀ u, U u → PathLv M (r + L) r ρ c u) → RClaimU U ρ σ c :=
                  hIH.2.2.1 rfl hdc
                have hsvc : s = ρ.v c := by
                  obtain ⟨y0, hy0⟩ := o_psi_sub hC hcM
                  rw [hsy] at hy0; simp only [psi.injEq] at hy0
                  rw [hy0.1, sf_ot (hG.ot_v c hcM)]
                have hvcot : isOT (σ.v c) = true :=
                  (ih _ (by have := (hRM c hcM).1; omega) false c (le_refl _) hcr).1
                have hs'v : s' = σ.v c := by
                  obtain ⟨y0, hy0⟩ := o_psi_sub hCN hcN
                  rw [hs'y'] at hy0; simp only [psi.injEq] at hy0
                  rw [hy0.1, sf_ot hvcot]
                -- a changed `v(c)`: `c` has no counted child, both arguments are `0`
                have hchv : σ.v c ≠ ρ.v c → y = z ∧ y' = z := by
                  intro hvc
                  have hdv : DepX M (r + L) false c := by
                    by_contra hn'; exact hvc ((hoffD c hcr).2 hn')
                  have hclc := cl_nil_of_depv' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hcr hdv
                  have hoN := o_N_noc' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hcr hclc hvcot
                  have hoM := o_of_no_counted hC hcM (hG.ot_v c hcM) (no_cnt_of_cl_nil hclc)
                  rw [hsy] at hoM; rw [hs'y'] at hoN
                  simp only [psi.injEq] at hoM hoN
                  exact ⟨hoM.2.1, hoN.2.1⟩
                have hss : y' ≠ z → s' = s := by
                  intro hyz
                  by_cases hvc : σ.v c = ρ.v c
                  · rw [hs'v, hvc, ← hsvc]
                  · exact absurd (hchv hvc).2 hyz
                -- RE at `c`, and the agreement of the rewrites
                have hREc : σ.v c = ρ.v c → y' ≠ y → REr y y' := by
                  intro hvc hne
                  have hs' : s' = s := by rw [hs'v, hvc, ← hsvc]
                  exact hIH.2.2.2 rfl hdc hvc y y' (by rw [hsy, hsvc]) (by rw [hs'y', hs', hsvc]) hne
                have htos : σ.v c = ρ.v c → (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) →
                    (lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true) ∨
                      ((split y (psi (succ s) z z)).2 = z ∧ ∃ P a' x T', y = app P (psi a' x z) ∧ y' = app P T' ∧
                        ∃ κ ∈ cutsNSG s (psi a' x z), B = app P κ ∧ ¬ κ < T') := by
                  intro hvc htr
                  by_cases hyy : y' = y
                  · rw [hyy]; exact Or.inl htr
                  exact trig_or_shadow (hREc hvc hyy) (fun hB => hPH i hiM Lc c [] (by rw [hclM]) s y hsy hB htr) htr
                have hyarg : ∀ s0, ρ.o c = psi s0 z z → ∃ s1, σ.o c = psi s1 z z := by
                  intro s0 hs0
                  have hclc : CL M c = [] := by
                    by_contra hne
                    have hlt := arg_lt_of_cl hC hG hcM hne
                    rw [o_cl_eq hC hG hcM] at hs0
                    simp only [psi.injEq] at hs0
                    rw [hs0.2.1] at hlt; exact lt_irrefl' _ hlt
                  exact ⟨_, o_N_noc' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hcr hclc hvcot⟩
                have hLi := o_frame_lhdS hC hG hF hCN hiM (hiN i hi) hv' hclN hclM hsame hsNc hlc hyarg
                  (fun s1 y1 s2 y2 h1 h2 hy2 => by
                    rw [hsy] at h1; rw [hs'y'] at h2
                    simp only [psi.injEq] at h1 h2
                    obtain ⟨rfl, rfl, -⟩ := h1; obtain ⟨rfl, rfl, -⟩ := h2
                    exact hss hy2) hpN0
                have hsub : ∀ g ∈ comps a s, g ≤ psi s z z ∨ g ≤ B := by
                  rw [hsvc]; exact hVS i hiM Lc c [] (by rw [hclM])
                have hot : isOT (psi a (step a B s y z) z) = true := by
                  rw [← hformM]; exact hG.ot_o i hiM
                have hsub' : ∀ g ∈ comps a s', g ≤ psi s' z z ∨ g ≤ B := by
                  by_cases hvc : σ.v c = ρ.v c
                  · rw [hs'v, hvc, ← hsvc]; exact hsub
                  · obtain ⟨hy0, -⟩ := hchv hvc
                    have hdv : DepX M (r + L) false c := by
                      by_contra hn'; exact hvc ((hoffD c hcr).2 hn')
                    have hlvPX : PX M Bd ρ σ false c :=
                      (ih _ (by have := (hRM c hcM).1; omega) false c (le_refl _) hcr).2.1 hdv
                    have hlv : Lhd z (σ.v c) (ρ.v c) :=
                      hlvPX.1.resolve_right (fun hb => hBdc hb.1)
                    rw [← hsvc] at hlv
                    rw [hs'v]
                    subst hy0
                    exact vs_changed_bound hvcot hlv hBc hsub hot
                have hBot' : isOT (psi a B z) = true := hFO i hiM Lc c [] (by rw [hclM])
                have hlc' : Lhd z (psi s' y' z) (psi s y z) := by rw [← hs'y', ← hsy]; exact hlc
                have hSi : isOT (psi a (step a B s' y' z) z) = true := by
                  apply node_ot_hard hc0 hc0' (Or.inr hlc') hBc hss hsub hsub' _ hot hBot'
                  intro hss' has ht' ht hhi
                  subst hss'
                  have hyy : y' ≤ y := by
                    rcases psi_lt_psi_z_iff.mp hlc'.1 with h | ⟨_, h⟩
                    · exact absurd h (lt_irrefl' _)
                    · exact le_of_lt h
                  have hot2 : isOT (psi a (H s' y) z) = true := by
                    have := hot; unfold step at this; rw [if_pos ht] at this; exact this
                  have hhz : (split y (psi (succ s') z z)).1 ≠ z := by
                    intro h; rw [h] at hhi; exact T.not_lt_z _ hhi
                  have hdi : DepX M (r + L) true i := DepX.ochild hc hcb hcu hdc
                  refine hard_of_relRU (U := fun u => u = a) hc0' has hvot hot2 (H_mono hc0' hc0 hyy) ?_ rfl
                  apply hIHR (fun u => u = a)
                    (fun u hu => by subst hu; exact PathLv.top hi hcr hclM hdi hdc hsy ht)
                    s' y y' a hsy hs'y' (fun h => lt_irrefl' _ (lt_trans (show a < s' from has) h))
                  intro u hu' hu g hg
                  subst hu'
                  rcases hVR i c Lc s' y hi hcr hclM hdi hdc hsy ht hhz _ (Or.inl rfl) hu g hg with h | h | h
                  · exact Or.inl h
                  · exact Or.inr (Or.inl (lt_of_le_of_lt h (lt_of_lt_of_le ht'.1 (le_H hc0'))))
                  · exact Or.inr (Or.inr h)
                have hPXi : PX M Bd ρ σ true i := by
                  refine ⟨Or.inl hLi, ?_⟩
                  change isOT (σ.o i) = true
                  rw [hformN]
                  exact hSi
                refine ⟨?_, hPXi, ?_, ?_⟩
                · change isOT (σ.o i) = true
                  rw [hformN]
                  exact hSi
                · -- the claim at `i`
                  intro U hU p yy yy' q hyy hyy' hqp hhyp
                  have hdi : DepX M (r + L) true i := DepX.ochild hc hcb hcu hdc
                  have hLi' := hLi
                  rw [hformM] at hyy; rw [hformN] at hyy'
                  rw [hformN, hformM] at hLi'
                  simp only [psi.injEq] at hyy hyy'
                  obtain ⟨rfl, rfl, -⟩ := hyy
                  obtain ⟨-, rfl, -⟩ := hyy'
                  exact relR_frameUL hc0 hc0' hBc (Or.inl ⟨Or.inr hlc', hss⟩) hSi hot (Or.inr hLi')
                    (fun htr hss0 q' hq' hyp' => by
                      subst hss0
                      exact hIHR U (fun u hu => PathLv.step hi hcr hclM hdi hdc hsy htr (hU u hu))
                        s' y y' q' hsy hs'y' hq' hyp')
                    (fun htr hhz u hu => hVR i c Lc s y hi hcr hclM hdi hdc hsy htr hhz u (Or.inr (hU u hu)))
                    (fun ht hne _ => by
                      exfalso
                      have hvc : σ.v c ≠ ρ.v c := fun h => hne (by rw [hs'v, h, ← hsvc])
                      have := ht.1; rw [(hchv hvc).1] at this; exact T.not_lt_z _ this)
                    (fun ht hnt hnp => by
                      by_cases hvc : σ.v c = ρ.v c
                      · have es : s' = s := by rw [hs'v, hvc, ← hsvc]
                        rw [es] at hnt ⊢
                        rcases htos hvc ht with hnew | ⟨hlo, P1, a1, x1, T1, e1, -, κ1, hκ1, hBk1, -⟩
                        · exact absurd hnew hnt
                        · have hyy : y' ≠ y := fun e => hnt (by rw [e]; exact ht)
                          obtain ⟨P0, a0, x0, T0, -, e2, hT0⟩ := hREc hvc hyy
                          have hyz' : y' ≠ z := by rw [e2]; exact app_ne_z_right hT0
                          have hyz : y ≠ z := fun e => by rw [e] at ht; exact T.not_lt_z _ ht.1
                          have hhz : (split y (psi (succ s) z z)).1 ≠ z := by
                            intro h0
                            have e := split_app (psi (succ s) z z) y
                            rw [h0, hlo] at e; simp [app] at e; exact hyz e.symm
                          have hl' : Lhd z (psi s y' z) (psi s y z) := by have h := hlc'; rw [es] at h; exact h
                          exact CutClosed.shadow_hShL_from_kind hvot hBot hc0
                            (fun hBz => hPH i hiM Lc c [] (by rw [hclM]) s y hsy hBz ht)
                            (by
                              have e := split_app (psi (succ s) z z) y
                              rw [hlo, app_z_right] at e
                              rw [e]; exact ht.1) hnp
                            hBc ht hnt hyz' hl' (by
                              have h := hSi
                              rw [es, step_eq_app_of_not (fun r hr => le_trans (le_of_lt hl'.1) (hBc r hr)) hnt] at h
                              exact h)
                            (fun u hu hau g hg => hVR i c Lc s y hi hcr hclM hdi hdc hsy ht hhz u
                              (Or.inr (hU u hu)) hau g hg)
                      · have := ht.1; rw [(hchv hvc).1] at this; exact absurd this (T.not_lt_z _))
                    hqp hhyp
                · -- RE at `i`
                  intro _ X X' hX hX' hne
                  rw [hformM] at hX; rw [hformN] at hX'
                  simp only [psi.injEq] at hX hX'
                  rw [← hX.2.1, ← hX'.2.1] at hne ⊢
                  by_cases hvc : σ.v c = ρ.v c
                  · have es : s' = s := by rw [hs'v, hvc, ← hsvc]
                    rw [es] at hne hc0' hlc' ⊢
                    have hyy' : y' ≠ y := fun h => hne (by rw [h])
                    have hlt : y' < y := by
                      rcases psi_lt_psi_z_iff.mp hlc'.1 with h | ⟨_, h⟩
                      · exact absurd h (lt_irrefl' _)
                      · exact h
                    by_cases hold : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
                    · rcases htos hvc hold with hnew | ⟨hlo, P, a', x, T', e1, e2, κ, hκ, hBk, hnk⟩
                      · exact re_step hc0 hc0' hBc hlt (hREc hvc hyy') (fun _ => hnew)
                      · by_cases hnew : lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true
                        · exact re_step hc0 hc0' hBc hlt (hREc hvc hyy') (fun _ => hnew)
                        · exact re_shadow hc0 hBc hlt hold hnew hlo e1 hBk
                    · exact re_step hc0 hc0' hBc hlt (hREc hvc hyy') (fun h => absurd h hold)
                  · obtain ⟨hy0, hy'0⟩ := hchv hvc
                    have hdv : DepX M (r + L) false c := by
                      by_contra hn'; exact hvc ((hoffD c hcr).2 hn')
                    have hlvPX : PX M Bd ρ σ false c :=
                      (ih _ (by have := (hRM c hcM).1; omega) false c (le_refl _) hcr).2.1 hdv
                    have hlv : Lhd z (σ.v c) (ρ.v c) :=
                      hlvPX.1.resolve_right (fun hb => hBdc hb.1)
                    rw [hy0] at hBc ⊢; rw [hy'0]
                    rw [hs'v, hsvc]
                    rw [hsvc] at hBc
                    exact re_leaf hlv.1 hBc

  intro b i hi
  exact key _ b i (le_refl _) hi


end
end Ytosk
