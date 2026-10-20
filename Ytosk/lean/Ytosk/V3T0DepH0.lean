/-
**3 行・t = 0: D の列を VSmallR・RClaim・RE なしで（`t0_dep_otH0`）。**

RE（と書き換えの一致、PH3c(M)・T0CutResG）は影の枠の狭め（V3T0Shadow）でだけ使うので、それを使わない
最上位（hExp_t0_topH0、drop-fix の V3TP1Cut で N の枠の 3 欄）では外せる。以下は t0_dep_otH の写し。

VSmallR は標準形で偽（t2、M13 の族）。t = 0 の帰納法で VSmallR と RClaim が使われるのは「難しい枠」
（両方書き換え、添字 s が同じ、v(i) < s、hi(y′) < hi(y)）の node_ot_hard の仮定 hy だけなので、
その結論「comps_{v(i)}(y′) の成分は H s y′ 以下」を枠ごとの仮定 `hHard` にとる（RClaim の欄は True に）。
-/
import Ytosk.V3T0DepH

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN

/-- **The `D` columns before `r` in the `RClaim` scheme** (`t = 0`, `n ≥ 2`, `r` has a parent `g`): standard,
`◁`, and `RClaim` at the `o` calls. No class is carried. -/
theorem t0_dep_otH0 {g : Nat} (hg : par M 0 r = some g) {rk : Bool → Nat → Nat} (hRM : Rk M rk)
    {ρ' : Valn} (hC1 : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i)
    (hσBv : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i)
    (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ)
    (hFO : FrameOT M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ) (hAbs : BumpAbsLo M r ρ)
    (hl : Lhd z (ρ'.o r) (ρ.o r))
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hLastC : Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hS3 : ∀ p, par M 0 g = some p → entry M 1 p ≠ 0 → entry M 2 p ≠ 0 → col M g = bump M p →
      Lhd z (σ.v p) (ρ.v p))
    (hS2 : col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → Lhd z (σ.v g) (ρ.v g))
    (hHard : HardArgN (TRIO.gexp M r L 0 0 n) r ρ σ)
    (hVchgR : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r →
      ¬ psi (ρ.v r) z z < psi (succ (ρ.v g)) z z → ¬ psi s' z z < psi (succ (ρ.v g)) z z)
    (hG0 : Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      ∀ Lc0 : List Nat, CL M g = Lc0 ++ [r] → ∀ s y, ρ.o r = psi s y z →
        ¬ (lt (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true)) :
    ∀ b i, i < r → isOT (valB σ b i) = true ∧
      (DepX M (r + L) b i → Lhd z (valB σ b i) (valB ρ b i)) ∧
      (b = true → DepX M (r + L) true i → True) ∧
      (b = true → DepX M (r + L) true i → True) := by
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
      isOT (valB σ b i) = true ∧ (DepX M (r + L) b i → Lhd z (valB σ b i) (valB ρ b i)) ∧
      (b = true → DepX M (r + L) true i → True) ∧
      (b = true → DepX M (r + L) true i → True) := by
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
        show Lhd z (σ.v i) (ρ.v i)
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
          have hIH : Lhd z (σ.v k) (ρ.v k) := (ih _ hkK false k (le_refl _) hkr).2.1 hdk
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
          rw [ek, ek']; exact hIH
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
              exact hS2 hjb h1 h2
            · have hjg : par M 0 r = some j := by
                by_contra hne
                have := children_lt_r hlen hL hp (by omega) hne hk; omega
              have hgj : g = j := Option.some.inj (hg.symm.trans hjg)
              subst hgj
              exact hS3 i (mem_children_iff.mp hj).2 h1 h2 hjb
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
              have hIH : Lhd z (σ.o k) (ρ.o k) :=
                (ih _ (by have := (hRr h1).2.2 h2 j hj hjb k hk; omega) true k (le_refl _) hkr').2.1 hdk
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
                  have hvIH : Lhd z (σ.v k) (ρ.v k) :=
                    (ih _ (by have := (hRM k (by omega)).1; have := (hRr h1).2.2 h2 j hj hjb k hk; omega)
                      false k (le_refl _) hkr').2.1 hdv
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
              exact v_bump_lhd hC hG hCN hiM (hiN i hi) h1 h2 (entry_pre0 hlen hn 1 (by omega))
                (entry_pre0 hlen hn 2 (by omega)) hV hch hchN hbL hbjM hbjN hGot hG'ot hS hlt hTD
                (hAbs i hi h1 h2)
      | true =>
        by_cases hD : DepX M (r + L) true i
        swap
        · have he := (hoffD i hi).1 hD
          exact ⟨by show isOT (σ.o i) = true; rw [he]; exact hG.ot_o i hiM, fun h => absurd h hD,
            fun _ h => absurd h hD, fun _ h => absurd h hD⟩
        suffices hmain : isOT (σ.o i) = true ∧ Lhd z (σ.o i) (ρ.o i) ∧ True ∧
            True by
          exact ⟨hmain.1, fun _ => hmain.2.1, fun _ _ => hmain.2.2.1, fun _ _ => hmain.2.2.2⟩
        have hvot : isOT (ρ.v i) = true := hG.ot_v i hiM
        cases hD with
        | leaf => omega
        | ov hv =>
          have hvIH := ih _ (by omega) false i (le_refl _) hi
          have hclM := cl_nil_of_depv' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hi hv
          have hoN := o_N_noc' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hi hclM hvIH.1
          have hoM := o_of_no_counted hC hiM hvot (no_cnt_of_cl_nil hclM)
          have hl' : Lhd z (σ.v i) (ρ.v i) := hvIH.2.1 hv
          refine ⟨by rw [hoN]; exact isOT_psi_zz hvIH.1, by rw [hoN, hoM]; exact lhd_psi_sub hl', trivial, trivial⟩
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
            obtain ⟨X, X', hX, hX', hlX, hXo, hcls⟩ := t0_S1A hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC
              hG hCN hg hcnt (fun c hc hd => (hoffD c hc).1 hd) hv' hσmid hσlast (hLastC hcnt) hl hy' hC1 hGT hm1
              hVchgR
            have hot := hG.ot_o g (by omega)
            rw [hX] at hot
            have hot' : isOT (psi (ρ.v g) X' z) = true := ot_parent_lhd hot hXo (Or.inr hlX)
            refine ⟨by rw [hX']; exact hot', by rw [hX, hX']; exact lhd_psi _ hlX,
              trivial, trivial⟩
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
              have hOTc' : isOT (σ.o c) = true := hIH.1
              have hlc : Lhd z (σ.o c) (ρ.o c) := hIH.2.1 hdc
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
                  have hlv : Lhd z (σ.v c) (ρ.v c) :=
                    (ih _ (by have := (hRM c hcM).1; omega) false c (le_refl _) hcr).2.1 hdv
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
                exact hHard i Lc c s' y y' hi hcr hclN hsy hs'y' has ht' ht hhi
              refine ⟨by rw [hformN]; exact hSi, hLi, ?_, ?_⟩
              · trivial
              · trivial

  intro b i hi
  exact key _ b i (le_refl _) hi

end

/-- **`hOTD` without VSmallR** (`t = 0`, residual `HardArgN`): the `D` columns before `r` of `N = M[n]` are standard, drop
by `◁`, and carry `RClaim`; a changed `v` gives `ψ_{v}(0)`. Residuals: PH3c of `M` and `hCutN` (the cut in the
last summand), with which the right-end change RE is carried and a rewriting frame keeps rewriting. -/
theorem t0_otdH0 (hU0 : OldUpgAbs) {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ) (hAbsS : BumpAbsLo M r ρ)
    (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsXW M (r + L) ρ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hLast : ∀ n, 2 ≤ n → ∀ g, par M 0 r = some g → Counted M g r →
      Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hHardN : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → HardArgN (TRIO.gexp M r L 0 0 n) r ρ σ)
    (hVchgRN : ∀ g, par M 0 r = some g → ∀ s' y', (drop1 M (r + L) rkM).o r = psi s' y' z → s' ≠ ρ.v r →
      ¬ psi (ρ.v r) z z < psi (succ (ρ.v g)) z z → ¬ psi s' z z < psi (succ (ρ.v g)) z z)
    (hG0N : ∀ n, 2 ≤ n → ∀ g, par M 0 r = some g →
      Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      ∀ Lc0 : List Nat, CL M g = Lc0 ++ [r] → ∀ s y, ρ.o r = psi s y z →
        ¬ (lt (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true)) :
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i, i < r → (DepX M (r + L) true i → isOT (σ.o i) = true ∧ Lhd z (σ.o i) (ρ.o i) ∧ True ∧
        (σ.v i ≠ ρ.v i → σ.o i = psi (σ.v i) z z) ∧
        True) ∧
        (DepX M (r + L) false i → isOT (σ.v i) = true ∧ Lhd z (σ.v i) (ρ.v i)) := by
  intro n hn2 σ hCN
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := hR12 _ he1
  -- the drop `M.take x`
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  set ρ' := drop1 M (r + L) rkM with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hdrop := drop_all (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hVSt hF hFO hArgT
    (bump_drop (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hKD hTD hAbs hWS) hUA
  have hoff := chg_off (show r + L + 1 = M.length from hlen) hC hG hC1 hRk1
  have hVT : ValInv (M.take (r + L)) ρ' :=
    drop_pres (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC
      ⟨hG, hVS, hF, hFO, hKD, hTD⟩ ⟨hArgT, hVSt, hWS, hUA, hAbs⟩ hC1 hRk1
  have hnx : ¬ DepX M (r + L) false (r + L) := not_depX_v_x he1
  have hD := dep_strict0 (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hx2 hp hnx
  -- the expansion `N`
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hnl : (n - 1) * L + L = n * L := by rw [← Nat.succ_mul]; congr 1; omega
  have hRN := rk_N0 hlen hL hp hn hR0 hZ2 hx2 hn2 hRM
  -- the values of `N`
  have hvC := t0_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB) hC hG hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB) hC hG hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i) := by
    intro i hi
    have h := hvD i (by rw [hlN]; omega)
    exact ⟨fun hd => by rw [h.1 (fun h' => hd h'.2), tau_o_lt hi],
      fun hd => by rw [h.2 (fun h' => hd h'.2), tau_v_lt hi]⟩
  have hσB : ∀ i, r ≤ i → i < N.length → σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i :=
    fun i hri hiN => (hvC i hiN).1 (fun h => by omega)
  have hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ := by
    intro k hk
    have : k * L + L ≤ n * L := by
      have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
    rw [hσB _ (by omega) (by rw [hlN]; omega)]
    exact tau_o_root hk hL
  have hσlast : σ.o (r + (n - 1) * L) = ρ'.o r := by
    rw [hσB _ (by omega) (by rw [hlN]; omega)]
    have := tau_o_last (r := r) (L := L) (n := n) (ρ := ρ) (ρ' := ρ') (oMid := omid M r L ρ) hL
    rwa [Nat.add_zero, Nat.add_zero] at this
  have hGT := good3_take (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG
  -- roots, frames
  have hOXle : omid M r L ρ ≤ ρ.o r := by
    rw [hor, hom]; exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one _⟩))
  have hlt0 : ρ'.o r < ρ.o r :=
    hD true r (depLike_r hlen hL hp hx2 (depLike_depX M (r + L))) (by omega)
  have hO'le : ρ'.o r ≤ omid M r L ρ := by
    obtain ⟨_, s', y', hs'⟩ := (hdrop r (by omega)).1.2
    have h := hlt0
    rw [hs', hor] at h
    rw [hs', hom]
    rcases psi_lt_psi_z_iff.mp h with h1 | ⟨rfl, h2⟩
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h1))
    · exact psi_le_psi_arg ((lt_succ_iff (x := _)).mp h2)
  have hσBv : ∀ i, r ≤ i → i < N.length → σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i :=
    fun i hri hiN => (hvC i hiN).2 (fun h => by omega)
  have hFOT : FrameOT (M.take (r + L)) ρ' :=
    frameOT_take (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hFO
  by_cases hrg : ∃ g, par M 0 r = some g
  · obtain ⟨g, hg⟩ := hrg
    have hgr : g < r := par_lt M 0 r g hg
    have hrc : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
    have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
    -- the drop at `r`
    have hDr : DepX M (r + L) true r := depLike_r hlen hL hp hx2 (depLike_depX M (r + L))
    have hlt : ρ'.o r < ρ.o r := hD true r hDr (by omega)
    have hl : Lhd z (ρ'.o r) (ρ.o r) := by
      rcases PO.zero_t0 (by omega) hUA he1 hp (fun _ _ => hU0 _ _ _) hC hG (by omega) (hdrop r (by omega)).1 (hdrop r (by omega)).2 with hE | ⟨_, w, hw⟩
      · exact lhd_of_lhdE_lt hE hlt
      · exfalso
        rw [hor] at hw; simp only [psi.injEq] at hw
        have := lt_app_one (spArg (ρ.v r) z
          (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r))))
        rw [hw.2.1] at this; exact T.not_lt_z _ this
    have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
    have hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z := by
      intro s' y' hs hne
      obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
      rw [hs] at hy0; simp only [psi.injEq] at hy0
      have hv'ot := (hdrop r (by omega)).2.2
      rw [sf_ot hv'ot] at hy0
      have hCv : ChgX M (r + L) false r := by
        by_contra hn'; apply hne; rw [hy0.1]; exact (hoff r (by omega)).2 hn'
      have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl (by omega)
      have ho := o_of_no_counted hC1 hrT hv'ot hT.2.1
      rw [hs] at ho; simp only [psi.injEq] at ho; exact ho.2.1
    have hG0le : ∀ g', par M 0 r = some g' → col M r = bump M g' → entry M 1 g' ≠ 0 → entry M 2 g' ≠ 0 →
        sumN ((children (M.take (r + L)) r).map ρ'.o) ≤ sumN ((children (M.take (r + L)) r).map ρ.o) := by
      intro g' hg' hjb h1 h2
      have hgg : g' = g := Option.some.inj (hg'.symm.trans hg)
      rw [hgg] at hjb h1 h2
      exact (brelS_lhdE (g0_drop_rel (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG
        hC1 hRk1 hKD hWS h1 h2 hrc hjb hxr (o_x_one hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG)
        (fun k _ hk => hdrop k hk)
        (fun k hk hkx _ => v_lhd_B (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hp
          hC hG hC1 hRk1 hKD hTD hAbs hWS (hU0 _ _ _) hdrop k (mem_children hk).1 hkx)).2).le
    -- seed S2
    have hS2 : col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → Lhd z (σ.v g) (ρ.v g) := by
      intro hjb h1 h2
      have hgD : DepX M (r + L) false g := DepX.vbump h1 h2 hrc hjb hxr DepX.leaf
      obtain ⟨_, hpnd, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hp (by omega) hgD
      rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j', k', hch, _, hchj, _, hKnd, hLnd⟩
      · exact absurd h2' h2
      · have hchM := children_g_last hlen hL hp hg
        have hjr : j' = r := by
          have := congrArg List.getLast? (hch.symm.trans hchM)
          simpa using this
        subst hjr
        -- the children of `r` in `M.take x` and the last copy
        have hdropR : isOT (sumN ((children (M.take (j' + L)) j').map ρ'.o)) = true ∧
            BRelS (sumN ((children (M.take (j' + L)) j').map ρ'.o))
              (sumN ((children (M.take (j' + L)) j').map ρ.o)) :=
          g0_drop_rel (show j' + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hKD hWS
            h1 h2 hrc hjb hxr (o_x_one hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG)
            (fun k _ hk => hdrop k hk)
            (fun k hk hkx _ => v_lhd_B (show j' + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hp
              hC hG hC1 hRk1 hKD hTD hAbs hWS (hU0 _ _ _) hdrop k (mem_children hk).1 hkx)
        have hG0ot : isOT (sumN ((children (M.take (j' + L)) j').map ρ.o)) = true := isOT_sumN _ (fun t ht => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
          rw [children_take, List.mem_filter] at hc
          exact hG.ot_o c (mem_children hc.1).2)
        have hcopy : ∀ k, k < n → bumpTerm N σ g (j' + k * L) =
            omega (sumN (((children M j').filter (fun c => decide (c < j' + L))).map
              (σ.o ∘ shk j' (k * L)))) := by
          intro k hk
          have hcolk : col N (j' + k * L) = bump N g := by
            rw [col_root0 hlen hL hp hn hk, bump_pre0 hlen hL hp hn (by omega)]; exact hjb
          unfold bumpTerm
          rw [if_pos hcolk]
          have hch0 := children_copy0 hlen hL hp hn (k := k) (q := 0) hk hL
          rw [Nat.add_zero, Nat.add_zero] at hch0
          rw [hch0, List.map_map]
        apply t0_S2G (O' := omega (sumN ((children (M.take (j' + L)) j').map ρ'.o))) hlen hL hp hn hR0 hZ2
          hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hg hjb h1 h2 hTD (AbsWN.of_strong hAbsS)
        · intro d hd hdr
          have hdL : d ∈ Lb := by
            rw [hch] at hd
            rcases List.mem_append.mp hd with h | h
            · exact h
            · simp at h; omega
          have hdg : par M 0 j' ≠ some d := by
            intro h'; rw [hg] at h'; cases h'; have := (mem_children hd).1; omega
          apply bumpTerm_eq_of
          · rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
          · intro _
            rw [children_pre0 hlen hL hp hn hdr hdg]
            apply List.map_congr_left
            intro e he
            have her := children_lt_r hlen hL hp hdr hdg he
            exact (hoffD e her).1 (hLnd d hdL e he).2
        · intro k hkn
          rw [hcopy k (by omega), children_take]
          congr 1; congr 1
          apply List.map_congr_left
          intro c hc
          rw [List.mem_filter] at hc
          have hcgt := (mem_children hc.1).1
          have hcx : c < j' + L := by simpa using hc.2
          obtain ⟨q', rfl⟩ : ∃ q', c = j' + q' := ⟨c - j', by omega⟩
          simp only [Function.comp]
          rw [shk_B, hσB _ (by omega) (by
            rw [hlN]; have : k * L + L ≤ n * L := by
              have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this
              exact this
            omega), tau_o_mid hkn (by omega) (by omega)]
        · rw [hcopy (n - 1) (by omega), children_take]
          congr 1; congr 1
          apply List.map_congr_left
          intro c hc
          rw [List.mem_filter] at hc
          have hcgt := (mem_children hc.1).1
          have hcx : c < j' + L := by simpa using hc.2
          obtain ⟨q', rfl⟩ : ∃ q', c = j' + q' := ⟨c - j', by omega⟩
          simp only [Function.comp]
          rw [shk_B, hσB _ (by omega) (by rw [hlN]; omega), tau_o_last (by omega)]
        · exact single_omega hdropR.1
        · exact brelS_lhdE (brelS_omega hdropR.1 hG0ot hdropR.2)
        · rw [par1_pre0 hlen hL hp hn hgr]
          cases hpp : par M 1 g with
          | none => rfl
          | some m =>
            have := par_lt M 1 g m hpp
            exact (hoffD m (by omega)).2 (hpnd m hpp)
    -- seed S3
    have hS3 : ∀ pp, par M 0 g = some pp → entry M 1 pp ≠ 0 → entry M 2 pp ≠ 0 → col M g = bump M pp →
        Lhd z (σ.v pp) (ρ.v pp) := by
      intro pp hpg h1 h2 hjb
      have hppg := par_lt M 0 g pp hpg
      have hgp : g ∈ children M pp := mem_children_iff.mpr ⟨by omega, hpg⟩
      have hpD : DepX M (r + L) false pp := DepX.vbump h1 h2 hgp hjb hrc hDr
      obtain ⟨_, hpnd, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hp (by omega) hpD
      rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j', k', hch, _, hchj, _, hKnd, hLnd⟩
      · exact absurd h2' h2
      · have hjg : j' = g := by
          by_contra hne
          have hgL : g ∈ Lb := by
            rw [hch] at hgp
            rcases List.mem_append.mp hgp with h | h
            · exact h
            · simp at h; exact absurd h.symm hne
          exact (hLnd g hgL r hrc).2 hDr
        subst hjg
        have hkr : k' = r := by
          have hchM := children_g_last hlen hL hp hg
          rw [hchj] at hchM
          have := congrArg List.getLast? hchM
          simpa using this
        rw [hkr] at hchj
        have hLj : ∀ d ∈ Lb, d < j' :=
          (sib_order (children_sorted M pp) (R := []) (by rw [hch])).1
        apply t0_S3 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hg hpg hjb h1 h2
          hTD hKD (AbsWN.of_strong hAbsS) hch
        · intro d hd
          have hdg : par M 0 r ≠ some d := fun h =>
            (hLnd d hd r (mem_children_iff.mpr ⟨by have := hLj d hd; omega, h⟩)).2 hDr
          have hdj := hLj d hd
          apply bumpTerm_eq_of
          · rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
          · intro _
            rw [children_pre0 hlen hL hp hn (by omega) hdg]
            apply List.map_congr_left
            intro e he
            have her := children_lt_r hlen hL hp (by omega) hdg he
            exact (hoffD e her).1 (hLnd d hd e he).2
        · intro d hd hdr
          have hdK : d ∈ Kb := by
            rw [hchj] at hd
            rcases List.mem_append.mp hd with h | h
            · exact h
            · simp at h; omega
          exact (hoffD d hdr).1 (hKnd d hdK)
        · exact hor
        · intro k hk; rw [hσmid k hk, hom]
        · rw [hσlast]; exact hl
        · rw [par1_pre0 hlen hL hp hn (by omega)]
          cases hpp : par M 1 pp with
          | none => rfl
          | some m =>
            have := par_lt M 1 pp m hpp
            exact (hoffD m (by omega)).2 (hpnd m hpp)
        · intro k hk
          by_cases hkn : k + 1 < n
          · rw [hσmid k hkn]; exact isOT_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN
          · rw [show k = n - 1 by omega, hσlast]; exact hGT.ot_o r (by rw [List.length_take]; omega)
    intro i hi
    have hdep := t0_dep_otH0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hg hRM hC1 hGT hσB hσBv
      hoffD hσmid hσlast hF hVS hFO hTD hKD hAbsS hl hy' (hLast n hn2 g hg) hS3 hS2
      (hHardN n hn2 σ hCN) (hVchgRN g hg) (hG0N n hn2 g hg)
    refine ⟨fun hd => ?_, fun hd => ⟨(hdep false i hi).1, (hdep false i hi).2.1 hd⟩⟩
    obtain ⟨hot, hlt, hR, hRE⟩ := hdep true i hi
    refine ⟨hot, hlt hd, hR rfl hd, fun hne => ?_, hRE rfl hd⟩
    have hdv : DepX M (r + L) false i := by
      by_contra hn'; exact hne ((hoffD i hi).2 hn')
    exact o_N_noc' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hi
      (cl_nil_of_depv' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hi hdv) (hdep false i hi).1
  · have hrn : par M 0 r = none := by
      cases h : par M 0 r with
      | none => rfl
      | some g => exact absurd ⟨g, h⟩ hrg
    intro i hi
    refine ⟨fun hd => ?_, fun hd => ?_⟩
    · have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn true i hd
      omega
    · have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn false i hd
      omega

end Ytosk
