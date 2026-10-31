/-
**WfQrL10 (2026-11-01): the q = r engine in `DQ` form** (`qr_engineDQ`).

`σ` a valuation whose glue `τ = glueQ M x ρ ρN σ.o σ.v` satisfies the local equations on `D` (the true valuation of
`M[n]`, `true_glue`).  By induction on the rank of `M`, every `D` call carries a `DQ` relation:
  `o` calls: `DQ η false (o(i)) (σ.o i)`,   `v` calls: `DQ η true (v(i)) (σ.v i)`   (some `η`),
composing the frame lemmas:
  * `o` frame, subscript only (`OShape` case 1): `DQ.sub` of the `v` relation;
  * `o` frame at the last counted child (`OShape` case 2): `o_frame_DQ` (WfQrL4) with the trigger agreement `hTrig`;
  * `v` upgrade frame (`VShape`): `v_upgDQ_glueQ` with the last-summand step `hUpgL`;
  * `v` bump frame (`VShape`): `v_bumpDQ_glueQ` with the `ω` exchange `hBW` (WfQrL2 `omega_DQ` is the tool).
No absorption, no `TPLoW`, no `fsD` form of the values.  Consequences (`qr_engineDQ_bounds`): `σ.o c ≤ o(c)` on
`D` and `σ.o Rt < o(Rt)` (`DQ.lt`), i.e. two of the facts of `hLocT` (WfQrL9).
-/
import Ytosk.WfQrL9
import Ytosk.V3HoleT1
import Ytosk.V3QRIdx

namespace Ytosk.WfQrL10
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL2 Ytosk.WfQrL4

/-- `OShape` with the `D` child named. -/
def OShapeD (M : Mat) (x i : Nat) : Prop :=
  (DepX M x false i ∧
    ∀ d ∈ children M i, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) ∨
  (¬ DepX M x false i ∧ ∃ L c R, children M i = L ++ c :: R ∧ col M c ≠ bump M i ∧
    ¬ (isUpg M c = true ∧ topped M c = true) ∧
    (∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) ∧
    (∀ d ∈ L, Counted M i d → ¬ DepX M x true d) ∧ DepX M x true c)

/-- The `o` value of a column whose children are all uncounted. -/
theorem oRhs_sub {M : Mat} {σ : Valn} {i : Nat}
    (hnc : ∀ d ∈ children M i, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) :
    oRhs M σ i = sf (psi (σ.v i) z z) := by
  have hzero : sumN ((children M i).map (cnt M σ i)) = z := by
    have : (children M i).map (cnt M σ i) = (children M i).map (fun _ => z) :=
      List.map_congr_left (fun d hd => cnt_unc σ (hnc d hd))
    rw [this, sumN_skip_z (fun t ht => by
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; exact Or.inl rfl)
      (by rw [nzs_zeros _ (fun t ht => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; rfl)]; simp),
      nzs_zeros _ (fun t ht => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; rfl)]
    rfl
  unfold oRhs; rw [hzero]

theorem isOT_om {v : T} (hv : isOT v = true) : isOT (psi v z z) = true := by
  rw [isOT_psi_iff]; exact ⟨hv, rfl, rfl, z_le _, by simp [comps]⟩

/-- The claim of the engine at a call. -/
def EngAt (ρ σ : Valn) (b : Bool) (i : Nat) : Prop :=
  match b with
  | true => ∃ η, DQ η false (ρ.o i) (σ.o i)
  | false => ∃ η, DQ η true (ρ.v i) (σ.v i)

section
variable {M : Mat} {x : Nat} {ρ ρN σ : Valn} {rkM : Bool → Nat → Nat}

/-- **The q = r engine in `DQ` form.** -/
theorem qr_engineDQ (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length) (hRM : Rk M rkM)
    (hxN : ρN.o x = σ.o x)
    (hEo : ∀ i, i < x → DepX M x true i → oRhs M (glueQ M x ρ ρN σ.o σ.v) i = σ.o i)
    (hEv : ∀ i, i < x → DepX M x false i → vRhs M (glueQ M x ρ ρN σ.o σ.v) i = σ.v i)
    (hX : ∃ η, DQ η false (ρ.o x) (σ.o x))
    (hOS : ∀ i, i < x → DepX M x true i → OShapeD M x i)
    (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
    -- standard form of the new values on `D` (part of `hLocT`)
    (hSo : ∀ c, c ≤ x → DepX M x true c → Single (σ.o c) ∧ isOT (σ.o c) = true)
    (hSv : ∀ i, i < x → DepX M x false i → isOT (σ.v i) = true)
    -- the `sp` step: the trigger is the same in `M` and in `M[n]` (no low part in the trigger case)
    (hTrig : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → DepX M x true c →
      ∀ s y, ρ.o c = psi s y z →
      (¬ (lt (preState M ρ i L) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) ∧
        ∀ s' y', σ.o c = psi s' y' z →
          ¬ (lt (preState M ρ i L) y' = true ∧ lt (psi (ρ.v i) z z) (psi s' y' z) = true)) ∨
      (∃ yN, σ.o c = psi s yN z ∧ (∀ η, DQ η false (ρ.o c) (σ.o c) → DQ η true y yN) ∧
        (lt (preState M ρ i L) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) ∧
        (lt (preState M ρ i L) yN = true ∧ lt (psi (ρ.v i) z z) (psi s yN z) = true) ∧
        (split y (psi (succ s) z z)).2 = z ∧ (split yN (psi (succ s) z z)).2 = z))
    -- the state before the last counted child is standard (an `M`-side fact)
    (hPre : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → isOT (preState M ρ i L) = true)
    -- the upgrade frame: the last summand of `v(k)` changes by a single step
    (hUpgL : ∀ i k, i < x → DepX M x false i → upg M i = some k → entry M 2 i = 0 →
      Single (last (ρ.v k)) ∧ Single (last (σ.v k)) ∧
      ∀ η, DQ η true (ρ.v k) (σ.v k) → DQ η false (last (ρ.v k)) (last (σ.v k)))
    -- the bump frame: the `ω` exchange (`omega_DQ`)
    (hBW : ∀ i L K j k, i < x → DepX M x false i → children M i = L ++ [j] → col M j = bump M i →
      children M j = K ++ [k] → DepX M x true k →
      Single (bumpW M ρ i) ∧ Single (bumpWQ M ρ i L K (σ.o k)) ∧
      ∀ η, DQ η false (ρ.o k) (σ.o k) → ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L K (σ.o k))) :
    ∀ n b i, rkM b i < n → (i < x ∨ (b = true ∧ i = x)) → DepX M x b i → EngAt ρ σ b i := by
  intro n
  induction n with
  | zero => intro b i h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro b i hrk hix hd
    rcases hix with hi | ⟨rfl, rfl⟩
    swap
    · exact hX
    have hiM : i < M.length := by omega
    obtain ⟨hrv, hrc, hr1⟩ := hRM i hiM
    cases b with
    | true =>
      show ∃ η, DQ η false (ρ.o i) (σ.o i)
      rcases hOS i hi hd with ⟨hv, hnc⟩ | ⟨hv, L, c, R, hch, hcb, hcu, hR, hLnd, hcd⟩
      · -- subscript only
        obtain ⟨η, hη⟩ := ih false i (by omega) (Or.inl hi) hv
        have e1 : σ.o i = sf (psi (σ.v i) z z) := by
          rw [← hEo i hi hd, oRhs_sub hnc, glueQ_v_dep hi hv]
        have e2 : ρ.o i = sf (psi (ρ.v i) z z) := by rw [(hC i hiM).1, oRhs_sub hnc]
        rw [e1, e2, sf_ot (isOT_om (hSv i hi hv)), sf_ot (isOT_om (hG.ot_v i hiM))]
        exact ⟨η, DQ.sub hη⟩
      · -- the last counted child
        have hc : c ∈ children M i := by rw [hch]; simp
        have hcM := (mem_children hc).2
        have hic := (mem_children hc).1
        have hcx : c ≤ x := by omega
        obtain ⟨η, hη⟩ : ∃ η, DQ η false (ρ.o c) (σ.o c) := by
          have := ih true c (by have := hrc c hc hcb hcu; omega)
            (by rcases Nat.lt_or_ge c x with h | h; exact Or.inl h; exact Or.inr ⟨rfl, by omega⟩) hcd
          exact this
        obtain ⟨hcS, hcot⟩ := hSo c hcx hcd
        have hle : σ.o c ≤ ρ.o c := le_of_lt hη.lt
        -- the new value by the frame equation
        have hsplit := cvals_split hch hcb hcu hR (single_ne_z (single_o hC hG hcM))
        have hdec := hG.dec i hiM
        rw [hsplit] at hdec
        have hp' : (nzs (L.map (cnt M ρ i)) ++ [σ.o c]).Pairwise (fun a b => b ≤ a) := by
          rw [List.pairwise_append] at hdec ⊢
          refine ⟨hdec.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
          rw [List.mem_singleton] at hb; subst hb
          exact le_trans hle (hdec.2.2 a ha _ (List.mem_singleton_self _))
        have e1 : σ.o i = psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (σ.o c)) z := by
          rw [← hEo i hi hd]
          apply oRhs_frame_gen hiM hch hcb hcu hR (glueQ_v_lt hi hv) ?_ (glueQ_o_D hxN hcx hcd)
            (hG.ot_v i hiM) ?_ hcS hp'
          · intro d hd'
            by_cases hcd' : Counted M i d
            · have hdc : d < c := by
                have hsort := children_sorted M i
                rw [hch] at hsort
                exact (List.pairwise_append.mp hsort).2.2 d hd' c List.mem_cons_self
              rw [cnt_cnt _ hcd'.1 hcd'.2, cnt_cnt _ hcd'.1 hcd'.2]
              exact glueQ_o_lt (by omega) (hLnd d hd' hcd')
            · have : col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true) := by
                by_cases h1 : col M d = bump M i
                · exact Or.inl h1
                · right; by_contra h2; exact hcd' ⟨h1, h2⟩
              rw [cnt_unc _ this, cnt_unc _ this]
          · intro t ht
            exact cnt_single hC hG i t (by rw [hch, List.map_append]; exact List.mem_append_left _ ht)
        obtain ⟨s, y, hoc⟩ : ∃ s y, ρ.o c = psi s y z := (single_o hC hG hcM).2
        have hpre : isOT (preState M ρ i L) = true := hPre i L c R hi hd hch
        refine ⟨η, ?_⟩
        rw [e1]
        apply o_frame_DQ hC hG hiM hch hcb hcu hR hoc hcS hcot hη hpre
        rcases hTrig i L c R hi hd hch hcd s y hoc with h | ⟨yN, hyN, hdy, ht, htN, hlo, hloN⟩
        · exact Or.inl h
        · exact Or.inr ⟨yN, hyN, hdy η hη, ht, htN, hlo, hloN⟩
    | false =>
      show ∃ η, DQ η true (ρ.v i) (σ.v i)
      obtain ⟨h1, hpd, hcase⟩ := hVS i hi hd
      rcases hcase with ⟨h2, hu, hk, hkd⟩ | ⟨h2, L, K, j, k, hch, hjb, hchj, hkd, hKnd, hLnd⟩
      · -- upgrade frame
        obtain ⟨η, hη⟩ : ∃ η, DQ η true (ρ.v (i + 1)) (σ.v (i + 1)) :=
          ih false (i + 1) (by have := (hr1 h1).2.1 h2 (i + 1) hu; omega) (Or.inl hk) hkd
        obtain ⟨hV, hV', hL⟩ := hUpgL i (i + 1) hi hd hu h2
        have h := v_upgDQ_glueQ (vq := σ.v) hC hG hx hi hk hkd h1 h2 hu hpd hV hV' (hL η hη)
        refine ⟨η, ?_⟩
        have e : σ.v i = sf (add (vOpt ρ (par M 1 i)) (last (σ.v (i + 1)))) := by
          rw [← hEv i hi hd]
          unfold vRhs
          rw [if_neg h1, if_pos h2, hu, vOpt_glueQ hi hpd]
          simp only
          rw [glueQ_v_dep hk hkd]
        rw [e]; exact h
      · -- bump frame
        have hj : j ∈ children M i := by rw [hch]; simp
        have hk : k ∈ children M j := by rw [hchj]; simp
        have hkx : k ≤ x := by have := (mem_children hk).2; omega
        obtain ⟨η, hη⟩ : ∃ η, DQ η false (ρ.o k) (σ.o k) := by
          have := ih true k (by have := (hr1 h1).2.2 h2 j hj hjb k hk; omega)
            (by rcases Nat.lt_or_ge k x with h | h; exact Or.inl h; exact Or.inr ⟨rfl, by omega⟩) hkd
          exact this
        obtain ⟨hW, hW', hBη⟩ := hBW i L K j k hi hd hch hjb hchj hkd
        obtain ⟨η', hη'⟩ := hBη η hη
        have h := v_bumpDQ_glueQ (ρN := ρN) (oq := σ.o) hC hG hx hxN hi h1 h2 hpd hch hjb hchj hkd hKnd hLnd hW hW' hη'
        refine ⟨η', ?_⟩
        have e : σ.v i = sf (add (vOpt ρ (par M 1 i)) (bumpWQ M ρ i L K (σ.o k))) := by
          rw [← hEv i hi hd]
          unfold vRhs
          rw [if_neg h1, if_neg h2, vOpt_glueQ hi hpd]
          have e' : omega (sumN (one :: (children M i).map (bumpTerm M (glueQ M x ρ ρN σ.o σ.v) i))) =
              bumpW M (glueQ M x ρ ρN σ.o σ.v) i := rfl
          rw [e', bumpW_glueQ hx hxN hch hjb hchj hkd hKnd hLnd]
        rw [e]; exact h

/-- **The bounds of `hLocT` from the engine**: `σ.o c < o(c)` on `D` (hence `≤`, and the root drop at `Rt`). -/
theorem engine_o_lt {c : Nat} (hc : c < x) (hcd : DepX M x true c)
    (hE : ∀ n b i, rkM b i < n → (i < x ∨ (b = true ∧ i = x)) → DepX M x b i → EngAt ρ σ b i) :
    σ.o c < ρ.o c := by
  obtain ⟨η, h⟩ : ∃ η, DQ η false (ρ.o c) (σ.o c) :=
    hE (rkM true c + 1) true c (Nat.lt_succ_self _) (Or.inl hc) hcd
  exact h.lt

end

end Ytosk.WfQrL10
