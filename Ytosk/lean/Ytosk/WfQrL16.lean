/-
**WfQrL16 (2026-11-01): the DQ engine with per-frame steps, and the shape predicates that supply them.**

`qr_engineDQ2` is `qr_engineDQ` (WfQrL10) with the two frame hypotheses replaced by the frame steps themselves
(`hOF`: last-child `o` frame, `hBW2`: bump term), each producing `DQ` with its own index.
`OFrameOK` lists the five measured shapes of the last-child `o` frame (frames.py, 0 exceptions on g36_2):
add | trig (no low part) | triglo (low part in both) | node | leafpar; `oframe_DQ` proves the step from it.
`LayerOK` lists the three shapes of an `ω` layer: generic (`OmSide`) | `ε₀` crossing | node; `layer_DQ`.
-/
import Ytosk.WfQrL15
import Ytosk.WfQrL10

namespace Ytosk.WfQrL16
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL2 Ytosk.WfQrL3 Ytosk.WfQrL4 Ytosk.WfQrL10 Ytosk.WfQrL11 Ytosk.WfQrL13
  Ytosk.WfQrL14 Ytosk.WfQrL15

section
variable {M : Mat} {x : Nat} {ρ ρN σ : Valn} {rkM : Bool → Nat → Nat}

/-- **The q = r engine in `DQ` form, with per-frame step hypotheses** (`hOF`: the last-child `o` frame,
`hBW2`: the bump term; supplied by `oframe_DQ` / `bumpW_DQ2` from the shape predicates). -/
theorem qr_engineDQ2 (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length) (hRM : Rk M rkM)
    (hxN : ρN.o x = σ.o x)
    (hEo : ∀ i, i < x → DepX M x true i → oRhs M (glueQ M x ρ ρN σ.o σ.v) i = σ.o i)
    (hEv : ∀ i, i < x → DepX M x false i → vRhs M (glueQ M x ρ ρN σ.o σ.v) i = σ.v i)
    (hX : ∃ η, DQ η false (ρ.o x) (σ.o x))
    (hOS : ∀ i, i < x → DepX M x true i → OShapeD M x i)
    (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
    -- standard form of the new values on `D` (part of `hLocT`)
    (hSo : ∀ c, c ≤ x → DepX M x true c → Single (σ.o c) ∧ isOT (σ.o c) = true)
    (hSv : ∀ i, i < x → DepX M x false i → isOT (σ.v i) = true)
    -- the last-child `o` frame step
    (hOF : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → DepX M x true c →
      (∃ η, DQ η false (ρ.o c) (σ.o c)) →
      ∃ η', DQ η' false (psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (ρ.o c)) z)
        (psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (σ.o c)) z))
    -- the state before the last counted child is standard (an `M`-side fact)
    (hPre : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → isOT (preState M ρ i L) = true)
    -- the upgrade frame: the last summand of `v(k)` changes by a single step
    (hUpgL : ∀ i k, i < x → DepX M x false i → upg M i = some k → entry M 2 i = 0 →
      Single (last (ρ.v k)) ∧ Single (last (σ.v k)) ∧
      ∀ η, DQ η true (ρ.v k) (σ.v k) → DQ η false (last (ρ.v k)) (last (σ.v k)))
    -- the bump frame: the `ω` exchange step
    (hBW2 : ∀ i L K j k, i < x → DepX M x false i → children M i = L ++ [j] → col M j = bump M i →
      children M j = K ++ [k] → DepX M x true k →
      Single (bumpW M ρ i) ∧ Single (bumpWQ M ρ i L K (σ.o k)) ∧
      ((∃ η, DQ η false (ρ.o k) (σ.o k)) → ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L K (σ.o k)))) :
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
        rw [e1, e2, sf_ot (WfQrL10.isOT_om (hSv i hi hv)), sf_ot (WfQrL10.isOT_om (hG.ot_v i hiM))]
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
        obtain ⟨η', hη'⟩ := hOF i L c R hi hd hch hcd ⟨η, hη⟩
        refine ⟨η', ?_⟩
        rw [e1, o_frame_eq hC hG hiM hch hcb hcu hR]
        exact hη'
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
        obtain ⟨hW, hW', hBη⟩ := hBW2 i L K j k hi hd hch hjb hchj hkd
        obtain ⟨η', hη'⟩ := hBη ⟨η, hη⟩
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

end

/-- The trigger of the `sp` step. -/
def Trig (v pre s y : T) : Prop := lt pre y = true ∧ lt (psi v z z) (psi s y z) = true

/-- **The five shapes of the last-child `o` frame** (`o(c) = ψ_s(y)`, `o_N(c) = oN`). -/
def OFrameOK (v pre s y oN : T) : Prop :=
  -- add: no trigger in `M` nor in `M[n]`
  (¬ Trig v pre s y ∧ Single oN ∧ ∀ s' y', oN = psi s' y' z → ¬ Trig v pre s' y') ∨
  -- trig: trigger in both, no low part
  (∃ yN, oN = psi s yN z ∧ isOT (psi s y z) = true ∧ isOT (psi s yN z) = true ∧
    Trig v pre s y ∧ Trig v pre s yN ∧ (split y (psi (succ s) z z)).2 = z ∧ (split yN (psi (succ s) z z)).2 = z ∧
    ∀ η, DQ η false (psi s y z) oN → DQ η true y yN) ∨
  -- triglo: trigger in both, low part in both, high part kept
  (∃ yN, oN = psi s yN z ∧ isOT (psi s y z) = true ∧ isOT (psi s yN z) = true ∧
    Trig v pre s y ∧ Trig v pre s yN ∧ (split y (psi (succ s) z z)).2 ≠ z ∧ (split yN (psi (succ s) z z)).2 ≠ z ∧
    (split yN (psi (succ s) z z)).1 = (split y (psi (succ s) z z)).1 ∧
    ∀ η, DQ η false (psi s y z) oN → DQ η true y yN) ∨
  -- node: `y = B + Ω_{s+1}`, a low part appears
  (∃ yN B, oN = psi s yN z ∧ isOT (psi s y z) = true ∧ isOT (psi s yN z) = true ∧
    Trig v pre s y ∧ Trig v pre s yN ∧ (split y (psi (succ s) z z)).2 = z ∧ (split yN (psi (succ s) z z)).2 ≠ z ∧
    y = app B (psi (succ s) z z) ∧ (split yN (psi (succ s) z z)).1 = B ∧ psi s yN z < psi (succ s) z z) ∨
  -- leafpar: `o(c) = Ω_{a+1}`, trigger only in `M[n]`
  (∃ a s' y' B Q, s = succ a ∧ y = z ∧ oN = psi s' y' z ∧ isOT (psi s' y' z) = true ∧
    ¬ Trig v pre (succ a) z ∧ Trig v pre s' y' ∧ (split y' (psi (succ s') z z)).2 ≠ z ∧
    add pre (psi (succ a) z z) = app B (psi (succ a) z z) ∧ (split y' (psi (succ s') z z)).1 = app B Q ∧
    (∀ q ∈ summands Q, psi s' y' z ≤ q ∧ q < psi (succ a) z z) ∧ psi s' y' z < psi (succ a) z z)

/-- **The last-child `o` frame step from its shape.** -/
theorem oframe_DQ {v pre s y oN : T} (hpre : isOT pre = true) (hd : ∃ η, DQ η false (psi s y z) oN)
    (h : OFrameOK v pre s y oN) :
    ∃ η', DQ η' false (psi v (spArg v pre (psi s y z)) z) (psi v (spArg v pre oN) z) := by
  obtain ⟨η, hη⟩ := hd
  rcases h with ⟨hnt, hoN, hntN⟩ | ⟨yN, rfl, hy, hyN, ht, htN, hlo, hloN, hdy⟩ |
      ⟨yN, rfl, hy, hyN, ht, htN, hlo, hloN, hhi, hdy⟩ | ⟨yN, B, rfl, hy, hyN, ht, htN, hlo, hloN, hyB, hhi, hlt⟩ |
      ⟨a, s', y', B, Q, rfl, rfl, rfl, hyN, hnt, htN, hloN, hadd, hhi, hQ, hlt⟩
  · exact ⟨η, frame_DQ_add hpre hoN hη hnt hntN⟩
  · exact ⟨η, frame_DQ_trig hy hyN (hdy η hη) ht htN hlo hloN⟩
  · exact ⟨η, frame_DQ_trig_lo hy hyN (hdy η hη) ht htN hlo hloN hhi⟩
  · exact frame_DQ_node hy hyN ht htN hlo hloN hyB hhi hlt
  · exact frame_DQ_leafpar hyN hnt htN hloN hadd hhi hQ hlt

/-- **The three shapes of an `ω` layer.** -/
def LayerOK (Y YN : T) : Prop :=
  (∀ η, OmSide η Y YN) ∨
  (Y = E0 ∧ YN < E0 ∧ isOT E0 = true) ∨
  (∃ a B bN, Y = psi a (app B (psi (succ a) z z)) z ∧ YN = psi a bN z ∧
    isOT (psi a (app B (psi (succ a) z z)) z) = true ∧ isOT (psi a bN z) = true ∧
    ¬ psi a (app B (psi (succ a) z z)) z < E0 ∧ ¬ psi a bN z < E0 ∧
    loOf a (app B (psi (succ a) z z)) = z ∧ loOf a bN ≠ z ∧ hiOf a bN = B ∧ psi a bN z < psi (succ a) z z)

/-- **An `ω` layer step from its shape.** -/
theorem layer_DQ {Y YN : T} (hd : ∃ η, DQ η true Y YN) (h : LayerOK Y YN) :
    ∃ η', DQ η' false (omega Y) (omega YN) := by
  obtain ⟨η, hη⟩ := hd
  rcases h with hO | ⟨rfl, hlt, hE⟩ | ⟨a, B, bN, rfl, rfl, hY, hYN, hE, hEN, hlo, hloN, hhi, hlt⟩
  · obtain ⟨hY, hYN, hsm, hQ0, hLo, hB⟩ := hO η
    exact ⟨η, omega_DQ_true hη hY hYN hsm hQ0 hLo hB⟩
  · exact omega_DQ_E0 hlt hE
  · exact omega_DQ_node hY hYN hE hEN hlo hloN hhi hlt

/-- **The bump term, two `ω` layers, each of one of the three shapes.** -/
theorem bumpW_DQ2 {P0 K0 ok oN : T} (hok : ∃ s y, ok = psi s y z) (hd : ∃ η, DQ η false ok oN)
    (hG : isOT (app K0 ok) = true)
    (L1 : LayerOK (app K0 ok) (app K0 oN))
    (L2 : LayerOK (app P0 (omega (app K0 ok))) (app P0 (omega (app K0 oN)))) :
    ∃ η', DQ η' false (omega (app P0 (omega (app K0 ok)))) (omega (app P0 (omega (app K0 oN)))) := by
  obtain ⟨η, hη⟩ := hd
  obtain ⟨η1, d2⟩ := layer_DQ ⟨η, DQ.snoc K0 hok hη⟩ L1
  have hs : ∃ s y, omega (app K0 ok) = psi s y z := (single_omega hG).2
  exact layer_DQ ⟨η1, DQ.snoc P0 hs d2⟩ L2

end Ytosk.WfQrL16
