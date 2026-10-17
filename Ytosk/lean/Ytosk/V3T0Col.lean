/-
**3 行・t = 0: 列ごとの値の欄 AbsDN・TPLo を N = M[n] に運ぶ。**

N の列は、r より前で D に入らない列（M と同じ値）、写しの列（中間の写しは M の、最後の写しは M.take x の値）、
r より前の D の列、中間の写しの根（o = omid）に分かれる。
- AbsDN は v(i)・v(P_1 i) と行 1・行 2 だけで決まる（bumpW = v の最後の加数、`t0c_bumpW_last`）。
  中間の写しの根の v は M と同じなので、残りは r より前で v が変わる列だけ（`T0AbsDNRes`）。
- TPLo は o(c) だけで決まる。残りは r より前で o が変わる列と中間の写しの根（`T0TPLoRes`）。
-/
import Ytosk.V3T0Phi

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The bump term is the last summand of `v`** at a column with rows 1 and 2 nonzero. -/
theorem t0c_bumpW_last {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {k : Nat} (hkM : k < M.length)
    (h1k : entry M 1 k ≠ 0) (h2k : entry M 2 k ≠ 0) : bumpW M ρ k = last (ρ.v k) := by
  have hVot : isOT (vOpt ρ (par M 1 k)) = true := by
    cases hp : par M 1 k with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 k m hp; omega)
  have hoot : ∀ j ∈ children M k, col M j = bump M k → ∀ k' ∈ children M j, isOT (ρ.o k') = true :=
    fun j _ _ k' hk' => hG.ot_o k' (mem_children hk').2
  obtain ⟨sW, yW, hv, _, _⟩ := v_bump_form hC hkM h1k h2k hVot hoot
  have hY : isOT (sumN (one :: (children M k).map (bumpTerm M ρ k))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      unfold bumpTerm
      split
      · rename_i hjb
        apply isOT_omega; apply isOT_sumN
        intro t' ht'
        obtain ⟨k', hk', rfl⟩ := List.mem_map.mp ht'
        exact hoot j hj hjb k' hk'
      · rfl
  have hv' := (hC k hkM).2
  unfold vRhs at hv'
  rw [if_neg h1k, if_neg h2k, sf_ot (isOT_add hVot (isOT_omega hY))] at hv'
  obtain ⟨s', y', hs'⟩ := (single_omega hY).2
  unfold bumpW; rw [hs', hv', hs', last_add_single]

/-- The `AbsDN` condition at one column, in terms of its values. -/
def AbsDNAt (W V : T) : Prop :=
  OHole W → cof W = .omega → NotNode W → ∀ q ∈ summands V, q < W → q < fsD W one

theorem absDN_at {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (h : AbsDN M ρ) {i : Nat}
    (hi : i < M.length) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) :
    AbsDNAt (last (ρ.v i)) (vOpt ρ (par M 1 i)) := by
  rw [← t0c_bumpW_last hC hG hi h1 h2]
  exact h i hi h1 h2

/-- **Residual of `AbsDN`**: the columns before `r` whose `v` changes. -/
def T0AbsDNRes : Prop :=
  ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN → ∀ i, i < r → DepX M (r + L) false i →
    entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
    AbsDNAt (last (σ.v i)) (vOpt σ (par M 1 i))

/-- **Residual of `TPLo`**: the columns before `r` whose `o` changes, and the middle copy roots. -/
def T0TPLoRes : Prop :=
  ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN →
    ∀ c, (c < r ∧ DepX M (r + L) true c) ∨ (∃ k, k + 1 < n ∧ c = r + k * L) →
    ∀ s y, σ.o c = psi s y z → (split y (psi (succ s) z z)).2 = z →
      ∀ a, last y = psi a z z → isSucc a = false → OHole a →
        ¬ psi (fsD a (etaOm (holeLev y))) z z < psi (succ s) z z

/-- **The value facts of `N`** (`t = 0`) from the context, with `ρ′ = drop1 M x rk` the valuation of
`M.take x`, and a valuation `τ` of `M.take x` with its invariants agreeing with `ρ′`. -/
theorem t0_vals_ctx {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L n : Nat} {σ : Valn}
    {rkN : Bool → Nat → Nat} (hctx : T0Ctx M ρ rk r L n σ rkN) :
    (∀ i, i < r → ¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
    (∀ i, i < r → ¬ DepX M (r + L) false i → σ.v i = ρ.v i) ∧
    (∀ k q, k + 1 < n → q < L → σ.v (r + (k * L + q)) = ρ.v (r + q)) ∧
    (∀ q, q < L → σ.v (r + ((n - 1) * L + q)) = (drop1 M (r + L) rk).v (r + q)) ∧
    (∀ k q, k + 1 < n → q < L → 0 < q → σ.o (r + (k * L + q)) = ρ.o (r + q)) ∧
    (∀ q, q < L → σ.o (r + ((n - 1) * L + q)) = (drop1 M (r + L) rk).o (r + q)) ∧
    (∀ m d, r ≤ d → d < r + L → (par M 1 d = some m ∨ (upg M d = some m ∧ m < d)) → m < r →
      σ.v m = ρ.v m ∧ (drop1 M (r + L) rk).v m = ρ.v m) ∧
    (∃ τ rkT, Inv3 (M.take (r + L)) τ rkT ∧ ∀ i, i < r + L →
      τ.o i = (drop1 M (r + L) rk).o i ∧ τ.v i = (drop1 M (r + L) rk).v i) := by
  obtain ⟨_, _, I, _, hlen, hL, hp, he1, hTx, hn2, hCN, hRN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  set ρ' := drop1 M (r + L) rk with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hkL : ∀ k, k + 1 < n → k * L + L ≤ n * L := fun k hk => by
    have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
  have hnl : (n - 1) * L + L = n * L := by rw [← Nat.succ_mul]; congr 1; omega
  have hvC := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  refine ⟨fun i hi hd => ?_, fun i hi hd => ?_, fun k q hk hq => ?_, fun q hq => ?_,
    fun k q hk hq hq0 => ?_, fun q hq => ?_, fun m d hrd hdx hpd hmr => ?_, ?_⟩
  · rw [(hvD i (by rw [hlN]; omega)).1 (fun h' => hd h'.2), tau_o_lt hi]
  · rw [(hvD i (by rw [hlN]; omega)).2 (fun h' => hd h'.2), tau_v_lt hi]
  · have := hkL k hk
    rw [(hvC _ (by rw [hlN]; omega)).2 (fun h => by omega), tau_v_mid hk hq]
  · rw [(hvC _ (by rw [hlN]; omega)).2 (fun h => by omega), tau_v_last hq]
  · have := hkL k hk
    rw [(hvC _ (by rw [hlN]; omega)).1 (fun h => by omega), tau_o_mid hk hq hq0]
  · rw [(hvC _ (by rw [hlN]; omega)).1 (fun h => by omega), tau_o_last hq]
  · have hnd := read_not_dep hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab m d hrd hdx hpd
    have hnc := read_not_chg hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab m d hrd hdx hpd
    refine ⟨?_, (hoff m (by omega)).2 hnc⟩
    rw [(hvD m (by rw [hlN]; omega)).2 (fun h' => hnd h'.2), tau_v_lt hmr]
  · obtain ⟨τ, rkT, IT, _⟩ := hTx
    exact ⟨τ, rkT, IT, fun i hi => agree_of_cons IT.cons hC1 IT.rank i (by rw [List.length_take]; omega)⟩

/-- A column of `N` at or after `r` is a copy column `r + (k L + q)`. -/
theorem copy_decomp {r L n i : Nat} (hL : 0 < L) (hri : r ≤ i) (hi : i < r + n * L) :
    ∃ k q, k < n ∧ q < L ∧ i = r + (k * L + q) := by
  refine ⟨(i - r) / L, (i - r) % L, ?_, Nat.mod_lt _ hL, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hL]; omega
  · have := Nat.div_add_mod (i - r) L; rw [Nat.mul_comm] at this; omega

/-- **`AbsDN` of `N`** (`t = 0`) from that of `M` and `M.take x`, with the residual at the changed `v` columns. -/
theorem t0_absDN (hRes : T0AbsDNRes) : T0Field AbsDN := by
  intro M ρ rk r L n σ rkN hctx
  obtain ⟨hoffo, hoffv, hmidv, hlastv, hmido, hlasto, hread, τ, rkT, IT, hag⟩ := t0_vals_ctx hctx
  obtain ⟨_, _, I, _, hlen, hL, hp, he1, _, hn2, hCN, _, hGN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen hn
  intro i hi h1 h2
  rw [t0c_bumpW_last hCN hGN hi h1 h2]
  change AbsDNAt (last (σ.v i)) (vOpt σ (par (TRIO.gexp M r L 0 0 n) 1 i))
  rcases Nat.lt_or_ge i r with hir | hir
  · rw [entry_pre0 hlen hn 1 (by omega)] at h1
    rw [entry_pre0 hlen hn 2 (by omega)] at h2
    rw [par1_pre0 hlen hL hp hn hir]
    by_cases hd : DepX M (r + L) false i
    · exact hRes M ρ rk r L n σ rkN hctx i hir hd h1 h2
    · have hV : vOpt σ (par M 1 i) = vOpt ρ (par M 1 i) := by
        cases hpm : par M 1 i with
        | none => rfl
        | some m =>
          have hmi := par_lt M 1 i m hpm
          exact hoffv m (by omega) (fun hdm => hd (DepX.vpar h1 hpm hdm))
      rw [hoffv i hir hd, hV]
      exact absDN_at I.cons I.good I.adn (by omega) h1 h2
  · obtain ⟨k, q, hk, hq, rfl⟩ := copy_decomp hL hir (lt_of_lt_of_eq hi hlN)
    rw [entry_copy0 hlen hk hq 1] at h1
    rw [entry_copy0 hlen hk hq 2] at h2
    rw [par1_copy0 hlen hL hp hn hk hq]
    have hrqM : r + q < M.length := by omega
    by_cases hkn : k + 1 < n
    · have hV : vOpt σ ((par M 1 (r + q)).map (shk r (k * L))) = vOpt ρ (par M 1 (r + q)) := by
        cases hpm : par M 1 (r + q) with
        | none => rfl
        | some m =>
          have hm := par_lt M 1 (r + q) m hpm
          show σ.v (shk r (k * L) m) = ρ.v m
          unfold shk
          split
          · rename_i hrm
            rw [show m + k * L = r + (k * L + (m - r)) by omega, hmidv k (m - r) hkn (by omega),
              show r + (m - r) = m by omega]
          · exact (hread m (r + q) (by omega) (by omega) (Or.inl hpm) (by omega)).1
      rw [hmidv k q hkn hq, hV]
      exact absDN_at I.cons I.good I.adn hrqM h1 h2
    · have hk' : k = n - 1 := by omega
      subst hk'
      have hrqT : r + q < (M.take (r + L)).length := by rw [List.length_take]; omega
      have hV : vOpt σ ((par M 1 (r + q)).map (shk r ((n - 1) * L))) = vOpt τ (par (M.take (r + L)) 1 (r + q)) := by
        rw [par_take M 1 (r + q) (by omega)]
        cases hpm : par M 1 (r + q) with
        | none => rfl
        | some m =>
          have hm := par_lt M 1 (r + q) m hpm
          show σ.v (shk r ((n - 1) * L) m) = τ.v m
          rw [(hag m (by omega)).2]
          unfold shk
          split
          · rename_i hrm
            rw [show m + (n - 1) * L = r + ((n - 1) * L + (m - r)) by omega, hlastv (m - r) (by omega),
              show r + (m - r) = m by omega]
          · obtain ⟨h1', h2'⟩ := hread m (r + q) (by omega) (by omega) (Or.inl hpm) (by omega)
            rw [h1', h2']
      rw [hlastv q hq, ← (hag (r + q) (by omega)).2, hV]
      exact absDN_at IT.cons IT.good IT.adn hrqT (by rw [entry_take M 1 (by omega)]; exact h1)
        (by rw [entry_take M 2 (by omega)]; exact h2)

/-- **`TPLo` of `N`** (`t = 0`) from that of `M` and `M.take x`, with the residual at the changed `o` columns
and the middle copy roots. -/
theorem t0_tplo (hRes : T0TPLoRes) : T0Field TPLo := by
  intro M ρ rk r L n σ rkN hctx
  obtain ⟨hoffo, hoffv, hmidv, hlastv, hmido, hlasto, hread, τ, rkT, IT, hag⟩ := t0_vals_ctx hctx
  obtain ⟨_, _, I, _, hlen, hL, hp, he1, _, hn2, hCN, _, hGN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen hn
  intro c hc
  rcases Nat.lt_or_ge c r with hcr | hcr
  · by_cases hd : DepX M (r + L) true c
    · exact hRes M ρ rk r L n σ rkN hctx c (Or.inl ⟨hcr, hd⟩)
    · rw [hoffo c hcr hd]; exact I.tplo c (by omega)
  · obtain ⟨k, q, hk, hq, rfl⟩ := copy_decomp hL hcr (lt_of_lt_of_eq hc hlN)
    by_cases hkn : k + 1 < n
    · by_cases hq0 : q = 0
      · subst hq0
        exact hRes M ρ rk r L n σ rkN hctx _ (Or.inr ⟨k, hkn, by omega⟩)
      · rw [hmido k q hkn hq (by omega)]; exact I.tplo (r + q) (by omega)
    · have hk' : k = n - 1 := by omega
      subst hk'
      rw [hlasto q hq, ← (hag (r + q) (by omega)).1]
      exact IT.tplo (r + q) (by rw [List.length_take]; omega)

/-- The `AbsUW` condition at an upgrade pair, in terms of its values. -/
def AbsUWAt (W V : T) : Prop :=
  OHole W → cof W = .omega → ∀ q ∈ summands V, q < W → q < fsD W one

/-- **Residual of `AbsUW`**: the pairs before `r` whose `v` changes, and the pair `(x − 1, r)` copied into the
next to last block, whose target becomes the last copy root (with the `v` of `M.take x`). -/
def T0AbsUWRes : Prop :=
  ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN →
    (∀ i k, i < r → DepX M (r + L) false i → upg M i = some k →
      AbsUWAt (last (σ.v k)) (vOpt σ (par M 1 i))) ∧
    (upg M (r + (L - 1)) = some r →
      AbsUWAt (last ((drop1 M (r + L) rk).v r)) (vOpt ρ (par M 1 (r + (L - 1)))))

/-- **`AbsUW` of `N`** (`t = 0`) from that of `M` and `M.take x`, with the residual `T0AbsUWRes`. -/
theorem t0_absUW (hRes : T0AbsUWRes) : T0Field AbsUW := by
  intro M ρ rk r L n σ rkN hctx
  obtain ⟨hoffo, hoffv, hmidv, hlastv, hmido, hlasto, hread, τ, rkT, IT, hag⟩ := t0_vals_ctx hctx
  obtain ⟨_, _, I, _, hlen, hL, hp, he1, _, hn2, hCN, _, hGN, _⟩ := id hctx
  obtain ⟨hR1, hR2⟩ := hRes M ρ rk r L n σ rkN hctx
  have hn : 1 ≤ n := by omega
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen hn
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  -- the `v` of a column `t < x` read from a block column of a middle copy
  have hvM : ∀ t d, r ≤ d → d < r + L → (par M 1 d = some t ∨ (upg M d = some t ∧ t < d)) → t < r + L →
      σ.v t = ρ.v t := by
    intro t d hrd hdx ht htx
    rcases Nat.lt_or_ge t r with htr | htr
    · exact (hread t d hrd hdx ht htr).1
    · have := hmidv 0 (t - r) (by omega) (by omega)
      rwa [show r + (0 * L + (t - r)) = t by omega, show r + (t - r) = t by omega] at this
  -- the shifted `v` in a middle block and in the last block
  have hsh : ∀ k t d, k + 1 < n → r ≤ d → d < r + L → (par M 1 d = some t ∨ (upg M d = some t ∧ t < d)) →
      t < d → σ.v (shk r (k * L) t) = ρ.v t := by
    intro k t d hk hrd hdx ht htd
    unfold shk
    split
    · rename_i hrt
      rw [show t + k * L = r + (k * L + (t - r)) by omega, hmidv k (t - r) hk (by omega),
        show r + (t - r) = t by omega]
    · rename_i hrt
      exact (hread t d hrd hdx ht (by omega)).1
  have hshL : ∀ t d, r ≤ d → d < r + L → (par M 1 d = some t ∨ (upg M d = some t ∧ t < d)) →
      t < d → σ.v (shk r ((n - 1) * L) t) = τ.v t := by
    intro t d hrd hdx ht htd
    rw [(hag t (by omega)).2]
    unfold shk
    split
    · rename_i hrt
      rw [show t + (n - 1) * L = r + ((n - 1) * L + (t - r)) by omega, hlastv (t - r) (by omega),
        show r + (t - r) = t by omega]
    · rename_i hrt
      obtain ⟨h1', h2'⟩ := hread t d hrd hdx ht (by omega)
      rw [h1', h2']
  have hvopt : ∀ k d, k + 1 < n → r ≤ d → d < r + L →
      vOpt σ ((par M 1 d).map (shk r (k * L))) = vOpt ρ (par M 1 d) := by
    intro k d hk hrd hdx
    cases hpm : par M 1 d with
    | none => rfl
    | some m => exact hsh k m d hk hrd hdx (Or.inl hpm) (par_lt M 1 d m hpm)
  have hvoptL : ∀ d, r ≤ d → d < r + L →
      vOpt σ ((par M 1 d).map (shk r ((n - 1) * L))) = vOpt τ (par (M.take (r + L)) 1 d) := by
    intro d hrd hdx
    rw [par_take M 1 d hdx]
    cases hpm : par M 1 d with
    | none => rfl
    | some m => exact hshL m d hrd hdx (Or.inl hpm) (par_lt M 1 d m hpm)
  intro i k hu
  change AbsUWAt (last (σ.v k)) (vOpt σ (par (TRIO.gexp M r L 0 0 n) 1 i))
  have hiN : i < (TRIO.gexp M r L 0 0 n).length := by have := upg_succ_lt hu; omega
  rcases Nat.lt_or_ge i r with hir | hir
  · rw [upg_pre0 hlen hL hp hn (by omega)] at hu
    rw [par1_pre0 hlen hL hp hn hir]
    by_cases hd : DepX M (r + L) false i
    · exact hR1 i k hir hd hu
    · have h12 := upg_e12 hu
      have h2 : entry M 2 i = 0 := by have := I.z2 i; omega
      obtain ⟨_, _, _, _, hcase⟩ := t0s_upg_facts hu
      have hkr : k ≤ r := by rcases hcase with h | ⟨_, h⟩ <;> omega
      have hvk : σ.v k = ρ.v k := by
        rcases Nat.lt_or_ge k r with hkr' | hkr'
        · exact hoffv k hkr' (fun hdk => hd (DepX.vupg h12.1 h2 hu hdk))
        · have := hmidv 0 0 (by omega) hL
          rwa [show r + (0 * L + 0) = k by omega, show r + 0 = k by omega] at this
      have hV : vOpt σ (par M 1 i) = vOpt ρ (par M 1 i) := by
        cases hpm : par M 1 i with
        | none => rfl
        | some m =>
          have hmi := par_lt M 1 i m hpm
          exact hoffv m (by omega) (fun hdm => hd (DepX.vpar h12.1 hpm hdm))
      rw [hvk, hV]
      exact I.auw i k hu
  · obtain ⟨k', q, hk', hq, rfl⟩ := copy_decomp hL hir (lt_of_lt_of_eq hiN hlN)
    rw [par1_copy0 hlen hL hp hn hk' hq]
    by_cases hqL : q + 1 < L
    · rw [upg_copy0 hlen hL hp hn hk' hqL] at hu
      cases hut : upg M (r + q) with
      | none => rw [hut] at hu; cases hu
      | some t =>
        rw [hut] at hu
        simp only [Option.map_some, Option.some.injEq] at hu
        subst hu
        obtain ⟨_, _, _, _, hcase⟩ := t0s_upg_facts hut
        by_cases hkn : k' + 1 < n
        · rcases hcase with rfl | ⟨_, htq⟩
          · rw [show shk r (k' * L) (r + q + 1) = r + (k' * L + (q + 1)) by unfold shk; rw [if_pos (by omega)]; omega,
              hmidv k' (q + 1) hkn hqL, show r + (q + 1) = r + q + 1 by omega, hvopt k' (r + q) hkn (by omega) (by omega)]
            exact I.auw (r + q) (r + q + 1) hut
          · rw [hsh k' t (r + q) hkn (by omega) (by omega) (Or.inr ⟨hut, htq⟩) htq,
              hvopt k' (r + q) hkn (by omega) (by omega)]
            exact I.auw (r + q) t hut
        · have hk'' : k' = n - 1 := by omega
          subst hk''
          have hutT : upg (M.take (r + L)) (r + q) = some t := by rw [upg_take M (by omega)]; exact hut
          rcases hcase with rfl | ⟨_, htq⟩
          · rw [show shk r ((n - 1) * L) (r + q + 1) = r + ((n - 1) * L + (q + 1)) by
                unfold shk; rw [if_pos (by omega)]; omega,
              hlastv (q + 1) hqL, ← (hag (r + (q + 1)) (by omega)).2, show r + (q + 1) = r + q + 1 by omega,
              hvoptL (r + q) (by omega) (by omega)]
            exact IT.auw (r + q) (r + q + 1) hutT
          · rw [hshL t (r + q) (by omega) (by omega) (Or.inr ⟨hut, htq⟩) htq, hvoptL (r + q) (by omega) (by omega)]
            exact IT.auw (r + q) t hutT
    · have hq' : q = L - 1 := by omega
      subst hq'
      by_cases hkn : k' + 1 < n
      · rw [upg_copy_last0 hlen hL hp hn I.r0p I.z2 hx2 hkn] at hu
        cases hut : upg M (r + (L - 1)) with
        | none => rw [hut] at hu; cases hu
        | some t =>
          rw [hut] at hu
          simp only [Option.map_some, Option.some.injEq] at hu
          subst hu
          have hte := upg_target_e2 hut
          obtain ⟨_, _, _, _, hcase⟩ := t0s_upg_facts hut
          have htx : t < r + (L - 1) := by
            rcases hcase with h | ⟨_, h⟩
            · exfalso; rw [h, show r + (L - 1) + 1 = r + L by omega, hx2] at hte; omega
            · exact h
          rw [hvopt k' (r + (L - 1)) hkn (by omega) (by omega)]
          by_cases htr : t = r
          · subst htr
            rw [if_pos rfl]
            by_cases hk2 : k' + 2 < n
            · have := hmidv (k' + 1) 0 (by omega) hL
              rw [Nat.add_zero, Nat.add_zero] at this
              rw [this]; exact I.auw _ _ hut
            · have hk3 : k' + 1 = n - 1 := by omega
              rw [hk3]
              have := hlastv 0 hL
              rw [Nat.add_zero, Nat.add_zero] at this
              rw [this]
              exact hR2 hut
          · rw [if_neg htr, hvM t (r + (L - 1)) (by omega) (by omega) (Or.inr ⟨hut, htx⟩) (by omega)]
            exact I.auw _ _ hut
      · have hk'' : k' = n - 1 := by omega
        subst hk''
        rw [upg_none_last0 hlen hL hp hn] at hu
        cases hu

/-- The residuals of the value fields after the column transfers. -/
structure T0RestC : Prop where
  vsD : T0VSResD2
  phi : T0FieldG PhiX0R
  tploR : T0TPLoRes
  auwR : T0AbsUWRes
  adnR : T0AbsDNRes
  tplon : T0FieldG TPLoN
  tplow : T0FieldG TPLoW
  adw : T0FieldG AbsDW

/-- **`hExp` for `t = 0`, the current residuals** (column transfers of `TPLo`・`AbsUW`・`AbsDN` done). -/
theorem hExp_t0_mainC2 (hU0 : OldUpgAbs)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hNG : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → NoGapP M ρ)
    (hIV : T0IVRes) (hII : T0IIRes) (hG : T0VSResG) (hS : T0ShapeR3) (hRest : T0RestC) (hC1 : T0RWResC PTP1)
    (hC1W : T0RWResC PTP1W) (hCT : T0RWResC PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN :=
  have f : ∀ F, T0Field F → T0FieldG F := fun _ h M ρ rk r L n σ rkN hctx _ => h M ρ rk r L n σ rkN hctx
  (hExp_t0_mainG hU0) hLast hNG hIV hII hG hS
    ⟨hRest.vsD, hRest.phi, f _ (t0_tplo hRest.tploR), f _ (t0_absUW hRest.auwR), hRest.tplon,
      f _ (t0_absDN hRest.adnR), hRest.tplow, hRest.adw⟩ hC1 hC1W hCT

end Ytosk
