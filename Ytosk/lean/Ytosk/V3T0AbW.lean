/-
**t = 0 の弱い吸収 T0AbsW を、落とし側の AbsWN と bumpW の単調性に分ける（2026-10-17、t0）。**

AbsWN M N bnd ρ σ の前件「q は bumpW N σ i に吸収されない」は、bumpW N′ σ′ i ≤ bumpW N σ i なら N′ でも立つ
（`absWN_mono`）。t = 0 では N′ = M.take x（落とし）、N = M[n]（展開）。
- 落とし側: AbsWN M (M.take x) r ρ τ（drop の BumpAbsW の筋）。
- 展開側: i < r（行 1・2 が 0 でない列）で bumpW (M.take x) τ i ≤ bumpW M[n] σ i（`T0BumpMono`）。測定（tools/probe_abswn_t0.py の mono、
  t0ext の 2 万行列、n = 2, 3）で 154034 件例外 0。なお bumpW M ρ i ≤ bumpW M[n] σ i は偽（18470 件で
  M[n] の方が小さい。x が i ののりしろの子の子のとき）。
- T0BumpMono は M[n] の接頭辞を 1 列ずつ落とす連鎖で出る（`bumpW_chain`）。1 列の落としは drop の `bumpW_take_le`
  （`drop_all_H` の PO・PV がどれも ≤ を含む）。`t0BumpDrop_of`: HDropV2 と接頭辞 M[n].take k（k ≥ r + L）の
  Std・≠ SRO・Inv3V2 から。
- 落とし側の AbsWN は DropResH の `ab : BumpAbsC` から、t = 0 では v(x) = 0 なので前提が自明（`absWN_take_t0`）。
- まとめ `t0AbWRes_of : HDropV2 → T0PrefixInv → T0AbWRes`。残りは `T0PrefixInv`（M[n] の接頭辞の不変条件）。
-/
import Ytosk.V3T0Inv2S
import Ytosk.V3Congr
import Ytosk.V3Copy2
import Ytosk.V3DropPres
import Ytosk.V3DropH

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **AbsWN is monotone in the bump term of `N`.** -/
theorem absWN_mono {M N N' : Mat} {bnd : Nat} {ρ σ σ' : Valn} (h : AbsWN M N' bnd ρ σ')
    (hm : ∀ i, i < bnd → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → bumpW N' σ' i ≤ bumpW N σ i) :
    AbsWN M N bnd ρ σ := by
  intro i hi h1 h2 q hq hq2 hn hlt
  exact h i hi h1 h2 q hq hq2 (fun h' => hn (lt_of_lt_of_le h' (hm i hi h1 h2))) hlt

/-- **The monotonicity of the bump term** from `M.take x` to `M[n]` (`t = 0`, columns below `r`). -/
def T0BumpMono (M : Mat) (r L : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
    ∀ i, i < r → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → bumpW (M.take (r + L)) τ i ≤ bumpW (TRIO.gexp M r L 0 0 n) σ i

/-- **`T0AbsW` from the drop side and the monotonicity.** -/
theorem t0AbsW_of {M : Mat} {r L : Nat} {ρ τ : Valn} (hτ : Cons (M.take (r + L)) τ)
    (hD : AbsWN M (M.take (r + L)) r ρ τ) (hm : T0BumpMono M r L) : T0AbsW M r L ρ :=
  fun n hn σ hσ => absWN_mono hD (hm τ hτ n hn σ hσ)

/-! ## 接頭辞を 1 列ずつ落として単調性をつなぐ -/

/-- **One-column drop monotonicity of the bump term** along the prefixes of `N` longer than `k0`. -/
def BumpDropMono (N : Mat) (k0 : Nat) : Prop :=
  ∀ k, k0 < k → k ≤ N.length → ∀ τ τ', Cons (N.take k) τ → Cons (N.take (k - 1)) τ' →
    ∀ i, i < k0 → entry N 1 i ≠ 0 → entry N 2 i ≠ 0 → bumpW (N.take (k - 1)) τ' i ≤ bumpW (N.take k) τ i

/-- The prefixes of `N` from `k0` on are ranked. -/
def PrefixRk (N : Mat) (k0 : Nat) : Prop := ∀ k, k0 ≤ k → k ≤ N.length → ∃ rk, Rk (N.take k) rk

theorem bumpW_chain {N : Mat} {k0 : Nat} (hD : BumpDropMono N k0) (hR : PrefixRk N k0) :
    ∀ m k, k = k0 + m → k ≤ N.length → ∀ τ0 τ, Cons (N.take k0) τ0 → Cons (N.take k) τ →
      ∀ i, i < k0 → entry N 1 i ≠ 0 → entry N 2 i ≠ 0 → bumpW (N.take k0) τ0 i ≤ bumpW (N.take k) τ i
  | 0, k, hk, hkN, τ0, τ, h0, h, i, _, _, _ => by
    simp only [Nat.add_zero] at hk
    subst hk
    obtain ⟨rk, hrk⟩ := hR _ (le_refl _) hkN
    rw [bumpW_congr (agree_of_cons h0 h hrk) i]
  | m + 1, k, hk, hkN, τ0, τ, h0, h, i, hi, h1, h2 => by
    obtain ⟨rk', hrk'⟩ := hR (k - 1) (by omega) (by omega)
    have hC' := cons_of_rk hrk'
    exact le_trans (bumpW_chain hD hR m (k - 1) (by omega) (by omega) τ0 _ h0 hC' i hi h1 h2)
      (hD k (by omega) hkN τ _ h hC' i hi h1 h2)

/-- **Residual of the monotonicity**: every `M[n]` (`t = 0`) has the one-column drop monotonicity of the bump
term and ranked prefixes from `r + L` on. -/
def T0BumpDrop (M : Mat) (r L : Nat) : Prop :=
  ∀ n, 2 ≤ n → BumpDropMono (TRIO.gexp M r L 0 0 n) (r + L) ∧ PrefixRk (TRIO.gexp M r L 0 0 n) (r + L)

/-- **`T0BumpMono` from the one-column drops** along the prefixes of `M[n]`. -/
theorem t0BumpMono_of {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hD : T0BumpDrop M r L) :
    T0BumpMono M r L := by
  intro τ hτ n hn σ hσ i hi h1 h2
  obtain ⟨hDm, hR⟩ := hD n hn
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
  have htake : (TRIO.gexp M r L 0 0 n).take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have he : ∀ q, entry (TRIO.gexp M r L 0 0 n) q i = entry M q i := by
    intro q
    rw [← entry_take (TRIO.gexp M r L 0 0 n) (l := r + L) q (show i < r + L by omega), htake,
      entry_take M q (show i < r + L by omega)]
  have hfull : (TRIO.gexp M r L 0 0 n).take (TRIO.gexp M r L 0 0 n).length = TRIO.gexp M r L 0 0 n :=
    List.take_length
  have hσ' : Cons ((TRIO.gexp M r L 0 0 n).take (TRIO.gexp M r L 0 0 n).length) σ := by rw [hfull]; exact hσ
  have hτ' : Cons ((TRIO.gexp M r L 0 0 n).take (r + L)) τ := by rw [htake]; exact hτ
  have key := bumpW_chain hDm hR (n * L - L) (TRIO.gexp M r L 0 0 n).length (by rw [hlN]; omega) (le_refl _)
    τ σ hτ' hσ' i (by omega) (by rw [he 1]; exact h1) (by rw [he 2]; exact h2)
  rw [htake, hfull] at key
  exact key

/-- **`BumpDropMono` from drop's one-column lemma** (`bumpW_take_le`): at every prefix `N.take k` (`k0 < k`), the
structural invariants, `Good3`, a rank of `N.take (k − 1)` and the drop relation `PO ∧ PV` (`drop_all_H`). -/
theorem bumpDropMono_of {N : Mat} {k0 : Nat}
    (h : ∀ k, k0 < k → k ≤ N.length → ∀ τ τ', Cons (N.take k) τ → Cons (N.take (k - 1)) τ' →
      R0P (N.take k) ∧ Z2 (N.take k) ∧ SibDec (N.take k) ∧ Z1C (N.take k) ∧ UAT (N.take k) ∧ UAB (N.take k) ∧
      Good3 (N.take k) τ ∧ (∃ rk, Rk (N.take (k - 1)) rk) ∧
      ∀ i, i < k - 1 → PO τ τ' i ∧ PV (N.take k) τ τ' i) : BumpDropMono N k0 := by
  intro k hk hkN τ τ' hC hC' i hi _ _
  obtain ⟨hR0, hZ2, hSD, hZ1, hUAT, hUAB, hG, ⟨rk, hRk⟩, hdrop⟩ := h k hk hkN τ τ' hC hC'
  have htt : (N.take k).take (k - 1) = N.take (k - 1) := by
    rw [List.take_take]; congr 1; omega
  have hx : k - 1 + 1 = (N.take k).length := by rw [List.length_take]; omega
  rw [← htt] at hC' hRk ⊢
  exact bumpW_take_le hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk hdrop (by omega)

/-- **One drop of a standard prefix with `Inv3V2`**: `bumpW` does not increase (drop's `HDropV2`, `drop_all_H`,
`bumpW_take_le`). -/
theorem bumpW_drop_std (hD : HDropV2) {K : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hStd : Std K) (hne : K ≠ SRO)
    (hK : 1 ≤ K.length) (I : Inv3V2 K ρ rk) {τ τ' : Valn} (hτ : Cons K τ) (hτ' : Cons (K.take (K.length - 1)) τ')
    {i : Nat} (hi : i < K.length - 1) : bumpW (K.take (K.length - 1)) τ' i ≤ bumpW K τ i := by
  have hS := sInv_std hStd hne
  have hx : K.length - 1 + 1 = K.length := by omega
  have hKne : K ≠ [] := fun h => by rw [h] at hK; simp at hK
  have hDr := hD K ρ rk hStd hne hKne I
  have hVI : ValInv K ρ := ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩
  have hcnt := counted_take_last hK hS.r0p hS.z2 hS.sibDec hS.z1c hS.uat
  have hRk1 : Rk (K.take (K.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := drop_all_H hx hS.r0p hS.z2 hS.sibDec hS.z1c hS.uat hS.uab I.cons hVI hDr hC1 hRk1
  have h := bumpW_take_le hx hS.r0p hS.z2 hS.sibDec hS.z1c hS.uat hS.uab I.cons I.good hC1 hRk1 hdrop hi
  rw [bumpW_congr (agree_of_cons hτ' hC1 hRk1) i, bumpW_congr (agree_of_cons hτ I.cons I.rank) i]
  exact h

/-- **`T0BumpDrop` from `HDropV2`** and the invariants of the prefixes `M[n].take k` (`r + L ≤ k`). -/
theorem t0BumpDrop_of (hD : HDropV2) {M : Mat} {r L : Nat}
    (hP : ∀ n, 2 ≤ n → ∀ k, r + L ≤ k → k ≤ (TRIO.gexp M r L 0 0 n).length →
      Std ((TRIO.gexp M r L 0 0 n).take k) ∧ (TRIO.gexp M r L 0 0 n).take k ≠ SRO ∧
      ∃ ρk rkk, Inv3V2 ((TRIO.gexp M r L 0 0 n).take k) ρk rkk) : T0BumpDrop M r L := by
  intro n hn
  refine ⟨?_, ?_⟩
  · intro k hk hkN τ τ' hC hC' i hi _ _
    obtain ⟨hStd, hne, ρk, rkk, I⟩ := hP n hn k (by omega) hkN
    have hlen : ((TRIO.gexp M r L 0 0 n).take k).length = k := by rw [List.length_take]; omega
    have htt : ((TRIO.gexp M r L 0 0 n).take k).take (((TRIO.gexp M r L 0 0 n).take k).length - 1) =
        (TRIO.gexp M r L 0 0 n).take (k - 1) := by
      rw [hlen, List.take_take]; congr 1; omega
    have h := bumpW_drop_std hD hStd hne (by rw [hlen]; omega) I hC (by rw [htt]; exact hC')
      (i := i) (by rw [hlen]; omega)
    rw [htt] at h
    exact h
  · intro k hk hkN
    obtain ⟨_, _, ρk, rkk, I⟩ := hP n hn k hk hkN
    exact ⟨rkk, I.rank⟩

/-- **`T0AbsW` from the drop side, `HDropV2` and the prefix invariants of `M[n]`.** -/
theorem t0AbsW_of_drop (hD : HDropV2) {M : Mat} {r L : Nat} {ρ τ : Valn} (hlen : r + L + 1 = M.length)
    (hτ : Cons (M.take (r + L)) τ) (hA : AbsWN M (M.take (r + L)) r ρ τ)
    (hP : ∀ n, 2 ≤ n → ∀ k, r + L ≤ k → k ≤ (TRIO.gexp M r L 0 0 n).length →
      Std ((TRIO.gexp M r L 0 0 n).take k) ∧ (TRIO.gexp M r L 0 0 n).take k ≠ SRO ∧
      ∃ ρk rkk, Inv3V2 ((TRIO.gexp M r L 0 0 n).take k) ρk rkk) : T0AbsW M r L ρ :=
  t0AbsW_of hτ hA (t0BumpMono_of hlen (t0BumpDrop_of hD hP))

/-- **The drop-side AbsWN at `t = 0`** from `BumpAbsC` (in `DropResH`): `v(x) = 0` since row 1 of `x` is `0`. -/
theorem absWN_take_t0 {M : Mat} {x bnd : Nat} {ρ τ : Valn} (hAbsC : BumpAbsC M x ρ) (hC : Cons M ρ)
    (hx : x < M.length) (he1 : entry M 1 x = 0) (hτ : Cons (M.take x) τ) : AbsWN M (M.take x) bnd ρ τ := by
  have hvx : ρ.v x = z := by rw [(hC x hx).2]; unfold vRhs; rw [if_pos he1]
  intro i _ h1 h2 q hq _ hn hlt
  exact hAbsC τ hτ i h1 h2 (fun _ _ _ _ => hvx) (Or.inr (Or.inr hvx)) q hq hn hlt

/-- **Residual: the invariants of the prefixes of `M[n]`** (`t = 0`) from `M.take x` on. -/
def T0PrefixInv : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → ∀ r L, r + L + 1 = M.length → par M 0 (r + L) = some r →
    entry M 1 (r + L) = 0 → ∀ n, 2 ≤ n → ∀ k, r + L ≤ k → k ≤ (TRIO.gexp M r L 0 0 n).length →
      Std ((TRIO.gexp M r L 0 0 n).take k) ∧ (TRIO.gexp M r L 0 0 n).take k ≠ SRO ∧
      ∃ ρk rkk, Inv3V2 ((TRIO.gexp M r L 0 0 n).take k) ρk rkk

/-- **`T0AbWRes` from drop's `HDropV2` and the prefix invariants of `M[n]`.** -/
theorem t0AbWRes_of (hD : HDropV2) (hP : T0PrefixInv) : T0AbWRes := by
  intro M ρ rk C r L hlen hr he1
  have hK : 1 ≤ M.length := by omega
  have hKne : M ≠ [] := fun h => by rw [h] at hK; simp at hK
  have hDr := hD M ρ rk C.std C.ne hKne C.I
  have hxl : M.length - 1 = r + L := by omega
  rw [hxl] at hDr
  have hS := C.S
  have hcnt := counted_take_last hK hS.r0p hS.z2 hS.sibDec hS.z1c hS.uat
  rw [hxl] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) C.I.rank hcnt
  have hτ := cons_of_rk hRk1
  exact t0AbsW_of_drop hD hlen hτ (absWN_take_t0 hDr.ab C.I.cons (by omega) he1 hτ)
    (hP M ρ rk C r L hlen hr he1)

end Ytosk
