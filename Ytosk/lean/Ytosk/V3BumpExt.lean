/-
**bump 項の単調性を 1 つの残り HBumpExt にまとめる（2026-10-17、lead）。**

`HBumpExt`: 標準形 K と接頭辞 K.take k で、i < k（行 1・2 が 0 でない）の bump 項は増える:
bumpW (K.take k) τ i ≤ bumpW K σ i。1 列の落としの場合は落とす補題の `bumpW_take_le` と同じ主張で、
接頭辞で閉じた集合では 1 列の場合から一般の k が出る。

- t = 0 の `T0BumpMono`（M.take x = M[n].take (r + L)、`gexp_take_x`）から `T0AbWRes`（`t0AbWRes_of_ext`）。
  これで残り T0PrefixInv（M[n] の接頭辞の Inv3V2、今の帰納法では使えない）が要らなくなる。
- t = 2 の `T2BumpMonoV2` も同じ形（`t2BumpMonoV2_of_ext`）。
-/
import Ytosk.V3T0AbW
import Ytosk.V3T2BelowR

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Residual: the bump term grows along prefixes of a standard matrix.** -/
def HBumpExt : Prop :=
  ∀ K σ, Std K → K ≠ SRO → Cons K σ → ∀ k τ, k ≤ K.length → Cons (K.take k) τ →
    ∀ i, i < k → entry K 1 i ≠ 0 → entry K 2 i ≠ 0 → bumpW (K.take k) τ i ≤ bumpW K σ i

/-- `HBumpExt` for a standard `N` whose prefix of length `k` is that of `M`. -/
theorem bumpMono_of_ext (hE : HBumpExt) {M N : Mat} (hN : Std N) (hNS : N ≠ SRO) {k : Nat}
    (hk : k ≤ N.length) (htake : N.take k = M.take k) {τ σ : Valn} (hτ : Cons (M.take k) τ)
    (hσ : Cons N σ) {i : Nat} (hi : i < k) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) :
    bumpW (M.take k) τ i ≤ bumpW N σ i := by
  have he : ∀ q, entry N q i = entry M q i := by
    intro q
    rw [← entry_take N (l := k) q hi, htake, entry_take M q hi]
  have hτ' : Cons (N.take k) τ := by rw [htake]; exact hτ
  have h := hE N σ hN hNS hσ k τ hk hτ' i hi (by rw [he 1]; exact h1) (by rw [he 2]; exact h2)
  rw [htake] at h
  exact h

/-- **`T0BumpMono` from `HBumpExt`.** -/
theorem t0BumpMono_of_ext (hE : HBumpExt) {M : Mat} (hM : Std M) {r L : Nat}
    (hlen : r + L + 1 = M.length) (hr : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    (he2 : entry M 2 (r + L) = 0) : T0BumpMono M r L := by
  intro τ hτ n hn σ hσ i hi h1 h2
  have hL : M.length - 1 = r + L := by omega
  have hs0 : TRIO.srow M (M.length - 1) = 0 := by
    unfold TRIO.srow; rw [← entry_eq, ← entry_eq, hL, he1, he2]; simp
  have he0 : entry M 0 r < entry M 0 (r + L) := ((par0_spec M).mp hr).2.1
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := by
    rintro ⟨h0, _, _⟩; rw [← entry_eq, hL] at h0; omega
  have hexp : expand M n = TRIO.gexp M r L 0 0 n := by
    rw [expand_eq_gexp_t0 M n (by omega) hzT (by rw [hs0, hL]; exact hr) hs0,
      show M.length - 1 - r = L by omega]
  have hN : Std (TRIO.gexp M r L 0 0 n) := hexp ▸ Std.exp n hM
  have hNS : TRIO.gexp M r L 0 0 n ≠ SRO := hexp ▸ expand_ne_SRO hM n
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
  exact bumpMono_of_ext hE hN hNS (by rw [hlN]; omega) (gexp_take_x hlen (by omega)) hτ hσ (by omega) h1 h2

/-- **`T0AbWRes` from `HBumpExt`** (and the drop side `BumpAbsC` of the step context). -/
theorem t0AbWRes_of_ext (hD : HDropV2) (hE : HBumpExt) : T0AbWRes := by
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
  exact t0AbsW_of hτ (absWN_take_t0 hDr.ab C.I.cons (by omega) he1 hτ)
    (t0BumpMono_of_ext hE C.std hlen hr he1 (hS.r12 _ he1))

/-- **`T2BumpMonoV2` from `HBumpExt`.** -/
theorem t2BumpMonoV2_of_ext (hE : HBumpExt) : T2BumpMonoV2 := by
  intro M ρ rk C hz h2 r L hlen hr τ hτ n hn σ hσ i hi h1 h2'
  have hL : M.length - 1 = r + L := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : expand M n = TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n := by
    have h := expand_eq_gexp M n (by omega) hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hN := hexp ▸ Std.exp n C.std
  have hNS := hexp ▸ expand_ne_SRO C.std n
  have hlN : (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n).length =
      r + n * L := TRIO.gexp_length hlen
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
  exact bumpMono_of_ext hE hN hNS (by rw [hlN]; omega) (gexp_take_x hlen (by omega)) hτ hσ hi h1 h2'

end Ytosk
