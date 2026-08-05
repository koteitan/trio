/-
Lind.lean: 長さの強帰納法で「基づく列はすべて `GX`」を**単元核ひとつ**に還元する。

`gx_graft` は
  「文脈 `E` の peel が `GX`」＋「データ `w` が `GX`」 ⟹ `graft E w ∈ GX`
という無条件の合成則。基づく列 `y`（長さ ≥ 2）を、末尾側 `[1, |y|)` で行 0 の
深さが最小になる位置 `p` で切ると

  y = graft (y.take (p+1)) (shiftl0 (entry y 0 p) (y.drop p))

であり、文脈側の peel は `y.take p`（長さ `p < |y|`）、データ側は長さ
`|y| - p < |y|`（`p ≥ 1`）。よって長さの強帰納法が回り、**基底は基づく単元
`[(0,b,c)]` のみ**になる。
-/
import Gamma

namespace TRIO

open Wset
open Classical

/-! ## 小道具: `drop` の成分 -/

theorem entry_drop {y : TrioSeq} {p i j : ℕ} :
    entry (y.drop p) i j = entry y i (p + j) := by
  unfold entry
  rw [getD_drop]

/-- Columns of the suffix at a tail-minimal cut are at least as deep as the
cut. -/
theorem le_of_mem_drop {y : TrioSeq} {p : ℕ}
    (h : ∀ j, p ≤ j → j < y.length → entry y 0 p ≤ entry y 0 j) :
    ∀ x ∈ y.drop p, entry y 0 p ≤ x.1 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [List.length_drop] at hi
  have hlen : p + i < y.length := by omega
  have hgd : entry (y.drop p) 0 i = entry y 0 (p + i) := entry_drop
  have hval : entry (y.drop p) 0 i
      = ((y.drop p).getD i ((0, 0, 0) : ℕ × ℕ × ℕ)).1 := by
    unfold entry; simp
  have hget : (y.drop p).getD i ((0, 0, 0) : ℕ × ℕ × ℕ)
      = (y.drop p)[i]'(by rw [List.length_drop]; omega) := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [List.length_drop]; omega)]
    rfl
  rw [← hget, ← hval, hgd]
  exact h (p + i) (by omega) hlen

/-! ## 窓分解 -/

theorem dropLast_take_succ {y : TrioSeq} {p : ℕ} (hp : p < y.length) :
    (y.take (p + 1)).dropLast = y.take p := by
  have hlen : (y.take (p + 1)).length = p + 1 := by
    rw [List.length_take]; omega
  rw [List.dropLast_eq_take, hlen, List.take_take, Nat.add_sub_cancel]
  congr 1
  omega

/-- **The window decomposition**: cutting at a tail-minimal column presents `y`
as a graft of a strictly shorter datum into a strictly shorter context. -/
theorem graft_take_drop {y : TrioSeq} {p : ℕ} (hp : p < y.length)
    (hmin : ∀ j, p ≤ j → j < y.length → entry y 0 p ≤ entry y 0 j) :
    graft (y.take (p + 1)) (shiftl0 (entry y 0 p) (y.drop p)) = y := by
  have hlen : (y.take (p + 1)).length = p + 1 := by
    rw [List.length_take]; omega
  have hentry : entry (y.take (p + 1)) 0 ((y.take (p + 1)).length - 1)
      = entry y 0 p := by
    rw [hlen, Nat.add_sub_cancel]
    exact Wset.entry_take (by omega)
  rw [graft_eq_shift, hentry, dropLast_take_succ hp,
    shiftr01_shiftl0 (le_of_mem_drop hmin), List.take_append_drop]

/-! ## ★ 長さ帰納 -/

/-- **Every based sequence is in the machine's set, modulo the singleton
core.**  The only irreducible input is `[(0,b,c)] ∈ GX`. -/
theorem mem_GX_of_singletons (hs : ∀ b c : ℕ, [((0, b, c) : ℕ × ℕ × ℕ)] ∈ GX) :
    ∀ (n : ℕ) (y : TrioSeq), y.length < n → based y → y ∈ GX := by
  intro n
  induction n with
  | zero => intro y hy; omega
  | succ n ih =>
      intro y hy hby
      rcases Nat.lt_or_ge y.length 2 with hsmall | hbig
      · rcases y with _ | ⟨c0, tl⟩
        · exact nil_mem_GX
        · have htl : tl = [] := by
            rcases tl with _ | ⟨c1, tl'⟩
            · rfl
            · simp only [List.length_cons] at hsmall; omega
          subst htl
          have hc1 : c0.1 = 0 := by
            have hb := hby
            unfold based entry at hb
            simpa using hb
          have hc0 : c0 = ((0, c0.2.1, c0.2.2) : ℕ × ℕ × ℕ) :=
            Prod.ext hc1 rfl
          rw [hc0]
          exact hs _ _
      · obtain ⟨p, hpmem, hpmin⟩ :=
          Finset.exists_min_image (Finset.Ico 1 y.length) (fun j => entry y 0 j)
            ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
        rw [Finset.mem_Ico] at hpmem
        have hmin : ∀ j, p ≤ j → j < y.length → entry y 0 p ≤ entry y 0 j :=
          fun j hj1 hj2 => hpmin j (Finset.mem_Ico.mpr ⟨by omega, hj2⟩)
        rw [← graft_take_drop hpmem.2 hmin]
        refine gx_graft ?_ ?_ ?_ ?_ ?_
        · intro hc
          have hz : (y.take (p + 1)).length = 0 := by rw [hc]; rfl
          rw [List.length_take] at hz
          omega
        · show entry (y.take (p + 1)) 0 0 = 0
          rw [Wset.entry_take (by omega)]
          exact hby
        · rw [dropLast_take_succ hpmem.2]
          refine ih (y.take p) (by rw [List.length_take]; omega) ?_
          show entry (y.take p) 0 0 = 0
          rw [Wset.entry_take (by omega)]
          exact hby
        · refine ih _ ?_ ?_
          · rw [shiftl0_length, List.length_drop]; omega
          · show entry (shiftl0 (entry y 0 p) (y.drop p)) 0 0 = 0
            rw [entry0_shiftl0', entry_drop, Nat.add_zero, Nat.sub_self]
        · show entry (shiftl0 (entry y 0 p) (y.drop p)) 0 0 = 0
          rw [entry0_shiftl0', entry_drop, Nat.add_zero, Nat.sub_self]

/-- **The singleton core**: every based one-column block is in the machine's
set.  By `mem_GX_of_singletons` this single family carries the whole `GX`
side of the campaign. -/
def CoreSingleton : Prop :=
  ∀ b c : ℕ, [((0, b, c) : ℕ × ℕ × ℕ)] ∈ GX

theorem mem_GX_of_core (hs : CoreSingleton) {y : TrioSeq} (hby : based y) :
    y ∈ GX :=
  mem_GX_of_singletons hs (y.length + 1) y (by omega) hby

/-- **The plant core falls to the singleton core**: the planted peel of an
equipped context is a based sequence. -/
theorem corePlantCtx0_of_singleton (hs : CoreSingleton) : CorePlantCtx0 := by
  intro M _ _ v z _ _
  exact mem_GX_of_core hs (based_cons v z M.dropLast)

/-! ## 単元核の素の形: **キャップ補題**（`GX` が statement から消える）

単元をデータとして接ぎ木すると、文脈の末尾列の**添字だけ**が差し替わる:

```
graft M [(0,b,c)] = M.dropLast ++ [(entry M 0 (|M|-1), b, c)] =: cap M b c
```

`GX` の接頭辞義務 `i = 0` は文脈の装備そのもの（自明）なので、`CoreSingleton`
は `i = 1` の一本、すなわち「装備つき文脈の末尾添字を任意に差し替えても
`W` package」に等しい。⟹ 残核から `GX` が完全に消える。 -/

/-- The context with its last column's subscript replaced by `(b, c)`. -/
def cap (M : TrioSeq) (b c : ℕ) : TrioSeq :=
  M.dropLast ++ [((entry M 0 (M.length - 1), b, c) : ℕ × ℕ × ℕ)]

theorem graft_singleton_eq_cap (M : TrioSeq) (b c : ℕ) :
    graft M [((0, b, c) : ℕ × ℕ × ℕ)] = cap M b c := by
  rw [graft_eq_shift]
  unfold cap shiftr01
  simp

/-- **The cap core**: a pure `W`-level statement — no `GX`. -/
def CoreCap : Prop :=
  ∀ (M : TrioSeq), argOK M → 1 ≤ M.length → ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ b c a t : ℕ, 2 * (v + t) + z ≤ a →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: cap M b c) t ∈ W a

theorem coreSingleton_of_cap (h : CoreCap) : CoreSingleton := by
  intro b c _ M hMarg hM2 v z hz1 hctx i hi a t hva
  rcases Nat.lt_or_ge i 1 with hi0 | hi1
  · have : i = 0 := by omega
    subst this
    rw [List.take_zero, graft_nil, List.dropLast_eq_take]
    exact hctx (M.length - 1) (by omega) a t hva
  · have hi1' : i = 1 := by
      simp only [List.length_cons, List.length_nil] at hi
      omega
    subst hi1'
    rw [List.take_one]
    simpa [graft_singleton_eq_cap] using h M hMarg hM2 v z hz1 hctx b c a t hva

theorem cap_of_coreSingleton (h : CoreSingleton) : CoreCap := by
  intro M hMarg hM2 v z hz1 hctx b c a t hva
  have hres := h b c (by show entry [((0, b, c) : ℕ × ℕ × ℕ)] 0 0 = 0; rfl)
    M hMarg hM2 v z hz1 hctx 1 (by simp) a t hva
  rw [List.take_one] at hres
  simpa [graft_singleton_eq_cap] using hres

/-! ## ★ 両方の文脈核が単元核から出る（`InfEquip` は不要）

`CoreCtxSuffixLift` の結論も `CorePlantCtxLift` の結論も **`GX` に入る基づく列**
なので、`mem_GX_of_core` がそのまま効く。⚠ 旧経路が使っていた `InfEquip` は
**偽**（`Infcex.not_infEquip`）なので、この経路で置き換える必要がある。 -/

theorem corePlantCtxLift_of_core (hs : CoreSingleton) : CorePlantCtxLift := by
  intro M _ _ v z _ _ t
  refine mem_GX_of_core hs ?_
  show entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) t) 0 0 = 0
  rw [entry0_Lift1]
  exact based_cons v z M.dropLast

theorem coreCtxSuffixLift_of_core (hs : CoreSingleton) : CoreCtxSuffixLift := by
  intro M p _ _ hplt _ v z _ _ s
  refine mem_GX_of_core hs ?_
  show entry (Lift1 (shiftl0 (entry M 0 p) (seg M p (M.length - 1 - p))) s) 0 0
    = 0
  rw [entry0_Lift1, entry0_shiftl0',
    entry_seg (N := M) (a := p) (l := M.length - 1 - p) (i := 0) (j := 0)
      (by omega), Nat.add_zero, Nat.sub_self]

/-- **No regression**: the old two-core route still supplies the singleton core
(`singleton_mem_GXs`), so the two formulations are equivalent — the length
induction trades two `∀`-context statements for a one-column family. -/
theorem coreSingleton_of_cores (hsl : CoreCtxSuffixLift) (hp : CorePlantCtxLift) :
    CoreSingleton :=
  fun b c => (singleton_mem_GXs (coreBlocked_of_ctxSuffixLift hsl)
    (coreT1L_of_plantctx hp) (coreT2E_of_plantctx hp) b c).1

end TRIO
