/-
**3 行・t = 1: A 群の値の欄（AbsD・AbsUW・AbsDN）を展開の鎖で運ぶ。**

N = M[n]、P = M[n − 1]、σ = 貼り合わせの評価。実測（C′ の t = 1 の行列 2 万個 × n = 2, 3）:
- 写しの列（x 以後）: 使う値はすべて P の対応する値と同じ。P_1・上げが r 以前に落ちる列 g は D の外（`hnd_t1`）で、
  g の v は M・P・N で同じ。これを運ぶ欄が `AgrT1`。
- x より前で D の外: 使う値は M と同じ。
- x より前で D の v の列（`dv_shape`）: 変わるのは段の項 W（のりしろの枠）か上げの先の v だけで、v(P_1 i) は同じ。
  新しい W は fsD(W, ζ)（`bumpW_D`）。吸収は groupA の `absorb_fsD_W` と種の条件 `SeedCond` から。
-/
import Ytosk.V3ExpT1
import Ytosk.V3BaseDrop

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Agreement of the low reads**: the `v`'s read through `P_1` or an upgrade from the columns `r + a`, at
columns at or before `r`, are those of `M`. -/
def AgrT1 (M : Mat) (r : Nat) (ρ : Valn) (N : Mat) (σ : Valn) : Prop :=
  ∀ g, g ≤ r → ∀ a, r + a < N.length →
    (par N 1 (r + a) = some g ∨ upg N (r + a) = some g) → σ.v g = ρ.v g

/-- The last summand of `add V W` for a single `W`. -/
theorem last_add_W {V W : T} (hW : ∃ s y, W = psi s y z) : last (add V W) = W := by
  obtain ⟨s, y, rfl⟩ := hW; exact last_add_single V

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
include hlen hL hA hd0e hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2

/-- **`AgrT1` is carried**: the reads of `M[n]` at or before `r` are off `D` (`hnd_t1` at `n + 1`). -/
theorem expStep_agr {ρ : Valn} : ExpStepT1 (AgrT1 M r ρ) M r L d0 ρ := by
  intro n hn ρP Z _ _ _ _ _ _ _ _ _ _ g hg a ha h
  have hlN := len_N (d0 := d0) hlen hn
  have hnL : (n + 1 - 1) * L = (n - 1) * L + L := by
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, Nat.succ_mul]
  have hnd := hnd_t1 hlen hL hA hd0e hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 (n + 1) (by omega) g hg a
    (by rw [hnL]; omega) (by rw [show n + 1 - 1 = n by omega]; exact h)
  exact glueZ_v_lt ρ (shiftV ρP L) Z (by omega) hnd

/-- **`AgrT1` at the base `M.take x`** (the drop valuation). -/
theorem agr_base {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hRk : Rk M rk) : AgrT1 M r ρ (M.take (r + L)) (drop1 M (r + L) rk) := by
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) hRk hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  intro g hg a ha h
  rw [List.length_take] at ha
  exact (base_v_read hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hg (by omega) h).symm

/-- The low reads of the copies agree between the glued valuation of `M[n]` and the valuation of `P`. -/
theorem agree_copy {n : Nat} (hn : 2 ≤ n) {ρ ρP : Valn} {Z : Nat → T}
    (hAg : AgrT1 M r ρ (TRIO.gexp M r L d0 0 (n - 1)) ρP) :
    ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueZ M (r + L) ρ (shiftV ρP L) Z).v g = ρP.v g := by
  intro g hg a ha h
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hnd := hnd_t1 hlen hL hA hd0e hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 n hn g hg a ha h
  rw [glueZ_v_lt ρ (shiftV ρP L) Z (by omega) hnd, hAg g hg a (by omega) h]

/-- **`v(P_1)` of a copy column** is that of the corresponding column of `P`. -/
theorem vOpt_par_copy {n : Nat} (hn : 2 ≤ n) {ρ ρP : Valn} {Z : Nat → T}
    (hAg : AgrT1 M r ρ (TRIO.gexp M r L d0 0 (n - 1)) ρP) {a : Nat} (ha : a < (n - 1) * L) :
    vOpt (glueZ M (r + L) ρ (shiftV ρP L) Z) (par (TRIO.gexp M r L d0 0 n) 1 (r + L + a)) =
      vOpt ρP (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a)) := by
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hagree := agree_copy hlen hL hA hd0e hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hn (Z := Z) hAg
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hshv : ∀ t, r ≤ t → (glueZ M (r + L) ρ (shiftV ρP L) Z).v (t + L) = ρP.v t := by
    intro t ht
    rw [glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.v (t + L - L) = ρP.v t
    rw [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0
    rw [show r + L + 0 = r + L by omega, show r + 0 = r by omega,
      par1_root hlen hL hA hd0e hn hpath, ← par_gexp_pre (m := n - 1) hlen (by omega) 1 (by omega)]
    cases ht : par (TRIO.gexp M r L d0 0 (n - 1)) 1 r with
    | none => rfl
    | some t =>
      have htr := par_lt _ 1 r t ht
      exact hagree t (by omega) 0 (by omega) (Or.inl (by simpa using ht))
  · rw [par1_copy hlen hL hA hd0e hn hpath h0 ha]
    cases ht : par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) with
    | none => rfl
    | some t =>
      simp only [Option.map_some, vOpt]
      split
      · rename_i htr; exact hshv t htr
      · rename_i htr; exact hagree t (by omega) a ha (Or.inl ht)

/-- **The bump term of a copy column** is that of the corresponding column of `P`. -/
theorem bumpW_copy {n : Nat} (hn : 2 ≤ n) {ρ ρP : Valn} {Z : Nat → T} {a : Nat} (ha : a < (n - 1) * L) :
    bumpW (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) (r + L + a) =
      bumpW (TRIO.gexp M r L d0 0 (n - 1)) ρP (r + a) := by
  unfold bumpW
  rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha, List.map_map]
  congr 3
  apply List.map_congr_left
  intro d hd
  exact bumpTerm_copy hlen hL hA hd0e hn ha hd


/-- **The new bump term at a `D` bump column below `x`** is `fsD(W, Z i)`, and `v(P_1 i)` does not change. -/
theorem bumpW_D {n : Nat} (hn : 2 ≤ n) {ρ ρP : Valn} {Z : Nat → T} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hCN : Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z))
    (hGN : Good3 (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z))
    {i : Nat} (hi : i < r + L) (hv : DepX M (r + L) false i) (h2 : entry M 2 i ≠ 0)
    {μ br vr : T} (hH : HoleT μ br vr (ρ.v i)) (hZs : ∃ s y, Z i = psi s y z) :
    bumpW (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) i = fsD (bumpW M ρ i) (Z i) ∧
      vOpt (glueZ M (r + L) ρ (shiftV ρP L) Z) (par (TRIO.gexp M r L d0 0 n) 1 i) = vOpt ρ (par M 1 i) ∧
      HoleT μ br vr (bumpW M ρ i) ∧ isOT (bumpW M ρ i) = true := by
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hlN := len_N (d0 := d0) hlen hn
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
    (hxnb_t1 hlen hL hA hd0e hZ2 hZ1 h1 n hn)
    (hiu_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn) i hi
  obtain ⟨he1, hpd, _⟩ := dv_shape hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hv
  have hiM : i < M.length := by omega
  have hbw : bumpW (TRIO.gexp M r L d0 0 n) σ i = bumpW M σ i := by
    unfold bumpW; rw [hSA.ch]
    congr 3
    exact List.map_congr_left (fun c hc => hSA.bt c hc σ)
  have hV : vOpt σ (par (TRIO.gexp M r L d0 0 n) 1 i) = vOpt ρ (par M 1 i) := by
    rw [hSA.par1, hσ]; exact vOpt_glueZ hi hpd
  have hVot : isOT (vOpt ρ (par M 1 i)) = true := vOpt_ot hG hiM
  -- the two equations
  have hY : ∀ τ : Valn, (∀ k, k < M.length → isOT (τ.o k) = true) →
      isOT (sumN (one :: (children M i).map (bumpTerm M τ i))) = true := by
    intro τ hτ
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm_of hτ i j
  have hρo : ∀ k, k < M.length → isOT (ρ.o k) = true := fun k hk => hG.ot_o k hk
  have hnL := Nat.mul_pos (show 0 < n - 1 by omega) hL
  have hσo : ∀ k, k < M.length → isOT (σ.o k) = true := fun k hk => hGN.ot_o k (by omega)
  obtain ⟨_, s, y, hW⟩ := single_omega (hY ρ hρo)
  obtain ⟨_, s', y', hW'⟩ := single_omega (hY σ hσo)
  have hW0 : bumpW M ρ i = psi s y z := hW
  have hW0' : bumpW M σ i = psi s' y' z := hW'
  have hvM : ρ.v i = add (vOpt ρ (par M 1 i)) (bumpW M ρ i) := by
    have := (hC i hiM).2
    unfold vRhs at this
    rw [if_neg he1, if_neg h2, sf_ot (isOT_add hVot (isOT_omega (hY ρ hρo)))] at this
    exact this
  have hvN : σ.v i = add (vOpt ρ (par M 1 i)) (bumpW M σ i) := by
    have := (hCN i (by omega)).2
    rw [vRhs_same hSA σ] at this
    unfold vRhs at this
    rw [if_neg he1, if_neg h2, hσ, vOpt_glueZ hi hpd, ← hσ,
      sf_ot (isOT_add hVot (isOT_omega (hY σ hσo)))] at this
    exact this
  have hWlast : last (ρ.v i) = bumpW M ρ i := by rw [hvM]; exact last_add_W (W := bumpW M ρ i) ⟨s, y, hW0⟩
  have hHW : HoleT μ br vr (bumpW M ρ i) := by rw [← hWlast]; exact holeT_last hH
  obtain ⟨a, b, hF⟩ := fsD_single_of_holeT hHW ⟨s, y, hW0⟩ hZs
  have hl1 : last (σ.v i) = bumpW M σ i := by rw [hvN]; exact last_add_W (W := bumpW M σ i) ⟨s', y', hW0'⟩
  have hl2 : last (σ.v i) = fsD (bumpW M ρ i) (Z i) := by
    rw [hσ, glueZ_v_dep ρ (shiftV ρP L) Z hi hv, fsD_init_last (holeT_ne_z hH), hWlast,
      last_app' _ (by rw [hF]; simp), hF]
    rfl
  exact ⟨by rw [hbw, ← hl1, hl2], hV, hHW, isOT_omega (hY ρ hρo)⟩

/-- **Off `D`, the bump term and `v(P_1 i)` do not change** (below `x`). -/
theorem bumpW_off {n : Nat} (hn : 2 ≤ n) {ρ ρP : Valn} {Z : Nat → T}
    {i : Nat} (hi : i < r + L) (hv : ¬ DepX M (r + L) false i) (he1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) :
    bumpW (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) i = bumpW M ρ i ∧
      vOpt (glueZ M (r + L) ρ (shiftV ρP L) Z) (par (TRIO.gexp M r L d0 0 n) 1 i) = vOpt ρ (par M 1 i) := by
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
    (hxnb_t1 hlen hL hA hd0e hZ2 hZ1 h1 n hn)
    (hiu_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn) i hi
  refine ⟨?_, ?_⟩
  · unfold bumpW; rw [hSA.ch]
    congr 3
    apply List.map_congr_left
    intro c hc
    rw [hSA.bt c hc σ]
    unfold bumpTerm
    split
    · rename_i hcb
      congr 2
      apply List.map_congr_left
      intro k hk
      have hkM := (mem_children hk).2
      have hnd : ¬ DepX M (r + L) true k := fun hd => hv (DepX.vbump he1 h2 hc hcb hk hd)
      have hkx : k < r + L := by
        rcases Nat.lt_or_ge k (r + L) with h | h
        · exact h
        · exact absurd (show k = r + L by omega ▸ DepX.leaf) hnd
      rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hkx hnd]
    · rfl
  · rw [hSA.par1]
    cases hp : par M 1 i with
    | none => rfl
    | some m =>
      have hm : m < i := par_lt M 1 i m hp
      exact glueZ_v_lt ρ (shiftV ρP L) Z (by omega) (fun hd => hv (DepX.vpar he1 hp hd))

end

/-- The chain terms are single when the seed is. -/
theorem gamS_single {μ b seed : T} (hs : ∃ a X, seed = psi a X z) : ∀ k, ∃ s y, gamS μ b seed k = psi s y z
  | 0 => hs
  | _ + 1 => ⟨μ, _, rfl⟩

/-- **Residual of the AbsD carry** (`t = 1`): at the bump columns of `D` below `x`, the index is not a
successor and the seed condition holds for the subterms of `v(P_1 i)` (C′ の 2 万行列 × n = 2, 3 で
P_1 の 6680 件、例外 0). -/
def AbsDRes (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    ∀ i, i < r + L → DepX M (r + L) false i → entry M 2 i ≠ 0 →
    isSucc (Z i) = false ∧
      SeedCond (vOpt ρ (par M 1 i)) (Z i) (etaOm (holeLev (bumpW M ρ i))) (etaOm (holeLev (Z i)))

/-- **AbsD is carried** (`t = 1`), together with `AgrT1`. Residual `AbsDRes`. -/
theorem expStep_absD {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hRes : AbsDRes M r L d0 ρ) :
    ExpStepT1 (fun N σ => AgrT1 M r ρ N σ ∧ AbsD N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  intro n hn ρP Z hCP hGP hQP hCN hGN hoto hotv hle hlex hH
  refine ⟨expStep_agr hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 n hn ρP Z hCP hGP hQP.1 hCN hGN
    hoto hotv hle hlex hH, ?_⟩
  have hR := hRes n hn ρP Z hH
  obtain ⟨μ, br, vr, seed, k0, hHD, hZk, _, _, _, _⟩ := hH
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hpath := hpath_of_par1 h1 hA (by omega)
  intro i hi he1 he2 hO q hq hlt
  rcases Nat.lt_or_ge i (r + L) with hi' | hi'
  · have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
      (hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn)
      (hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn) i hi'
    rw [hSA.e1] at he1; rw [hSA.e2] at he2
    have hiM : i < M.length := by omega
    by_cases hv : DepX M (r + L) false i
    · have hHv := hHD.hole false i hv hi'
      simp only [valB, cond_false] at hHv
      obtain ⟨k, _, hZe⟩ := hZk i
      have hZs : ∃ s y, Z i = psi s y z := by rw [hZe]; exact gamS_single hHD.seedS k
      obtain ⟨hW, hV, hHW, hWot⟩ := bumpW_D hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 hn
        I.cons I.good hCN hGN hi' hv he2 hHv hZs
      rw [← hσ] at hW hV
      rw [hV] at hq
      rw [hW] at hlt hO ⊢
      obtain ⟨hζs, hSC⟩ := hR i hi' hv he2
      have hOW := ohole_of_holeT hHW
      have hζz : Z i ≠ z := by obtain ⟨s, y, h⟩ := hZs; rw [h]; simp
      have hlt' : fsD (bumpW M ρ i) (Z i) < bumpW M ρ i := by
        rw [hZe]; exact (hok_of_holeT hHD.rot hHD.cb hHD.hμ hHD.S hWot hHW k).2
      rw [holeLev_fsD hOW hζz hζs]
      exact absorb_fsD_W hOW hζz hζs (I.ad i hiM he1 he2 hOW) hlt' hSC q hq hlt
    · obtain ⟨hW, hV⟩ := bumpW_off hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 hn
        (ρ := ρ) (ρP := ρP) (Z := Z) hi' hv he1 he2
      rw [← hσ] at hW hV
      rw [hV] at hq
      rw [hW] at hlt hO ⊢
      exact I.ad i hiM he1 he2 hO q hq hlt
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    rw [e1_gexp_shift hlen hL hn ha] at he1
    rw [e2_copy (d0 := d0) hlen hL hn ha] at he2
    have hW := bumpW_copy hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 hn
      (ρ := ρ) (ρP := ρP) (Z := Z) ha
    have hV := vOpt_par_copy hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 hn (Z := Z) hQP.1 ha
    rw [← hσ] at hW hV
    rw [hV] at hq
    rw [hW] at hlt hO ⊢
    exact hQP.2 (r + a) (by omega) he1 he2 hO q hq hlt

/-- `last (fsD t ζ) = fsD (last t) ζ` when the latter is single. -/
theorem last_fsD_single {t ζ a b : T} (ht : t ≠ z) (h : fsD (last t) ζ = psi a b z) :
    last (fsD t ζ) = fsD (last t) ζ := by
  rw [fsD_init_last ht, last_app' _ (by rw [h]; simp), h]; rfl

/-- **Residual of the AbsUW carry** (`t = 1`): at an upgrade `i → k` with `k` a `v` call of `D` below `x`,
the index is not a successor, and the seed condition at `η = 1` holds for the subterms of `v(P_1 i)` or
the field holds at the new value (C′ の 2 万行列 × n = 2, 3 で 1026 件、種の条件は退化した種の 1 件を除き成立). -/
def AbsUWRes (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    ∀ i k, i < r + L → upg M i = some k → DepX M (r + L) false k →
    isSucc (Z k) = false ∧
      (SeedCond (vOpt ρ (par M 1 i)) (Z k) (etaOm (holeLev (last (ρ.v k)))) one ∨
        ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < fsD (last (ρ.v k)) (Z k) →
          q < fsD (fsD (last (ρ.v k)) (Z k)) one)

/-- **AbsUW is carried** (`t = 1`), with `AgrT1` from `P`. Residual `AbsUWRes`. -/
theorem expStep_absUW {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hRes : AbsUWRes M r L d0 ρ) :
    ExpStepT1 (fun N σ => AgrT1 M r ρ N σ ∧ AbsUW N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q0, hq0⟩ := par0_of_anc hA (by omega)
  intro n hn ρP Z hCP hGP hQP hCN hGN hoto hotv hle hlex hH
  refine ⟨expStep_agr hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 n hn ρP Z hCP hGP hQP.1 hCN hGN
    hoto hotv hle hlex hH, ?_⟩
  have hR := hRes n hn ρP Z hH
  obtain ⟨μ, br, vr, seed, k0, hHD, hZk, _, _, _, _⟩ := hH
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hpath := hpath_of_par1 h1 hA (by omega)
  intro i k hu hO hcof q hq hlt
  have hiN : i < (TRIO.gexp M r L d0 0 n).length := by have := upg_succ_lt hu; omega
  rcases Nat.lt_or_ge i (r + L) with hi' | hi'
  · have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
      (hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn)
      (hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn) i hi'
    rw [hSA.upg] at hu
    have hkM : k < M.length := upg_lt (by omega) hu
    have hkx : k < r + L := by
      rcases Nat.lt_or_ge k (r + L) with h | h
      · exact h
      · exact absurd (by rw [show k = r + L by omega]; exact hx2) (fun h' => upg_ne_e2z hu h')
    obtain ⟨he1, he2'⟩ := upg_e12 hu
    have he2 : entry M 2 i = 0 := by have := I.z2 i; omega
    have hV : vOpt σ (par (TRIO.gexp M r L d0 0 n) 1 i) = vOpt ρ (par M 1 i) := by
      rw [hSA.par1]
      cases hp : par M 1 i with
      | none => rfl
      | some m =>
        have hm : m < i := par_lt M 1 i m hp
        have hmD : ¬ DepX M (r + L) false m := by
          intro hd
          have hiv : DepX M (r + L) false i := DepX.vpar he1 hp hd
          exact (dv_shape hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq0 hi' hiv).2.1 m hp hd
        exact glueZ_v_lt ρ (shiftV ρP L) Z (by omega) hmD
    rw [hV] at hq
    by_cases hkv : DepX M (r + L) false k
    · have hHv := hHD.hole false k hkv hkx
      simp only [valB, cond_false] at hHv
      have hHl := holeT_last hHv
      obtain ⟨kk, _, hZe⟩ := hZk k
      have hZs : ∃ s y, Z k = psi s y z := by rw [hZe]; exact gamS_single hHD.seedS kk
      obtain ⟨a, b, hF⟩ := fsD_single_of_holeT hHl (last_single' (holeT_ne_z hHv)) hZs
      have hlv : last (σ.v k) = fsD (last (ρ.v k)) (Z k) := by
        rw [hσ, glueZ_v_dep ρ (shiftV ρP L) Z hkx hkv]
        exact last_fsD_single (holeT_ne_z hHv) hF
      rw [hlv] at hlt ⊢
      obtain ⟨hζs, hSC⟩ := hR i k hi' hu hkv
      rcases hSC with hSC | hFld
      · have hOW := ohole_of_holeT hHl
        have hζz : Z k ≠ z := by obtain ⟨s, y, h⟩ := hZs; rw [h]; simp
        have hlt' : fsD (last (ρ.v k)) (Z k) < last (ρ.v k) := by
          rw [hZe]; exact (hok_of_holeT hHD.rot hHD.cb hHD.hμ hHD.S (isOT_last (I.good.ot_v k hkM)) hHl kk).2
        exact absorb_fsD_W hOW hζz hζs (I.au i k hu hOW) hlt' hSC q hq hlt
      · exact hFld q hq hlt
    · have hiv : ¬ DepX M (r + L) false i := by
        intro hd
        rcases (dv_shape hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq0 hi' hd).2.2 with
          ⟨_, hu', _, hd'⟩ | ⟨h2', _⟩
        · rw [hu] at hu'; cases hu'; exact hkv hd'
        · exact h2' he2
      have hvk : σ.v k = ρ.v k := glueZ_v_lt ρ (shiftV ρP L) Z hkx hkv
      rw [hvk] at hO hcof hlt ⊢
      exact I.auw i k hu hO hcof q hq hlt
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    have hV := vOpt_par_copy hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 hn (Z := Z) hQP.1 ha
    rw [← hσ] at hV
    rw [hV] at hq
    -- the upgrade of a copy column
    have hup : ∃ t, upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some t ∧ σ.v k = ρP.v t := by
      have hshv : ∀ t, r ≤ t → σ.v (t + L) = ρP.v t := by
        intro t ht
        rw [hσ, glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
        show ρP.v (t + L - L) = ρP.v t
        rw [Nat.add_sub_cancel]
      have hagree := agree_copy hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 hn (Z := Z) hQP.1
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0
        rw [show r + L + 0 = r + L by omega, upg_root hlen hL hA hd0e hn hpath (I.z2 r)] at hu
        refine ⟨k, by simpa using hu, ?_⟩
        have hkr := upgP_root_lt hlen hL hA hd0e hn hu
        exact hagree k (by omega) 0 (by omega) (Or.inr (by simpa using hu))
      · rw [upg_copy hlen hL hA hd0e hn hpath h0 ha] at hu
        cases ht : upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) with
        | none => rw [ht] at hu; cases hu
        | some t =>
          rw [ht] at hu
          simp only [Option.map_some, Option.some.injEq] at hu
          refine ⟨t, rfl, ?_⟩
          by_cases htr : r < t
          · rw [if_pos htr] at hu; rw [← hu]; exact hshv t (by omega)
          · rw [if_neg htr] at hu; rw [← hu]; exact hagree t (by omega) a ha (Or.inr ht)
    obtain ⟨t, hut, hvt⟩ := hup
    rw [hvt] at hO hcof hlt ⊢
    exact hQP.2 (r + a) t hut hO hcof q hq hlt

/-- **Residual of the AbsDN carry** (`t = 1`): at the bump columns of `D` below `x`, the index is not a
successor, and the seed condition at `η = 1` holds or the field holds at the new value (C′ の 2 万行列 ×
n = 2, 3 で 6112 件、欄は全件成立、種の条件は 56 件で偽: v(P_1 i) の加数が W より遥かに小さく、比較が穴まで
降りない場合). -/
def AbsDNRes (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    ∀ i, i < r + L → DepX M (r + L) false i → entry M 2 i ≠ 0 →
    isSucc (Z i) = false ∧
      (SeedCond (vOpt ρ (par M 1 i)) (Z i) (etaOm (holeLev (bumpW M ρ i))) one ∨
        (cof (fsD (bumpW M ρ i) (Z i)) = .omega → NotNode (fsD (bumpW M ρ i) (Z i)) →
          ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < fsD (bumpW M ρ i) (Z i) →
            q < fsD (fsD (bumpW M ρ i) (Z i)) one))

/-- **AbsDN is carried** (`t = 1`), with `AgrT1` from `P`. Residual `AbsDNRes`. -/
theorem expStep_absDN {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hRes : AbsDNRes M r L d0 ρ) :
    ExpStepT1 (fun N σ => AgrT1 M r ρ N σ ∧ AbsDN N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  intro n hn ρP Z hCP hGP hQP hCN hGN hoto hotv hle hlex hH
  refine ⟨expStep_agr hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 n hn ρP Z hCP hGP hQP.1 hCN hGN
    hoto hotv hle hlex hH, ?_⟩
  have hR := hRes n hn ρP Z hH
  obtain ⟨μ, br, vr, seed, k0, hHD, hZk, _, _, _, _⟩ := hH
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hpath := hpath_of_par1 h1 hA (by omega)
  intro i hi he1 he2 hO hcof hNN q hq hlt
  rcases Nat.lt_or_ge i (r + L) with hi' | hi'
  · have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
      (hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn)
      (hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn) i hi'
    rw [hSA.e1] at he1; rw [hSA.e2] at he2
    have hiM : i < M.length := by omega
    by_cases hv : DepX M (r + L) false i
    · have hHv := hHD.hole false i hv hi'
      simp only [valB, cond_false] at hHv
      obtain ⟨k, _, hZe⟩ := hZk i
      have hZs : ∃ s y, Z i = psi s y z := by rw [hZe]; exact gamS_single hHD.seedS k
      obtain ⟨hW, hV, hHW, hWot⟩ := bumpW_D hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 hn
        I.cons I.good hCN hGN hi' hv he2 hHv hZs
      rw [← hσ] at hW hV
      rw [hV] at hq
      rw [hW] at hlt hO hcof hNN ⊢
      obtain ⟨hζs, hSC⟩ := hR i hi' hv he2
      rcases hSC with hSC | hFld
      · have hOW := ohole_of_holeT hHW
        have hζz : Z i ≠ z := by obtain ⟨s, y, h⟩ := hZs; rw [h]; simp
        have hlt' : fsD (bumpW M ρ i) (Z i) < bumpW M ρ i := by
          rw [hZe]; exact (hok_of_holeT hHD.rot hHD.cb hHD.hμ hHD.S hWot hHW k).2
        exact absorb_fsD_W hOW hζz hζs (I.ad i hiM he1 he2 hOW) hlt' hSC q hq hlt
      · exact hFld hcof hNN q hq hlt
    · obtain ⟨hW, hV⟩ := bumpW_off hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 hn
        (ρ := ρ) (ρP := ρP) (Z := Z) hi' hv he1 he2
      rw [← hσ] at hW hV
      rw [hV] at hq
      rw [hW] at hlt hO hcof hNN ⊢
      exact I.adn i hiM he1 he2 hO hcof hNN q hq hlt
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    rw [e1_gexp_shift hlen hL hn ha] at he1
    rw [e2_copy (d0 := d0) hlen hL hn ha] at he2
    have hW := bumpW_copy hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 hn
      (ρ := ρ) (ρP := ρP) (Z := Z) ha
    have hV := vOpt_par_copy hlen hL hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 hx2 hn (Z := Z) hQP.1 ha
    rw [← hσ] at hW hV
    rw [hV] at hq
    rw [hW] at hlt hO hcof hNN ⊢
    exact hQP.2 (r + a) (by omega) he1 he2 hO hcof hNN q hq hlt

end Ytosk
