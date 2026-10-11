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
successor and the seed condition holds for the subterms of `v(P_1 i)`, or the field holds at the new value
(C′ の 4 万行列 × 鎖の項 k = 0..4 で 64190 件。種の条件で成り立たないのは種 = 1（q = r・n = 2）の 1232 件だけ). -/
def AbsDRes (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ i, i < r + L → DepX M (r + L) false i → entry M 2 i ≠ 0 →
    (isSucc (Z i) = false ∧
      SeedCond (vOpt ρ (par M 1 i)) (Z i) (etaOm (holeLev (bumpW M ρ i))) (etaOm (holeLev (Z i)))) ∨
    (OHole (fsD (bumpW M ρ i) (Z i)) → ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < fsD (bumpW M ρ i) (Z i) →
      q < fsD (fsD (bumpW M ρ i) (Z i)) (etaOm (holeLev (fsD (bumpW M ρ i) (Z i)))))

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
  have hR := hRes n hn ρP Z hH hCN
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
      rcases hR i hi' hv he2 with ⟨hζs, hSC⟩ | hFld
      · have hOW := ohole_of_holeT hHW
        have hζz : Z i ≠ z := by obtain ⟨s, y, h⟩ := hZs; rw [h]; simp
        have hlt' : fsD (bumpW M ρ i) (Z i) < bumpW M ρ i := by
          rw [hZe]; exact (hok_of_holeT hHD.rot hHD.cb hHD.hμ hHD.S hWot hHW k).2
        rw [holeLev_fsD hOW hζz hζs]
        exact absorb_fsD_W hOW hζz hζs (I.ad i hiM he1 he2 hOW) hlt' hSC q hq hlt
      · exact hFld hO q hq hlt
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
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ i k, i < r + L → upg M i = some k → DepX M (r + L) false k →
    (isSucc (Z k) = false ∧ SeedCond (vOpt ρ (par M 1 i)) (Z k) (etaOm (holeLev (last (ρ.v k)))) one) ∨
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < fsD (last (ρ.v k)) (Z k) →
        q < fsD (fsD (last (ρ.v k)) (Z k)) one

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
  have hR := hRes n hn ρP Z hH hCN
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
      rcases hR i k hi' hu hkv with ⟨hζs, hSC⟩ | hFld
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
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ i, i < r + L → DepX M (r + L) false i → entry M 2 i ≠ 0 →
    (isSucc (Z i) = false ∧ SeedCond (vOpt ρ (par M 1 i)) (Z i) (etaOm (holeLev (bumpW M ρ i))) one) ∨
      (cof (fsD (bumpW M ρ i) (Z i)) = .omega → NotNode (fsD (bumpW M ρ i) (Z i)) →
        ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < fsD (bumpW M ρ i) (Z i) →
          q < fsD (fsD (bumpW M ρ i) (Z i)) one)

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
  have hR := hRes n hn ρP Z hH hCN
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
      rcases hR i hi' hv he2 with ⟨hζs, hSC⟩ | hFld
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

/-! ## VSmallF -/

/-- **Residual of the VSmallF carry** (`t = 1`): the frames below `x` whose counted child `c` has a changed
`v` (`c` a `v` call of `D`, or `c = x`). The parent's `v` and the earlier counted children do not change there.
実測（C′ の 2 万行列 × n = 2, 3、36 万成分）: 新しい成分はすべて Ω_{v′(c)} 以下（B 側は不要）。v′(c) の前の部分
（v(P_1 c) の残った加数）は親の段で成分を持たず、成分は最後の加数 fsD(W, ζ) から来て Ω_{fsD(W, ζ)} 以下. -/
def VSFRes (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ i, i < r + L → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
    (DepX M (r + L) false c ∨ c = r + L) →
    ∀ g ∈ comps (ρ.v i) ((glueZ M (r + L) ρ (shiftV ρP L) Z).v c),
      g ≤ psi ((glueZ M (r + L) ρ (shiftV ρP L) Z).v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o))

/-- **VSmallF is carried** (`t = 1`): the frames off the changed children are those of `M` (the parent's
`v` and the earlier counted children do not change, as for FrameOT), the copy frames those of `P`.
Residual `VSFRes`. -/
theorem expStep_vsmallF {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hRes : VSFRes M r L d0 ρ) :
    ExpStepT1 VSmallF M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q0, hq0⟩ := par0_of_anc hA (by omega)
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq0
  intro n hn ρP Z hCP _ hQP hCN _ _ _ _ _ hH
  have hR := hRes n hn ρP Z hH hCN
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
    (hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn)
    (hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn)
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
  intro i hi Lc c R hCL
  rcases Nat.lt_or_ge i (r + L) with h | h
  · have hS := hSA i h
    have hCLe : CL (TRIO.gexp M r L d0 0 n) i = CL M i := by
      unfold CL; rw [hS.ch]
      apply List.filter_congr
      intro c hc
      exact decide_eq_decide.mpr (counted_iff_of_cnt (hS.cnt c hc))
    rw [hCLe] at hCL
    have hcCL : c ∈ CL M i := by rw [hCL]; simp
    have hcch : c ∈ children M i := (List.mem_filter.mp hcCL).1
    have hccnt : Counted M i c := by simpa using (List.mem_filter.mp hcCL).2
    have hvd : ¬ DepX M (r + L) false i := by
      intro hv
      rcases hOS i h (DepX.ov hv) with ⟨_, hnc⟩ | ⟨hnv, _⟩
      · rcases hnc c hcch with h' | h'
        · exact hccnt.1 h'
        · exact hccnt.2 h'
      · exact hnv hv
    have hLd : ∀ d ∈ Lc, ¬ DepX M (r + L) true d := by
      intro d hd hdD
      have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
      have hdch : d ∈ children M i := (List.mem_filter.mp hdCL).1
      have hdcnt : Counted M i d := by simpa using (List.mem_filter.mp hdCL).2
      have hdc : d < c := by
        have hs : (CL M i).Pairwise (· < ·) := (children_sorted M i).filter _
        rw [hCL] at hs
        exact (List.pairwise_append.mp hs).2.2 d hd c List.mem_cons_self
      have hiD : DepX M (r + L) true i := DepX.ochild hdch hdcnt.1 hdcnt.2 hdD
      rcases hOS i h hiD with ⟨hv, _⟩ | ⟨_, L', c', R', hch, _, _, hR', hL'⟩
      · exact hvd hv
      · have hdc' : d = c' := by
          rw [hch] at hdch
          rcases List.mem_append.mp hdch with h' | h'
          · exact absurd hdD (hL' d h' hdcnt)
          · rcases List.mem_cons.mp h' with h' | h'
            · exact h'
            · rcases hR' d h' with h'' | h''
              · exact absurd h'' hdcnt.1
              · exact absurd h'' hdcnt.2
        subst hdc'
        have hsort := children_sorted M i
        rw [hch] at hsort hcch
        rcases List.mem_append.mp hcch with h' | h'
        · have := (List.pairwise_append.mp hsort).2.2 c h' d List.mem_cons_self
          omega
        · rcases List.mem_cons.mp h' with h' | h'
          · omega
          · rcases hR' c h' with h'' | h''
            · exact hccnt.1 h''
            · exact hccnt.2 h''
    have hLo : Lc.map σ.o = Lc.map ρ.o := by
      apply List.map_congr_left
      intro d hd
      have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
      have hdM := (mem_children (List.mem_filter.mp hdCL).1).2
      have hdx : d < r + L := by
        rcases Nat.lt_or_ge d (r + L) with h' | h'
        · exact h'
        · exfalso
          have : d = r + L := by omega
          exact hLd d hd (this ▸ DepX.leaf)
      rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hdx (hLd d hd)]
    rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z h hvd, ← hσ, hLo]
    have hcM := (mem_children hcch).2
    by_cases hcv : DepX M (r + L) false c ∨ c = r + L
    · exact hR i h Lc c R hCL hcv
    · push_neg at hcv
      have hcx : c < r + L := by omega
      rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z hcx hcv.1]
      exact I.vs i (by omega) Lc c R hCL
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    have hCLs : CL (TRIO.gexp M r L d0 0 n) (r + L + a) =
        (CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a)).map (· + L) := by
      unfold CL
      rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha, List.filter_map]
      congr 1
      apply List.filter_congr
      intro d hd
      have hdc := mem_children hd
      rw [hlP] at hdc
      show decide (Counted (TRIO.gexp M r L d0 0 n) (r + L + a) (d + L)) =
        decide (Counted (TRIO.gexp M r L d0 0 (n - 1)) (r + a) d)
      apply decide_eq_decide.mpr
      apply counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath (I.z2 r) (ρ := ρ) (Z := Z) ha hd)
      · have := hσo (d - r); rw [show r + L + (d - r) = d + L by omega,
          show r + (d - r) = d by omega] at this
        exact this
      · obtain ⟨s, y, he⟩ := o_psi_form hCP (i := d) (by rw [hlP]; omega)
        rw [he]; simp
    rw [hCLs] at hCL
    obtain ⟨Lc', T', hsplit, hLc, hT⟩ := List.map_eq_append_iff.mp hCL
    obtain ⟨c', R', hT', hc', hR'⟩ := List.map_eq_cons_iff.mp hT
    subst hLc hc' hR'
    rw [hT'] at hsplit
    have hLo : (Lc'.map (· + L)).map σ.o = Lc'.map ρP.o := by
      rw [List.map_map]
      apply List.map_congr_left
      intro d hd
      have hdCL : d ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp [hd]
      have hdc := mem_children (List.mem_filter.mp hdCL).1
      have := hσo (d - r)
      rw [show r + L + (d - r) = d + L by omega, show r + (d - r) = d by omega] at this
      exact this
    have hc'c := mem_children (List.mem_filter.mp (show c' ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) by
      rw [hsplit]; simp)).1
    rw [hlP] at hc'c
    have hvc : σ.v (c' + L) = ρP.v c' := by
      have := hσv (c' - r)
      rw [show r + L + (c' - r) = c' + L by omega, show r + (c' - r) = c' by omega] at this
      exact this
    rw [hσv, hLo, hvc]
    exact hQP (r + a) (by rw [hlP]; omega) Lc' c' R' hsplit

/-! ## 組み立て: AbsD・AbsUW・AbsDN を運んだ形の hExp（t = 1） -/

/-- **The value fields of `Inv3V` still not carried** (`t = 1`): the three fields of the frame of the last column
(TPLoW・AbsDW・TPLoN). -/
def QV2 (N : Mat) (σ : Valn) : Prop := TPLoW N σ ∧ AbsDW N σ ∧ TPLoN N σ

/-- **The property carried along the `t = 1` chain** (with the A-group fields). -/
def PT1A (M : Mat) (r : Nat) (ρ : Valn) (N : Mat) (σ : Valn) : Prop :=
  FrameOT N σ ∧ RootP N σ ∧ BumpDec N σ ∧ FrameClosed N σ ∧ TrigOmC N σ ∧ TP1C N σ ∧ TP1WC N σ ∧
    TPLo N σ ∧ (AgrT1 M r ρ N σ ∧ AbsD N σ) ∧ (AgrT1 M r ρ N σ ∧ AbsUW N σ) ∧
    (AgrT1 M r ρ N σ ∧ AbsDN N σ) ∧ VSmallF N σ ∧ QV2 N σ

/-- **`Inv3V` from the chain's output.** -/
theorem inv3V_of_PT1A {M N : Mat} {r : Nat} {ρ σ : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ)
    (hR : Rk N rk) (hG : Good3 N σ) (hP : PT1A M r ρ N σ) : Inv3V N σ rk :=
  let ⟨fo, rp, ⟨kd, td⟩, fc, trig, tp1, tp1w, tplo, ⟨_, ad⟩, ⟨_, auw⟩, ⟨_, adn⟩, vs, tplow, adw, tplon⟩ := hP
  ⟨hC, hG, hR, vs, fc, fo, kd, td, ad, absU_of_absD hC hG ad, tp1, tplo, tp1w, tplow, auw, adw, trig, tplon, adn,
    rootS_of_good hC hG, rp⟩

/-- **`t = 1`, `n ≥ 2`, in the `gexp` form**, with AbsD・AbsUW・AbsDN carried. Residuals: the base
`RestT`, the step `hQs` of `QV2`, and the residuals of the carried fields. -/
theorem inv3V_N_t1A {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 1 (r + L) = some r)
    (hx2 : entry M 2 (r + L) = 0)
    (hRT : RestT M rk)
    (hQs : ExpStepT1 QV2 M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResL : TPLoRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResD : AbsDRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResU : AbsUWRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResDN : AbsDNRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResV : VSFRes M r L (entry M 0 (r + L) - entry M 0 r) ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN,
      Inv3V (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN rkN ∧
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN < root M ρ := by
  intro n hn
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; have := par_lt M 1 _ r hr; omega
    · exact h
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hdr := R.drop
  have hsd := R.seed
  rw [show M.length - 1 = r + L by omega] at hdr hsd
  have hVI : ValInv M ρ := ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩
  have V1 := valInv_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank hVI hdr
  have hx0 : entry M 0 (r + L) ≠ 0 := by
    have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
  have hRP1 := rootP_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r01 I.r12 I.e00 hx0 I.cons I.rank hVI hdr
    I.rootP
  have hRT' := hRT
  simp only [RestT] at hRT'
  rw [show M.length - 1 = r + L by omega] at hRT'
  obtain ⟨ad, tp1, tplo, tp1w, tplow, auw, adw, trig, tplon, adn⟩ := hRT'
  have hAg := agr_base hlen hL0 hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 I.cons I.good I.rank
  have hP1 : PT1A M r ρ (M.take (r + L)) (drop1 M (r + L) rk) :=
    ⟨V1.fo, hRP1, ⟨V1.kd, V1.td⟩, V1.fc, trig, tp1, tp1w, tplo, ⟨hAg, ad⟩, ⟨hAg, auw⟩, ⟨hAg, adn⟩,
      V1.vs, tplow, adw, tplon⟩
  have hPs : ExpStepT1 (PT1A M r ρ) M r L (entry M 0 (r + L) - entry M 0 r) ρ :=
    expStep_and (expStep_frameOT_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.fo)
      (expStep_and (expStep_rootP_t1 hlen hL0 hd0e I.z2 I.uat I.r12 I.be I.r01 I.e00 hr hx2 I.rootP)
        (expStep_and (expStep_bumpDec_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.good
            ⟨I.kd, I.td⟩)
          (expStep_and (expStep_frameClosed_t1' I hlen hL0 hd0e hr hx2)
            (expStep_and (expStep_trigOmC I hlen hL0 hd0e hr hx2)
              (expStep_and (expStep_tp1C I hlen hL0 hd0e hr hx2)
                (expStep_and (expStep_tp1WC I hlen hL0 hd0e hr hx2)
                  (expStep_and (expStep_tplo I hlen hL0 hd0e hr hx2 hResL)
                    (expStep_and (expStep_absD I hlen hL0 hd0e hr hx2 hResD)
                      (expStep_and (expStep_absUW I hlen hL0 hd0e hr hx2 hResU)
                        (expStep_and (expStep_absDN I hlen hL0 hd0e hr hx2 hResDN)
                          (expStep_and (expStep_vsmallF I hlen hL0 hd0e hr hx2 hResV) hQs)))))))))))
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩ :=
      qr_final4 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2 hq
        I.cons I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua I.ad I.tp1w
        I.tplow I.auw I.adw I.tp1 I.trig I.tplon I.adn I.rootS I.rootP (hsd q hr hq) (PT1A M q ρ) hP1 hPs n hn
    exact ⟨ρN, rkN, inv3V_of_PT1A hCN hRN hGN hPN, hot, hlt⟩
  · obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons (show r < M.length by omega)
    obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩ :=
      t1_main_final hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2
        (fun h' => hqr (Option.some.inj (hq.symm.trans h'))) I.cons I.good I.rank I.vs I.fc I.fo
        I.tp1 I.tplo I.ad I.au hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua rfl h0 I.rootS I.rootP
        V1.g (PT1A M r ρ) hP1 hPs n hn
    exact ⟨ρN, rkN, inv3V_of_PT1A hCN hRN hGN hPN, hot, hlt⟩

/-- **The `t = 1` part of `hExp`** with AbsD・AbsUW・AbsDN carried. Residuals (each for the `t = 1`
matrices only): `hRT` (the base, shared with `hLast`), `hQs` (`QV2` = TPLoW・AbsDW・TPLoN), the
residuals of the carried fields (`TPLoRes`・`AbsDRes`・`AbsUWRes`・`AbsDNRes`・`VSFRes`), and `hRes`
(`Res3A` of `M[n]`). -/
theorem hExp_t1A
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hQs : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      ExpStepT1 QV2 M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      TPLoRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
      AbsDRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsUWRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
      AbsDNRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ VSFRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hRes : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → ∀ n, 2 ≤ n →
      ∀ σ rkN, Inv3 (expand M n) σ rkN → Res3A (expand M n) σ rkN) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
      ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz h1t n hn hNS _
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hlen2 : 2 ≤ M.length := by
    by_contra h
    have hx0 : M.length - 1 = 0 := by omega
    apply hz
    rw [hx0]
    have e0 := I.e00
    have e1 := I.r01 0 e0
    have e2 := I.r12 0 e1
    exact (col_zero_iff M 0).mpr ⟨e0, e1, e2⟩
  have hx2 : entry M 2 (M.length - 1) = 0 := by
    unfold TRIO.srow at h1t
    by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
    · rw [if_pos ha] at h1t; cases h1t
    · show TRIO.entry M 2 (M.length - 1) = 0; omega
  rw [h1t] at hr
  have hexp := expand_eq_gexp_t1 M n hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  rw [hL] at hexp hr hx2
  simp only [Nat.add_sub_cancel_left] at hexp
  have hlen : r + L + 1 = M.length := by omega
  obtain ⟨ρN, rkN, V, _, _⟩ :=
    inv3V_N_t1A I R hlen hr hx2 (hRT M ρ rk hM hS I R hz h1t)
      (hQs M ρ rk hM hS I R r L hlen hr hx2)
      (hResN M ρ rk hM hS I R r L hlen hr hx2).1 (hResN M ρ rk hM hS I R r L hlen hr hx2).2.1
      (hResN M ρ rk hM hS I R r L hlen hr hx2).2.2.1 (hResN M ρ rk hM hS I R r L hlen hr hx2).2.2.2.1
      (hResN M ρ rk hM hS I R r L hlen hr hx2).2.2.2.2 n hn
  rw [← hexp] at V
  exact ⟨ρN, rkN, V, hRes M ρ rk hM hS I R hz h1t n hn ρN rkN
    (Inv3.ofV (sInv_std (Std.exp n hM) hNS) V)⟩


end Ytosk
