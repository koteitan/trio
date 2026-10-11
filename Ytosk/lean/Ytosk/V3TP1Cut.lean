/-
**TP1C を PH3c から導く（2026-10-12、drop-fix）。**

書き換える数える子の枠（状態 B、子 ψ_s(y)、y の穴の段 μ、η = ψ_μ(1)）で、B < fsD(y, η) を示す。
- B = 0、PH3c の eq・pre: B は y の先頭部分なので t0-exp の `prefix_fsD`。
- cut で lo ≠ 0: fsD は lo の中しか変えないので B ≤ hi < fsD(y, η)。
- cut で lo = 0: 切り口の位置 π（B が Ω_s に替えた位置）と fsD の穴の道を比べる（`cutNS_lt`・`cutH_lt`・`scut_lt`）。
  π より右か π の項の引数の中で fsD が働くなら、π の項の添字は残り B < fsD(y, η)。π の項が後続の葉 Ω_{μ+1} なら
  fsD はそれを η = ψ_μ(1) に替え、s ≤ μ なので Ω_s < η。π の項が Ω_k（k は極限）で穴が k の中のときだけ、
  s < fsD(k, η) が要る（残り `TP1Leaf`。5 集合で C′ の 5 枠だけ、どれも k = s + X）。
共終数が大きい項では fsD = fs（`fsD_eq_fs`）なので、穴の道の上で fsD は同じ η のまま降りる（`fsD_psi`）。
-/
import Ytosk.V3ExpT0
import Ytosk.V3T0RW
import Ytosk.V3PDef
import Ytosk.V3PSh
import Ytosk.V3T0Cut
import Ytosk.V3FsdComp
import Ytosk.V3GroupA

namespace Ytosk

open T

/-! ## 切り口の葉 -/

/-- The leaf of a subscript-chain cut: `t ∈ scuts s a` reaches `Ω_k` with the replaced term `Ω_k` itself. -/
inductive SLeaf (s : T) : T → T → T → Prop
  | here (k : T) : SLeaf s (psi s z z) (psi k z z) k
  | sub {t a k : T} : SLeaf s t a k → SLeaf s (psi t z z) (psi a z z) k

/-- The leaf of a high-path cut (`cutsH`). -/
inductive HLeaf (s : T) : T → T → T → Prop
  | here (k : T) : HLeaf s (psi s z z) (psi k z z) k
  | arg {b t w k : T} : HLeaf s t w k → HLeaf s (psi b t z) (psi b w z) k
  | rest {b w t c k : T} : HLeaf s t c k → HLeaf s (psi b w t) (psi b w c) k

/-- The leaf of a cut of `PH3c` (`cutsNS`). -/
inductive CLeaf (s : T) : T → T → T → Prop
  | sub {t a k : T} : SLeaf s t a k → CLeaf s (psi t z z) (psi a z z) k
  | arg {a t x k : T} : HLeaf s t x k → CLeaf s (psi a t z) (psi a x z) k
  | rest {a x B c k : T} : CLeaf s B c k → CLeaf s (psi a x B) (psi a x c) k

/-! ## 順序の小さな補題 -/

theorem om_lt_om_inv {t a : T} (h : psi t z z < psi a z z) : t < a := by
  rw [psi_lt_psi_z_iff] at h
  rcases h with h | ⟨_, h⟩
  · exact h
  · exact absurd h (T.not_lt_z _)

theorem om_lt_psi_arg {k w : T} (hw : w ≠ z) : psi k z z < psi k w z := by
  rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, lt_of_le_of_ne (z_le w) (Ne.symm hw)⟩

theorem psi_lt_rest {a b c : T} (hc : c ≠ z) : psi a b z < psi a b c := by
  rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, lt_of_le_of_ne (z_le c) (Ne.symm hc)⟩)

theorem om_lt_eta {s μ : T} (h : s ≤ μ) : psi s z z < psi μ one z :=
  lt_of_le_of_lt (psi_le_psi_z h) (om_lt_psi_arg (by simp [one]))

/-- `scuts` reads only the head subscript, so a successor has the cuts of its predecessor. -/
theorem scuts_succ {s : T} : ∀ {m : T}, m ≠ z → scuts s (succ m) = scuts s m
  | z, h => absurd rfl h
  | psi a b c, _ => by simp [succ, scuts, app]

/-- The cuts along the subscripts of a successor `k` are at most its predecessor (`s ≠ 0`). -/
theorem scuts_le_init {s k t : T} (hs : s ≠ z) (hk : isSucc k = true) (ht : t ∈ scuts s k) :
    t ≤ init k := by
  have hke := init_app_one hk
  by_cases h0 : init k = z
  · exfalso
    rw [h0] at hke
    rw [← hke] at ht
    simp only [app, one, scuts, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨u, hu, _⟩
    · split at ht
      · rename_i hle
        exact hs (by
          have := le_of_le_bool hle
          rcases (le_iff _ _).mp this with h | h
          · exact absurd h (T.not_lt_z _)
          · exact h)
      · simp at ht
    · simp at hu
  · rw [← hke, show app (init k) one = succ (init k) from rfl, scuts_succ h0] at ht
    exact scuts_le ht

theorem ohole_rest {a b c : T} (hc : c ≠ z) (h : OHole (psi a b c)) : OHole c := by
  cases c with
  | z => exact absurd rfl hc
  | psi _ _ _ => exact h

theorem holeLev_rest_ne {a b c : T} (hc : c ≠ z) : holeLev (psi a b c) = holeLev c := by
  cases c with
  | z => exact absurd rfl hc
  | psi _ _ _ => rfl

/-- At a nonzero argument, a hole is not a successor and the argument has a hole. -/
theorem ohole_arg {a b : T} (hb : b ≠ z) (h : OHole (psi a b z)) : isSucc b = false ∧ OHole b := by
  unfold OHole at h
  rw [if_neg hb] at h
  by_cases hs : isSucc b = true
  · rw [if_pos hs] at h; exact absurd h id
  · rw [if_neg hs] at h
    refine ⟨by simpa using hs, ?_⟩
    cases hc : cof b with
    | big μ => exact ohole_of_cof_big hc
    | zero => rw [hc] at h; exact h
    | succ => rw [hc] at h; exact h
    | omega => rw [hc] at h; exact h

theorem ohole_om {k : T} (h : OHole (psi k z z)) : k ≠ z ∧ (isSucc k = true ∨ OHole k) := by
  unfold OHole at h; rw [if_pos rfl] at h; exact h

theorem holeLev_om_succ {k : T} (hs : isSucc k = true) : holeLev (psi k z z) = init k := by
  simp [holeLev, hs]

theorem holeLev_om {k : T} (hs : isSucc k = false) : holeLev (psi k z z) = holeLev k := by
  simp [holeLev, hs]

/-! ## 3 つの帰納法 -/

section
variable {s μ : T}

/-- **Subscript-chain cuts.** -/
theorem scut_lt (hs : s ≠ z) : ∀ {a t : T}, t ∈ scuts s a → t < a → OHole a → holeLev a = μ →
    (∀ k, SLeaf s t a k → isSucc k = false → OHole k → s < fsD k (psi μ one z)) →
    t < fsD a (psi μ one z)
  | z, _, ht, _, _, _, _ => by simp [scuts] at ht
  | psi k γ r, t, ht, hlt, hO, hμ, hL => by
    have ht' := ht
    simp only [scuts, List.mem_append, List.mem_map] at ht'
    have htle : t ≤ psi k z z := by
      rcases ht' with h | ⟨u, hu, rfl⟩
      · split at h
        · rename_i hle; simp only [List.mem_singleton] at h; subst h
          exact psi_le_psi_z (le_of_le_bool hle)
        · simp at h
      · exact psi_le_psi_z (scuts_le hu)
    by_cases hr : r = z
    · subst hr
      by_cases hγ : γ = z
      · subst hγ
        obtain ⟨hk0, hk⟩ := ohole_om hO
        by_cases hks : isSucc k = true
        · rw [fsD_leaf hks hk0]
          rw [holeLev_om_succ hks] at hμ
          rcases ht' with h | ⟨u, hu, rfl⟩
          · split at h
            · simp only [List.mem_singleton] at h; subst h
              have hsk := om_lt_om_inv hlt
              rw [← init_app_one hks] at hsk
              exact om_lt_eta (by rw [← hμ]; exact lt_succ_iff.mp hsk)
            · simp at h
          · exact om_lt_eta (by rw [← hμ]; exact scuts_le_init hs hks hu)
        · have hks' : isSucc k = false := by simpa using hks
          have hOk : OHole k := hk.resolve_left hks
          rw [fsD_sub hk0 hks']
          rw [holeLev_om hks'] at hμ
          rcases ht' with h | ⟨u, hu, rfl⟩
          · split at h
            · simp only [List.mem_singleton] at h; subst h
              exact psi_lt_psi_z_iff.mpr (Or.inl (hL k (SLeaf.here k) hks' hOk))
            · simp at h
          · exact psi_lt_psi_z_iff.mpr (Or.inl (scut_lt hs hu (om_lt_om_inv hlt) hOk hμ
              (fun k' hl => hL k' (SLeaf.sub hl))))
      · obtain ⟨hγs, hγO⟩ := ohole_arg hγ hO
        rw [fsD_psi hγ hγs]
        exact lt_of_le_of_lt htle (om_lt_psi_arg (fsD_ne_z_oh hγO (by simp [one])))
    · rw [fsD_rest hr]
      have hrO := ohole_rest hr hO
      exact lt_of_le_of_lt (le_trans htle (psi_le_psi_any (le_refl k)))
        (psi_lt_rest (fsD_ne_z_oh hrO (by simp [one])))

/-- **High-path cuts.** -/
theorem cutH_lt : ∀ {x t : T}, t ∈ cutsH s x → t < x → OHole x → holeLev x = μ →
    (∀ k, HLeaf s t x k → isSucc k = false → OHole k → s < fsD k (psi μ one z)) →
    t < fsD x (psi μ one z)
  | z, _, ht, _, _, _, _ => by simp [cutsH] at ht
  | psi b w c, t, ht, hlt, hO, hμ, hL => by
    rcases mem_cutsH_psi.mp ht with ⟨hsb, rfl⟩ | ⟨hsb, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · -- `t = Ω_s` replaces the term `ψ_b(w) + c`
      have hsb' := le_of_le_bool hsb
      by_cases hc : c = z
      · subst hc
        by_cases hw : w = z
        · subst hw
          obtain ⟨hb0, hb⟩ := ohole_om hO
          by_cases hbs : isSucc b = true
          · rw [fsD_leaf hbs hb0]
            rw [holeLev_om_succ hbs] at hμ
            have hsb2 := om_lt_om_inv hlt
            rw [← init_app_one hbs] at hsb2
            exact om_lt_eta (by rw [← hμ]; exact lt_succ_iff.mp hsb2)
          · have hbs' : isSucc b = false := by simpa using hbs
            rw [fsD_sub hb0 hbs']
            exact psi_lt_psi_z_iff.mpr (Or.inl (hL b (HLeaf.here b) hbs' (hb.resolve_left hbs)))
        · obtain ⟨hws, hwO⟩ := ohole_arg hw hO
          rw [fsD_psi hw hws]
          exact lt_of_le_of_lt (psi_le_psi_z hsb') (om_lt_psi_arg (fsD_ne_z_oh hwO (by simp [one])))
      · rw [fsD_rest hc]
        exact lt_of_le_of_lt (psi_le_psi_any hsb') (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) (by simp [one])))
    · -- `t = ψ_b(u)`, `u ∈ cutsH s w`
      by_cases hc : c = z
      · subst hc
        have hw : w ≠ z := by rintro rfl; simp [cutsH] at hu
        obtain ⟨hws, hwO⟩ := ohole_arg hw hO
        rw [fsD_psi hw hws]
        have hult : u < w := by
          rw [psi_lt_psi_z_iff] at hlt
          rcases hlt with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact h
        rw [holeLev_psi_arg hw] at hμ
        exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, cutH_lt hu hult hwO hμ (fun k hl => hL k (HLeaf.arg hl))⟩)
      · rw [fsD_rest hc]
        have hule := cutsH_le hu
        exact lt_of_le_of_lt (psi_le_psi_arg hule) (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) (by simp [one])))
    · -- `t = ψ_b(w) + u`, `u ∈ cutsH s c`
      have hc : c ≠ z := by rintro rfl; simp [cutsH] at hu
      rw [fsD_rest hc]
      have hult : u < c := by
        rw [T.psi_lt_psi] at hlt
        rcases hlt with h | ⟨_, h⟩ | ⟨_, _, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact absurd h (lt_irrefl' _)
        · exact h
      rw [holeLev_rest_ne hc] at hμ
      rw [T.psi_lt_psi]
      exact Or.inr (Or.inr ⟨rfl, rfl, cutH_lt hu hult (ohole_rest hc hO) hμ (fun k hl => hL k (HLeaf.rest hl))⟩)

/-- **The cuts of `PH3c`.** -/
theorem cutNS_lt (hs : s ≠ z) : ∀ {h B : T}, B ∈ cutsNS s h → B < h → OHole h → holeLev h = μ →
    (∀ k, CLeaf s B h k → isSucc k = false → OHole k → s < fsD k (psi μ one z)) →
    B < fsD h (psi μ one z)
  | z, _, hB, _, _, _, _ => by simp [cutsNS] at hB
  | psi a x c, B, hB, hlt, hO, hμ, hL => by
    simp only [cutsNS, List.mem_append, List.mem_map] at hB
    rcases hB with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
    · -- `B = Ω_t`, `t ∈ scuts s a`
      have hta := scuts_le ht
      by_cases hc : c = z
      · subst hc
        by_cases hx : x = z
        · subst hx
          obtain ⟨ha0, ha⟩ := ohole_om hO
          by_cases has : isSucc a = true
          · rw [fsD_leaf has ha0]
            rw [holeLev_om_succ has] at hμ
            exact om_lt_eta (by rw [← hμ]; exact scuts_le_init hs has ht)
          · have has' : isSucc a = false := by simpa using has
            have haO : OHole a := ha.resolve_left has
            rw [fsD_sub ha0 has']
            rw [holeLev_om has'] at hμ
            exact psi_lt_psi_z_iff.mpr (Or.inl (scut_lt hs ht (om_lt_om_inv hlt) haO hμ
              (fun k hl => hL k (CLeaf.sub hl))))
        · obtain ⟨hxs, hxO⟩ := ohole_arg hx hO
          rw [fsD_psi hx hxs]
          exact lt_of_le_of_lt (psi_le_psi_z hta) (om_lt_psi_arg (fsD_ne_z_oh hxO (by simp [one])))
      · rw [fsD_rest hc]
        exact lt_of_le_of_lt (psi_le_psi_any hta) (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) (by simp [one])))
    · -- `B = ψ_a(t)`, `t ∈ cutsH s x`
      by_cases hc : c = z
      · subst hc
        have hx : x ≠ z := by rintro rfl; simp [cutsH] at ht
        obtain ⟨hxs, hxO⟩ := ohole_arg hx hO
        rw [fsD_psi hx hxs]
        have htx : t < x := by
          rw [psi_lt_psi_z_iff] at hlt
          rcases hlt with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact h
        rw [holeLev_psi_arg hx] at hμ
        exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, cutH_lt ht htx hxO hμ (fun k hl => hL k (CLeaf.arg hl))⟩)
      · rw [fsD_rest hc]
        exact lt_of_le_of_lt (psi_le_psi_arg (cutsH_le ht)) (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) (by simp [one])))
    · -- `B = ψ_a(x) + t`, `t ∈ cutsNS s c`
      have hc : c ≠ z := by rintro rfl; simp [cutsNS] at ht
      rw [fsD_rest hc]
      have htc : t < c := by
        rw [T.psi_lt_psi] at hlt
        rcases hlt with h | ⟨_, h⟩ | ⟨_, _, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact absurd h (lt_irrefl' _)
        · exact h
      rw [holeLev_rest_ne hc] at hμ
      rw [T.psi_lt_psi]
      exact Or.inr (Or.inr ⟨rfl, rfl, cutNS_lt hs ht htc (ohole_rest hc hO) hμ (fun k hl => hL k (CLeaf.rest hl))⟩)

end

/-! ## 枠の形 -/

/-- **The residual of TP1**: at a rewriting frame of kind `cut` with `lo = 0`, a cut whose replaced term is
`Ω_k` with the hole inside a limit `k` needs `s < fsD(k, η)` (5 集合で C′ の 5 枠、どれも k = s + X). -/
def TP1Leaf (N : Mat) (σ : Valn) : Prop :=
  ∀ i, i < N.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL N i = L ++ c :: R → ∀ s y,
    σ.o c = psi s y z → stB σ i L ≠ z →
    lt (stB σ i L) y = true → lt (psi (σ.v i) z z) (psi s y z) = true →
    (split y (psi (succ s) z z)).2 = z → OHole y →
    ∀ k, CLeaf s (stB σ i L) y k → isSucc k = false → OHole k → s < fsD k (psi (holeLev y) one z)

/-- **TP1 at a frame of a kind of `PH3c`.** -/
theorem ptp1_of_kind {a B s y : T} (hlt : lt B y = true)
    (hK : PH3cKind B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s)
    (hL : (split y (psi (succ s) z z)).2 = z → OHole y →
      ∀ k, CLeaf s B y k → isSucc k = false → OHole k → s < fsD k (psi (holeLev y) one z)) :
    PTP1 a B s y := by
  intro hO
  have hy : app (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 = y := split_app _ y
  rcases hK with ⟨heq, _⟩ | ⟨_, ⟨R, _, hpre⟩ | ⟨hs, hcut⟩⟩
  · exact prefix_fsD hlt (Or.inr ⟨_, by rw [← heq, hy]⟩) hO (by simp [one])
  · exact prefix_fsD hlt (Or.inr ⟨app R (split y (psi (succ s) z z)).2, by
      rw [← app_assoc, ← hpre]; exact hy.symm⟩) hO (by simp [one])
  · by_cases hlo : (split y (psi (succ s) z z)).2 = z
    · have hy' : (split y (psi (succ s) z z)).1 = y := by
        have h := hy; rw [hlo, app_z_right] at h; exact h
      rw [hy'] at hcut
      exact cutNS_lt hs hcut hlt hO rfl (hL hlo hO)
    · have hO' : OHole (app (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2) := by rw [hy]; exact hO
      have key : B < fsD (app (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2)
          (psi (holeLev y) one z) := by
        rw [fsD_app _ hlo]
        exact lt_of_le_of_lt (cutsNS_le hcut) (lt_app_of (fsD_ne_z_oh (ohole_app_inv0 hlo hO') (by simp [one])))
      rw [hy] at key
      exact key

/-- **TP1C from PH3c** and the leaf residual `TP1Leaf`, for any matrix and valuation. -/
theorem tp1C_of_ph3c {N : Mat} {σ : Valn} (hC : Cons N σ) (hO : GoodOT N σ) (hP : PH3c N σ)
    (hL : TP1Leaf N σ) : TP1C N σ := by
  rw [← rwc_tp1]
  refine rwc_of_cl (P := PTP1) hC hO ?_
  intro i hi L c R hcl s y hcy hlt htr
  by_cases hB : spArg (σ.v i) z (sumN (L.map σ.o)) = z
  · exact ptp1_prefix hlt (Or.inl hB)
  · exact ptp1_of_kind hlt (hP i hi L c R hcl s y hcy hB ⟨hlt, htr⟩)
      (fun hlo hOy k hk h1 h2 => hL i hi L c R hcl s y hcy hB hlt htr hlo hOy k hk h1 h2)

/-! ## 一般の η（TP1W 用）: 後続の葉も残りにする -/

/-- The pairs `(u, Ω_k)` of a subscript-chain cut along the chain. -/
inductive SPair (s : T) : T → T → T → T → Prop
  | top (t k : T) : SPair s t (psi k z z) t k
  | sub {t a u k : T} : SPair s t a u k → SPair s (psi t z z) (psi a z z) u k

/-- The pairs `(u, Ω_k)` of a high-path cut. -/
inductive HPair (s : T) : T → T → T → T → Prop
  | top (t k : T) : HPair s t (psi k z z) t k
  | arg {b t w u k : T} : HPair s t w u k → HPair s (psi b t z) (psi b w z) u k
  | rest {b w t c u k : T} : HPair s t c u k → HPair s (psi b w t) (psi b w c) u k

/-- The pairs `(u, Ω_k)` of a cut of `PH3c`. -/
inductive CPair (s : T) : T → T → T → T → Prop
  | top (B k : T) : CPair s B (psi k z z) B k
  | sub {t a u k : T} : SPair s t a u k → CPair s (psi t z z) (psi a z z) u k
  | arg {a t x u k : T} : HPair s t x u k → CPair s (psi a t z) (psi a x z) u k
  | rest {a x B c u k : T} : CPair s B c u k → CPair s (psi a x B) (psi a x c) u k

section
variable {s η : T} (hη : η ≠ z)
include hη

/-- **Subscript-chain cuts, any index.** -/
theorem scut_ltG (hs : s ≠ z) : ∀ {a t : T}, t ∈ scuts s a → t < a → OHole a →
    (∀ u k, SPair s t a u k → isSucc k = true → u < η) →
    (∀ k, SPair s t a (psi s z z) k → isSucc k = false → OHole k → s < fsD k η) →
    t < fsD a η
  | z, _, ht, _, _, _, _ => by simp [scuts] at ht
  | psi k γ r, t, ht, hlt, hO, hS, hL => by
    have ht' := ht
    simp only [scuts, List.mem_append, List.mem_map] at ht'
    have htle : t ≤ psi k z z := by
      rcases ht' with h | ⟨u, hu, rfl⟩
      · split at h
        · rename_i hle; simp only [List.mem_singleton] at h; subst h
          exact psi_le_psi_z (le_of_le_bool hle)
        · simp at h
      · exact psi_le_psi_z (scuts_le hu)
    by_cases hr : r = z
    · subst hr
      by_cases hγ : γ = z
      · subst hγ
        obtain ⟨hk0, hk⟩ := ohole_om hO
        by_cases hks : isSucc k = true
        · rw [fsD_leaf hks hk0]; exact hS t k (SPair.top t k) hks
        · have hks' : isSucc k = false := by simpa using hks
          have hOk : OHole k := hk.resolve_left hks
          rw [fsD_sub hk0 hks']
          rcases ht' with h | ⟨u, hu, rfl⟩
          · split at h
            · simp only [List.mem_singleton] at h; subst h
              exact psi_lt_psi_z_iff.mpr (Or.inl (hL k (SPair.top _ k) hks' hOk))
            · simp at h
          · exact psi_lt_psi_z_iff.mpr (Or.inl (scut_ltG hs hu (om_lt_om_inv hlt) hOk
              (fun u' k' hp => hS u' k' (SPair.sub hp)) (fun k' hp => hL k' (SPair.sub hp))))
      · obtain ⟨hγs, hγO⟩ := ohole_arg hγ hO
        rw [fsD_psi hγ hγs]
        exact lt_of_le_of_lt htle (om_lt_psi_arg (fsD_ne_z_oh hγO hη))
    · rw [fsD_rest hr]
      have hrO := ohole_rest hr hO
      exact lt_of_le_of_lt (le_trans htle (psi_le_psi_any (le_refl k))) (psi_lt_rest (fsD_ne_z_oh hrO hη))

/-- **High-path cuts, any index.** -/
theorem cutH_ltG : ∀ {x t : T}, t ∈ cutsH s x → t < x → OHole x →
    (∀ u k, HPair s t x u k → isSucc k = true → u < η) →
    (∀ k, HPair s t x (psi s z z) k → isSucc k = false → OHole k → s < fsD k η) →
    t < fsD x η
  | z, _, ht, _, _, _, _ => by simp [cutsH] at ht
  | psi b w c, t, ht, hlt, hO, hS, hL => by
    rcases mem_cutsH_psi.mp ht with ⟨hsb, rfl⟩ | ⟨hsb, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · have hsb' := le_of_le_bool hsb
      by_cases hc : c = z
      · subst hc
        by_cases hw : w = z
        · subst hw
          obtain ⟨hb0, hb⟩ := ohole_om hO
          by_cases hbs : isSucc b = true
          · rw [fsD_leaf hbs hb0]; exact hS _ b (HPair.top _ b) hbs
          · have hbs' : isSucc b = false := by simpa using hbs
            rw [fsD_sub hb0 hbs']
            exact psi_lt_psi_z_iff.mpr (Or.inl (hL b (HPair.top _ b) hbs' (hb.resolve_left hbs)))
        · obtain ⟨hws, hwO⟩ := ohole_arg hw hO
          rw [fsD_psi hw hws]
          exact lt_of_le_of_lt (psi_le_psi_z hsb') (om_lt_psi_arg (fsD_ne_z_oh hwO hη))
      · rw [fsD_rest hc]
        exact lt_of_le_of_lt (psi_le_psi_any hsb') (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) hη))
    · by_cases hc : c = z
      · subst hc
        have hw : w ≠ z := by rintro rfl; simp [cutsH] at hu
        obtain ⟨hws, hwO⟩ := ohole_arg hw hO
        rw [fsD_psi hw hws]
        have hult : u < w := by
          rw [psi_lt_psi_z_iff] at hlt
          rcases hlt with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact h
        exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, cutH_ltG hu hult hwO
          (fun u' k hp => hS u' k (HPair.arg hp)) (fun k hp => hL k (HPair.arg hp))⟩)
      · rw [fsD_rest hc]
        exact lt_of_le_of_lt (psi_le_psi_arg (cutsH_le hu)) (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) hη))
    · have hc : c ≠ z := by rintro rfl; simp [cutsH] at hu
      rw [fsD_rest hc]
      have hult : u < c := by
        rw [T.psi_lt_psi] at hlt
        rcases hlt with h | ⟨_, h⟩ | ⟨_, _, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact absurd h (lt_irrefl' _)
        · exact h
      rw [T.psi_lt_psi]
      exact Or.inr (Or.inr ⟨rfl, rfl, cutH_ltG hu hult (ohole_rest hc hO)
        (fun u' k hp => hS u' k (HPair.rest hp)) (fun k hp => hL k (HPair.rest hp))⟩)

/-- **The cuts of `PH3c`, any index.** -/
theorem cutNS_ltG (hs : s ≠ z) : ∀ {h B : T}, B ∈ cutsNS s h → B < h → OHole h →
    (∀ u k, CPair s B h u k → isSucc k = true → u < η) →
    (∀ k, CPair s B h (psi s z z) k → isSucc k = false → OHole k → s < fsD k η) →
    B < fsD h η
  | z, _, hB, _, _, _, _ => by simp [cutsNS] at hB
  | psi a x c, B, hB, hlt, hO, hS, hL => by
    simp only [cutsNS, List.mem_append, List.mem_map] at hB
    rcases hB with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
    · have hta := scuts_le ht
      by_cases hc : c = z
      · subst hc
        by_cases hx : x = z
        · subst hx
          obtain ⟨ha0, ha⟩ := ohole_om hO
          by_cases has : isSucc a = true
          · rw [fsD_leaf has ha0]; exact hS _ a (CPair.top _ a) has
          · have has' : isSucc a = false := by simpa using has
            have haO : OHole a := ha.resolve_left has
            rw [fsD_sub ha0 has']
            exact psi_lt_psi_z_iff.mpr (Or.inl (scut_ltG hη hs ht (om_lt_om_inv hlt) haO
              (fun u k hp => hS u k (CPair.sub hp)) (fun k hp => hL k (CPair.sub hp))))
        · obtain ⟨hxs, hxO⟩ := ohole_arg hx hO
          rw [fsD_psi hx hxs]
          exact lt_of_le_of_lt (psi_le_psi_z hta) (om_lt_psi_arg (fsD_ne_z_oh hxO hη))
      · rw [fsD_rest hc]
        exact lt_of_le_of_lt (psi_le_psi_any hta) (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) hη))
    · by_cases hc : c = z
      · subst hc
        have hx : x ≠ z := by rintro rfl; simp [cutsH] at ht
        obtain ⟨hxs, hxO⟩ := ohole_arg hx hO
        rw [fsD_psi hx hxs]
        have htx : t < x := by
          rw [psi_lt_psi_z_iff] at hlt
          rcases hlt with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact h
        exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, cutH_ltG hη ht htx hxO
          (fun u k hp => hS u k (CPair.arg hp)) (fun k hp => hL k (CPair.arg hp))⟩)
      · rw [fsD_rest hc]
        exact lt_of_le_of_lt (psi_le_psi_arg (cutsH_le ht)) (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) hη))
    · have hc : c ≠ z := by rintro rfl; simp [cutsNS] at ht
      rw [fsD_rest hc]
      have htc : t < c := by
        rw [T.psi_lt_psi] at hlt
        rcases hlt with h | ⟨_, h⟩ | ⟨_, _, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact absurd h (lt_irrefl' _)
        · exact h
      rw [T.psi_lt_psi]
      exact Or.inr (Or.inr ⟨rfl, rfl, cutNS_ltG hs ht htc (ohole_rest hc hO)
        (fun u k hp => hS u k (CPair.rest hp)) (fun k hp => hL k (CPair.rest hp))⟩)

end

/-- **The residual of TP1W**: at a rewriting frame of kind `cut` with `lo = 0` and `cof y = ω`, no pair of the cut
reaches a successor `Ω_k` below `1`, and a pair `(Ω_s, Ω_k)` with a limit `k` has `s < fsD(k, 1)`. -/
def TP1WLeaf (N : Mat) (σ : Valn) : Prop :=
  ∀ i, i < N.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL N i = L ++ c :: R → ∀ s y,
    σ.o c = psi s y z → stB σ i L ≠ z →
    lt (stB σ i L) y = true → lt (psi (σ.v i) z z) (psi s y z) = true →
    (split y (psi (succ s) z z)).2 = z → cof y = .omega → OHole y →
    (∀ u k, CPair s (stB σ i L) y u k → isSucc k = true → u < one) ∧
    (∀ k, CPair s (stB σ i L) y (psi s z z) k → isSucc k = false → OHole k → s < fsD k one)

theorem ptp1w_of_kind {a B s y : T} (hlt : lt B y = true)
    (hK : PH3cKind B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s)
    (hL : (split y (psi (succ s) z z)).2 = z → cof y = .omega → OHole y →
      (∀ u k, CPair s B y u k → isSucc k = true → u < one) ∧
      (∀ k, CPair s B y (psi s z z) k → isSucc k = false → OHole k → s < fsD k one)) :
    PTP1W a B s y := by
  intro hcof hO
  have hη : one ≠ z := by simp [one]
  have hy : app (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 = y := split_app _ y
  rcases hK with ⟨heq, _⟩ | ⟨_, ⟨R, _, hpre⟩ | ⟨hs, hcut⟩⟩
  · exact prefix_fsD hlt (Or.inr ⟨_, by rw [← heq, hy]⟩) hO hη
  · exact prefix_fsD hlt (Or.inr ⟨app R (split y (psi (succ s) z z)).2, by
      rw [← app_assoc, ← hpre]; exact hy.symm⟩) hO hη
  · by_cases hlo : (split y (psi (succ s) z z)).2 = z
    · have hy' : (split y (psi (succ s) z z)).1 = y := by
        have h := hy; rw [hlo, app_z_right] at h; exact h
      rw [hy'] at hcut
      obtain ⟨h1, h2⟩ := hL hlo hcof hO
      exact cutNS_ltG hη hs hcut hlt hO h1 h2
    · have hO' : OHole (app (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2) := by rw [hy]; exact hO
      have key : B < fsD (app (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2) one := by
        rw [fsD_app _ hlo]
        exact lt_of_le_of_lt (cutsNS_le hcut) (lt_app_of (fsD_ne_z_oh (ohole_app_inv0 hlo hO') hη))
      rw [hy] at key
      exact key

/-- **TP1WC from PH3c** and the residual `TP1WLeaf`. -/
theorem tp1WC_of_ph3c {N : Mat} {σ : Valn} (hC : Cons N σ) (hO : GoodOT N σ) (hP : PH3c N σ)
    (hL : TP1WLeaf N σ) : TP1WC N σ := by
  rw [← rwc_tp1w]
  refine rwc_of_cl (P := PTP1W) hC hO ?_
  intro i hi L c R hcl s y hcy hlt htr
  by_cases hB : spArg (σ.v i) z (sumN (L.map σ.o)) = z
  · exact ptp1w_prefix hlt (Or.inl hB)
  · exact ptp1w_of_kind hlt (hP i hi L c R hcl s y hcy hB ⟨hlt, htr⟩)
      (fun hlo hcof hOy => hL i hi L c R hcl s y hcy hB hlt htr hlo hcof hOy)

/-! ## TrigOm -/

/-- **The residual of TrigOm**: no rewriting frame with a nonzero state has a child `ψ_s(Ω_{ν+1})` whose state is a
cut of `Ω_{ν+1}` (5 集合でそのような枠は 0)。 -/
def TrigCut (N : Mat) (σ : Valn) : Prop :=
  ∀ i, i < N.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL N i = L ++ c :: R → ∀ s ν,
    σ.o c = psi s (psi (succ ν) z z) z → stB σ i L ≠ z →
    lt (stB σ i L) (psi (succ ν) z z) = true → lt (psi (σ.v i) z z) (psi s (psi (succ ν) z z) z) = true →
    stB σ i L ∉ cutsNS s (psi (succ ν) z z)

theorem ptrig_of_kind {a B s y : T} (hlt : lt B y = true)
    (hK : PH3cKind B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s)
    (hT : ∀ ν, y = psi (succ ν) z z → B ∉ cutsNS s y) : PTrig a B s y := by
  intro ν hyν
  have hy : app (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 = y := split_app _ y
  rcases hK with ⟨heq, _⟩ | ⟨_, ⟨R, _, hpre⟩ | ⟨_, hcut⟩⟩
  · exact ptrig_prefix (a := a) (s := s) hlt (Or.inr ⟨_, by rw [← heq, hy]⟩) ν hyν
  · exact ptrig_prefix (a := a) (s := s) hlt (Or.inr ⟨app R (split y (psi (succ s) z z)).2, by
      rw [← app_assoc, ← hpre]; exact hy.symm⟩) ν hyν
  · exfalso
    have hT' := hT ν hyν
    subst hyν
    by_cases hlo : (split (psi (succ ν) z z) (psi (succ s) z z)).2 = z
    · have hy' : (split (psi (succ ν) z z) (psi (succ s) z z)).1 = psi (succ ν) z z := by
        have h := hy; rw [hlo, app_z_right] at h; exact h
      rw [hy'] at hcut
      exact hT' hcut
    · -- a single summand with a nonzero low part has no high part
      have hhi : (split (psi (succ ν) z z) (psi (succ s) z z)).1 = z := by
        cases hh : (split (psi (succ ν) z z) (psi (succ s) z z)).1 with
        | z => rfl
        | psi a1 b1 c1 =>
          exfalso
          rw [hh] at hy
          simp only [app, psi.injEq] at hy
          exact hlo (app_eq_z hy.2.2).2
      rw [hhi] at hcut
      simp [cutsNS] at hcut

/-- **TrigOmC from PH3c** and the residual `TrigCut`. -/
theorem trigOmC_of_ph3c {N : Mat} {σ : Valn} (hC : Cons N σ) (hO : GoodOT N σ) (hP : PH3c N σ)
    (hT : TrigCut N σ) : TrigOmC N σ := by
  rw [← rwc_trig]
  refine rwc_of_cl (P := PTrig) hC hO ?_
  intro i hi L c R hcl s y hcy hlt htr
  by_cases hB : spArg (σ.v i) z (sumN (L.map σ.o)) = z
  · exact ptrig_prefix hlt (Or.inl hB)
  · refine ptrig_of_kind hlt (hP i hi L c R hcl s y hcy hB ⟨hlt, htr⟩) ?_
    intro ν hyν
    subst hyν
    exact hT i hi L c R hcl s ν hcy hB hlt htr

end Ytosk
