/-
**TP1C・TP1WC・TrigOmC を PH3cG（G3 の切り口）から導く（2026-10-12、drop-fix）。**

V3TP1Cut の G3 版。旧 PH3c は標準形で偽（closure、ext1 の t = 2 の M[2]）なので、こちらを使う。
G3 の切り口 `cutsHG` は「添字に入る（どの項でも）／Ω_s に替える・引数に入る・後ろへ進む（添字 ≥ s の項だけ）」。
帰納法は 1 組（`cutHG_ltG`・`cutNSG_ltG`、η 一般）で、葉の組 `HPairG`・`CPairG`（その段の項が Ω_k、状態の側が Ω_{t′}）
に二つの条件を残す:
- 後続の葉（k が後続）: Ω_{t′} < η。TP1（η = ψ_μ(1)、μ = holeLev y）では μ = init k（`cpairG_holeLev`）なので自動。
- 極限の葉（k が極限で穴を持ち、t′ = s）: s < fsD(k, η)。
-/
import Ytosk.V3TP1Cut
import Ytosk.V3PKindG

namespace Ytosk

open T

/-! ## 葉の組（G3） -/

/-- The leaf pairs of a G3 high cut: at a level `Ω_k` the state side is `Ω_{t′}`. -/
inductive HPairG (s : T) : T → T → T → T → Prop
  | top (t' k : T) : HPairG s (psi t' z z) (psi k z z) t' k
  | sub {t a t' k : T} : isSucc a = false → HPairG s t a t' k → HPairG s (psi t z z) (psi a z z) t' k
  | arg {b t w t' k : T} : HPairG s t w t' k → HPairG s (psi b t z) (psi b w z) t' k
  | rest {b w t c t' k : T} : HPairG s t c t' k → HPairG s (psi b w t) (psi b w c) t' k

/-- The leaf pairs of a G3 cut of `PH3cG`. -/
inductive CPairG (s : T) : T → T → T → T → Prop
  | top (t' k : T) : CPairG s (psi t' z z) (psi k z z) t' k
  | sub {t a t' k : T} : isSucc a = false → HPairG s t a t' k → CPairG s (psi t z z) (psi a z z) t' k
  | arg {a t x t' k : T} : HPairG s t x t' k → CPairG s (psi a t z) (psi a x z) t' k
  | rest {a x B c t' k : T} : CPairG s B c t' k → CPairG s (psi a x B) (psi a x c) t' k

theorem HPairG.ne_z {s t x t' k : T} (h : HPairG s t x t' k) : x ≠ z := by
  cases h <;> simp

theorem CPairG.ne_z {s t x t' k : T} (h : CPairG s t x t' k) : x ≠ z := by
  cases h <;> simp

/-- Along a leaf pair the hole level is that of the leaf. -/
theorem hpairG_holeLev {s : T} : ∀ {t x t' k : T}, HPairG s t x t' k → isSucc k = true → holeLev x = init k
  | _, _, _, _, .top _ _, hk => holeLev_om_succ hk
  | _, _, _, _, .sub ha h, hk => by rw [holeLev_om ha]; exact hpairG_holeLev h hk
  | _, _, _, _, .arg h, hk => by rw [holeLev_psi_arg h.ne_z]; exact hpairG_holeLev h hk
  | _, _, _, _, .rest h, hk => by rw [holeLev_rest_ne h.ne_z]; exact hpairG_holeLev h hk

theorem cpairG_holeLev {s : T} : ∀ {B y t' k : T}, CPairG s B y t' k → isSucc k = true → holeLev y = init k
  | _, _, _, _, .top _ _, hk => holeLev_om_succ hk
  | _, _, _, _, .sub ha h, hk => by rw [holeLev_om ha]; exact hpairG_holeLev h hk
  | _, _, _, _, .arg h, hk => by rw [holeLev_psi_arg h.ne_z]; exact hpairG_holeLev h hk
  | _, _, _, _, .rest h, hk => by rw [holeLev_rest_ne h.ne_z]; exact cpairG_holeLev h hk

/-! ## 帰納法 -/

section
variable {s η : T} (hη : η ≠ z)
include hη

/-- **G3 high cuts.** -/
theorem cutHG_ltG : ∀ {x t : T}, t ∈ cutsHG s x → t < x → OHole x →
    (∀ t' k, HPairG s t x t' k → isSucc k = true → t' < k → psi t' z z < η) →
    (∀ k, HPairG s t x s k → isSucc k = false → OHole k → s < k → s < fsD k η) →
    t < fsD x η
  | z, _, ht, _, _, _, _ => by simp [cutsHG] at ht
  | psi b w c, t, ht, hlt, hO, hS, hL => by
    rcases mem_cutsHG_psi.mp ht with ⟨hsb, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hsb, u, hu, rfl⟩ | ⟨hsb, u, hu, rfl⟩
    · -- `Ω_s` replaces the term
      have hsb' := le_of_le_bool hsb
      by_cases hc : c = z
      · subst hc
        by_cases hw : w = z
        · subst hw
          obtain ⟨hb0, hb⟩ := ohole_om hO
          have hsb2 := om_lt_om_inv hlt
          by_cases hbs : isSucc b = true
          · rw [fsD_leaf hbs hb0]; exact hS s b (HPairG.top s b) hbs hsb2
          · have hbs' : isSucc b = false := by simpa using hbs
            rw [fsD_sub hb0 hbs']
            exact psi_lt_psi_z_iff.mpr (Or.inl (hL b (HPairG.top s b) hbs' (hb.resolve_left hbs) hsb2))
        · obtain ⟨hws, hwO⟩ := ohole_arg hw hO
          rw [fsD_psi hw hws]
          exact lt_of_le_of_lt (psi_le_psi_z hsb') (om_lt_psi_arg (fsD_ne_z_oh hwO hη))
      · rw [fsD_rest hc]
        exact lt_of_le_of_lt (psi_le_psi_any hsb') (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) hη))
    · -- into the subscript: `Ω_u`, `u ∈ cutsHG s b`
      have hub := cutsHG_le hu
      by_cases hc : c = z
      · subst hc
        by_cases hw : w = z
        · subst hw
          obtain ⟨hb0, hb⟩ := ohole_om hO
          have hub2 := om_lt_om_inv hlt
          by_cases hbs : isSucc b = true
          · rw [fsD_leaf hbs hb0]; exact hS u b (HPairG.top u b) hbs hub2
          · have hbs' : isSucc b = false := by simpa using hbs
            rw [fsD_sub hb0 hbs']
            exact psi_lt_psi_z_iff.mpr (Or.inl (cutHG_ltG hu hub2 (hb.resolve_left hbs)
              (fun t' k hp => hS t' k (HPairG.sub hbs' hp)) (fun k hp => hL k (HPairG.sub hbs' hp))))
        · obtain ⟨hws, hwO⟩ := ohole_arg hw hO
          rw [fsD_psi hw hws]
          exact lt_of_le_of_lt (psi_le_psi_z hub) (om_lt_psi_arg (fsD_ne_z_oh hwO hη))
      · rw [fsD_rest hc]
        exact lt_of_le_of_lt (psi_le_psi_any hub) (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) hη))
    · -- into the argument
      by_cases hc : c = z
      · subst hc
        have hw : w ≠ z := by rintro rfl; simp [cutsHG] at hu
        obtain ⟨hws, hwO⟩ := ohole_arg hw hO
        rw [fsD_psi hw hws]
        have hult : u < w := by
          rw [psi_lt_psi_z_iff] at hlt
          rcases hlt with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact h
        exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, cutHG_ltG hu hult hwO
          (fun t' k hp => hS t' k (HPairG.arg hp)) (fun k hp => hL k (HPairG.arg hp))⟩)
      · rw [fsD_rest hc]
        exact lt_of_le_of_lt (psi_le_psi_arg (cutsHG_le hu)) (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) hη))
    · -- into the rest
      have hc : c ≠ z := by rintro rfl; simp [cutsHG] at hu
      rw [fsD_rest hc]
      have hult : u < c := by
        rw [T.psi_lt_psi] at hlt
        rcases hlt with h | ⟨_, h⟩ | ⟨_, _, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact absurd h (lt_irrefl' _)
        · exact h
      rw [T.psi_lt_psi]
      exact Or.inr (Or.inr ⟨rfl, rfl, cutHG_ltG hu hult (ohole_rest hc hO)
        (fun t' k hp => hS t' k (HPairG.rest hp)) (fun k hp => hL k (HPairG.rest hp))⟩)

/-- **The G3 cuts of `PH3cG`.** -/
theorem cutNSG_ltG : ∀ {h B : T}, B ∈ cutsNSG s h → B < h → OHole h →
    (∀ t' k, CPairG s B h t' k → isSucc k = true → t' < k → psi t' z z < η) →
    (∀ k, CPairG s B h s k → isSucc k = false → OHole k → s < k → s < fsD k η) →
    B < fsD h η
  | z, _, hB, _, _, _, _ => by simp [cutsNSG] at hB
  | psi a x c, B, hB, hlt, hO, hS, hL => by
    rcases mem_cutsNSG_psi.mp hB with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · -- `B = Ω_t`, `t ∈ cutsHG s a`
      have hta := cutsHG_le ht
      by_cases hc : c = z
      · subst hc
        by_cases hx : x = z
        · subst hx
          obtain ⟨ha0, ha⟩ := ohole_om hO
          have hta2 := om_lt_om_inv hlt
          by_cases has : isSucc a = true
          · rw [fsD_leaf has ha0]; exact hS t a (CPairG.top t a) has hta2
          · have has' : isSucc a = false := by simpa using has
            rw [fsD_sub ha0 has']
            exact psi_lt_psi_z_iff.mpr (Or.inl (cutHG_ltG hη ht hta2 (ha.resolve_left has)
              (fun t' k hp => hS t' k (CPairG.sub has' hp)) (fun k hp => hL k (CPairG.sub has' hp))))
        · obtain ⟨hxs, hxO⟩ := ohole_arg hx hO
          rw [fsD_psi hx hxs]
          exact lt_of_le_of_lt (psi_le_psi_z hta) (om_lt_psi_arg (fsD_ne_z_oh hxO hη))
      · rw [fsD_rest hc]
        exact lt_of_le_of_lt (psi_le_psi_any hta) (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) hη))
    · -- `B = ψ_a(t)`, `t ∈ cutsHG s x`
      by_cases hc : c = z
      · subst hc
        have hx : x ≠ z := by rintro rfl; simp [cutsHG] at ht
        obtain ⟨hxs, hxO⟩ := ohole_arg hx hO
        rw [fsD_psi hx hxs]
        have htx : t < x := by
          rw [psi_lt_psi_z_iff] at hlt
          rcases hlt with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact h
        exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, cutHG_ltG hη ht htx hxO
          (fun t' k hp => hS t' k (CPairG.arg hp)) (fun k hp => hL k (CPairG.arg hp))⟩)
      · rw [fsD_rest hc]
        exact lt_of_le_of_lt (psi_le_psi_arg (cutsHG_le ht)) (psi_lt_rest (fsD_ne_z_oh (ohole_rest hc hO) hη))
    · -- `B = ψ_a(x) + t`, `t ∈ cutsNSG s c`
      have hc : c ≠ z := by rintro rfl; simp [cutsNSG] at ht
      rw [fsD_rest hc]
      have htc : t < c := by
        rw [T.psi_lt_psi] at hlt
        rcases hlt with h | ⟨_, h⟩ | ⟨_, _, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact absurd h (lt_irrefl' _)
        · exact h
      rw [T.psi_lt_psi]
      exact Or.inr (Or.inr ⟨rfl, rfl, cutNSG_ltG ht htc (ohole_rest hc hO)
        (fun t' k hp => hS t' k (CPairG.rest hp)) (fun k hp => hL k (CPairG.rest hp))⟩)

end

/-! ## 枠の形 -/

/-- **The residual of TP1 (G3)**: the limit leaves of a cut (`s < fsD(k, η)`). -/
def TP1LeafG (N : Mat) (σ : Valn) : Prop :=
  ∀ i, i < N.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL N i = L ++ c :: R → ∀ s y,
    σ.o c = psi s y z → stB σ i L ≠ z →
    lt (stB σ i L) y = true → lt (psi (σ.v i) z z) (psi s y z) = true →
    (split y (psi (succ s) z z)).2 = z → OHole y →
    ∀ k, CPairG s (stB σ i L) y s k → isSucc k = false → OHole k → s < k → s < fsD k (psi (holeLev y) one z)

/-- **The residual of TP1W (G3)**: no successor leaf (`Ω_{t′} < 1` is impossible), and the limit leaves. -/
def TP1WLeafG (N : Mat) (σ : Valn) : Prop :=
  ∀ i, i < N.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL N i = L ++ c :: R → ∀ s y,
    σ.o c = psi s y z → stB σ i L ≠ z →
    lt (stB σ i L) y = true → lt (psi (σ.v i) z z) (psi s y z) = true →
    (split y (psi (succ s) z z)).2 = z → cof y = .omega → OHole y →
    (∀ t' k, CPairG s (stB σ i L) y t' k → isSucc k = true → t' < k → psi t' z z < one) ∧
    (∀ k, CPairG s (stB σ i L) y s k → isSucc k = false → OHole k → s < k → s < fsD k one)

/-- **The residual of TrigOm (G3)**. -/
def TrigCutG (N : Mat) (σ : Valn) : Prop :=
  ∀ i, i < N.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL N i = L ++ c :: R → ∀ s ν,
    σ.o c = psi s (psi (succ ν) z z) z → stB σ i L ≠ z →
    lt (stB σ i L) (psi (succ ν) z z) = true → lt (psi (σ.v i) z z) (psi s (psi (succ ν) z z) z) = true →
    stB σ i L ∉ cutsNSG s (psi (succ ν) z z)

/-- The shared part: the cut case with `lo = 0` reduced to `cutNSG_ltG`; the other kinds are prefixes or below
`hi`. -/
theorem lt_fsD_of_kindG {B s y η : T} (hη : η ≠ z) (hlt : lt B y = true) (hO : OHole y)
    (hK : PH3cKindG B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s)
    (hcut : (split y (psi (succ s) z z)).2 = z → B ∈ cutsNSG s y → B < fsD y η) :
    lt B (fsD y η) = true := by
  have hy : app (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 = y := split_app _ y
  rcases hK with ⟨heq, _⟩ | ⟨_, ⟨R, _, hpre⟩ | ⟨_, hc⟩⟩
  · exact prefix_fsD hlt (Or.inr ⟨_, by rw [← heq, hy]⟩) hO hη
  · exact prefix_fsD hlt (Or.inr ⟨app R (split y (psi (succ s) z z)).2, by
      rw [← app_assoc, ← hpre]; exact hy.symm⟩) hO hη
  · by_cases hlo : (split y (psi (succ s) z z)).2 = z
    · have hy' : (split y (psi (succ s) z z)).1 = y := by
        have h := hy; rw [hlo, app_z_right] at h; exact h
      rw [hy'] at hc
      exact hcut hlo hc
    · have hO' : OHole (app (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2) := by rw [hy]; exact hO
      have key : B < fsD (app (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2) η := by
        rw [fsD_app _ hlo]
        exact lt_of_le_of_lt (cutsNSG_le hc) (lt_app_of (fsD_ne_z_oh (ohole_app_inv0 hlo hO') hη))
      rw [hy] at key
      exact key

/-- **TP1C from PH3cG** and `TP1LeafG`. -/
theorem tp1C_of_ph3cG {N : Mat} {σ : Valn} (hC : Cons N σ) (hO : GoodOT N σ) (hP : PH3cG N σ)
    (hL : TP1LeafG N σ) : TP1C N σ := by
  rw [← rwc_tp1]
  refine rwc_of_cl (P := PTP1) hC hO ?_
  intro i hi L c R hcl s y hcy hlt htr
  by_cases hB : spArg (σ.v i) z (sumN (L.map σ.o)) = z
  · exact ptp1_prefix hlt (Or.inl hB)
  · intro hOy
    refine lt_fsD_of_kindG (by simp [one]) hlt hOy (hP i hi L c R hcl s y hcy hB ⟨hlt, htr⟩) ?_
    intro hlo hc
    refine cutNSG_ltG (by simp [one]) hc hlt hOy ?_ (hL i hi L c R hcl s y hcy hB hlt htr hlo hOy)
    intro t' k hp hk htk
    apply om_lt_eta
    rw [cpairG_holeLev hp hk, ← lt_succ_iff, show succ (init k) = app (init k) one from rfl, init_app_one hk]
    exact htk

/-- **TP1WC from PH3cG** and `TP1WLeafG`. -/
theorem tp1WC_of_ph3cG {N : Mat} {σ : Valn} (hC : Cons N σ) (hO : GoodOT N σ) (hP : PH3cG N σ)
    (hL : TP1WLeafG N σ) : TP1WC N σ := by
  rw [← rwc_tp1w]
  refine rwc_of_cl (P := PTP1W) hC hO ?_
  intro i hi L c R hcl s y hcy hlt htr
  by_cases hB : spArg (σ.v i) z (sumN (L.map σ.o)) = z
  · exact ptp1w_prefix hlt (Or.inl hB)
  · intro hcof hOy
    refine lt_fsD_of_kindG (by simp [one]) hlt hOy (hP i hi L c R hcl s y hcy hB ⟨hlt, htr⟩) ?_
    intro hlo hc
    obtain ⟨h1, h2⟩ := hL i hi L c R hcl s y hcy hB hlt htr hlo hcof hOy
    exact cutNSG_ltG (by simp [one]) hc hlt hOy h1 h2

theorem ptrig_of_kindG {a B s y : T} (hlt : lt B y = true)
    (hK : PH3cKindG B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s)
    (hT : ∀ ν, y = psi (succ ν) z z → B ∉ cutsNSG s y) : PTrig a B s y := by
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
    · have hhi : (split (psi (succ ν) z z) (psi (succ s) z z)).1 = z := by
        cases hh : (split (psi (succ ν) z z) (psi (succ s) z z)).1 with
        | z => rfl
        | psi a1 b1 c1 =>
          exfalso
          rw [hh] at hy
          simp only [app, psi.injEq] at hy
          exact hlo (app_eq_z hy.2.2).2
      rw [hhi] at hcut
      simp [cutsNSG] at hcut

/-- **TrigOmC from PH3cG** and `TrigCutG`. -/
theorem trigOmC_of_ph3cG {N : Mat} {σ : Valn} (hC : Cons N σ) (hO : GoodOT N σ) (hP : PH3cG N σ)
    (hT : TrigCutG N σ) : TrigOmC N σ := by
  rw [← rwc_trig]
  refine rwc_of_cl (P := PTrig) hC hO ?_
  intro i hi L c R hcl s y hcy hlt htr
  by_cases hB : spArg (σ.v i) z (sumN (L.map σ.o)) = z
  · exact ptrig_prefix hlt (Or.inl hB)
  · refine ptrig_of_kindG hlt (hP i hi L c R hcl s y hcy hB ⟨hlt, htr⟩) ?_
    intro ν hyν
    subst hyν
    exact hT i hi L c R hcl s ν hcy hB hlt htr

end Ytosk
