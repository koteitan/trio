/-
**落とす補題の関係: ◁ と弱い関係。**

崩れの節点の値 w′ は、成分がすべて Ω_1 より下（`CS`）で 1 以上。
- v の関係 `DRelV`: w′ ⊴ w か、弱い関係 `WkV`（w′ < w、`CS w′`、1 ≤ w′）。
- o の関係 `DRelO`: ⊴ か、ψ_{w′}(0) と ψ_w(X) で `WkV w′ w`。
弱い子 ψ_{w′}(0) は自分の成分を自分で押さえる（`self_small_weak`）ので、親で ⊴ に戻る（`lhd_weak_child`）。
-/
import Ytosk.V3DropAsm
import Ytosk.V3NodeLhd

namespace Ytosk

open T

/-- All components are countable. -/
def CS (t : T) : Prop := ∀ g ∈ comps z t, g < Om one

/-- The weak relation of subscripts. -/
def WkV (w' w : T) : Prop := w' < w ∧ CS w' ∧ one ≤ w' ∧ isOT w' = true

def DRelV (w' w : T) : Prop := LhdE w' w ∨ WkV w' w

def WkO (t' t : T) : Prop := ∃ w' w X, t' = psi w' z z ∧ t = psi w X z ∧ WkV w' w

def DRelO (t' t : T) : Prop := LhdE t' t ∨ WkO t' t

/-- Components at a level are among the components at level `0`. -/
theorem comps_sub_z (u : T) : ∀ t, ∀ g ∈ comps u t, g ∈ comps z t
  | z, g, hg => by simp [comps] at hg
  | psi v b c, g, hg => by
    simp only [comps, List.mem_append] at hg ⊢
    rcases hg with hg | hg
    · left
      split at hg
      · simp at hg
      · rw [if_neg (by simp [lt])]
        simp only [List.mem_cons, List.mem_append] at hg ⊢
        rcases hg with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (comps_sub_z u b g h))
        · exact Or.inr (Or.inr (comps_sub_z u v g h))
    · exact Or.inr (comps_sub_z u c g hg)

theorem Om_one_le_psi {w : T} (hw : one ≤ w) : Om one ≤ psi w z z := by
  unfold Om
  rcases (le_iff _ _).mp hw with h | h
  · left
    show psi one z z < psi w z z
    rw [psi_lt_psi_z_iff]; exact Or.inl h
  · right; rw [h]

/-- **A weak child dominates its own components.** -/
theorem self_small_weak {w' : T} (hcs : CS w') (h1 : one ≤ w') :
    ∀ u, ∀ g ∈ comps u (psi w' z z), g ≤ psi w' z z := by
  intro u g hg
  have hg0 := comps_sub_z u _ g hg
  simp only [comps, List.mem_append] at hg0
  rw [if_neg (by simp [lt])] at hg0
  simp only [List.mem_cons, List.mem_append] at hg0
  rcases hg0 with (rfl | h | h) | h
  · exact z_le _
  · simp at h
  · exact le_of_lt (lt_of_lt_of_le (hcs g h) (Om_one_le_psi h1))
  · simp at h

/-- **`o` from `v`**: `ψ_{v′}(0)` against `ψ_v(X)`. -/
theorem drelO_of_v {v' v X : T} (h : DRelV v' v) : DRelO (psi v' z z) (psi v X z) := by
  rcases h with h | h
  · exact Or.inl (lhdE_oq_v h)
  · exact Or.inr ⟨v', v, X, rfl, rfl, h⟩

/-- A single summand is at most a sum ending with it, when the earlier summands are at least it. -/
theorem le_app_of_ge {s y : T} : ∀ (B : T), (∀ q ∈ summands B, psi s y z ≤ q) → psi s y z ≤ app B (psi s y z)
  | z, _ => by simp
  | psi a b c, h => by
    have hh := h (psi a b z) (by simp [summands])
    rcases (le_iff _ _).mp hh with hlt | heq
    · left
      rw [psi_lt_psi_z_iff] at hlt
      show psi s y z < psi a b (app c (psi s y z))
      rw [T.psi_lt_psi]
      rcases hlt with h1 | ⟨rfl, h1⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨rfl, h1⟩)
    · simp only [psi.injEq] at heq
      obtain ⟨rfl, rfl, -⟩ := heq
      exact psi_le_psi_rest (z_le _)

/-- **The `o` frame with a weak last child**: the new child is `ψ_{w′}(0)` (no rewrite), the relation
of the old side to the state without the child (`hdrop`) is a hypothesis. -/
theorem o_frame_weak {a w' w F : T} {L : List T}
    (hs' : ∀ t ∈ L ++ [psi w' z z], Single t) (hp' : (L ++ [psi w' z z]).Pairwise (fun a b => b ≤ a))
    (hW : WkV w' w) (hdrop : LhdE (psi a (spArg a z (sumN L)) z) (psi a F z))
    (hlt : app (spArg a z (sumN L)) (psi w' z z) < F) :
    LhdE (psi a (spArg a z (sumN (L ++ [psi w' z z]))) z) (psi a F z) := by
  set B := spArg a z (sumN L) with hB
  have hc : Single (psi w' z z) := hs' _ (by simp)
  have e2 : sumN (L ++ [psi w' z z]) = app (sumN L) (psi w' z z) := by
    rw [sumN_append_dec hs' hp']
    congr 1
    show sf (add z (psi w' z z)) = psi w' z z
    rw [add_z_left]; exact sf_ot hc.1
  have hL := sumN_dec L (fun t ht => hs' t (List.mem_append_left _ ht)) (List.pairwise_append.mp hp').1
  have hBge : ∀ q ∈ summands B, psi w' z z ≤ q := by
    apply spArg_summands_ge ⟨w', z, rfl⟩ (sumN L) z hL.1
    · rw [hL.2]; intro q hq
      exact (List.pairwise_append.mp hp').2.2 q hq _ (by simp)
    · simp [summands]
  have estep : spArg a z (sumN (L ++ [psi w' z z])) = app B (psi w' z z) := by
    rw [e2, spArg_app, spArg_single, step_leaf, ← hB]
    exact add_eq_app_of_ge ⟨w', z, rfl⟩ B hBge
  have hBlt : B < app B (psi w' z z) := by
    have := app_lt_app_left B (show z < psi w' z z from T.z_lt_psi _ _ _)
    rwa [app_z_right] at this
  rw [estep]
  right
  rcases hdrop with he | hl
  · exfalso
    simp only [psi.injEq] at he
    have := lt_trans hBlt hlt
    rw [he.2.1] at this; exact lt_irrefl' _ this
  · exact lhd_weak_child hl (by simp)
      (fun u g hg => le_trans (self_small_weak hW.2.1 hW.2.2.1 u g hg) (le_app_of_ge B hBge)) hlt

/-! ## 評価器の段の o の枠 (1): v が変わる列 -/

theorem sumN_all_z : ∀ (l : List T), (∀ t ∈ l, t = z) → sumN l = z := by
  intro l h
  unfold sumN
  suffices ∀ acc, acc = z → l.foldl (fun a b => sf (add a b)) acc = z by exact this z rfl
  induction l with
  | nil => intro acc h0; simpa using h0
  | cons t l ih =>
    intro acc h0
    simp only [List.foldl_cons]
    apply ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
    rw [h0, h t List.mem_cons_self]; rfl

/-- **A column with no counted child**: `o = ψ_v(0)`. -/
theorem o_of_no_counted {M : Mat} {ρ : Valn} {i : Nat} (hC : Cons M ρ) (hi : i < M.length)
    (hv : isOT (ρ.v i) = true) (hn : ∀ c ∈ children M i, ¬ Counted M i c) : ρ.o i = psi (ρ.v i) z z := by
  classical
  rw [(hC i hi).1]
  unfold oRhs
  rw [sumN_all_z _ (fun t ht => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    rw [cnt_eq_ite, if_neg (hn c hc)])]
  rw [sf_psi_spArg hv rfl]
  rfl

/-- **The `o` frame where `v` changes**: no counted child in `M.take x`, so `o′ = ψ_{v′}(0)`. -/
theorem o_frame_vchg {M : Mat} {x : Nat} {ρ ρ' : Valn} {i : Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hix : i < (M.take x).length) (hiM : i < M.length)
    (hv' : isOT (ρ'.v i) = true) (hT : ∀ c ∈ children (M.take x) i, ¬ Counted (M.take x) i c)
    (hrel : DRelV (ρ'.v i) (ρ.v i)) : DRelO (ρ'.o i) (ρ.o i) := by
  rw [o_of_no_counted hC' hix hv' hT, o_spArg hC hG hiM]
  exact drelO_of_v hrel

/-! ## 末尾の子を外す -/

/-- Closedness of each state of a tail where the next summand rewrites. -/
def TailCl (a : T) : T → List T → Prop
  | _, [] => True
  | X, t :: Tl => (∀ s y, t = psi s y z → lt X y = true ∧ lt (psi a z z) (psi s y z) = true → Closed a X) ∧
      TailCl a (spArg a X t) Tl

theorem sumN_cons_dec {t : T} {l : List T} (hs : ∀ u ∈ t :: l, Single u)
    (hp : (t :: l).Pairwise (fun a b => b ≤ a)) : sumN (t :: l) = app t (sumN l) := by
  have := sumN_append_dec (L1 := [t]) (L2 := l) hs hp
  rw [show [t] ++ l = t :: l from rfl] at this
  rw [this]
  congr 1
  show sf (add z t) = t
  rw [add_z_left]; exact sf_ot (hs t (by simp)).1

/-- **Dropping a tail of children**: `ψ_a(X) ⊴ ψ_a(spArg a X (sum of the tail))`. -/
theorem drop_tail (a : T) : ∀ (Tl : List T) (X : T), (∀ u ∈ Tl, Single u) →
    Tl.Pairwise (fun a b => b ≤ a) → (∀ u ∈ Tl, ∀ q ∈ summands X, u ≤ q) → TailCl a X Tl →
    LhdE (psi a X z) (psi a (spArg a X (sumN Tl)) z)
  | [], X, _, _, _, _ => by simp [sumN, spArg]; exact Or.inl rfl
  | t :: Tl, X, hs, hp, hX, hcl => by
    obtain ⟨s, y, rfl⟩ := (hs _ List.mem_cons_self).2
    have hc := (hs _ List.mem_cons_self).1
    rw [sumN_cons_dec hs hp, show app (psi s y z) (sumN Tl) = psi s y (sumN Tl) from rfl, spArg_cons,
      step_rest a X s y (sumN Tl) z]
    have h1 := drop_child_lhd hc (hX _ List.mem_cons_self) (hcl.1 s y rfl)
    have hTl := (List.pairwise_cons.mp hp)
    have hsT : ∀ u ∈ Tl, Single u := fun u hu => hs u (List.mem_cons_of_mem _ hu)
    have hX' : ∀ u ∈ Tl, ∀ q ∈ summands (step a X s y z), u ≤ q := by
      intro u hu
      obtain ⟨s2, y2, hu2⟩ := (hsT u hu).2
      have := spArg_summands_ge (a := a) (c := u) ⟨s2, y2, hu2⟩ (psi s y z) X hc
        (by intro q hq; simp [summands] at hq; rw [hq]; exact hTl.1 u hu)
        (fun q hq => le_trans (hTl.1 u hu) (hX _ List.mem_cons_self q hq))
      simpa [spArg_single] using this
    have h2 := drop_tail a Tl (step a X s y z) hsT hTl.2 hX' (by simpa [spArg_single] using hcl.2)
    exact LhdE.trans h1 h2

/-! ## 値の不変条件: 書き換える枠の状態は閉じている -/

/-- **Value invariant**: in every frame of `M` where the counted child rewrites the state, the state is
closed at the levels `≤ v(i)`. -/
def FrameClosed (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL M i = L ++ c :: R → ∀ s y,
    ρ.o c = psi s y z →
    lt (spArg (ρ.v i) z (sumN (L.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
    Closed (ρ.v i) (spArg (ρ.v i) z (sumN (L.map ρ.o)))

theorem cl_mem_children {M : Mat} {i c : Nat} (h : c ∈ CL M i) : c ∈ children M i := by
  unfold CL at h; exact (List.mem_filter.mp h).1

/-- The counted values in order are single and non-increasing. -/
theorem cl_vals {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {i : Nat} (hi : i < M.length) :
    (∀ t ∈ (CL M i).map ρ.o, Single t) ∧ ((CL M i).map ρ.o).Pairwise (fun a b => b ≤ a) := by
  rw [← cvals_eq_map hC hG i]
  exact ⟨cvals_single hC hG i, hG.dec i hi⟩

/-- **The tail closedness from the invariant.** -/
theorem tailcl_of_frame {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (hF : FrameClosed M ρ)
    {i : Nat} (hi : i < M.length) :
    ∀ (Tl P : List Nat), CL M i = P ++ Tl →
      TailCl (ρ.v i) (spArg (ρ.v i) z (sumN (P.map ρ.o))) (Tl.map ρ.o)
  | [], _, _ => trivial
  | c :: Tl, P, h => by
    refine ⟨fun s y hc ht => hF i hi P c Tl h s y hc ht, ?_⟩
    obtain ⟨hs, hp⟩ := cl_vals hC hG hi
    rw [h] at hs hp
    have hs' : ∀ t ∈ P.map ρ.o ++ [ρ.o c], Single t := fun t ht => hs t (by
      simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at ht ⊢
      rcases ht with ht | ht
      · exact Or.inl ht
      · simp at ht; exact Or.inr (Or.inl ht))
    have hp' : (P.map ρ.o ++ [ρ.o c]).Pairwise (fun a b => b ≤ a) := by
      rw [List.map_append, List.map_cons] at hp
      have := List.pairwise_append.mp hp
      refine List.pairwise_append.mpr ⟨this.1, by simp, fun a ha b hb => ?_⟩
      simp at hb; rw [hb]; exact this.2.2 a ha _ List.mem_cons_self
    have e : spArg (ρ.v i) (spArg (ρ.v i) z (sumN (P.map ρ.o))) (ρ.o c) =
        spArg (ρ.v i) z (sumN ((P ++ [c]).map ρ.o)) := by
      rw [List.map_append, List.map_singleton, sumN_append_dec hs' hp', spArg_app]
      congr 1
      show ρ.o c = sf (add z (ρ.o c))
      rw [add_z_left]; exact (sf_ot (hs' _ (by simp)).1).symm
    rw [e]
    exact tailcl_of_frame hC hG hF hi Tl (P ++ [c]) (by rw [h]; simp)

/-! ## 評価器の段の o の枠 (2): v が変わらない列 -/

/-- `o` through the counted children, with local hypotheses. -/
theorem o_cl_loc {M : Mat} {ρ : Valn} {i : Nat} (hC : Cons M ρ) (hi : i < M.length)
    (hv : isOT (ρ.v i) = true) (hs : ∀ c ∈ CL M i, Single (ρ.o c))
    (hp : ((CL M i).map ρ.o).Pairwise (fun a b => b ≤ a)) :
    ρ.o i = psi (ρ.v i) (spArg (ρ.v i) z (sumN ((CL M i).map ρ.o))) z := by
  classical
  have hcv : cvals M ρ i = (CL M i).map ρ.o := by
    unfold cvals CL
    have : (children M i).map (cnt M ρ i) =
        (children M i).map (fun c => if Counted M i c then ρ.o c else z) := by
      apply List.map_congr_left; intro c _; exact cnt_eq_ite M ρ i c
    rw [this]
    apply nzs_map_ite
    intro c hc hcnt
    exact single_ne_z (hs c (by unfold CL; exact List.mem_filter.mpr ⟨hc, by simpa using hcnt⟩))
  have hsl : ∀ t ∈ (children M i).map (cnt M ρ i), t = z ∨ Single t := by
    intro t ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    rw [cnt_eq_ite]
    split
    · rename_i hcnt
      exact Or.inr (hs c (by unfold CL; exact List.mem_filter.mpr ⟨hc, by simpa using hcnt⟩))
    · exact Or.inl rfl
  have := o_spArg_loc hC hi hv hsl (by rw [hcv]; exact hp)
  rw [this, hcv]

theorem DRelO.le {t' t : T} (h : DRelO t' t) : t' ≤ t := by
  rcases h with h | ⟨w', w, X, rfl, rfl, hW⟩
  · exact h.le
  · left; show psi w' z z < psi w X z; rw [psi_lt_psi_z_iff]; exact Or.inl hW.1

theorem sumN_singleton {t : T} (h : Single t) : sumN [t] = t := by
  show sf (add z t) = t
  rw [add_z_left]; exact sf_ot h.1

/-- **The `o` frame where `v` does not change**: the counted children of `M.take x` are those of `M`
up to a tail, and only the last one changes. -/
theorem o_frame_eval {M : Mat} {x : Nat} {ρ ρ' : Valn} {i cs : Nat} {Lc Tl : List Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hF : FrameClosed M ρ)
    (hC' : Cons (M.take x) ρ') (hiT : i < (M.take x).length) (hiM : i < M.length)
    (hv : ρ'.v i = ρ.v i)
    (hclT : CL (M.take x) i = Lc ++ [cs]) (hcl : CL M i = Lc ++ [cs] ++ Tl)
    (hsame : ∀ d ∈ Lc, ρ'.o d = ρ.o d)
    (hcs' : Single (ρ'.o cs))
    (hrel : LhdE (ρ'.o cs) (ρ.o cs) ∨ (WkO (ρ'.o cs) (ρ.o cs) ∧ ∃ w, ρ.o cs = psi w z z))
    (hsub : ∀ s y, ρ.o cs = psi s y z →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
      SubSmall (ρ.v i) s)
    (hsub' : ∀ s y s' y', ρ.o cs = psi s y z → ρ'.o cs = psi s' y' z →
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s' y' z) = true) ∨
      (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
      SubSmall (ρ.v i) s') :
    LhdE (ρ'.o i) (ρ.o i) := by
  set a := ρ.v i with ha
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
  rw [hcl] at hsM hpM
  simp only [List.map_append, List.map_cons, List.map_nil] at hsM hpM
  set Lv := Lc.map ρ.o with hLv
  set Tv := Tl.map ρ.o with hTv
  have hsL : ∀ t ∈ Lv, Single t := fun t ht => hsM t (by simp [ht])
  have hcsS : Single (ρ.o cs) := hsM _ (by simp)
  have hsT : ∀ t ∈ Tv, Single t := fun t ht => hsM t (by simp [ht])
  have hp1 := List.pairwise_append.mp hpM
  have hpL : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp1.1).1
  have hLc : ∀ t ∈ Lv, ρ.o cs ≤ t := fun t ht =>
    (List.pairwise_append.mp hp1.1).2.2 t ht _ (by simp)
  have hpcT : (ρ.o cs :: Tv).Pairwise (fun a b => b ≤ a) := by
    refine List.pairwise_cons.mpr ⟨fun t ht => hp1.2.2 _ (by simp) t ht, hp1.2.1⟩
  have hsC : ∀ t ∈ ρ.o cs :: Tv, Single t := fun t ht => by
    rcases List.mem_cons.mp ht with h | h
    · rw [h]; exact hcsS
    · exact hsT t h
  have hLC : ∀ u ∈ ρ.o cs :: Tv, u ≤ ρ.o cs := fun u hu => by
    rcases List.mem_cons.mp hu with h | h
    · rw [h]
    · exact hp1.2.2 _ (by simp) u h
  have hsLc : ∀ t ∈ Lv ++ [ρ.o cs], Single t := fun t ht => by
    rcases List.mem_append.mp ht with h | h
    · exact hsL t h
    · simp at h; rw [h]; exact hcsS
  have hpLc : (Lv ++ [ρ.o cs]).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_append.mpr ⟨hpL, by simp, fun t ht b hb => by simp at hb; rw [hb]; exact hLc t ht⟩
  -- the value in `M.take x`
  have hmapT : (CL (M.take x) i).map ρ'.o = Lv ++ [ρ'.o cs] := by
    rw [hclT, List.map_append, List.map_singleton, hLv]
    congr 1
    exact List.map_congr_left hsame
  have hle' : ρ'.o cs ≤ ρ.o cs := by
    rcases hrel with h | ⟨h, _⟩
    · exact h.le
    · exact DRelO.le (Or.inr h)
  have hs' : ∀ t ∈ Lv ++ [ρ'.o cs], Single t := by
    intro t ht; rcases List.mem_append.mp ht with ht | ht
    · exact hsL t ht
    · simp at ht; rw [ht]; exact hcs'
  have hp' : (Lv ++ [ρ'.o cs]).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_append.mpr ⟨hpL, by simp, fun t ht b hb => by
      simp at hb; rw [hb]; exact le_trans hle' (hLc t ht)⟩
  have hvot : isOT a = true := hG.ot_v i hiM
  have ho' : ρ'.o i = psi a (spArg a z (sumN (Lv ++ [ρ'.o cs]))) z := by
    have := o_cl_loc hC' hiT (by rw [hv]; exact hvot)
      (fun c hc => by
        have : ρ'.o c ∈ (CL (M.take x) i).map ρ'.o := List.mem_map_of_mem hc
        rw [hmapT] at this; exact hs' _ this)
      (by rw [hmapT]; exact hp')
    rw [this, hmapT, hv]
  have ho : ρ.o i = psi a (spArg a z (sumN (Lv ++ [ρ.o cs] ++ Tv))) z := by
    rw [o_spArg hC hG hiM, cvals_eq_map hC hG i, hcl]
    simp only [List.map_append, List.map_singleton]
    rfl
  rw [ho', ho]
  set B := spArg a z (sumN Lv) with hB
  have hLs := sumN_dec Lv hsL hpL
  -- the state before `cs` is above the children
  have hBge : ∀ t, Single t → t ≤ ρ.o cs → ∀ q ∈ summands B, t ≤ q := by
    intro t ht htc
    obtain ⟨s0, y0, rfl⟩ := ht.2
    apply spArg_summands_ge ⟨s0, y0, rfl⟩ (sumN Lv) z hLs.1
    · rw [hLs.2]; intro q hq; exact le_trans htc (hLc q hq)
    · simp [summands]
  have hCL : CL M i = Lc ++ cs :: Tl := by rw [hcl]; simp
  obtain ⟨s, y, hsy⟩ := hcsS.2
  rcases hrel with hrel | hW
  · -- `⊴` child: one frame, then the tail
    obtain ⟨s', y', hs'y'⟩ := hcs'.2
    rw [hsy, hs'y'] at hrel
    have hc := hcsS.1; rw [hsy] at hc
    have hc' := hcs'.1; rw [hs'y'] at hc'
    have hN := node_lhd (a := a) (B := B) hc hc' hrel (hBge _ hcsS (le_refl _) |> fun h => by
        rw [hsy] at h; exact h) (hsub s y hsy) (hsub' s y s' y' hsy hs'y')
      (fun _ hr => hF i hiM Lc cs Tl hCL s y hsy hr)
    have hstate : spArg a z (sumN ((Lc ++ [cs]).map ρ.o)) = step a B s y z := by
      rw [List.map_append, List.map_singleton, ← hLv, sumN_append_dec hsLc hpLc,
        sumN_singleton hcsS, spArg_app, hsy, spArg_single]
    have hTcl := tailcl_of_frame hC hG hF hiM Tl (Lc ++ [cs]) (by rw [hcl])
    rw [hstate] at hTcl
    have hT := drop_tail a Tv (step a B s y z) hsT hp1.2.1
      (fun u hu q hq => by
        obtain ⟨s2, y2, hu2⟩ := (hsT u hu).2
        have := spArg_summands_ge (a := a) (c := u) ⟨s2, y2, hu2⟩ (psi s y z) B hc
          (by intro q2 hq2; simp [summands] at hq2; rw [hq2, ← hsy]; exact hp1.2.2 _ (by simp) u hu)
          (hBge u (hsT u hu) (hp1.2.2 _ (by simp) u hu))
        rw [spArg_single] at this
        exact this q hq) hTcl
    rw [hsy, hs'y']
    rw [hs'y'] at hs' hp'
    rw [hsy] at hsM hpM
    exact o_frame_term (L := Lv) (Tl := Tv) hsM hpM hs' hp' hN hT
  · -- weak child
    obtain ⟨⟨w', w, X, hw', hw, hWk⟩, w0, hw0⟩ := hW
    rw [hw] at hw0; simp only [psi.injEq] at hw0; obtain ⟨rfl, rfl, -⟩ := hw0
    have hF' : spArg a z (sumN (Lv ++ [ρ.o cs] ++ Tv)) = spArg a B (sumN (ρ.o cs :: Tv)) := by
      rw [List.append_assoc, show [ρ.o cs] ++ Tv = ρ.o cs :: Tv from rfl,
        sumN_append_dec (fun t ht => hsM t (by simpa using ht)) (by simpa using hpM), spArg_app]
    rw [hF']
    have hTcl := tailcl_of_frame hC hG hF hiM (cs :: Tl) Lc (by rw [hCL])
    have hdrop := drop_tail a (ρ.o cs :: Tv) B hsC hpcT
      (fun u hu q hq => hBge u (hsC u hu) (hLC u hu) q hq) (by simpa using hTcl)
    -- the old state after `cs` is `B + ψ_w(0)`, and the rest only grows
    have hstep : spArg a B (ρ.o cs) = app B (psi w z z) := by
      rw [hw, spArg_single, step_leaf]
      exact add_eq_app_of_ge ⟨w, z, rfl⟩ B (hBge _ hcsS (le_refl _) |> fun h => by rw [hw] at h; exact h)
    have hTcl2 := tailcl_of_frame hC hG hF hiM Tl (Lc ++ [cs]) (by rw [hcl])
    have hgrow : app B (psi w z z) ≤ spArg a B (sumN (ρ.o cs :: Tv)) := by
      have e : spArg a B (sumN (ρ.o cs :: Tv)) = spArg a (app B (psi w z z)) (sumN Tv) := by
        rw [sumN_cons_dec hsC hpcT, hw,
          show app (psi w z z) (sumN Tv) = psi w z (sumN Tv) from rfl, spArg_cons, step_rest a B w z (sumN Tv) z,
          step_leaf, add_eq_app_of_ge ⟨w, z, rfl⟩ B (hBge _ hcsS (le_refl _) |> fun h => by rw [hw] at h; exact h)]
      have hs2 : spArg a z (sumN ((Lc ++ [cs]).map ρ.o)) = app B (psi w z z) := by
        rw [List.map_append, List.map_singleton, ← hLv, sumN_append_dec hsLc hpLc,
          sumN_singleton hcsS, spArg_app, hstep]
      rw [hs2] at hTcl2
      have hd := drop_tail a Tv (app B (psi w z z)) hsT hp1.2.1
        (fun u hu q hq => by
          obtain ⟨s2, y2, hu2⟩ := (hsT u hu).2
          have hcw : isOT (psi w z z) = true := by rw [← hw]; exact hcsS.1
          have := spArg_summands_ge (a := a) (c := u) ⟨s2, y2, hu2⟩ (psi w z z) B hcw
            (by intro q2 hq2; simp [summands] at hq2; rw [hq2, ← hw]; exact hp1.2.2 _ (by simp) u hu)
            (hBge u (hsT u hu) (hp1.2.2 _ (by simp) u hu))
          rw [spArg_single, step_leaf, add_eq_app_of_ge ⟨w, z, rfl⟩ B
            (hBge _ hcsS (le_refl _) |> fun h => by rw [hw] at h; exact h)] at this
          exact this q hq) hTcl2
      rw [e]
      clear e
      have := hd.le
      rcases (le_iff _ _).mp this with h | h
      · rw [psi_lt_psi_z_iff] at h
        rcases h with h | ⟨_, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact le_of_lt h
      · simp only [psi.injEq] at h; exact (le_iff _ _).mpr (Or.inr h.2.1)
    have hlt : app B (psi w' z z) < spArg a B (sumN (ρ.o cs :: Tv)) := by
      apply lt_of_lt_of_le _ hgrow
      apply app_lt_app_left
      rw [psi_lt_psi_z_iff]; exact Or.inl hWk.1
    rw [hw'] at hs' hp'
    rw [hw']
    exact o_frame_weak hs' hp' hWk hdrop hlt

/-- **The `o` frame with no counted child in `M.take x`** (`v` unchanged): all counted children of `M` are
dropped. -/
theorem o_frame_empty {M : Mat} {x : Nat} {ρ ρ' : Valn} {i : Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hF : FrameClosed M ρ)
    (hC' : Cons (M.take x) ρ') (hiT : i < (M.take x).length) (hiM : i < M.length)
    (hv : ρ'.v i = ρ.v i) (hclT : CL (M.take x) i = []) : LhdE (ρ'.o i) (ρ.o i) := by
  have hvot : isOT (ρ.v i) = true := hG.ot_v i hiM
  have hn : ∀ c ∈ children (M.take x) i, ¬ Counted (M.take x) i c := by
    intro c hc hcnt
    have : c ∈ CL (M.take x) i := by unfold CL; exact List.mem_filter.mpr ⟨hc, by simpa using hcnt⟩
    rw [hclT] at this; simp at this
  rw [o_of_no_counted hC' hiT (by rw [hv]; exact hvot) hn, hv, o_spArg hC hG hiM, cvals_eq_map hC hG i]
  obtain ⟨hs, hp⟩ := cl_vals hC hG hiM
  have hTcl := tailcl_of_frame hC hG hF hiM (CL M i) [] (by simp)
  simp only [List.map_nil] at hTcl
  have h := drop_tail (ρ.v i) ((CL M i).map ρ.o) (spArg (ρ.v i) z (sumN [])) hs hp
    (fun u _ q hq => by simp [sumN, spArg, summands] at hq) hTcl
  simpa [sumN, spArg] using h

/-! ## v の枠 (1): 上げ -/

theorem last_add_single {s y : T} : ∀ V : T, last (add V (psi s y z)) = psi s y z
  | z => by simp [last]
  | psi a b c => by
    rw [add_psi_psi]
    split
    · simp [last]
    · have ih := last_add_single (s := s) (y := y) c
      have hne : add c (psi s y z) ≠ z := by
        intro h; rw [h] at ih; simp [last] at ih
      cases hc : add c (psi s y z) with
      | z => exact absurd hc hne
      | psi a' b' c' => simp only [last]; rw [← hc]; exact ih

/-- **An upgraded column has the value of its target**: `v(i) = v(k)` when `upg(i) = k`. -/
theorem v_upg_eq {M : Mat} {ρ : Valn} {i k : Nat} (hC : Cons M ρ) (hiM : i < M.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i = 0) (hu : upg M i = some k)
    (hVot : isOT (vOpt ρ (par M 1 i)) = true)
    (hoot : ∀ j ∈ children M k, col M j = bump M k → ∀ k' ∈ children M j, isOT (ρ.o k') = true) :
    ρ.v i = ρ.v k := by
  have hk := upg_lt hiM hu
  obtain ⟨m, hm1, hm2, hcol, _⟩ := upg_spec hu
  have hk1 : entry M 1 k ≠ 0 := by
    have : entry M 1 k = (col M k).2.1 := rfl
    rw [this, hcol]; exact h1
  have hk2 : entry M 2 k ≠ 0 := by
    have : entry M 2 k = (col M k).2.2 := rfl
    rw [this, hcol]; simp
  have hV : vOpt ρ (par M 1 k) = vOpt ρ (par M 1 i) := by rw [hm1, hm2]
  set W := omega (sumN (one :: (children M k).map (bumpTerm M ρ k))) with hW
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
  have hWot : isOT W = true := isOT_omega hY
  obtain ⟨sW, yW, hWf⟩ := (single_omega hY).2
  have hvk : ρ.v k = add (vOpt ρ (par M 1 i)) W := by
    rw [(hC k hk).2]; unfold vRhs
    rw [if_neg hk1, if_neg hk2, hV, ← hW, sf_ot (isOT_add hVot hWot)]
  rw [(hC i hiM).2]; unfold vRhs
  rw [if_neg h1, if_pos h2, hu]
  simp only
  rw [hvk]
  have hl : last (add (vOpt ρ (par M 1 i)) W) = W := by
    have hWf' : W = psi sW yW z := hWf
    rw [hWf']; exact last_add_single _
  rw [hl, sf_ot (isOT_add hVot hWot)]

/-- **The lost upgrade of `x − 1`**: `v′ = V + 1` against `v = V + W` (`W = ω^p` the bump value of the
target). The summands of `V` absorbed only by `W` are assumed `◁ W` (measured: they are `1`). -/
theorem v_frame_xm1 {V sW yW : T} (hV : isOT V = true) (hW : isOT (psi sW yW z) = true)
    (h1 : one ≤ psi sW yW z)
    (hR : ∀ r ∈ summands V, ¬ r < one → r < psi sW yW z → Lhd z r (psi sW yW z)) :
    LhdE (sf (add V one)) (add V (psi sW yW z)) := by
  have hone : isOT one = true := rfl
  have hot1 : isOT (add V one) = true := isOT_add hV hone
  rw [sf_ot hot1]
  exact lhdE_add_absorb (s' := z) (y' := z) (lhdE_one h1) V hV hot1 hR

/-! ## v の枠 (2): のりしろの p の段 -/

theorem summands_foldl_sub : ∀ (l : List T) (acc : T), isOT acc = true → (∀ t ∈ l, Single t) →
    ∀ q ∈ summands (l.foldl (fun a b => sf (add a b)) acc), q ∈ summands acc ∨ q ∈ l
  | [], acc, _, _, q, hq => Or.inl hq
  | t :: l, acc, hacc, hs, q, hq => by
    simp only [List.foldl_cons] at hq
    obtain ⟨s0, y0, rfl⟩ := (hs t List.mem_cons_self).2
    have hot : isOT (add acc (psi s0 y0 z)) = true := isOT_add hacc (hs _ List.mem_cons_self).1
    rcases summands_foldl_sub l _ (by rw [sf_ot hot]; exact hot)
      (fun u hu => hs u (List.mem_cons_of_mem _ hu)) q hq with h | h
    · rw [sf_ot hot] at h
      rcases summands_add_single acc q h with h' | ⟨h', _⟩
      · exact Or.inr (by rw [h']; exact List.mem_cons_self)
      · exact Or.inl h'
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem summands_sumN_sub {l : List T} (hs : ∀ t ∈ l, Single t) : ∀ q ∈ summands (sumN l), q ∈ l := by
  intro q hq
  rcases summands_foldl_sub l z rfl hs q hq with h | h
  · simp [summands] at h
  · exact h

theorem sumN_snoc_ot {l : List T} {t : T} (hs : ∀ u ∈ l, Single u) (ht : Single t) :
    sumN (l ++ [t]) = add (sumN l) t := by
  rw [sumN_snoc, sf_ot (isOT_add (isOT_sumN l (fun u hu => (hs u hu).1)) ht.1)]

/-- **The `p` level of a bump frame**: `1 + P + b′ ⊴ 1 + P + b` from `b′ ⊴ b` (with `P ≥ b`). -/
theorem bump_p_lhd {Pt : List T} {s' y' s y : T} (hsP : ∀ t ∈ Pt, Single t)
    (hPb : ∀ t ∈ Pt, psi s y z ≤ t) (hb : Single (psi s y z)) (hb' : Single (psi s' y' z))
    (h : LhdE (psi s' y' z) (psi s y z)) :
    LhdE (sumN (one :: Pt ++ [psi s' y' z])) (sumN (one :: Pt ++ [psi s y z])) := by
  have hsK : ∀ t ∈ one :: Pt, Single t := fun t ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨rfl, z, z, rfl⟩
    · exact hsP t ht
  rw [List.cons_append, List.cons_append, ← List.cons_append, ← List.cons_append,
    sumN_snoc_ot hsK hb', sumN_snoc_ot hsK hb]
  have hK : isOT (sumN (one :: Pt)) = true := isOT_sumN _ (fun u hu => (hsK u hu).1)
  apply lhdE_add_absorb h _ hK (isOT_add hK hb'.1)
  intro r hr hn hlt
  rcases List.mem_cons.mp (summands_sumN_sub hsK r hr) with rfl | hrP
  · exact lhd_one hlt
  · exact absurd hlt (fun h' => lt_irrefl' _ (lt_of_lt_of_le h' (hPb r hrP)))

/-! ## v の枠 (3): のりしろの ω^ の段（ε_0 をまたぐ場合） -/

/-- A standard `ψ_0(y)` below `ψ_0(Ω_1)` dominates its components. -/
theorem closed_psi0 {y : T} (hot : isOT (psi z y z) = true) (hE : psi z y z < E0) : Closed z (psi z y z) := by
  intro u hu g hg
  have hu0 : u = z := by
    cases u with
    | z => rfl
    | psi _ _ _ => exact absurd (by simp [lt]) hu
  subst hu0
  obtain ⟨_, hyot, _, _, hcy⟩ := isOT_psi_iff.mp hot
  have hy1 : y < Om one := (below_E0 hE).2
  -- `y < ψ_0(y)`
  have hyl : y < psi z y z := by
    cases y with
    | z => exact T.z_lt_psi _ _ _
    | psi a e r =>
      have ha : a = z := by
        cases a with
        | z => rfl
        | psi a1 a2 a3 =>
          exfalso
          unfold Om at hy1; rw [psi_lt_psi_z_iff] at hy1
          rcases hy1 with h | ⟨_, h⟩
          · unfold one at h; rw [T.psi_lt_psi] at h
            rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> exact T.not_lt_z _ h
          · exact T.not_lt_z _ h
      subst ha
      have he : e < psi z e r := hcy e (by simp [comps, lt])
      rw [T.psi_lt_psi]; right; left; exact ⟨rfl, he⟩
  simp only [comps, List.mem_append] at hg
  rw [if_neg (by simp [lt])] at hg
  simp only [List.mem_cons, List.mem_append] at hg
  rcases hg with (rfl | h | h) | h
  · exact le_of_lt hyl
  · exact le_of_lt (lt_trans (hcy g h) hyl)
  · simp [comps] at h
  · simp [comps] at h

/-- **`ω^` across `ψ_0(Ω_1)` with subscript `0`**: a closed `G′ < ψ_0(Ω_1)` against `G ≥ ψ_0(Ω_1)` whose
leading subscript is `0`. -/
theorem omega_lhd_mixed0 {G' b c : T} (hG' : G' < E0) (hcl : Closed z G') (hot : isOT (psi z b c) = true)
    (hE : ¬ psi z b c < E0) : LhdE (omega G') (omega (psi z b c)) := by
  rw [omega_small hG', omega_big hot hE]
  apply lhdE_psi_closed _ hcl
  -- the argument of `ω^G` is at least `Ω_1`
  have hge := le_omega_big hot hE
  rw [omega_big hot hE] at hge
  generalize (app (split b (psi (succ z) z z)).1
    (if (split b (psi (succ z) z z)).2 = z then c else psi z b c)) = Y at hge ⊢
  have hEG : E0 ≤ psi z b c := by
    rcases lt_trichotomy' E0 (psi z b c) with h | h | h
    · exact le_of_lt h
    · rw [h]
    · exact absurd h hE
  have hEY : E0 ≤ psi z Y z := le_trans hEG hge
  have hY : Om one ≤ Y := by
    unfold E0 at hEY
    rcases (le_iff _ _).mp hEY with h | h
    · rw [psi_lt_psi_z_iff] at h
      rcases h with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact le_of_lt h
    · simp only [psi.injEq] at h; rw [h.2.1]
  have hE1 : E0 < Om one := by
    unfold E0 Om; rw [psi_lt_psi_z_iff]; left; exact T.z_lt_psi _ _ _
  exact le_of_lt (lt_of_lt_of_le (lt_trans hG' hE1) hY)

end Ytosk
