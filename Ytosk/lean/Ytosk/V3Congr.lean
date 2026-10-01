/-
**評価の一致の補題。** 評価の方程式 `Cons` の解は範囲内で一意（`cons_unique`）。不変条件と落とす補題の残りの
仮定は評価を範囲内の列でしか読まないので、範囲内で一致する評価に移る。
-/
import Ytosk.V3Top

namespace Ytosk

open T

/-- Two valuations agree on the columns of `M`. -/
def Agree (M : Mat) (σ τ : Valn) : Prop := ∀ i, i < M.length → σ.o i = τ.o i ∧ σ.v i = τ.v i

theorem agree_of_cons {M : Mat} {σ τ : Valn} {rk : Bool → Nat → Nat} (hσ : Cons M σ) (hτ : Cons M τ)
    (hR : Rk M rk) : Agree M σ τ := cons_unique hσ hτ hR

theorem Agree.symm {M : Mat} {σ τ : Valn} (h : Agree M σ τ) : Agree M τ σ :=
  fun i hi => ⟨(h i hi).1.symm, (h i hi).2.symm⟩

theorem cnt_congr {M : Mat} {σ τ : Valn} (h : Agree M σ τ) (i : Nat) :
    (children M i).map (cnt M σ i) = (children M i).map (cnt M τ i) := by
  apply List.map_congr_left
  intro c hc
  unfold cnt
  rw [(h c (mem_children hc).2).1]

theorem good3_congr {M : Mat} {σ τ : Valn} (hG : Good3 M σ) (h : Agree M σ τ) : Good3 M τ where
  ot_o i hi := by rw [← (h i hi).1]; exact hG.ot_o i hi
  ot_v i hi := by rw [← (h i hi).2]; exact hG.ot_v i hi
  dec i hi := by
    have := hG.dec i hi
    unfold cvals at this ⊢
    rwa [← cnt_congr h i]

theorem roots_lt {M : Mat} {i : Nat} (hi : i ∈ roots M) : i < M.length := by
  unfold roots at hi; rw [List.mem_filter] at hi; simpa using hi.1

theorem roots_map_congr {M : Mat} {σ τ : Valn} (h : Agree M σ τ) :
    (roots M).map σ.o = (roots M).map τ.o :=
  List.map_congr_left (fun i hi => (h i (roots_lt hi)).1)

theorem rootS_congr {M : Mat} {σ τ : Valn} (hS : ∀ i ∈ roots M, Single (σ.o i)) (h : Agree M σ τ) :
    ∀ i ∈ roots M, Single (τ.o i) := fun i hi => by rw [← (h i (roots_lt hi)).1]; exact hS i hi

theorem rootP_congr {M : Mat} {σ τ : Valn} (hP : ((roots M).map σ.o).Pairwise (fun a b => b ≤ a))
    (h : Agree M σ τ) : ((roots M).map τ.o).Pairwise (fun a b => b ≤ a) := by
  rwa [← roots_map_congr h]

theorem lt_of_entry_ne {M : Mat} {r i : Nat} (h : entry M r i ≠ 0) : i < M.length := by
  by_contra hn; exact h (entry_out (by omega) r)

theorem vOpt_par_congr {M : Mat} {σ τ : Valn} (h : Agree M σ τ) {r i : Nat} (hi : i < M.length) :
    vOpt σ (par M r i) = vOpt τ (par M r i) := by
  cases hp : par M r i with
  | none => rfl
  | some m => exact (h m (by have := par_lt M r i m hp; omega)).2

theorem bumpW_congr {M : Mat} {σ τ : Valn} (h : Agree M σ τ) (i : Nat) :
    bumpW M σ i = bumpW M τ i := by
  unfold bumpW
  congr 3
  apply List.map_congr_left
  intro j _
  unfold bumpTerm
  split
  · congr 2
    apply List.map_congr_left
    intro k hk
    exact (h k (mem_children hk).2).1
  · rfl

theorem mem_CL_take {N : Mat} {x i c : Nat} (hx : x ≤ N.length) (hc : c ∈ CL (N.take x) i) :
    c < x := by
  unfold CL at hc
  rw [List.mem_filter] at hc
  have := (mem_children hc.1).2
  rw [List.length_take] at this; omega

theorem map_o_congr {N : Mat} {σ τ : Valn} (h : Agree N σ τ) {Lc : List Nat}
    (hL : ∀ c ∈ Lc, c < N.length) : Lc.map σ.o = Lc.map τ.o :=
  List.map_congr_left (fun c hc => (h c (hL c hc)).1)

/-- **`DropRes` moves to agreeing valuations** (of `N` and of `N.take x`). -/
theorem dropRes_congr {N : Mat} {x : Nat} {σ σ' τ τ' : Valn} (hx : x < N.length)
    (hD : DropRes N x σ σ') (h : Agree N σ τ) (h' : Agree (N.take x) σ' τ') : DropRes N x τ τ' := by
  have hlt : (N.take x).length = x := by rw [List.length_take]; omega
  have hLc : ∀ i (Lc : List Nat) cs, CL (N.take x) i = Lc ++ [cs] →
      (∀ c ∈ Lc, c < N.length) ∧ cs < x := by
    intro i Lc cs hcl
    refine ⟨fun c hc => ?_, mem_CL_take hx.le (by rw [hcl]; simp)⟩
    have := mem_CL_take hx.le (show c ∈ CL (N.take x) i by rw [hcl]; simp [hc]); omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi Lc cs hcl s y ho hs g hg
    obtain ⟨hL, hcs⟩ := hLc i Lc cs hcl
    have hv := (h i (by omega)).2
    rw [← hv, ← map_o_congr h hL]
    rw [← hv] at hs hg
    exact hD.argT i hi Lc cs hcl s y (by rw [(h' cs (by omega)).1]; exact ho) hs g hg
  · intro i hi Lc cs hcl hne
    obtain ⟨hL, hcs⟩ := hLc i Lc cs hcl
    have hv := (h i (by omega)).2
    have hvc' := (h' cs (by omega)).2
    have hvc := (h cs (by omega)).2
    have hoc := (h cs (by omega)).1
    rw [← hvc', ← hvc] at hne
    obtain ⟨h1, h2⟩ := hD.vst i hi Lc cs hcl hne
    refine ⟨?_, ?_⟩
    · rw [← hv, ← hvc']; exact h1
    · intro s y ho htr
      rw [← hvc']
      rw [← hoc] at ho
      rw [← hv, ← map_o_congr h hL] at htr
      exact h2 s y ho htr
  · intro i h1 h2 j hj hjb k hk hw hcase
    have hkN := (mem_children hk).2
    have hiN := lt_of_entry_ne h1
    have hok := (h k hkN).1
    rw [← vOpt_par_congr h hiN]
    apply hD.ws i h1 h2 j hj hjb k hk (by rw [hok]; exact hw)
    rcases hcase with hc | ⟨hkx, hne, hl⟩
    · exact Or.inl hc
    · right
      refine ⟨hkx, ?_, ?_⟩
      · rw [(h' k (by omega)).1, hok]; exact hne
      · rw [(h' k (by omega)).2, (h k hkN).2]; exact hl
  · intro i k W hix hu hv hW r hr hrW
    have hiN : i < N.length := by omega
    rw [← vOpt_par_congr h hiN] at hv hr
    rw [← (h k (upg_lt hiN hu)).2] at hv
    exact hD.ua i k W hix hu hv hW r hr hrW
  · intro i h1 h2 hcol r hr hr2
    have hiN := lt_of_entry_ne h1
    rw [← vOpt_par_congr h hiN] at hr
    rw [← bumpW_congr h]
    refine hD.ab i h1 h2 (fun j hj hjb hch => ?_) r hr hr2
    rw [(h x hx).2]; exact hcol j hj hjb hch

end Ytosk
