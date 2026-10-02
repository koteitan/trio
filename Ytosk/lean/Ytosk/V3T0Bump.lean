/-
**3 行・t = 0: 展開 N = M[n] の評価の BumpKidsDec（のりしろの子の子の値が減ること）。**

- r 以後のコピーの列の子: 中間のコピーは M の値、最後のコピーは M.take x の値（`copy_kids_vals`）。
- r より前: のりしろの子 j の子で D に入るのは、`dv_shape` から i の最後の子の最後の子だけ。値は ◁ で下がる。
  j = g（r の親）のときは子にコピーの根が並ぶ: 値は M の子、omid × (n − 1)、o′(r)。
-/
import Ytosk.V3T0Root

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) (hGN : GoodOT (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN

omit hC hG hCN hGN in
/-- **The values of the children of a copy column**: those of `M` in a middle copy, of `M.take x` in the
last. -/
theorem copy_kids_vals {ρ' : Valn}
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i)
    {k q : Nat} (hk : k < n) (hq : q < L) :
    (children (TRIO.gexp M r L 0 0 n) (r + (k * L + q))).map σ.o =
      ((children M (r + q)).filter (fun c => decide (c < r + L))).map
        (if k + 1 < n then ρ.o else ρ'.o) := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hkL : k * L + L ≤ n * L := by
    have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
  rw [children_copy0 hlen hL hp hn hk hq, List.map_map]
  apply List.map_congr_left
  intro d hd
  have h := List.mem_filter.mp hd
  have h1 := (mem_children h.1).1
  have h2 : d < r + L := by simpa using h.2
  obtain ⟨q', rfl⟩ : ∃ q', d = r + q' := ⟨d - r, by omega⟩
  simp only [Function.comp, shk, if_pos (show r ≤ r + q' by omega)]
  rw [show r + q' + k * L = r + (k * L + q') by omega, hσB _ (by omega) (by rw [hlN]; omega)]
  split
  · rename_i hkn; exact tau_o_mid hkn (by omega) (by omega)
  · have hk' : k = n - 1 := by omega
    rw [hk']
    exact tau_o_last (by omega)

/-- **`BumpKidsDec` of `N = M[n]`** (`t = 0`). -/
theorem bumpKidsDec_N_t0 {ρ' : Valn} (hKD : BumpKidsDec M ρ) (hKDT : BumpKidsDec (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i)
    (hoffD : ∀ i, i < r → ¬ DepX M (r + L) true i → σ.o i = ρ.o i)
    (hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hOX : omid M r L ρ ≤ ρ.o r) (hO'le : ρ'.o r ≤ omid M r L ρ) :
    BumpKidsDec (TRIO.gexp M r L 0 0 n) σ := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hDr : DepX M (r + L) true r := depLike_r hlen hL hp he2 (depLike_depX M (r + L))
  -- the children of a copy column: those of `M` below `x`
  have hcopy : ∀ k q, k < n → q < L →
      (((children (TRIO.gexp M r L 0 0 n) (r + (k * L + q))).map σ.o).Pairwise (fun a b => b ≤ a) ↔
      (((children M (r + q)).filter (fun c => decide (c < r + L))).map
        (if k + 1 < n then ρ.o else ρ'.o)).Pairwise (fun a b => b ≤ a)) := by
    intro k q hk hq
    rw [copy_kids_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hσB hk hq]
  -- a bump child `d` of `r + q` below `x`: its children in the copy decrease
  have hcopyKD : ∀ k q d, k < n → q < L → entry M 1 (r + q) ≠ 0 → entry M 2 (r + q) ≠ 0 →
      d ∈ children M (r + q) → d < r + L → col M d = bump M (r + q) →
      (((children M d).filter (fun c => decide (c < r + L))).map
        (if k + 1 < n then ρ.o else ρ'.o)).Pairwise (fun a b => b ≤ a) := by
    intro k q d hk hq h1 h2 hd hdx hdb
    split
    · have hpM := hKD (r + q) h1 h2 d hd hdb
      exact hpM.sublist ((List.filter_sublist).map _)
    · have hdT : d ∈ children (M.take (r + L)) (r + q) := by
        rw [children_take, List.mem_filter]; exact ⟨hd, by simpa using hdx⟩
      have hT := hKDT (r + q) (by rw [entry_take M 1 (by omega)]; exact h1)
        (by rw [entry_take M 2 (by omega)]; exact h2) d hdT
        (by rw [col_take M hdx, bump_take M (by omega)]; exact hdb)
      rwa [children_take] at hT
  intro i h1 h2 j hj hjb
  have hij := (mem_children hj).1
  have hjN := (mem_children hj).2
  rcases Nat.lt_or_ge i r with hir | hir
  · -- a column before `r`
    have he1i : entry M 1 i ≠ 0 := by rwa [entry_pre0 hlen hn 1 (by omega)] at h1
    have he2i : entry M 2 i ≠ 0 := by rwa [entry_pre0 hlen hn 2 (by omega)] at h2
    -- the shape of a `v` call at `i`
    have hshape : DepX M (r + L) false i → ∃ Li K j' k', children M i = Li ++ [j'] ∧
        children M j' = K ++ [k'] ∧ (∀ d ∈ K, ¬ DepX M (r + L) true d) ∧
        (∀ d ∈ Li, ∀ e ∈ children M d, ¬ DepX M (r + L) true e) := by
      intro hv
      obtain ⟨_, _, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hv
      rcases hcase with ⟨h2', _⟩ | ⟨_, Li, K, j', k', hch, _, hchj, _, hKnd, hLnd⟩
      · exact absurd h2' he2i
      · exact ⟨Li, K, j', k', hch, hchj, hKnd, fun d hd e he => (hLnd d hd e he).2⟩
    -- a bump child `j < r` other than `g`: only its last child can be in `D`
    have hlow : ∀ j, j ∈ children M i → j < r → par M 0 r ≠ some j → col M j = bump M i →
        ((children M j).map σ.o).Pairwise (fun a b => b ≤ a) := by
      intro j hjM hjr hjg hjbM
      have hjr' : ∀ d ∈ children M j, d < r := fun d hd => children_lt_r hlen hL hp hjr hjg hd
      apply pairwise_lower_last (P := fun d => DepX M (r + L) true d) (children_sorted M j)
        (hKD i he1i he2i j hjM hjbM)
      · intro d hd hD e he hde
        obtain ⟨Li, K, j', k', hch, hchj, hKnd, hLnd⟩ :=
          hshape (DepX.vbump he1i he2i hjM hjbM hd hD)
        have hjL : j = j' ∨ j ∈ Li := by
          rw [hch] at hjM
          rcases List.mem_append.mp hjM with h | h
          · exact Or.inr h
          · exact Or.inl (List.mem_singleton.mp h)
        rcases hjL with rfl | hjL
        · rw [hchj] at hd he
          rcases List.mem_append.mp hd with hdK | hdk
          · exact hKnd d hdK hD
          · have hdk' := List.mem_singleton.mp hdk
            have hs := children_sorted M j
            rw [hchj] at hs
            rcases List.mem_append.mp he with heK | hek
            · have := (List.pairwise_append.mp hs).2.2 e heK k' (by simp); omega
            · have := List.mem_singleton.mp hek; omega
        · exact hLnd j hjL d hd hD
      · intro d hd hD; exact hoffD d (hjr' d hd) hD
      · intro d hd hD; exact hdl d (hjr' d hd) hD
    by_cases hig : par M 0 r = some i
    · -- `i = g`: its children in `N` are those of `M` and the copy roots
      rw [children_g0 hlen hL hp hn hig] at hj
      rw [bump_pre0 hlen hL hp hn (by omega)] at hjb
      rcases List.mem_append.mp hj with hjM | hjc
      · have hjle := children_g_le hlen hL hp hig hjM
        rcases Nat.lt_or_ge j r with hjr | hjr
        · have hjg : par M 0 r ≠ some j := by rw [hig]; intro h; cases h; omega
          rw [col_pre0 hlen hL hp hn (by omega)] at hjb
          rw [children_pre0 hlen hL hp hn hjr hjg]
          exact hlow j hjM hjr hjg hjb
        · -- `j = r`, the first copy root
          have hjr' : j = r := by omega
          subst hjr'
          have := (hcopy 0 0 (by omega) hL).mpr
          simp only [Nat.zero_mul, Nat.add_zero] at this
          apply this
          have hjb' : col M j = bump M i := by
            have hc := col_copy0 hlen (n := n) (k := 0) (q := 0) (by omega) hL
            simp only [Nat.zero_mul, Nat.add_zero] at hc
            rw [← hc]; exact hjb
          have hpM := hKD i he1i he2i j hjM hjb'
          split
          · exact hpM.sublist ((List.filter_sublist).map _)
          · omega
      · -- a later copy root `r + (k + 1) L`
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hjc
        have hk' := List.mem_range.mp hk
        have hc := col_copy0 hlen (n := n) (k := k + 1) (q := 0) (by omega) hL
        simp only [Nat.add_zero] at hc
        have hjb' : col M r = bump M i := by rw [← hc]; exact hjb
        have hrM : r ∈ children M i := mem_children_iff.mpr ⟨by omega, hig⟩
        have := (hcopy (k + 1) 0 (by omega) hL).mpr
        simp only [Nat.add_zero] at this
        apply this
        have hpM := hKD i he1i he2i r hrM hjb'
        split
        · exact hpM.sublist ((List.filter_sublist).map _)
        · have hrT : r ∈ children (M.take (r + L)) i := by
            rw [children_take, List.mem_filter]; exact ⟨hrM, by simpa using (show r < r + L by omega)⟩
          have hT := hKDT i (by rw [entry_take M 1 (by omega)]; exact he1i)
            (by rw [entry_take M 2 (by omega)]; exact he2i) r hrT
            (by rw [col_take M (by omega), bump_take M (by omega)]; exact hjb')
          rwa [children_take] at hT
    · rw [children_pre0 hlen hL hp hn hir hig] at hj
      have hjr := children_lt_r hlen hL hp hir hig hj
      rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)] at hjb
      by_cases hjg : par M 0 r = some j
      · -- `j = g`: the copy roots follow the children of `g`
        rw [children_g0 hlen hL hp hn hjg, children_g_last hlen hL hp hjg]
        have hrM : r ∈ children M j := mem_children_iff.mpr ⟨by omega, hjg⟩
        obtain ⟨Li, K, j', k', hch, hchj, hKnd, hLnd⟩ := hshape (DepX.vbump he1i he2i hj hjb hrM hDr)
        have hjj : j = j' := by
          rw [hch] at hj
          rcases List.mem_append.mp hj with h | h
          · exact absurd hDr (hLnd j h r hrM)
          · exact List.mem_singleton.mp h
        subst hjj
        have hlast := children_g_last hlen hL hp hjg
        have hkr : k' = r := by
          rw [hchj] at hlast
          have := congrArg List.getLast? hlast; simpa using this
        subst hkr
        have hKF : K = (children M j).filter (fun d => decide (d < k')) := by
          have := hchj.symm.trans hlast
          exact List.append_inj_left' this rfl
        have hFv : K.map σ.o = K.map ρ.o := List.map_congr_left (fun d hd => by
          have hdr : d < k' := by rw [hKF] at hd; simpa using (List.mem_filter.mp hd).2
          exact hoffD d hdr (hKnd d hd))
        have hmapN : (k' :: (List.range (n - 1)).map (fun k => k' + (k + 1) * L)).map σ.o =
            List.replicate (n - 1) (omid M k' L ρ) ++ [ρ'.o k'] := by
          have hl : (k' :: (List.range (n - 1)).map (fun k => k' + (k + 1) * L)) =
              (List.range n).map (fun k => k' + k * L) := by
            rw [show n = (n - 1) + 1 by omega, List.range_succ_eq_map, List.map_cons, List.map_map]
            simp only [Nat.zero_mul, Nat.add_zero, Nat.add_sub_cancel]
            rfl
          have hr : List.range n = List.range (n - 1) ++ [n - 1] := by
            rw [← List.range_succ]; congr 1; omega
          rw [hl, hr, List.map_append, List.map_append]
          congr 1
          · rw [List.map_map, List.eq_replicate_iff]
            refine ⟨by simp, fun b hb => ?_⟩
            obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
            exact hσmid k (by have := List.mem_range.mp hk; omega)
          · simp only [List.map_cons, List.map_nil]; rw [hσlast]
        rw [← hKF, List.append_assoc, List.singleton_append, List.map_append, hmapN, hFv]
        have hpM := hKD i he1i he2i j hj hjb
        rw [hchj, List.map_append, List.map_singleton] at hpM
        have hp1 := List.pairwise_append.mp hpM
        refine List.pairwise_append.mpr ⟨hp1.1, List.pairwise_append.mpr
          ⟨List.pairwise_replicate.mpr (Or.inr (le_refl _)), by simp, fun a ha b hb => ?_⟩,
          fun a ha b hb => ?_⟩
        · simp at hb; rw [hb, (List.mem_replicate.mp ha).2]; exact hO'le
        · have hra := hp1.2.2 a ha (ρ.o k') (by simp)
          rcases List.mem_append.mp hb with hb | hb
          · rw [(List.mem_replicate.mp hb).2]; exact le_trans hOX hra
          · simp at hb; rw [hb]; exact le_trans hO'le (le_trans hOX hra)
      · rw [children_pre0 hlen hL hp hn hjr hjg]
        exact hlow j hj hjr hjg hjb
  · -- a copy column
    have hk0 : (i - r) / L < n := by
      rw [hlN] at hjN
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hq0 : (i - r) % L < L := Nat.mod_lt _ hL
    have hi' : i = r + ((i - r) / L * L + (i - r) % L) := by
      have := Nat.div_add_mod (i - r) L
      rw [Nat.mul_comm] at this; omega
    obtain ⟨k, q, hk, hq, rfl⟩ : ∃ k q, k < n ∧ q < L ∧ i = r + (k * L + q) := ⟨_, _, hk0, hq0, hi'⟩
    rw [entry_copy0 hlen hk hq] at h1 h2
    rw [children_copy0 hlen hL hp hn hk hq] at hj
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hj
    have hd' := List.mem_filter.mp hd
    have hdM := hd'.1
    have hdx : d < r + L := by simpa using hd'.2
    have hdr := (mem_children hdM).1
    obtain ⟨q', rfl⟩ : ∃ q', d = r + q' := ⟨d - r, by omega⟩
    simp only [shk, if_pos (show r ≤ r + q' by omega)] at hjb ⊢
    rw [show r + q' + k * L = r + (k * L + q') by omega] at hjb ⊢
    have hb : bump (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) = bump M (r + q) := by
      unfold bump; rw [entry_copy0 hlen hk hq 0, entry_copy0 hlen hk hq 1]
    rw [col_copy0 hlen hk (by omega), hb] at hjb
    rw [hcopy k q' hk (by omega)]
    exact hcopyKD k q (r + q') hk hq h1 h2 hdM hdx hjb

omit hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hGN in
/-- `nzs` of a filtered map is a sublist of `nzs` of the map. -/
theorem nzs_filter_map_sublist {α : Type} (l : List α) (p : α → Bool) (f : α → T) :
    (nzs ((l.filter p).map f)).Sublist (nzs (l.map f)) :=
  ((List.filter_sublist).map f).filter _

/-- **`BumpTermDec` of `N = M[n]`** (`t = 0`). -/
theorem bumpTermDec_N_t0 {ρ' : Valn} (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
    (hTDT : BumpTermDec (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i)
    (hoffD : ∀ i, i < r → ¬ DepX M (r + L) true i → σ.o i = ρ.o i)
    (hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hl : par M 0 r ≠ none → Lhd z (ρ'.o r) (ρ.o r))
    (hG0le : ∀ g, par M 0 r = some g → col M r = bump M g →
      sumN ((children (M.take (r + L)) r).map ρ'.o) ≤ sumN ((children (M.take (r + L)) r).map ρ.o)) :
    BumpTermDec (TRIO.gexp M r L 0 0 n) σ := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hDr : DepX M (r + L) true r := depLike_r hlen hL hp he2 (depLike_depX M (r + L))
  have hOTN : ∀ t, t < (TRIO.gexp M r L 0 0 n).length → isOT (σ.o t) = true := hGN.ot_o
  have hbtOT : ∀ (N' : Mat) (τ : Valn) (i j : Nat), (∀ c ∈ children N' j, isOT (τ.o c) = true) →
      isOT (bumpTerm N' τ i j) = true := by
    intro N' τ i j h
    unfold bumpTerm; split
    · apply isOT_omega; apply isOT_sumN
      intro t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact h c hc
    · rfl
  intro i h1 h2
  rcases Nat.lt_or_ge i r with hir | hir
  · have he1i : entry M 1 i ≠ 0 := by rwa [entry_pre0 hlen hn 1 (by omega)] at h1
    have he2i : entry M 2 i ≠ 0 := by rwa [entry_pre0 hlen hn 2 (by omega)] at h2
    have hbi : bump (TRIO.gexp M r L 0 0 n) i = bump M i := bump_pre0 hlen hL hp hn (by omega)
    -- a child `j < r` other than `g` whose children are not in `D` keeps its term
    have hsame : ∀ j, j ∈ children M i → j < r → par M 0 r ≠ some j →
        (∀ e ∈ children M j, ¬ DepX M (r + L) true e) →
        bumpTerm (TRIO.gexp M r L 0 0 n) σ i j = bumpTerm M ρ i j := by
      intro j hjM hjr hjg hnd
      unfold bumpTerm
      rw [col_pre0 hlen hL hp hn (by omega), hbi, children_pre0 hlen hL hp hn hjr hjg]
      split
      · congr 2
        exact List.map_congr_left (fun e he => hoffD e (children_lt_r hlen hL hp hjr hjg he) (hnd e he))
      · rfl
    by_cases hig : par M 0 r = some i
    · -- `i = g`
      rw [children_g0 hlen hL hp hn hig, children_g_last hlen hL hp hig]
      set F := (children M i).filter (fun d => decide (d < r)) with hF
      have hFr : ∀ d ∈ F, d < r := fun d hd => by simpa using (List.mem_filter.mp hd).2
      have hFM : ∀ d ∈ F, d ∈ children M i := fun d hd => (List.mem_filter.mp hd).1
      have hrM : r ∈ children M i := mem_children_iff.mpr ⟨by omega, hig⟩
      -- the children of `F` are not in `D`
      have hFnd : ∀ d ∈ F, col M d = bump M i → ∀ e ∈ children M d, ¬ DepX M (r + L) true e := by
        intro d hd hdb e he hD
        obtain ⟨_, _, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega)
          (DepX.vbump he1i he2i (hFM d hd) hdb he hD)
        rcases hcase with ⟨h2', _⟩ | ⟨_, Li, _, j', _, hch, _, _, _, _, hLnd⟩
        · exact he2i h2'
        · have hlast := children_g_last hlen hL hp hig
          rw [hch] at hlast
          have hj'r : j' = r := by
            have := congrArg List.getLast? hlast; simpa using this
          have hdL : d ∈ Li := by
            have hdc := hFM d hd
            rw [hch] at hdc
            rcases List.mem_append.mp hdc with h | h
            · exact h
            · have := List.mem_singleton.mp h; have := hFr d hd; omega
          exact (hLnd d hdL e he).2 hD
      have hFv : F.map (bumpTerm (TRIO.gexp M r L 0 0 n) σ i) = F.map (bumpTerm M ρ i) := by
        apply List.map_congr_left
        intro d hd
        have hdg : par M 0 r ≠ some d := by
          rw [hig]; intro h
          have hid : i = d := Option.some.inj h
          have := (mem_children (hFM d hd)).1; omega
        by_cases hdb : col M d = bump M i
        · exact hsame d (hFM d hd) (hFr d hd) hdg (hFnd d hd hdb)
        · unfold bumpTerm
          rw [col_pre0 hlen hL hp hn (by have := hFr d hd; omega), hbi, if_neg hdb, if_neg hdb]
      have hM := hTD i he1i he2i
      rw [children_g_last hlen hL hp hig, List.map_append, List.map_singleton, ← hF] at hM
      -- the copy roots
      have hroots : (r :: (List.range (n - 1)).map (fun k => r + (k + 1) * L)) =
          (List.range n).map (fun k => r + k * L) := by
        rw [show n = (n - 1) + 1 by omega, List.range_succ_eq_map, List.map_cons, List.map_map]
        simp only [Nat.zero_mul, Nat.add_zero, Nat.add_sub_cancel]
        rfl
      rw [List.append_assoc, List.singleton_append, hroots, List.map_append, nzs_append, hFv]
      rw [nzs_append] at hM
      by_cases hrb : col M r = bump M i
      · -- the copy roots are bump children: `ω^{G0}` × (n − 1), then `ω^{G0′}`
        set G0 := sumN ((children (M.take (r + L)) r).map ρ.o) with hG0
        set G0' := sumN ((children (M.take (r + L)) r).map ρ'.o) with hG0'
        have hG0ot : isOT G0 = true := isOT_sumN _ (fun t ht => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
          rw [children_take, List.mem_filter] at hc
          exact hG.ot_o c (mem_children hc.1).2)
        have hbt : ∀ k, k < n → bumpTerm (TRIO.gexp M r L 0 0 n) σ i (r + k * L) =
            omega (if k + 1 < n then G0 else G0') := by
          intro k hk
          have hc := col_copy0 hlen (n := n) (k := k) (q := 0) hk hL
          simp only [Nat.add_zero] at hc
          unfold bumpTerm
          rw [hc, hbi, if_pos hrb]
          have hv := copy_kids_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hσB hk hL
            (q := 0)
          simp only [Nat.add_zero] at hv
          rw [hv, ← children_take]
          split <;> rfl
        have hG0'ot : isOT G0' = true := by
          have hv := copy_kids_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hσB
            (k := n - 1) (q := 0) (by omega) hL
          simp only [Nat.add_zero] at hv
          rw [if_neg (by omega)] at hv
          apply isOT_sumN
          intro t ht
          rw [children_take, ← hv] at ht
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
          exact hOTN c (mem_children hc).2
        have hmapN : ((List.range n).map (fun k => r + k * L)).map (bumpTerm (TRIO.gexp M r L 0 0 n) σ i) =
            List.replicate (n - 1) (omega G0) ++ [omega G0'] := by
          have hr : List.range n = List.range (n - 1) ++ [n - 1] := by
            rw [← List.range_succ]; congr 1; omega
          rw [hr, List.map_append, List.map_append]
          congr 1
          · rw [List.map_map, List.eq_replicate_iff]
            refine ⟨by simp, fun b hb => ?_⟩
            obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
            have hk' := List.mem_range.mp hk
            simp only [Function.comp]
            rw [hbt k (by omega), if_pos (by omega)]
          · simp only [List.map_cons, List.map_nil]
            rw [hbt (n - 1) (by omega), if_neg (by omega)]
        have hbtM : bumpTerm M ρ i r = omega (app G0 one) := by
          unfold bumpTerm
          rw [if_pos hrb]
          have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
          rw [children_split_x (x := r + L) hlen hxr, List.map_append, List.map_singleton,
            o_x_one hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG, sumN_snoc,
            ← children_take, ← hG0, sf_ot (isOT_add hG0ot rfl), add_one_eq_app]
        rw [hmapN, nzs_append, nzs_single (omega_ne_z _)]
        rw [hbtM, nzs_single (omega_ne_z _)] at hM
        have hrep : nzs (List.replicate (n - 1) (omega G0)) = List.replicate (n - 1) (omega G0) := by
          rw [nzs, List.filter_eq_self]; intro t ht; rw [(List.mem_replicate.mp ht).2]; simp [omega_ne_z]
        rw [hrep]
        have hp1 := List.pairwise_append.mp hM
        have hOle : omega G0 ≤ omega (app G0 one) :=
          omega_le_omega hG0ot (by rw [← add_one_eq_app]; exact isOT_add hG0ot rfl) (le_of_lt (lt_app_one G0))
        have hO'le : omega G0' ≤ omega G0 := omega_le_omega hG0'ot hG0ot (hG0le i hig hrb)
        rw [← List.append_assoc]
        refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨hp1.1,
          List.pairwise_replicate.mpr (Or.inr (le_refl _)), fun a ha b hb => ?_⟩, by simp,
          fun a ha b hb => ?_⟩
        · rw [(List.mem_replicate.mp hb).2]; exact le_trans hOle (hp1.2.2 a ha _ (by simp))
        · simp at hb; rw [hb]
          rcases List.mem_append.mp ha with ha | ha
          · exact le_trans hO'le (le_trans hOle (hp1.2.2 a ha _ (by simp)))
          · rw [(List.mem_replicate.mp ha).2]; exact hO'le
      · -- the copy roots are not bump children
        have hz : ∀ k, k < n → bumpTerm (TRIO.gexp M r L 0 0 n) σ i (r + k * L) = z := by
          intro k hk
          have hc := col_copy0 hlen (n := n) (k := k) (q := 0) hk hL
          simp only [Nat.add_zero] at hc
          unfold bumpTerm; rw [hc, hbi, if_neg hrb]
        have hbtM : bumpTerm M ρ i r = z := by unfold bumpTerm; rw [if_neg hrb]
        have hnz : nzs (((List.range n).map (fun k => r + k * L)).map
            (bumpTerm (TRIO.gexp M r L 0 0 n) σ i)) = [] := by
          rw [nzs, List.filter_eq_nil_iff]
          intro t ht
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
          obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
          simp [hz k' (List.mem_range.mp hk')]
        rw [hnz, List.append_nil]
        rw [hbtM] at hM
        simpa [nzs] using hM
    · rw [children_pre0 hlen hL hp hn hir hig]
      by_cases hiv : DepX M (r + L) false i
      · obtain ⟨_, _, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hiv
        rcases hcase with ⟨h2', _⟩ | ⟨_, Li, K, j', k', hch, hjb', hchj, hk'D, hKnd, hLnd⟩
        · exact absurd h2' he2i
        have hM := hTD i he1i he2i
        have hj'M : j' ∈ children M i := by rw [hch]; simp
        have hj'r : j' < r := children_lt_r hlen hL hp hir hig hj'M
        rw [hch, List.map_append, List.map_singleton] at hM ⊢
        have hLi : Li.map (bumpTerm (TRIO.gexp M r L 0 0 n) σ i) = Li.map (bumpTerm M ρ i) := by
          apply List.map_congr_left
          intro d hd
          have hdM : d ∈ children M i := by rw [hch]; simp [hd]
          have hdr := children_lt_r hlen hL hp hir hig hdM
          have hdg : par M 0 r ≠ some d := by
            intro h
            have hrd : r ∈ children M d := mem_children_iff.mpr ⟨by omega, h⟩
            exact (hLnd d hd r hrd).2 hDr
          exact hsame d hdM hdr hdg (fun e he => (hLnd d hd e he).2)
        have hj'nz : bumpTerm (TRIO.gexp M r L 0 0 n) σ i j' ≠ z := by
          unfold bumpTerm
          rw [col_pre0 hlen hL hp hn (by omega), hbi, if_pos hjb']; exact omega_ne_z _
        have hj'nzM : bumpTerm M ρ i j' ≠ z := by
          unfold bumpTerm; rw [if_pos hjb']; exact omega_ne_z _
        rw [hLi, nzs_append, nzs_single hj'nz]
        rw [nzs_append, nzs_single hj'nzM] at hM
        apply pairwise_snoc_le hM
        -- the term of `j′` decreases
        have hj'ot : ∀ c ∈ children M j', isOT (ρ.o c) = true := fun c hc => hG.ot_o c (mem_children hc).2
        unfold bumpTerm
        rw [col_pre0 hlen hL hp hn (by omega), hbi, if_pos hjb', if_pos hjb']
        by_cases hjg : par M 0 r = some j'
        · -- `j′ = g`: the copy roots follow
          have hl' := hl (by rw [hjg]; simp)
          have hlast := children_g_last hlen hL hp hjg
          have hKk : K = (children M j').filter (fun d => decide (d < r)) ∧ k' = r := by
            have h := hchj.symm.trans hlast
            exact ⟨List.append_inj_left' h rfl, List.singleton_inj.mp (List.append_inj_right' h rfl)⟩
          obtain ⟨hKF, rfl⟩ := hKk
          rw [children_g0 hlen hL hp hn hjg, hchj]
          obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG
          have hKv : K.map σ.o = K.map ρ.o := List.map_congr_left (fun d hd => by
            have hdr : d < k' := by rw [hKF] at hd; simpa using (List.mem_filter.mp hd).2
            exact hoffD d hdr (hKnd d hd))
          have hroots : ([k'] ++ (List.range (n - 1)).map (fun k => k' + (k + 1) * L)) =
              (List.range n).map (fun k => k' + k * L) := by
            rw [show n = (n - 1) + 1 by omega, List.range_succ_eq_map, List.map_cons, List.map_map]
            simp only [Nat.zero_mul, Nat.add_zero, Nat.add_sub_cancel]
            rfl
          have hmapN : ((List.range n).map (fun k => k' + k * L)).map σ.o =
              List.replicate (n - 1) (omid M k' L ρ) ++ [ρ'.o k'] := by
            have hr : List.range n = List.range (n - 1) ++ [n - 1] := by
              rw [← List.range_succ]; congr 1; omega
            rw [hr, List.map_append, List.map_append]
            congr 1
            · rw [List.map_map, List.eq_replicate_iff]
              refine ⟨by simp, fun b hb => ?_⟩
              obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
              exact hσmid k (by have := List.mem_range.mp hk; omega)
            · simp only [List.map_cons, List.map_nil]; rw [hσlast]
          rw [List.append_assoc, hroots, List.map_append, hmapN, hKv, List.map_append, List.map_singleton]
          have hdec := hKD i he1i he2i j' hj'M hjb'
          rw [hchj, List.map_append, List.map_singleton] at hdec
          have hsK : ∀ u ∈ K.map ρ.o, Single u := fun u hu => by
            obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
            exact single_o hC hG (mem_children (show d ∈ children M j' by rw [hchj]; simp [hd])).2
          have hX : Single (ρ.o k') := single_o hC hG (by omega)
          have hO : Single (omid M k' L ρ) := by
            rw [← hσmid 0 (by omega)]
            exact single_oT hCN hGN (by rw [hlN]; omega)
          have ho' : Single (ρ'.o k') := by
            rw [← hσlast]; exact single_oT hCN hGN (by
              rw [hlN]; have : (n - 1) * L + L ≤ n * L := by
                rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right L (by omega)
              omega)
          rw [hor] at hdec hX hl' ⊢
          rw [hom] at hO ⊢
          obtain ⟨_, hlt, hG'ot⟩ := g3_brel hn2 hsK hdec hX hO ho' hl'
          exact omega_le_omega hG'ot (isOT_sumN _ (fun u hu => by
            rcases List.mem_append.mp hu with h | h
            · exact (hsK u h).1
            · simp at h; rw [h]; exact hX.1)) (le_of_lt hlt)
        · rw [children_pre0 hlen hL hp hn hj'r hjg]
          have hot1 : ∀ t ∈ (children M j').map σ.o, isOT t = true := by
            intro t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
            exact hOTN c (by rw [hlN]; have := (mem_children hc).2; have := children_lt_r hlen hL hp hj'r hjg hc; omega)
          have hot2 : ∀ t ∈ (children M j').map ρ.o, isOT t = true := by
            intro t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact hj'ot c hc
          apply omega_le_omega (isOT_sumN _ hot1) (isOT_sumN _ hot2)
          apply sumN_le2 _ hot1 hot2
          apply forall2_map_le
          intro c hc
          have hcr := children_lt_r hlen hL hp hj'r hjg hc
          by_cases hcD : DepX M (r + L) true c
          · exact hdl c hcr hcD
          · rw [hoffD c hcr hcD]
      · -- no bump child has a child in `D`
        have : (children M i).map (bumpTerm (TRIO.gexp M r L 0 0 n) σ i) = (children M i).map (bumpTerm M ρ i) := by
          apply List.map_congr_left
          intro c hc
          have hcr := children_lt_r hlen hL hp hir hig hc
          by_cases hcb : col M c = bump M i
          · have hcg : par M 0 r ≠ some c := by
              intro h
              have hrc : r ∈ children M c := mem_children_iff.mpr ⟨by omega, h⟩
              exact hiv (DepX.vbump he1i he2i hc hcb hrc hDr)
            exact hsame c hc hcr hcg (fun e he hD => hiv (DepX.vbump he1i he2i hc hcb he hD))
          · unfold bumpTerm; rw [col_pre0 hlen hL hp hn (by omega), hbi, if_neg hcb, if_neg hcb]
        rw [this]; exact hTD i he1i he2i
  · -- a copy column
    have hk0 : (i - r) / L < n := by
      have hiN : i < (TRIO.gexp M r L 0 0 n).length := by
        by_contra hc
        apply h1
        exact entry_out' (by omega) 1
      rw [hlN] at hiN
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hq0 : (i - r) % L < L := Nat.mod_lt _ hL
    have hi' : i = r + ((i - r) / L * L + (i - r) % L) := by
      have := Nat.div_add_mod (i - r) L
      rw [Nat.mul_comm] at this; omega
    obtain ⟨k, q, hk, hq, rfl⟩ : ∃ k q, k < n ∧ q < L ∧ i = r + (k * L + q) := ⟨_, _, hk0, hq0, hi'⟩
    rw [entry_copy0 hlen hk hq] at h1 h2
    have hb : bump (TRIO.gexp M r L 0 0 n) (r + (k * L + q)) = bump M (r + q) := by
      unfold bump; rw [entry_copy0 hlen hk hq 0, entry_copy0 hlen hk hq 1]
    rw [children_copy0 hlen hL hp hn hk hq, List.map_map]
    set Fq := (children M (r + q)).filter (fun c => decide (c < r + L)) with hFq
    have hvals : ∀ d ∈ Fq, (bumpTerm (TRIO.gexp M r L 0 0 n) σ (r + (k * L + q)) ∘ shk r (k * L)) d =
        if k + 1 < n then bumpTerm M ρ (r + q) d else bumpTerm (M.take (r + L)) ρ' (r + q) d := by
      intro d hd
      have hdM := (List.mem_filter.mp hd).1
      have hdx : d < r + L := by simpa using (List.mem_filter.mp hd).2
      have hdr := (mem_children hdM).1
      obtain ⟨q', rfl⟩ : ∃ q', d = r + q' := ⟨d - r, by omega⟩
      simp only [Function.comp, shk, if_pos (show r ≤ r + q' by omega)]
      rw [show r + q' + k * L = r + (k * L + q') by omega]
      unfold bumpTerm
      rw [col_copy0 hlen hk (by omega), hb,
        copy_kids_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hσB hk (by omega)]
      have hxq : r + L ∉ children M (r + q') := by
        intro h
        have := (mem_children_iff.mp h).2; rw [hp] at this
        have := Option.some.inj this; omega
      by_cases hkn : k + 1 < n
      · simp only [hkn, if_true]; rw [children_filter_x (x := r + L) hlen hxq]
      · simp only [hkn, if_false]
        rw [col_take M hdx, bump_take M (by omega), children_take]
    rw [List.map_congr_left hvals]
    split
    · exact (hTD (r + q) h1 h2).sublist (nzs_filter_map_sublist _ _ _)
    · have hT := hTDT (r + q) (by rw [entry_take M 1 (by omega)]; exact h1)
        (by rw [entry_take M 2 (by omega)]; exact h2)
      rwa [children_take] at hT

end

end Ytosk
