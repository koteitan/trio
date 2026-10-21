/-
**t = 2 の種の列の枠の VSmallF・FrameOT・FrameClosed（2026-10-17、t2）。**

closure の V3PSeed*G は種の列の枠のデータ（N = M[n] での数える子とその値）を出して PH3cG・FC3 を示した。
同じデータから、t2 の枠の性質 QVSF（VSmallF）・QFO（FrameOT）・QFCo（FrameClosed）も出す。
- FrameDom の接頭辞の形 `frameDom_prefix`: H = B + R（R ≠ 0）なら (B, H] の C はどれも B で始まるので、B の成分は
  C の成分。添字 s の成分が z・B 以下・親の添字 a の成分のどれかなら FrameDom。
- qr（q = r で x へ上げなし）: r の最後の枠は状態 B（M と同じ）・子 ψ_{V+1}(Y)。n = 2 では書き換えない
  （`T2SeedQRRes.w1`）。n ≥ 3 では Y = B + ψ_{V+n−1}(…) でどの加数も Ω_{V+2} 以上なので H = Y（接頭辞の形）。
  QVSF・QFO は子の値に依らない部分（段 V での V + 1 の成分は z だけ、状態は M と同じ）。
-/
import Ytosk.V3PSeedAllG
import Ytosk.V3T2FC

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## 項の補題 -/

/-- **FrameDom when `H` extends the state**: every `C ∈ (B, B + R]` starts with `B`. -/
theorem frameDom_prefix {a B s R : T}
    (hsa : ∀ u, ¬ lt a u = true → ∀ g ∈ comps u s, g = z ∨ g ≤ B ∨ g ≤ psi s z z ∨ ∃ d ∈ comps u a, g ≤ d) :
    FrameDom a B s (app B R) := by
  intro u hu C hBC hOC hCX g hg
  obtain ⟨c0, hc0, _, _⟩ := between_app (A := B) (x := z) (y := R) (c := C)
    (by rw [app_z_right]; exact hBC) hCX
  rcases hg with hg | hg
  · refine ⟨g, List.mem_cons_of_mem _ (List.mem_append_left _ ?_), le_refl _⟩
    rw [hc0, comps_app]; exact List.mem_append_left _ hg
  · rcases hsa u hu g hg with h | h | h | ⟨d, hd, hgd⟩
    · subst h; exact ⟨C, List.mem_cons_self .., z_le _⟩
    · exact ⟨C, List.mem_cons_self .., le_trans h (le_of_lt hBC)⟩
    · exact ⟨C, List.mem_cons_self .., le_trans h (le_of_lt hOC)⟩
    · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_right _ hd), hgd⟩

/-- **`frameDom_prefix` with the components of `B` as a further bound**: every `C ∈ (B, B + R]` starts with
`B`, so the components of `B` are components of `C`. -/
theorem frameDom_prefixB {a B s R : T}
    (hsa : ∀ u, ¬ lt a u = true → ∀ g ∈ comps u s, g = z ∨ g ≤ B ∨ g ≤ psi s z z ∨
      (∃ d ∈ comps u B, g ≤ d) ∨ ∃ d ∈ comps u a, g ≤ d) :
    FrameDom a B s (app B R) := by
  intro u hu C hBC hOC hCX g hg
  obtain ⟨c0, hc0, _, _⟩ := between_app (A := B) (x := z) (y := R) (c := C)
    (by rw [app_z_right]; exact hBC) hCX
  have hBC' : ∀ d ∈ comps u B, d ∈ comps u C := by
    intro d hd; rw [hc0, comps_app]; exact List.mem_append_left _ hd
  rcases hg with hg | hg
  · exact ⟨g, List.mem_cons_of_mem _ (List.mem_append_left _ (hBC' g hg)), le_refl _⟩
  · rcases hsa u hu g hg with h | h | h | ⟨d, hd, hgd⟩ | ⟨d, hd, hgd⟩
    · subst h; exact ⟨C, List.mem_cons_self .., z_le _⟩
    · exact ⟨C, List.mem_cons_self .., le_trans h (le_of_lt hBC)⟩
    · exact ⟨C, List.mem_cons_self .., le_trans h (le_of_lt hOC)⟩
    · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_left _ (hBC' d hd)), hgd⟩
    · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_right _ hd), hgd⟩

/-- **FrameDom of a first frame** (`B = 0`) when the head subscript of `H` starts with `s`: every
`C ∈ (Ω_s, H]` has a head subscript `s + w₀`, so the components of `s` are components of `C`. -/
theorem frameDom_first {a s Hx X : T} (has : a ≤ s) (hX : lev Hx = app s X) :
    FrameDom a z s Hx := by
  intro u hu C _ hOC hCX g hg
  rcases hg with hg | hg
  · simp [comps] at hg
  cases C with
  | z => exact absurd hOC (not_lt_z _)
  | psi w c R =>
    have hsw : s ≤ w := by
      have := lev_le_of_le (le_of_lt hOC); simpa [lev] using this
    have hwX : w ≤ app s X := by
      have := lev_le_of_le hCX; rw [hX] at this; simpa [lev] using this
    obtain ⟨w0, hw0⟩ : ∃ w0, w = app s w0 := by
      rcases (le_iff _ _).mp hsw with h | h
      · obtain ⟨c0, hc0, _, _⟩ := between_app (A := s) (x := z) (y := X) (c := w)
          (by rw [app_z_right]; exact h) hwX
        exact ⟨c0, hc0⟩
      · exact ⟨z, by rw [app_z_right]; exact h.symm⟩
    have huw : ¬ lt w u = true := by
      intro h
      have hus : u ≤ s := le_of_not_gt (fun h' => hu (lt_of_le_of_lt has h'))
      exact lt_irrefl' _ (lt_of_lt_of_le (lt_of_lt_of_le h hus) hsw)
    refine ⟨g, List.mem_cons_of_mem _ (List.mem_append_left _ ?_), le_refl _⟩
    simp only [comps, if_neg huw, List.mem_append, List.mem_cons]
    left; right; right
    rw [hw0, comps_app]; exact List.mem_append_left _ hg

/-- The components of `V + 1` at a level `u ≤ V` are those of `V` and `z`. -/
theorem comps_succ_sub {V : T} (u : T) : ∀ g ∈ comps u (succ V), g = z ∨ g ∈ comps u V := by
  intro g hg
  rw [show succ V = app V one from rfl, comps_app] at hg
  rcases List.mem_append.mp hg with h | h
  · exact Or.inr h
  · left
    simp only [one, comps] at h
    split at h <;> simp at h <;> exact h

/-- At the level `V` itself, the components of `V + 1` are only `z`. -/
theorem comps_succ_self {V : T} (hV : isOT V = true) : ∀ g ∈ comps V (succ V), g = z := by
  intro g hg
  rcases comps_succ_sub V g hg with h | h
  · exact h
  · rw [comps_eq_nil_of_lev (fun q hq => lev_lt_of_summand hV hq)] at h; simp at h

/-! ## qr -/

open Classical in
/-- **The last frame of the seed `r` in `M[n]`** (qr): the data that closure's `seed_frames_qr` reads. -/
theorem seed_last_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) (hRes : T2SeedQRRes M ρ r L Lc)
    {τ0 : Valn} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : ∃ rk0, Rk (M.take (r + L)) rk0)
    (n : Nat) (hn : 2 ≤ n)
    (hGlow : ∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ)
    (σ : Valn) (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ) :
    ∃ Y, σ.o (r + L) = psi (succ (ρ.v r)) Y z ∧
      ((n = 2 ∧ ¬ t2B (ρ.v r) ρ Lc < Y) ∨
        (3 ≤ n ∧ Y = sh (ρ.v r) (succ (ρ.v r)) (seqZ (ρ.v r) (t2B (ρ.v r) ρ Lc)
          (t2W1 (M.take (r + L)) (ρ.v r) τ0 r) (n - 3)))) ∧
      CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = Lc ++ [r + L] ∧
      σ.v r = ρ.v r ∧ ∀ d ∈ Lc, σ.o d = ρ.o d := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hRk : ∀ m, 1 ≤ m → ∃ rk', Rk (TRIO.gexp M r L d0 d1 m) rk' := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have hn2 : n = 2 := by omega
    subst hn2
    have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
    have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hC0
    have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := hGlow 1 (le_refl 1) (by omega) τ0 hCP
    obtain ⟨rk0, hRk0⟩ := hR0
    have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hRk0
    obtain ⟨hCLN, hvr, hLc, hox⟩ :=
      G.seed_frame_data_qr hM hS I R hz h2 hlen hr hq hXu hCLM (le_refl 2) hCN hRN hCP hGP hRP
    rw [← hd0def, ← hd1def] at hCLN hox
    rw [show (2 - 1 : Nat) = 1 from rfl, hP1] at hox
    exact ⟨_, hox, Or.inl ⟨rfl, hRes.w1 τ0 hC0⟩, hCLN, hvr, hLc⟩
  · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
    have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
    have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
    obtain ⟨hCLN, hvr, hLc, hox⟩ :=
      G.seed_frame_data_qr hM hS I R hz h2 hlen hr hq hXu hCLM hn hCN hRN hCP hGP hRP
    rw [← hd0def, ← hd1def] at hCLN hox
    have hval := seed_r_value_qr hM hS I R hz h2 hlen hr hq hXu hCLM hRes hC0 ⟨_, hR0.choose_spec⟩ (n - 1)
      (by omega) (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP
    have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
    have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
      have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
      omega
    have hform := o_cl_eq hCP hGP hrP
    rw [hval] at hform
    simp only [psi.injEq] at hform
    have h21 := hform.2.1
    rw [← hform.1] at h21
    rw [← hform.1, ← h21, show n - 1 - 2 = n - 3 by omega] at hox
    exact ⟨_, hox, Or.inr ⟨hn3, rfl⟩, hCLN, hvr, hLc⟩

open Classical in
/-- **The seed frames of `r` in `M[n]`** (qr) for `QVSF`, `QFO` and `QFCo`, from the same data. -/
theorem seed_frames_qr3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) (hRes : T2SeedQRRes M ρ r L Lc)
    {τ0 : Valn} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : ∃ rk0, Rk (M.take (r + L)) rk0) :
    G.SeedFr QVSF M r L r ∧ G.SeedFr QFO M r L r ∧ G.SeedFr QFCo M r L r := by
  have hrM : r < M.length := by have := par_lt M 0 _ _ hq; omega
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hrx : r < r + L := par_lt M 0 _ _ hq
  obtain ⟨hBc, hBot, _⟩ := qr_M_side I hlen hrx hCLM
  have hσB := tame_sigmaB_std hM hS I hlen hr hq hXu hCLM
  have hQV := clField_of_vsmallF I.cons I.good I.vs r hrM
  have hQO : CLField QFO M ρ := I.fo
  have hQC := clField_QFCo I.good I.fc r hrM
  refine ⟨fun n hn hGlow σ hCN hGN => ?_, fun n hn hGlow σ hCN hGN => ?_, fun n hn hGlow σ hCN hGN => ?_⟩
  all_goals obtain ⟨Y, hox, hcase, hCLN, hvr, hLc⟩ :=
    seed_last_qr hM hS I R hz h2 hlen hr hq hXu hCLM hRes hC0 hR0 n hn hGlow σ hCN
  · -- VSmallF: at the level `V` the subscript `V + 1` has only the component `z`
    refine G.seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => hQV Lc' c R' h) ?_
    rw [hox]
    intro s y hsy g hg
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, -⟩ := hsy
    left; rw [comps_succ_self hVot g hg]; exact z_le _
  · -- FrameOT: the state before the last child is that of `M`
    exact G.seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => hQO r hrM Lc' c R' h)
      (hQO r hrM Lc (r + L) [] hCLM)
  · -- FrameClosed: no rewrite at `n = 2`; at `n ≥ 3` the new state extends `B`
    refine G.seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => hQC Lc' c R' h) ?_
    have hxN : r + L < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n).length := by
      rw [TRIO.gexp_length hlen]
      have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
      omega
    refine ⟨hGN.ot_o _ hxN, ?_⟩
    rw [hox]
    intro s y hsy ht
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, rfl, -⟩ := hsy
    rcases hcase with ⟨_, hnr⟩ | ⟨hn3, hY⟩
    · exact absurd ht.1 hnr
    · have hot : isOT (psi (succ (ρ.v r)) Y z) = true := by rw [← hox]; exact hGN.ot_o _ hxN
      have hall : ∀ q ∈ summands Y, ¬ q < psi (succ (succ (ρ.v r))) z z := by
        rw [hY]; exact G.sh_seqZ_allGe hVot hσB hBc hRes.ks (n - 3)
      have hH : H (succ (ρ.v r)) Y = Y := by
        rw [H_eq hot, split_all_ge hall]; simp
      have hsz := G.sh_seqZ hVot hσB hBc hRes.ks (W1 := t2W1 (M.take (r + L)) (ρ.v r) τ0 r) (n - 3)
      rw [hH, hY, show t2B (ρ.v r) ρ Lc = spArg (ρ.v r) z (sumN (Lc.map ρ.o)) from rfl, hsz]
      apply frameDom_prefix
      intro u hu g hg
      rcases comps_succ_sub u g hg with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr ⟨g, h, le_refl _⟩))

/-- **FrameDom when the subscript is the parent's**: the components of `s = a` are components of `a`. -/
theorem frameDom_self {a B X : T} (hB : ∀ u, ¬ lt a u = true → comps u B = []) : FrameDom a B a X := by
  intro u hu C _ _ _ g hg
  rcases hg with hg | hg
  · rw [hB u hu] at hg; simp at hg
  · exact ⟨g, List.mem_cons_of_mem _ (List.mem_append_right _ hg), le_refl _⟩

/-! ## qn -/

/-- **The residual of the qn seed frames**: the components of `s′ = v_N(q)` at the levels `u ≤ V`. With a
state before `q` (`Lc ≠ []`) they are `0`, below `B`, below `Ω_{s′}`, below a component of `B` or below a component of `V`
(2026-10-21: the form without the components of `B` is false on a standard matrix; FrameDom only needs this one); at the level `V` they are below `Ω_{s′}` or `B`
（実測: 9 集合で例外 0）. -/
def T2SeedQNDom (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop :=
  (Lc ≠ [] → ∀ u, ¬ lt (ρ.v r) u = true → ∀ g ∈ comps u (qnS M ρ r L q),
    g = z ∨ g ≤ t2B (ρ.v r) ρ Lc ∨ g ≤ psi (qnS M ρ r L q) z z ∨
      (∃ d ∈ comps u (t2B (ρ.v r) ρ Lc), g ≤ d) ∨ ∃ d ∈ comps u (ρ.v r), g ≤ d) ∧
  ∀ g ∈ comps (ρ.v r) (qnS M ρ r L q), g ≤ psi (qnS M ρ r L q) z z ∨ g ≤ t2B (ρ.v r) ρ Lc

open Classical in
/-- **The frames of the seeds `r` and `q` in `M[n]`** (qn): the data that closure's `seed_frames_qn` reads.
`o_N(q) = ψ_{s′}(B + Ω_{f(t)})` with every summand at least `Ω_{s′+1}`, and with `Lc = []` the subscript `f(t)`
starts with `s′` (`T2SeedQNFC`). -/
theorem seed_last_qn {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) (hRes : T2SeedQNRes M ρ r L q Lc)
    {τ0 : Valn} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : ∃ rk0, Rk (M.take (r + L)) rk0)
    (n : Nat) (hn : 2 ≤ n)
    (hGlow : ∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ)
    (σ : Valn) (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ) :
    ∃ ft, CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = Lc ++ [q] ∧
      CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) q = [r + L] ∧
      σ.v r = ρ.v r ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧ σ.v (r + L) = qnS M ρ r L q ∧
      σ.v q = qnS M ρ r L q ∧
      σ.o q = psi (qnS M ρ r L q) (app (t2B (ρ.v r) ρ Lc) (psi ft z z)) z ∧
      (∀ g ∈ summands (app (t2B (ρ.v r) ρ Lc) (psi ft z z)), ¬ g < psi (succ (qnS M ρ r L q)) z z) ∧
      (Lc = [] → ∃ X, X ≠ z ∧ ft = app (qnS M ρ r L q) X) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set V := ρ.v r with hVdef
  set B := t2B V ρ Lc with hBdef
  set s' := qnS M ρ r L q with hs'def
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hpq : par M 0 q = some r := (mem_children_iff.mp (cl_mem_children hqcl)).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hRk : ∀ m, 1 ≤ m → ∃ rk', Rk (TRIO.gexp M r L d0 d1 m) rk' := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hs'ot : isOT s' = true := qnS_ot I hrM L q
  have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
  have hv0 := v_take_of_untopped I hlen (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hC0
  obtain ⟨t1, ht1, hch⟩ := hRes.base τ0 hC0
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  have hvq : σ.v q = s' := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  obtain ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩ : CL (TRIO.gexp M r L d0 d1 n) r = Lc ++ [q] ∧
      CL (TRIO.gexp M r L d0 d1 n) q = [r + L] ∧ σ.v r = V ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧
      σ.v (r + L) = s' ∧
      σ.o q = psi s' (step s' z s' (sh V s' (app B (psi (tqN V s' t1 (n - 2)) z z))) z) z := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn2 : n = 2 := by omega
      subst hn2
      have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hC0
      have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := hGlow 1 (le_refl 1) (by omega) τ0 hCP
      obtain ⟨rk0, hRk0⟩ := hR0
      have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hRk0
      obtain ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩ :=
        G.seed_frame_data_qn hM hS I R hz h2 hlen hr hq hqr hCLM (le_refl 2) hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hCLNq hoq
      rw [show (2 - 1 : Nat) = 1 from rfl, hP1, ht1, hv0] at hoq
      rw [hvq, qnS_vxs] at hvx
      rw [hvq, hvx, G.spArg_nil] at hoq
      exact ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      obtain ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩ :=
        G.seed_frame_data_qn hM hS I R hz h2 hlen hr hq hqr hCLM hn hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hCLNq hoq
      have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
      have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hqP : q < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hval := seed_r_value_qn hM hS I R hz h2 hlen hr hq hqr hCLM hRes hC0 hR0 hv0 ht1
        (fun k => ⟨(hch k).1, (hch k).2.1⟩) (n - 1) (by omega)
        (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP (hGP.ot_o q hqP) (cl_vals hCP hGP hrP).2
      have hform := o_cl_eq hCP hGP hrP
      rw [hval] at hform
      simp only [psi.injEq] at hform
      have h21 := hform.2.1
      rw [← hform.1] at h21
      rw [← hform.1, ← h21, show n - 1 - 1 = n - 2 by omega] at hoq
      rw [hvq, qnS_vxs] at hvx
      rw [hvq, hvx, G.spArg_nil] at hoq
      exact ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩
  set t := tqN V s' t1 (n - 2) with htdef
  have hat : V < t := (hch (n - 2)).1
  have hts : ¬ shf V s' t < succ s' := (hch (n - 2)).2.1
  have hσB := hRes.σB
  have hBc := hRes.Bc
  have hhigh : ∀ g ∈ summands (app B (psi (shf V s' t) z z)), ¬ g < psi (succ s') z z := by
    intro g hg
    rw [summands_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hBc g hg
    · simp [summands] at hg; rw [hg]
      intro hlt
      rw [psi_lt_psi_z_iff] at hlt
      rcases hlt with h | ⟨_, h⟩
      · exact hts h
      · exact T.not_lt_z _ h
  have hinner : step s' z s' (sh V s' (app B (psi t z z))) z = app B (psi (shf V s' t) z z) := by
    rw [sh_app, hσB, sh_psi_gt hat, sh_z]
    have hne : app B (psi (shf V s' t) z z) ≠ z := by
      intro h; cases hB : B with
      | z => rw [hB] at h; simp at h
      | psi _ _ _ => rw [hB] at h; simp at h
    have hzlt : z < app B (psi (shf V s' t) z z) := by
      cases h : app B (psi (shf V s' t) z z) with
      | z => exact absurd h hne
      | psi _ _ _ => exact T.z_lt_psi _ _ _
    unfold step
    rw [if_pos ⟨hzlt, psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hzlt⟩)⟩]
    exact H_of_high hs'ot hhigh
  rw [hinner] at hoq
  refine ⟨shf V s' t, hCLN, hCLNq, hvr, hLc, hvx, hvq, hoq, hhigh, fun hLc0 => ?_⟩
  obtain ⟨X, hX0, hXe⟩ := G.t2SeedQNFC_holds hM hS I R hlen hr hq hqr hCLM hLc0 τ0 hC0 t1 ht1 (n - 2)
  exact ⟨X, hX0, hXe⟩

open Classical in
/-- **The seed frames of `r` and `q` in `M[n]`** (qn) for `QVSF`, `QFO` and `QFCo`. -/
theorem seed_frames_qn3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) (hRes : T2SeedQNRes M ρ r L q Lc)
    (hDom : T2SeedQNDom M ρ r L q Lc)
    {τ0 : Valn} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : ∃ rk0, Rk (M.take (r + L)) rk0) :
    ∀ i, (i = r ∨ i = q) → G.SeedFr QVSF M r L i ∧ G.SeedFr QFO M r L i ∧ G.SeedFr QFCo M r L i := by
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hpq : par M 0 q = some r := (mem_children_iff.mp (cl_mem_children hqcl)).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hs'ot : isOT (qnS M ρ r L q) = true := qnS_ot I hrM L q
  have hVs' : ρ.v r < qnS M ρ r L q := qnS_gt M ρ r L q
  have hQV := clField_of_vsmallF I.cons I.good I.vs r hrM
  have hQO : CLField QFO M ρ := I.fo
  have hQC := clField_QFCo I.good I.fc r hrM
  intro i hi
  refine ⟨fun n hn hGlow σ hCN hGN => ?_, fun n hn hGlow σ hCN hGN => ?_, fun n hn hGlow σ hCN hGN => ?_⟩
  all_goals
    obtain ⟨ft, hCLN, hCLNq, hvr, hLc, hvx, hvq, hoq, hhigh, hfc⟩ :=
      seed_last_qn hM hS I R hz h2 hlen hr hq hqr hCLM hRes hC0 hR0 n hn hGlow σ hCN
    have hxN : r + L < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n).length := by
      rw [TRIO.gexp_length hlen]
      have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
      omega
    have hqN : q < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n).length := by omega
    obtain ⟨y0, hy0⟩ := o_psi_sub hCN hxN
    rw [sf_ot (hGN.ot_v _ hxN), hvx] at hy0
    have hfrq : ∀ {Q : T → List T → T → Prop}, Q (σ.v q) [] (σ.o (r + L)) →
        ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat),
          CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) q =
            Lc' ++ c :: R' → Q (σ.v q) (Lc'.map σ.o) (σ.o c) := by
      intro Q h Lc' c R' hCL
      rw [hCLNq] at hCL
      rcases Lc' with _ | ⟨a, l⟩
      · simp at hCL; rw [← hCL.1]; exact h
      · simp at hCL
    rcases hi with hi | hi <;> subst i
  · -- VSmallF, the frames of `r`
    refine G.seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => hQV Lc' c R' h) ?_
    rw [hoq]
    intro s y hsy g hg
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, -⟩ := hsy
    exact hDom.2 g hg
  · -- VSmallF, the frame of `q`: the subscript is `v(q)`, which has no components at its own level
    refine hfrq ?_
    rw [hy0, hvq]
    intro s y hsy g hg
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, -⟩ := hsy
    rw [comps_eq_nil_of_lev (fun q hq => lev_lt_of_summand hs'ot hq)] at hg; simp at hg
  · -- FrameOT, the frames of `r`
    exact G.seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => hQO r hrM Lc' c R' h)
      (hQO r hrM Lc q [] hCLM)
  · -- FrameOT, the frame of `q`
    refine hfrq ?_
    show isOT (psi (σ.v q) (spArg (σ.v q) z (sumN ([] : List T))) z) = true
    rw [G.spArg_nil, hvq]
    exact isOT_psi_zz hs'ot
  · -- FrameClosed, the frames of `r`
    refine G.seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => hQC Lc' c R' h) ⟨hGN.ot_o q hqN, ?_⟩
    rw [hoq]
    intro s y hsy _
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, rfl, -⟩ := hsy
    rw [H_of_high hs'ot hhigh]
    by_cases hL0 : Lc = []
    · obtain ⟨X, _, hX⟩ := hfc hL0
      have hB : t2B (ρ.v r) ρ Lc = z := by rw [hL0]; rfl
      show FrameDom (ρ.v r) (t2B (ρ.v r) ρ Lc) _ _
      rw [hB, app_z]
      exact frameDom_first (le_of_lt hVs') (by rw [lev_psi, hX])
    · exact frameDom_prefixB (hDom.1 hL0)
  · -- FrameClosed, the frame of `q`: the child's subscript is `v(q)`
    refine hfrq ⟨hGN.ot_o _ hxN, ?_⟩
    rw [hy0, hvq]
    intro s y hsy _
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, -⟩ := hsy
    exact frameDom_self (fun u _ => by rw [G.spArg_nil]; rfl)

end Ytosk
