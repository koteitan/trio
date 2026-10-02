/-
**3 行・t = 1: TrigOm の保存のための順序数の補題。**

D の値 ψ_s(y) は fsD で下がる。下がった値の引数 fsD(y, ζ) が Ω_{ν+1} の形なら、元の y も Ω_{t+1} の形
（`hole_om_shape`）。穴が対角点（DiagAt）なら fsD は Ω の形にならない（`diag_fsD_not_om`）。
穴が大きい共終数なら、fs(y, ζ) が Ω の形になるのは y = Ω_{t+1} のときだけ（`fs_om_shape`）。
ただし ζ が後続でない（ζ ≠ 1）ことが要る: ζ = 1 だと fs(Ω_1, 1) = 1 で、y = Ω_{Ω_1} から Ω_1 ができる。
-/
import Ytosk.V3FrameClN
import Ytosk.V3TP1
import Ytosk.V3QRFinal4

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem isSucc_psi_z' {a b : T} (h : a ≠ z ∨ b ≠ z) : isSucc (psi a b z) = false := by
  unfold isSucc last
  rcases h with h | h <;> simp [one, h]

theorem count_pos {η : T} (h : η ≠ z) : 0 < count η := by
  cases η with
  | z => exact absurd rfl h
  | psi _ _ _ => simp [count]

/-- `fs` of a term of big cofinality at a non-successor index is not a successor. -/
theorem fs_not_succ_big : ∀ {a μ η : T}, cof a = .big μ → η ≠ z → isSucc η = false →
    isSucc (fs a η) = false
  | z, _, _, h, _, _ => by simp [cof] at h
  | psi p q (psi c d e), μ, η, h, hη, hs => by
    have hc : cof (psi c d e) = .big μ := by simpa [cof] using h
    show isSucc (psi p q (fs (psi c d e) η)) = false
    rw [isSucc_psi_rest _ _ _ (fs_ne_z_big hc hη)]
    exact fs_not_succ_big hc hη hs
  | psi p q z, μ, η, h, hη, hs => by
    unfold fs
    unfold cof at h
    by_cases hq : q = z
    · subst hq
      rw [if_pos rfl] at h ⊢
      by_cases hp : p = z
      · rw [if_pos hp] at h; cases h
      · rw [if_neg hp] at h ⊢
        by_cases hps : isSucc p = true
        · rw [if_pos hps]; exact hs
        · rw [if_neg hps] at h ⊢
          exact isSucc_psi_z' (Or.inl (fs_ne_z_big h hη))
    · rw [if_neg hq] at h ⊢
      by_cases hqs : isSucc q = true
      · rw [if_pos hqs] at h; cases h
      · rw [if_neg hqs] at h ⊢
        cases hcq : cof q with
        | big ν =>
          simp only
          split
          · exact isSucc_psi_z' (Or.inr (fs_ne_z_big hcq hη))
          · apply isSucc_psi_z' (Or.inr _)
            apply fs_ne_z_big hcq
            obtain ⟨k, hk⟩ : ∃ k, count η = k + 1 := ⟨count η - 1, by have := count_pos hη; omega⟩
            rw [hk]; simp
        | zero => rw [hcq] at h; cases h
        | succ => rw [hcq] at h; cases h
        | omega => rw [hcq] at h; cases h

/-- `fs(y, ζ)` (big cofinality) is `Ω_{ν+1}` only when `y` is some `Ω_{t+1}`. -/
theorem fs_om_shape : ∀ {y μ ζ ν : T}, cof y = .big μ → ζ ≠ z → isSucc ζ = false →
    fs y ζ = psi (succ ν) z z → ∃ t, y = psi (succ t) z z
  | z, _, _, _, h, _, _, _ => by simp [cof] at h
  | psi p q (psi c d e), μ, ζ, ν, h, hζ, _, he => by
    have hc : cof (psi c d e) = .big μ := by simpa [cof] using h
    have : fs (psi p q (psi c d e)) ζ = psi p q (fs (psi c d e) ζ) := rfl
    rw [this] at he
    exact absurd (T.psi.inj he).2.2 (fs_ne_z_big hc hζ)
  | psi p q z, μ, ζ, ν, h, hζ, hs, he => by
    unfold fs at he
    unfold cof at h
    by_cases hq : q = z
    · subst hq
      rw [if_pos rfl] at h he
      by_cases hp : p = z
      · rw [if_pos hp] at h; cases h
      · rw [if_neg hp] at h he
        by_cases hps : isSucc p = true
        · exact ⟨init p, by rw [show succ (init p) = p from init_app_one hps]⟩
        · rw [if_neg hps] at h he
          have h1 := (T.psi.inj he).1
          have h2 := fs_not_succ_big h hζ hs
          rw [h1, isSucc_succ] at h2; cases h2
    · rw [if_neg hq] at h he
      by_cases hqs : isSucc q = true
      · rw [if_pos hqs] at h; cases h
      · rw [if_neg hqs] at h he
        cases hcq : cof q with
        | big ν' =>
          rw [hcq] at he
          simp only at he
          split at he
          · exact absurd (T.psi.inj he).2.1 (fs_ne_z_big hcq hζ)
          · exfalso
            apply fs_ne_z_big hcq _ (T.psi.inj he).2.1
            obtain ⟨k, hk⟩ : ∃ k, count ζ = k + 1 := ⟨count ζ - 1, by have := count_pos hζ; omega⟩
            rw [hk]; simp
        | zero => rw [hcq] at h; cases h
        | succ => rw [hcq] at h; cases h
        | omega => rw [hcq] at h; cases h

/-- At a diagonal position, `fsD` is neither `Ω_{ν+1}` nor a successor. -/
theorem diag_fsD_not_om {a b μ ζ : T} (hζ : ζ ≠ z) {t : T} (hD : DiagAt a b μ t) :
    (∀ ν, fsD t ζ ≠ psi (succ ν) z z) ∧ isSucc (fsD t ζ) = false := by
  have hne : ∀ {t'}, DiagAt a b μ t' → fsD t' ζ ≠ z := fun h' =>
    fsD_ne_z_of_holeT (μ := μ) (br := b) (vr := a) hζ (Or.inr ⟨a, lt_irrefl' a, h'⟩)
  induction hD with
  | here hb hc _ =>
    rw [fsD_here hb hc]
    exact ⟨fun ν h => fs_ne_z_big hc hζ (T.psi.inj h).2.1, isSucc_psi_z' (Or.inr (fs_ne_z_big hc hζ))⟩
  | @rest a' b' c d e h' ih =>
    have : fsD (psi a' b' (psi c d e)) ζ = psi a' b' (fsD (psi c d e) ζ) := rfl
    rw [this]
    exact ⟨fun ν h => hne h' (T.psi.inj h).2.2,
      by rw [isSucc_psi_rest _ _ _ (hne h')]; exact ih.2⟩
  | @arg a' b' hb hs h' _ =>
    rw [fsD_psi hb hs]
    exact ⟨fun ν h => hne h' (T.psi.inj h).2.1, isSucc_psi_z' (Or.inr (hne h'))⟩
  | @sub a' ha hs h' ih =>
    rw [fsD_sub ha hs]
    refine ⟨fun ν h => ?_, isSucc_psi_z' (Or.inl (hne h'))⟩
    have h1 := (T.psi.inj h).1
    have h2 := ih.2
    rw [h1, isSucc_succ] at h2; cases h2

/-- **The shape of a lowered value**: under a hole, if `fsD(ψ_s(y), ζ)` has the argument `Ω_{ν+1}`
(and `ζ` is not a successor), then `y` is some `Ω_{t+1}`. -/
theorem hole_om_shape {μ br vr s y ζ s' ν : T} (hH : HoleT μ br vr (psi s y z)) (hy : y ≠ z)
    (hζ : ζ ≠ z) (hζs : isSucc ζ = false)
    (h : fsD (psi s y z) ζ = psi s' (psi (succ ν) z z) z) : ∃ t, y = psi (succ t) z z := by
  rcases hH with hc | ⟨a', _, hD⟩
  · obtain ⟨hcy, _⟩ := cof_psi_inv hy hc
    rw [fsD_here hy hcy] at h
    exact fs_om_shape hcy hζ hζs (T.psi.inj h).2.1
  · cases hD with
    | here hb hc _ =>
      rw [fsD_here hb hc] at h
      exact fs_om_shape hc hζ hζs (T.psi.inj h).2.1
    | arg hb hs h' =>
      rw [fsD_psi hb hs] at h
      exact absurd (T.psi.inj h).2.1 ((diag_fsD_not_om hζ h').1 ν)
    | sub ha hs h' => exact absurd rfl hy

/-- **No trigger at an uncounted child** (C′ で 91 万件、例外 0: のりしろの子は v の条件で、上げの先は頭 ≥ y で). -/
def NoTrigU (M : Mat) (ρ : Valn) : Prop :=
  ∀ i L c R, children M i = L ++ c :: R → ¬ Counted M i c → ∀ s y, ρ.o c = psi s y z →
    ¬ (lt (preState M ρ i L) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true)

theorem trigOmC_of {M : Mat} {ρ : Valn} (h : TrigOm M ρ) : TrigOmC M ρ :=
  fun i L c R hch _ => h i L c R hch

theorem trigOm_of_C {M : Mat} {ρ : Valn} (h : TrigOmC M ρ) (hNU : NoTrigU M ρ) : TrigOm M ρ := by
  intro i L c R hch s ν hc ht1 ht2
  by_cases hcn : Counted M i c
  · exact h i L c R hch hcn s ν hc ht1 ht2
  · exact absurd ⟨ht1, ht2⟩ (hNU i L c R hch hcn s _ hc)

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L → entry M 1 r < entry M 1 s)
  (hx2 : entry M 2 (r + L) = 0)
  (hxnb : ∀ c, par M 0 (r + L) = some c →
    col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
  (hz2 : entry M 2 r ≤ 1)
  (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
  (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
  {ρ ρP : Valn} {Z : Nat → T}
  (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
include hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hOS

/-- **The head before a counted child, before `x`, is that of `M`.** -/
theorem preState_lt {i : Nat} (h : i < r + L) {Lc : List Nat} {c : Nat} {R : List Nat}
    (hch : children M i = Lc ++ c :: R) (hcnt : Counted M i c) :
    (glueZ M (r + L) ρ (shiftV ρP L) Z).v i = ρ.v i ∧
      preState (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) i Lc = preState M ρ i Lc := by
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hS := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux i h
  have hcch : c ∈ children M i := by rw [hch]; simp
  have hvd : ¬ DepX M (r + L) false i := by
    intro hv
    rcases hOS i h (DepX.ov hv) with ⟨_, hnc⟩ | ⟨hnv, _⟩
    · rcases hnc c hcch with h' | h'
      · exact hcnt.1 h'
      · exact hcnt.2 h'
    · exact hnv hv
  have hv : σ.v i = ρ.v i := by rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z h hvd]
  refine ⟨hv, ?_⟩
  unfold preState
  rw [hv]
  congr 3
  apply List.map_congr_left
  intro d hd
  have hdch : d ∈ children M i := by rw [hch]; simp [hd]
  rw [hS.cnt d hdch σ]
  have hdc : d < c := by
    have hsort := children_sorted M i
    rw [hch] at hsort
    exact (List.pairwise_append.mp hsort).2.2 d hd c List.mem_cons_self
  by_cases hdcnt : Counted M i d
  · rw [cnt_cnt σ hdcnt.1 hdcnt.2, cnt_cnt ρ hdcnt.1 hdcnt.2]
    have hdD : ¬ DepX M (r + L) true d := by
      intro hdD
      have hiD : DepX M (r + L) true i := DepX.ochild hdch hdcnt.1 hdcnt.2 hdD
      rcases hOS i h hiD with ⟨hv', _⟩ | ⟨_, L', c', R', hch', _, _, hR', hL'⟩
      · exact hvd hv'
      · have hdc' : d = c' := by
          rw [hch'] at hdch
          rcases List.mem_append.mp hdch with h' | h'
          · exact absurd hdD (hL' d h' hdcnt)
          · rcases List.mem_cons.mp h' with h' | h'
            · exact h'
            · rcases hR' d h' with h'' | h''
              · exact absurd h'' hdcnt.1
              · exact absurd h'' hdcnt.2
        subst hdc'
        have hsort := children_sorted M i
        rw [hch'] at hsort hcch
        rcases List.mem_append.mp hcch with h' | h'
        · have := (List.pairwise_append.mp hsort).2.2 c h' d List.mem_cons_self
          omega
        · rcases List.mem_cons.mp h' with h' | h'
          · omega
          · rcases hR' c h' with h'' | h''
            · exact hcnt.1 h''
            · exact hcnt.2 h''
    have hdx : d < r + L := by
      have := (mem_children hcch).2; omega
    rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hdx hdD]
  · have : col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true) := by
      by_cases h1 : col M d = bump M i
      · exact Or.inl h1
      · right; by_contra h2; exact hdcnt ⟨h1, h2⟩
    rw [cnt_unc σ this, cnt_unc ρ this]


/-- **TrigOm passes to the glued valuation of `M[n]`** (`t = 1`): the head is that of `M` (or of `M[n − 1]`
on the copies). A lowered child keeps an `Ω_{t+1}` argument (hypothesis `hShape`: from `hole_om_shape` when
`Z c` is not a successor, or from the diagonal point for `q = r`),
so the trigger goes back to `M` (`trig_back_fsD`). Remaining as hypotheses: the children whose old value is
`Ω_{t+1}` itself (`x`, and `D` leaves) `hLeaf`. Stated for counted children (`TrigOmC`); with `NoTrigU` it gives
`TrigOm` (`trigOm_of_C`). -/
theorem trigOm_N_t1 (hC : Cons M ρ) (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hTO : TrigOmC M ρ) (hTOP : TrigOmC (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hShape : ∀ c, c < r + L → DepX M (r + L) true c → ∀ s0 y0, ρ.o c = psi s0 y0 z → y0 ≠ z →
      ∀ s ν, fsD (psi s0 y0 z) (Z c) = psi s (psi (succ ν) z z) z → ∃ t, y0 = psi (succ t) z z)
    (hle : ∀ c, c < r + L → DepX M (r + L) true c → fsD (ρ.o c) (Z c) ≤ ρ.o c)
    (hLeaf : ∀ i Lc c R, i < r + L → children M i = Lc ++ c :: R → Counted M i c → c ≤ r + L →
      DepX M (r + L) true c → ∀ t, ρ.o c = psi (succ t) z z → ∀ s ν,
      (glueZ M (r + L) ρ (shiftV ρP L) Z).o c = psi s (psi (succ ν) z z) z →
      lt (preState M ρ i Lc) (psi (succ ν) z z) = true →
      lt (psi (ρ.v i) z z) (psi s (psi (succ ν) z z) z) = true → preState M ρ i Lc = z)
    (hox : ∃ t, ρ.o (r + L) = psi (succ t) z z) :
    TrigOmC (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) := by
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  intro i Lc c R hch hcN s ν hc ht1 ht2
  have hcmem : c ∈ children (TRIO.gexp M r L d0 0 n) i := by rw [hch]; simp
  have hcl := mem_children hcmem
  rcases Nat.lt_or_ge i (r + L) with h | h
  · have hS := hSA i h
    rw [hS.ch] at hch hcmem
    have hcM : Counted M i c := (counted_iff_of_cnt (hS.cnt c hcmem)).mp hcN
    obtain ⟨hv, hpre⟩ := preState_lt hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux (ρ := ρ) (ρP := ρP)
      (Z := Z) hOS h hch hcM
    rw [← hσ] at hv hpre
    rw [hpre] at ht1 ⊢
    rw [hv] at ht2
    have hcx : c ≤ r + L := by have := (mem_children hcmem).2; omega
    by_cases hd : DepX M (r + L) true c
    · rcases Nat.lt_or_ge c (r + L) with hc' | hc'
      · obtain ⟨s0, y0, h0⟩ := o_psi_form hC (show c < M.length by omega)
        rw [hσ, glueZ_o_dep ρ (shiftV ρP L) Z hc' hd, h0] at hc
        by_cases hy0 : y0 = z
        · subst hy0
          by_cases hs0 : s0 = z
          · subst hs0; unfold fsD at hc; simp at hc
          by_cases hss : isSucc s0 = true
          · have hs' : s0 = succ (init s0) := (init_app_one hss).symm
            refine hLeaf i Lc c R h hch hcM hcx hd (init s0) (by rw [h0, ← hs']) s ν ?_ ht1 ht2
            rw [hσ, glueZ_o_dep ρ (shiftV ρP L) Z hc' hd, h0]; exact hc
          · rw [fsD_sub hs0 (by simpa using hss)] at hc
            exact absurd (T.psi.inj hc).2.1 (by simp)
        · obtain ⟨t, ht⟩ := hShape c hc' hd s0 y0 h0 hy0 s ν hc
          have hl := hle c hc' hd
          rw [h0] at hl
          rcases trig_back_fsD hl hc ⟨ht1, ht2⟩ with htM | ⟨_, _, hy0z, _⟩
          · rw [ht] at htM
            exact hTO i Lc c R hch hcM s0 t (by rw [h0, ht]) htM.1 htM.2
          · exact absurd hy0z hy0
      · have hcx' : c = r + L := by omega
        obtain ⟨t, hto⟩ : ∃ t, ρ.o c = psi (succ t) z z := by rw [hcx']; exact hox
        exact hLeaf i Lc c R h hch hcM hcx hd t hto s ν hc ht1 ht2
    · have hc' : c < r + L := by
        rcases Nat.lt_or_ge c (r + L) with h' | h'
        · exact h'
        · exact absurd (show c = r + L by omega ▸ DepX.leaf) hd
      rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hc' hd] at hc
      exact hTO i Lc c R hch hcM s ν hc ht1 ht2
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    have hσo : ∀ b, σ.o (r + L + b) = ρP.o (r + b) := by
      intro b; rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
      show ρP.o (r + L + b - L) = ρP.o (r + b); congr 1; omega
    have hσv : σ.v (r + L + a) = ρP.v (r + a) := by
      rw [hσ, glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
      show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
    rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha] at hch
    obtain ⟨Lc', T', hsplit, hLc, hT⟩ := List.map_eq_append_iff.mp hch
    obtain ⟨c', R', hT', hc', hR⟩ := List.map_eq_cons_iff.mp hT
    subst hLc hc' hR
    rw [hT'] at hsplit
    have hc'm : c' ∈ children (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp
    have hc'l := mem_children hc'm
    rw [hlP] at hc'l
    have hpre : preState (TRIO.gexp M r L d0 0 n) σ (r + L + a) (Lc'.map (· + L)) =
        preState (TRIO.gexp M r L d0 0 (n - 1)) ρP (r + a) Lc' := by
      unfold preState
      rw [hσv, List.map_map]
      congr 3
      apply List.map_congr_left
      intro d hd
      have hdm : d ∈ children (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp [hd]
      exact cnt_copy hlen hL hA hd0e hn hpath hz2 ha hdm
    have hco : σ.o (c' + L) = ρP.o c' := by
      have := hσo (c' - r)
      rw [show r + L + (c' - r) = c' + L by omega, show r + (c' - r) = c' by omega] at this
      exact this
    rw [hpre] at ht1 ⊢
    rw [hσv] at ht2
    rw [hco] at hc
    have hcntP : Counted (TRIO.gexp M r L d0 0 (n - 1)) (r + a) c' := by
      have hcmN : c' + L ∈ children (TRIO.gexp M r L d0 0 n) (r + L + a) := by
        rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha]; exact List.mem_map_of_mem hc'm
      refine (counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath hz2 (ρ := ρ) (Z := Z) ha hc'm)
        hco ?_).mp hcN
      obtain ⟨s1, y1, he⟩ := o_psi_form hCP (i := c') (by rw [hlP]; omega)
      rw [he]; simp
    exact hTOP (r + a) Lc' c' R' hsplit hcntP s ν hc ht1 ht2

end

end Ytosk
