/-
**t = 2 の種の列の枠（T2SeedFrames）の振り分け（closure、2026-10-12）。**

種の列 i（T2SeedCol）は次の 4 つの場合に分かれる（x = r + L、q = P_0(x)）。
- qr: q = r で x へ上げる列がない。このとき CL_M(r) = Lc ++ [x]。
- sv: q = r で x − 1 が x へ上げる（x へ上げる列は x − 1 しかない）。
- qn: q ≠ r、P_0(q) = r、q は r で数えられる最後の子（CL_M(r) = Lc ++ [q]）。i は r か q。
- C: q ≠ r で q は r の最後の数える子でない。i は r か q。
`t2_seed_frames_of` は枠の性質 Q 一般で振り分ける（t2 の QFO にも使える）。
`seed_frames_PF` は PH3cG・FC3 の部分を、t2 の残り（QRRes・SVRes・QNRes・CRes）と closure の残り
（CBig: r の q より前の数えない子は v > s′）から出す。QNFC は V3QNFC、SVFix は V3SVFix、CFix は V3CFix で CBig に帰着。`ph3c_expand_t2S`・`fc3_expand_t2S` は t2 の QFO の種の枠と合わせた形。
-/
import Ytosk.V3PSeedCG
import Ytosk.V3PSeedSVG
import Ytosk.V3PSeedQRG
import Ytosk.V3PT2G
import Ytosk.V3QNFC
import Ytosk.V3SVFix
import Ytosk.V3CFix

namespace Ytosk.G

open T

set_option linter.unusedSectionVars false

/-- The frames of a seed column `i` of every `M[n]` (`n ≥ 2`). -/
def SeedFr (Q : T → List T → T → Prop) (M : Mat) (r L i : Nat) : Prop :=
  ∀ n, 2 ≤ n →
    (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) m) τ) → ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n) σ →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
        CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) i =
          Lc ++ c :: R → Q (σ.v i) (Lc.map σ.o) (σ.o c)

/-- The only column that may upgrade into the last column `x` is `x − 1`. -/
theorem upg_last_eq {M : Mat} {i x : Nat} (hlen : x + 1 = M.length) (h : upg M i = some x) : i = x - 1 := by
  have h1 := upg_le h
  have h2 := upg_lt_len h
  omega

/-- In the `qr` case (`q = r`, nothing upgrades into `x`), `x` is the last counted child of `r`. -/
theorem cl_qr {M : Mat} {r L : Nat} (hZ2 : Z2 M) (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L)) :
    ∃ Lc, CL M r = Lc ++ [r + L] := by
  obtain ⟨_, h1lt⟩ := par2_facts hZ2 (by omega) hr
  have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have hsplit := split_last_max _ _ (children_sorted M r) hxr
    (fun d hd => by have := (mem_children hd).2; omega)
  have hxc : Counted M r (r + L) := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := congrArg (fun t => t.2.1) h
      simp [col_eq_entries, bump] at this; omega
    · have hu := h.1
      unfold isUpg at hu
      obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hu
      exact hXu k (of_decide_eq_true hk)
  refine ⟨((children M r).filter (fun d => decide (d < r + L))).filter (fun c => decide (Counted M r c)), ?_⟩
  unfold CL
  rw [hsplit, List.filter_append]
  simp [hxc]

/-- **The case split of the seed frames** for any frame property `Q`. -/
theorem t2_seed_frames_of {Q : T → List T → T → Prop} {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk)
    (hQR : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
      (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → SeedFr Q M r L r)
    (hSV : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
      upg M (r + L - 1) = some (r + L) → SeedFr Q M r L r)
    (hQN : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] → ∀ i, (i = r ∨ i = q) → SeedFr Q M r L i)
    (hC : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → ∀ i, (i = r ∨ i = q) → SeedFr Q M r L i) :
    T2SeedFrames Q M := by
  intro r L hlen hr n hn hlow σ hσ hG i hi
  have hqcase : ∀ q, par M 0 (r + L) = some q → q ≠ r → ∀ i, (i = r ∨ i = q) → SeedFr Q M r L i := by
    intro q hq hqr i hi
    by_cases hcl : ∃ Lc, CL M r = Lc ++ [q]
    · obtain ⟨Lc, hLc⟩ := hcl
      exact hQN r L q hlen hr hq hqr Lc hLc i hi
    · exact hC r L q hlen hr hq hqr hcl i hi
  have hfr : SeedFr Q M r L i := by
    rcases hi with (⟨hq, hir⟩ | ⟨q, hq, hqr, hpi⟩) | ⟨q, hq, hqr, hiq⟩
    · rw [hir]
      by_cases hux : upg M (r + L - 1) = some (r + L)
      · exact hSV _ L hlen hr hq hux
      · have hXu : ∀ j, upg M j ≠ some (r + L) := by
          intro j hj
          have := upg_last_eq hlen hj
          rw [this] at hj; exact hux hj
        obtain ⟨Lc, hLc⟩ := cl_qr I.z2 hlen hr hq hXu
        exact hQR _ L hlen hr hq hXu Lc hLc
    · have hp := par0_q_t2 hM hS I hlen hr hq hqr
      rw [hp] at hpi; cases hpi
      exact hqcase q hq hqr _ (Or.inl rfl)
    · rw [hiq]; exact hqcase q hq hqr _ (Or.inr rfl)
  exact hfr n hn hlow σ hσ hG

/-- **The residuals of the seed frames** (PH3cG・FC3 part): t2 の残りと closure の残り（CBig）. -/
structure T2SeedPRes (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQRRes M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → T2SeedSVRes M ρ r L
  qn : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNRes M ρ r L q Lc
  C : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCRes M ρ r L q ∧ T2SeedCBig M ρ r L q

/-- **PH3cG and FC3 at the seed frames of every `M[n]`** (`t = 2`). -/
theorem seed_frames_PF {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk) (hP : PH3cG M ρ) (hF : FC3 M ρ)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      FrameOT (M.take (M.length - 1)) τ ∧ PH3cG (M.take (M.length - 1)) τ ∧ FC3 (M.take (M.length - 1)) τ)
    (hRes : T2SeedPRes M ρ) :
    T2SeedFrames (fun a Lv cv => QPHs a Lv cv ∧ QF3s a Lv cv) M := by
  -- the prefix `M.take x`
  have hRk1 : Rk (M.take (M.length - 1)) rk := by
    have hlen1 : 1 ≤ M.length := by
      rcases hM0 : M with _ | _
      · rw [hM0] at hz; exact absurd rfl hz
      · simp
    exact rk_take (by omega) I.rank (counted_take_last (M := M) hlen1 I.r0p I.z2 I.sd I.z1 I.uat)
  have hC1 := cons_of_rk hRk1
  set τ0 := rhsIt (M.take (M.length - 1)) (rkBound (M.take (M.length - 1)) rk) with hτ0
  have hx : ∀ r L, r + L + 1 = M.length → M.length - 1 = r + L := fun r L h => by omega
  refine t2_seed_frames_of (Q := fun a Lv cv => QPHs a Lv cv ∧ QF3s a Lv cv) hM hS I ?_ ?_ ?_ ?_
  · intro r L hlen hr hq hXu Lc hLc n hn hlow σ hσ _ Lc' c R' hcl
    rw [hx r L hlen] at hC1 hRk1
    exact seed_frames_qr hM hS I R hz h2 hlen hr hq hXu hLc (hRes.qr r L hlen hr hq hXu Lc hLc) hC1
      ⟨rk, hRk1⟩ hP hF n hn hlow σ hσ Lc' c R' hcl
  · intro r L hlen hr hq hux n hn hlow σ hσ hG Lc' c R' hcl
    have hT' := hT τ0 hC1
    rw [hx r L hlen] at hC1 hRk1 hT'
    have hSV := hRes.sv r L hlen hr hq hux
    have hFix := t2SeedSVFix_holds hM hS I R hlen hr hq hux
    have hrN : r < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n).length := by
      have hc : c ∈ children _ r := cl_mem_children (by rw [hcl]; simp)
      have := mem_children hc; omega
    have hdec : ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n)
        r).map σ.o).Pairwise (fun a b => b ≤ a) := by
      rw [← cvals_eq_map hσ hG]; exact hG.dec r hrN
    exact seed_frames_sv hM hS I R hz h2 hlen hr hq hux hSV hFix hC1 hRk1 hT' n hn hlow σ hσ hdec Lc' c R' hcl
  · intro r L q hlen hr hq hqr Lc hLc i hi n hn hlow σ hσ hG Lc' c R' hcl
    rw [hx r L hlen] at hC1 hRk1
    have hQN := hRes.qn r L q hlen hr hq hqr Lc hLc
    have hFC := t2SeedQNFC_holds hM hS I R hlen hr hq hqr hLc
    exact seed_frames_qn hM hS I R hz h2 hlen hr hq hqr hLc hQN hFC hC1 ⟨rk, hRk1⟩ hP hF n hn hlow σ hσ hG
      i hi Lc' c R' hcl
  · intro r L q hlen hr hq hqr hncl i hi n hn hlow σ hσ hG Lc' c R' hcl
    have hT' := hT τ0 hC1
    rw [hx r L hlen] at hC1 hRk1 hT'
    obtain ⟨hCR, hBig⟩ := hRes.C r L q hlen hr hq hqr hncl
    have hFix := t2SeedCFix_of hM hS I R hlen hr hq hqr hncl hCR hBig
    exact seed_frames_C hM hS I R hz h2 hlen hr hq hqr hncl hCR hFix hC1 hRk1 hT' n hn hlow σ hσ hG
      i hi Lc' c R' hcl

/-- Joining two seed-frame properties. -/
theorem t2SeedFrames_and {Q₁ Q₂ : T → List T → T → Prop} {M : Mat} (h₁ : T2SeedFrames Q₁ M)
    (h₂ : T2SeedFrames Q₂ M) : T2SeedFrames (fun a Lv cv => Q₁ a Lv cv ∧ Q₂ a Lv cv) M :=
  fun r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl =>
    ⟨h₁ r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl, h₂ r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl⟩

/-- **PH3cG of every `M[n]`** (`t = 2`), with the seed frames reduced to the named residuals. -/
theorem ph3c_expand_t2S (hB : T2BelowXRes) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk) (hP : PH3cG M ρ) (hF : FC3 M ρ)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      FrameOT (M.take (M.length - 1)) τ ∧ PH3cG (M.take (M.length - 1)) τ ∧ FC3 (M.take (M.length - 1)) τ)
    (hFO : T2SeedFrames QFO M) (hRes : T2SeedPRes M ρ) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → PH3cG (expand M n) σ := by
  have hPF := seed_frames_PF hM hS I R hP hF hz h2 hT hRes
  refine ph3c_expand_t2 hB hM hS I R hP hz h2 (fun τ hτ => ⟨(hT τ hτ).1, (hT τ hτ).2.1⟩) ?_
  intro r L hlen hr n hn hlow σ hσ hG i hi Lc c R' hcl
  exact ⟨hFO r L hlen hr n hn hlow σ hσ hG i hi Lc c R' hcl, (hPF r L hlen hr n hn hlow σ hσ hG i hi Lc c R' hcl).1⟩

/-- **FC3 of every `M[n]`** (`t = 2`), with the seed frames reduced to the named residuals. -/
theorem fc3_expand_t2S (hB : T2BelowXRes) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk) (hP : PH3cG M ρ) (hF : FC3 M ρ)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      FrameOT (M.take (M.length - 1)) τ ∧ PH3cG (M.take (M.length - 1)) τ ∧ FC3 (M.take (M.length - 1)) τ)
    (hFO : T2SeedFrames QFO M) (hRes : T2SeedPRes M ρ) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → FC3 (expand M n) σ := by
  have hPF := seed_frames_PF hM hS I R hP hF hz h2 hT hRes
  refine fc3_expand_t2 hB hM hS I R hF hz h2 (fun τ hτ => ⟨(hT τ hτ).1, (hT τ hτ).2.2⟩) ?_
  intro r L hlen hr n hn hlow σ hσ hG i hi Lc c R' hcl
  exact ⟨hFO r L hlen hr n hn hlow σ hσ hG i hi Lc c R' hcl, (hPF r L hlen hr n hn hlow σ hσ hG i hi Lc c R' hcl).2⟩

end Ytosk.G

