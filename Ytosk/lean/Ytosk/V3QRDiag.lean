/-
**3 行・t = 1・q = r: 引き上げの量と、引き上げのない列の対角化の点。**

A = o(r) = ψ_μ(b_r)、b_r = b + Ω_{μ+1}。
- o の枠の引き上げ `loQ i c`: 子の値が A で書き換えが起きるとき 1。
- のりしろの枠の引き上げ `lbQ i j k`: j の子が k だけで o(k) = A のとき、前の項 P が 0 なら 2、そうでなければ 1。
- 引き上げの数 0 の D の値は A の対角化の点 ψ_μ(b_r) の下にある（`qr_diag0`）。
  よって ψ_s(b_r)（s ≠ μ）を値にもつ列は引き上げの数が 1 以上（`qr_d_pos`）。
-/
import Ytosk.V3QRLocO

namespace Ytosk

open T

/-- In a sorted list split at `c`, the part before `c` is the filter `· < c`. -/
theorem filter_lt_split {l L R : List Nat} {c : Nat} (hs : l.Pairwise (· < ·)) (h : l = L ++ c :: R) :
    l.filter (fun d => decide (d < c)) = L := by
  obtain ⟨hL, hR⟩ := sib_order hs h
  rw [h, List.filter_append, List.filter_cons, if_neg (by simp)]
  rw [List.filter_eq_self.mpr (fun d hd => by simpa using hL d hd),
    List.filter_eq_nil_iff.mpr (fun d hd => by have := hR d hd; simp; omega)]
  simp

open Classical in
/-- The lift at an `o` frame: the child is `A` and the frame rewrites. -/
noncomputable def loQ (M : Mat) (ρ : Valn) (μ b : T) (i c : Nat) : Nat :=
  if ρ.o c = psi μ (app b (psi (succ μ) z z)) z ∧
      lt (preState M ρ i ((children M i).filter (fun d => decide (d < c))))
        (app b (psi (succ μ) z z)) = true ∧
      lt (psi (ρ.v i) z z) (psi μ (app b (psi (succ μ) z z)) z) = true then 1 else 0

open Classical in
/-- The lift at a bump frame: `k` is the only child of the bump child `j` and has the value `A`. -/
noncomputable def lbQ (M : Mat) (ρ : Valn) (μ b : T) (i j k : Nat) : Nat :=
  if children M j = [k] ∧ ρ.o k = psi μ (app b (psi (succ μ) z z)) z then
    (if sumN (nzs (((children M i).filter (fun d => decide (d < j))).map (bumpTerm M ρ i))) = z
      then 2 else 1)
  else 0

/-- `b_r` itself has no diagonal point (its last summand is `Ω_{μ+1}`). -/
theorem not_diag_br {a μ b : T} : ¬ DiagAt a (app b (psi (succ μ) z z)) μ (app b (psi (succ μ) z z)) := by
  intro h
  have h2 := h.last_g
  rw [last_app b (by simp)] at h2
  have := DiagAt.not_omega_succ (show DiagAt a _ μ (psi (succ μ) z z) from h2)
  rw [isSucc_succ] at this; cases this

/-- `ψ_s(b_r)` with `s ≠ μ` has no diagonal point at `μ`. -/
theorem not_diag_mu {μ b s : T} (hs : s ≠ μ) :
    ¬ DiagAt μ (app b (psi (succ μ) z z)) μ (psi s (app b (psi (succ μ) z z)) z) := by
  intro h
  generalize hB : app b (psi (succ μ) z z) = B at h
  cases h with
  | here _ _ _ => exact hs rfl
  | arg _ _ hD => rw [← hB] at hD; exact not_diag_br hD
  | sub _ _ _ => exact absurd (app_eq_z hB).2 (by simp)

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ b : T} (hx : x + 1 = M.length)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
  (hq : par M 0 x = some r) (hro : ρ.o r = psi μ (app b (psi (succ μ) z z)) z)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
  (hBk : ∀ i j k, i < x → DepX M x false i → j ∈ children M i → col M j = bump M i →
    k ∈ children M j → DepX M x true k → k < x)
include hx hC hG hKD hTD hq hro hOS hVS hBk

/-- **Without a lift, the diagonal point of `A` stays below.** -/
theorem qr_diag0 {bb : Bool} {i d : Nat} (hD : DepL M x (loQ M ρ μ b) (lbQ M ρ μ b) bb i d) :
    i < x → d = 0 → DiagAt μ (app b (psi (succ μ) z z)) μ (valB ρ bb i) := by
  have hbr : app b (psi (succ μ) z z) ≠ z := fun h => absurd (app_eq_z h).2 (by simp)
  induction hD with
  | leaf => intro h; omega
  | @ochild i c d hc hcb hcu hdc ih =>
    intro hi hd0
    have hd : d = 0 := by omega
    have hlo : loQ M ρ μ b i c = 0 := by omega
    have hcm := mem_children hc
    have hcM := hcm.2
    have hiM : i < M.length := by omega
    show DiagAt μ _ μ (ρ.o i)
    rcases Nat.lt_or_ge c x with hcx | hcx
    · have ihc := ih hcx hd
      simp only [valB, cond_true] at ihc
      have hDi : DepX M x true i := DepX.ochild hc hcb hcu (depX_of_depL hdc)
      rcases hOS i hi hDi with ⟨_, hnc⟩ | ⟨_, L, c', R, hch, _, _, hR, hLnd⟩
      · exact absurd (hnc c hc) (by rintro (h | h); exact hcb h; exact hcu h)
      · have hcc : c = c' := by
          rw [hch] at hc
          rcases List.mem_append.mp hc with h | h
          · exact absurd (depX_of_depL hdc) (hLnd c h ⟨hcb, hcu⟩)
          · rcases List.mem_cons.mp h with h | h
            · exact h
            · rcases hR c h with h' | h'
              · exact absurd h' hcb
              · exact absurd h' hcu
        subst hcc
        have hfl := filter_lt_split (children_sorted M i) hch
        obtain ⟨s, y, hcv⟩ := o_psi_form hC hcM
        have hcot : isOT (psi s y z) = true := by rw [← hcv]; exact hG.ot_o c hcM
        rw [o_frame hC hG hiM hch hcb hcu hR hcM, hcv, spArg_single]
        rw [hcv] at ihc
        rcases step_cases (a := ρ.v i) (b := preState M ρ i L) hcot with ⟨B, hB⟩ | ⟨hy, _, hyz, htr1, htr2⟩
        · rw [hB]
          have hD' := DiagAt.append B (by simp) ihc
          exact DiagAt.arg (DiagAt.ne_z hD') (DiagAt.not_succ hD') hD'
        · rw [hy]
          by_cases hne : s = μ ∧ y = app b (psi (succ μ) z z)
          · exfalso
            obtain ⟨rfl, rfl⟩ := hne
            have : loQ M ρ s b i c = 1 := by
              unfold loQ; rw [hfl, if_pos ⟨hcv, htr1, htr2⟩]
            omega
          · have hDy := DiagAt.arg_inv ihc hyz hne
            exact DiagAt.arg hyz (DiagAt.not_succ hDy) hDy
    · have hcx' : c = x := by omega
      subst hcx'
      have hir : i = r := by
        have := (mem_children_iff.mp hc).2; rw [hq] at this; exact (Option.some.inj this).symm
      subst hir
      rw [hro]
      exact DiagAt.here hbr cof_br (lt_irrefl' μ)
  | @ov i d hv ih =>
    intro hi hd0
    have ihv := ih hi hd0
    simp only [valB, cond_false] at ihv
    show DiagAt μ _ μ (ρ.o i)
    rcases hOS i hi (DepX.ov (depX_of_depL hv)) with ⟨_, hnc⟩ | ⟨hnv, _⟩
    · rw [o_nocnt hC hG (by omega) hnc]
      exact DiagAt.sub (DiagAt.ne_z ihv) (DiagAt.not_succ ihv) ihv
    · exact absurd (depX_of_depL hv) hnv
  | @vpar i m d h1 hp hdm _ =>
    intro hi _
    exact absurd (depX_of_depL hdm) ((hVS i hi (DepX.vpar h1 hp (depX_of_depL hdm))).2.1 m hp)
  | @vupg i k d h1 h2 hu hdk ih =>
    intro hi hd0
    have hDi : DepX M x false i := DepX.vupg h1 h2 hu (depX_of_depL hdk)
    obtain ⟨_, _, hcase⟩ := hVS i hi hDi
    have hkx : k < x := by
      rcases hcase with ⟨_, hu', hlt, _⟩ | ⟨h2', _⟩
      · rw [hu] at hu'; cases hu'; exact hlt
      · exact absurd h2 h2'
    have ihk := ih hkx hd0
    simp only [valB, cond_false] at ihk
    show DiagAt μ _ μ (ρ.v i)
    have hkM : k < M.length := by omega
    have hvkz : ρ.v k ≠ z := DiagAt.ne_z ihk
    have hVs : Single (last (ρ.v k)) := ⟨isOT_last (hG.ot_v k hkM), last_psi_form hvkz⟩
    obtain ⟨B, hvi⟩ := upg_valL hC (by omega) h1 h2 hu hVs (vOpt_ot hG (by omega))
    rw [hvi]
    exact DiagAt.append B (single_ne_z hVs) ihk.last_g
  | @vbump i j k d h1 h2 hj hjb hk hdk ih =>
    intro hi hd0
    have hd : d = 0 := by omega
    have hDi : DepX M x false i := DepX.vbump h1 h2 hj hjb hk (depX_of_depL hdk)
    have hiM : i < M.length := by omega
    obtain ⟨_, _, hcase⟩ := hVS i hi hDi
    rcases hcase with ⟨h2', _⟩ | ⟨_, L, K, j', k', hch, hjb', hchj, _, hKnd, hLnd⟩
    · exact absurd h2' h2
    have hjj : j = j' := by
      rw [hch] at hj
      rcases List.mem_append.mp hj with h | h
      · exact absurd (depX_of_depL hdk) (hLnd j h k hk).2
      · exact List.mem_singleton.mp h
    subst hjj
    have hkk : k = k' := by
      rw [hchj] at hk
      rcases List.mem_append.mp hk with h | h
      · exact absurd (depX_of_depL hdk) (hKnd k h)
      · exact List.mem_singleton.mp h
    subst hkk
    have hkM := (mem_children hk).2
    have hkx : k < x := hBk i j k hi hDi hj hjb hk (depX_of_depL hdk)
    have ihk := ih hkx hd
    simp only [valB, cond_true] at ihk
    show DiagAt μ _ μ (ρ.v i)
    have hBD : BumpData M ρ μ i L K j k := bump_data hC hG hKD hTD h1 h2 hch hjb hchj
    have hvi := v_bump_valueG hC hiM h1 h2 hch hjb hchj hBD.sK hBD.pK hBD.sL hBD.pp hBD.gt
      (vOpt_ot hG (by omega))
    set P := nzs (L.map (bumpTerm M ρ i)) with hPdef
    set G := sumN (K.map ρ.o ++ [ρ.o k]) with hGdef
    have hGot : isOT G = true := (sumN_dec _ hBD.sK hBD.pK).1
    have hkS : Single (ρ.o k) := hBD.sK _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hG : G = app (sumN (K.map ρ.o)) (ρ.o k) := sumN_snoc_dec hBD.sK hBD.pK
    have hωGz : omega G ≠ z := single_ne_z (single_omega hGot)
    have hWz : omega (app (sumN P) (omega G)) ≠ z := single_ne_z (single_omega hBD.potW)
    obtain ⟨B, hvi2⟩ : ∃ B, ρ.v i = app B (omega (app (sumN P) (omega G))) := by
      obtain ⟨_, s0, y0, hW0⟩ := single_omega hBD.potW
      obtain ⟨B, X, _, _, hadd⟩ := add_prefix s0 y0 (vOpt ρ (par M 1 i))
      exact ⟨B, by rw [hvi, hW0, hadd]⟩
    rw [hvi2]
    have hDG : DiagAt μ (app b (psi (succ μ) z z)) μ G := by rw [hG]; exact DiagAt.append _ (single_ne_z hkS) ihk
    exact DiagAt.append B hWz (diag_omega hBD.potW (DiagAt.append _ hωGz (diag_omega hGot hDG)))

/-- **A column with the value `ψ_s(b_r)`, `s ≠ μ`, has at least one lift.** -/
theorem qr_d_pos (hxv : ¬ DepX M x false x) {c : Nat} {s : T} (hc : c < x) (hdc : DepX M x true c)
    (hcv : ρ.o c = psi s (app b (psi (succ μ) z z)) z) (hs : s ≠ μ) :
    dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c ≠ 0 := by
  obtain ⟨d, hd⟩ := depL_of_depX (lo := loQ M ρ μ b) (lb := lbQ M ρ μ b) hdc
  rw [dOf_o hx hxv hOS hVS (by omega) hd]
  intro h0
  have := qr_diag0 hx hC hG hKD hTD hq hro hOS hVS hBk hd hc h0
  simp only [valB, cond_true] at this
  rw [hcv] at this
  exact not_diag_mu hs this

end

end Ytosk
