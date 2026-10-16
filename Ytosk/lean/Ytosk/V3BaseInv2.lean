/-
**Inv3V2 の帰納法の基底。**
SRO[n] の新しい欄を証明する。吸収の欄は行 1 の親の値が 0 なので空。
VSmallRAll と TrigS0 は基底の枠が書き換えないことから出る。
TPLoS の始点は ω² を底とする落とした行列の値で、etaOm 0 以上。
-/
import Ytosk.V3Base
import Ytosk.V3Inv2
import Ytosk.V3PBaseG

namespace Ytosk

open T

theorem base_vsmallRAll {L : Nat} {β : T} (hF : BaseFit L β) :
    VSmallRAll (Mlen L) (bval L β) := by
  intro k c Lc R s y hcl ho htr
  obtain ⟨_, hc, _⟩ := CL_split hF hcl
  have hk : k < L := by have := mem_children hc; simp at this; omega
  exact (no_trig hF hk hc ho htr.1 htr.2).elim

theorem base_absDS {L : Nat} {β : T} {rk : Bool → Nat → Nat} :
    AbsDS (Mlen L) (bval L β) rk := by
  intro r μ b h1 h0 h2 hro i hi hd he1 he2 hO hl q hq
  rw [vOpt_par1] at hq
  simp [summands] at hq

theorem base_absUS {L : Nat} {β : T} {rk : Bool → Nat → Nat} :
    AbsUS (Mlen L) (bval L β) rk := by
  intro r μ b h1 h0 h2 hro i k hi hd hu hO hl q hq
  rw [vOpt_par1] at hq
  simp [summands] at hq

theorem base_absUWL {L : Nat} {β : T} : AbsUWL (Mlen L) (bval L β) := by
  intro r μ b h1 h0 h2 hro i k hi hd hu hO hcof q hq
  rw [vOpt_par1] at hq
  simp [summands] at hq

theorem base_absUW0 {L : Nat} {β : T} {rk : Bool → Nat → Nat} :
    AbsUW0 (Mlen L) (bval L β) rk := by
  intro r μ b h1 h0 h2 hro i k hi hd hu hdi hO hcof q hq
  rw [vOpt_par1] at hq
  simp [summands] at hq

theorem base_trigS0 {L : Nat} {β : T} {rk : Bool → Nat → Nat} (hF : BaseFit L β) :
    TrigS0 (Mlen L) (bval L β) rk := by
  intro r μ b h1 h0 h2 hro hseed i L' c R hi hd hch hcnt hdc hd0 s ho htr1 htr2
  have hc : c ∈ children (Mlen L) i := by rw [hch]; simp
  have hiL : i < L := by simp at hi; omega
  exact (no_trig hF hiL hc ho htr1 htr2).elim

theorem one_le_tw_w2 (k : Nat) : one ≤ tw w2 k := by
  cases k with
  | zero => exact le_of_lt (by decide : one < w2)
  | succ k =>
    apply le_of_lt
    show psi z z z < psi (tw w2 k) z z
    rw [psi_lt_psi]
    exact Or.inl (z_lt_tw (Or.inr rfl) k)

/-- The seed for the base last-column frame dominates `etaOm 0`. -/
theorem base_seed_etaOm {n : Nat} (hn : 0 < n) :
    etaOm z ≤ (drop1 (Mlen (1 + 3 * n)) (3 * n) (brk (1 + 3 * n))).o 0 := by
  rw [(drop_eq n 0 (by omega)).1, bval_o0, if_pos (by omega)]
  apply le_psi_arg
  exact le_psi_sub (one_le_tw_w2 _)

theorem base_tplos {n : Nat} :
    TPLoS (Mlen (1 + 3 * n)) (bval (1 + 3 * n) one) (brk (1 + 3 * n)) := by
  have hF : BaseFit (1 + 3 * n) one := Or.inl ⟨by omega, rfl⟩
  intro r μ b h1 h0 h2 hro c hc hd s y ho hy a hla hns hO hl
  have hx : (Mlen (1 + 3 * n)).length - 1 = 3 * n := by simp
  rw [hx] at h1 ⊢
  have hn : 0 < n := by
    have := par_lt _ 1 (3 * n) r h1
    omega
  rw [Mlen_par1 (by omega) (by omega)] at h1
  cases h1
  rw [bval_o0] at hro
  cases hro
  have hμ : holeLev y = z := hl
  have hcM : c < (Mlen (1 + 3 * n)).length := by simp at hc ⊢; omega
  have htpl := base_tplo hF c hcM s y ho hy a hla hns hO
  rw [hμ] at htpl
  intro hlt
  exact htpl (lt_of_le_of_lt (le_psi_sub (fsD_mono_eta hO (base_seed_etaOm hn))) hlt)

/-- All fields of the redesigned invariant are proved at the induction base. -/
theorem hBaseV2_holds (n : Nat) :
    ∃ ρ rk, Inv3V2 (expand SRO n) ρ rk ∧ Res3A (expand SRO n) ρ rk := by
  rw [expand_SRO_eq]
  have hF : BaseFit (1 + 3 * n) one := Or.inl ⟨by omega, rfl⟩
  exact ⟨bval (1 + 3 * n) one, brk (1 + 3 * n),
    ⟨bval_cons hF, base_good3 hF, brk_rk le_rfl,
      base_vsmallF hF, base_frameClosed hF, base_frameOT hF, base_kd hF, base_td hF,
      G.base_ph3c hF, G.base_fc3 hF, base_vsmallRAll hF,
      base_absDS, base_absUS, base_tp1 hF, base_tplos, base_tp1w hF,
      base_tplow hF, base_absUWL, base_absUW0, base_adw hF, base_trigS0 hF,
      base_tplon hF, base_adn hF, base_rootS hF (by omega), base_rootP hF (by omega)⟩,
    base_res3A⟩

end Ytosk
