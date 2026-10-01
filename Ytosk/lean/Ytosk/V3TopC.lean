/-
**最上位の仮定を「ある評価で」述べる形 `HInvE`。**

帰納法の各段で展開の仕組みが作る評価をそのまま使えるように、最上位の仮定を「各標準形にある評価と順位が
あって `Inv3 ∧ Res3A`」の形にする。接頭辞の落とす補題の残り（`Res3.chain`）と、`t = 0` の `M[n]` の評価の
`Good3` などは、評価の一意性（`cons_unique`）と一致の補題（`V3Congr`）で移す。
-/
import Ytosk.V3TopB
import Ytosk.V3Congr

namespace Ytosk

open T

/-- **The top hypothesis, for some valuation.** -/
def HInvE : Prop :=
  ∀ M, Std M → M ≠ SRO → M ≠ [] → ∃ ρ rk, Inv3 M ρ rk ∧ Res3A M ρ rk

theorem HInvA.toE (h : HInvA) : HInvE := by
  intro M hM hS hE
  obtain ⟨⟨rk, hR⟩, hall⟩ := h M hM hS hE
  exact ⟨_, rk, hall _ rk (cons_of_rk hR) hR⟩

/-- A ranking excludes SRO. -/
theorem ne_SRO_of_rk {N : Mat} {rk : Bool → Nat → Nat} (hR : Rk N rk) : N ≠ SRO := by
  intro he; rw [he] at hR; exact not_val_SRO _ (val_of_rk hR)

/-- **`HInvE` at a standard matrix with a ranking**: every valuation has `Good3` and the root conditions. -/
theorem good_of_E (h : HInvE) {N : Mat} (hN : Std N) (hE : N ≠ []) {σ : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons N σ) (hR : Rk N rk) :
    Good3 N σ ∧ (∀ i ∈ roots N, Single (σ.o i)) ∧ ((roots N).map σ.o).Pairwise (fun a b => b ≤ a) := by
  obtain ⟨ρ, rk', I, _⟩ := h N hN (ne_SRO_of_rk hR) hE
  have hA := agree_of_cons I.cons hC hR
  exact ⟨good3_congr I.good hA, rootS_congr I.rootS hA, rootP_congr I.rootP hA⟩

/-- **The prefix drops from `HInvE`.** -/
theorem chain_of_E (h : HInvE) {M : Mat} (hM : Std M) {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) :
    ∀ j, j + 1 < M.length → DropRes (M.take (j + 1)) j (drop1 M (j + 1) rk) (drop1 M j rk) := by
  have hRk := rk_take_all I.rank I.r0p I.z2 I.sd I.z1 I.uab
  intro j hj
  set P := M.take (j + 1) with hPdef
  have hlj : P.length = j + 1 := by rw [List.length_take]; omega
  have hRj : Rk P rk := hRk (j + 1) (by omega)
  have hSj : Std P := std_take hM (j + 1) (by omega)
  have hEj : P ≠ [] := by intro he; rw [he] at hlj; simp at hlj
  obtain ⟨ρP, rkP, IP, RP⟩ := h P hSj (ne_SRO_of_rk hRj) hEj
  have hD := RP.drop
  rw [hlj, show j + 1 - 1 = j by omega] at hD
  have hRPj : Rk (P.take j) rkP := rk_take_all IP.rank IP.r0p IP.z2 IP.sd IP.z1 IP.uab j (by omega)
  have hRPj' : Rk (P.take j) rk := by
    rw [hPdef, take_take_succ]; exact hRk j (by omega)
  have hA : Agree P ρP (drop1 M (j + 1) rk) := agree_of_cons IP.cons (cons_of_rk hRj) hRj
  have hA' : Agree (P.take j) (drop1 P j rkP) (drop1 M j rk) := by
    have h1 : Cons (P.take j) (drop1 P j rkP) := cons_of_rk hRPj
    have h2 : Cons (P.take j) (drop1 M j rk) := by
      rw [← drop1_take_succ M j rk]; exact cons_of_rk hRPj'
    exact agree_of_cons h1 h2 hRPj
  exact dropRes_congr (by omega) hD hA hA'

/-- **`HInvE` gives the old top hypothesis.** -/
theorem hInv_of_E (h : HInvE) :
    ∀ M, Std M → M ≠ SRO → M ≠ [] → ∃ ρ rk, Inv3 M ρ rk ∧ Res3 M ρ rk := by
  intro M hM hS hE
  obtain ⟨ρ, rk, I, RA⟩ := h M hM hS hE
  have hC := I.cons
  have hR := I.rank
  refine ⟨ρ, rk, I, ⟨RA.drop, chain_of_E h hM I, RA.seed, ?_⟩⟩
  intro r L hlen hp he1
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; have := par_lt M 0 _ r hp; omega
    · exact h0
  have he2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hDr := RA.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  refine ⟨t0_vr hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 hC hR
    ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hDr, ?_⟩
  intro n hn2 σ hCN
  have hRN := rk_N0 hlen hL hp (show 1 ≤ n by omega) I.r0p I.z2 he2 hn2 hR
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen (show 1 ≤ n by omega)
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := by
    rw [show M.length - 1 = r + L by omega, ← entry_eq, ← entry_eq, ← entry_eq, I.r0p _ _ hp]
    omega
  have hs0 : TRIO.srow M (M.length - 1) = 0 := by
    unfold TRIO.srow
    rw [show M.length - 1 = r + L by omega, ← entry_eq, ← entry_eq, he1, he2]; rfl
  have hexp := expand_eq_gexp_t0 M n (by omega) hzT
    (by rw [hs0, show M.length - 1 = r + L by omega]; exact hp) hs0
  rw [show M.length - 1 - r = L by omega] at hexp
  have hSN : Std (TRIO.gexp M r L 0 0 n) := hexp ▸ Std.exp n hM
  have hEN : TRIO.gexp M r L 0 0 n ≠ [] := by
    intro he; rw [he] at hlN; simp at hlN
    have : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
    omega
  obtain ⟨hG, hS', hP'⟩ := good_of_E h hSN hEN hCN hRN
  exact ⟨hG, t0_vsmallNewN hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 hC I.good hR hn2 hCN,
    hS', hP'⟩

/-- **Termination of the 3-row BMS from SRO**, with the top hypothesis for some valuation (the form an
induction on `Std` produces). The case `t = 2` may use `HInvE` and that `M` is standard. -/
theorem trio_terminatesE (hInv : HInvE)
    (hT2 : HInvE → ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n) :
    WellFounded Step' :=
  trio_terminates' (hInv_of_E hInv) (hT2 hInv)

end Ytosk
