/-
**3 行・t = 2: M[n] の写しの事実 CopyFacts を gexp で（`copy_facts_gexp`）。**
-/
import Ytosk.V3ExpT2W
import Ytosk.V3ExpT2CF

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hd0 : 0 < d0) (hd1 : 0 < d1) (hgx : TRIO.le1 M r (r + L)) (he2r : entry M 2 r = 0)
  (hBEP : BumpE2 (TRIO.gexp M r L d0 d1 (n - 1)))
include hlen hL hA hd0e hn hd0 hd1 hgx he2r hBEP

/-- **`CopyFacts` of `M[n]` over `M[n − 1]`** (`t = 2`). -/
theorem copy_facts_gexp {σ ρ : Valn} {rk : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) ρ)
    (hGP : Good3 (TRIO.gexp M r L d0 d1 (n - 1)) ρ) (hRP : Rk (TRIO.gexp M r L d0 d1 (n - 1)) rk)
    (hK : T2GuardKids (TRIO.gexp M r L d0 d1 (n - 1)) r)
    (hKV : T2GuardVal (TRIO.gexp M r L d0 d1 (n - 1)) ρ r)
    (hRK : T2RootKids (TRIO.gexp M r L d0 d1 (n - 1)) r)
    (hB : T2Base (TRIO.gexp M r L d0 d1 (n - 1)) σ ρ r)
    (hV' : isOT (σ.v (r + L)) = true) (hVV : ρ.v r < σ.v (r + L)) :
    CopyFacts (TRIO.gexp M r L d0 d1 n) (TRIO.gexp M r L d0 d1 (n - 1)) σ ρ r L (σ.v (r + L))
      (TRIO.le1 (TRIO.gexp M r L d0 d1 (n - 1)) r) := by
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
  have hNl : N.length = P.length + L := by omega
  have hrP : r < P.length := by
    have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
    omega
  have he2rP : entry P 2 r = 0 := by
    rw [hP, entry_gexp_pre hlen (show 1 ≤ n - 1 by omega) 2 (by omega)]; exact he2r
  -- index conversion
  have conv : ∀ i, r ≤ i → i < P.length → ∃ b, i = r + b ∧ b < (n - 1) * L ∧ i + L = r + L + b :=
    fun i h1 h2 => ⟨i - r, by omega, by omega, by omega⟩
  have hch : ∀ i, r ≤ i → i < P.length → children N (i + L) = (children P i).map (· + L) := by
    intro i h1 h2
    obtain ⟨b, rfl, hb, he⟩ := conv i h1 h2
    rw [he]; exact children_shift2 hlen hL hA hd0e hn hb
  have hcnt : ∀ i d, r ≤ i → i < P.length → d ∈ children P i →
      (Counted N (i + L) (d + L) ↔ Counted P i d) := by
    intro i d h1 h2 hd
    obtain ⟨b, rfl, hb, he⟩ := conv i h1 h2
    rw [he]; exact counted_copy2 hlen hL hA hd0e hn hd0 hd1 hgx he2r hBEP hb hd
  have hbmp : ∀ i d, r ≤ i → i < P.length → d ∈ children P i →
      (col N (d + L) = bump N (i + L) ↔ col P d = bump P i) := by
    intro i d h1 h2 hd
    obtain ⟨b, rfl, hb, he⟩ := conv i h1 h2
    rw [he]; exact bump_copy2 hlen hL hA hd0e hn hd0 hd1 hgx he2r hBEP hb hd
  have he2 : ∀ i, r ≤ i → i < P.length → entry N 2 (i + L) = entry P 2 i := by
    intro i h1 h2
    obtain ⟨b, rfl, hb, he⟩ := conv i h1 h2
    rw [he]; exact e2_copy2 hlen hL hA hd0e hn hb
  have he1 : ∀ i, r < i → i < P.length → (entry N 1 (i + L) = 0 ↔ entry P 1 i = 0) := by
    intro i h1 h2
    rw [e1_shift2 (s := i) hlen hL hA hd0e hn hd0 hd1 hgx (by omega) (by omega)]
    split
    · rename_i hg
      obtain ⟨b, rfl, hb, _⟩ := conv i (by omega) h2
      have := guard_e1P hlen hL hA hd0e hn hd0 hd1 hgx (show 0 < b by omega) hb hg
      rw [← hP] at this ⊢
      constructor <;> intro h <;> omega
    · rw [← hP]; simp
  have hp1 : ∀ i, r < i → i < P.length → par N 1 (i + L) = (par P 1 i).map (sft r L) := by
    intro i h1 h2
    obtain ⟨b, rfl, hb, he⟩ := conv i (by omega) h2
    rw [he]; exact par1_copy2 hlen hL hA hd0e hn hd0 hd1 hgx (by omega) hb
  have hup : ∀ i, r < i → i < P.length → upg N (i + L) = (upg P i).map (sft r L) := by
    intro i h1 h2
    obtain ⟨b, rfl, hb, he⟩ := conv i (by omega) h2
    rw [he]; exact upg_copy2 hlen hL hA hd0e hn hd0 hd1 hgx he2r (by omega) hb
  -- the guard
  have hg0 : TRIO.le1 P r r := ⟨hrP, hrP, Relation.ReflTransGen.refl⟩
  have hge1 : ∀ i, r < i → i < P.length → TRIO.le1 P r i → entry P 1 i ≠ 0 := by
    intro i h1 h2 hg
    obtain ⟨b, rfl, hb, _⟩ := conv i (by omega) h2
    have := guard_e1P hlen hL hA hd0e hn hd0 hd1 hgx (show 0 < b by omega) hb hg
    rw [← hP] at this
    omega
  have hgp : ∀ i, r < i → i < P.length → TRIO.le1 P r i → ∃ t, par P 1 i = some t ∧ r ≤ t ∧ TRIO.le1 P r t := by
    intro i h1 _ hg
    obtain ⟨m, hm, hgm⟩ := le1_par1_down hg (by omega)
    exact ⟨m, hm, le1_ge hgm, hgm⟩
  have hgpn : ∀ i t, r < i → i < P.length → ¬ TRIO.le1 P r i → par P 1 i = some t → r ≤ t →
      ¬ TRIO.le1 P r t := by
    intro i t _ h2 hg ht _ hgt
    exact hg (le1_par1_up hgt ht h2)
  have hupk : ∀ i k, upg P i = some k → k ≠ r := by
    intro i k hk hkr
    have := upg_target_e2 hk
    rw [hkr, he2rP] at this; omega
  have hgu : ∀ i k, r < i → i < P.length → TRIO.le1 P r i → entry P 2 i = 0 → upg P i = some k →
      r < k ∧ TRIO.le1 P r k := by
    intro i k h1 h2 hg _ hk
    obtain ⟨m, hm1, hmk, _, _⟩ := upg_spec hk
    obtain ⟨m', hm', hgm⟩ := le1_par1_down hg (by omega)
    rw [hm1] at hm'; cases hm'
    have hkl : k < P.length := upg_lt h2 hk
    have hgk := le1_par1_up hgm hmk hkl
    exact ⟨lt_of_le_of_ne (le1_ge hgk) (Ne.symm (hupk i k hk)), hgk⟩
  have hgun : ∀ i k, r < i → i < P.length → ¬ TRIO.le1 P r i → upg P i = some k → r ≤ k →
      ¬ TRIO.le1 P r k := by
    intro i k _ h2 hg hk _ hgk
    obtain ⟨m, hm1, hmk, _, _⟩ := upg_spec hk
    obtain ⟨m', hm', hgm⟩ := le1_par1_down hgk (hupk i k hk)
    rw [hmk] at hm'; cases hm'
    exact hg (le1_par1_up hgm hm1 h2)
  exact copy_facts (g := TRIO.le1 P r) hCN hCP hGP hRP hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0
    hge1 hgp hgpn hgu hgun hK.1 hK.2 hKV.1 hKV.2 hB rfl hV' hVV hRK

end

end Ytosk
