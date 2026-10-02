/-
**3 行・t = 2: 写しの関係と写しの列の Good3 を `TRIO.gexp` に当てはめる（`copy_good3_gexp`）。**

N = M[n]、P = M[n − 1]（n ≥ 2）、ガード g = le1 P r。構造の仮定は V3ExpT2C・V3ExpT2D の補題で埋まる。
上げの先は P_1 が同じで行 2 ≥ 1（r ではない）なので、上げについてのガードの閉じ方も構造から出る。

残り（明示した仮定、実測は C′ の t = 2 の 3000 行列 × n = 2..4 で例外 0）:
- （`T2GuardKids`: g でない列の数える子・のりしろの子の子は g でない。守られた子の親は守られる（guard_par）ので証明済み。）
- `T2GuardVal`: g の列の、g でない数える子・のりしろの子の子の v は V = v_P(r) 以下。
- `T2RootKids`: r の数える子は g。
- `T2Base`: 写しの v が読む r より前の列の v は N と P で等しい。
- 根: v_N(x) は標準形で V < v_N(x)。
-/
import Ytosk.V3ExpT2V
import Ytosk.V3ExpT2E

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- Unguarded columns of the copy block read only unguarded children. -/
def T2GuardKids (P : Mat) (r : Nat) : Prop :=
  (∀ i d, r ≤ i → i < P.length → d ∈ children P i → Counted P i d → ¬ TRIO.le1 P r i → ¬ TRIO.le1 P r d) ∧
  (∀ i j k, r < i → i < P.length → j ∈ children P i → col P j = bump P i → k ∈ children P j →
    ¬ TRIO.le1 P r i → ¬ TRIO.le1 P r k)

/-- The unguarded values read by guarded columns are at most `V = v(r)`. -/
def T2GuardVal (P : Mat) (ρ : Valn) (r : Nat) : Prop :=
  (∀ i d, r ≤ i → i < P.length → d ∈ children P i → Counted P i d → TRIO.le1 P r i →
    ¬ TRIO.le1 P r d → ¬ ρ.v r < ρ.v d) ∧
  (∀ i j k, r < i → i < P.length → j ∈ children P i → col P j = bump P i → k ∈ children P j →
    TRIO.le1 P r i → ¬ TRIO.le1 P r k → ¬ ρ.v r < ρ.v k)

/-- The counted children of `r` are guarded. -/
def T2RootKids (P : Mat) (r : Nat) : Prop :=
  ∀ d ∈ children P r, Counted P r d → TRIO.le1 P r d

/-- The `v`-targets below `r` of the copies have the same value in `N` and `P`. -/
def T2Base (P : Mat) (σ ρ : Valn) (r : Nat) : Prop :=
  ∀ i t, r < i → i < P.length → (par P 1 i = some t ∨ upg P i = some t) → t < r → σ.v t = ρ.v t

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hd0 : 0 < d0) (hd1 : 0 < d1) (hgx : TRIO.le1 M r (r + L)) (he2r : entry M 2 r = 0)
  (hBEP : BumpE2 (TRIO.gexp M r L d0 d1 (n - 1)))
include hlen hL hA hd0e hn hd0 hd1 hgx he2r hBEP

/-- **`T2GuardKids` holds**: the parent of a guarded child is guarded (`guard_par`). -/
theorem t2GuardKids_gexp : T2GuardKids (TRIO.gexp M r L d0 d1 (n - 1)) r := by
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hanc : ∀ i, r ≤ i → i < P.length → Anc0 P r i := by
    intro i h1 h2
    obtain ⟨a, rfl⟩ : ∃ a, i = r + a := ⟨i - r, by omega⟩
    exact ancP_r hlen hL hA hd0e hn hd0 hd1 hgx (by omega)
  refine ⟨fun i d h1 h2 hd _ hg hgd => hg ?_, fun i j k h1 h2 hj _ hk hg hgk => hg ?_⟩
  · obtain ⟨hdl, hpd⟩ := mem_children_iff.mp hd
    exact guard_par (hanc i h1 h2) hpd hdl hgd
  · obtain ⟨hjl, hpj⟩ := mem_children_iff.mp hj
    obtain ⟨hkl, hpk⟩ := mem_children_iff.mp hk
    have hrj : Anc0 P r j := Anc0.step hpj (hanc i (by omega) h2)
    exact guard_par (hanc i (by omega) h2) hpj hjl (guard_par hrj hpk hkl hgk)

/-- **The copy relation and Good3 at the copies of `M[n]`** (`t = 2`). -/
theorem copy_good3_gexp {σ ρ : Valn} {rk : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) ρ)
    (hGP : Good3 (TRIO.gexp M r L d0 d1 (n - 1)) ρ) (hRP : Rk (TRIO.gexp M r L d0 d1 (n - 1)) rk)
    (hK : T2GuardKids (TRIO.gexp M r L d0 d1 (n - 1)) r)
    (hKV : T2GuardVal (TRIO.gexp M r L d0 d1 (n - 1)) ρ r)
    (hRK : T2RootKids (TRIO.gexp M r L d0 d1 (n - 1)) r)
    (hB : T2Base (TRIO.gexp M r L d0 d1 (n - 1)) σ ρ r)
    (hV' : isOT (σ.v (r + L)) = true) (hVV : ρ.v r < σ.v (r + L)) :
    ∀ a, a < (n - 1) * L →
      let P := TRIO.gexp M r L d0 d1 (n - 1)
      (TRIO.le1 P r (r + a) → σ.v (r + L + a) = shf (ρ.v r) (σ.v (r + L)) (ρ.v (r + a)) ∧
        σ.o (r + L + a) = shO (ρ.v r) (σ.v (r + L)) (ρ.o (r + a))) ∧
      (¬ TRIO.le1 P r (r + a) → σ.v (r + L + a) = ρ.v (r + a) ∧ σ.o (r + L + a) = ρ.o (r + a)) ∧
      isOT (σ.o (r + L + a)) = true ∧ isOT (σ.v (r + L + a)) = true ∧
      (cvals (TRIO.gexp M r L d0 d1 n) σ (r + L + a)).Pairwise (fun a b => b ≤ a) := by
  intro a ha
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
  -- the abstract theorem
  have hb : r ≤ r + a := by omega
  have hal : r + a < P.length := by omega
  have rel := fun b => copy_rel (g := TRIO.le1 P r) hCN hCP hGP hRP hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0
    hge1 hgp hgpn hgu hgun hK.1 hK.2 hKV.1 hKV.2 hB rfl hV' hVV hRK _ b (r + a) (Nat.lt_succ_self _) hb hal
  have hgd := copy_good3 (g := TRIO.le1 P r) hCN hCP hGP hRP hNl hrP hch hcnt hbmp he2 he1 hp1 hup hg0
    hge1 hgp hgpn hgu hgun hK.1 hK.2 hKV.1 hKV.2 hB rfl hV' hVV hRK hb hal
  have e : r + a + L = r + L + a := by omega
  rw [e] at rel hgd
  refine ⟨fun hg => ⟨(rel false).1 hg, (rel true).1 hg⟩, fun hg => ⟨(rel false).2 hg, (rel true).2 hg⟩, hgd⟩

end

/-- **The remaining facts of the copy block** of every `M[n]` (`n ≥ 2`, measured with 0 exceptions). -/
def T2CopyRes (M : Mat) (r L d0 d1 : Nat) : Prop :=
  ∀ n, 2 ≤ n → ∀ σ ρ, Cons (TRIO.gexp M r L d0 d1 n) σ → Cons (TRIO.gexp M r L d0 d1 (n - 1)) ρ →
    T2GuardVal (TRIO.gexp M r L d0 d1 (n - 1)) ρ r ∧
    T2RootKids (TRIO.gexp M r L d0 d1 (n - 1)) r ∧ T2Base (TRIO.gexp M r L d0 d1 (n - 1)) σ ρ r ∧
    isOT (σ.v (r + L)) = true ∧ ρ.v r < σ.v (r + L)

/-- **The part before `x`** of Good3 of `M[n]`, given standard values from `x` on (the `hOTout` of
`deps_lhd_ot`): the `D` calls by `◁`, the seeds `q`, `p2`, and the unchanged calls from `M`. -/
def T2BelowX (M : Mat) (r L d0 d1 : Nat) : Prop :=
  ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L d0 d1 n) σ →
    (∀ j, r + L ≤ j → j < (TRIO.gexp M r L d0 d1 n).length → isOT (σ.o j) = true ∧ isOT (σ.v j) = true) →
    ∀ i, i < r + L → isOT (σ.o i) = true ∧ isOT (σ.v i) = true ∧
      (cvals (TRIO.gexp M r L d0 d1 n) σ i).Pairwise (fun a b => b ≤ a)

section
variable {M : Mat} {r L d0 d1 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
  (hd0 : 0 < d0) (hd1 : 0 < d1) (hgx : TRIO.le1 M r (r + L)) (he2r : entry M 2 r = 0)
include hlen hL hA hd0e hd0 hd1 hgx he2r

/-- **Good3 of every `M[n]`** (`t = 2`, `n ≥ 1`), by induction on `n`: the copies by `σ` from `M[n − 1]`,
the part before `x` from `T2BelowX`, the base `M[1] = M.take x` given. -/
theorem good3_gexp_t2
    (hRk : ∀ n, 1 ≤ n → ∃ rk, Rk (TRIO.gexp M r L d0 d1 n) rk)
    (hBE : ∀ n, 1 ≤ n → BumpE2 (TRIO.gexp M r L d0 d1 n))
    (hB1 : ∀ σ, Cons (TRIO.gexp M r L d0 d1 1) σ → Good3 (TRIO.gexp M r L d0 d1 1) σ)
    (hRes : T2CopyRes M r L d0 d1) (hBX : T2BelowX M r L d0 d1) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (TRIO.gexp M r L d0 d1 n) σ → Good3 (TRIO.gexp M r L d0 d1 n) σ := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0; exact hB1
    · intro σ hCN
      have hn2 : 2 ≤ m + 1 := by omega
      obtain ⟨rk, hRP⟩ := hRk m hm0
      have hCP : Cons (TRIO.gexp M r L d0 d1 m) (rhsIt _ (rkBound _ rk)) := cons_of_rk hRP
      have hGP := ih hm0 _ hCP
      have hm : m + 1 - 1 = m := by omega
      obtain ⟨hKV, hRK, hB, hV', hVV⟩ := hRes (m + 1) hn2 σ _ hCN (by rw [hm]; exact hCP)
      have hK := t2GuardKids_gexp hlen hL hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
      rw [hm] at hK hKV hRK hB
      have hcp := copy_good3_gexp hlen hL hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
        hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP) (by rw [hm]; exact hRP)
        (by rw [hm]; exact hK) (by rw [hm]; exact hKV) (by rw [hm]; exact hRK) (by rw [hm]; exact hB)
        hV' hVV
      have hlN : (TRIO.gexp M r L d0 d1 (m + 1)).length = r + (m + 1) * L := TRIO.gexp_length hlen
      have hnL : (m + 1) * L = (m + 1 - 1) * L + L := by rw [hm, Nat.succ_mul]
      have hcopy : ∀ j, r + L ≤ j → j < (TRIO.gexp M r L d0 d1 (m + 1)).length →
          isOT (σ.o j) = true ∧ isOT (σ.v j) = true ∧
          (cvals (TRIO.gexp M r L d0 d1 (m + 1)) σ j).Pairwise (fun a b => b ≤ a) := by
        intro j h1 h2
        obtain ⟨a, rfl⟩ : ∃ a, j = r + L + a := ⟨j - (r + L), by omega⟩
        obtain ⟨_, _, h3, h4, h5⟩ := hcp a (by omega)
        exact ⟨h3, h4, h5⟩
      have hbx := hBX (m + 1) hn2 σ hCN (fun j h1 h2 => ⟨(hcopy j h1 h2).1, (hcopy j h1 h2).2.1⟩)
      have hall : ∀ i, i < (TRIO.gexp M r L d0 d1 (m + 1)).length →
          isOT (σ.o i) = true ∧ isOT (σ.v i) = true ∧
          (cvals (TRIO.gexp M r L d0 d1 (m + 1)) σ i).Pairwise (fun a b => b ≤ a) := by
        intro i hi
        rcases Nat.lt_or_ge i (r + L) with h | h
        · exact hbx i h
        · exact hcopy i h hi
      exact ⟨fun i hi => (hall i hi).1, fun i hi => (hall i hi).2.1, fun i hi => (hall i hi).2.2⟩

end

end Ytosk
