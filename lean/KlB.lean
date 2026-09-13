/-
KlB.lean: κ つきの持ち上げ klift は展開と可換（notes 追記505〜509、tools/probe_kappa.py）。

    klift_oper : ∃ K', klift (A⟦n⟧) o j K' = (klift A o j K)⟦n⟧

K' は写しの位置 j0 + (k·Lb + q) に K (j0 + q) を置く（operK）。証明は Aexp の slift_oper の写し:
写しの Lk は元の列の Lk と同じ（Lk_oper_mir）。段 j0 < o なら両方 0、段 j0 ≥ o なら上昇する列は段 > o で λ = j のまま。
-/
import KlA

namespace TRIO
namespace KlB

open Classical Wset KlA

/-! ## Lk の基本の移し替え -/

theorem lamK_congr {A B : TrioSeq} {o j : ℕ} {K1 K2 : ℕ → ℕ} {y y' : ℕ}
    (h1 : entry A 1 y = entry B 1 y') (h2 : entry A 2 y = entry B 2 y') (hK : K1 y = K2 y') :
    lamK A o j K1 y = lamK B o j K2 y' := by
  unfold lamK; rw [h1, h2, hK]

theorem Lk_congrK {A : TrioSeq} {o j : ℕ} {K1 K2 : ℕ → ℕ} {c : ℕ}
    (hK : ∀ y, y ≤ c → K1 y = K2 y) : Lk A o j K1 c = Lk A o j K2 c := by
  have hlam : ∀ y, y ≤ c → lamK A o j K1 y = lamK A o j K2 y :=
    fun y hy => lamK_congr rfl rfl (hK y hy)
  refine le_antisymm ?_ ?_
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := A) (o := o) (j := j) (K := K2) c
    rw [← hey, ← hlam y (rtg0_le hy)]; exact Lk_le hy
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := A) (o := o) (j := j) (K := K1) c
    rw [← hey, hlam y (rtg0_le hy)]; exact Lk_le hy

theorem Lk_le1 {A : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {a b : ℕ} (h : le1 A a b) :
    Lk A o j K a = Lk A o j K b := by
  obtain ⟨-, -, hr⟩ := h
  induction hr with
  | refl => rfl
  | @tail y w _ hyw ih => rw [ih, Lk_parent hyw]

theorem Lk_take {X : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {l c : ℕ} (hl : l ≤ X.length) (hc : c < l) :
    Lk (X.take l) o j K c = Lk X o j K c := by
  have hlam : ∀ y, y ≤ c → lamK (X.take l) o j K y = lamK X o j K y := by
    intro y hy
    exact lamK_congr (Wset.entry_take (X := X) (l := l) (i := 1) (j := y) (by omega))
      (Wset.entry_take (X := X) (l := l) (i := 2) (j := y) (by omega)) rfl
  refine le_antisymm ?_ ?_
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := X) (o := o) (j := j) (K := K) c
    rw [← hey, ← hlam y (rtg0_le hy)]
    exact Lk_le ((rtg0_take_iff hl hc).2 hy)
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := X.take l) (o := o) (j := j) (K := K) c
    rw [← hey, hlam y (rtg0_le hy)]
    exact Lk_le ((rtg0_take_iff hl hc).1 hy)

theorem Lk_oper_prefix {M : TrioSeq} {o j : ℕ} {K K' : ℕ → ℕ} {n i : ℕ} (L : 1 < M.length)
    (n1 : 1 ≤ n) (hi : i < M.length - 1) (hK : ∀ y, y ≤ i → K' y = K y) :
    Lk (M⟦n⟧) o j K' i = Lk M o j K i := by
  have h1 : (M⟦n⟧).take (M.length - 1) = M.take (M.length - 1) :=
    oper_take_prefix L n1 (le_refl _)
  have hlen : M.length - 1 ≤ (M⟦n⟧).length := by
    have h2 := congrArg List.length h1
    rw [List.length_take, List.length_take] at h2
    omega
  rw [Lk_congrK (A := M⟦n⟧) (K1 := K') (K2 := K) hK,
    ← Lk_take (X := M⟦n⟧) (l := M.length - 1) hlen hi, h1, Lk_take (by omega) hi]

/-! ## 写しの Lk -/

section GexpLk

variable {M : TrioSeq} {j0 Lb d0 d1 n : ℕ} {o j : ℕ} {K K' : ℕ → ℕ}

theorem Lk_gexp_mir {k q : ℕ} (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
    (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hrow : Lk M o j K j0 ≤ Lk M o j K (j0 + Lb))
    (hKlow : ∀ p, p < j0 → K' p = K p)
    (hKmir : ∀ k' q', k' < n → q' < Lb → K' (j0 + (k' * Lb + q')) = K (j0 + q')) :
    Lk (gexp M j0 Lb d0 d1 n) o j K' (j0 + (k * Lb + q)) = Lk M o j K (j0 + q) := by
  classical
  have hn : 0 < n := by omega
  have hXlen : (gexp M j0 Lb d0 d1 n).length = j0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hplt : j0 + (k * Lb + q) < (gexp M j0 Lb d0 d1 n).length := by rw [hXlen]; omega
  have hroot0 : entry (gexp M j0 Lb d0 d1 n) 0 j0 = entry M 0 j0 := gexp_entry_root hlen hn hLb
  have hMj0q : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q) :=
    rtg0_of_window (by omega) (by omega) fun l hl0 hl1 => hup l hl0 (by omega)
  have hXj0p : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) j0 (j0 + (k * Lb + q)) :=
    gexp_rtg0_root hlen hn hLb hup hd0pos _ (by omega) (by omega)
  have hlamLow : ∀ p, p < j0 → lamK (gexp M j0 Lb d0 d1 n) o j K' p = lamK M o j K p :=
    fun p hp => lamK_congr (gexp_entry_low hlen hp) (gexp_entry_low hlen hp) (hKlow p hp)
  have hlamRoot : lamK (gexp M j0 Lb d0 d1 n) o j K' j0 = lamK M o j K j0 := by
    have hK0 := hKmir 0 0 hn hLb
    simp only [Nat.zero_mul, Nat.add_zero] at hK0
    exact lamK_congr (gexp_entry_root hlen hn hLb) (gexp_entry_root hlen hn hLb) hK0
  by_cases hlow : entry M 1 j0 < o
  · have hX1 : entry (gexp M j0 Lb d0 d1 n) 1 j0 < o := by
      rw [gexp_entry_root hlen hn hLb]; exact hlow
    have e1 := Lk_le (A := gexp M j0 Lb d0 d1 n) (o := o) (j := j) (K := K') hXj0p
    rw [lamK_low hX1] at e1
    have e2 := Lk_le (A := M) (o := o) (j := j) (K := K) hMj0q
    rw [lamK_low hlow] at e2
    omega
  have hhigh : o ≤ entry M 1 j0 := by omega
  have H1 : ∀ k' q', k' < n → q' < Lb →
      lamK (gexp M j0 Lb d0 d1 n) o j K' (j0 + (k' * Lb + q')) = lamK M o j K (j0 + q') ∨
      (lamK M o j K (j0 + q') = j ∧
        lamK (gexp M j0 Lb d0 d1 n) o j K' (j0 + (k' * Lb + q')) = j) ∨
      (q' = 0 ∧ lamK (gexp M j0 Lb d0 d1 n) o j K' (j0 + (k' * Lb + q')) = j) := by
    intro k' q' hk' hq'
    have e1 : entry (gexp M j0 Lb d0 d1 n) 1 (j0 + (k' * Lb + q'))
        = entry M 1 (j0 + q') + (if le1 M j0 (j0 + q') then k' * d1 else 0) :=
      gexp_entry1_mir hlen hk' hq'
    have e2 : entry (gexp M j0 Lb d0 d1 n) 2 (j0 + (k' * Lb + q')) = entry M 2 (j0 + q') :=
      gexp_entry2_mir hlen hk' hq' d0 d1
    by_cases hg : le1 M j0 (j0 + q')
    · rw [if_pos hg] at e1
      rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
      · by_cases hkd : k' * d1 = 0
        · left
          exact lamK_congr (by rw [e1, hkd, Nat.add_zero]) e2 (hKmir k' 0 hk' hq')
        · right; right
          refine ⟨rfl, lamK_high ?_⟩
          rw [e1]; simp only [Nat.add_zero]; omega
      · have hlt := le1_entry1_lt hg (by omega)
        right; left
        exact ⟨lamK_high (by omega), lamK_high (by rw [e1]; omega)⟩
    · rw [if_neg hg] at e1
      left
      exact lamK_congr (by rw [e1, Nat.add_zero]) e2 (hKmir k' q' hk' hq')
  refine le_antisymm ?_ ?_
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := M) (o := o) (j := j) (K := K) (j0 + q)
    have hyle : y ≤ j0 + q := nextrel0_rtrancl_index_le hy
    rcases Nat.lt_or_ge y j0 with hyj | hyj
    · have hMyj0 := (le0_of_le0_le0 (X := M) ⟨by omega, by omega, hy⟩
        ⟨by omega, by omega, hMj0q⟩ hyj).2.2
      have hXyj0 : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) y j0 :=
        rtg0_of_agree_last (M := M) (X := gexp M j0 Lb d0 d1 n) (by rw [hXlen]; omega)
          (fun x hx => gexp_getD_low hlen (by omega)) hroot0 hMyj0
      rw [← hey, ← hlamLow y hyj]
      exact Lk_le (hXyj0.trans hXj0p)
    · obtain ⟨q', rfl⟩ : ∃ q', y = j0 + q' := ⟨y - j0, by omega⟩
      have hq'lt : q' < Lb := by omega
      have hmir : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n))
          (j0 + (k * Lb + q')) (j0 + (k * Lb + q)) :=
        gexp_rtg0_mir hlen hk hy q rfl hq
      rcases H1 k q' hk hq'lt with he | ⟨he1, _⟩ | ⟨rfl, _⟩
      · rw [← hey, ← he]; exact Lk_le hmir
      · rw [← hey, he1]; exact Lk_le_j _
      · rw [← hey]
        have := Lk_le (A := gexp M j0 Lb d0 d1 n) (o := o) (j := j) (K := K') hXj0p
        rw [hlamRoot] at this
        simpa using this
  · obtain ⟨y, hy, hey⟩ :=
      Lk_mem (A := gexp M j0 Lb d0 d1 n) (o := o) (j := j) (K := K') (j0 + (k * Lb + q))
    rcases Nat.lt_or_ge y j0 with hyj | hyj
    · have hXyj0 := (le0_of_le0_le0 (X := gexp M j0 Lb d0 d1 n)
        ⟨by rw [hXlen]; omega, hplt, hy⟩ ⟨by rw [hXlen]; omega, hplt, hXj0p⟩ hyj).2.2
      have hMyj0 : Relation.ReflTransGen (nextrel0 M) y j0 :=
        rtg0_of_agree_last (M := gexp M j0 Lb d0 d1 n) (X := M) (by omega)
          (fun x hx => (gexp_getD_low hlen (by omega)).symm) hroot0.symm hXyj0
      rw [← hey, hlamLow y hyj]
      exact Lk_le (hMyj0.trans hMj0q)
    · obtain ⟨k', q', hk', hq', rfl, hcase⟩ :=
        gexp_chain_inversion hlen hk hq hup hd0e y hy hyj
      rcases H1 k' q' (by omega) hq' with he | ⟨_, he2⟩ | ⟨_, he2⟩
      · rw [← hey, he]
        rcases hcase with ⟨_, hM⟩ | ⟨_, hM⟩
        · exact Lk_le hM
        · have h2 : Lk M o j K (j0 + q) ≤ Lk M o j K j0 := Lk_mono hMj0q
          have h3 : Lk M o j K (j0 + Lb) ≤ lamK M o j K (j0 + q') := Lk_le hM
          omega
      · rw [← hey, he2]; exact Lk_le_j _
      · rw [← hey, he2]; exact Lk_le_j _

theorem Lk_gexp_mir_flat {k q : ℕ} (hlen : j0 + Lb + 1 = M.length)
    (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hKlow : ∀ p, p < j0 → K' p = K p)
    (hKmir : ∀ k' q', k' < n → q' < Lb → K' (j0 + (k' * Lb + q')) = K (j0 + q')) :
    Lk (gexp M j0 Lb 0 0 n) o j K' (j0 + (k * Lb + q)) = Lk M o j K (j0 + q) := by
  classical
  have hn : 0 < n := by omega
  have hXlen : (gexp M j0 Lb 0 0 n).length = j0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hplt : j0 + (k * Lb + q) < (gexp M j0 Lb 0 0 n).length := by
    rw [hXlen]; omega
  have hMj0q : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q) :=
    rtg0_of_window (by omega) (by omega) fun l hl0 hl1 => hup l hl0 (by omega)
  have hXrp : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n))
      (j0 + k * Lb) (j0 + (k * Lb + q)) :=
    gexp_flat_rtg0_root hlen hLb hk hq hn hup
  have hlowX : ∀ y, y < j0 →
      (Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n)) y (j0 + k * Lb)
        ↔ Relation.ReflTransGen (nextrel0 M) y j0) := by
    intro y hy
    constructor
    · intro h
      rcases h.cases_tail with heq | ⟨w, hw1, hw2⟩
      · exact absurd heq (by omega)
      · have hwj : w < j0 := by
          by_contra hcon
          have hlt : entry (gexp M j0 Lb 0 0 n) 0 w
              < entry (gexp M j0 Lb 0 0 n) 0 (j0 + k * Lb) := hw2.2.2.2.1
          rw [gexp_flat_root_entry hlen hk hLb] at hlt
          have hge := gexp_flat_ge (n := n) hlen hLb hup w (by omega)
            (by have := nextrel0_index_less hw2; omega)
          omega
        exact ((gexp_flat_rtg0_low hlen hLb hn hwj).1 hw1).tail
          ((nextrel0_flat_root hlen hLb hk hwj hup).1 hw2)
    · intro h
      rcases h.cases_tail with heq | ⟨w, hw1, hw2⟩
      · exact absurd heq (by omega)
      · have hwj : w < j0 := nextrel0_index_less hw2
        exact ((gexp_flat_rtg0_low hlen hLb hn hwj).2 hw1).tail
          ((nextrel0_flat_root hlen hLb hk hwj hup).2 hw2)
  have hlamMir : ∀ q', q' < Lb →
      lamK (gexp M j0 Lb 0 0 n) o j K' (j0 + (k * Lb + q')) = lamK M o j K (j0 + q') :=
    fun q' hq' => lamK_congr (gexp_flat_entry hlen hk hq') (gexp_flat_entry hlen hk hq')
      (hKmir k q' hk hq')
  have hlamLow : ∀ p, p < j0 → lamK (gexp M j0 Lb 0 0 n) o j K' p = lamK M o j K p :=
    fun p hp => lamK_congr (gexp_entry_low hlen hp) (gexp_entry_low hlen hp) (hKlow p hp)
  refine le_antisymm ?_ ?_
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := M) (o := o) (j := j) (K := K) (j0 + q)
    have hyle : y ≤ j0 + q := nextrel0_rtrancl_index_le hy
    rcases Nat.lt_or_ge y j0 with hyj | hyj
    · have hMyj0 := (le0_of_le0_le0 (X := M) ⟨by omega, by omega, hy⟩
        ⟨by omega, by omega, hMj0q⟩ hyj).2.2
      rw [← hey, ← hlamLow y hyj]
      exact Lk_le (((hlowX y hyj).2 hMyj0).trans hXrp)
    · obtain ⟨q', rfl⟩ : ∃ q', y = j0 + q' := ⟨y - j0, by omega⟩
      have hq'lt : q' < Lb := by omega
      have hmir : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n))
          (j0 + (k * Lb + q')) (j0 + (k * Lb + q)) :=
        gexp_rtg0_mir hlen hk hy q rfl hq
      rw [← hey, ← hlamMir q' hq'lt]
      exact Lk_le hmir
  · obtain ⟨y, hy, hey⟩ :=
      Lk_mem (A := gexp M j0 Lb 0 0 n) (o := o) (j := j) (K := K') (j0 + (k * Lb + q))
    rcases Nat.lt_or_ge y j0 with hyj | hyj
    · have hXyr := (le0_of_le0_le0 (X := gexp M j0 Lb 0 0 n)
        ⟨by rw [hXlen]; omega, hplt, hy⟩ ⟨by rw [hXlen]; omega, hplt, hXrp⟩
        (by omega)).2.2
      rw [← hey, hlamLow y hyj]
      exact Lk_le (((hlowX y hyj).1 hXyr).trans hMj0q)
    · obtain ⟨q', hq', rfl, hM⟩ :=
        gexp_flat_chain_inversion hlen hLb hk hq hup y hy hyj
      rw [← hey, hlamMir q' hq']
      exact Lk_le hM

end GexpLk

/-! ## 展開の形 -/

/-- 写しの位置 j0 + (k·Lb + q) に K (j0 + q) を置く。 -/
def operK (j0 Lb : ℕ) (K : ℕ → ℕ) : ℕ → ℕ :=
  fun p => if p < j0 then K p else K (j0 + (p - j0) % Lb)

theorem operK_low {j0 Lb p : ℕ} {K : ℕ → ℕ} (hp : p < j0) : operK j0 Lb K p = K p := by
  unfold operK; rw [if_pos hp]

theorem operK_mir {j0 Lb k q : ℕ} {K : ℕ → ℕ} (hq : q < Lb) :
    operK j0 Lb K (j0 + (k * Lb + q)) = K (j0 + q) := by
  unfold operK
  rw [if_neg (by omega), show j0 + (k * Lb + q) - j0 = q + k * Lb by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]

theorem operK_prefix {j0 Lb p : ℕ} {K : ℕ → ℕ} (hp : p < j0 + Lb) : operK j0 Lb K p = K p := by
  rcases Nat.lt_or_ge p j0 with h | h
  · exact operK_low h
  · have := operK_mir (j0 := j0) (Lb := Lb) (k := 0) (q := p - j0) (K := K) (by omega)
    simp only [Nat.zero_mul, Nat.zero_add] at this
    rwa [show j0 + (p - j0) = p by omega] at this

open Classical in
theorem Lk_oper_mir {M : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {n j0 Lb k q : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (_hn : 0 < n)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0 : parent M (srow M (M.length - 1)) (M.length - 1) = j0)
    (hk : k < n) (hq : q < Lb) :
    Lk (M⟦n⟧) o j (operK j0 Lb K) (j0 + (k * Lb + q)) = Lk M o j K (j0 + q) := by
  classical
  have hL : M.length - 1 ≠ 0 := by omega
  have hj1 : M.length - 1 = j0 + Lb := by omega
  have hnr : nextR M (srow M (M.length - 1)) j0 (M.length - 1) := by
    rw [← hj0]; exact parent_nextR hp
  have hsr2 : srow M (M.length - 1) = 0 ∨ srow M (M.length - 1) = 1
      ∨ srow M (M.length - 1) = 2 := by
    unfold srow; split_ifs <;> omega
  have hrtg : Relation.ReflTransGen (nextrel0 M) j0 (j0 + Lb) := by
    rw [← hj1]
    rcases hsr2 with hs | hs | hs <;> rw [hs] at hnr <;> unfold nextR at hnr
    · rw [if_pos rfl] at hnr
      exact Relation.ReflTransGen.single hnr
    · rw [if_neg (by omega), if_pos rfl] at hnr
      exact hnr.2.2.2.2.1.2.2
    · rw [if_neg (by omega), if_neg (by omega)] at hnr
      exact rtg0_of_rtg1 hnr.2.2.2.2.1.2.2
  have hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l :=
    window_of_rtg0 hrtg (by omega)
  rw [oper_eq_gexp_gen n hL hz hp, hj0,
    show M.length - 1 - j0 = Lb from by omega, hj1]
  by_cases h0 : 0 < srow M (j0 + Lb)
  · have hd0pos : 0 < entry M 0 (j0 + Lb) - entry M 0 j0 := by
      have := hup (j0 + Lb) (by omega) (le_refl _); omega
    have hd0e : entry M 0 (j0 + Lb) = entry M 0 j0
        + (entry M 0 (j0 + Lb) - entry M 0 j0) := by omega
    have hle1 : le1 M j0 (j0 + Lb) := by
      rw [hj1] at hsr2
      rcases hsr2 with hs | hs | hs
      · exact absurd hs (by omega)
      · rw [hj1, hs] at hnr
        unfold nextR at hnr
        rw [if_neg (by omega), if_pos rfl] at hnr
        exact ⟨hnr.1, hnr.2.1, Relation.ReflTransGen.single hnr⟩
      · rw [hj1, hs] at hnr
        unfold nextR at hnr
        rw [if_neg (by omega), if_neg (by omega)] at hnr
        exact hnr.2.2.2.2.1
    rw [if_pos h0]
    exact Lk_gexp_mir hlen hLb hk hq hup hd0pos hd0e (le_of_eq (Lk_le1 hle1))
      (fun p hp => operK_low hp) (fun k' q' _ hq' => operK_mir hq')
  · rw [if_neg h0, if_neg (by omega)]
    exact Lk_gexp_mir_flat hlen hLb hk hq hup (fun p hp => operK_low hp)
      (fun k' q' _ hq' => operK_mir hq')

/-! ## klift は展開と可換 -/

theorem klift_take {A : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {l : ℕ} (hl : l ≤ A.length) :
    klift (A.take l) o j K = (klift A o j K).take l := by
  refine List.ext_getElem (by simp) ?_
  intro i hi1 hi2
  rw [klift_length, List.length_take] at hi1
  have hiA : i < A.length := by omega
  have hil : i < l := by omega
  rw [← entry_triple (X := klift (A.take l) o j K)
      (by rw [klift_length, List.length_take]; omega),
    ← entry_triple (X := (klift A o j K).take l)
      (by rw [List.length_take, klift_length]; omega)]
  have hL : ∀ y, entry ((klift A o j K).take l) y i = entry (klift A o j K) y i :=
    fun y => Wset.entry_take (X := klift A o j K) (l := l) (i := y) (j := i) hil
  have hR : ∀ y, entry (A.take l) y i = entry A y i :=
    fun y => Wset.entry_take (X := A) (l := l) (i := y) (j := i) hil
  rw [hL 0, hL 1, hL 2, entry0_klift, entry0_klift, entry2_klift, entry2_klift,
    entry1_klift (by rw [List.length_take]; omega), entry1_klift hiA, hR 0,
    hR 1, hR 2, Lk_take hl hil]

theorem klift_dropLast {A : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} :
    klift A.dropLast o j K = (klift A o j K).dropLast := by
  rw [List.dropLast_eq_take, List.dropLast_eq_take, klift_length, klift_take (by omega)]

open Classical in
theorem klift_oper_main {A : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {n j0 Lb d0 d1 : ℕ}
    (hlen : j0 + Lb + 1 = A.length) (hLb : 0 < Lb) (hn : 0 < n)
    (hz : ¬ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0 ∧
      entry A 2 (A.length - 1) = 0))
    (hp : hasParent A (srow A (A.length - 1)) (A.length - 1))
    (hj0 : parent A (srow A (A.length - 1)) (A.length - 1) = j0)
    (hAn : A⟦n⟧ = gexp A j0 Lb d0 d1 n)
    (hBn : (klift A o j K)⟦n⟧ = gexp (klift A o j K) j0 Lb d0 d1 n) :
    klift (A⟦n⟧) o j (operK j0 Lb K) = (klift A o j K)⟦n⟧ := by
  classical
  have hBlen : (klift A o j K).length = A.length := klift_length A o j K
  have hlenB : j0 + Lb + 1 = (klift A o j K).length := by rw [hBlen]; exact hlen
  have hlenA : (A⟦n⟧).length = j0 + n * Lb := by rw [hAn]; exact gexp_length hlen
  have hlenBn : ((klift A o j K)⟦n⟧).length = j0 + n * Lb := by
    rw [hBn]; exact gexp_length hlenB
  refine List.ext_getElem (by rw [klift_length, hlenA, hlenBn]) ?_
  intro i hi1 _
  rw [klift_length, hlenA] at hi1
  rw [← entry_triple (X := klift (A⟦n⟧) o j (operK j0 Lb K)) (by rw [klift_length, hlenA]; omega),
    ← entry_triple (X := (klift A o j K)⟦n⟧) (by rw [hlenBn]; omega)]
  rcases Nat.lt_or_ge i j0 with hlo | hhi
  · have hiA : i < A.length := by omega
    have hA0 : entry (A⟦n⟧) 0 i = entry A 0 i := by rw [hAn]; exact gexp_entry_low hlen hlo
    have hA1 : entry (A⟦n⟧) 1 i = entry A 1 i := by rw [hAn]; exact gexp_entry_low hlen hlo
    have hA2 : entry (A⟦n⟧) 2 i = entry A 2 i := by rw [hAn]; exact gexp_entry_low hlen hlo
    have hLk : Lk (A⟦n⟧) o j (operK j0 Lb K) i = Lk A o j K i :=
      Lk_oper_prefix (by omega) hn (by omega) (fun y hy => operK_low (by omega))
    have hB0 : entry ((klift A o j K)⟦n⟧) 0 i = entry A 0 i := by
      rw [hBn, gexp_entry_low hlenB hlo, entry0_klift]
    have hB1 : entry ((klift A o j K)⟦n⟧) 1 i = entry A 1 i + Lk A o j K i := by
      rw [hBn, gexp_entry_low hlenB hlo, entry1_klift hiA]
    have hB2 : entry ((klift A o j K)⟦n⟧) 2 i = entry A 2 i := by
      rw [hBn, gexp_entry_low hlenB hlo, entry2_klift]
    rw [entry0_klift, entry2_klift, entry1_klift (by rw [hlenA]; omega),
      hA0, hA1, hA2, hLk, hB0, hB1, hB2]
  · obtain ⟨k, q, hk, hq, rfl⟩ := gexp_pos_decomp hLb hhi hi1
    have hqA : j0 + q < A.length := by omega
    have hA0 : entry (A⟦n⟧) 0 (j0 + (k * Lb + q)) = entry A 0 (j0 + q) + k * d0 := by
      rw [hAn]; exact gexp_entry0_mir hlen hk hq
    have hA1 : entry (A⟦n⟧) 1 (j0 + (k * Lb + q))
        = entry A 1 (j0 + q) + (if le1 A j0 (j0 + q) then k * d1 else 0) := by
      rw [hAn]; exact gexp_entry1_mir hlen hk hq
    have hA2 : entry (A⟦n⟧) 2 (j0 + (k * Lb + q)) = entry A 2 (j0 + q) := by
      rw [hAn]; exact gexp_entry2_mir hlen hk hq d0 d1
    have hLk : Lk (A⟦n⟧) o j (operK j0 Lb K) (j0 + (k * Lb + q)) = Lk A o j K (j0 + q) :=
      Lk_oper_mir hlen hLb hn hz hp hj0 hk hq
    have hB0 : entry ((klift A o j K)⟦n⟧) 0 (j0 + (k * Lb + q)) = entry A 0 (j0 + q) + k * d0 := by
      rw [hBn, gexp_entry0_mir hlenB hk hq, entry0_klift]
    have hB1 : entry ((klift A o j K)⟦n⟧) 1 (j0 + (k * Lb + q))
        = entry A 1 (j0 + q) + Lk A o j K (j0 + q)
          + (if le1 A j0 (j0 + q) then k * d1 else 0) := by
      rw [hBn, gexp_entry1_mir hlenB hk hq, entry1_klift hqA]
      congr 1
      exact if_congr le1_klift rfl rfl
    have hB2 : entry ((klift A o j K)⟦n⟧) 2 (j0 + (k * Lb + q)) = entry A 2 (j0 + q) := by
      rw [hBn, gexp_entry2_mir hlenB hk hq d0 d1, entry2_klift]
    rw [entry0_klift, entry2_klift, entry1_klift (by rw [hlenA]; omega),
      hA0, hA1, hA2, hLk, hB0, hB1, hB2]
    have he : entry A 1 (j0 + q) + (if le1 A j0 (j0 + q) then k * d1 else 0) + Lk A o j K (j0 + q)
        = entry A 1 (j0 + q) + Lk A o j K (j0 + q) + (if le1 A j0 (j0 + q) then k * d1 else 0) := by
      omega
    rw [he]

open Classical in
/-- ★ κ つきの持ち上げは展開と可換（κ を付け直す）。 -/
theorem klift_oper {A : TrioSeq} {o j : ℕ} (ho : 1 ≤ o) (K : ℕ → ℕ) (n : ℕ) :
    ∃ K', klift (A⟦n⟧) o j K' = (klift A o j K)⟦n⟧ := by
  classical
  have hBlen : (klift A o j K).length = A.length := klift_length A o j K
  have hj1 : (klift A o j K).length - 1 = A.length - 1 := by rw [hBlen]
  by_cases hL : A.length - 1 = 0
  · exact ⟨K, by rw [oper_eq_self_of_short n hL, oper_eq_self_of_short n (by rw [hj1]; exact hL)]⟩
  · have hAlen : 1 < A.length := by omega
    have hj1lt : A.length - 1 < A.length := by omega
    have hLB : (klift A o j K).length - 1 ≠ 0 := by rw [hj1]; exact hL
    have hpred : Pred (klift A o j K) = (klift A o j K).dropLast := by
      unfold Pred; rw [if_neg (by rw [hBlen]; omega)]
    have hpredA : Pred A = A.dropLast := by
      unfold Pred; rw [if_neg (by omega)]
    have hzero : (entry (klift A o j K) 0 ((klift A o j K).length - 1) = 0 ∧
        entry (klift A o j K) 1 ((klift A o j K).length - 1) = 0 ∧
        entry (klift A o j K) 2 ((klift A o j K).length - 1) = 0)
        ↔ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0 ∧
          entry A 2 (A.length - 1) = 0) := by
      rw [hj1, entry0_klift, entry2_klift]
      have h1 := entry1_klift_pos (K := K) (j := j) ho hj1lt
      omega
    have hsrB : srow (klift A o j K) ((klift A o j K).length - 1) = srow A (A.length - 1) := by
      rw [hj1]; exact srow_klift ho hj1lt
    by_cases hz0 : entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0 ∧
        entry A 2 (A.length - 1) = 0
    · refine ⟨K, ?_⟩
      rw [oper_eq_pred_of_zero n hL hz0, oper_eq_pred_of_zero n hLB (hzero.2 hz0), hpred, hpredA]
      exact klift_dropLast
    · by_cases hp : hasParent A (srow A (A.length - 1)) (A.length - 1)
      · have hnr := parent_nextR hp
        have hj0lt : parent A (srow A (A.length - 1)) (A.length - 1) < A.length - 1 :=
          nextR_index_lt hnr
        have hparB : parent (klift A o j K) (srow (klift A o j K) ((klift A o j K).length - 1))
            ((klift A o j K).length - 1) = parent A (srow A (A.length - 1)) (A.length - 1) := by
          rw [hsrB, hj1, parent_klift]
        have hpB : hasParent (klift A o j K) (srow (klift A o j K) ((klift A o j K).length - 1))
            ((klift A o j K).length - 1) := by
          rw [hsrB, hj1]; exact hasParent_klift.2 hp
        have hzB : ¬ (entry (klift A o j K) 0 ((klift A o j K).length - 1) = 0 ∧
            entry (klift A o j K) 1 ((klift A o j K).length - 1) = 0 ∧
            entry (klift A o j K) 2 ((klift A o j K).length - 1) = 0) :=
          fun h => hz0 (hzero.1 h)
        have hd1eq : (if 1 < srow A (A.length - 1)
              then entry (klift A o j K) 1 (A.length - 1)
                - entry (klift A o j K) 1 (parent A (srow A (A.length - 1)) (A.length - 1))
              else 0)
            = (if 1 < srow A (A.length - 1)
              then entry A 1 (A.length - 1)
                - entry A 1 (parent A (srow A (A.length - 1)) (A.length - 1))
              else 0) := by
          split_ifs with h2
          · have hn2 : nextrel2 A (parent A (srow A (A.length - 1)) (A.length - 1))
                (A.length - 1) := by
              have h := hnr
              unfold nextR at h
              rw [if_neg (by omega), if_neg (by omega)] at h
              exact h
            rw [entry1_klift hj1lt, entry1_klift (by omega), Lk_le1 hn2.2.2.2.2.1]
            omega
          · rfl
        have hBn : (klift A o j K)⟦n⟧ = gexp (klift A o j K)
            (parent A (srow A (A.length - 1)) (A.length - 1))
            (A.length - 1 - parent A (srow A (A.length - 1)) (A.length - 1))
            (if 0 < srow A (A.length - 1) then entry A 0 (A.length - 1)
              - entry A 0 (parent A (srow A (A.length - 1)) (A.length - 1))
              else 0)
            (if 1 < srow A (A.length - 1) then entry A 1 (A.length - 1)
              - entry A 1 (parent A (srow A (A.length - 1)) (A.length - 1))
              else 0) n := by
          rw [oper_eq_gexp_gen n hLB hzB hpB, hparB, hsrB, hj1, entry0_klift,
            entry0_klift, hd1eq]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · refine ⟨K, ?_⟩
          rw [oper_zero_take hL hz0 hp, oper_zero_take hLB hzB hpB, hparB, klift_take (by omega)]
        · exact ⟨_, klift_oper_main (by omega) (by omega) hn hz0 hp rfl
            (oper_eq_gexp_gen n hL hz0 hp) hBn⟩
      · have hpB : ¬ hasParent (klift A o j K) (srow (klift A o j K) ((klift A o j K).length - 1))
            ((klift A o j K).length - 1) := by
          rw [hsrB, hj1]
          exact fun h => hp (hasParent_klift.1 h)
        refine ⟨K, ?_⟩
        rw [oper_eq_pred_of_noParent n hL hz0 hp,
          oper_eq_pred_of_noParent n hLB (fun h => hz0 (hzero.1 h)) hpB, hpred, hpredA]
        exact klift_dropLast

end KlB
end TRIO
