/-
**t = 2 の M[n] の NoGapP の仮定 hpre: r + L より前の行 1 の親の v は M と同じ。**

行 1 の親 p（行 2 は 0、葉でない）の v から届く呼び出しは、次の集合 G に入る（`gt_noreach`）。
- p の祖先 a の v（a の行 2 が 0 でないなら、p は a ののりしろの子の下にない、`GA`）、
- そのような a ののりしろの子 j の部分木の列（o と v、`GB`）。のりしろの子は兄弟の中で先頭にある
  （SibDec・Z1C）ので、この部分木はすべて p より左（`gb_lt`）。
v の辺は P_1（行 2 は 0 の列へ）・上げ（祖先への上げは UAB で p をのりしろの子の下に置かない、次の列への
上げはのりしろの部分木の中にとどまる）・のりしろの孫の o で、どれも G の中に戻る。
t = 2 の N = M[n] の種（o(q)、q ≠ r なら v(q)・o(P_0 q)、M で x − 1 が x へ上げるなら v(x − 1)）は
G に入らない: o(q)・o(P_0 q) の部分木は x′ = r + L ≥ p を含み、v(q) は p を q ののりしろの子の下に置き
（q ≠ r なら q の子はすべてのりしろ）、x − 1 は p より右。よって agree_N で v_N(p) = v_M(p)。
実測（d3s・deep2・deep3・C′ の t = 2、n = 2, 3、計 600 万件、例外 0）。
-/
import Ytosk.V3PhiGapT2
import Ytosk.V3ExpT2X
import Ytosk.V3InvExpand

namespace Ytosk

open T

/-- The `v` calls on the ancestors of `p` reached from `v(p)`. -/
def GA (M : Mat) (p a : Nat) : Prop :=
  Anc0 M a p ∧ (entry M 2 a ≠ 0 → ∀ j, j ∈ children M a → col M j = bump M a → ¬ Anc0 M j p)

/-- The columns in a bump subtree of such an ancestor. -/
def GB (M : Mat) (p d : Nat) : Prop :=
  ∃ a j, GA M p a ∧ entry M 2 a ≠ 0 ∧ j ∈ children M a ∧ col M j = bump M a ∧ Anc0 M j d

/-- The closed set of calls. -/
def GT (M : Mat) (p : Nat) (b : Bool) (i : Nat) : Prop := (b = false ∧ GA M p i) ∨ GB M p i

section
variable {M : Mat} (hS : SInv M)
include hS

/-- **The bump children come first**: a bump child is before every non-bump child. -/
theorem bump_lt_nonbump {a j b : Nat} (he : entry M 2 a ≠ 0) (hj : j ∈ children M a)
    (hjb : col M j = bump M a) (hb : b ∈ children M a) (hbb : col M b ≠ bump M a) : j < b := by
  by_contra hlt
  have hjb' : j ≠ b := fun e => hbb (e ▸ hjb)
  have hbj : b < j := by omega
  obtain ⟨l1, l2, hl⟩ := List.append_of_mem hb
  have hsort := children_sorted M a
  rw [hl, List.pairwise_append] at hsort
  have hj2 : j ∈ l2 := by
    have hjm := hj
    rw [hl] at hjm
    rcases List.mem_append.mp hjm with h | h
    · have := hsort.2.2 j h b (by simp); omega
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h hjb'
      · exact h
  have hle := sib_le hS.sibDec l2 l1 b hl j hj2
  have hpb : par M 0 b = some a := (mem_children_iff.mp hb).2
  have h0 := hS.r0p b a hpb
  have he2a : entry M 2 a = 1 := by have := hS.z2 a; omega
  have h1 := hS.z1c a b he2a hb
  have h2 := hS.z2 b
  rw [hjb] at hle
  unfold colLe bump at hle
  apply hbb
  unfold bump
  have e0 : (col M b).1 = entry M 0 b := rfl
  have e1 : (col M b).2.1 = entry M 1 b := rfl
  have e2 : (col M b).2.2 = entry M 2 b := rfl
  simp only at hle
  rw [e0, e1, e2] at hle
  have f1 : entry M 1 b = entry M 1 a := by omega
  have f2 : entry M 2 b = 1 := by omega
  rw [show col M b = (entry M 0 b, entry M 1 b, entry M 2 b) from rfl, h0, f1, f2]

variable {p : Nat} (hpl : p < M.length) (hp2 : entry M 2 p = 0)
include hpl hp2

/-- **A bump subtree lies left of `p`.** -/
theorem gb_lt {i : Nat} (hG : GB M p i) : ∀ d, Anc0 M i d → d < p := by
  intro d hid
  obtain ⟨a, j, ⟨hap, hcond⟩, he, hj, hjb, hji⟩ := hG
  have hjd : Anc0 M j d := hji.trans hid
  have hap' : a ≠ p := fun e => he (e ▸ hp2)
  obtain ⟨b, hba, hbp⟩ := anc0_child hap hap'
  have hbl : b < M.length := by have := hbp.le; omega
  have hb : b ∈ children M a := mem_children_iff.mpr ⟨hbl, hba⟩
  have hbb : col M b ≠ bump M a := fun h => hcond he b hb h hbp
  have hjb' := bump_lt_nonbump hS he hj hjb hb hbb
  have hja : par M 0 j = some a := (mem_children_iff.mp hj).2
  by_contra hdp
  have hjbA : Anc0 M j b := anc_between hjd b (by omega) (by have := hbp.le; omega)
  have hjaA : Anc0 M j a := anc0_par hjbA (by omega) hba
  have := hjaA.le
  have := par_lt M 0 j a hja
  omega

omit hS hpl hp2 in
theorem entry1_lt {i : Nat} (h1 : entry M 1 i ≠ 0) : i < M.length := by
  by_contra h; exact h1 (entry_out' (by omega) 1)

/-- **The closure of `v(p)` stays in `GT`** (`p` not a leaf, row 2 zero). -/
theorem gt_noreach {S : Bool → Nat → Prop} (hpd : ∃ c, Anc0 M p c ∧ c ≠ p)
    (hSd : ∀ b i, S b i → ¬ GT M p b i) : ∀ {b i}, DepS M S b i → GT M p b i → False := by
  intro b i h
  induction h with
  | seed hs => intro hG; exact hSd _ _ hs hG
  | ochild hc _ _ _ ih =>
    intro hG
    rcases hG with ⟨hb, _⟩ | ⟨a, j, hA, he, hj, hjb, hji⟩
    · cases hb
    · exact ih (Or.inr ⟨a, j, hA, he, hj, hjb, hji.trans (anc0_of_child hc)⟩)
  | ov _ ih =>
    intro hG
    rcases hG with ⟨hb, _⟩ | hB
    · cases hb
    · exact ih (Or.inr hB)
  | @vpar i m h1 hm _ ih =>
    intro hG
    apply ih
    have hil := entry1_lt h1
    have hm2 : entry M 2 m = 0 := by
      have := hS.z2 m
      by_contra hne
      exact no_par1_of_e2 hS.z1c hil (by omega) hm
    have hmi := anc0_of_par M 1 m i hm
    have hGA : Anc0 M m p → GT M p false m := fun hA => Or.inl ⟨rfl, hA, fun h => absurd hm2 h⟩
    rcases hG with ⟨_, hap, _⟩ | ⟨a, j, hA, he, hj, hjb, hji⟩
    · exact hGA (hmi.trans hap)
    · rcases anc0_total hmi hji with h | h
      · by_cases hmj : m = j
        · subst hmj; exact Or.inr ⟨a, m, hA, he, hj, hjb, Anc0.refl m⟩
        · exact hGA ((anc0_par h hmj (mem_children_iff.mp hj).2).trans hA.1)
      · exact Or.inr ⟨a, j, hA, he, hj, hjb, h⟩
  | @vupg i k h1 h2 hk _ ih =>
    intro hG
    apply ih
    have hil := entry1_lt h1
    obtain ⟨m, hm, hkm, _, hcase⟩ := upg_facts hk
    rcases hG with ⟨_, hap, _⟩ | ⟨a, j, ⟨hap, hcond⟩, he, hj, hjb, hji⟩
    · rcases hcase with hk1 | ⟨hA, hki⟩
      · exfalso
        rw [hk1] at hk
        have hleaf := leaf_of_upg_next hS.r0p hk
        obtain ⟨c, hpc, hcp⟩ := hpd
        have := hleaf c (hap.trans hpc)
        have := hleaf p hap
        omega
      · refine Or.inl ⟨rfl, hA.trans hap, fun _ j hj hjb hjp => ?_⟩
        have hU := hS.uab i k hk (by omega) j hj hjb
        have hjk : par M 0 j = some k := (mem_children_iff.mp hj).2
        rcases anc0_total hjp hap with h | h
        · exact hU h
        · by_cases hij : i = j
          · subst hij; exact hU (Anc0.refl _)
          · have := anc0_antisymm (anc0_par h hij hjk) hA
            omega
    · have hja : par M 0 j = some a := (mem_children_iff.mp hj).2
      have hjaL := par_lt M 0 j a hja
      rcases hcase with hk1 | ⟨hA, hki⟩
      · refine Or.inr ⟨a, j, ⟨hap, hcond⟩, he, hj, hjb, ?_⟩
        have hmi := anc0_of_par M 1 m i hm
        rcases anc0_total hmi hji with h | h
        · by_cases hmj : m = j
          · subst hmj; exact Anc0.step hkm (Anc0.refl _)
          · exfalso
            have hma := anc0_par h hmj hja
            have hip := gb_lt hS hpl hp2 ⟨a, j, ⟨hap, hcond⟩, he, hj, hjb, hji⟩ i (Anc0.refl i)
            have hak : Anc0 M a k := anc_between hap k (by have := hji.le; omega) (by omega)
            have ham := anc0_par hak (by have := hji.le; omega) hkm
            have hmaE := anc0_antisymm hma ham
            subst hmaE
            have := hS.z2 m
            exact no_par1_of_e2 hS.z1c hil (by omega) hm
        · exact Anc0.step hkm h
      · rcases anc0_total hA hji with h | h
        · by_cases hkj : k = j
          · subst hkj; exact Or.inr ⟨a, k, ⟨hap, hcond⟩, he, hj, hjb, Anc0.refl k⟩
          · have hka := anc0_par h hkj hja
            refine Or.inl ⟨rfl, hka.trans hap, fun _ j' hj' hj'b hj'p => ?_⟩
            have hU := hS.uab i k hk (by omega) j' hj' hj'b
            have haj : Anc0 M a j := Anc0.step hja (Anc0.refl a)
            rcases anc0_total hj'p hap with h' | h'
            · exact hU (h'.trans (haj.trans hji))
            · by_cases haj' : a = j'
              · subst haj'; exact hU (haj.trans hji)
              · have hj'k : par M 0 j' = some k := (mem_children_iff.mp hj').2
                have := anc0_antisymm (anc0_par h' haj' hj'k) hka
                subst this
                exact hS.uab i a hk (by omega) j hj hjb hji
        · exact Or.inr ⟨a, j, ⟨hap, hcond⟩, he, hj, hjb, h⟩
  | @vbump i j k h1 h2 hj hjb hk _ ih =>
    intro hG
    apply ih
    rcases hG with ⟨_, hA⟩ | ⟨a, j0, hA, he, hj0, hj0b, hj0i⟩
    · exact Or.inr ⟨i, j, hA, h2, hj, hjb, anc0_of_child hk⟩
    · exact Or.inr ⟨a, j0, hA, he, hj0, hj0b, hj0i.trans ((anc0_of_child hj).trans (anc0_of_child hk))⟩

/-- **`v(p)` depends on no seed outside `GT`.** -/
theorem not_depS_rowpar {S : Bool → Nat → Prop} (hpd : ∃ c, Anc0 M p c ∧ c ≠ p)
    (hSd : ∀ b i, S b i → ¬ GT M p b i) : ¬ DepS M S false p := fun h =>
  gt_noreach hS hpl hp2 hpd hSd h (Or.inl ⟨rfl, Anc0.refl p, fun h => absurd hp2 h⟩)

/-- A seed whose subtree reaches `p` or beyond is not in a bump subtree. -/
theorem not_gb_of_right {i d : Nat} (hid : Anc0 M i d) (hpd : p ≤ d) : ¬ GB M p i := fun hG => by
  have := gb_lt hS hpl hp2 hG d hid; omega

end

/-! ## t = 2 -/

section
variable {M : Mat} {r L q d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hq : par M 0 (r + L) = some q)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hq hd0e hn

/-- **The row-1 parents before `x′` keep their `v`** (`t = 2`, `N = M[n]`, `n ≥ 2`). -/
theorem v_rowpar_N (he2r : entry M 2 r = 0) (h1x : entry M 1 r < entry M 1 (r + L))
    (hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i)
    (hxb : q ≠ r → col M (r + L) = bump M q) (hSM : SInv M) (hSN : SInv (TRIO.gexp M r L d0 d1 n))
    {ρ σ : Valn} {rkN : Bool → Nat → Nat}
    (hCM : Cons M ρ) (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN)
    {c p : Nat} (hc : c < r + L) (hp : par (TRIO.gexp M r L d0 d1 n) 1 c = some p) :
    σ.v p = ρ.v p := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hm1 : 1 ≤ n := by omega
  have hpc := par_lt N 1 c p hp
  have hpl : p < N.length := by omega
  have hcN : c < N.length := by omega
  have hp2 : entry N 2 p = 0 := by
    have := hSN.z2 p
    by_contra hne
    exact no_par1_of_e2 hSN.z1c hcN (by omega) hp
  have hanc := fun {a b : Nat} (hb : b ≤ r + L) => anc0_N_iff (d1 := d1) hlen hL hA hq hd0e hn (a := a) hb
  have hqx := par_lt M 0 _ _ hq
  have hqxN : Anc0 N q (r + L) := (hanc (le_refl _)).mpr (Anc0.step hq (Anc0.refl q))
  have hnd : ¬ DepS N (SN M r (r + L) q) false p := by
    apply not_depS_rowpar hSN hpl hp2 ⟨c, anc0_of_par N 1 p c hp, by omega⟩
    intro b i hs hG
    rcases hs with ⟨hb, hi⟩ | ⟨hb, hi, hqr⟩ | ⟨hb, hqr, hpi⟩ | ⟨hb, hix, hu⟩
    · subst hb; rw [hi] at hG
      rcases hG with ⟨hb, _⟩ | hB
      · cases hb
      · exact not_gb_of_right hSN hpl hp2 hqxN (by omega) hB
    · subst hb; rw [hi] at hG
      rcases hG with ⟨_, hqp, hcond⟩ | hB
      · -- `p` is below a bump child of `q`
        have hqp' : q ≠ p := by
          intro e
          have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
          have := hSM.bumpE2 q (r + L) hxq (hxb hqr)
          rw [← e, entry_gexp_pre hlen hm1 2 (by omega)] at hp2
          omega
        obtain ⟨b, hbq, hbp⟩ := anc0_child hqp hqp'
        have hbx : b < r + L := by have := hbp.le; omega
        have hbN : b ∈ children N q := mem_children_iff.mpr ⟨by omega, hbq⟩
        have hbM : b ∈ children M q := by rw [← children_N2g hlen hL hA hq hd0e hn hqx]; exact hbN
        have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
        have he2q := hSM.bumpE2 q (r + L) hxq (hxb hqr)
        have hall := all_bump_of_last hSM.r0p hSM.z2 hSM.sibDec hSM.z1c he2q
          (children_split_x (show r + L + 1 = M.length from hlen) hxq) (hxb hqr) b hbM
        have hbump : bump N q = bump M q := by
          unfold bump; rw [entry_gexp_pre hlen hm1 0 hqx, entry_gexp_pre hlen hm1 1 hqx]
        apply hcond (by rw [entry_gexp_pre hlen hm1 2 hqx]; omega) b hbN
          (by rw [col_gexp_pre hlen hm1 hbx, hbump]; exact hall) hbp
      · exact not_gb_of_right hSN hpl hp2 hqxN (by omega) hB
    · subst hb
      rcases hG with ⟨hb, _⟩ | hB
      · cases hb
      · have hiq := par_lt M 0 q i hpi
        have hiqN : Anc0 N i q := (hanc (by omega)).mpr (Anc0.step hpi (Anc0.refl i))
        exact not_gb_of_right hSN hpl hp2 (hiqN.trans hqxN) (by omega) hB
    · subst hb
      rcases hG with ⟨_, hip, _⟩ | hB
      · have := hip.le; omega
      · exact not_gb_of_right hSN hpl hp2 (Anc0.refl i) (by omega) hB
  exact (agree_N hlen hL hA hq hd0e hn he2r h1x hqb hSM.uat hSN.uat hCM hCN hRN p (by omega)).2 hnd

/-- **hpre of `noGapP_t2`**: the row-1 parents before `x′` have no gap (from `NoGapP M`). -/
theorem hpre_t2 (he2r : entry M 2 r = 0) (h1x : entry M 1 r < entry M 1 (r + L))
    (hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i)
    (hxb : q ≠ r → col M (r + L) = bump M q) (hSM : SInv M) (hSN : SInv (TRIO.gexp M r L d0 d1 n))
    {ρ σ : Valn} {rkN : Bool → Nat → Nat}
    (hCM : Cons M ρ) (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN)
    (hNM : NoGapP M ρ) :
    ∀ c p, c < r + L → par (TRIO.gexp M r L d0 d1 n) 1 c = some p → NoGap (σ.v p) := by
  intro c p hc hp
  rw [v_rowpar_N hlen hL hA hq hd0e hn he2r h1x hqb hxb hSM hSN hCM hCN hRN hc hp]
  exact hNM c p (by omega) (by rw [← par_gexp_pre hlen (show 1 ≤ n by omega) 1 hc]; exact hp)

end

end Ytosk
