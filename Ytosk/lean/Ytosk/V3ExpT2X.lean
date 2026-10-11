/-
**3 行・t = 2: 写しの根 x′ の v（T2CopyRes の残り: v_N(x) は標準形で V < v_N(x)）。**

- `depS_rk_ex`: 種に依存する呼び出しの順位は、ある種の順位以上。
- `depS_gate'`: 門の補題（V3ExpT2G）で、部分木の真の中の種は v でもよい形。
- `agree_N`: N = M[n]（n ≥ 2）の x より前で、N の依存の閉包で種 SN（o(q)、q ≠ r なら v(q)・o(P_0 q)、
  M で x − 1 が x へ上げるなら v(x − 1)）に依存しない呼び出しは M と同じ値（`cons_agree`）。
- x′ の P_1 は r、x′ の上げの先は q（q ≠ r のとき）か、ない（q = r）。v_N(r) = v_M(r)。
-/
import Ytosk.V3ExpT2B

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **The rank of a dependent call is at least that of some seed.** -/
theorem depS_rk_ex {M : Mat} {S : Bool → Nat → Prop} {rk : Bool → Nat → Nat} (hR : Rk M rk) :
    ∀ {b i}, DepS M S b i → i < M.length → ∃ b' i', S b' i' ∧ rk b' i' ≤ rk b i := by
  intro b i h
  induction h with
  | @seed b i hs => intro _; exact ⟨b, i, hs, le_refl _⟩
  | ochild hc hcb hcu _ ih =>
    intro hi
    have := (hR _ hi).2.1 _ hc hcb hcu
    obtain ⟨b', i', hs, hle⟩ := ih (mem_children hc).2
    exact ⟨b', i', hs, by omega⟩
  | ov _ ih =>
    intro hi
    have := (hR _ hi).1
    obtain ⟨b', i', hs, hle⟩ := ih hi
    exact ⟨b', i', hs, by omega⟩
  | vpar h1 hm _ ih =>
    intro hi
    have := ((hR _ hi).2.2 h1).1 _ hm
    obtain ⟨b', i', hs, hle⟩ := ih (by have := par_lt _ 1 _ _ hm; omega)
    exact ⟨b', i', hs, by omega⟩
  | vupg h1 h2 hk _ ih =>
    intro hi
    have := ((hR _ hi).2.2 h1).2.1 h2 _ hk
    obtain ⟨b', i', hs, hle⟩ := ih (upg_lt hi hk)
    exact ⟨b', i', hs, by omega⟩
  | vbump h1 h2 hj hjb hk _ ih =>
    intro hi
    have := ((hR _ hi).2.2 h1).2.2 h2 _ hj hjb _ hk
    obtain ⟨b', i', hs, hle⟩ := ih (mem_children hk).2
    exact ⟨b', i', hs, by omega⟩

/-- **The gate** (`depS_gate`) with seeds strictly inside the subtree allowed to be `v` calls. -/
theorem depS_gate' {M : Mat} {S : Bool → Nat → Prop} {s : Nat} (hs2 : entry M 2 s = 0)
    (hsu : upg M s ≠ some (s + 1)) (hS : ∀ b i, S b i → (b = true ∧ i = s) ∨ SubT M s i) :
    ∀ {b i}, DepS M S b i → ¬ SubT M s i → DepS M (SR s) b i := by
  intro b i h
  induction h with
  | @seed b i hs =>
    intro hni
    rcases hS b i hs with ⟨hb, h⟩ | h
    · subst hb; exact DepS.seed ⟨rfl, h⟩
    · exact absurd h hni
  | @ochild i c hc hcb hcu _ ih =>
    intro hni
    by_cases hsc : SubT M s c
    · have hpc := (mem_children_iff.mp hc).2
      have hsi : Anc0 M s i := anc0_par hsc.1 hsc.2.symm hpc
      by_cases his : i = s
      · exact DepS.seed ⟨rfl, his⟩
      · exact absurd ⟨hsi, his⟩ hni
    · exact DepS.ochild hc hcb hcu (ih hsc)
  | ov _ ih =>
    intro hni; exact DepS.ov (ih hni)
  | @vpar i m h1 hm _ ih =>
    intro hni
    have hmi := anc0_of_par M 1 _ _ hm
    have hsm : ¬ SubT M s m := by
      rintro ⟨ha, hne⟩
      apply hni
      refine ⟨Anc0.trans ha hmi, fun his => ?_⟩
      have := ha.le; have := par_lt M 1 _ _ hm; omega
    exact DepS.vpar h1 hm (ih hsm)
  | @vupg i k h1 h2 hk _ ih =>
    intro hni
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hk
    rcases hcase with hk1 | ⟨hA, hlt⟩
    · by_cases hsk : SubT M s k
      · exfalso
        have hsi1 : Anc0 M s (i + 1) := by rw [← hk1]; exact hsk.1
        have hsle := hsi1.le
        have hne : i + 1 ≠ s := by rw [← hk1]; exact hsk.2
        have hsi : Anc0 M s i := anc_between hsi1 i (by omega) (by omega)
        by_cases his : i = s
        · subst his; exact hsu (by rw [hk, hk1])
        · exact hni ⟨hsi, his⟩
      · exact DepS.vupg h1 h2 hk (ih hsk)
    · have hsk : ¬ SubT M s k := by
        rintro ⟨ha, hne⟩
        apply hni
        refine ⟨Anc0.trans ha hA, fun his => ?_⟩
        have := ha.le; omega
      exact DepS.vupg h1 h2 hk (ih hsk)
  | @vbump i j k h1 h2 hj hjb hk _ ih =>
    intro hni
    by_cases hsk : SubT M s k
    · exfalso
      have hpk := (mem_children_iff.mp hk).2
      have hsj : Anc0 M s j := anc0_par hsk.1 hsk.2.symm hpk
      by_cases hjs : j = s
      · subst hjs
        have := (bump_eq hjb).2.2
        have h2' : (col M j).2.2 = entry M 2 j := rfl
        rw [h2', hs2] at this; omega
      · have hpj := (mem_children_iff.mp hj).2
        have hsi : Anc0 M s i := anc0_par hsj (Ne.symm hjs) hpj
        by_cases his : i = s
        · subst his; exact h2 hs2
        · exact hni ⟨hsi, his⟩
    · exact DepS.vbump h1 h2 hj hjb hk (ih hsk)

/-- **`v` of a sealed column depends on no seed strictly inside its subtree** (nor on its own `o`). -/
theorem not_depS_sealed' {M : Mat} {S : Bool → Nat → Prop} {s : Nat} {rk : Bool → Nat → Nat}
    (hR : Rk M rk) (hs : s < M.length) (hs2 : entry M 2 s = 0) (hsu : upg M s ≠ some (s + 1))
    (hS : ∀ b i, S b i → (b = true ∧ i = s) ∨ SubT M s i) : ¬ DepS M S false s := fun h =>
  not_depS_v_self hR hs (depS_gate' hs2 hsu hS h (fun h' => h'.2 rfl))

/-- The seeds of `N = M[n]` before `x` (`t = 2`): `o(q)`; for `q ≠ r` also `v(q)` (the bump child `x` is lost)
and `o(P_0 q)` (`q` is no longer topped); `v(x − 1)` if it upgrades to `x` in `M`. -/
def SN (M : Mat) (r x q : Nat) : Bool → Nat → Prop := fun b i =>
  (b = true ∧ i = q) ∨ (b = false ∧ i = q ∧ q ≠ r) ∨ (b = true ∧ q ≠ r ∧ par M 0 q = some i) ∨
    (b = false ∧ i + 1 = x ∧ upg M i = some x)

section
variable {M : Mat} {r L q d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hq : par M 0 (r + L) = some q)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hq hd0e hn

/-- **Upgrades before `x`** are those of `M`, unless `M` upgrades `x − 1` to `x`. -/
theorem upgN_eq (he2r : entry M 2 r = 0) {i : Nat} (hi : i < r + L)
    (hnx : ¬ (i + 1 = r + L ∧ upg M i = some (r + L))) :
    upg (TRIO.gexp M r L d0 d1 n) i = upg M i := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hm1 : 1 ≤ n := by omega
  rcases Nat.lt_or_ge (i + 1) (r + L) with hi1 | hi1
  · rw [← upg_take _ hi1, hN, gexp_take_x hlen hm1, upg_take M hi1]
  · have hix : i + 1 = r + L := by omega
    obtain ⟨hx2', hx0'⟩ := entry_xprime_g (d1 := d1) hlen hL hA hq hd0e hn
    have hpre : ∀ y j, j < r + L → entry N y j = entry M y j := fun y j hj => entry_gexp_pre hlen hm1 y hj
    have hparpre : ∀ k j, j < r + L → par N k j = par M k j := fun k j hj => par_gexp_pre hlen hm1 k hj
    have hcolpre : ∀ j, j < r + L → col N j = col M j := fun j hj => col_gexp_pre hlen hm1 hj
    have hlenN : ¬ i + 1 = N.length := by omega
    have hlenM : ¬ i + 1 = M.length := by omega
    unfold upg
    rw [hpre 1 i (by omega), hpre 2 i (by omega), hparpre 1 i (by omega)]
    by_cases hc : entry M 1 i = 0 ∨ entry M 2 i = 1
    · rw [if_pos (by rcases hc with h' | h'; exact Or.inl h'; exact Or.inr (Or.inl h')),
        if_pos (by rcases hc with h' | h'; exact Or.inl h'; exact Or.inr (Or.inl h'))]
    · rw [if_neg (by rintro (h' | h' | h'); exact hc (Or.inl h'); exact hc (Or.inr h'); exact hlenN h'),
        if_neg (by rintro (h' | h' | h'); exact hc (Or.inl h'); exact hc (Or.inr h'); exact hlenM h')]
      cases hm : par M 1 i with
      | none => rfl
      | some m =>
        simp only
        have hmi := par_lt M 1 i m hm
        have hN1 : ¬ (par N 1 (i + 1) = some m ∧ col N (i + 1) =
            (entry N 0 m + 1, entry M 1 i, entry N 2 m + 1)) := by
          rintro ⟨_, hc'⟩
          have : entry N 2 (i + 1) = (col N (i + 1)).2.2 := rfl
          rw [hc'] at this; simp at this; rw [hix, hx2', he2r] at this; omega
        rw [if_neg hN1, hpre 0 m (by omega), hpre 2 m (by omega)]
        have hcl : climb (par N 0)
            (fun q => decide (par N 1 q = some m ∧
              col N q = (entry M 0 m + 1, entry M 1 i, entry M 2 m + 1) ∧ entry N 0 q < entry N 0 (i + 1)))
            (i + 1) (par N 0 i) =
          climb (par M 0)
            (fun q => decide (par M 1 q = some m ∧
              col M q = (entry M 0 m + 1, entry M 1 i, entry M 2 m + 1) ∧ entry M 0 q < entry M 0 (i + 1)))
            (i + 1) (par M 0 i) := by
          rw [hparpre 0 i (by omega)]
          apply climb_congr (i + 1)
          · intro q' hq'; exact hparpre 0 q' (by omega)
          · intro q' hq'
            rw [hparpre 1 q' (by omega), hcolpre q' (by omega), hpre 0 q' (by omega), hix, hx0']
          · exact par_lt N 0
          · intro q' h'; have := par_lt M 0 _ q' h'; omega
        rw [hcl]
        have hM1 : ¬ (par M 1 (i + 1) = some m ∧ col M (i + 1) =
            (entry M 0 m + 1, entry M 1 i, entry M 2 m + 1)) := by
          intro h'
          apply hnx
          refine ⟨hix, ?_⟩
          unfold upg
          have hc3 : ¬ (entry M 1 i = 0 ∨ entry M 2 i = 1 ∨ i + 1 = M.length) := by
            rintro (h'' | h'' | h'')
            · exact hc (Or.inl h'')
            · exact hc (Or.inr h'')
            · exact hlenM h''
          rw [if_neg hc3, hm]
          simp only
          rw [if_pos h', hix]
        rw [if_neg hM1]

/-- **Agreement of `N = M[n]` with `M` before `x`, off the closure in `N` of the seeds `SN`.** -/
theorem agree_N (he2r : entry M 2 r = 0) (h1x : entry M 1 r < entry M 1 (r + L))
    (hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i)
    (hUM : UAT M) (hUN : UAT (TRIO.gexp M r L d0 d1 n)) {ρ σ : Valn} {rkN : Bool → Nat → Nat}
    (hCM : Cons M ρ) (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN) :
    ∀ i, i < r + L →
      (¬ DepS (TRIO.gexp M r L d0 d1 n) (SN M r (r + L) q) true i → σ.o i = ρ.o i) ∧
      (¬ DepS (TRIO.gexp M r L d0 d1 n) (SN M r (r + L) q) false i → σ.v i = ρ.v i) := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  set S := SN M r (r + L) q with hS
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hm1 : 1 ≤ n := by omega
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hent : ∀ y j, j < r + L → entry N y j = entry M y j := fun y j hj => entry_gexp_pre hlen hm1 y hj
  have hcol : ∀ j, j < r + L → col N j = col M j := fun j hj => col_gexp_pre hlen hm1 hj
  have hbump : ∀ j, j < r + L → bump N j = bump M j := fun j hj => by
    unfold bump; rw [hent 0 j hj, hent 1 j hj]
  have hpar : ∀ k j, j < r + L → par N k j = par M k j := fun k j hj => par_gexp_pre hlen hm1 k hj
  have hch : ∀ j, j < r + L → children N j = children M j := fun j hj =>
    children_N2g hlen hL hA hq hd0e hn hj
  obtain ⟨hx2', _⟩ := entry_xprime_g (d1 := d1) hlen hL hA hq hd0e hn
  have hx2 : entry N 2 (r + L) = 0 := by rw [hx2', he2r]
  have hxnb : ∀ i, col N (r + L) ≠ bump N i := fun i h => by
    have := (bump_eq h).2.2
    have h2' : (col N (r + L)).2.2 = entry N 2 (r + L) := rfl
    rw [h2', hx2] at this; omega
  -- a child of a column before `x` is before `x`, or is `x` under `q`
  have hchx : ∀ i c, i < r + L → c ∈ children M i → c < r + L ∨ (c = r + L ∧ i = q) := by
    intro i c hi hc
    have hcl := (mem_children hc).2
    rcases Nat.lt_or_ge c (r + L) with h | h
    · exact Or.inl h
    · right
      have hcx : c = r + L := by omega
      refine ⟨hcx, ?_⟩
      have h' := (mem_children_iff.mp hc).2
      rw [hcx, hq] at h'; exact (Option.some.inj h').symm
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen hm1
  -- `r` is not an upgrade target
  have hrU : ∀ (H : Mat), entry H 2 r = 0 → isUpg H r = false := by
    intro H h2
    cases h : isUpg H r with
    | false => rfl
    | true =>
      exfalso
      unfold isUpg at h
      obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
      have := upg_target_e2 (of_decide_eq_true hk); omega
  -- counting before `x`
  have hcntEq : ∀ i c, i < r + L → c ∈ children M i → c < r + L → ¬ (q ≠ r ∧ c = q) →
      (Counted N i c ↔ Counted M i c) := by
    intro i c hi hc hcx hcq
    unfold Counted
    rw [hcol c hcx, hbump i hi]
    by_cases hcq' : c = q
    · have hqr : q = r := by by_contra h'; exact hcq ⟨h', hcq'⟩
      subst hcq'; subst hqr
      rw [hrU N (by rw [hent 2 c hcx]; exact he2r), hrU M he2r]; simp
    · have htop : topped N c = topped M c := topped_N2g hlen hL hA hq hd0e hn hcx hcq'
      rw [htop]
      by_cases ht : topped M c = true
      · rw [isUpg_topped_take (by omega) (by omega) hT hUM hUN hcx (by rw [htop]; exact ht) ht]
      · simp [ht]
  have hcnt : ∀ i c, i < r + L → ¬ S true i → c ∈ children M i → cnt N ρ i c = cnt M ρ i c := by
    intro i c hi hSi hc
    rcases hchx i c hi hc with hcx | ⟨_, hiq⟩
    · have hcq : ¬ (q ≠ r ∧ c = q) := by
        rintro ⟨hqr, rfl⟩
        exact hSi (Or.inr (Or.inr (Or.inl ⟨rfl, hqr, (mem_children_iff.mp hc).2⟩)))
      rw [cnt_eq_ite, cnt_eq_ite]
      by_cases h : Counted M i c
      · rw [if_pos h, if_pos ((hcntEq i c hi hc hcx hcq).mpr h)]
      · rw [if_neg h, if_neg (fun h' => h ((hcntEq i c hi hc hcx hcq).mp h'))]
    · exact absurd (Or.inl ⟨rfl, hiq⟩) hSi
  have hbt : ∀ i j, i < r + L → ¬ S false i → j ∈ children M i → bumpTerm N ρ i j = bumpTerm M ρ i j := by
    intro i j hi hSi hj
    rcases hchx i j hi hj with hjx | ⟨hjx, hiq⟩
    · unfold bumpTerm
      rw [hcol j hjx, hbump i hi, hch j hjx]
    · subst hjx
      have hqr : q = r := by
        by_contra h'; exact hSi (Or.inr (Or.inl ⟨rfl, hiq, h'⟩))
      unfold bumpTerm
      rw [if_neg (hxnb i), if_neg]
      intro hb
      have := (bump_eq hb).2.1
      have h1' : (col M (r + L)).2.1 = entry M 1 (r + L) := rfl
      rw [h1', hiq, hqr] at this; omega
  have hoEq : ∀ i, i < r + L → ¬ S true i → oRhs N ρ i = oRhs M ρ i := by
    intro i hi hSi
    unfold oRhs
    rw [hch i hi, List.map_congr_left (fun c hc => hcnt i c hi hSi hc)]
  have hvEq : ∀ i, i < r + L → ¬ S false i → vRhs N ρ i = vRhs M ρ i := by
    intro i hi hSi
    have hu : upg N i = upg M i :=
      upgN_eq hlen hL hA hq hd0e hn he2r hi (fun h => hSi (Or.inr (Or.inr (Or.inr ⟨rfl, h.1, h.2⟩))))
    unfold vRhs
    rw [hent 1 i hi, hent 2 i hi, hpar 1 i hi, hu, hch i hi,
      List.map_congr_left (fun j hj => hbt i j hi hSi hj)]
  set E : Bool → Nat → Prop := fun b i => r + L ≤ i ∨ DepS N S b i with hE
  have hag := cons_agree E hCN hRN
    (fun i _ hi => by
      have hix : i < r + L := by by_contra h; exact hi (Or.inl (by omega))
      rw [hoEq i hix (fun h => hi (Or.inr (DepS.seed h)))]; exact (hCM i (by omega)).1)
    (fun i _ hi => by
      have hix : i < r + L := by by_contra h; exact hi (Or.inl (by omega))
      rw [hvEq i hix (fun h => hi (Or.inr (DepS.seed h)))]; exact (hCM i (by omega)).2)
    (by
      intro i _ hi
      have hix : i < r + L := by by_contra h; exact hi (Or.inl (by omega))
      have hD : ¬ DepS N S true i := fun h => hi (Or.inr h)
      refine ⟨?_, fun c hc hcnt' => ?_⟩
      · rintro (h | h)
        · omega
        · exact hD (DepS.ov h)
      · have hcM : c ∈ children M i := by rw [← hch i hix]; exact hc
        rintro (h | h)
        · rcases hchx i c hix hcM with hcx | ⟨_, hiq⟩
          · omega
          · exact hD (DepS.seed (Or.inl ⟨rfl, hiq⟩))
        · exact hD (DepS.ochild hc hcnt'.1 hcnt'.2 h))
    (by
      intro i _ hi h1
      have hix : i < r + L := by by_contra h; exact hi (Or.inl (by omega))
      have hD : ¬ DepS N S false i := fun h => hi (Or.inr h)
      refine ⟨fun m hm => ?_, fun h2 k hk => ?_, fun h2 j hj hb k hk => ?_⟩
      · have := par_lt N 1 i m hm
        rintro (h | h)
        · omega
        · exact hD (DepS.vpar h1 hm h)
      · have hkl := upg_le hk
        rintro (h | h)
        · have hkx : k = r + L := by omega
          subst hkx
          have := upg_target_e2 hk; omega
        · exact hD (DepS.vupg h1 h2 hk h)
      · have hjM : j ∈ children M i := by rw [← hch i hix]; exact hj
        have hjx : j < r + L := by
          rcases hchx i j hix hjM with h | ⟨h, _⟩
          · exact h
          · subst h; exact absurd hb (hxnb i)
        have hkM : k ∈ children M j := by rw [← hch j hjx]; exact hk
        rintro (h | h)
        · rcases hchx j k hjx hkM with hkx | ⟨_, hjq⟩
          · omega
          · subst hjq
            rw [hcol _ hjx, hbump i hix] at hb
            exact hqb i (mem_children_iff.mp hjM).2 hb
        · exact hD (DepS.vbump h1 h2 hj hb hk h))
  intro i hix
  obtain ⟨ho, hv⟩ := hag i (by omega)
  refine ⟨fun hD => ho ?_, fun hD => hv ?_⟩
  · rintro (h | h)
    · omega
    · exact hD h
  · rintro (h | h)
    · omega
    · exact hD h

/-- **The row-1 entry of the copy root** is that of `x`. -/
theorem entry1_xN (hd1e : entry M 1 (r + L) = entry M 1 r + d1) :
    entry (TRIO.gexp M r L d0 d1 n) 1 (r + L) = entry M 1 (r + L) := by
  have h := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := n)
    (k := 1) (q := 0) hlen (by omega) hL
  rw [show r + (1 * L + 0) = r + L by omega, Nat.add_zero] at h
  have h1 : entry (TRIO.gexp M r L d0 d1 n) 1 (r + L) =
      entry M 1 r + (if TRIO.le1 M r r then 1 * d1 else 0) := by unfold entry; rw [h]; rfl
  rw [h1, if_pos ⟨by omega, by omega, Relation.ReflTransGen.refl⟩, hd1e]; omega

/-- The row-0 parent of the copy root is `q`. -/
theorem par0_xN : par (TRIO.gexp M r L d0 d1 n) 0 (r + L) = some q := by
  rcases par0_tail2g (d1 := d1) hlen hL hA hq hd0e hn (le_refl _)
    (by have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn; omega) with ⟨_, h⟩ | ⟨p, _, h1, h2⟩
  · exact h
  · omega

/-- **`P_1` of the copy root** is that of `x` in `M`. -/
theorem par1_xN (hd1e : entry M 1 (r + L) = entry M 1 r + d1) :
    par (TRIO.gexp M r L d0 d1 n) 1 (r + L) = par M 1 (r + L) := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hm1 : 1 ≤ n := by omega
  have e1 : par N 1 (r + L) = climb (par N 0) (fun j => decide (entry N 1 j < entry N 1 (r + L)))
      (r + L + 1) (par N 0 (r + L)) := rfl
  have e2 : par M 1 (r + L) = climb (par M 0) (fun j => decide (entry M 1 j < entry M 1 (r + L)))
      (r + L + 1) (par M 0 (r + L)) := rfl
  rw [e1, e2, par0_xN hlen hL hA hq hd0e hn, hq, entry1_xN hlen hL hA hq hd0e hn hd1e]
  apply climb_congr (r + L) (fun j hj => par_gexp_pre hlen hm1 0 hj)
    (fun j hj => by rw [entry_gexp_pre hlen hm1 1 hj]) (par_lt N 0)
  intro j h; cases h; exact par_lt M 0 _ _ hq

/-- Ancestry up to `x` is the same in `N` and `M`. -/
theorem anc0_N_iff {a b : Nat} (hb : b ≤ r + L) :
    Anc0 (TRIO.gexp M r L d0 d1 n) a b ↔ Anc0 M a b := by
  have hm1 : 1 ≤ n := by omega
  apply anc0_congr_le (B := r + L) _ hb
  intro j hj
  rcases Nat.lt_or_ge j (r + L) with h | h
  · exact par_gexp_pre hlen hm1 0 h
  · rw [show j = r + L by omega, par0_xN hlen hL hA hq hd0e hn, hq]

/-- **The upgrade target of the copy root** is `q` (and then `q ≠ r`): it is a child of `r = P_1(x′)` on
the path to `x`, and a child of `r` other than `q` would make `q` the bump child of its parent (`RowJ`). -/
theorem upg_xN (hd1e : entry M 1 (r + L) = entry M 1 r + d1) (hr1 : par M 1 (r + L) = some r)
    (hxb : q ≠ r → col M (r + L) = bump M q) (hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i)
    (hJ : RowJ M) (hR0 : R0P M) (hBE : BumpE2 M) {k : Nat}
    (hk : upg (TRIO.gexp M r L d0 d1 n) (r + L) = some k) : k = q ∧ q ≠ r := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hm1 : 1 ≤ n := by omega
  obtain ⟨m, hm, hkm, _, hcase⟩ := upg_facts hk
  rw [par1_xN hlen hL hA hq hd0e hn hd1e, hr1] at hm
  cases hm
  have hkl : k < N.length := upg_lt (by omega) hk
  rcases hcase with hk1 | ⟨hAk, hkx⟩
  · rw [hk1] at hkm hkl
    rw [hlN] at hkl
    rcases par0_tail2g (d1 := d1) hlen hL hA hq hd0e hn (show r + L ≤ r + L + 1 by omega)
      hkl with ⟨h, _⟩ | ⟨p, hp, hp1, _⟩
    · omega
    · rw [hkm] at hp; cases hp; omega
  · have hkM : par M 0 k = some r := by rw [← par_gexp_pre hlen hm1 0 hkx]; exact hkm
    have hAkM : Anc0 M k (r + L) := (anc0_N_iff hlen hL hA hq hd0e hn (le_refl _)).mp hAk
    have hkq : Anc0 M k q := anc0_par hAkM (by omega) hq
    have hrk : r < k := par_lt M 0 k r hkM
    have hqr : q ≠ r := by intro h; have := hkq.le; omega
    refine ⟨?_, hqr⟩
    by_contra hkq'
    obtain ⟨pq, hpq⟩ := par0_of_anc hkq hkq'
    have hkpq : Anc0 M k pq := anc0_par hkq hkq' hpq
    have hxb' := hxb hqr
    have he1q : entry M 1 (r + L) = entry M 1 q :=
      e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from hxb')
    have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
    have he2q : entry M 2 q = 1 := hBE q (r + L) hxq hxb'
    have hJq := hJ q pq (by omega) hpq
    obtain ⟨_, _, _, hbet⟩ := par1_facts hr1
    have hrpq : Anc0 M r pq := Anc0.trans (Anc0.step hkM (Anc0.refl r)) hkpq
    have hpqx : Anc0 M pq (r + L) := Anc0.step hq (Anc0.step hpq (Anc0.refl pq))
    have hpqlt := par_lt M 0 q pq hpq
    have hqlt := par_lt M 0 _ q hq
    have h1 := hbet pq hrpq hpqx (by have := hkpq.le; omega) (by omega)
    have h0 := hR0 q pq hpq
    apply hqb pq hpq
    rw [col_eq_entries, h0, he2q, show entry M 1 q = entry M 1 pq by omega]
    rfl

end

/-- **`P_1(x) = r`** (`t = 2`): a row-1 parent strictly after `r` would have row 2 equal to `1`, and its
child towards `x` would have row 1 at most its own (`Z1C`), below `e1(x)`. -/
theorem par1_x_r {M : Mat} {r x : Nat} (hxl : x < M.length) (hZ2 : Z2 M) (hZ1 : Z1C M)
    (hr2 : par M 2 x = some r) : par M 1 x = some r := by
  obtain ⟨_, _, hrx, he2lt, hle1, hmin⟩ := (par2_iff M hxl).mp hr2
  obtain ⟨w, hw, hrw⟩ := le1_par1_down hle1 (by omega)
  by_cases hwr : w = r
  · rw [hw, hwr]
  · exfalso
    have hrw' : r < w := lt_of_le_of_ne (le1_ge hrw) (Ne.symm hwr)
    have hwx : TRIO.le1 M w x := le1_par1_up ⟨hrw.2.1, hrw.2.1, Relation.ReflTransGen.refl⟩ hw hxl
    have he2w : entry M 2 x ≤ entry M 2 w := hmin w ⟨hrw', hwx⟩
    have he2lt' : entry M 2 r < entry M 2 x := he2lt
    have he2x := hZ2 x
    have he2w1 : entry M 2 w = 1 := by have := hZ2 w; omega
    obtain ⟨hAwx, hwlt, he1w, hbet⟩ := par1_facts hw
    obtain ⟨c, hcw, hcx⟩ := anc0_child hAwx (by omega)
    have hcM : c ∈ children M w := mem_children_iff.mpr ⟨by have := hcx.le; omega, hcw⟩
    have h1c := hZ1 w c he2w1 hcM
    by_cases hcxe : c = x
    · subst hcxe; omega
    · have := hbet c (Anc0.step hcw (Anc0.refl w)) hcx (by have := par_lt M 0 c w hcw; omega) hcxe
      omega

section
variable {M : Mat} {r L q d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hq : par M 0 (r + L) = some q)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hd1e : entry M 1 (r + L) = entry M 1 r + d1) (he2r : entry M 2 r = 0)
  (h1x : entry M 1 r < entry M 1 (r + L)) (hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i)
  (hr1 : par M 1 (r + L) = some r)
include hlen hL hA hq hd0e hn hd1e he2r h1x hqb hr1

/-- **`v(r)` of `N` is that of `M`** (`r` is sealed, every seed of `N` lies in its subtree). -/
theorem vr_N (hUM : UAT M) (hUN : UAT (TRIO.gexp M r L d0 d1 n)) {ρ σ : Valn} {rkN : Bool → Nat → Nat}
    (hCM : Cons M ρ) (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN) :
    σ.v r = ρ.v r := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hm1 : 1 ≤ n := by omega
  have hanc := fun {a b : Nat} (hb : b ≤ r + L) => anc0_N_iff (d1 := d1) hlen hL hA hq hd0e hn (a := a) hb
  have hr1M : Anc0 M r (r + 1) := anc_between hA (r + 1) (by omega) (by omega)
  have hrq : Anc0 M r q := anc0_par hA (by omega) hq
  have hqx := par_lt M 0 _ _ hq
  have hnd : ¬ DepS N (SN M r (r + L) q) false r := by
    apply not_depS_sealed' hRN (by omega) (by rw [entry_gexp_pre hlen hm1 2 (by omega)]; exact he2r)
    · intro h
      have := upg_lt_of_child ((hanc (by omega)).mpr hr1M) h; omega
    · intro b i hs
      rcases hs with ⟨hb, hi⟩ | ⟨hb, hi, hqr⟩ | ⟨hb, hqr, hpi⟩ | ⟨hb, hix, hu⟩
      · by_cases hqr : q = r
        · exact Or.inl ⟨hb, hi.trans hqr⟩
        · subst hi; exact Or.inr ⟨(hanc (by omega)).mpr hrq, hqr⟩
      · subst hi; exact Or.inr ⟨(hanc (by omega)).mpr hrq, hqr⟩
      · have hri : Anc0 M r i := anc0_par hrq (Ne.symm hqr) hpi
        have hiq := par_lt M 0 q i hpi
        by_cases hir : i = r
        · exact Or.inl ⟨hb, hir⟩
        · exact Or.inr ⟨(hanc (by omega)).mpr hri, hir⟩
      · have hir : i ≠ r := by
          intro h; rw [h] at hu
          have := upg_lt_of_child hr1M hu; omega
        exact Or.inr ⟨(hanc (by omega)).mpr (anc_between hA i (by omega) (by omega)), hir⟩
  exact (agree_N hlen hL hA hq hd0e hn he2r h1x hqb hUM hUN hCM hCN hRN r (by omega)).2 hnd

/-- `P_1(q) = r` (`q ≠ r`, `x` the bump child of `q`). -/
theorem par1_q (hqr : q ≠ r) (hxb : col M (r + L) = bump M q) : par M 1 q = some r := by
  have hrq : Anc0 M r q := anc0_par hA (by omega) hq
  have hqx := par_lt M 0 _ _ hq
  have he1q : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from hxb)
  obtain ⟨_, _, _, hbet⟩ := par1_facts hr1
  rw [par1_some_iff]
  refine ⟨mem_ancL_of_anc hrq (Ne.symm hqr), by omega, fun y hy hry => ?_⟩
  have hyq : Anc0 M y q := anc0_of_mem_ancL hy
  have hylt := mem_ancL_lt hy
  have hry' : Anc0 M r y := by
    rcases anc0_total hrq hyq with h | h
    · exact h
    · have := h.le; omega
  have := hbet y hry' (Anc0.trans hyq (Anc0.step hq (Anc0.refl q))) (by omega) (by omega)
  omega

/-- **`v(q)` of `N` is standard and nonzero** (`q ≠ r`): the bump terms of `q` other than the lost `x`
read values that the seeds of `N` do not reach (ranking). -/
theorem vq_N (hqr : q ≠ r) (hxb : col M (r + L) = bump M q) (hBE : BumpE2 M) (hUM : UAT M)
    (hUN : UAT (TRIO.gexp M r L d0 d1 n)) {ρ σ : Valn} {rkN : Bool → Nat → Nat}
    (hCM : Cons M ρ) (hGM : Good3 M ρ) (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ)
    (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN) :
    isOT (σ.v q) = true ∧ σ.v q ≠ z := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hm1 : 1 ≤ n := by omega
  have hqx := par_lt M 0 _ _ hq
  have hqN : q < N.length := by omega
  have hrq : Anc0 M r q := anc0_par hA (by omega) hq
  have he1q : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from hxb)
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he2q : entry M 2 q = 1 := hBE q (r + L) hxq hxb
  have he1N : entry N 1 q ≠ 0 := by rw [entry_gexp_pre hlen hm1 1 hqx]; omega
  have he2N : entry N 2 q ≠ 0 := by rw [entry_gexp_pre hlen hm1 2 hqx]; omega
  have hch : ∀ j, j < r + L → children N j = children M j := fun j hj =>
    children_N2g hlen hL hA hq hd0e hn hj
  obtain ⟨hx2', _⟩ := entry_xprime_g (d1 := d1) hlen hL hA hq hd0e hn
  have hxnb : ∀ i, col N (r + L) ≠ bump N i := fun i h => by
    have := (bump_eq h).2.2
    have h2' : (col N (r + L)).2.2 = entry N 2 (r + L) := rfl
    rw [h2', hx2', he2r] at this; omega
  have hvr := vr_N hlen hL hA hq hd0e hn hd1e he2r h1x hqb hr1 hUM hUN hCM hCN hRN
  have hag := agree_N hlen hL hA hq hd0e hn he2r h1x hqb hUM hUN hCM hCN hRN
  -- `q` is counted at its parent in `N` (its last child `x′` is not a bump child)
  have hlastq : (children N q).getLast? = some (r + L) := by
    rw [hch q hqx, split_last_max _ _ (children_sorted M q) hxq
      (fun d hd => by have := (mem_children hd).2; omega)]
    simp
  have htopq : topped N q = false := by
    unfold topped; rw [hlastq]; simp only [decide_eq_false_iff_not]; exact hxnb q
  -- the values read by the bump terms of `q` in `N`
  have hok : ∀ j ∈ children N q, col N j = bump N q → ∀ k ∈ children N j, isOT (σ.o k) = true := by
    intro j hj hjb k hk
    have hjM : j ∈ children M q := by rw [← hch q hqx]; exact hj
    have hjx : j < r + L := by
      have := (mem_children hjM).2
      rcases Nat.lt_or_ge j (r + L) with h | h
      · exact h
      · exfalso; rw [show j = r + L by omega] at hjb; exact hxnb q hjb
    have hkM : k ∈ children M j := by rw [← hch j hjx]; exact hk
    have hkx : k < r + L := by
      have := (mem_children hkM).2
      rcases Nat.lt_or_ge k (r + L) with h | h
      · exact h
      · exfalso
        have hkx' : k = r + L := by omega
        have h' := (mem_children_iff.mp hkM).2; rw [hkx', hq] at h'
        have := (mem_children hjM).1; cases h'; omega
    have hnd : ¬ DepS N (SN M r (r + L) q) true k := by
      intro hD
      obtain ⟨b', i', hs, hle⟩ := depS_rk_ex hRN hD (by omega)
      have hrk : rkN true k < rkN false q := ((hRN q hqN).2.2 he1N).2.2 he2N j hj hjb k hk
      have hvo := (hRN q hqN).1
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, _, hpi⟩ | ⟨rfl, hix, hu⟩
      · omega
      · omega
      · have hiq := par_lt M 0 q i' hpi
        have hqch : q ∈ children N i' := mem_children_iff.mpr ⟨hqN, by
          rw [par_gexp_pre hlen hm1 0 hqx]; exact hpi⟩
        have hnb : col N q ≠ bump N i' := by
          rw [col_gexp_pre hlen hm1 hqx]
          unfold bump; rw [entry_gexp_pre hlen hm1 0 (by omega), entry_gexp_pre hlen hm1 1 (by omega)]
          exact hqb i' hpi
        have := (hRN i' (by omega)).2.1 q hqch hnb (by rw [htopq]; simp)
        omega
      · exfalso
        obtain ⟨m', _, hm2, hcol, _⟩ := upg_spec hu
        rw [hr1] at hm2; cases hm2
        have h0 : entry M 0 (r + L) = entry M 0 r + 1 := by
          have : entry M 0 (r + L) = (col M (r + L)).1 := rfl; rw [this, hcol]
        have h0' : entry M 0 (r + L) = entry M 0 q + 1 := by
          have : entry M 0 (r + L) = (col M (r + L)).1 := rfl; rw [this, hxb]; rfl
        have := anc0_e0_lt hrq (Ne.symm hqr)
        omega
    rw [(hag k hkx).1 hnd]
    exact hGM.ot_o k (by omega)
  have hbt : ∀ t ∈ one :: (children N q).map (bumpTerm N σ q), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      unfold bumpTerm
      split
      · rename_i hjb
        apply isOT_omega; apply isOT_sumN
        intro u hu
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hu
        exact hok j hj hjb k hk
      · rfl
  have hpq1 : par N 1 q = some r := by rw [par_gexp_pre hlen hm1 1 hqx]; exact par1_q hlen hL hA hq hd0e hn hd1e he2r h1x hqb hr1 hqr hxb
  have hot : isOT (add (vOpt σ (par N 1 q)) (omega (sumN (one :: (children N q).map (bumpTerm N σ q))))) = true := by
    rw [hpq1]
    exact isOT_add (by show isOT (σ.v r) = true; rw [hvr]; exact hGM.ot_v r (by omega))
      (isOT_omega (isOT_sumN _ hbt))
  have hv := (hCN q hqN).2
  unfold vRhs at hv
  rw [if_neg he1N, if_neg he2N, sf_ot hot] at hv
  exact ⟨by rw [hv]; exact hot, v_ne_z_of_e1 hCN hqN he1N⟩

/-- **`v` of the copy root is standard and above `v_M(r)`**: `v_N(x′) = v(r) + 1` (`q = r`) or
`v(r) + last(v_N(q))` (`q ≠ r`). -/
theorem vx_N (hxb : q ≠ r → col M (r + L) = bump M q) (hBE : BumpE2 M) (hJ : RowJ M) (hR0 : R0P M)
    (hUM : UAT M) (hUN : UAT (TRIO.gexp M r L d0 d1 n)) {ρ σ : Valn} {rkN : Bool → Nat → Nat}
    (hCM : Cons M ρ) (hGM : Good3 M ρ) (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ)
    (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN) :
    isOT (σ.v (r + L)) = true ∧ ρ.v r < σ.v (r + L) := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hxN : r + L < N.length := by omega
  obtain ⟨hx2', _⟩ := entry_xprime_g (d1 := d1) hlen hL hA hq hd0e hn
  have he1N : entry N 1 (r + L) ≠ 0 := by
    rw [entry1_xN hlen hL hA hq hd0e hn hd1e]; omega
  have he2N : entry N 2 (r + L) = 0 := by rw [hx2', he2r]
  have hvr := vr_N hlen hL hA hq hd0e hn hd1e he2r h1x hqb hr1 hUM hUN hCM hCN hRN
  have hVot : isOT (σ.v r) = true := by rw [hvr]; exact hGM.ot_v r (by omega)
  have hv := (hCN (r + L) hxN).2
  unfold vRhs at hv
  rw [if_neg he1N, if_pos he2N, par1_xN hlen hL hA hq hd0e hn hd1e, hr1] at hv
  cases hu : upg N (r + L) with
  | none =>
    rw [hu] at hv
    have hot : isOT (add (σ.v r) one) = true := isOT_add hVot rfl
    change σ.v (r + L) = sf (add (σ.v r) one) at hv
    rw [sf_ot hot] at hv
    refine ⟨by rw [hv]; exact hot, ?_⟩
    rw [hv, ← hvr]; exact lt_add_principal z z _
  | some k =>
    obtain ⟨rfl, hqr⟩ := upg_xN hlen hL hA hq hd0e hn hd1e hr1 hxb hqb hJ hR0 hBE hu
    obtain ⟨hqot, hqz⟩ := vq_N hlen hL hA hq hd0e hn hd1e he2r h1x hqb hr1 hqr (hxb hqr) hBE hUM hUN
      hCM hGM hCN hRN
    rw [hu] at hv
    change σ.v (r + L) = sf (add (σ.v r) (last (σ.v k))) at hv
    have hot : isOT (add (σ.v r) (last (σ.v k))) = true := isOT_add hVot (isOT_last hqot)
    rw [sf_ot hot] at hv
    obtain ⟨st, u, hl⟩ := last_psi_form hqz
    refine ⟨by rw [hv]; exact hot, ?_⟩
    rw [hv, hl, ← hvr]; exact lt_add_principal st u _

end

/-- **`v(r)` of `M[1] = M.take x` is at most that of `M`** (equal unless `r = x − 1` loses its upgrade). -/
theorem vr_take_le {M : Mat} {r L d0 d1 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (he2r : entry M 2 r = 0)
    (hUM : UAT M) (hUG : UAT (TRIO.gexp M r L d0 d1 1)) {ρ τ : Valn} {rkM rkG : Bool → Nat → Nat}
    (hCM : Cons M ρ) (hGM : Good3 M ρ) (hRM : Rk M rkM) (hCG : Cons (TRIO.gexp M r L d0 d1 1) τ)
    (hRG : Rk (TRIO.gexp M r L d0 d1 1) rkG) : τ.v r ≤ ρ.v r := by
  set G := TRIO.gexp M r L d0 d1 1 with hG
  have hlG : G.length = r + 1 * L := TRIO.gexp_length hlen
  have hag := agree_gexp hlen hL hA hd0e (le_refl 1) he2r hUM hUG hCM hCG hRG
  have hrM : r < M.length := by omega
  have hr1M : Anc0 M r (r + 1) := anc_between hA (r + 1) (by omega) (by omega)
  have hnd : ∀ m, entry M 1 r ≠ 0 → (par M 1 r = some m ∨ (entry M 2 r = 0 ∧ upg M r = some m)) →
      ¬ DepS M (SR r) false m := by
    intro m h1 hm hd
    rcases hm with hm | ⟨h2, hm⟩
    · exact not_depS_v_self hRM hrM (DepS.vpar h1 hm hd)
    · exact not_depS_v_self hRM hrM (DepS.vupg h1 h2 hm hd)
  rw [(hCG r (by omega)).2, (hCM r hrM).2]
  unfold vRhs
  rw [entry_gexp_pre hlen (le_refl 1) 1 (by omega), entry_gexp_pre hlen (le_refl 1) 2 (by omega),
    par_gexp_pre hlen (le_refl 1) 1 (by omega)]
  by_cases h1 : entry M 1 r = 0
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1, if_pos he2r, if_pos he2r]
  have hV : vOpt τ (par M 1 r) = vOpt ρ (par M 1 r) := by
    cases hm : par M 1 r with
    | none => rfl
    | some m =>
      show τ.v m = ρ.v m
      exact (hag m (par_lt M 1 r m hm)).2 (hnd m h1 (Or.inl hm))
  have hVot : isOT (vOpt ρ (par M 1 r)) = true := by
    cases hm : par M 1 r with
    | none => rfl
    | some m => exact hGM.ot_v m (by have := par_lt M 1 r m hm; omega)
  rw [hV]
  have hincM : ∀ k, upg M r = some k → τ.v k = ρ.v k ∧ isOT (last (ρ.v k)) = true ∧
      one ≤ last (ρ.v k) := by
    intro k hk
    have hkr := upg_lt_of_child hr1M hk
    refine ⟨(hag k hkr).2 (hnd k h1 (Or.inr ⟨he2r, hk⟩)), isOT_last (hGM.ot_v k (by omega)), ?_⟩
    obtain ⟨_, _, _, he, _⟩ := upg_facts hk
    exact one_le_of_ne_z (last_ne_z_bd (v_ne_z_of_e1 hCM (by omega) (by rw [he]; exact h1)))
  by_cases hr1x : r + 1 < r + L
  · have hu : upg G r = upg M r := by
      rw [← upg_take G hr1x, hG, gexp_take_x hlen (le_refl 1), upg_take M hr1x]
    rw [hu]
    cases hk : upg M r with
    | none => exact le_refl _
    | some k =>
      simp only
      rw [(hincM k hk).1]
  · have hu : upg G r = none := by
      rw [hG, gexp_one_gen hlen]
      have := upg_take_last M (k := r + L) (by omega) (by omega)
      rwa [show r + L - 1 = r by omega] at this
    rw [hu]
    simp only
    have hot1 : isOT (add (vOpt ρ (par M 1 r)) one) = true := isOT_add hVot rfl
    cases hk : upg M r with
    | none => exact le_refl _
    | some k =>
      simp only
      obtain ⟨_, hlot, hle⟩ := hincM k hk
      rw [sf_ot hot1, sf_ot (isOT_add hVot hlot)]
      exact add_le_add_left _ hle

end Ytosk
