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

end

end Ytosk
