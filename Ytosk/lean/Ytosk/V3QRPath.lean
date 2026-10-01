/-
**3 行・t = 1・q = r: 列ごとの添字での局所の等式（経路の定理の一般形）。**

q = r の展開では D の列ごとに添字 Zf(i) が違う（引き上げで鎖の先へずれる）。各 D の呼び出しに
局所の条件 `OLocZ`・`VLocZ`（枠の形と、親の添字 Zf(i) と子の添字 Zf(c) をつなぐ枠の等式）を置くと、
貼り合わせ glueZ の右辺は fsD(M の値, Zf(i)) になる（`qr_path`）。帰納法は要らない
（子の貼り合わせの値は glueZ の定義から出る）。
-/
import Ytosk.V3QRMain

namespace Ytosk

open T

/-- Local conditions at an `o` call with per-column indices: either only the subscript changes, or the
last counted child `c` is in `D` and the frame equation links `Zf c` and `Zf i`. -/
def OLocZ (M : Mat) (x : Nat) (ρ : Valn) (Zf : Nat → T) (i : Nat) : Prop :=
  (DepX M x false i ∧
    (∀ d ∈ children M i, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) ∧
    isOT (fsD (ρ.v i) (Zf i)) = true ∧ ρ.v i ≠ z ∧ isSucc (ρ.v i) = false) ∨
  (¬ DepX M x false i ∧ ∃ L c R, children M i = L ++ c :: R ∧ col M c ≠ bump M i ∧
    ¬ (isUpg M c = true ∧ topped M c = true) ∧
    (∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true)) ∧
    (∀ d ∈ L, Counted M i d → ¬ DepX M x true d) ∧ DepX M x true c ∧
    Single (fsD (ρ.o c) (Zf c)) ∧ fsD (ρ.o c) (Zf c) ≤ ρ.o c ∧
    fsD (ρ.o i) (Zf i) =
      psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (fsD (ρ.o c) (Zf c))) z)

/-- Local conditions at a `v` call with per-column indices: an upgrade frame (same index as `U i`) or
a bump frame (the `ω` exchange links `Zf k` and `Zf i`). -/
def VLocZ (M : Mat) (x : Nat) (ρ : Valn) (Zf : Nat → T) (i : Nat) : Prop :=
  entry M 1 i ≠ 0 ∧ (∀ m, par M 1 i = some m → ¬ DepX M x false m) ∧
  ((∃ k, entry M 2 i = 0 ∧ upg M i = some k ∧ k < x ∧ DepX M x false k ∧ Zf i = Zf k ∧
      Single (last (ρ.v k)) ∧ Single (fsD (last (ρ.v k)) (Zf k)) ∧
      fsD (last (ρ.v k)) (Zf k) ≤ last (ρ.v k) ∧
      (∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) → q < fsD (last (ρ.v k)) (Zf k))) ∨
   (∃ L K j k, entry M 2 i ≠ 0 ∧ children M i = L ++ [j] ∧ col M j = bump M i ∧
      children M j = K ++ [k] ∧ DepX M x true k ∧ (∀ d ∈ K, ¬ DepX M x true d) ∧
      (∀ d ∈ L, ∀ e ∈ children M d, e < x ∧ ¬ DepX M x true e) ∧
      Single (fsD (ρ.o k) (Zf k)) ∧ fsD (ρ.o k) (Zf k) ≤ ρ.o k ∧
      (∀ t ∈ K.map ρ.o ++ [ρ.o k], Single t) ∧
      (K.map ρ.o ++ [ρ.o k]).Pairwise (fun a b => b ≤ a) ∧
      (∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t) ∧
      (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))]).Pairwise
        (fun a b => b ≤ a) ∧
      (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) (Zf k)]))]).Pairwise
        (fun a b => b ≤ a) ∧
      (∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))], one < t) ∧
      (∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) (Zf k)]))],
        one < t) ∧
      fsD (omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
          (omega (sumN (K.map ρ.o ++ [ρ.o k]))))) (Zf i) =
        omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
          (omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) (Zf k)])))) ∧
      (∀ q ∈ summands (vOpt ρ (par M 1 i)), q < omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
            (omega (sumN (K.map ρ.o ++ [ρ.o k])))) →
        q < omega (app (sumN (nzs (L.map (bumpTerm M ρ i))))
            (omega (sumN (K.map ρ.o ++ [fsD (ρ.o k) (Zf k)])))))))

section
variable {M : Mat} {x : Nat} {ρ ρN : Valn} {Zf : Nat → T}

/-- The glued `o` value of a `D` column at or below `x`. -/
theorem glueZ_o_D (hxN : ρN.o x = fsD (ρ.o x) (Zf x)) {c : Nat} (hc : c ≤ x) (hd : DepX M x true c) :
    (glueZ M x ρ ρN Zf).o c = fsD (ρ.o c) (Zf c) := by
  rcases Nat.lt_or_ge c x with h | h
  · exact glueZ_o_dep ρ ρN Zf h hd
  · have : c = x := by omega
    subst this; rw [glueZ_o_ge ρ ρN Zf (le_refl _)]; exact hxN

theorem vOpt_glueZ {i : Nat} (hi : i < x) (hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m) :
    vOpt (glueZ M x ρ ρN Zf) (par M 1 i) = vOpt ρ (par M 1 i) := by
  cases hp : par M 1 i with
  | none => rfl
  | some m =>
    have hm : m < i := par_lt M 1 i m hp
    exact glueZ_v_lt ρ ρN Zf (by omega) (hpd m hp)

/-- **Only the subscript changes**, per-column index. -/
theorem qr_o_sub (hC : Cons M ρ) (hx : x + 1 = M.length) {i : Nat} (hi : i < x)
    (hnc : ∀ d ∈ children M i, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hv : DepX M x false i) (hvot : isOT (ρ.v i) = true) (hvot' : isOT (fsD (ρ.v i) (Zf i)) = true)
    (hvz : ρ.v i ≠ z) (hvs : isSucc (ρ.v i) = false) :
    oRhs M (glueZ M x ρ ρN Zf) i = fsD (ρ.o i) (Zf i) := by
  have hiM : i < M.length := by omega
  have hzero : ∀ σ : Valn, sumN ((children M i).map (cnt M σ i)) = z := by
    intro σ
    have : (children M i).map (cnt M σ i) = (children M i).map (fun _ => z) :=
      List.map_congr_left (fun d hd => cnt_unc σ (hnc d hd))
    rw [this, sumN_skip_z (fun t ht => by
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; exact Or.inl rfl)
      (by rw [nzs_zeros _ (fun t ht => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; rfl)]; simp),
      nzs_zeros _ (fun t ht => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; rfl)]
    rfl
  rw [(hC i hiM).1]
  unfold oRhs
  rw [hzero, hzero, glueZ_v_dep ρ ρN Zf hi hv]
  exact (frame_sub hvot hvot' hvz hvs).symm

/-- **One upgrade frame**, per-column index (the index of `i` is that of `U i`). -/
theorem qr_v_upg (hC : Cons M ρ) (hx : x + 1 = M.length) {i k : Nat} (hi : i < x) (hk : k < x)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i = 0) (hu : upg M i = some k)
    (hpd : ∀ m, par M 1 i = some m → ¬ DepX M x false m)
    (hkd : DepX M x false k) (hZ : Zf i = Zf k) (hV : Single (last (ρ.v k)))
    (hV' : Single (fsD (last (ρ.v k)) (Zf k))) (hle : fsD (last (ρ.v k)) (Zf k) ≤ last (ρ.v k))
    (hAot : isOT (vOpt ρ (par M 1 i)) = true)
    (hAV : ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) → q < fsD (last (ρ.v k)) (Zf k)) :
    vRhs M (glueZ M x ρ ρN Zf) i = fsD (ρ.v i) (Zf i) := by
  have hiM : i < M.length := by omega
  have hA := vOpt_glueZ (ρ := ρ) (ρN := ρN) (Zf := Zf) hi hpd
  have hkz : ρ.v k ≠ z := by
    intro h; have := single_ne_z hV; rw [h] at this; exact this rfl
  have hlast' : last ((glueZ M x ρ ρN Zf).v k) = fsD (last (ρ.v k)) (Zf k) := by
    rw [glueZ_v_dep ρ ρN Zf hk hkd]; exact last_fsD hkz hV'
  obtain ⟨B, h1B, h2B⟩ := add_exchange hAot hV hV' hle hAV
  have hvi : ρ.v i = app B (last (ρ.v k)) := by
    rw [(hC i hiM).2]
    unfold vRhs
    rw [if_neg h1, if_pos h2, hu]
    simp only
    rw [sf_ot (isOT_add hAot hV.1), h1B]
  rw [hvi, hZ, fsD_app B (single_ne_z hV)]
  unfold vRhs
  rw [if_neg h1, if_pos h2, hu, hA]
  simp only
  rw [hlast', sf_ot (isOT_add hAot hV'.1), h2B]

/-- **One `o` frame at the last counted child**, per-column index. -/
theorem qr_o_last (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hxN : ρN.o x = fsD (ρ.o x) (Zf x)) {i : Nat} (hi : i < x) {L R : List Nat} {c : Nat}
    (hch : children M i = L ++ c :: R) (hcb : col M c ≠ bump M i)
    (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
    (hR : ∀ d ∈ R, col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true))
    (hLnd : ∀ d ∈ L, Counted M i d → ¬ DepX M x true d) (hcd : DepX M x true c)
    (hv : ¬ DepX M x false i)
    (hcS' : Single (fsD (ρ.o c) (Zf c))) (hle : fsD (ρ.o c) (Zf c) ≤ ρ.o c)
    (hF : fsD (ρ.o i) (Zf i) =
      psi (ρ.v i) (spArg (ρ.v i) (preState M ρ i L) (fsD (ρ.o c) (Zf c))) z) :
    oRhs M (glueZ M x ρ ρN Zf) i = fsD (ρ.o i) (Zf i) := by
  have hiM : i < M.length := by omega
  have hc : c ∈ children M i := by rw [hch]; simp
  have hcM := (mem_children hc).2
  have hic := (mem_children hc).1
  have hcx : c ≤ x := by omega
  have hsplit := cvals_split hch hcb hcu hR (single_ne_z (single_o hC hG hcM))
  have hdec := hG.dec i hiM
  rw [hsplit] at hdec
  have hp' : (nzs (L.map (cnt M ρ i)) ++ [fsD (ρ.o c) (Zf c)]).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_append] at hdec ⊢
    refine ⟨hdec.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    exact le_trans hle (hdec.2.2 a ha _ (List.mem_singleton_self _))
  rw [hF]
  apply oRhs_frame_gen hiM hch hcb hcu hR (glueZ_v_lt ρ ρN Zf hi hv) ?_ (glueZ_o_D hxN hcx hcd)
    (hG.ot_v i hiM) ?_ hcS' hp'
  · intro d hd
    by_cases hcd' : Counted M i d
    · have hdc : d < c := by
        have hsort := children_sorted M i
        rw [hch] at hsort
        exact (List.pairwise_append.mp hsort).2.2 d hd c List.mem_cons_self
      rw [cnt_cnt _ hcd'.1 hcd'.2, cnt_cnt _ hcd'.1 hcd'.2]
      exact glueZ_o_lt ρ ρN Zf (by omega) (hLnd d hd hcd')
    · have : col M d = bump M i ∨ (isUpg M d = true ∧ topped M d = true) := by
        by_cases h1 : col M d = bump M i
        · exact Or.inl h1
        · right; by_contra h2; exact hcd' ⟨h1, h2⟩
      rw [cnt_unc _ this, cnt_unc _ this]
  · intro t ht
    exact cnt_single hC hG i t (by rw [hch, List.map_append]; exact List.mem_append_left _ ht)

/-- **The path theorem with per-column indices** (`t = 1`, `q = r`): the local conditions give the
local equations of the glued valuation on `D`. -/
theorem qr_path (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hxN : ρN.o x = fsD (ρ.o x) (Zf x))
    (hO : ∀ i, i < x → DepX M x true i → OLocZ M x ρ Zf i)
    (hV : ∀ i, i < x → DepX M x false i → VLocZ M x ρ Zf i) :
    ∀ i, i < x →
      (DepX M x true i → oRhs M (glueZ M x ρ ρN Zf) i = fsD (ρ.o i) (Zf i)) ∧
      (DepX M x false i → vRhs M (glueZ M x ρ ρN Zf) i = fsD (ρ.v i) (Zf i)) := by
  intro i hi
  have hiM : i < M.length := by omega
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rcases hO i hi hd with ⟨hv, hnc, hvot', hvz, hvs⟩ | ⟨hv, L, c, R, hch, hcb, hcu, hR, hLnd, hcd,
        hcS', hle, hF⟩
    · exact qr_o_sub hC hx hi hnc hv (hG.ot_v i hiM) hvot' hvz hvs
    · exact qr_o_last hC hG hx hxN hi hch hcb hcu hR hLnd hcd hv hcS' hle hF
  · obtain ⟨h1, hpd, hcase⟩ := hV i hi hd
    rcases hcase with ⟨k, h2, hu, hk, hkd, hZ, hVs, hVs', hle, hAV⟩ | ⟨L, K, j, k, h2, hch, hjb, hchj,
        hkd, hKnd, hLnd, hsk', hle, hsK, hpK, hsL, hpp, hpp', hgt, hgt', hωp, hAbs⟩
    · exact qr_v_upg hC hx hi hk h1 h2 hu hpd hkd hZ hVs hVs' hle (vOpt_ot hG hiM) hAV
    · have hj : j ∈ children M i := by rw [hch]; simp
      have hk : k ∈ children M j := by rw [hchj]; simp
      have hkx : k ≤ x := by
        have := (mem_children hk).2; omega
      have hK : ∀ d ∈ K, (glueZ M x ρ ρN Zf).o d = ρ.o d := by
        intro d hd'
        have hsort := children_sorted M j
        rw [hchj] at hsort
        have hdk : d < k := (List.pairwise_append.mp hsort).2.2 d hd' k (List.mem_singleton_self _)
        exact glueZ_o_lt ρ ρN Zf (by omega) (hKnd d hd')
      have hL : ∀ d ∈ L, bumpTerm M (glueZ M x ρ ρN Zf) i d = bumpTerm M ρ i d := by
        intro d hd'
        unfold bumpTerm
        split
        · congr 2
          apply List.map_congr_left
          intro e he
          exact glueZ_o_lt ρ ρN Zf (hLnd d hd' e he).1 (hLnd d hd' e he).2
        · rfl
      exact vRhs_bump_gen hC hiM h1 h2 hch hjb hchj (glueZ_o_D hxN hkx hkd) hK hL
        (vOpt_glueZ hi hpd) hsK hpK hsk' hle hsL hpp hpp' hgt hgt' hωp (vOpt_ot hG hiM) hAbs

end

end Ytosk
