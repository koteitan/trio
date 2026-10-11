/-
**段の結び LevLink: 値に現れる Ω_{μ+1}（μ ≠ 0）の μ は行 1 の子を持つ列の v。**

値の部分項の節点 ψ_a(0) + c（引数 0）を追う。ZNode Q t: t のどの節点 ψ_a(0) + c も「a = μ + 1、μ ≠ 0 なら Q μ」。
- 項の演算（add・app・sub・cut・split・H・step・spArg・omega・sumN・last）は ZNode を保つ。新しい節点の
  (添字, 引数) の組は入力の節点の組か、引数が 0 でない（omega の ψ_s(c) は c ≠ 0 のときだけ新しい）。
- 評価で新しく出る引数 0 の節点は o(i) = ψ_{v(i)}(0) だけ。v(i) = μ + 1 なら増分は 1 で μ = v(P_1 i)。
-/
import Ytosk.V3PhiLev
import Ytosk.V3ExpT2GV

namespace Ytosk

open T

section
variable (Q : T → Prop)

/-- The pair condition at a node `ψ_a(0) + c`. -/
def ZPairOK (a : T) : Prop := ∀ μ, a = succ μ → μ ≠ z → Q μ

/-- **Every node with argument `0` satisfies the pair condition.** -/
def ZNode (t : T) : Prop := ∀ a c, SubT (psi a z c) t → ZPairOK Q a

variable {Q}

theorem ZNode.of_subT {t w : T} (h : ZNode Q t) (hw : SubT w t) : ZNode Q w :=
  fun a c hs => h a c (hs.trans hw)

theorem zn_z : ZNode Q z := by intro a c h; cases h

theorem zn_psi_intro {a b c : T} (hab : b = z → ZPairOK Q a) (ha : ZNode Q a) (hb : ZNode Q b) (hc : ZNode Q c) :
    ZNode Q (psi a b c) := by
  intro a' c' h
  cases h with
  | refl => exact hab rfl
  | sub h => exact ha a' c' h
  | arg h => exact hb a' c' h
  | rest h => exact hc a' c' h

theorem ZNode.sub {a b c : T} (h : ZNode Q (psi a b c)) : ZNode Q a := h.of_subT (.sub (.refl a))
theorem ZNode.arg {a b c : T} (h : ZNode Q (psi a b c)) : ZNode Q b := h.of_subT (.arg (.refl b))
theorem ZNode.rest {a b c : T} (h : ZNode Q (psi a b c)) : ZNode Q c := h.of_subT (.rest (.refl c))
theorem ZNode.pair {a b c : T} (h : ZNode Q (psi a b c)) (hb : b = z) : ZPairOK Q a := by
  subst hb; exact h a c (.refl _)

/-- The head of a node keeps the condition. -/
theorem ZNode.head {a b c : T} (h : ZNode Q (psi a b c)) : ZNode Q (psi a b z) :=
  zn_psi_intro h.pair h.sub h.arg zn_z

theorem zn_app : ∀ {P X : T}, ZNode Q P → ZNode Q X → ZNode Q (app P X)
  | z, _, _, hX => by simpa using hX
  | psi a b P, X, hP, hX => by
    rw [app_psi]; exact zn_psi_intro hP.pair hP.sub hP.arg (zn_app hP.rest hX)

theorem zn_add : ∀ {x y : T}, ZNode Q x → ZNode Q y → ZNode Q (add x y)
  | z, _, _, hy => by simpa [add] using hy
  | psi a b c, z, hx, _ => by simpa [add] using hx
  | psi a b c, psi d e f, hx, hy => by
    rw [add_psi_psi]
    split
    · exact hy
    · exact zn_psi_intro hx.pair hx.sub hx.arg (zn_add hx.rest hy)

theorem zn_sub {x : T} (h : ZNode Q x) (y : T) : ZNode Q (sub x y) := h.of_subT (subT_sub x y)

theorem zn_cut (w : T) : ∀ {x : T}, ZNode Q x → ZNode Q (cut w x)
  | z, _ => zn_z
  | psi s b c, h => by
    unfold cut
    simp only
    split
    · exact zn_z
    · exact zn_psi_intro h.pair h.sub h.arg (zn_cut w h.rest)

theorem zn_split1 (t : T) : ∀ {x : T}, ZNode Q x → ZNode Q (split x t).1
  | z, _ => by simpa [split] using zn_z
  | psi a b c, h => by
    unfold split
    split
    · exact zn_z
    · exact zn_psi_intro h.pair h.sub h.arg (zn_split1 t h.rest)

theorem zn_H {s y c : T} (h : ZNode Q (psi s y c)) : ZNode Q (H s y) := by
  unfold H
  exact zn_add (zn_cut _ h.arg) (zn_sub h.head _)

theorem zn_step {a b s y c : T} (hb : ZNode Q b) (h : ZNode Q (psi s y c)) : ZNode Q (step a b s y c) := by
  unfold step
  split
  · exact zn_H h
  · exact zn_add hb h.head

theorem zn_spArg (a : T) : ∀ {b c : T}, ZNode Q b → ZNode Q c → ZNode Q (spArg a b c)
  | _, z, hb, _ => hb
  | b, psi s y c, hb, hc => by
    rw [spArg_cons]; exact zn_spArg a (zn_step hb hc) hc.rest

theorem zn_last : ∀ {t : T}, ZNode Q t → ZNode Q (last t)
  | z, h => h
  | psi _ _ z, h => h
  | psi _ _ (psi c d e), h => by
    show ZNode Q (last (psi c d e)); exact zn_last h.rest

theorem add_eq_z' : ∀ {x y : T}, add x y = z → x = z ∧ y = z
  | z, y, h => by simpa [add] using h
  | psi a b c, z, h => by simp [add] at h
  | psi a b c, psi d e f, h => by
    rw [add_psi_psi] at h
    split at h
    · cases h
    · cases h

theorem zPairOK_z : ZPairOK Q z := by
  intro μ h; exact absurd h.symm (succ_ne_z μ)

theorem zn_omega {x : T} (h : ZNode Q x) : ZNode Q (omega x) := by
  unfold omega
  split
  · exact zn_psi_intro (fun _ => zPairOK_z) zn_z h zn_z
  · split
    · exact zn_psi_intro (fun _ => zPairOK_z) zn_z zn_z zn_z
    · rename_i s b c _
      refine zn_psi_intro ?_ h.sub (zn_add (zn_split1 _ h.arg) (zn_sub h _)) zn_z
      intro hz
      -- the argument is `0` only if `b = 0`
      have hb : b = z := by
        obtain ⟨hp, hs⟩ := add_eq_z' hz
        rw [hp] at hs
        by_contra hb
        unfold sub at hs
        simp only at hs
        have hlt : psi s z z < psi s b z := by
          rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hb)⟩)
        rw [if_pos (show lt (psi s z z) (psi s b z) = true from hlt)] at hs
        cases hs
      exact h.pair hb

theorem zn_one : ZNode Q one := zn_psi_intro (fun _ => zPairOK_z) zn_z zn_z zn_z

theorem zn_foldl : ∀ (l : List T) {acc : T}, ZNode Q acc → isOT acc = true →
    (∀ t ∈ l, ZNode Q t ∧ isOT t = true) → ZNode Q (l.foldl (fun a b => sf (add a b)) acc)
  | [], _, h, _, _ => h
  | t :: l, acc, h, hot, hl => by
    simp only [List.foldl_cons]
    have ht := hl t (by simp)
    have hadd : isOT (add acc t) = true := isOT_add hot ht.2
    rw [sf_ot hadd]
    exact zn_foldl l (zn_add h ht.1) hadd (fun t' h' => hl t' (by simp [h']))

theorem zn_sumN {l : List T} (hl : ∀ t ∈ l, ZNode Q t ∧ isOT t = true) : ZNode Q (sumN l) :=
  zn_foldl l zn_z rfl hl

end

/-! ## 添字の加算 -/

theorem app_one_inj : ∀ {x y : T}, app x one = app y one → x = y
  | z, z, _ => rfl
  | z, psi a b c, h => by
    simp [one] at h
    exact absurd h.2.2 (by cases c <;> simp)
  | psi a b c, z, h => by
    simp [one] at h
    exact absurd h.2.2.symm (by cases c <;> simp)
  | psi a b c, psi d e f, h => by
    simp only [app_psi, psi.injEq] at h
    obtain ⟨rfl, rfl, h⟩ := h
    rw [app_one_inj h]

theorem last_succ : ∀ μ : T, last (succ μ) = one
  | z => rfl
  | psi a b c => by
    show last (psi a b (app c one)) = one
    have := last_succ c
    change last (app c one) = one at this
    cases hc : app c one with
    | z => exact absurd hc (succ_ne_z c)
    | psi d e f => rw [hc] at this; exact this

/-- `V + X = μ + 1` with a single `X` forces `X = 1` and `μ = V`. -/
theorem succ_of_add_single {V X μ : T} (hX : ∃ s y, X = psi s y z) (h : add V X = succ μ) :
    X = one ∧ μ = V := by
  obtain ⟨s, y, rfl⟩ := hX
  have hl := congrArg last h
  rw [last_add_single, last_succ] at hl
  rw [hl] at h ⊢
  refine ⟨rfl, ?_⟩
  rw [add_one_eq_app] at h
  exact (app_one_inj h).symm

theorem omega_ne_one {x : T} (hx : x ≠ z) : omega x ≠ one := by
  unfold omega
  by_cases hlt : lt x (psi z (psi one z z) z) = true
  · rw [if_pos hlt]; intro h; simp [one] at h; exact hx h
  · rw [if_neg hlt]
    cases x with
    | z => exact absurd rfl hx
    | psi s b c =>
      simp only
      intro h
      simp only [one, psi.injEq] at h
      obtain ⟨rfl, hz, -⟩ := h
      obtain ⟨hp, hs⟩ := add_eq_z' hz
      rw [hp] at hs
      by_cases hb : b = z
      · subst hb
        apply hlt
        show psi z z c < psi z (psi one z z) z
        rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, T.z_lt_psi _ _ _⟩)
      · unfold sub at hs
        simp only at hs
        have hlt' : psi z z z < psi z b z := by
          rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hb)⟩)
        rw [if_pos (show lt (psi z z z) (psi z b z) = true from hlt')] at hs
        cases hs

theorem foldl_ne_z : ∀ (l : List T) {acc : T}, acc ≠ z → isOT acc = true → (∀ t ∈ l, isOT t = true) →
    l.foldl (fun a b => sf (add a b)) acc ≠ z
  | [], _, h, _, _ => h
  | t :: l, acc, h, hot, hl => by
    simp only [List.foldl_cons]
    have hadd : isOT (add acc t) = true := isOT_add hot (hl t (by simp))
    rw [sf_ot hadd]
    exact foldl_ne_z l (fun he => h (add_eq_z' he).1) hadd (fun t' h' => hl t' (by simp [h']))

theorem sumN_one_cons_ne_z {l : List T} (hl : ∀ t ∈ l, isOT t = true) : sumN (one :: l) ≠ z := by
  unfold sumN
  simp only [List.foldl_cons]
  have h1 : sf (add z one) = one := rfl
  rw [h1]
  exact foldl_ne_z l (by simp [one]) rfl hl

section
variable {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
include hC hG

theorem isOT_bumpOmega (i : Nat) :
    isOT (omega (sumN (one :: (children M i).map (bumpTerm M ρ i)))) = true := by
  apply isOT_omega; apply isOT_sumN
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · rfl
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i j

theorem bumpOmega_ne_one (i : Nat) : omega (sumN (one :: (children M i).map (bumpTerm M ρ i))) ≠ one := by
  apply omega_ne_one
  apply sumN_one_cons_ne_z
  intro t ht
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i j

/-- **`v(i) = μ + 1` only as `v(P_1 i) + 1`**, so `μ ∈ VK`. -/
theorem zPairOK_v {i : Nat} (hi : i < M.length) : ZPairOK (InVK M ρ) (ρ.v i) := by
  intro μ hμ hne
  have hv := (hC i hi).2
  unfold vRhs at hv
  by_cases h1 : entry M 1 i = 0
  · rw [if_pos h1] at hv; rw [hv] at hμ; exact absurd hμ.symm (succ_ne_z μ)
  rw [if_neg h1] at hv
  have hV0 : isOT (vOpt ρ (par M 1 i)) = true := by
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  have fin : μ = vOpt ρ (par M 1 i) → InVK M ρ μ := by
    intro he
    cases hp : par M 1 i with
    | none => rw [hp] at he; exact absurd he hne
    | some m => rw [hp] at he; exact ⟨i, m, hi, hp, he.symm⟩
  by_cases h2 : entry M 2 i = 0
  · rw [if_pos h2] at hv
    cases hu : upg M i with
    | none =>
      rw [hu] at hv
      simp only at hv
      rw [sf_ot (isOT_add hV0 rfl)] at hv
      rw [hv] at hμ
      exact fin (succ_of_add_single ⟨z, z, rfl⟩ hμ).2
    | some k =>
      rw [hu] at hv
      simp only at hv
      rw [upg_target_last hC hG hi hu] at hv
      have hW : isOT (bumpW M ρ k) = true := isOT_bumpOmega hC hG k
      rw [sf_ot (isOT_add hV0 hW)] at hv
      rw [hv] at hμ
      have := (succ_of_add_single (omega_psi_form _) hμ).1
      exact absurd this (bumpOmega_ne_one hC hG k)
  · rw [if_neg h2] at hv
    rw [sf_ot (isOT_add hV0 (isOT_bumpOmega hC hG i))] at hv
    rw [hv] at hμ
    have := (succ_of_add_single (omega_psi_form _) hμ).1
    exact absurd this (bumpOmega_ne_one hC hG i)

/-- **LevLink**: every node `ψ_{μ+1}(0) + c` (`μ ≠ 0`) in a value has `μ ∈ VK`. -/
theorem levLink {rk : Bool → Nat → Nat} (hR : Rk M rk) :
    ∀ i, i < M.length → ZNode (InVK M ρ) (ρ.o i) ∧ ZNode (InVK M ρ) (ρ.v i) := by
  have key : ∀ N, ∀ i, i < M.length →
      (rk true i ≤ N → ZNode (InVK M ρ) (ρ.o i)) ∧ (rk false i ≤ N → ZNode (InVK M ρ) (ρ.v i)) := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      have hV : ∀ i, i < M.length → rk false i ≤ N → ZNode (InVK M ρ) (ρ.v i) := by
        intro i hi hN
        obtain ⟨_, _, hR3⟩ := hR i hi
        have hv := (hC i hi).2
        unfold vRhs at hv
        by_cases h1 : entry M 1 i = 0
        · rw [if_pos h1] at hv; rw [hv]; exact zn_z
        rw [if_neg h1] at hv
        obtain ⟨hRp, hRu, hRb⟩ := hR3 h1
        have hV0 : isOT (vOpt ρ (par M 1 i)) = true ∧ ZNode (InVK M ρ) (vOpt ρ (par M 1 i)) := by
          cases hp : par M 1 i with
          | none => exact ⟨rfl, zn_z⟩
          | some m =>
            have hml : m < M.length := by have := par_lt M 1 i m hp; omega
            have hlt := hRp m hp
            exact ⟨hG.ot_v m hml, (ih _ (by omega) m hml).2 (Nat.le_refl _)⟩
        by_cases h2 : entry M 2 i = 0
        · rw [if_pos h2] at hv
          cases hu : upg M i with
          | none =>
            rw [hu] at hv; simp only at hv
            rw [sf_ot (isOT_add hV0.1 rfl)] at hv
            rw [hv]; exact zn_add hV0.2 zn_one
          | some k =>
            rw [hu] at hv; simp only at hv
            have hkl : k < M.length := upg_lt hi hu
            have hlt := hRu h2 k hu
            have hXot : isOT (last (ρ.v k)) = true := isOT_last (hG.ot_v k hkl)
            rw [sf_ot (isOT_add hV0.1 hXot)] at hv
            rw [hv]; exact zn_add hV0.2 (zn_last ((ih _ (by omega) k hkl).2 (Nat.le_refl _)))
        · rw [if_neg h2] at hv
          rw [sf_ot (isOT_add hV0.1 (isOT_bumpOmega hC hG i))] at hv
          rw [hv]
          refine zn_add hV0.2 (zn_omega (zn_sumN ?_))
          intro t ht
          refine ⟨?_, ?_⟩
          · rcases List.mem_cons.mp ht with rfl | ht
            · exact zn_one
            · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
              unfold bumpTerm
              split
              · rename_i hjb
                refine zn_omega (zn_sumN ?_)
                intro t' ht'
                obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht'
                have hkl : k < M.length := (mem_children hk).2
                have hlt := hRb h2 j hj hjb k hk
                exact ⟨(ih _ (by omega) k hkl).1 (Nat.le_refl _), hG.ot_o k hkl⟩
              · exact zn_z
          · rcases List.mem_cons.mp ht with rfl | ht
            · rfl
            · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i j
      refine fun i hi => ⟨fun hN => ?_, hV i hi⟩
      obtain ⟨hvo, hRc, _⟩ := hR i hi
      rw [o_spArg hC hG hi]
      refine zn_psi_intro (fun _ => zPairOK_v hC hG hi) ?_ ?_ zn_z
      · exact (ih _ (by omega) i hi).2 (Nat.le_refl _)
      · refine zn_spArg _ zn_z (zn_sumN ?_)
        intro t ht
        unfold cvals nzs at ht
        rw [List.mem_filter] at ht
        obtain ⟨ht, hne⟩ := ht
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
        have hcl : c < M.length := (mem_children hc).2
        unfold cnt at hne ⊢
        split at hne
        · simp at hne
        · rename_i hb
          split at hne
          · simp at hne
          · rename_i hu
            have hlt := hRc c hc hb hu
            rw [if_neg hb, if_neg hu]
            exact ⟨(ih _ (by omega) c hcl).1 (Nat.le_refl _), hG.ot_o c hcl⟩
  exact fun i hi => ⟨(key _ i hi).1 (Nat.le_refl _), (key _ i hi).2 (Nat.le_refl _)⟩

end

/-- **The hole node**: a term with an `Ω`-type hole contains `Ω_{μ+1} + c` at its hole level `μ`. -/
theorem hole_node : ∀ {X : T}, OHole X → ∃ c, SubT (psi (succ (holeLev X)) z c) X
  | z, h => absurd h (by simp [OHole])
  | psi a b (psi c d e), h => by
    have h' : OHole (psi c d e) := h
    obtain ⟨c', hc'⟩ := hole_node h'
    exact ⟨c', by rw [holeLev_rest]; exact .rest hc'⟩
  | psi a b z, h => by
    by_cases hb : b = z
    · subst hb
      have h2 : a ≠ z ∧ (isSucc a = true ∨ OHole a) := by simpa [OHole] using h
      by_cases hs : isSucc a = true
      · have hl : holeLev (psi a z z) = init a := by simp [holeLev, hs]
        refine ⟨z, ?_⟩
        rw [hl, succ, init_app_one hs]; exact .refl _
      · have hOa : OHole a := by simpa [hs] using h2.2
        have hs' : isSucc a = false := by simpa using hs
        obtain ⟨c', hc'⟩ := hole_node hOa
        exact ⟨c', by rw [holeLev_sub' hs']; exact .sub hc'⟩
    · have hs : isSucc b = false := by
        by_contra hc
        have : isSucc b = true := by simpa using hc
        simp [OHole, hb, this] at h
      have hOb : OHole b := by
        cases hcb : cof b with
        | big μ => exact ohole_of_cof_big hcb
        | zero => simpa [OHole, hb, hs, hcb] using h
        | succ => simpa [OHole, hb, hs, hcb] using h
        | omega => simpa [OHole, hb, hs, hcb] using h
      obtain ⟨c', hc'⟩ := hole_node hOb
      exact ⟨c', by rw [holeLev_arg hb]; exact .arg hc'⟩

section
variable {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {rk : Bool → Nat → Nat} (hR : Rk M rk)
include hC hG hR

theorem zn_bumpW (i : Nat) : ZNode (InVK M ρ) (bumpW M ρ i) := by
  have hL := levLink hC hG hR
  unfold bumpW
  refine zn_omega (zn_sumN ?_)
  intro t ht
  refine ⟨?_, ?_⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact zn_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
      unfold bumpTerm
      split
      · refine zn_omega (zn_sumN ?_)
        intro t' ht'
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht'
        have hkl : k < M.length := (mem_children hk).2
        exact ⟨(hL k hkl).1, hG.ot_o k hkl⟩
      · exact zn_z
  · rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG i j

/-- **The hole level of a bump term is in `VK`.** -/
theorem holeLev_inVK {c : Nat} (hO : OHole (bumpW M ρ c)) (hμ : holeLev (bumpW M ρ c) ≠ z) :
    InVK M ρ (holeLev (bumpW M ρ c)) := by
  obtain ⟨c', hc'⟩ := hole_node hO
  exact zn_bumpW hC hG hR c _ _ hc' _ rfl hμ

/-- **LevFree at the hole level of a bump term** (the μ > 0 seed condition of t1-exp), from `VKFree`. -/
theorem levFree_hole (hV : VKFree M ρ) {c p : Nat} (hc : c < M.length) (hch : P1Chain M p c)
    (hO : OHole (bumpW M ρ c)) (hμ : holeLev (bumpW M ρ c) ≠ z) :
    LevFree (holeLev (bumpW M ρ c)) (ρ.v p) :=
  levFree_chain_of_vk hV hc hch hμ (holeLev_inVK hC hG hR hO hμ)

end

end Ytosk
