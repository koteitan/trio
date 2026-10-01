/-
**3 行・t = 0: M.take x で r の子の値は変わらない（hG′ の構造的な根拠）。**

x = r + L（最後の列、P_0(x) = r、行 1 が 0）。x − 1 に上げがなければ（upg M (x − 1) = none）、
r < d < x の列はどれも変化の集合 C（`ChgX`）に入らない（`no_chg_B`）。
- 源: x の葉は x、上げの源は x − 1（仮定で除く）、数え方の変化は x の親 r か上げの先（`cnt_change`）、
  のりしろの源は x の親 r。どれも (r, x) に入らない。
- 伝播: 子から親（o）は、(r, x) の外の子は x だけで、その親は r。v の読み込み（P_1・祖先型の上げ）は、
  読まれる側が r 以下なら `chg_struct` の TopC と `no_anc_upg` で起きない。
したがって r の子（x を除く）の o は M.take x でも同じで、その和も同じ（`sum_children_r_take`）。
上げの仮定は外せない: 構造の不変条件をすべて満たす非標準形
(0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,1,0)(5,0,0) では x − 1 = 5 が祖先 1 に上げる。
集合 A・B（SRO から届く行列）では、P_0(r) ののりしろの子 r の下で x − 1 の上げは 0 件。
-/
import Ytosk.V3T0S3

namespace Ytosk

open T

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB

/-- **Nothing strictly between the parent `r` of `x` and `x` changes** when `x − 1` has no upgrade. -/
theorem no_chg_B {r : Nat} (hp : par M 0 x = some r) (he1 : entry M 1 x = 0)
    (hU : r < x - 1 → upg M (x - 1) = none) :
    ∀ b d, ChgX M x b d → r < d → d < x → False := by
  have hrx : r < x := par_lt M 0 x r hp
  have hparx : ∀ i, x ∈ children M i → i = r := fun i h => by
    have := (mem_children_iff.mp h).2; rw [hp] at this; exact (Option.some.inj this).symm
  intro b d h
  induction h with
  | leaf => intro _ h; omega
  | supg hne =>
    intro h1 _
    exact hne (hU h1)
  | @scnt i c hc hcx hnot =>
    intro h1 h2
    have hic := (mem_children hc).1
    rcases cnt_change hx h2 hcx hnot with h | h
    · have := hparx c h; omega
    · exact absurd h (by rw [hU (by omega)]; simp)
  | @snb i _ _ hxi _ =>
    intro h1 _
    have := hparx i hxi; omega
  | @ochild i c hc _ _ _ ih =>
    intro h1 h2
    have hic := (mem_children hc).1
    have hcl := (mem_children hc).2
    by_cases hcx : c < x
    · exact ih (by omega) hcx
    · have hce : c = x := by omega
      subst hce
      have := hparx i hc; omega
  | ov _ ih => exact ih
  | @vpar i m _ hpm hm ih =>
    intro h1 h2
    have hmi := par_lt M 1 i m hpm
    by_cases hrm : r < m
    · exact ih hrm (by omega)
    · have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hm).1 rfl (by omega)
      exact hT.2.2 i h2 hpm
  | @vupg i k h1 _ hu hk ih =>
    intro hri hix
    obtain ⟨m, _, _, hcol, hcase⟩ := upg_spec hu
    rcases hcase with hki | ⟨hA, hki⟩
    · by_cases hkx : k < x
      · exact ih (by omega) hkx
      · -- `k = x` would give row 1 of `x` equal to that of `i`
        have hke : k = x := by have := upg_succ_lt hu; omega
        subst hke
        have : entry M 1 k = entry M 1 i := by
          have e : entry M 1 k = (col M k).2.1 := rfl
          rw [e, hcol]
        exact h1 (this ▸ he1)
    · by_cases hrk : r < k
      · exact ih hrk (by omega)
      · have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hk).1 rfl (by omega)
        exact no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB hT (by omega) hu hA hki
  | @vbump i j k _ _ hj _ hk _ ih =>
    intro h1 h2
    have hij := (mem_children hj).1
    have hjk := (mem_children hk).1
    have hkl := (mem_children hk).2
    by_cases hkx : k < x
    · exact ih (by omega) hkx
    · have hke : k = x := by omega
      subst hke
      have := hparx j hk; omega

end

/-- **The children of `r` keep their values in `M.take x`** (hence their sum: `hG′` of `t0_main′`). -/
theorem children_r_take_same {M : Mat} {x r : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hp : par M 0 x = some r) (he1 : entry M 1 x = 0) (hU : r < x - 1 → upg M (x - 1) = none)
    {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hR' : Rk (M.take x) rk') :
    (children (M.take x) r).map ρ'.o = (children (M.take x) r).map ρ.o := by
  apply List.map_congr_left
  intro c hc
  rw [children_take, List.mem_filter] at hc
  have hcx : c < x := by simpa using hc.2
  have hrc := (mem_children hc.1).1
  exact (chg_off hx hC hG hC' hR' c hcx).1
    (fun h => no_chg_B hx hR0 hZ2 hSD hZ1 hUAT hUAB hp he1 hU true c h hrc hcx)

end Ytosk
