/-
**WfExQ1 (2026-11-01): the target bundle `Inv3V3` of the new `t = 1` engines.**

`Inv3V2` (V3Inv2) failed below SRO only in five fields, all through the bad bump call (WfBad.BadCall):
`adn`, `tplow`, `adw` (q = r) and `ads`, `tplos` (q ≠ r).  `Inv3V3` is `Inv3V2` with
- `adn   : AbsDN`  → `adn0  : AbsDN0`  (WfInvA1, the seed use only),
- `tplow : TPLoWs` → `tploq : TPLoQ`   (below: the old conclusion, or the re-exposed form `P + W[g]` at every
  source `v` call of the hole `a`; WfQrE notes §3 (L')),
- `adw   : AbsDWs` dropped (the DQ engine does not use absorption),
- `auwl  : AbsUWL` dropped (absorption at upgrade calls; false on a standard 39-column matrix, WfExQ12; the first
  version of this file, commit aad2270f, still had it),
- `ads   : AbsDS`  → `adsx  : AbsDSX`  (WfQnE2),
- `tplos : TPLoS`  → `tplosx : TPLoSX` (WfQnE2).
Every other field is unchanged.  Bridges: `Inv3V2A.toV3`, `Inv3V2.toV3` (each new form is weaker).
-/
import Ytosk.WfInvA1
import Ytosk.WfQnE2

namespace Ytosk.WfExQ1
open T Ytosk Ytosk.WfQnE2

set_option linter.unusedSectionVars false

/-- **A source of the hole `a`**: a `v` call `i` of `D` with `v(i) = a`, row 1 nonzero, and its last term `W`
(the bump term `bumpW i` when row 2 ≠ 0; the last summand of `v(upg i)` when row 2 = 0). -/
def TSrc (M : Mat) (ρ : Valn) (a : T) (i : Nat) (W : T) : Prop :=
  i < M.length - 1 ∧ DepX M (M.length - 1) false i ∧ entry M 1 i ≠ 0 ∧ ρ.v i = a ∧
    ((entry M 2 i ≠ 0 ∧ W = bumpW M ρ i) ∨ (entry M 2 i = 0 ∧ ∃ k, upg M i = some k ∧ W = last (ρ.v k)))

/-- **`TPLoQ`** (replaces `TPLoWs`): the pattern of `TPLoWAt` at the seed; at chain level `m` (index `m + d_c`
for the old form, `m + d_i` for the source form) either the old conclusion holds, or the hole has a source and at
every source `i` the re-exposed value `P + W[g]` (`P = v(P₁ i)`) keeps the low part empty. -/
def TPLoQ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z →
    one ≤ (drop1 M (M.length - 1) rk).o r →
    ∀ c, c < M.length - 1 → DepX M (M.length - 1) true c → ∀ s y, ρ.o c = psi s y z →
    y ≠ app b (psi (succ μ) z z) → (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a → cof a = .omega →
    ∀ m : Nat, 1 ≤ m + dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c →
      ¬ psi (fsD a (gamS μ (app b (psi (succ μ) z z)) ((drop1 M (M.length - 1) rk).o r)
          (m + dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c))) z z < psi (succ s) z z ∨
      ((∃ i W, TSrc M ρ a i W) ∧ ∀ i W, TSrc M ρ a i W →
        ¬ psi (add (vOpt ρ (par M 1 i)) (fsD W (gamS μ (app b (psi (succ μ) z z))
            ((drop1 M (M.length - 1) rk).o r)
            (max 1 (m + dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) i))))) z z < psi (succ s) z z)

/-- `TPLoWs` gives `TPLoQ` (left disjunct; `k = m + d_c ≥ max 1 d_c`). -/
theorem tpLoQ_of_tpLoWs {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (h : TPLoWs M ρ rk) : TPLoQ M ρ rk := by
  intro r μ b h1 h0 h2 hro hs c hc hd s y hcv hyb hl a hla hns hOa hca m hm
  exact Or.inl (h r μ b h1 h0 h2 hro hs c hc hd s y hcv hyb hl a hla hns hOa hca _
    (max_le hm (Nat.le_add_left _ _)))

/-- **`Inv3V3`: the carried value invariant of the new `t = 1` engines.** -/
structure Inv3V3 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  cons : Cons M ρ
  good : Good3 M ρ
  rank : Rk M rk
  vs : VSmallF M ρ
  fc : FrameClosed M ρ
  fo : FrameOT M ρ
  kd : BumpKidsDec M ρ
  td : BumpTermDec M ρ
  ph : PH3cG M ρ
  fc3 : FC3 M ρ
  vra : VSmallRAll M ρ
  adsx : AbsDSX M ρ rk
  aus : AbsUS M ρ rk
  tp1 : TP1C M ρ
  tplosx : TPLoSX M ρ rk
  tp1w : TP1WC M ρ
  tploq : TPLoQ M ρ rk
  auw0 : AbsUW0 M ρ rk
  trigs : TrigS0 M ρ rk
  tplon : TPLoN M ρ
  adn0 : AbsDN0 M ρ rk
  rootS : ∀ i ∈ roots M, Single (ρ.o i)
  rootP : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)

/-- `Inv3V2A` gives `Inv3V3`. -/
theorem Inv3V2A.toV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3V2A M ρ rk) : Inv3V3 M ρ rk :=
  ⟨I.cons, I.good, I.rank, I.vs, I.fc, I.fo, I.kd, I.td, I.ph, I.fc3, I.vra, absDSX_of_absDS I.ads, I.aus,
    I.tp1, tpLoSX_of_tpLoS I.tplos, I.tp1w, tpLoQ_of_tpLoWs I.tplow, I.auw0, I.trigs, I.tplon,
    I.adn0, I.rootS, I.rootP⟩

/-- `Inv3V2` gives `Inv3V3`. -/
theorem Inv3V2.toV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3V2 M ρ rk) : Inv3V3 M ρ rk :=
  Inv3V2A.toV3 I.toA

end Ytosk.WfExQ1
