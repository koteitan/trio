/-
HeU.lean: 深い葉の keystone (GoodChtX_deep) への背骨 — 一般段 q の深い葉の展開像。

深い葉を遠い語の子に積むと悪い根の段は遠い段 r。その展開の内側の再下降は段 r-1（段 0 でない）で、
また深い葉になる（HeT の一段木化 tow_dtree は最上段 r=1 専用）。よって GoodChtX_deep は段 q の整礎帰納:
段 q'+1 の深い葉の GpT を upleaf_deep_core（HeQ）で展開 → hrep = 段 q' の深い葉の塔 → IH。段 0 で木。

- dtreeQ q' j: 外段 q'+1、内側再下降 段 q' の深い葉の塔（dtreeQ 0 = HeT.dtree = 木）。
- tow_dtreeQ: tow (q'+1) 0 [(1,q'+2,0),(2,q'+2,0)] (j+1) = (0,q'+1,0) :: topTs 0 [dtreeQ q' j]。
  これが帰納の各段で「生の展開 tow」を「段 q' の深い葉を持つ topTs」に橋渡しする。
-/
import HeT
import HeQ

namespace TRIO
namespace HeU

open Wset Small HdA HdB HdE HdF HdG HdH HdI HdJ HdQ HeI HeK HeQ
open GwS GxJ GxL GxP GxW GyB HbM

/-- 外段 q'+1、内側再下降 段 q' の深い葉の塔（段 0 に達すると HeT.dtree = 木）。 -/
noncomputable def dtreeQ (q' : ℕ) : ℕ → HdA.UT
  | 0 => HdA.UT.tie (q'+1) []
  | j + 1 => HdA.UT.tie (q'+1) [HdA.UT.tie q' [dtreeQ q' j]]

/-- ★ 一般段 q'+1 の深い葉の展開像: tow (q'+1) 0 [(1,q'+2,0),(2,q'+2,0)] (j+1)
    = (0,q'+1,0) :: topTs 0 [dtreeQ q' j]。 -/
theorem tow_dtreeQ (q' j : ℕ) :
    (tow (q'+1) 0 [((1,q'+2,0):ℕ×ℕ×ℕ),((2,q'+2,0):ℕ×ℕ×ℕ)] (j+1) : TrioSeq)
      = ((0,q'+1,0):ℕ×ℕ×ℕ) :: topTs 0 [dtreeQ q' j] := by
  induction j with
  | zero =>
      simp only [dtreeQ, tow, graft_eq_shift, topTs, topT, shiftr01, entry, List.getD,
        List.dropLast, List.append_nil, List.map_nil, List.map_cons, Nat.add_zero]
      refine congrArg (List.cons _) ?_
      refine congrArg (fun z => [z]) ?_
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      simp; omega
  | succ j ih =>
    rw [tow, graft_eq_shift]
    simp only [show [((1,q'+2,0):ℕ×ℕ×ℕ),((2,q'+2,0):ℕ×ℕ×ℕ)].dropLast = [((1,q'+2,0):ℕ×ℕ×ℕ)] from rfl,
      show entry [((1,q'+2,0):ℕ×ℕ×ℕ),((2,q'+2,0):ℕ×ℕ×ℕ)] 0 ([((1,q'+2,0):ℕ×ℕ×ℕ),((2,q'+2,0):ℕ×ℕ×ℕ)].length - 1) = 2 from rfl]
    rw [ih]
    simp only [dtreeQ, topTs, topT, shiftr01, List.map_cons, List.map_nil, List.append_nil,
      List.cons_append, List.nil_append, Nat.add_zero, Nat.zero_add, List.map_map]
    rw [show 1 + (q' + 1) = q' + 2 from by omega, show 1 + q' = q' + 1 from by omega,
      show (1:ℕ) + 1 = 2 from rfl,
      show ((fun (p : ℕ×ℕ×ℕ) => (p.1 + 1, p.2.1, p.2.2)) ∘ fun p => (p.1 + 1, p.2.1, p.2.2))
        = (fun (p : ℕ×ℕ×ℕ) => (p.1 + 2, p.2.1, p.2.2)) from by funext p; simp [Function.comp]]

/-- 段 0 では深い葉の塔は HeT.dtree（木）に一致。 -/
theorem dtreeQ_zero (j : ℕ) : dtreeQ 0 j = HeT.dtree j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [dtreeQ, HeT.dtree, ih]

/-! ## 段の帰納の底（L=1）: 木の塔 dtree は GpT 側でも木（TreeOKs）で良い子並び -/

/-- ★ HeT.dtree は GpT 側の木条件 TreeOKs（段 0 の再下降）を満たす。TreeTs_dtree の TreeOKs 版。 -/
theorem TreeOKs_dtree (c j : ℕ) : HeI.TreeOKs c 0 true [HeT.dtree j] := by
  induction j with
  | zero =>
      exact HeI.TreeOKs_cons_up (l := 0) rfl (by decide)
        (HeI.TreeOKs_nil c 1 false) (HeI.TreeOKs_nil c 0 true)
  | succ j ih =>
      exact HeI.TreeOKs_cons_up (l := 0) rfl (by decide)
        (HeI.TreeOKs_cons_tie0 ih (HeI.TreeOKs_nil c 1 false)) (HeI.TreeOKs_nil c 0 true)

/-- ★ 段の帰納の底: 木の塔 dtree j は良い子並び（GoodChtX）。GoodChtX_snocT + TreeOKs_dtree。 -/
theorem GoodChtX_dtree {A0 : List ℕ} {o u : ℕ} (hAo : ∀ a ∈ A0, a < o) (hA01 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) (j : ℕ) : GoodChtX A0 o (fun _ => 0) u [[HeT.dtree j]] := by
  have := HeI.GoodChtX_snocT hAo hA01 ho (GoodChtX_nil A0 o (fun _ => 0) u) (TreeOKs_dtree u j)
  simpa using this

/-! ## ★★ 突破: 深い塔は「段 q の木 dtree」の像に等しい（深くない！） -/

/-- ★★ topTs 0 [dtreeQ q j] = topTs q [dtree j]。段 0 の深い構造 = 段 q の木。
    深い塔は遠い段では**木**（dtree）であり、整礎帰納は不要。 -/
theorem topTs0_dtreeQ_eq (q : ℕ) : ∀ j, topTs 0 [dtreeQ q j] = topTs q [HeT.dtree j]
  | 0 => by
      simp only [dtreeQ, HeT.dtree, topTs, topT, shiftr01, List.map_nil, List.append_nil,
        Nat.add_zero, Nat.zero_add]
      refine congrArg (fun z => [z]) (Prod.ext rfl (Prod.ext ?_ rfl))
      simp; omega
  | j + 1 => by
      simp only [dtreeQ, HeT.dtree, topTs, topT, shiftr01, List.map_cons, List.map_nil,
        List.append_nil, List.cons_append, List.nil_append, Nat.add_zero, Nat.zero_add]
      have ih := topTs0_dtreeQ_eq q j
      simp only [topTs, List.append_nil] at ih
      rw [show (1:ℕ) + (q + 1) = q + 1 + 1 from by omega, show (1:ℕ) + q = q + 1 from by omega, ih]

/-- ★★ 純タイの木 dtree では chT b (q+1) u = topTs q（chT の段は r+l、topTs は v+1+l、r=v+1 で一致）。 -/
theorem chT_dtree_eq (b u q : ℕ) : ∀ j, chT b (q+1) u [HeT.dtree j] = topTs q [HeT.dtree j]
  | 0 => by simp [HeT.dtree, chT, unitT, topTs, topT, shiftr01]
  | j + 1 => by
      have ih := chT_dtree_eq b u q j
      simp only [HeT.dtree, chT, unitT, topTs, topT, shiftr01, List.map_cons, List.map_nil,
        List.append_nil, List.cons_append, List.nil_append, Nat.add_zero] at ih ⊢
      rw [ih]

/-! ## ★★★ 深い葉の keystone: GoodChtX_deep（既存機構で、整礎帰納なし） -/

/-- relT は純タイ木 dtree を変えない（ch 荷が無いので relift しない）。 -/
theorem relT_dtree (A0 : List ℕ) (h g : ℕ → ℕ) (u : ℕ) :
    ∀ j, relT A0 h g u (HeT.dtree j) = HeT.dtree j
  | 0 => by simp [HeT.dtree, relT, relTs]
  | j + 1 => by simp only [HeT.dtree, relT, relTs, relT_dtree A0 h g u j]

/-- 木の子 dtree の遠い語での描画は、深い葉の展開 tow の形にちょうど一致。 -/
theorem key_dtree (b u q0 : ℕ) (j : ℕ) :
    fwH b (q0+1) (FTLt b (q0+1) u [[HeT.dtree j]]) u []
      = [((1,q0+1,1):ℕ×ℕ×ℕ), ((2,q0+1,1):ℕ×ℕ×ℕ)]
        ++ shiftr01 1 0 (shiftr01 1 0 (((0,q0+1,0):ℕ×ℕ×ℕ) :: chT b (q0+1) u [HeT.dtree j])) := by
  simp [fwH, FTLt, shiftr01, mlift_nil]

/-- ★★ 深い葉の展開 tow は、遠い段 q0+1 で描画した木の塔 chT[dtree] に等しい。 -/
theorem tow_eq_chT_dtree (b u q0 : ℕ) (j : ℕ) :
    (tow (q0+1) 0 [((1,q0+2,0):ℕ×ℕ×ℕ),((2,q0+2,0):ℕ×ℕ×ℕ)] (j+1) : TrioSeq)
      = ((0,q0+1,0):ℕ×ℕ×ℕ) :: chT b (q0+1) u [HeT.dtree j] := by
  rw [tow_dtreeQ, topTs0_dtreeQ_eq, ← chT_dtree_eq b u q0]

/-- ★★★ 深い葉 tie 1 [tie 1 []] は良い子並び（GoodChtX）。深い塔が遠い段では木であることを使い、
    整礎帰納なしで upleaf_deep_coreD + GoodChtX_dtree（木の塔）で出る。 -/
theorem GoodChtX_deep {A0 : List ℕ} {o u : ℕ} (hAo : ∀ a ∈ A0, a < o) (hA01 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) : GoodChtX A0 o (fun _ => 0) u [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]] := by
  refine ⟨?_, ?_⟩
  · intro us hus; simp only [List.mem_singleton] at hus; subst hus; simp [RawTs, RawT]
  · intro g S o' f b hE hub ws hC hR
    have hrel : [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]].map (relTs A0 (fun _ => 0) g u)
        = [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]] := by simp [relTs, relT]
    rw [hrel, farWt_snoc]
    obtain ⟨q0, hq0⟩ : ∃ q0, b + liftOff f (S ++ A0) o' + 1 = q0 + 1 :=
      ⟨b + liftOff f (S ++ A0) o', rfl⟩
    rw [hq0]
    have key : fwH b (q0+1) (FTLt b (q0+1) u [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]]) u []
        = [((1,q0+1,1):ℕ×ℕ×ℕ), ((2,q0+1,1):ℕ×ℕ×ℕ)]
          ++ shiftr01 1 0 (shiftr01 1 0 (((0,q0+1,0):ℕ×ℕ×ℕ) :: ([((1,q0+2,0):ℕ×ℕ×ℕ)] ++ [((2,q0+2,0):ℕ×ℕ×ℕ)]))) := by
      simp [fwH, FTLt, chT, unitT, shiftr01, mlift_nil]
    rw [key]
    refine upleaf_deep_coreD hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 f
      (Fr_farWt _ _ _) (Fr_letter (q0+1) [((1,q0+1,1):ℕ×ℕ×ℕ)])
      (Hd_letter (q0+1) [((1,q0+1,1):ℕ×ℕ×ℕ)]) (by simp)
      (D := [((1,q0+2,0):ℕ×ℕ×ℕ)]) (d0 := 2) (m := q0+2) (q := q0+1) (d := 1)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; omega)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact le_refl _)
      (by omega) (by omega) (by omega) ?_
    intro m' hm'
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    rw [show ([((1,q0+2,0):ℕ×ℕ×ℕ)] ++ [((2,q0+2,0):ℕ×ℕ×ℕ)])
        = [((1,q0+2,0):ℕ×ℕ×ℕ),((2,q0+2,0):ℕ×ℕ×ℕ)] from rfl, tow_eq_chT_dtree b u q0]
    have hgd := (GoodChtX_dtree hAo hA01 ho j).2 g S o' f b hE hub ws hC hR
    have hreldt : [[HeT.dtree j]].map (relTs A0 (fun _ => 0) g u) = [[HeT.dtree j]] := by
      simp only [List.map_cons, List.map_nil, relTs, relT_dtree A0 (fun _ => 0) g u j]
    rw [hreldt, hq0, farWt_snoc, key_dtree] at hgd
    exact hgd

end HeU
end TRIO
