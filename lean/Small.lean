/-
Small.lean: `SmallA.lean` の続き。

ビルド時間を短くするため、安定した部分を `SmallA.lean` に分けた。
このファイルには新しく足す定理だけを書く。大きくなったらまた分ける。
-/
import SmallA
import Mathlib.Data.Finsupp.WellFounded

namespace TRIO
namespace Small

open Wset

/-! ### ★ 壁を `SbT` の文法の 1 本の欠けに絞る

`SbT` / `SbF` は「安全な兄弟」の文法で、走り 2 は既に入っている:

    SbT.ttwoB : SbT A → SbF B → SbT (two A (two B nil))

つまり **走り 2 そのものは無条件で緑**（`NPd_true_twoTwoB_lift`、階段は `nstN2`）。
足りないのは走り 2 の**先端に荷**を載せる構成子だけ:

    ttwoZ : SbT A → SbF B → SbF Z → SbT (two A (two B Z))

`Z = nil` が `ttwoB`。`SbF` には `two` の構成子が無いので、`ttwoZ` を足しても
`stk 3`（2 の記録 3 連）は出ない。行376 には届かず、シート証明中の行だけが出る。 -/

def TtwoZ : Prop := ∀ (A B Z : Jk1), SbT A → SbF B → SbF Z →
  ∀ ks : List Bool, NPd (true :: ks) (Jk1.two A (Jk1.two B Z))

/-- `TtwoZ` の `Z = nil` の場合は緑（`SbT.ttwoB`）。 -/
theorem TtwoZ_nilTop {A B : Jk1} (hA : SbT A) (hB : SbF B) (ks : List Bool) :
    NPd (true :: ks) (Jk1.two A (Jk1.two B Jk1.nil)) :=
  NPd_true_of_SbT (SbT.ttwoB hA hB) ks

/-- `TtwoZ` の `Z = pay nil C` の場合がちょうど壁 `Pay2`。 -/
theorem Pay2_of_TtwoZ (h : TtwoZ) : Pay2 := fun C hC =>
  (NPd_bnil _).mp (NPd_step [] (JkT_nil : FrmJ [] Jk1.nil)
    ((NPd_bnil _).mpr GOK_nil)
    (h Jk1.nil Jk1.nil (Jk1.pay Jk1.nil C) SbT.nil SbF.nil (SbF.pay SbF.nil hC) []))

/-- ★ シート証明中の行は `TtwoZ` 1 文から出る。 -/
theorem RB_of_TtwoZ (h : TtwoZ) :
    [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
     ((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ),
     ((4, 2, 0) : ℕ × ℕ × ℕ), ((5, 2, 0) : ℕ × ℕ × ℕ), ((6, 0, 0) : ℕ × ℕ × ℕ),
     ((7, 1, 1) : ℕ × ℕ × ℕ), ((8, 1, 0) : ℕ × ℕ × ℕ), ((7, 1, 0) : ℕ × ℕ × ℕ),
     ((8, 2, 1) : ℕ × ℕ × ℕ), ((9, 1, 0) : ℕ × ℕ × ℕ), ((10, 2, 0) : ℕ × ℕ × ℕ),
     ((11, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := RB_of_Pay2 (Pay2_of_TtwoZ h)

/-- ★ いま開いている最小の行列も同じ 1 文から出る。 -/
theorem R375m61_of_TtwoZ (h : TtwoZ) :
    R375m ++ [((6, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  R375m61_of_Pay2 (Pay2_of_TtwoZ h)

/-- 連鎖の兄弟 `twoIt nil (pay nil Y) n` は `SbT`（`SbF` の先端を横に積むだけ）。
だから `ChBase` のうち連鎖で要る分は文法の中に入っている。 -/
theorem SbT_twoItPay {Y : TrioSeq} (hY : Bok Y) :
    ∀ n : ℕ, SbT (twoIt Jk1.nil (Jk1.pay Jk1.nil Y) n)
  | 0 => SbT.nil
  | (n + 1) => SbT.two (SbT_twoItPay hY n) (SbF.pay SbF.nil hY)

#print axioms TtwoZ_nilTop
#print axioms Pay2_of_TtwoZ
#print axioms RB_of_TtwoZ
#print axioms SbT_twoItPay

/-! ### ★ いま開いている最小の行列（`bms` 実測, 2026-09-12）

    R600 (6,0,0)
      = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,0,0)(6,0,0)

これは今まで証明できた一番大きい行列より大きく、`R600 (7,0,0)`,
`R600 (7,1,0)`, `R600 (7,1,1)`, …, `RB` のどれよりも小さい（全部標準形）。
展開は

    R600 (6,0,0) [n] = R373 ++ ((5,2,0)(6,0,0))^(n+1)

というシフト無しの平らな塔なので、`flat_mem''` でこの塔 1 本に落ちる。 -/

def Blk60 : TrioSeq := [((5, 2, 0) : ℕ × ℕ × ℕ), ((6, 0, 0) : ℕ × ℕ × ℕ)]

theorem R600_eq_R373blk : R600 = R373 ++ Blk60 := by
  simp [R600, R375m, Blk60, List.append_assoc]

/-- ★ シート証明中の行は「平らな塔」1 本に落ちる。 -/
theorem R6006_flat (htw : ∀ n : ℕ, R373 ++ copies Blk60 n ∈ W 0) :
    R600 ++ [((6, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hne : Blk60 ≠ [] := by simp [Blk60]
  have hhead : entry Blk60 0 0 < 6 := by simp [Blk60, entry]
  have htail : ∀ r, 1 ≤ r → r < Blk60.length → 6 ≤ entry Blk60 0 r := by
    intro r hr1 hr2
    have hr : r = 1 := by simp [Blk60] at hr2; omega
    subst hr
    simp [Blk60, entry]
  have h := flat_mem'' (Y0 := R373) (M := Blk60) (d := 6) hne hhead htail
    (by intro n; simpa [copies] using htw n)
  rw [R600_eq_R373blk]
  simpa [List.append_assoc] using h

#print axioms R6006_flat

/-! ### ★ 壁の最小形（`WPd` 層）: 平らな走りの先端に荷

`WPd_twoA_runB`（緑）は

    b + 1 ≤ k → JkA A → (∀ ks, WPd ((b+1)::ks) A) → WPd ((k+1)::ks) (two A nil)

で、先端が `nil` の場合。先端に荷 `pay nil B` を許すのが `WRunPay`。
`WPd_FLr`（緑）は同じ木を予算 `0` で作るので、足りないのは予算 `k+1` の版だけ。 -/

def WRunPay : Prop := ∀ (k b : ℕ), b + 1 ≤ k → ∀ A : Jk1, JkA A →
  (∀ ks : List ℕ, WPd ((b + 1) :: ks) A) → ∀ B : TrioSeq, Bok B →
  ∀ ks : List ℕ, WPd ((k + 1) :: ks) (Jk1.two A (Jk1.pay Jk1.nil B))

theorem WPd_FLr_bud (h : WRunPay) : ∀ (Bs : List TrioSeq), (∀ C ∈ Bs, Bok C) →
    ∀ k : ℕ, Bs.length ≤ k → ∀ ks : List ℕ, WPd ((k + 1) :: ks) (FLr Bs)
  | [], _, k, _, ks => WPd_nilF k ks
  | (B :: Bs), hB, k, hk, ks => by
      have hsub : ∀ C ∈ Bs, Bok C := fun C hC => hB C (List.mem_cons_of_mem B hC)
      have hlen : Bs.length + 1 ≤ k := by simpa using hk
      have hA : ∀ ks' : List ℕ, WPd ((Bs.length + 1) :: ks') (FLr Bs) :=
        fun ks' => WPd_FLr_bud h Bs hsub Bs.length (le_refl _) ks'
      exact h k Bs.length hlen (FLr Bs) (JkA_FLr Bs hsub) hA B (hB B List.mem_cons_self) ks

theorem WPd_twoNilFLr (h : WRunPay) (Bs : List TrioSeq) (hB : ∀ C ∈ Bs, Bok C)
    (ks : List ℕ) : WPd (0 :: ks) (Jk1.two Jk1.nil (FLr Bs)) :=
  WPd_twoOf (k := Bs.length) trivial (fun q _ => WPd_nilAll _)
    (WPd_FLr_bud h Bs hB Bs.length (le_refl _) ks)

/-- 荷が全部 `[(0,0,0)]` の平らな走り。`jk1 l (FLz n) = ((l+1,2,0)(l+2,0,0))^n`。 -/
def FLz (n : ℕ) : Jk1 := FLr (List.replicate n [((0, 0, 0) : ℕ × ℕ × ℕ)])

theorem Bok_FLz_mem (n : ℕ) :
    ∀ C ∈ List.replicate n [((0, 0, 0) : ℕ × ℕ × ℕ)], Bok C := by
  intro C hC
  rw [List.eq_of_mem_replicate hC]
  exact Bok_zero

theorem FLz_succ (n : ℕ) :
    FLz (n + 1) = Jk1.two (FLz n) (Jk1.pay Jk1.nil [((0, 0, 0) : ℕ × ℕ × ℕ)]) := by
  show FLr (List.replicate (n + 1) [((0, 0, 0) : ℕ × ℕ × ℕ)]) = _
  rw [List.replicate_succ]
  rfl

theorem jk1_FLz (l : ℕ) : ∀ n : ℕ,
    jk1 l (FLz n)
      = copies [((l + 1, 2, 0) : ℕ × ℕ × ℕ), ((l + 2, 0, 0) : ℕ × ℕ × ℕ)] n
  | 0 => by simp [FLz, FLr, jk1, copies]
  | (n + 1) => by
      rw [FLz_succ]
      show jk1 l (FLz n) ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
        (jk1 (l + 1) Jk1.nil ++ shiftr01 (l + 1 + 1) 0 [((0, 0, 0) : ℕ × ℕ × ℕ)])) = _
      rw [jk1_FLz l n, copies_snoc, show l + 1 + 1 = l + 2 from by omega]
      simp [jk1, shiftr01]

theorem GOK_oneNilTwoFLz (h : WRunPay) (n : ℕ) :
    GOK (Jk1.one Jk1.nil (Jk1.two Jk1.nil (FLz n))) :=
  (WPd_bnil _).mp (WPd_step [] (JkT_nil : FrmN [] Jk1.nil)
    ((WPd_bnil _).mpr GOK_nil)
    (WPd_twoNilFLr h (List.replicate n [((0, 0, 0) : ℕ × ℕ × ℕ)]) (Bok_FLz_mem n) []))

theorem jk1_oneTwoFLz (n : ℕ) :
    jk1 2 (Jk1.one Jk1.nil (Jk1.two Jk1.nil (FLz n)))
      = [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ)] ++ copies Blk60 n := by
  have e : jk1 4 (FLz n) = copies Blk60 n := by
    have h := jk1_FLz 4 n
    simpa [Blk60] using h
  show jk1 2 Jk1.nil ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) ::
    (jk1 (2 + 1) Jk1.nil ++ (((2 + 1 + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      jk1 (2 + 1 + 1) (FLz n)))) = _
  rw [show (2 : ℕ) + 1 + 1 = 4 from by omega, e]
  simp [jk1]

/-- ★ シート証明中の行は `WRunPay` 1 文から出る。 -/
theorem tw_R373_Blk60 (h : WRunPay) (n : ℕ) : R373 ++ copies Blk60 n ∈ W 0 := by
  have hG0 := GOK_oneNilTwoFLz h n [] WOk_nil GoodFb_wordJ_nil
  have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (Jk1.two Jk1.nil (FLz n))]) := by
    simpa using hG0
  have hh := rowJ_mem_genF Aok_R338 hG
  rw [wordJ_singleton, colJ, jk1_oneTwoFLz n] at hh
  simpa [R373, R344, R341, R338, List.append_assoc] using hh

theorem R6006_of_WRunPay (h : WRunPay) : R600 ++ [((6, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  R6006_flat (tw_R373_Blk60 h)

#print axioms WPd_FLr_bud
#print axioms jk1_FLz
#print axioms R6006_of_WRunPay

/-! ### ★ いま開いている最小の 1 列追加: `R600 (4,0,0)`

    R600 (4,0,0)
      = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,0,0)(4,0,0)

`bms -c` の実測で、`R600` の 1 列追加のうち「証明できたどれよりも大きい」
最小のもの。展開は `R341 ++ ((3,1,0)(4,2,0)(5,2,0)(6,0,0))^(n+1)`、
つまり `T6` の語の平らな塔。これも `WRunPay` 1 文から出る。 -/

def Tb60 : Jk1 :=
  Jk1.two Jk1.nil (Jk1.two Jk1.nil (Jk1.pay Jk1.nil [((0, 0, 0) : ℕ × ℕ × ℕ)]))

theorem JkA_Tb60 : JkA Tb60 := ⟨trivial, trivial, trivial, Bok_zero⟩

theorem WPd_Tb60 (h : WRunPay) (ks : List ℕ) : WPd (0 :: ks) Tb60 :=
  WPd_twoOf (k := 1) trivial (fun q _ => WPd_nilAll _)
    (h 1 0 (by omega) Jk1.nil trivial (fun ks' => WPd_nilF 0 ks')
      [((0, 0, 0) : ℕ × ℕ × ℕ)] Bok_zero ks)

def T6blk : TrioSeq :=
  [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ),
   ((5, 2, 0) : ℕ × ℕ × ℕ), ((6, 0, 0) : ℕ × ℕ × ℕ)]

theorem jk1_ItV_Tb60 : ∀ n : ℕ, jk1 2 (ItV Tb60 Jk1.nil n) = copies T6blk n
  | 0 => by simp [ItV, jk1, copies]
  | (n + 1) => by
      show jk1 2 (ItV Tb60 Jk1.nil n) ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) ::
        jk1 (2 + 1) Tb60) = _
      rw [jk1_ItV_Tb60 n, copies_snoc]
      simp [Tb60, jk1, shiftr01, T6blk]

theorem tw_R341_T6blk (h : WRunPay) (n : ℕ) : R341 ++ copies T6blk n ∈ W 0 := by
  have hGok : GOK (ItV Tb60 Jk1.nil n) :=
    (WPd_bnil _).mp (WPd_ItV [] JkA_Tb60 (WPd_Tb60 h []) (JkT_nil : FrmN [] Jk1.nil)
      ((WPd_bnil _).mpr GOK_nil) n)
  have hG : GoodFb (fun a b => wordJ a b [ItV Tb60 Jk1.nil n]) := by
    simpa using hGok [] WOk_nil GoodFb_wordJ_nil
  have hh := rowJ_mem_genF Aok_R338 hG
  rw [wordJ_singleton, colJ, jk1_ItV_Tb60 n] at hh
  simpa [R341, R338, List.append_assoc] using hh

/-- ★ いま開いている最小の 1 列追加も `WRunPay` 1 文から出る。 -/
theorem R600400_of_WRunPay (h : WRunPay) :
    R600 ++ [((4, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hne : T6blk ≠ [] := by simp [T6blk]
  have hhead : entry T6blk 0 0 < 4 := by simp [T6blk, entry]
  have htail : ∀ r, 1 ≤ r → r < T6blk.length → 4 ≤ entry T6blk 0 r := by
    intro r hr1 hr2
    simp only [T6blk, List.length_cons, List.length_nil] at hr2
    rcases r with _ | _ | _ | _ | r <;>
      first
        | omega
        | simp [T6blk, entry]
  have hmem := flat_mem'' (Y0 := R341) (M := T6blk) (d := 4) hne hhead htail
    (by intro n; simpa [copies] using tw_R341_T6blk h n)
  have e : R341 ++ T6blk = R600 := by
    simp [R600, R375m, R373, R344, R341, T6blk, List.append_assoc]
  rw [← e]
  simpa [List.append_assoc] using hmem

#print axioms tw_R341_T6blk
#print axioms R600400_of_WRunPay

/-! ### ★ `WPd (0::ks) Tb60` は無条件（`WRunPay` は要らなかった）

`Tb60 = two nil (two nil (pay nil [(0,0,0)]))` の荷 `(0,0,0)` を
`GoodFb_snoc_dupJt0` で展開すると、鎖は `twoIt nil (pay nil []) n`。
荷が空なので語は `twoIt nil nil n`（平らな走り）と同じで、
`WPd_twoIt_nil n n` + `WPd_twoOf (k := n)` で緑。兄弟が `nil` なので
`WPd_nilAll` がどの予算でも効き、幅 `n` に上限が要らない。 -/

theorem jk1_twoIt_payNil : ∀ (n l : ℕ),
    jk1 l (twoIt Jk1.nil (Jk1.pay Jk1.nil ([] : TrioSeq)) n)
      = jk1 l (twoIt Jk1.nil Jk1.nil n)
  | 0, _ => rfl
  | (n + 1), l => by
      show jk1 l (twoIt Jk1.nil (Jk1.pay Jk1.nil ([] : TrioSeq)) n) ++
          (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) (Jk1.pay Jk1.nil ([] : TrioSeq)))
        = jk1 l (twoIt Jk1.nil Jk1.nil n) ++
          (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) Jk1.nil)
      rw [jk1_twoIt_payNil n l, jk1_pay_nil]

theorem WPd_twoNil_twoItPayNil (n : ℕ) (ks : List ℕ) :
    WPd (0 :: ks) (Jk1.two Jk1.nil (twoIt Jk1.nil (Jk1.pay Jk1.nil ([] : TrioSeq)) n)) := by
  refine WPd_congr (0 :: ks) (fun l => ?_)
    (WPd_twoOf (k := n) (N := Jk1.nil) trivial (fun q _ => WPd_nilAll _)
      (WPd_twoIt_nil n n (le_refl n) ks))
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      jk1 (l + 1) (twoIt Jk1.nil Jk1.nil n))
    = jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      jk1 (l + 1) (twoIt Jk1.nil (Jk1.pay Jk1.nil ([] : TrioSeq)) n))
  rw [jk1_twoIt_payNil n (l + 1)]

/-- ★★★★★★ 無条件。 -/
theorem WPd_Tb60u (ks : List ℕ) : WPd (0 :: ks) Tb60 := by
  rw [WPd_iff]
  intro ctx hc
  have eT : Jk1.two Jk1.nil (Jk1.two Jk1.nil (Jk1.pay Jk1.nil
      (([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))) = Tb60 := by simp [Tb60]
  have hJT : JkT (plug (ctx ++ [Frm.ftwo Jk1.nil])
      (Jk1.two Jk1.nil (Jk1.pay Jk1.nil (([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))) := by
    rw [plug_snoc2, eT]
    exact WCtx_JkT (0 :: ks) ctx hc Tb60 (JkA_Tb60 : FrmN (0 :: ks) Tb60)
  intro ws hw hG
  have hIH : ∀ n : ℕ, 1 ≤ n → GoodFb (fun a b => wordJ a b
      (ws ++ [plug (ctx ++ [Frm.ftwo Jk1.nil])
        (twoIt Jk1.nil (Jk1.pay Jk1.nil ([] : TrioSeq)) n)])) := by
    intro n _
    rw [plug_snoc2]
    exact (WPd_iff (0 :: ks) _).mp (WPd_twoNil_twoItPayNil n ks) ctx hc ws hw hG
  have h := GoodFb_snoc_dupJt0 hw hJT hIH
  rw [plug_snoc2, eT] at h
  exact h

#print axioms WPd_Tb60u

/-! ### ★★★★★★ 無条件で緑になった行列 -/

theorem tw_R341_T6blk_u (n : ℕ) : R341 ++ copies T6blk n ∈ W 0 := by
  have hGok : GOK (ItV Tb60 Jk1.nil n) :=
    (WPd_bnil _).mp (WPd_ItV [] JkA_Tb60 (WPd_Tb60u []) (JkT_nil : FrmN [] Jk1.nil)
      ((WPd_bnil _).mpr GOK_nil) n)
  have hG : GoodFb (fun a b => wordJ a b [ItV Tb60 Jk1.nil n]) := by
    simpa using hGok [] WOk_nil GoodFb_wordJ_nil
  have hh := rowJ_mem_genF Aok_R338 hG
  rw [wordJ_singleton, colJ, jk1_ItV_Tb60 n] at hh
  simpa [R341, R338, List.append_assoc] using hh

theorem R341_T6blk_eq_R600 : R341 ++ T6blk = R600 := by
  simp [R600, R375m, R373, R344, R341, T6blk, List.append_assoc]

/-- ★★★★★★ `R600 (3,1,0)(4,2,0)(5,2,0)(6,0,0)`（塔の 2 段目）。 -/
theorem R600_T6blk2_mem : R600 ++ T6blk ∈ W 0 := by
  have h := tw_R341_T6blk_u 2
  have ec : copies T6blk 2 = T6blk ++ T6blk := by
    rw [copies_succ, copies_succ]
    simp [copies]
  rw [ec, ← List.append_assoc, R341_T6blk_eq_R600] at h
  exact h

/-- ★★★★★★ シート証明中の行が無条件で緑。 -/
theorem R600400_mem : R600 ++ [((4, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hne : T6blk ≠ [] := by simp [T6blk]
  have hhead : entry T6blk 0 0 < 4 := by simp [T6blk, entry]
  have htail : ∀ r, 1 ≤ r → r < T6blk.length → 4 ≤ entry T6blk 0 r := by
    intro r hr1 hr2
    simp only [T6blk, List.length_cons, List.length_nil] at hr2
    rcases r with _ | _ | _ | _ | r <;>
      first
        | omega
        | simp [T6blk, entry]
  have hmem := flat_mem'' (Y0 := R341) (M := T6blk) (d := 4) hne hhead htail
    (by intro n; simpa [copies] using tw_R341_T6blk_u n)
  rw [← R341_T6blk_eq_R600]
  simpa [List.append_assoc] using hmem

#print axioms tw_R341_T6blk_u
#print axioms R600_T6blk2_mem
#print axioms R600400_mem

/-! ### ★ `R600 (4,1,0)`（シート証明中）

展開は `TwD 4 R600 (n+1)`（`R600` 自身を高さ 4 で積む塔）。高さ 4 の吊るしの字は

    one nil (pay Tb60 B)      jk1 l = (l+1,1,0)(l+2,2,0)(l+3,2,0)(l+4,0,0) ++ B↑(l+2)

で、`WPd_Tb60u`（無条件）+ `WPd_payA` から出る。 -/

theorem jk1_Tb60 (l : ℕ) :
    jk1 l Tb60 = [((l + 1, 2, 0) : ℕ × ℕ × ℕ), ((l + 2, 2, 0) : ℕ × ℕ × ℕ),
      ((l + 3, 0, 0) : ℕ × ℕ × ℕ)] := by
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
    (jk1 (l + 1) Jk1.nil ++ (((l + 1 + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1 + 1) Jk1.nil ++
        shiftr01 (l + 1 + 1 + 1) 0 [((0, 0, 0) : ℕ × ℕ × ℕ)])))) = _
  rw [show l + 1 + 1 = l + 2 from by omega, show l + 2 + 1 = l + 3 from by omega]
  simp [jk1, shiftr01]

theorem WPd_payTb60 (ks : List ℕ) (B : TrioSeq) (hB : Bok B) :
    WPd (0 :: ks) (Jk1.pay Tb60 B) :=
  WPd_payA (0 :: ks) Tb60 (JkA_Tb60 : FrmN (0 :: ks) Tb60) (WPd_Tb60u ks) B hB

theorem GOK_onePayTb60 (B : TrioSeq) (hB : Bok B) :
    GOK (Jk1.one Jk1.nil (Jk1.pay Tb60 B)) :=
  (WPd_bnil _).mp (WPd_step [] (JkT_nil : FrmN [] Jk1.nil)
    ((WPd_bnil _).mpr GOK_nil) (WPd_payTb60 [] B hB))

theorem jk1_onePayTb60 (l : ℕ) (B : TrioSeq) :
    jk1 l (Jk1.one Jk1.nil (Jk1.pay Tb60 B))
      = [((l + 1, 1, 0) : ℕ × ℕ × ℕ), ((l + 2, 2, 0) : ℕ × ℕ × ℕ),
          ((l + 3, 2, 0) : ℕ × ℕ × ℕ), ((l + 4, 0, 0) : ℕ × ℕ × ℕ)]
        ++ shiftr01 (l + 2) 0 B := by
  show jk1 l Jk1.nil ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
    (jk1 (l + 1) Tb60 ++ shiftr01 (l + 1 + 1) 0 B)) = _
  rw [jk1_Tb60 (l + 1), show l + 1 + 1 = l + 2 from by omega,
    show l + 1 + 2 = l + 3 from by omega, show l + 1 + 3 = l + 4 from by omega]
  simp [jk1]

theorem hang4_R600 {B : TrioSeq} (hB : Bok B) : R600 ++ shiftr01 4 0 B ∈ W 0 := by
  have hG0 := GOK_onePayTb60 B hB [] WOk_nil GoodFb_wordJ_nil
  have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (Jk1.pay Tb60 B)]) := by
    simpa using hG0
  have hh := rowJ_mem_genF Aok_R338 hG
  rw [wordJ_singleton, colJ, jk1_onePayTb60 2 B] at hh
  simpa [R600, R375m, R373, R344, R341, R338, List.append_assoc] using hh

theorem Ancd4_R600 : Ancd 4 R600 := by
  intro j hj0 hjl hlt hmin
  have hlen : R600.length = 9 := by
    simp [R600, R375m, R373, R344, R341, R338]
  rw [hlen] at hjl
  have h3 : (3 : ℕ) < R600.length := by rw [hlen]; omega
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · omega
  · exact absurd (hmin 3 (by omega) h3) (by simp [R600, R375m, R373, R344, R341, R338, entry])
  · exact absurd (hmin 3 (by omega) h3) (by simp [R600, R375m, R373, R344, R341, R338, entry])
  · simp [R600, R375m, R373, R344, R341, R338, entry]
  · simp [R600, R375m, R373, R344, R341, R338, entry]
  · simp [R600, R375m, R373, R344, R341, R338, entry]
  · simp [R600, R375m, R373, R344, R341, R338, entry] at hlt
  · simp [R600, R375m, R373, R344, R341, R338, entry] at hlt
  · simp [R600, R375m, R373, R344, R341, R338, entry] at hlt
  · omega

/-- ★★★★★★ シート証明中の行。 -/
theorem R600410_mem : R600 ++ [((4, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (by omega) Aok_R600 Ancd4_R600 (fun B hB => hang4_R600 hB)

#print axioms R600410_mem

/-! ### ★ `R600 (4,2,0)`

字は `one nil (two Tb60 nil)`:
`jk1 3 (two Tb60 nil) = (4,2,0)(5,2,0)(6,0,0)(4,2,0)`。
`Tb60` は予算 0 の族（`WPd_Tb60u`）なので兄弟に置ける。先端は `nil`。 -/

theorem WPd_twoTb60Nil (ks : List ℕ) : WPd (0 :: ks) (Jk1.two Tb60 Jk1.nil) :=
  WPd_twoOf (k := 0) JkA_Tb60
    (fun q _ => by
      have h := WPd_Tb60u (q ++ ks)
      simpa using h)
    (WPd_nilF 0 ks)

theorem GOK_oneTwoTb60Nil : GOK (Jk1.one Jk1.nil (Jk1.two Tb60 Jk1.nil)) :=
  (WPd_bnil _).mp (WPd_step [] (JkT_nil : FrmN [] Jk1.nil)
    ((WPd_bnil _).mpr GOK_nil) (WPd_twoTb60Nil []))

theorem jk1_oneTwoTb60Nil (l : ℕ) :
    jk1 l (Jk1.one Jk1.nil (Jk1.two Tb60 Jk1.nil))
      = [((l + 1, 1, 0) : ℕ × ℕ × ℕ), ((l + 2, 2, 0) : ℕ × ℕ × ℕ),
          ((l + 3, 2, 0) : ℕ × ℕ × ℕ), ((l + 4, 0, 0) : ℕ × ℕ × ℕ),
          ((l + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
  show jk1 l Jk1.nil ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
    (jk1 (l + 1) Tb60 ++ (((l + 1 + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1 + 1) Jk1.nil))) = _
  rw [jk1_Tb60 (l + 1), show l + 1 + 1 = l + 2 from by omega,
    show l + 1 + 2 = l + 3 from by omega, show l + 1 + 3 = l + 4 from by omega]
  simp [jk1]

/-- ★★★★★★ `R600 (4,2,0)`。 -/
theorem R600420_mem : R600 ++ [((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hG0 := GOK_oneTwoTb60Nil [] WOk_nil GoodFb_wordJ_nil
  have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (Jk1.two Tb60 Jk1.nil)]) := by
    simpa using hG0
  have hh := rowJ_mem_genF Aok_R338 hG
  rw [wordJ_singleton, colJ, jk1_oneTwoTb60Nil 2] at hh
  simpa [R600, R375m, R373, R344, R341, R338, List.append_assoc] using hh

#print axioms R600420_mem

/-! ### ★ `R600 (4,2,0)(5,2,0)^m` と `R600 (4,2,0)(5,0,0)`

`Tb60` は予算 0 の族なので `two Tb60 T` の兄弟に置ける。先端 `T` は
予算 `c+1` の族（`nil` / `pay nil Y` / 平らな走り `twoIt nil nil m`）。 -/

theorem WPd_twoTb60 {T : Jk1} (c : ℕ) (ks : List ℕ) (hT : WPd ((c + 1) :: ks) T) :
    WPd (0 :: ks) (Jk1.two Tb60 T) :=
  WPd_twoOf (k := c) JkA_Tb60
    (fun q _ => by
      have h := WPd_Tb60u (q ++ ks)
      simpa using h)
    hT

theorem jk1_oneTwoTb60 (l : ℕ) (T : Jk1) :
    jk1 l (Jk1.one Jk1.nil (Jk1.two Tb60 T))
      = [((l + 1, 1, 0) : ℕ × ℕ × ℕ), ((l + 2, 2, 0) : ℕ × ℕ × ℕ),
          ((l + 3, 2, 0) : ℕ × ℕ × ℕ), ((l + 4, 0, 0) : ℕ × ℕ × ℕ),
          ((l + 2, 2, 0) : ℕ × ℕ × ℕ)] ++ jk1 (l + 2) T := by
  show jk1 l Jk1.nil ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
    (jk1 (l + 1) Tb60 ++ (((l + 1 + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1 + 1) T))) = _
  rw [jk1_Tb60 (l + 1), show l + 1 + 1 = l + 2 from by omega,
    show l + 1 + 2 = l + 3 from by omega, show l + 1 + 3 = l + 4 from by omega]
  simp [jk1]

theorem R600_42_gen {T : Jk1} (c : ℕ) (hT : ∀ ks : List ℕ, WPd ((c + 1) :: ks) T) :
    R600 ++ (((4, 2, 0) : ℕ × ℕ × ℕ) :: jk1 4 T) ∈ W 0 := by
  have hGok : GOK (Jk1.one Jk1.nil (Jk1.two Tb60 T)) :=
    (WPd_bnil _).mp (WPd_step [] (JkT_nil : FrmN [] Jk1.nil)
      ((WPd_bnil _).mpr GOK_nil) (WPd_twoTb60 c [] (hT [])))
  have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (Jk1.two Tb60 T)]) := by
    simpa using hGok [] WOk_nil GoodFb_wordJ_nil
  have hh := rowJ_mem_genF Aok_R338 hG
  rw [wordJ_singleton, colJ, jk1_oneTwoTb60 2 T] at hh
  simpa [R600, R375m, R373, R344, R341, R338, List.append_assoc] using hh

/-- ★★★★★★ `R600 (4,2,0)(5,2,0)^m`（どの `m` でも）。 -/
theorem R600_42_run_mem (m : ℕ) :
    R600 ++ (((4, 2, 0) : ℕ × ℕ × ℕ) ::
      List.replicate m ((5, 2, 0) : ℕ × ℕ × ℕ)) ∈ W 0 := by
  have h := R600_42_gen (T := twoIt Jk1.nil Jk1.nil m) m
    (fun ks => WPd_twoIt_nil m m (le_refl m) ks)
  rwa [jk1_twoIt_nil m 4] at h

/-- ★★★★★★ `R600 (4,2,0)(5,0,0)`。 -/
theorem R600_42_50_mem :
    R600 ++ [((4, 2, 0) : ℕ × ℕ × ℕ), ((5, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := R600_42_gen (T := Jk1.pay Jk1.nil [((0, 0, 0) : ℕ × ℕ × ℕ)]) 0
    (fun ks => WPd_payA ((0 + 1) :: ks) Jk1.nil (trivial : FrmN ((0 + 1) :: ks) Jk1.nil)
      (WPd_nilAll _) _ Bok_zero)
  simpa [jk1, shiftr01] using h

#print axioms R600_42_run_mem
#print axioms R600_42_50_mem

/-! ### ★ `WPd_Tb60u` の兄弟を一般化: `two N M0t`

`M0t = two nil (pay nil [(0,0,0)])`、`Tb60 = two nil M0t`。
兄弟 `N` が**予算 0 の族**（`∀ks, WPd (0::ks) N`）なら `two N M0t` も予算 0 の族。
証明は `WPd_Tb60u` と同じ: 荷 `(0,0,0)` を `GoodFb_snoc_dupJt0` で展開すると
鎖は `twoIt nil (pay nil []) m`（空荷）で、語が平らな走りと同じ。
兄弟の側条件は「予算 0 の族」だけなので `hN` がそのまま効く。 -/

def M0t : Jk1 := Jk1.two Jk1.nil (Jk1.pay Jk1.nil [((0, 0, 0) : ℕ × ℕ × ℕ)])

theorem JkA_M0t : JkA M0t := ⟨trivial, trivial, Bok_zero⟩

theorem jk1_M0t (l : ℕ) :
    jk1 l M0t = [((l + 1, 2, 0) : ℕ × ℕ × ℕ), ((l + 2, 0, 0) : ℕ × ℕ × ℕ)] := by
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
    (jk1 (l + 1) Jk1.nil ++ shiftr01 (l + 1 + 1) 0 [((0, 0, 0) : ℕ × ℕ × ℕ)])) = _
  rw [show l + 1 + 1 = l + 2 from by omega]
  simp [jk1, shiftr01]

theorem WPd_twoM0 {N : Jk1} (hJN : JkA N) (hN : ∀ ks : List ℕ, WPd (0 :: ks) N) :
    ∀ ks : List ℕ, WPd (0 :: ks) (Jk1.two N M0t) := by
  intro ks
  rw [WPd_iff]
  intro ctx hc
  have eT : Jk1.two Jk1.nil (Jk1.pay Jk1.nil
      (([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])) = M0t := by simp [M0t]
  have hJT : JkT (plug (ctx ++ [Frm.ftwo N])
      (Jk1.two Jk1.nil (Jk1.pay Jk1.nil (([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))) := by
    rw [plug_snoc2, eT]
    exact WCtx_JkT (0 :: ks) ctx hc (Jk1.two N M0t)
      (⟨hJN, JkA_M0t⟩ : FrmN (0 :: ks) (Jk1.two N M0t))
  intro ws hw hG
  have hIH : ∀ m : ℕ, 1 ≤ m → GoodFb (fun a b => wordJ a b
      (ws ++ [plug (ctx ++ [Frm.ftwo N])
        (twoIt Jk1.nil (Jk1.pay Jk1.nil ([] : TrioSeq)) m)])) := by
    intro m _
    rw [plug_snoc2]
    have hw2 : WPd (0 :: ks)
        (Jk1.two N (twoIt Jk1.nil (Jk1.pay Jk1.nil ([] : TrioSeq)) m)) := by
      refine WPd_congr (0 :: ks) (fun l => ?_)
        (WPd_twoOf (k := m) hJN (fun q _ => by simpa using hN (q ++ ks))
          (WPd_twoIt_nil m m (le_refl m) ks))
      show jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
          jk1 (l + 1) (twoIt Jk1.nil Jk1.nil m))
        = jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
          jk1 (l + 1) (twoIt Jk1.nil (Jk1.pay Jk1.nil ([] : TrioSeq)) m))
      rw [jk1_twoIt_payNil m (l + 1)]
    exact (WPd_iff (0 :: ks) _).mp hw2 ctx hc ws hw hG
  have h := GoodFb_snoc_dupJt0 hw hJT hIH
  rw [plug_snoc2, eT] at h
  exact h

theorem JkA_twoItM0 : ∀ n : ℕ, JkA (twoIt Jk1.nil M0t n)
  | 0 => trivial
  | (n + 1) => ⟨JkA_twoItM0 n, JkA_M0t⟩

theorem WPd_twoItM0 : ∀ (n : ℕ) (ks : List ℕ), WPd (0 :: ks) (twoIt Jk1.nil M0t n)
  | 0, ks => WPd_nilT ks
  | (n + 1), ks =>
      WPd_twoM0 (JkA_twoItM0 n) (fun ks' => WPd_twoItM0 n ks') ks

def Blk420 : TrioSeq :=
  [((4, 2, 0) : ℕ × ℕ × ℕ), ((5, 2, 0) : ℕ × ℕ × ℕ), ((6, 0, 0) : ℕ × ℕ × ℕ)]

theorem jk1_twoItM0 : ∀ (n : ℕ),
    jk1 3 (twoIt Jk1.nil M0t n) = copies Blk420 n
  | 0 => rfl
  | (n + 1) => by
      show jk1 3 (twoIt Jk1.nil M0t n) ++
        (((3 + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (3 + 1) M0t) = _
      rw [jk1_twoItM0 n, jk1_M0t 4, copies_snoc]
      simp [Blk420]

theorem tw_R344_Blk420 (n : ℕ) : R344 ++ copies Blk420 n ∈ W 0 := by
  have hGok : GOK (Jk1.one Jk1.nil (twoIt Jk1.nil M0t n)) :=
    (WPd_bnil _).mp (WPd_step [] (JkT_nil : FrmN [] Jk1.nil)
      ((WPd_bnil _).mpr GOK_nil) (WPd_twoItM0 n []))
  have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (twoIt Jk1.nil M0t n)]) := by
    simpa using hGok [] WOk_nil GoodFb_wordJ_nil
  have hh := rowJ_mem_genF Aok_R338 hG
  have e : jk1 2 (Jk1.one Jk1.nil (twoIt Jk1.nil M0t n))
      = ((3, 1, 0) : ℕ × ℕ × ℕ) :: copies Blk420 n := by
    show jk1 2 Jk1.nil ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) ::
      jk1 (2 + 1) (twoIt Jk1.nil M0t n)) = _
    rw [jk1_twoItM0 n]
    simp [jk1]
  rw [wordJ_singleton, colJ, e] at hh
  simpa [R344, R341, R338, List.append_assoc] using hh

/-- ★★★★★★ `R600 (5,0,0)`（シート証明中）。 -/
theorem R600500_mem : R600 ++ [((5, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hne : Blk420 ≠ [] := by simp [Blk420]
  have hhead : entry Blk420 0 0 < 5 := by simp [Blk420, entry]
  have htail : ∀ r, 1 ≤ r → r < Blk420.length → 5 ≤ entry Blk420 0 r := by
    intro r hr1 hr2
    simp only [Blk420, List.length_cons, List.length_nil] at hr2
    rcases r with _ | _ | _ | r <;>
      first
        | omega
        | simp [Blk420, entry]
  have hmem := flat_mem'' (Y0 := R344) (M := Blk420) (d := 5) hne hhead htail
    (by intro n; simpa [copies] using tw_R344_Blk420 n)
  have e : R344 ++ Blk420 = R600 := by
    simp [R600, R375m, R373, R344, Blk420, List.append_assoc]
  rw [← e]
  simpa [List.append_assoc] using hmem

#print axioms WPd_twoM0
#print axioms R600500_mem

/-! ### ★ `R344 ++ Blk420^k ++ (4,2,0) ++ jk1 4 T` の一般形

兄弟に `twoIt nil M0t k`（予算 0 の族）、先端に予算 `c+1` の族 `T`。 -/

theorem R344_blk_gen (k : ℕ) {T : Jk1} (c : ℕ) (hT : ∀ ks : List ℕ, WPd ((c + 1) :: ks) T) :
    R344 ++ copies Blk420 k ++ (((4, 2, 0) : ℕ × ℕ × ℕ) :: jk1 4 T) ∈ W 0 := by
  have hGok : GOK (Jk1.one Jk1.nil (Jk1.two (twoIt Jk1.nil M0t k) T)) :=
    (WPd_bnil _).mp (WPd_step [] (JkT_nil : FrmN [] Jk1.nil)
      ((WPd_bnil _).mpr GOK_nil)
      (WPd_twoOf (k := c) (JkA_twoItM0 k)
        (fun q _ => by simpa using WPd_twoItM0 k q) (hT [])))
  have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (Jk1.two (twoIt Jk1.nil M0t k) T)]) := by
    simpa using hGok [] WOk_nil GoodFb_wordJ_nil
  have hh := rowJ_mem_genF Aok_R338 hG
  have e : jk1 2 (Jk1.one Jk1.nil (Jk1.two (twoIt Jk1.nil M0t k) T))
      = ((3, 1, 0) : ℕ × ℕ × ℕ) ::
        (copies Blk420 k ++ (((4, 2, 0) : ℕ × ℕ × ℕ) :: jk1 4 T)) := by
    show jk1 2 Jk1.nil ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (2 + 1) (twoIt Jk1.nil M0t k) ++
        (((2 + 1 + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (2 + 1 + 1) T))) = _
    rw [jk1_twoItM0 k]
    simp [jk1]
  rw [wordJ_singleton, colJ, e] at hh
  simpa [R344, R341, R338, List.append_assoc] using hh

/-- ★★★★★★ `R344 ++ Blk420^k ++ (4,2,0)(5,2,0)^m`（どの `k`, `m` でも）。 -/
theorem R344_blk_run_mem (k m : ℕ) :
    R344 ++ copies Blk420 k ++ (((4, 2, 0) : ℕ × ℕ × ℕ) ::
      List.replicate m ((5, 2, 0) : ℕ × ℕ × ℕ)) ∈ W 0 := by
  have h := R344_blk_gen k (T := twoIt Jk1.nil Jk1.nil m) m
    (fun ks => WPd_twoIt_nil m m (le_refl m) ks)
  rwa [jk1_twoIt_nil m 4] at h

#print axioms R344_blk_run_mem

/-! ### ★ `two N (pay M0t B)` の荷の W 帰納

底（`B = []`）は `WPd_twoM0`（緑）。`(0,0,0)` を足す段の鎖
`twoIt N (pay M0t Y) m` は、兄弟 `N` を全称した帰納法で回る
（`TwoOk_twoPayG` と同じ形だが、底がこちらは緑）。 -/

theorem WPd_twoPayNilM0 {N : Jk1} (hJN : JkA N) (hN : ∀ ks : List ℕ, WPd (0 :: ks) N)
    (ks : List ℕ) : WPd (0 :: ks) (Jk1.two N (Jk1.pay M0t ([] : TrioSeq))) := by
  refine WPd_congr (0 :: ks) (fun l => ?_) (WPd_twoM0 hJN hN ks)
  show jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M0t)
    = jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) (Jk1.pay M0t ([] : TrioSeq)))
  rw [jk1_pay_nil]

theorem WPd_chainM0 {N : Jk1} (hJN : JkA N) (hN : ∀ ks : List ℕ, WPd (0 :: ks) N)
    {Y : TrioSeq} (hYb : Bok Y)
    (hprev : ∀ N' : Jk1, JkA N' → (∀ ks' : List ℕ, WPd (0 :: ks') N') →
      ∀ ks' : List ℕ, WPd (0 :: ks') (Jk1.two N' (Jk1.pay M0t Y))) :
    ∀ m : ℕ, JkA (twoIt N (Jk1.pay M0t Y) m) ∧
      ∀ ks' : List ℕ, WPd (0 :: ks') (twoIt N (Jk1.pay M0t Y) m)
  | 0 => ⟨hJN, hN⟩
  | (m + 1) => by
      obtain ⟨h1, h2⟩ := WPd_chainM0 hJN hN hYb hprev m
      exact ⟨⟨h1, JkA_M0t, hYb⟩, hprev _ h1 h2⟩

theorem WPd_dupM0 {N : Jk1} (hJN : JkA N) (hN : ∀ ks : List ℕ, WPd (0 :: ks) N)
    {Y : TrioSeq} (hYb : Bok Y) (hY0 : Bok (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))
    (hprev : ∀ N' : Jk1, JkA N' → (∀ ks' : List ℕ, WPd (0 :: ks') N') →
      ∀ ks' : List ℕ, WPd (0 :: ks') (Jk1.two N' (Jk1.pay M0t Y)))
    (ks : List ℕ) :
    WPd (0 :: ks) (Jk1.two N (Jk1.pay M0t (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))) := by
  rw [WPd_iff]
  intro ctx hc
  have hJT : JkT (plug ctx (Jk1.two N (Jk1.pay M0t (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))) :=
    WCtx_JkT (0 :: ks) ctx hc _
      (⟨hJN, JkA_M0t, hY0⟩ :
        FrmN (0 :: ks) (Jk1.two N (Jk1.pay M0t (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))))
  intro ws hw hG
  refine GoodFb_snoc_dupJt0 hw hJT ?_
  intro m _
  exact (WPd_iff (0 :: ks) _).mp
    ((WPd_chainM0 hJN hN hYb hprev m).2 ks) ctx hc ws hw hG

theorem WPd_innerM0 {N : Jk1} (hJN : JkA N)
    {Y : TrioSeq} (hYb : Bok Y) (hlen : 2 ≤ Y.length)
    (hp : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1))
    (hIH : ∀ n : ℕ, 1 ≤ n → ∀ ks' : List ℕ,
      WPd (0 :: ks') (Jk1.two N (Jk1.pay M0t (Y⟦n⟧))))
    (ks : List ℕ) : WPd (0 :: ks) (Jk1.two N (Jk1.pay M0t Y)) := by
  rw [WPd_iff]
  intro ctx hc
  have hJT : JkT (plug ctx (Jk1.two N (Jk1.pay M0t Y))) :=
    WCtx_JkT (0 :: ks) ctx hc _
      (⟨hJN, JkA_M0t, hYb⟩ : FrmN (0 :: ks) (Jk1.two N (Jk1.pay M0t Y)))
  intro ws hw hG
  refine GoodFb_snoc_innerJt0 hw hJT hlen hp ?_
  intro n hn
  exact (WPd_iff (0 :: ks) _).mp (hIH n hn ks) ctx hc ws hw hG

/-- ★★★★★★ `two N (pay M0t B)` はどの `Bok B` でも予算 0 の族。 -/
theorem WPd_twoPayM0 : ∀ (B : TrioSeq), Bok B → ∀ N : Jk1, JkA N →
    (∀ ks : List ℕ, WPd (0 :: ks) N) →
    ∀ ks : List ℕ, WPd (0 :: ks) (Jk1.two N (Jk1.pay M0t B)) := by
  have key : W 0 ⊆ {B : TrioSeq | Bok B → ∀ N : Jk1, JkA N →
      (∀ ks : List ℕ, WPd (0 :: ks) N) →
      ∀ ks : List ℕ, WPd (0 :: ks) (Jk1.two N (Jk1.pay M0t B))} := by
    refine A2' ?_
    intro B hB
    simp only [Set.mem_setOf_eq]
    intro hBb N hJN hN ks
    by_cases hshort : B.length ≤ 1
    · rcases (by omega : B.length = 0 ∨ B.length = 1) with h0 | h1
      · have hnil0 : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil0
        exact WPd_twoPayNilM0 hJN hN ks
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hBb.root
        obtain ⟨hc1, hc2⟩ := hBb.zroot c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have e : ([((0, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
            = ([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by simp
        rw [e]
        exact WPd_dupM0 hJN hN Bok_nil (by rw [← e]; exact hBb)
          (fun N' hJN' hN' ks' => WPd_twoPayNilM0 hJN' hN' ks') ks
    · have hlen2 : 2 ≤ B.length := by omega
      have hBne : B ≠ [] := by intro hcc; rw [hcc] at hlen2; simp at hlen2
      rcases hB with ⟨hl, -⟩ | hnat | ⟨mm, hm, -, -⟩
      · exact absurd hl hshort
      · by_cases hlast : entry B 0 (B.length - 1) = 0
        · obtain ⟨he1, he2⟩ := Zroot_entry hBb.zroot hlast
          have hcol : B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ)
              = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hlast (Prod.ext he1 he2)
          have hgl : B.getLast hBne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            have h1 : B.getLast hBne = B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
              rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem (show B.length - 1 < B.length by omega)]
              rfl
            rw [h1, hcol]
          have hsplit : B = B.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
            rw [← hgl]; exact (List.dropLast_append_getLast hBne).symm
          have hop : B⟦1⟧ = B.dropLast := by
            rw [oper_eq_pred_of_zero 1 (by omega) ⟨hlast, he1, he2⟩]
            unfold Pred
            rw [if_neg (by omega)]
          have hdl := hnat 1 le_rfl
          rw [hop] at hdl
          simp only [Set.mem_setOf_eq] at hdl
          have hdb : Bok B.dropLast := Bok_dropLast hBb
          rw [hsplit]
          exact WPd_dupM0 hJN hN hdb (by rw [← hsplit]; exact hBb)
            (fun N' hJN' hN' ks' => hdl hdb N' hJN' hN' ks') ks
        · have hnz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
              entry B 2 (B.length - 1) = 0) := fun h => hlast h.1
          have hp := hasParent_of_ZrootMono hBb.zroot hBb.mono hBb.root hlen2 hnz
          refine WPd_innerM0 hJN hBb hlen2 hp ?_ ks
          intro n hn ks'
          have hh := hnat n hn
          simp only [Set.mem_setOf_eq] at hh
          exact hh (Bok_oper hBb hn) N hJN hN ks'
      · exact absurd hm (Nat.not_lt_zero mm)
  intro B hBb N hJN hN ks
  exact key hBb.mem hBb N hJN hN ks

#print axioms WPd_twoPayM0

/-! ### ★ `R600 (5,1,0)`（シート証明中）

高さ 5 の吊るしの字は `one nil (two nil (pay M0t B))`:
`jk1 l = (l+1,1,0)(l+2,2,0)(l+3,2,0)(l+4,0,0) ++ B↑(l+3)`。
`WPd_twoPayM0` から予算 0 で出るので、荷 `B` はどの `Bok B` でも良い。 -/

theorem jk1_hang5M0 (l : ℕ) (B : TrioSeq) :
    jk1 l (Jk1.one Jk1.nil (Jk1.two Jk1.nil (Jk1.pay M0t B)))
      = [((l + 1, 1, 0) : ℕ × ℕ × ℕ), ((l + 2, 2, 0) : ℕ × ℕ × ℕ),
          ((l + 3, 2, 0) : ℕ × ℕ × ℕ), ((l + 4, 0, 0) : ℕ × ℕ × ℕ)]
        ++ shiftr01 (l + 3) 0 B := by
  show jk1 l Jk1.nil ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
    (jk1 (l + 1) Jk1.nil ++ (((l + 1 + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1 + 1) M0t ++ shiftr01 (l + 1 + 1 + 1) 0 B)))) = _
  rw [show l + 1 + 1 = l + 2 from by omega, jk1_M0t (l + 2),
    show l + 2 + 1 = l + 3 from by omega, show l + 2 + 2 = l + 4 from by omega]
  simp [jk1]

theorem hang5_R600 {B : TrioSeq} (hB : Bok B) : R600 ++ shiftr01 5 0 B ∈ W 0 := by
  have hGok : GOK (Jk1.one Jk1.nil (Jk1.two Jk1.nil (Jk1.pay M0t B))) :=
    (WPd_bnil _).mp (WPd_step [] (JkT_nil : FrmN [] Jk1.nil)
      ((WPd_bnil _).mpr GOK_nil)
      (WPd_twoPayM0 B hB Jk1.nil trivial (fun ks => WPd_nilT ks) []))
  have hG : GoodFb (fun a b =>
      wordJ a b [Jk1.one Jk1.nil (Jk1.two Jk1.nil (Jk1.pay M0t B))]) := by
    simpa using hGok [] WOk_nil GoodFb_wordJ_nil
  have hh := rowJ_mem_genF Aok_R338 hG
  rw [wordJ_singleton, colJ, jk1_hang5M0 2 B] at hh
  simpa [R600, R375m, R373, R344, R341, R338, List.append_assoc] using hh

theorem Ancd_R600 (d : ℕ) (hd : d ≤ 6) : Ancd d R600 := by
  intro j hj0 hjl hlt hmin
  have hlen : R600.length = 9 := by
    simp [R600, R375m, R373, R344, R341, R338]
  rw [hlen] at hjl
  have h3 : (3 : ℕ) < R600.length := by rw [hlen]; omega
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · omega
  · exact absurd (hmin 3 (by omega) h3)
      (by simp [R600, R375m, R373, R344, R341, R338, entry])
  · exact absurd (hmin 3 (by omega) h3)
      (by simp [R600, R375m, R373, R344, R341, R338, entry])
  · simp [R600, R375m, R373, R344, R341, R338, entry]
  · simp [R600, R375m, R373, R344, R341, R338, entry]
  · simp [R600, R375m, R373, R344, R341, R338, entry]
  · simp [R600, R375m, R373, R344, R341, R338, entry]
  · simp [R600, R375m, R373, R344, R341, R338, entry]
  · simp [R600, R375m, R373, R344, R341, R338, entry] at hlt
    omega
  · omega

/-- ★★★★★★ `R600 (5,1,0)`。 -/
theorem R600510_mem : R600 ++ [((5, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (by omega) Aok_R600 (Ancd_R600 5 (by omega)) (fun B hB => hang5_R600 hB)

#print axioms R600510_mem

/-! ### `R600 (5,1,0)` の上（`Aok` からの継ぎ足し） -/

theorem Aok_R600510 : Aok (R600 ++ [((5, 1, 0) : ℕ × ℕ × ℕ)]) :=
  Aok_append_Mid (d := 6) (by omega) Aok_R600 (MidD_one 5 (by omega)) R600510_mem

theorem R600510_110_mem :
    (R600 ++ [((5, 1, 0) : ℕ × ℕ × ℕ)]) ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa using Lv_snoc 1 0 _ (Aok_R600510 : Lv 1 0 (R600 ++ [((5, 1, 0) : ℕ × ℕ × ℕ)]))

theorem R600510_1122_mem :
    (R600 ++ [((5, 1, 0) : ℕ × ℕ × ℕ)])
      ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa using Lv_snoc2 1 0 _ (Aok_R600510 : Lv 1 0 (R600 ++ [((5, 1, 0) : ℕ × ℕ × ℕ)]))

#print axioms R600510_1122_mem

/-! ### ★ `R600 (5,1,0)` の上に `RunA` の機構をまるごと乗せる

`Aok_R600510` から `LwA_of_Aok` → `LwA_U11` で `RunA 0 1` が出るので、
`RunG_snoc2` / `PkGA` / `LadB`（junk の語・梯子）が全部使える。 -/

def X510 : TrioSeq := R600 ++ [((5, 1, 0) : ℕ × ℕ × ℕ)]

def Y510 (m : ℕ) : TrioSeq := X510 ++ U11 0 m

theorem Y510_RunA0 (m : ℕ) : RunA 0 1 (Y510 m) :=
  LwA_U11 (LwA_of_Aok Aok_R600510) m

theorem Aok_Y510 (m : ℕ) : Aok (Y510 m) := (BaseOk_RunA 0).aok _ _ (Y510_RunA0 m)

theorem Y510_mem (m : ℕ) : Y510 m ∈ W 0 := (Aok_Y510 m).mem

/-- ★★★★★★ `R600 (5,1,0)(1,1,0)(2,2,1)^m (2,2,0)`。 -/
theorem Y510_220_mem (m : ℕ) : Y510 m ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunG_snoc2 Iface_RunA0 0 1 (Y510 m) (Y510_RunA0 m)

def Y510j (m : ℕ) (ws : List Jk1) : TrioSeq :=
  Y510 m ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ wordJ 2 2 ws)

theorem Y510j_PkGA (m : ℕ) {ws : List Jk1} (hw : WJ ws) : PkGA 2 (Y510j m ws) :=
  ⟨RunA 0, Iface_RunA0, 0, 1, Y510 m, wordJ 2 2 ws, rfl, Y510_RunA0 m, rfl,
    (GoodFb_wordJ ws hw).pk 1⟩

/-- ★★★★★★ その上に junk の語（どの `WJ ws` でも）。 -/
theorem Y510j_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) : Y510j m ws ∈ W 0 :=
  (PkGA_Aok (Y510j_PkGA m hw)).mem

/-- ★★★★★★ さらにその上に `PU` の梯子。 -/
theorem Y510Lad_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (n : ℕ) :
    LadB (Y510j m ws) n ∈ W 0 := LadB_mem (Y510j_PkGA m hw) n

#print axioms Y510_220_mem
#print axioms Y510j_mem
#print axioms Y510Lad_mem

/-! ### ★ 一般形: `Aok` を取るたびに `RunA` の機構が乗る（反復できる）

`Aok A → Aok (A ++ U11 0 m)` と `Aok A → Aok (A ++ U11 0 m ++ (2,2,0) ++ wordJ 2 2 ws)`。
後者を反復すると 2 パラメータの無限族になる。 -/

theorem Aok_addU11 {A : TrioSeq} (hA : Aok A) (m : ℕ) : Aok (A ++ U11 0 m) :=
  (BaseOk_RunA 0).aok _ _ (LwA_U11 (LwA_of_Aok hA) m)

theorem Aok_junk {A : TrioSeq} (hA : Aok A) (m : ℕ) {ws : List Jk1} (hw : WJ ws) :
    Aok ((A ++ U11 0 m) ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ wordJ 2 2 ws)) :=
  PkGA_Aok ⟨RunA 0, Iface_RunA0, 0, 1, A ++ U11 0 m, wordJ 2 2 ws, rfl,
    LwA_U11 (LwA_of_Aok hA) m, rfl, (GoodFb_wordJ ws hw).pk 1⟩

/-- 1 段 = `(1,1,0)(2,2,1)^m(2,2,0)(3,3,1)`。 -/
def UJit (A : TrioSeq) (m : ℕ) : ℕ → TrioSeq
  | 0 => A
  | (n + 1) => (UJit A m n ++ U11 0 m)
      ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ wordJ 2 2 [Jk1.nil])

theorem Aok_UJit {A : TrioSeq} (hA : Aok A) (m : ℕ) : ∀ n : ℕ, Aok (UJit A m n)
  | 0 => hA
  | (n + 1) => Aok_junk (Aok_UJit hA m n) m (WJ_singleton JkOk_nil)

/-- ★★★★★★ `R600 (5,1,0)` の上の 2 パラメータの無限族。 -/
theorem UJit_X510_mem (m n : ℕ) : UJit X510 m n ∈ W 0 :=
  (Aok_UJit Aok_R600510 m n).mem

#print axioms UJit_X510_mem

/-! ### ★ junk の語を一般化（`WJ ws` なら何でも） -/

def UJitW (A : TrioSeq) (m : ℕ) (ws : List Jk1) : ℕ → TrioSeq
  | 0 => A
  | (n + 1) => (UJitW A m ws n ++ U11 0 m) ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ wordJ 2 2 ws)

theorem Aok_UJitW {A : TrioSeq} (hA : Aok A) (m : ℕ) {ws : List Jk1} (hw : WJ ws) :
    ∀ n : ℕ, Aok (UJitW A m ws n)
  | 0 => hA
  | (n + 1) => Aok_junk (Aok_UJitW hA m hw n) m hw

/-- ★★★★★★ `R600 (5,1,0)` の上の 4 パラメータの無限族。 -/
theorem UJitW_X510_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (n : ℕ) :
    UJitW X510 m ws n ∈ W 0 := (Aok_UJitW Aok_R600510 m hw n).mem

theorem UJitW_alt_mem (m i p n : ℕ) :
    UJitW X510 m (List.replicate p (AltT i)) n ∈ W 0 :=
  UJitW_X510_mem m (WJ_rep_AltT i p) n

theorem Y510alt_mem (m i p : ℕ) : Y510j m (List.replicate p (AltT i)) ∈ W 0 :=
  Y510j_mem m (WJ_rep_AltT i p)

theorem Y510altLad_mem (m i p n : ℕ) :
    LadB (Y510j m (List.replicate p (AltT i))) n ∈ W 0 :=
  Y510Lad_mem m (WJ_rep_AltT i p) n

#print axioms UJitW_alt_mem
#print axioms Y510altLad_mem

/-! ### ★ `APd` 層でも「兄弟の側は自由」: `FLr Bs` は良い兄弟

`WPd_FLr`（`WPd` 層）の `APd` 版。`TwoOk (pay nil B)`（緑）を
兄弟について帰納すればそのまま出る。**先端**に置くのが壁であって、
**兄弟**に置くのは荷つきの走りでも自由、というのがはっきりする。 -/

theorem APd_FLr : ∀ (Bs : List TrioSeq), (∀ C ∈ Bs, Bok C) →
    ∀ (j : ℕ) (kk : List Bool), APd (List.replicate j true ++ (true :: kk)) (FLr Bs)
  | [], _, j, kk => APd_nil _
  | (B :: Bs), h, j, kk => by
      have hsub : ∀ C ∈ Bs, Bok C := fun C hC => h C (List.mem_cons_of_mem B hC)
      have hpay : TwoOk (Jk1.pay Jk1.nil B) :=
        TwoOk_pay B (h B List.mem_cons_self) Jk1.nil trivial TwoOk_nil
      exact hpay (FLr Bs) (JkA_FLr Bs hsub) (fun j' kk' => APd_FLr Bs hsub j' kk') j kk

theorem GOK_oneFLr (Bs : List TrioSeq) (h : ∀ C ∈ Bs, Bok C) :
    GOK (Jk1.one Jk1.nil (FLr Bs)) :=
  (APd_bnil _).mp (APd_step [] (JkT_nil : FrmJ [] Jk1.nil) trivial
    ((APd_bnil _).mpr GOK_nil) (by simpa using APd_FLr Bs h 0 []))

#print axioms APd_FLr
#print axioms GOK_oneFLr

theorem Y510Lad_flat_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (n : ℕ) :
    LadB (Y510j m ws) n ++ [((n + 4, n + 4, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  LadB_flat_mem (Y510j_PkGA m hw) n

theorem UJitLad_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (n j : ℕ) :
    LadB ((UJitW X510 m ws n ++ U11 0 m)
      ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ wordJ 2 2 ws)) j ∈ W 0 :=
  LadB_mem ⟨RunA 0, Iface_RunA0, 0, 1, UJitW X510 m ws n ++ U11 0 m, wordJ 2 2 ws, rfl,
    LwA_U11 (LwA_of_Aok (Aok_UJitW Aok_R600510 m hw n)) m, rfl,
    (GoodFb_wordJ ws hw).pk 1⟩ j

#print axioms Y510Lad_flat_mem
#print axioms UJitLad_mem

/-- 梯子＋平らな段も `Aok`。ここからまた `Aok` の機構が乗る。 -/
theorem Aok_Y510Ladf (m : ℕ) {ws : List Jk1} (hw : WJ ws) (n : ℕ) :
    Aok (LadB (Y510j m ws) n ++ [((n + 4, n + 4, 0) : ℕ × ℕ × ℕ)]) :=
  (BaseOk_PU (n + 3)).aok _ _ (LadB_flat_PU (Y510j_PkGA m hw) n)

/-- ★★★★★★ 梯子＋平らな段の上に、また `U11` と junk の語。 -/
theorem Y510Ladf_UJ_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (n m' : ℕ)
    {ws' : List Jk1} (hw' : WJ ws') (j : ℕ) :
    UJitW (LadB (Y510j m ws) n ++ [((n + 4, n + 4, 0) : ℕ × ℕ × ℕ)]) m' ws' j ∈ W 0 :=
  (Aok_UJitW (Aok_Y510Ladf m hw n) m' hw' j).mem

#print axioms Aok_Y510Ladf
#print axioms Y510Ladf_UJ_mem

/-! ### ★ `Aok` の輪を 1 つの演算子に: `Loop` と `LoopIt`

1 周 = `U11 0 m`（`(1,1,0)(2,2,1)^m`）+ `(2,2,0)` + junk の語 `wordJ 2 2 ws`
     + `PU` の梯子 `LadB ... j` + 平らな段 `(j+4,j+4,0)`。
結論がまた `Aok` なので何周でも回せる。 -/

def Loop (A : TrioSeq) (m : ℕ) (ws : List Jk1) (j : ℕ) : TrioSeq :=
  LadB ((A ++ U11 0 m) ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ wordJ 2 2 ws)) j
    ++ [((j + 4, j + 4, 0) : ℕ × ℕ × ℕ)]

theorem PkGA_Loopbase {A : TrioSeq} (hA : Aok A) (m : ℕ) {ws : List Jk1} (hw : WJ ws) :
    PkGA 2 ((A ++ U11 0 m) ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ wordJ 2 2 ws)) :=
  ⟨RunA 0, Iface_RunA0, 0, 1, A ++ U11 0 m, wordJ 2 2 ws, rfl,
    LwA_U11 (LwA_of_Aok hA) m, rfl, (GoodFb_wordJ ws hw).pk 1⟩

theorem Aok_Loop {A : TrioSeq} (hA : Aok A) (m : ℕ) {ws : List Jk1} (hw : WJ ws) (j : ℕ) :
    Aok (Loop A m ws j) :=
  (BaseOk_PU (j + 3)).aok _ _ (LadB_flat_PU (PkGA_Loopbase hA m hw) j)

def LoopIt (A : TrioSeq) (m : ℕ) (ws : List Jk1) (j : ℕ) : ℕ → TrioSeq
  | 0 => A
  | (n + 1) => Loop (LoopIt A m ws j n) m ws j

theorem Aok_LoopIt {A : TrioSeq} (hA : Aok A) (m : ℕ) {ws : List Jk1} (hw : WJ ws) (j : ℕ) :
    ∀ n : ℕ, Aok (LoopIt A m ws j n)
  | 0 => hA
  | (n + 1) => Aok_Loop (Aok_LoopIt hA m hw j n) m hw j

/-- ★★★★★★ `R600 (5,1,0)` の上、輪を `n` 周した 4 パラメータの無限族。 -/
theorem LoopIt_X510_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (j n : ℕ) :
    LoopIt X510 m ws j n ∈ W 0 := (Aok_LoopIt Aok_R600510 m hw j n).mem

theorem LoopIt_X510_nil_mem (m p j n : ℕ) :
    LoopIt X510 m (List.replicate p (AltT 0)) j n ∈ W 0 :=
  LoopIt_X510_mem m (WJ_rep_AltT 0 p) j n

#print axioms Aok_Loop
#print axioms LoopIt_X510_nil_mem

/-! ### ★ `RHang` の底（`C = []`）を仮定から外す: `RHang2`

`RNil_of_RHang` の `step` は `hG : GOK (plug D (stk j))` を `RCx.step` から
**もらっている**。だから `RHang` の側にも `hG` を仮定として入れてよい。
すると `C = []` の場合（`stkP j (pay nil []) ≡ stk j`）が仮定そのものになり、
荷の W 帰納の**底が消える**。 -/

theorem jk1_stkP_pay_nil : ∀ (j l : ℕ),
    jk1 l (stkP j (Jk1.pay Jk1.nil ([] : TrioSeq))) = jk1 l (stk j)
  | 0, l => by
      show jk1 l (Jk1.pay Jk1.nil ([] : TrioSeq)) = jk1 l Jk1.nil
      rw [jk1_pay_nil]
  | (j + 1), l => by
      show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
          jk1 (l + 1) (stkP j (Jk1.pay Jk1.nil ([] : TrioSeq))))
        = jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) (stkP j Jk1.nil))
      rw [jk1_stkP_pay_nil j (l + 1)]
      rfl

/-- `C = []` の場合は `hG` そのもの。 -/
theorem RHang2_nil {D : List Frm} {j : ℕ} (hG : GOK (plug D (stk j))) :
    GOK (plug D (stkP j (Jk1.pay Jk1.nil ([] : TrioSeq)))) :=
  GOK_congr (jk1_plug_congr D (fun l => (jk1_stkP_pay_nil j l).symm)) hG

def RHang2 : Prop := ∀ (D : List Frm) (j : ℕ) (C : TrioSeq), RCx D →
    GOK (plug D (stk j)) → Bok C → GOK (plug D (stkP j (Jk1.pay Jk1.nil C)))

theorem RHang2_of_RHang (h : RHang) : RHang2 := fun D j C hD _ hC => h D j C hD hC

theorem RNil_of_RHang2 (h : RHang2) : RNil := by
  intro D hD
  induction hD with
  | @base ks ctx hc => exact RNil_base hc
  | @step D j hD hG _ =>
      rw [plug_stkP_one, plug_stkP_gen]
      refine APnil_gen0 (D ++ List.replicate j (Frm.ftwo Jk1.nil)) Jk1.nil
        (CtxJT_repF (RCx_CtxJT hD) j _ ⟨trivial, trivial⟩) ?_ ?_
      · rw [← plug_stkP_gen]; exact hG
      · intro C hC
        rw [← plug_stkP_gen]
        exact h D j C hD hG hC

/-- ★★★★★★ 目標行376 は `RHang2` 1 文から出る（`RHang` より真に弱い）。 -/
theorem R376_of_RHang2 (h : RHang2) : R373 ++ [((5, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  R376_of_RNil (RNil_of_RHang2 h)

#print axioms RHang2_nil
#print axioms R376_of_RHang2

/-! ### ★ 予算の型を一般化する

壁 `WPd ((k+1)::ks) M0t` は「兄弟 `N` の予算が `≤ k` までしか無い」のが原因。
予算を「整礎な全順序 `Bud`」にして、自然数の段 `nb 0 < nb 1 < ...` の上に
予算 `t` を置くと、`t` の節では兄弟が全ての `nb m` の予算で来るので、
幅に上限の無い鎖が作れる。DM 順序は `Bud` が整礎なら整礎のまま。 -/

/-- 予算の「ω 段」。`nb : ℕ → Bud` は下から `⊥` で始まる真に増える列。 -/
structure Scale (B : Type) [Preorder B] [OrderBot B] where
  nb : ℕ → B
  nbmono : StrictMono nb

section Bud

variable {Bud : Type} [LinearOrder Bud] [OrderBot Bud] [WellFoundedLT Bud]


theorem dmT_step {b : Bud} {X Y : Multiset Bud} (h : ∀ y ∈ Y, y < b) :
    Multiset.IsDershowitzMannaLT (X + Y) (b ::ₘ X) := by
  refine ⟨X, Y, {b}, by simp, rfl, ?_, ?_⟩
  · rw [← Multiset.singleton_add, add_comm]
  · intro y hy
    exact ⟨b, by simp, h y hy⟩

theorem dmT_cons (b : Bud) (ks : List Bud) :
    Multiset.IsDershowitzMannaLT ((ks : List Bud) : Multiset Bud)
      ((b :: ks : List Bud) : Multiset Bud) := by
  simpa using dmT_step (b := b) (X := ((ks : List Bud) : Multiset Bud))
    (Y := 0) (by simp)

theorem dmT_app {b : Bud} (ks a : List Bud) (h : ∀ x ∈ a, x < b) :
    Multiset.IsDershowitzMannaLT ((a ++ ks : List Bud) : Multiset Bud)
      ((b :: ks : List Bud) : Multiset Bud) := by
  have e : ((a ++ ks : List Bud) : Multiset Bud)
      = ((ks : List Bud) : Multiset Bud)
        + ((a : List Bud) : Multiset Bud) := by
    rw [← Multiset.coe_add]
    exact Multiset.coe_eq_coe.mpr List.perm_append_comm
  rw [e]
  exact dmT_step (b := b) (X := ((ks : List Bud) : Multiset Bud))
    (Y := ((a : List Bud) : Multiset Bud))
    (fun y hy => h y (by simpa using hy))

#print axioms dmT_app

def FrmNT : List Bud → Jk1 → Prop
  | [], U => JkT U
  | (_ :: _), U => JkA U

/-- `WPd` の予算を `Bud` にしたもの。`⊥` が 1 の枠、`⊥ < b` が 2 の枠で、
兄弟は「予算 `< b`」。`b = ⊤` の節では兄弟が**全ての自然数の予算**で来る。 -/
def WPdT {Bud : Type} [LinearOrder Bud] [OrderBot Bud] [WellFoundedLT Bud] :
    List Bud → Jk1 → Prop
  | [], V => GOK V
  | (b :: ks), V =>
      (b = ⊥ → ∀ U : Jk1, FrmNT ks U → WPdT ks U → WPdT ks (Jk1.one U V)) ∧
      (b ≠ ⊥ → ∀ (r : List Bud), (∀ x ∈ r, x < b) → ∀ (U N : Jk1),
        FrmNT (r ++ ks) U → WPdT (r ++ ks) U → JkA N →
        (∀ q : List Bud, (∀ x ∈ q, x < b) →
          WPdT ((⊥ : Bud) :: q ++ (r ++ ks)) N) →
        WPdT (r ++ ks) (Jk1.one U (Jk1.two N V)))
termination_by ks _ => ((ks : List Bud) : Multiset Bud)
decreasing_by
  all_goals
    first
      | exact dmT_cons _ _
      | exact dmT_app ks _ (by assumption)
      | (rw [show (⊥ : Bud) :: q ++ (r ++ ks)
              = ((⊥ : Bud) :: (q ++ r)) ++ ks from by simp]
         refine dmT_app ks ((⊥ : Bud) :: (q ++ r)) ?_
         intro x hx
         simp only [List.mem_cons, List.mem_append] at hx
         rcases hx with h1 | h1 | h1
         · subst h1
           exact Ne.bot_lt' (Ne.symm (by assumption))
         · exact (by assumption : ∀ x ∈ q, x < b) x h1
         · exact (by assumption : ∀ x ∈ r, x < b) x h1)

#print axioms WPdT

theorem WPdT_bnil (V : Jk1) : WPdT ([] : List Bud) V ↔ GOK V := by rw [WPdT]

theorem WPdT_cons (b : Bud) (ks : List Bud) (V : Jk1) :
    WPdT (b :: ks) V ↔
      (b = ⊥ → ∀ U : Jk1, FrmNT ks U → WPdT ks U → WPdT ks (Jk1.one U V)) ∧
      (b ≠ ⊥ → ∀ (r : List Bud), (∀ x ∈ r, x < b) → ∀ (U N : Jk1),
        FrmNT (r ++ ks) U → WPdT (r ++ ks) U → JkA N →
        (∀ q : List Bud, (∀ x ∈ q, x < b) →
          WPdT ((⊥ : Bud) :: q ++ (r ++ ks)) N) →
        WPdT (r ++ ks) (Jk1.one U (Jk1.two N V))) := by
  rw [WPdT]

/-- `⊥` の節（1 の枠）。 -/
theorem WPdT_c0 (ks : List Bud) (V : Jk1) :
    WPdT ((⊥ : Bud) :: ks) V ↔
      ∀ U : Jk1, FrmNT ks U → WPdT ks U → WPdT ks (Jk1.one U V) := by
  rw [WPdT_cons]
  constructor
  · exact fun h => h.1 rfl
  · exact fun h => ⟨fun _ => h, fun hne => absurd rfl hne⟩

/-- `b ≠ ⊥` の節（2 の枠）。 -/
theorem WPdT_cb {b : Bud} (hb : b ≠ ⊥) (ks : List Bud) (V : Jk1) :
    WPdT (b :: ks) V ↔
      ∀ (r : List Bud), (∀ x ∈ r, x < b) → ∀ (U N : Jk1),
        FrmNT (r ++ ks) U → WPdT (r ++ ks) U → JkA N →
        (∀ q : List Bud, (∀ x ∈ q, x < b) →
          WPdT ((⊥ : Bud) :: q ++ (r ++ ks)) N) →
        WPdT (r ++ ks) (Jk1.one U (Jk1.two N V)) := by
  rw [WPdT_cons]
  constructor
  · exact fun h => h.2 hb
  · exact fun h => ⟨fun he => absurd he hb, fun _ => h⟩

/-- `⊥` の節から `one` を継ぐ（`WPd_step` の `WPdT` 版）。 -/
theorem WPdT_step (ks : List Bud) {V W : Jk1} (hV : FrmNT ks V) (hVk : WPdT ks V)
    (hW : WPdT ((⊥ : Bud) :: ks) W) : WPdT ks (Jk1.one V W) :=
  (WPdT_c0 ks W).mp hW V hV hVk

/-- `2 の枠`（`WPd_twoOf` の `WPdT` 版）。予算 `b` は自由に選べる。 -/
theorem WPdT_twoOf {b : Bud} (hb : b ≠ ⊥) {ks : List Bud} {V N : Jk1}
    (hJN : JkA N)
    (hNt : ∀ q : List Bud, (∀ x ∈ q, x < b) →
      WPdT ((⊥ : Bud) :: q ++ ks) N)
    (hV : WPdT (b :: ks) V) : WPdT ((⊥ : Bud) :: ks) (Jk1.two N V) :=
  (WPdT_c0 ks _).mpr (fun U hU hUk => by
    have h := (WPdT_cb hb ks V).mp hV [] (by simp) U N (by simpa using hU)
      (by simpa using hUk) hJN (fun q hq => by simpa using hNt q hq)
    simpa using h)

#print axioms WPdT_twoOf

def WCtxU {Bud : Type} [LinearOrder Bud] [OrderBot Bud] [WellFoundedLT Bud] :
    List Bud → List Frm → Prop
  | [], ctx => ctx = []
  | (b :: ks), ctx =>
      (b = ⊥ → ∃ (ctx' : List Frm) (U : Jk1), ctx = ctx' ++ [Frm.fone U] ∧
        WCtxU ks ctx' ∧ FrmNT ks U ∧ WPdT ks U) ∧
      (b ≠ ⊥ → ∃ (r : List Bud) (_ : ∀ x ∈ r, x < b)
        (ctx' : List Frm) (U N : Jk1),
        ctx = ctx' ++ [Frm.fone U, Frm.ftwo N] ∧
        WCtxU (r ++ ks) ctx' ∧
        FrmNT (r ++ ks) U ∧ WPdT (r ++ ks) U ∧ JkA N ∧
        (∀ q : List Bud, (∀ x ∈ q, x < b) →
          WPdT ((⊥ : Bud) :: q ++ (r ++ ks)) N))
termination_by ks _ => ((ks : List Bud) : Multiset Bud)
decreasing_by
  all_goals
    first
      | exact dmT_cons _ _
      | exact dmT_app ks _ (by assumption)

theorem WCtxU_bnil (ctx : List Frm) : WCtxU ([] : List Bud) ctx ↔ ctx = [] := by
  rw [WCtxU]

theorem WCtxU_c0 (ks : List Bud) (ctx : List Frm) :
    WCtxU ((⊥ : Bud) :: ks) ctx ↔ ∃ (ctx' : List Frm) (U : Jk1),
      ctx = ctx' ++ [Frm.fone U] ∧ WCtxU ks ctx' ∧ FrmNT ks U ∧ WPdT ks U := by
  rw [WCtxU]
  constructor
  · exact fun h => h.1 rfl
  · exact fun h => ⟨fun _ => h, fun hne => absurd rfl hne⟩

theorem WCtxU_cb {b : Bud} (hb : b ≠ ⊥) (ks : List Bud) (ctx : List Frm) :
    WCtxU (b :: ks) ctx ↔ ∃ (r : List Bud) (_ : ∀ x ∈ r, x < b)
      (ctx' : List Frm) (U N : Jk1),
      ctx = ctx' ++ [Frm.fone U, Frm.ftwo N] ∧
      WCtxU (r ++ ks) ctx' ∧
      FrmNT (r ++ ks) U ∧ WPdT (r ++ ks) U ∧ JkA N ∧
      (∀ q : List Bud, (∀ x ∈ q, x < b) →
        WPdT ((⊥ : Bud) :: q ++ (r ++ ks)) N) := by
  rw [WCtxU]
  constructor
  · exact fun h => h.2 hb
  · exact fun h => ⟨fun he => absurd he hb, fun _ => h⟩

theorem WPdT_iff : ∀ (ks : List Bud) (V : Jk1),
    WPdT ks V ↔ ∀ ctx : List Frm, WCtxU ks ctx → GOK (plug ctx V)
  | [], V => by
      rw [WPdT_bnil]
      constructor
      · intro h ctx hc
        rw [WCtxU_bnil] at hc
        subst hc
        exact h
      · intro h
        exact h [] ((WCtxU_bnil []).mpr rfl)
  | (b :: ks), V => by
      by_cases hb : b = ⊥
      · subst hb
        rw [WPdT_c0]
        constructor
        · intro h ctx hc
          rw [WCtxU_c0] at hc
          obtain ⟨ctx', U, rfl, hc', hU, hUk⟩ := hc
          rw [plug_snoc]
          exact (WPdT_iff ks (Jk1.one U V)).mp (h U hU hUk) ctx' hc'
        · intro h U hU hUk
          refine (WPdT_iff ks (Jk1.one U V)).mpr ?_
          intro ctx' hc'
          rw [← plug_snoc]
          exact h (ctx' ++ [Frm.fone U]) ((WCtxU_c0 ks _).mpr ⟨ctx', U, rfl, hc', hU, hUk⟩)
      · rw [WPdT_cb hb]
        constructor
        · intro h ctx hc
          rw [WCtxU_cb hb] at hc
          obtain ⟨r, hr, ctx', U, N, rfl, hc', hU, hUk, hJN, hNt⟩ := hc
          rw [plug_snoc12]
          exact (WPdT_iff (r ++ ks) _).mp (h r hr U N hU hUk hJN hNt) ctx' hc'
        · intro h r hr U N hU hUk hJN hNt
          refine (WPdT_iff (r ++ ks) _).mpr ?_
          intro ctx' hc'
          rw [← plug_snoc12]
          exact h (ctx' ++ [Frm.fone U, Frm.ftwo N])
            ((WCtxU_cb hb ks _).mpr ⟨r, hr, ctx', U, N, rfl, hc', hU, hUk, hJN, hNt⟩)
termination_by ks _ => ((ks : List Bud) : Multiset Bud)
decreasing_by
  all_goals
    first
      | exact dmT_cons _ _
      | exact dmT_app ks _ (by assumption)

theorem WPdT_congr : ∀ (ks : List Bud) {V1 V2 : Jk1},
    (∀ l, jk1 l V1 = jk1 l V2) → WPdT ks V1 → WPdT ks V2 := by
  intro ks V1 V2 h hA
  rw [WPdT_iff] at hA ⊢
  intro ctx hc
  exact GOK_congr (jk1_plug_congr ctx h) (hA ctx hc)

#print axioms WPdT_iff
#print axioms WPdT_congr

theorem FrmNT_JkA : ∀ (ks : List Bud) (U : Jk1), FrmNT ks U → JkA U
  | [], _, h => h.1
  | (_ :: _), _, h => h

theorem FrmNT_nilA : ∀ ks : List Bud, FrmNT ks Jk1.nil
  | [] => JkT_nil
  | (_ :: _) => trivial

theorem FrmNT_one (ks : List Bud) (U X : Jk1) (hU : FrmNT ks U) (hX : JkA X) :
    FrmNT ks (Jk1.one U X) := by
  cases ks with
  | nil => exact ⟨⟨hU.1, hX⟩, hU.2⟩
  | cons b bs => exact ⟨hU, hX⟩

theorem WCtxU_split (ks : List Bud) (ctx : List Frm)
    (h : WCtxU ((⊥ : Bud) :: ks) ctx) :
    ∃ (ctx0 : List Frm) (V : Jk1), ctx = ctx0 ++ [Frm.fone V] ∧ WCtxU ks ctx0 ∧
      FrmNT ks V ∧ GOK (plug ctx0 V) := by
  rw [WCtxU_c0] at h
  obtain ⟨ctx', U, rfl, hc', hU, hUk⟩ := h
  exact ⟨ctx', U, rfl, hc', hU, (WPdT_iff ks U).mp hUk ctx' hc'⟩

theorem WCtxU_JkT : ∀ (ks : List Bud) (ctx : List Frm), WCtxU ks ctx →
    ∀ X : Jk1, FrmNT ks X → JkT (plug ctx X)
  | [], ctx, h, X, hX => by
      rw [WCtxU_bnil] at h
      subst h
      exact hX
  | (b :: ks), ctx, h, X, hX => by
      by_cases hb : b = ⊥
      · subst hb
        rw [WCtxU_c0] at h
        obtain ⟨ctx', U, rfl, hc', hU, -⟩ := h
        rw [plug_snoc]
        exact WCtxU_JkT ks ctx' hc' (Jk1.one U X) (FrmNT_one ks U X hU hX)
      · rw [WCtxU_cb hb] at h
        obtain ⟨r, hr, ctx', U, N, rfl, hc', hU, hUk, hJN, hNt⟩ := h
        rw [plug_snoc12]
        exact WCtxU_JkT (r ++ ks) ctx' hc' (Jk1.one U (Jk1.two N X))
          (FrmNT_one (r ++ ks) U _ hU ⟨hJN, hX⟩)
termination_by ks _ => ((ks : List Bud) : Multiset Bud)
decreasing_by
  all_goals
    first
      | exact dmT_cons _ _
      | exact dmT_app ks _ (by assumption)

theorem WPdT_two_of_ctx {kk : List Bud} {U N V : Jk1}
    (hU : FrmNT kk U) (hUk : WPdT kk U)
    (h : ∀ ctx : List Frm, WCtxU ((⊥ : Bud) :: kk) ctx →
      GOK (plug ctx (Jk1.two N V))) :
    WPdT kk (Jk1.one U (Jk1.two N V)) := by
  rw [WPdT_iff]
  intro ctx0 hc0
  rw [← plug_snoc]
  exact h (ctx0 ++ [Frm.fone U]) ((WCtxU_c0 kk _).mpr ⟨ctx0, U, rfl, hc0, hU, hUk⟩)

theorem WPdT_payE (V : Jk1) (hV : JkT V) (hVk : WPdT ([] : List Bud) V)
    (C : TrioSeq) (hC : Bok C) : WPdT ([] : List Bud) (Jk1.pay V C) :=
  (WPdT_bnil _).mpr (AY0 C hC V hV ((WPdT_bnil V).mp hVk))

theorem WPdT_ck_shift {b : Bud} (hb : b ≠ ⊥) {ks : List Bud} {T : Jk1}
    (h : WPdT (b :: ks) T) (a : List Bud) (ha : ∀ x ∈ a, x < b) :
    WPdT (b :: (a ++ ks)) T := by
  rw [WPdT_cb hb]
  intro r hr U N hU hUk hJN hNt
  have e : r ++ (a ++ ks) = (r ++ a) ++ ks := (List.append_assoc r a ks).symm
  rw [e] at hU hUk hNt ⊢
  refine (WPdT_cb hb ks T).mp h (r ++ a) ?_ U N hU hUk hJN hNt
  intro x hx
  rcases List.mem_append.mp hx with h1 | h1
  · exact hr x h1
  · exact ha x h1

#print axioms WCtxU_JkT
#print axioms WPdT_ck_shift

/-! ### `WPdT` 層の荷（pay） -/

theorem FrmNT_itJ : ∀ (ks : List Bud) {T : Jk1}, JkA T → ∀ (n : ℕ) {X : Jk1},
    FrmNT ks X → FrmNT ks (itJ T n X)
  | [], _, hT, n, _, h => JkT_itJ hT n h
  | (_ :: _), _, hT, n, _, h => JkA_itJ hT n h

theorem GOK_chainJdWT {ks : List Bud} {ctx : List Frm} (hc : WCtxU ks ctx) {X T : Jk1}
    (hXok : FrmNT ks X) (hXk : WPdT ks X) (hTok : JkA T)
    (hstep : ∀ V : Jk1, FrmNT ks V → WPdT ks V → WPdT ks (Jk1.one V T)) :
    ∀ n, GOK (plug ctx (itJ T n X)) ∧ WPdT ks (itJ T n X)
  | 0 => ⟨(WPdT_iff ks X).mp hXk ctx hc, hXk⟩
  | (n + 1) => by
      obtain ⟨h1, h2⟩ := GOK_chainJdWT hc hXok hXk hTok hstep n
      have hok := FrmNT_itJ ks hTok n hXok
      have h3 := hstep (itJ T n X) hok h2
      exact ⟨(WPdT_iff ks _).mp h3 ctx hc, h3⟩

/-- 予算 `⊥` の荷（`AYdW` の `WPdT` 版）。 -/
theorem AYdWT : ∀ (Y : TrioSeq), Bok Y → ∀ (ks : List Bud) (Z : Jk1), JkA Z →
    WPdT ((⊥ : Bud) :: ks) Z →
    ∀ (X : Jk1), FrmNT ks X → WPdT ks X → WPdT ks (Jk1.one X (Jk1.pay Z Y)) := by
  have key : W 0 ⊆ {Y : TrioSeq | Bok Y → ∀ (ks : List Bud) (Z : Jk1), JkA Z →
      WPdT ((⊥ : Bud) :: ks) Z →
      ∀ (X : Jk1), FrmNT ks X → WPdT ks X → WPdT ks (Jk1.one X (Jk1.pay Z Y))} := by
    refine A2' ?_
    intro Y hY
    simp only [Set.mem_setOf_eq]
    intro hYb ks Z hZ hRZ X hX hXk
    by_cases hshort : Y.length ≤ 1
    · rcases (by omega : Y.length = 0 ∨ Y.length = 1) with h0 | h1
      · have hnil0 : Y = [] := List.length_eq_zero_iff.mp h0
        subst hnil0
        exact WPdT_congr ks (fun l => (jk1_one_pay_nil X Z l).symm) (WPdT_step ks hX hXk hRZ)
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hYb.root
        obtain ⟨hc1, hc2⟩ := hYb.zroot c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have hpres : ∀ V : Jk1, FrmNT ks V → WPdT ks V →
            WPdT ks (Jk1.one V (Jk1.pay Z ([] : TrioSeq))) :=
          fun V hV hVk =>
            WPdT_congr ks (fun l => (jk1_one_pay_nil V Z l).symm) (WPdT_step ks hV hVk hRZ)
        have e : ([((0, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
            = ([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by simp
        rw [e, WPdT_iff]
        intro ctx hc ws hw hG
        refine GoodFb_snoc_dupJs0 hw
          (WCtxU_JkT ks ctx hc (Jk1.one X (Jk1.pay Z (([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))
            (FrmNT_one ks X _ hX ⟨hZ, by simpa using hYb⟩))
          (by simpa using hYb) Bok_nil ?_
        intro n hn
        exact (GOK_chainJdWT (T := Jk1.pay Z ([] : TrioSeq)) hc hX hXk ⟨hZ, Bok_nil⟩
          hpres n).1 ws hw hG
    have hlen2 : 2 ≤ Y.length := by omega
    have hYne : Y ≠ [] := by intro hcc; rw [hcc] at hlen2; simp at hlen2
    rcases hY with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry Y 0 (Y.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hYb.zroot hlast
        have hcol : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) :=
          Prod.ext hlast (Prod.ext he1 he2)
        have hgl : Y.getLast hYne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : Y.getLast hYne = Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show Y.length - 1 < Y.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : Y = Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hYne).symm
        have hop : Y⟦1⟧ = Y.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) ⟨hlast, he1, he2⟩]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdb : Bok Y.dropLast := Bok_dropLast hYb
        have hpres : ∀ V : Jk1, FrmNT ks V → WPdT ks V →
            WPdT ks (Jk1.one V (Jk1.pay Z Y.dropLast)) :=
          fun V hV hVk => hdl hdb ks Z hZ hRZ V hV hVk
        rw [hsplit, WPdT_iff]
        intro ctx hc ws hw hG
        refine GoodFb_snoc_dupJs0 hw
          (WCtxU_JkT ks ctx hc (Jk1.one X (Jk1.pay Z (Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))
            (FrmNT_one ks X _ hX ⟨hZ, by rw [← hsplit]; exact hYb⟩))
          (by rw [← hsplit]; exact hYb) hdb ?_
        intro n hn
        exact (GOK_chainJdWT (T := Jk1.pay Z Y.dropLast) hc hX hXk ⟨hZ, hdb⟩
          hpres n).1 ws hw hG
      · have hnz : ¬ (entry Y 0 (Y.length - 1) = 0 ∧ entry Y 1 (Y.length - 1) = 0 ∧
            entry Y 2 (Y.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hYb.zroot hYb.mono hYb.root hlen2 hnz
        rw [WPdT_iff]
        intro ctx hc ws hw hG
        refine GoodFb_snoc_innerJs0 hw
          (WCtxU_JkT ks ctx hc (Jk1.one X (Jk1.pay Z Y)) (FrmNT_one ks X _ hX ⟨hZ, hYb⟩))
          hYb hlen2 hp ?_
        intro n hn
        have hh := hnat n hn
        simp only [Set.mem_setOf_eq] at hh
        exact (WPdT_iff ks _).mp (hh (Bok_oper hYb hn) ks Z hZ hRZ X hX hXk) ctx hc ws hw hG
    · exact absurd hm (Nat.not_lt_zero m)
  intro Y hYb ks Z hZ hRZ X hX hXk
  exact key hYb.mem hYb ks Z hZ hRZ X hX hXk

theorem WPdT_payT (ks : List Bud) (V : Jk1) (hV : JkA V)
    (hVk : WPdT ((⊥ : Bud) :: ks) V) (C : TrioSeq) (hC : Bok C) :
    WPdT ((⊥ : Bud) :: ks) (Jk1.pay V C) :=
  (WPdT_c0 ks _).mpr (fun U hU hUk => AYdWT C hC ks V hV hVk U hU hUk)

#print axioms AYdWT

theorem WPdT_chainT {b : Bud} {B : List Bud} {ctx : List Frm}
    (hc : WCtxU ((⊥ : Bud) :: B) ctx) {N T : Jk1}
    (hN : JkA N)
    (hNall : ∀ q : List Bud, (∀ x ∈ q, x < b) →
      WPdT ((⊥ : Bud) :: q ++ B) N)
    (hT : JkA T)
    (hstep : ∀ N' : Jk1, JkA N' →
      (∀ q : List Bud, (∀ x ∈ q, x < b) → WPdT ((⊥ : Bud) :: q ++ B) N') →
      ∀ q : List Bud, (∀ x ∈ q, x < b) →
        WPdT ((⊥ : Bud) :: q ++ B) (Jk1.two N' T)) :
    ∀ n, GOK (plug ctx (twoIt N T n)) ∧ JkA (twoIt N T n) ∧
      (∀ q : List Bud, (∀ x ∈ q, x < b) →
        WPdT ((⊥ : Bud) :: q ++ B) (twoIt N T n))
  | 0 => ⟨(WPdT_iff ((⊥ : Bud) :: B) N).mp (by simpa using hNall [] (by simp)) ctx hc,
      hN, hNall⟩
  | (n + 1) => by
      obtain ⟨-, h2, h3⟩ := WPdT_chainT hc hN hNall hT hstep n
      have h4 := hstep (twoIt N T n) h2 h3
      exact ⟨(WPdT_iff ((⊥ : Bud) :: B) _).mp (by simpa using h4 [] (by simp)) ctx hc,
        ⟨h2, hT⟩, h4⟩

theorem AYdTWT_hstep {b : Bud} (hb : b ≠ ⊥) {ks r : List Bud}
    (hr : ∀ x ∈ r, x < b) {T : Jk1} (hTk : WPdT (b :: ks) T) :
    ∀ N' : Jk1, JkA N' →
      (∀ q : List Bud, (∀ x ∈ q, x < b) →
        WPdT ((⊥ : Bud) :: q ++ (r ++ ks)) N') →
      ∀ q : List Bud, (∀ x ∈ q, x < b) →
        WPdT ((⊥ : Bud) :: q ++ (r ++ ks)) (Jk1.two N' T) := by
  intro N' hN' hN'all q hq
  have e : (⊥ : Bud) :: q ++ (r ++ ks) = (⊥ : Bud) :: (q ++ r ++ ks) := by simp
  rw [e]
  refine WPdT_twoOf hb hN' ?_ ?_
  · intro q' hq'
    have e2 : (⊥ : Bud) :: q' ++ (q ++ r ++ ks)
        = ((⊥ : Bud) :: (q' ++ q)) ++ (r ++ ks) := by simp
    rw [e2]
    refine hN'all (q' ++ q) ?_
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact hq' x h1
    · exact hq x h1
  · have hsh := WPdT_ck_shift hb hTk (q ++ r)
      (by
        intro x hx
        rcases List.mem_append.mp hx with h1 | h1
        · exact hq x h1
        · exact hr x h1)
    simpa using hsh

/-- 予算 `b ≠ ⊥` の荷（`AYdTW` の `WPdT` 版）。 -/
theorem AYdTWT : ∀ (Y : TrioSeq), Bok Y → ∀ (b : Bud), b ≠ ⊥ →
    ∀ (ks : List Bud) (Z : Jk1), JkA Z →
    WPdT (b :: ks) Z → WPdT (b :: ks) (Jk1.pay Z Y) := by
  have key : W 0 ⊆ {Y : TrioSeq | Bok Y → ∀ (b : Bud), b ≠ ⊥ →
      ∀ (ks : List Bud) (Z : Jk1), JkA Z →
      WPdT (b :: ks) Z → WPdT (b :: ks) (Jk1.pay Z Y)} := by
    refine A2' ?_
    intro Y hY
    simp only [Set.mem_setOf_eq]
    intro hYb b hb ks Z hZ hZk
    by_cases hshort : Y.length ≤ 1
    · rcases (by omega : Y.length = 0 ∨ Y.length = 1) with h0 | h1
      · have hnil0 : Y = [] := List.length_eq_zero_iff.mp h0
        subst hnil0
        exact WPdT_congr (b :: ks) (fun l => (jk1_pay_nil l Z).symm) hZk
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hYb.root
        obtain ⟨hc1, hc2⟩ := hYb.zroot c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have hZnil : WPdT (b :: ks) (Jk1.pay Z ([] : TrioSeq)) :=
          WPdT_congr (b :: ks) (fun l => (jk1_pay_nil l Z).symm) hZk
        have e : ([((0, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
            = ([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by simp
        rw [e, WPdT_cb hb]
        intro r hr U N hU hUk hN hNt
        refine WPdT_two_of_ctx hU hUk ?_
        intro ctx hc ws hw hG
        refine GoodFb_snoc_dupJt0 hw
          (WCtxU_JkT ((⊥ : Bud) :: (r ++ ks)) ctx hc
            (Jk1.two N (Jk1.pay Z (([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))
            ⟨hN, hZ, by simpa using hYb⟩) ?_
        intro n hn
        exact (WPdT_chainT (T := Jk1.pay Z ([] : TrioSeq)) hc hN hNt ⟨hZ, Bok_nil⟩
          (AYdTWT_hstep hb hr hZnil) n).1 ws hw hG
    have hlen2 : 2 ≤ Y.length := by omega
    have hYne : Y ≠ [] := by intro hcc; rw [hcc] at hlen2; simp at hlen2
    rcases hY with ⟨hl, -⟩ | hnat | ⟨mm, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry Y 0 (Y.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hYb.zroot hlast
        have hcol : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) :=
          Prod.ext hlast (Prod.ext he1 he2)
        have hgl : Y.getLast hYne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : Y.getLast hYne = Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show Y.length - 1 < Y.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : Y = Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hYne).symm
        have hop : Y⟦1⟧ = Y.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) ⟨hlast, he1, he2⟩]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdb : Bok Y.dropLast := Bok_dropLast hYb
        have hprev : WPdT (b :: ks) (Jk1.pay Z Y.dropLast) := hdl hdb b hb ks Z hZ hZk
        rw [hsplit, WPdT_cb hb]
        intro r hr U N hU hUk hN hNt
        refine WPdT_two_of_ctx hU hUk ?_
        intro ctx hc ws hw hG
        refine GoodFb_snoc_dupJt0 hw
          (WCtxU_JkT ((⊥ : Bud) :: (r ++ ks)) ctx hc
            (Jk1.two N (Jk1.pay Z (Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))
            ⟨hN, hZ, by rw [← hsplit]; exact hYb⟩) ?_
        intro n hn
        exact (WPdT_chainT (T := Jk1.pay Z Y.dropLast) hc hN hNt ⟨hZ, hdb⟩
          (AYdTWT_hstep hb hr hprev) n).1 ws hw hG
      · have hnz : ¬ (entry Y 0 (Y.length - 1) = 0 ∧ entry Y 1 (Y.length - 1) = 0 ∧
            entry Y 2 (Y.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hYb.zroot hYb.mono hYb.root hlen2 hnz
        rw [WPdT_cb hb]
        intro r hr U N hU hUk hN hNt
        refine WPdT_two_of_ctx hU hUk ?_
        intro ctx hc ws hw hG
        refine GoodFb_snoc_innerJt0 hw
          (WCtxU_JkT ((⊥ : Bud) :: (r ++ ks)) ctx hc
            (Jk1.two N (Jk1.pay Z Y)) ⟨hN, hZ, hYb⟩)
          hlen2 hp ?_
        intro n hn
        have hh := hnat n hn
        simp only [Set.mem_setOf_eq] at hh
        have hh2 := hh (Bok_oper hYb hn) b hb ks Z hZ hZk
        have hc' := hc
        rw [WCtxU_c0] at hc'
        obtain ⟨ctx0, U', hce, hc0, hU', hU'k⟩ := hc'
        subst hce
        have h2 := (WPdT_cb hb ks _).mp hh2 r hr U' N hU' hU'k hN hNt
        rw [plug_snoc]
        exact (WPdT_iff _ _).mp h2 ctx0 hc0 ws hw hG
    · exact absurd hm (Nat.not_lt_zero mm)
  intro Y hYb b hb ks Z hZ hZk
  exact key hYb.mem hYb b hb ks Z hZ hZk

/-- ★★★★★ `WPdT` 層の荷（どの形でも）。 -/
theorem WPdT_payA : ∀ (ks : List Bud) (V : Jk1), FrmNT ks V → WPdT ks V →
    ∀ C : TrioSeq, Bok C → WPdT ks (Jk1.pay V C)
  | [], V, hV, hVk, C, hC => WPdT_payE V hV hVk C hC
  | (b :: ks), V, hV, hVk, C, hC => by
      by_cases hb : b = ⊥
      · subst hb
        exact WPdT_payT ks V (FrmNT_JkA _ V hV) hVk C hC
      · exact AYdTWT C hC b hb ks V (FrmNT_JkA _ V hV) hVk

#print axioms AYdTWT
#print axioms WPdT_payA

/-! ### `WPdT` 層の空木 -/

theorem FrmNT_repB (m : ℕ) (b : Bud) (ks : List Bud) (N : Jk1) :
    FrmNT (List.replicate m (⊥ : Bud) ++ (b :: ks)) N ↔ JkA N := by
  cases m with
  | zero => exact Iff.rfl
  | succ m => exact Iff.rfl

theorem repB_succ_cons (m : ℕ) (ks : List Bud) :
    List.replicate (m + 1) (⊥ : Bud) ++ ks
      = (⊥ : Bud) :: (List.replicate m (⊥ : Bud) ++ ks) := rfl

theorem lt_of_mem_repB {b : Bud} (hb : b ≠ ⊥) (j : ℕ) :
    ∀ x ∈ List.replicate j (⊥ : Bud), x < b := by
  intro x hx
  have hx0 : x = (⊥ : Bud) := List.eq_of_mem_replicate hx
  subst hx0
  exact Ne.bot_lt' (Ne.symm hb)

theorem repB_mid : ∀ (j : ℕ) (B : List Bud),
    List.replicate j (⊥ : Bud) ++ ((⊥ : Bud) :: B)
      = ((⊥ : Bud) :: List.replicate j (⊥ : Bud)) ++ B
  | 0, B => rfl
  | (j + 1), B => by
      show (⊥ : Bud) :: (List.replicate j (⊥ : Bud) ++ ((⊥ : Bud) :: B))
        = (⊥ : Bud) :: ((⊥ : Bud) :: (List.replicate j (⊥ : Bud) ++ B))
      rw [repB_mid j B]
      rfl

theorem WCtxU_rep {N : Jk1} (hJN : JkA N) (ks : List Bud)
    (hNall : ∀ j : ℕ, WPdT (List.replicate j (⊥ : Bud) ++ ((⊥ : Bud) :: ks)) N) :
    ∀ (m : ℕ) (ctx : List Frm), WCtxU ((⊥ : Bud) :: ks) ctx →
      WCtxU (List.replicate m (⊥ : Bud) ++ ((⊥ : Bud) :: ks))
        (ctx ++ List.replicate m (Frm.fone N))
  | 0, ctx, hc => by simpa using hc
  | (m + 1), ctx, hc => by
      have h1 := WCtxU_rep hJN ks hNall m ctx hc
      have e : ctx ++ List.replicate (m + 1) (Frm.fone N)
          = (ctx ++ List.replicate m (Frm.fone N)) ++ [Frm.fone N] := by
        rw [List.replicate_succ']
        simp
      rw [e, repB_succ_cons, WCtxU_c0]
      exact ⟨ctx ++ List.replicate m (Frm.fone N), N, rfl, h1,
        (FrmNT_repB m (⊥ : Bud) ks N).mpr hJN, hNall m⟩

theorem WPdT_plug_rep (N : Jk1) (hJN : JkA N) (ks : List Bud)
    (hNall : ∀ j : ℕ, WPdT (List.replicate j (⊥ : Bud) ++ ((⊥ : Bud) :: ks)) N)
    (m : ℕ) :
    WPdT ((⊥ : Bud) :: ks) (plug (List.replicate m (Frm.fone N)) N) := by
  rw [WPdT_iff]
  intro ctx hc
  rw [← plug_append]
  exact (WPdT_iff _ N).mp (hNall m) _ (WCtxU_rep hJN ks hNall m ctx hc)

theorem WPdT_twoNilGen {N : Jk1} (hJN : JkA N) (ks : List Bud)
    (hNall : ∀ j : ℕ, WPdT (List.replicate j (⊥ : Bud) ++ ((⊥ : Bud) :: ks)) N) :
    WPdT ((⊥ : Bud) :: ks) (Jk1.two N Jk1.nil) := by
  rw [WPdT_iff]
  intro ctx hc
  obtain ⟨ctx0, V, rfl, hc0, hV, hGV⟩ := WCtxU_split ks ctx hc
  exact GOK_twoNilW_gen ctx0 V hJN
    (WCtxU_JkT ((⊥ : Bud) :: ks) _ hc (Jk1.two N Jk1.nil)
      (⟨hJN, trivial⟩ : FrmNT ((⊥ : Bud) :: ks) (Jk1.two N Jk1.nil)))
    hGV
    (fun m => (WPdT_iff ((⊥ : Bud) :: ks) _).mp (WPdT_plug_rep N hJN ks hNall m) _ hc)

theorem WPdT_nilF {b : Bud} (hb : b ≠ ⊥) (ks : List Bud) :
    WPdT (b :: ks) Jk1.nil :=
  (WPdT_cb hb ks _).mpr (fun r hr U N hU hUk hJN hNt =>
    (WPdT_c0 _ _).mp
      (WPdT_twoNilGen hJN (r ++ ks)
        (fun j => by
          rw [repB_mid j (r ++ ks)]
          exact hNt (List.replicate j (⊥ : Bud)) (lt_of_mem_repB hb j))) U hU hUk)

theorem WPdT_oneNil (ks : List Bud) (V : Jk1) (hV : FrmNT ks V) (hVk : WPdT ks V) :
    WPdT ks (Jk1.one V Jk1.nil) := by
  rw [WPdT_iff]
  intro ctx hc
  refine APnil_gen0 ctx V
    (WCtxU_JkT ks ctx hc (Jk1.one V Jk1.nil) (FrmNT_one ks V Jk1.nil hV trivial))
    ((WPdT_iff ks V).mp hVk ctx hc) ?_
  intro C hC
  exact (WPdT_iff ks _).mp (WPdT_payA ks V hV hVk C hC) ctx hc

theorem WPdT_nilT (ks : List Bud) : WPdT ((⊥ : Bud) :: ks) Jk1.nil :=
  (WPdT_c0 ks _).mpr (fun U hU hUk => WPdT_oneNil ks U hU hUk)

/-- ★★★★★ 空木はどの形でも差せる（`WPdT` 層、無条件）。 -/
theorem WPdT_nilAll : ∀ ks : List Bud, WPdT ks Jk1.nil
  | [] => (WPdT_bnil _).mpr GOK_nil
  | (b :: ks) => by
      by_cases hb : b = ⊥
      · subst hb
        exact WPdT_nilT ks
      · exact WPdT_nilF hb ks

#print axioms WPdT_nilAll

/-! ### `WPdT` 層の走り（`WPd_stairB` / `WPd_twoA_runB` / `WPd_twoIt_nil` の移植）

予算が `Bud` になったので、外側の予算 `c` と兄弟 `A` の予算 `a` の関係は
`a < c` の 1 本だけ。`c = ⊤` を取れば `a` は任意の自然数でよい。 -/

theorem WPdT_stairB {c a : Bud} (ha : a ≠ ⊥) (hac : a < c) {N A : Jk1}
    (hJN : JkA N) (hJA : JkA A) (hAall : ∀ ks : List Bud, WPdT (a :: ks) A) :
    ∀ (n : ℕ) (B' : List Bud),
      (∀ q : List Bud, (∀ x ∈ q, x < c) →
        WPdT ((⊥ : Bud) :: q ++ B') N) →
      WPdT ((⊥ : Bud) :: B') (Jk1.two N (appJ A (UtwP [N] A n)))
  | 0, B', hsib =>
      WPdT_twoOf ha hJN
        (fun q hq => hsib q (fun x hx => lt_trans (hq x hx) hac))
        (hAall B')
  | (n + 1), B', hsib => by
      refine WPdT_twoOf ha hJN
        (fun q hq => hsib q (fun x hx => lt_trans (hq x hx) hac)) ?_
      show WPdT (a :: B') (Jk1.one A (Jk1.two N (appJ A (UtwP [N] A n))))
      refine WPdT_step (a :: B') (hJA : FrmNT (a :: B') A) (hAall B') ?_
      refine WPdT_stairB ha hac hJN hJA hAall n (a :: B') ?_
      intro q hq
      have e : (⊥ : Bud) :: q ++ (a :: B') = ((⊥ : Bud) :: (q ++ [a])) ++ B' := by
        simp
      rw [e]
      refine hsib (q ++ [a]) ?_
      intro x hx
      rcases List.mem_append.mp hx with h1 | h1
      · exact hq x h1
      · simp only [List.mem_singleton] at h1
        subst h1
        exact hac

theorem WPdT_twoA_runB {c a : Bud} (ha : a ≠ ⊥) (hac : a < c) {A : Jk1}
    (hJA : JkA A) (hAall : ∀ ks : List Bud, WPdT (a :: ks) A)
    (ks : List Bud) :
    WPdT (c :: ks) (Jk1.two A Jk1.nil) := by
  have hcb : c ≠ ⊥ := ne_bot_of_gt hac
  refine (WPdT_cb hcb ks _).mpr (fun r hr U N hU hUk hJN hNt => ?_)
  refine (WPdT_c0 (r ++ ks) _).mp ?_ U hU hUk
  rw [WPdT_iff]
  intro ctx hc
  obtain ⟨ctx0, V, rfl, hc0, hV, hGV⟩ := WCtxU_split (r ++ ks) ctx hc
  have hJT : JkT (plug (ctx0 ++ [Frm.fone V]) (Jk1.two N (Jk1.two A Jk1.nil))) :=
    WCtxU_JkT ((⊥ : Bud) :: (r ++ ks)) _ hc (Jk1.two N (Jk1.two A Jk1.nil))
      (⟨hJN, hJA, trivial⟩ :
        FrmNT ((⊥ : Bud) :: (r ++ ks)) (Jk1.two N (Jk1.two A Jk1.nil)))
  have erun : Jk1.two N (Jk1.two A Jk1.nil) = RunS ([N] ++ [A]) := rfl
  rw [plug_snoc] at hJT ⊢
  rw [erun] at hJT ⊢
  refine GOK_oneUV_RunSB ctx0 [N] A V (by simpa using hJN) hJA hJT hGV ?_
  intro n
  cases n with
  | zero =>
      show GOK (plug ctx0 V)
      exact hGV
  | succ n =>
      show GOK (plug ctx0 (Jk1.one V (Jk1.two N (appJ A (UtwP [N] A n)))))
      rw [← plug_snoc]
      exact (WPdT_iff ((⊥ : Bud) :: (r ++ ks)) _).mp
        (WPdT_stairB ha hac hJN hJA hAall n (r ++ ks) hNt) _ hc

theorem Scale.nb_ne_bot (S : Scale Bud) (m : ℕ) : S.nb (m + 1) ≠ ⊥ :=
  ne_bot_of_gt (lt_of_le_of_lt bot_le (S.nbmono (Nat.succ_pos m)))

/-- 平らな走り `twoIt nil nil m` は、予算 `c > nb m` のどの形にも差せる。 -/
theorem WPdT_twoIt_nil (S : Scale Bud) : ∀ (m : ℕ) (c : Bud), S.nb m < c →
    ∀ ks : List Bud, WPdT (c :: ks) (twoIt Jk1.nil Jk1.nil m)
  | 0, c, hc, ks => WPdT_nilF (ne_bot_of_gt (lt_of_le_of_lt bot_le hc)) ks
  | (m + 1), c, hc, ks =>
      WPdT_twoA_runB (a := S.nb (m + 1)) (S.nb_ne_bot m) hc
        (JkA_twoIt_nil m)
        (fun ks' => WPdT_twoIt_nil S m (S.nb (m + 1)) (S.nbmono (by omega)) ks') ks

#print axioms WPdT_twoIt_nil

/-! ### ★★★★★★★ 壁: `M0t` を予算 `⊤` の節に差す

`WPd` 層では `WPd ((k+1)::ks) M0t` が通らなかった。荷の重複鎖が
`twoIt nil (pay nil []) m` という「幅 m の横の走り」を作り、兄弟の予算 `k` が
その幅を止めていたため。予算を `⊤` にすると兄弟は全部の自然数予算で使えるので、
どの幅 `m` にも届く。 -/

theorem WPdT_twoM0_at (S : Scale Bud) {t : Bud} (ht : ∀ m : ℕ, S.nb m < t)
    {B : List Bud} {N : Jk1} (hJN : JkA N)
    (hNt : ∀ q : List Bud, (∀ x ∈ q, x < t) →
      WPdT ((⊥ : Bud) :: q ++ B) N) :
    WPdT ((⊥ : Bud) :: B) (Jk1.two N M0t) := by
  rw [WPdT_iff]
  intro ctx hc
  have eT : Jk1.two Jk1.nil (Jk1.pay Jk1.nil
      (([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])) = M0t := by simp [M0t]
  have hJT : JkT (plug (ctx ++ [Frm.ftwo N])
      (Jk1.two Jk1.nil (Jk1.pay Jk1.nil (([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))) := by
    rw [plug_snoc2, eT]
    exact WCtxU_JkT ((⊥ : Bud) :: B) ctx hc (Jk1.two N M0t)
      (⟨hJN, JkA_M0t⟩ : FrmNT ((⊥ : Bud) :: B) (Jk1.two N M0t))
  intro ws hw hG
  have hIH : ∀ m : ℕ, 1 ≤ m → GoodFb (fun a b => wordJ a b
      (ws ++ [plug (ctx ++ [Frm.ftwo N])
        (twoIt Jk1.nil (Jk1.pay Jk1.nil ([] : TrioSeq)) m)])) := by
    intro m _
    rw [plug_snoc2]
    have hw2 : WPdT ((⊥ : Bud) :: B)
        (Jk1.two N (twoIt Jk1.nil (Jk1.pay Jk1.nil ([] : TrioSeq)) m)) := by
      refine WPdT_congr ((⊥ : Bud) :: B) (fun l => ?_)
        (WPdT_twoOf (b := S.nb (m + 1)) (S.nb_ne_bot m) hJN
          (fun q hq => hNt q (fun x hx => lt_trans (hq x hx) (ht (m + 1))))
          (WPdT_twoIt_nil S m (S.nb (m + 1)) (S.nbmono (by omega)) B))
      show jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
          jk1 (l + 1) (twoIt Jk1.nil Jk1.nil m))
        = jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
          jk1 (l + 1) (twoIt Jk1.nil (Jk1.pay Jk1.nil ([] : TrioSeq)) m))
      rw [jk1_twoIt_payNil m (l + 1)]
    exact (WPdT_iff ((⊥ : Bud) :: B) _).mp hw2 ctx hc ws hw hG
  have h := GoodFb_snoc_dupJt0 hw hJT hIH
  rw [plug_snoc2, eT] at h
  exact h

/-- ★★★★★★★ 壁が抜けた。`M0t` は「ω 段の上」の予算 `t` の節に差せる。 -/
theorem WPdT_M0t_top (S : Scale Bud) {t : Bud} (ht : ∀ m : ℕ, S.nb m < t)
    (ks : List Bud) : WPdT (t :: ks) M0t :=
  have htb : t ≠ ⊥ := ne_bot_of_gt (lt_of_le_of_lt bot_le (ht 0))
  (WPdT_cb htb ks _).mpr (fun r hr U N hU hUk hJN hNt =>
    WPdT_two_of_ctx hU hUk
      (fun ctx hc => (WPdT_iff ((⊥ : Bud) :: (r ++ ks)) _).mp
        (WPdT_twoM0_at S ht hJN hNt) ctx hc))

#print axioms WPdT_M0t_top

/-! ### ★ `WPdT_M0t_top` の一般形: 荷つきの平らな走りを予算の節に置く

`two A (pay Z [(0,0,0)])` の最後の列を重複させると鎖は
`twoIt A (pay Z []) m`、語は `twoIt A Z m` と同じ（`jk1_pay_nil`）。
だから「`twoIt A Z m` を段 `nb m` の上の予算に置ける」ことさえ言えれば、
`two A (pay Z [(0,0,0)])` は段の上の予算 `t` に置ける。 -/

theorem jk1_twoIt_payZ (A Z : Jk1) : ∀ (n l : ℕ),
    jk1 l (twoIt A (Jk1.pay Z ([] : TrioSeq)) n) = jk1 l (twoIt A Z n)
  | 0, _ => rfl
  | (n + 1), l => by
      show jk1 l (twoIt A (Jk1.pay Z ([] : TrioSeq)) n) ++
          (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) (Jk1.pay Z ([] : TrioSeq)))
        = jk1 l (twoIt A Z n) ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) Z)
      rw [jk1_twoIt_payZ A Z n l, jk1_pay_nil]

/-- 上が空の平らな走り。底 `A` は「段 `nb 0` より上の予算ならどこでも」でよい。 -/
theorem WPdT_twoItA_nil (S : Scale Bud) {A : Jk1} (hJA : JkA A)
    (hA : ∀ c : Bud, S.nb 0 < c → ∀ ks : List Bud, WPdT (c :: ks) A) :
    ∀ (m : ℕ) (c : Bud), S.nb m < c → ∀ ks : List Bud,
      WPdT (c :: ks) (twoIt A Jk1.nil m)
  | 0, c, hc, ks => hA c hc ks
  | (m + 1), c, hc, ks =>
      WPdT_twoA_runB (a := S.nb (m + 1)) (S.nb_ne_bot m) hc
        (JkA_twoItP (Wl := A) (T := Jk1.nil) hJA trivial m)
        (fun ks' => WPdT_twoItA_nil S hJA hA m (S.nb (m + 1)) (S.nbmono (by omega)) ks') ks

theorem WPdT_twoAZ_at (S : Scale Bud) {t : Bud} (ht : ∀ m : ℕ, S.nb m < t)
    {A Z : Jk1} (hJA : JkA A) (hJZ : JkA Z)
    (hchain : ∀ (m : ℕ) (c : Bud), S.nb m < c → ∀ ks : List Bud,
      WPdT (c :: ks) (twoIt A Z m))
    {B : List Bud} {N : Jk1} (hJN : JkA N)
    (hNt : ∀ q : List Bud, (∀ x ∈ q, x < t) → WPdT ((⊥ : Bud) :: q ++ B) N) :
    WPdT ((⊥ : Bud) :: B)
      (Jk1.two N (Jk1.two A (Jk1.pay Z [((0, 0, 0) : ℕ × ℕ × ℕ)]))) := by
  rw [WPdT_iff]
  intro ctx hc
  have eT : Jk1.two A (Jk1.pay Z (([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))
      = Jk1.two A (Jk1.pay Z [((0, 0, 0) : ℕ × ℕ × ℕ)]) := by simp
  have hJT : JkT (plug (ctx ++ [Frm.ftwo N])
      (Jk1.two A (Jk1.pay Z (([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))) := by
    rw [plug_snoc2, eT]
    exact WCtxU_JkT ((⊥ : Bud) :: B) ctx hc
      (Jk1.two N (Jk1.two A (Jk1.pay Z [((0, 0, 0) : ℕ × ℕ × ℕ)])))
      (⟨hJN, hJA, hJZ, Bok_zero⟩ : FrmNT ((⊥ : Bud) :: B)
        (Jk1.two N (Jk1.two A (Jk1.pay Z [((0, 0, 0) : ℕ × ℕ × ℕ)]))))
  intro ws hw hG
  have hIH : ∀ m : ℕ, 1 ≤ m → GoodFb (fun a b => wordJ a b
      (ws ++ [plug (ctx ++ [Frm.ftwo N]) (twoIt A (Jk1.pay Z ([] : TrioSeq)) m)])) := by
    intro m _
    rw [plug_snoc2]
    have hw2 : WPdT ((⊥ : Bud) :: B)
        (Jk1.two N (twoIt A (Jk1.pay Z ([] : TrioSeq)) m)) := by
      refine WPdT_congr ((⊥ : Bud) :: B) (fun l => ?_)
        (WPdT_twoOf (b := S.nb (m + 1)) (S.nb_ne_bot m) hJN
          (fun q hq => hNt q (fun x hx => lt_trans (hq x hx) (ht (m + 1))))
          (hchain m (S.nb (m + 1)) (S.nbmono (by omega)) B))
      show jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) (twoIt A Z m))
        = jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
          jk1 (l + 1) (twoIt A (Jk1.pay Z ([] : TrioSeq)) m))
      rw [jk1_twoIt_payZ A Z m (l + 1)]
    exact (WPdT_iff ((⊥ : Bud) :: B) _).mp hw2 ctx hc ws hw hG
  have h := GoodFb_snoc_dupJt0 hw hJT hIH
  rw [plug_snoc2, eT] at h
  exact h

/-- ★★★★★★★ 荷 `[(0,0,0)]` を乗せた 2 の記録は、鎖が段の上に置ければ
段の上の予算 `t` に置ける。`A = Z = nil` が `WPdT_M0t_top`。 -/
theorem WPdT_twoAZ_top (S : Scale Bud) {t : Bud} (ht : ∀ m : ℕ, S.nb m < t)
    {A Z : Jk1} (hJA : JkA A) (hJZ : JkA Z)
    (hchain : ∀ (m : ℕ) (c : Bud), S.nb m < c → ∀ ks : List Bud,
      WPdT (c :: ks) (twoIt A Z m))
    (ks : List Bud) :
    WPdT (t :: ks) (Jk1.two A (Jk1.pay Z [((0, 0, 0) : ℕ × ℕ × ℕ)])) :=
  have htb : t ≠ ⊥ := ne_bot_of_gt (lt_of_le_of_lt bot_le (ht 0))
  (WPdT_cb htb ks _).mpr (fun r hr U N hU hUk hJN hNt =>
    WPdT_two_of_ctx hU hUk
      (fun ctx hc => (WPdT_iff ((⊥ : Bud) :: (r ++ ks)) _).mp
        (WPdT_twoAZ_at S ht hJA hJZ hchain hJN hNt) ctx hc))

#print axioms WPdT_twoAZ_top

end Bud

/-! ### 予算型の実体化: `Bud2 = ℕ ×ₗ ℕ`（順序型 ω²）

`nb m = (0, m)` が ω 段、その上の `(1, 0)` に `M0t` が乗り、
さらにその上の `(1, 1)` に `two M0t nil`（M0t の直上の 2 の記録）が乗る。 -/

abbrev Bud2 : Type := ℕ ×ₗ ℕ

def Sc2 : Scale Bud2 where
  nb := fun m => toLex (0, m)
  nbmono := fun _ _ h => Prod.Lex.right _ h

theorem Sc2_lt_w (m : ℕ) : Sc2.nb m < (toLex (1, 0) : Bud2) := Prod.Lex.left _ _ (by omega)

theorem Bud2_ne_bot (i j : ℕ) (h : 0 < i) : (toLex (i, j) : Bud2) ≠ ⊥ :=
  ne_bot_of_gt (show (⊥ : Bud2) < toLex (i, j) from Prod.Lex.left _ _ h)

/-- `M0t` は予算 `(1,0) = ω` の節に差せる。 -/
theorem WPdT2_M0t (ks : List Bud2) : WPdT ((toLex (1, 0) : Bud2) :: ks) M0t :=
  WPdT_M0t_top Sc2 Sc2_lt_w ks

/-- ★ `two M0t nil`（`M0t` の直上にもう 1 本 2 の記録）は予算 `(1,1) = ω+1` で差せる。 -/
theorem WPdT2_twoM0nil (ks : List Bud2) :
    WPdT ((toLex (1, 1) : Bud2) :: ks) (Jk1.two M0t Jk1.nil) :=
  WPdT_twoA_runB (a := (toLex (1, 0) : Bud2)) (Bud2_ne_bot 1 0 (by omega))
    (Prod.Lex.right _ (by omega)) JkA_M0t WPdT2_M0t ks

def X52 : Jk1 := Jk1.two Jk1.nil (Jk1.two M0t Jk1.nil)

theorem JkA_X52 : JkA X52 := ⟨trivial, JkA_M0t, trivial⟩

theorem WPdT2_X52 (ks : List Bud2) : WPdT ((⊥ : Bud2) :: ks) X52 :=
  WPdT_twoOf (b := (toLex (1, 1) : Bud2)) (Bud2_ne_bot 1 1 (by omega)) trivial
    (fun q _ => WPdT_nilAll _) (WPdT2_twoM0nil ks)

theorem GOK_oneX52 : GOK (Jk1.one Jk1.nil X52) :=
  (WPdT_bnil (Bud := Bud2) _).mp
    (WPdT_step ([] : List Bud2) (JkT_nil : FrmNT ([] : List Bud2) Jk1.nil)
      ((WPdT_bnil (Bud := Bud2) _).mpr GOK_nil) (WPdT2_X52 []))

theorem jk1_X52 (l : ℕ) : jk1 l X52
    = [((l + 1, 2, 0) : ℕ × ℕ × ℕ), ((l + 2, 2, 0) : ℕ × ℕ × ℕ),
       ((l + 3, 0, 0) : ℕ × ℕ × ℕ), ((l + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1) M0t ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 2) Jk1.nil))) = _
  rw [jk1_M0t (l + 1)]
  simp [jk1, show l + 1 + 1 = l + 2 from by omega, show l + 1 + 2 = l + 3 from by omega]

/-- ★★★★★★★ シート「証明中」の行:
`(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,0,0)(5,2,0)` -/
theorem R600520_mem : R600 ++ [((5, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil X52]) := by
    simpa using GOK_oneX52 [] WOk_nil GoodFb_wordJ_nil
  have hh := rowJ_mem_genF Aok_R338 hG
  have e : jk1 2 (Jk1.one Jk1.nil X52)
      = [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ), ((5, 2, 0) : ℕ × ℕ × ℕ),
         ((6, 0, 0) : ℕ × ℕ × ℕ), ((5, 2, 0) : ℕ × ℕ × ℕ)] := by
    show jk1 2 Jk1.nil ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (2 + 1) X52) = _
    rw [jk1_X52 3]
    simp [jk1]
  rw [wordJ_singleton, colJ, e] at hh
  simpa [R600, R375m, R373, R344, R341, R338, List.append_assoc] using hh

#print axioms R600520_mem

/-! ### ★ 新しい行 `R600 (5,2,0)` の `Aok` を取って、族の台座を差し替える -/

def Z520 : TrioSeq := R600 ++ [((5, 2, 0) : ℕ × ℕ × ℕ)]

theorem Aok_Z520 : Aok Z520 :=
  Aok_append_Mid (d := 6) (by omega) Aok_R600 MidD_col52 R600520_mem

theorem Z520_110_mem : Z520 ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa using Lv_snoc 1 0 _ (Aok_Z520 : Lv 1 0 Z520)

theorem Z520_1122_mem :
    Z520 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa using Lv_snoc2 1 0 _ (Aok_Z520 : Lv 1 0 Z520)

/-- ★★★★★★ `R600 (5,2,0)` の上、輪を `n` 周した 4 パラメータの無限族。 -/
theorem LoopIt_Z520_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (j n : ℕ) :
    LoopIt Z520 m ws j n ∈ W 0 := (Aok_LoopIt Aok_Z520 m hw j n).mem

theorem LoopIt_Z520_nil_mem (m p j n : ℕ) :
    LoopIt Z520 m (List.replicate p (AltT 0)) j n ∈ W 0 :=
  LoopIt_Z520_mem m (WJ_rep_AltT 0 p) j n

#print axioms Aok_Z520
#print axioms LoopIt_Z520_nil_mem

/-! ### 予算型 `Bud3 = ℕ ×ₗ (ℕ ×ₗ ℕ)`（順序型 ω³）と `R600 (6,0,0)`

荷が入れ子になると（`pay (pay nil [(0,0,0)]) [(0,0,0)]`）、鎖は荷つきの平らな
走り `FLz m` になる。`FLz m` を置くには `ω·m` の予算が要るので、
その上の `ω²` が要る。 -/

abbrev Bud3 : Type := ℕ ×ₗ (ℕ ×ₗ ℕ)

def b3 (a b c : ℕ) : Bud3 := toLex (a, toLex (b, c))

theorem b3_lt1 {a a' : ℕ} (h : a < a') (b c b' c' : ℕ) : b3 a b c < b3 a' b' c' :=
  Prod.Lex.left _ _ h

theorem b3_lt2 (a : ℕ) {b b' : ℕ} (h : b < b') (c c' : ℕ) : b3 a b c < b3 a b' c' :=
  Prod.Lex.right _ (Prod.Lex.left _ _ h)

theorem b3_lt3 (a b : ℕ) {c c' : ℕ} (h : c < c') : b3 a b c < b3 a b c' :=
  Prod.Lex.right _ (Prod.Lex.right _ h)

/-- `ω·k` の上の段 `ω·k + i`。 -/
def Sc3 (k : ℕ) : Scale Bud3 where
  nb := fun i => b3 0 k i
  nbmono := fun _ _ h => b3_lt3 0 k h

/-- `ω·m` の段。 -/
def Scw : Scale Bud3 where
  nb := fun m => b3 0 m 0
  nbmono := fun _ _ h => b3_lt2 0 h 0 0

def M1t : Jk1 := Jk1.pay Jk1.nil [((0, 0, 0) : ℕ × ℕ × ℕ)]

theorem JkA_M1t : JkA M1t := ⟨trivial, Bok_zero⟩

theorem JkA_FLz (n : ℕ) : JkA (FLz n) := JkA_FLr _ (Bok_FLz_mem n)

theorem FLz_eq_twoIt : ∀ n : ℕ, FLz n = twoIt Jk1.nil M1t n
  | 0 => rfl
  | (n + 1) => by
      rw [FLz_succ n, FLz_eq_twoIt n]
      rfl

/-- 荷が全部 `[(0,0,0)]` の平らな走り `FLz k` は、予算 `> ω·k` のどの節にも置ける。 -/
theorem WPdT3_FLz : ∀ (k : ℕ) (c : Bud3), b3 0 k 0 < c → ∀ ks : List Bud3,
    WPdT (c :: ks) (FLz k)
  | 0, c, hc, ks => WPdT_nilF (ne_bot_of_gt (lt_of_le_of_lt bot_le hc)) ks
  | (k + 1), c, hc, ks => by
      rw [FLz_succ k]
      refine WPdT_twoAZ_top (Sc3 k) (A := FLz k) (Z := Jk1.nil) ?_ (JkA_FLz k)
        trivial ?_ ks
      · intro m
        exact lt_trans (b3_lt2 0 (by omega : k < k + 1) m 0) hc
      · intro m c' hc' ks'
        exact WPdT_twoItA_nil (Sc3 k) (JkA_FLz k)
          (fun c'' hc'' ks'' => WPdT3_FLz k c'' hc'' ks'') m c' hc' ks'

def M0u : Jk1 := Jk1.two Jk1.nil (Jk1.pay M1t [((0, 0, 0) : ℕ × ℕ × ℕ)])

theorem JkA_M0u : JkA M0u := ⟨trivial, JkA_M1t, Bok_zero⟩

/-- ★★★★★★★ 荷が 2 段の `M0u` は予算 `ω²` の節に置ける。 -/
theorem WPdT3_M0u (ks : List Bud3) : WPdT (b3 1 0 0 :: ks) M0u := by
  refine WPdT_twoAZ_top Scw (A := Jk1.nil) (Z := M1t) ?_ trivial JkA_M1t ?_ ks
  · intro m
    exact b3_lt1 (show (0 : ℕ) < 1 by omega) m 0 0 0
  · intro m c hc ks'
    have h := WPdT3_FLz m c hc ks'
    rw [FLz_eq_twoIt m] at h
    exact h

def Xu : Jk1 := Jk1.two Jk1.nil M0u

theorem WPdT3_Xu (ks : List Bud3) : WPdT ((⊥ : Bud3) :: ks) Xu :=
  WPdT_twoOf (b := b3 1 0 0)
    (ne_bot_of_gt (b3_lt1 (show (0 : ℕ) < 1 by omega) 0 0 0 0)) trivial
    (fun q _ => WPdT_nilAll _) (WPdT3_M0u ks)

theorem GOK_oneXu : GOK (Jk1.one Jk1.nil Xu) :=
  (WPdT_bnil (Bud := Bud3) _).mp
    (WPdT_step ([] : List Bud3) (JkT_nil : FrmNT ([] : List Bud3) Jk1.nil)
      ((WPdT_bnil (Bud := Bud3) _).mpr GOK_nil) (WPdT3_Xu []))

theorem jk1_M1t (l : ℕ) : jk1 l M1t = [((l + 1, 0, 0) : ℕ × ℕ × ℕ)] := by
  show jk1 l Jk1.nil ++ shiftr01 (l + 1) 0 [((0, 0, 0) : ℕ × ℕ × ℕ)] = _
  simp [jk1, shiftr01]

theorem jk1_M0u (l : ℕ) : jk1 l M0u
    = [((l + 1, 2, 0) : ℕ × ℕ × ℕ), ((l + 2, 0, 0) : ℕ × ℕ × ℕ),
       ((l + 2, 0, 0) : ℕ × ℕ × ℕ)] := by
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1) M1t ++ shiftr01 (l + 1 + 1) 0 [((0, 0, 0) : ℕ × ℕ × ℕ)])) = _
  rw [jk1_M1t (l + 1)]
  simp [jk1, shiftr01, show l + 1 + 1 = l + 2 from by omega]

theorem jk1_Xu (l : ℕ) : jk1 l Xu
    = [((l + 1, 2, 0) : ℕ × ℕ × ℕ), ((l + 2, 2, 0) : ℕ × ℕ × ℕ),
       ((l + 3, 0, 0) : ℕ × ℕ × ℕ), ((l + 3, 0, 0) : ℕ × ℕ × ℕ)] := by
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M0u) = _
  rw [jk1_M0u (l + 1)]
  simp [jk1, show l + 1 + 1 = l + 2 from by omega, show l + 1 + 2 = l + 3 from by omega]

/-- ★★★★★★★ `R600 (6,0,0)`:
`(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,0,0)(6,0,0)` -/
theorem R600600_mem : R600 ++ [((6, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil Xu]) := by
    simpa using GOK_oneXu [] WOk_nil GoodFb_wordJ_nil
  have hh := rowJ_mem_genF Aok_R338 hG
  have e : jk1 2 (Jk1.one Jk1.nil Xu)
      = [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ), ((5, 2, 0) : ℕ × ℕ × ℕ),
         ((6, 0, 0) : ℕ × ℕ × ℕ), ((6, 0, 0) : ℕ × ℕ × ℕ)] := by
    show jk1 2 Jk1.nil ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (2 + 1) Xu) = _
    rw [jk1_Xu 3]
    simp [jk1]
  rw [wordJ_singleton, colJ, e] at hh
  simpa [R600, R375m, R373, R344, R341, R338, List.append_assoc] using hh

#print axioms R600600_mem

/-! ### `R600 (6,0,0)` の `Aok` を取って、族の台座をもう一段上げる -/

def Z600 : TrioSeq := R600 ++ [((6, 0, 0) : ℕ × ℕ × ℕ)]

theorem Z600_eq : Z600 = [((0, 0, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ),
    ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ),
    ((5, 2, 0) : ℕ × ℕ × ℕ),
    ((6, 0, 0) : ℕ × ℕ × ℕ),
    ((6, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [Z600, R600, R375m, R373, R344, R341, R338]

theorem Z600_ne : Z600 ≠ [] := by simp [Z600, R600, R375m, R373, R344, R341, R338]

theorem Z600_head : entry Z600 0 0 = 0 := by
  simp [Z600, R600, R375m, R373, R344, R341, R338, entry]

theorem Z600_tail : ∀ r, 1 ≤ r → r < Z600.length → 1 ≤ entry Z600 0 r := by
  intro r hr1 hrl
  simp only [Z600, R600, R375m, R373, R344, R341, R338, List.length_append,
    List.length_cons, List.length_nil] at hrl
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r <;>
    first
      | omega
      | simp [Z600, R600, R375m, R373, R344, R341, R338, entry]

theorem Aok_Z600 : Aok Z600 where
  mem := R600600_mem
  ne := Z600_ne
  deep := ⟨Z600_head, Z600_tail⟩
  zroot := by
    rw [Z600_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  mono := by
    rw [Z600_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem Z600_1122_mem :
    Z600 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa using Lv_snoc2 1 0 _ (Aok_Z600 : Lv 1 0 Z600)

/-- ★★★★★★ `R600 (6,0,0)` の上、輪を `n` 周した 4 パラメータの無限族。 -/
theorem LoopIt_Z600_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (j n : ℕ) :
    LoopIt Z600 m ws j n ∈ W 0 := (Aok_LoopIt Aok_Z600 m hw j n).mem

theorem LoopIt_Z600_nil_mem (m p j n : ℕ) :
    LoopIt Z600 m (List.replicate p (AltT 0)) j n ∈ W 0 :=
  LoopIt_Z600_mem m (WJ_rep_AltT 0 p) j n

#print axioms Aok_Z600
#print axioms LoopIt_Z600_nil_mem

/-! ### ★★ 走りを文脈に持てる層 `WPdS`

`WPdT` の文脈 `WCtxU` は 2 の枠を必ず `[fone U, ftwo N]` の対で持つので、
`ftwo` が 2 つ続く形（縦の走り）を表せない。そこで枠を 1 つずつに分ける:

    ⊥      … `fone U`（U は下の形で良い）
    e ≠ ⊥  … `ftwo N`（N は「入り目 `< e` の形」で良い）

`ftwo` だけの枠が取れるので `SCtx` の `false` の節（`ftwo nil` の連続）が入る。
しかも兄弟の条件は予算 `e` で抑えられているので DM 測度が効く。
`WPdT` の 2 の節は `[e, ⊥] ++ ks`（`ftwo` の下に `fone`）に対応する。 -/

section EntS

variable {Ent : Type} [LinearOrder Ent] [OrderBot Ent] [WellFoundedLT Ent]

def FrmS : List Ent → Jk1 → Prop
  | [], U => JkT U
  | (_ :: _), U => JkA U

def WPdS {Ent : Type} [LinearOrder Ent] [OrderBot Ent] [WellFoundedLT Ent] :
    List Ent → Jk1 → Prop
  | [], V => GOK V
  | (e :: ks), V =>
      (e = ⊥ → ∀ U : Jk1, FrmS ks U → WPdS ks U → WPdS ks (Jk1.one U V)) ∧
      (e ≠ ⊥ → ∀ (r : List Ent), (∀ x ∈ r, x < e) → ∀ N : Jk1, JkA N →
        (∀ q : List Ent, (∀ x ∈ q, x < e) → WPdS (q ++ (r ++ ks)) N) →
        WPdS (r ++ ks) (Jk1.two N V))
termination_by ks _ => ((ks : List Ent) : Multiset Ent)
decreasing_by
  all_goals
    first
      | exact dmT_cons _ _
      | exact dmT_app ks _ (by assumption)
      | (rw [show q ++ (r ++ ks) = (q ++ r) ++ ks from by simp]
         refine dmT_app ks (q ++ r) ?_
         intro x hx
         rcases List.mem_append.mp hx with h1 | h1
         · exact (by assumption : ∀ x ∈ q, x < e) x h1
         · exact (by assumption : ∀ x ∈ r, x < e) x h1)

theorem WPdS_bnil (V : Jk1) : WPdS ([] : List Ent) V ↔ GOK V := by rw [WPdS]

theorem WPdS_cons (e : Ent) (ks : List Ent) (V : Jk1) :
    WPdS (e :: ks) V ↔
      (e = ⊥ → ∀ U : Jk1, FrmS ks U → WPdS ks U → WPdS ks (Jk1.one U V)) ∧
      (e ≠ ⊥ → ∀ (r : List Ent), (∀ x ∈ r, x < e) → ∀ N : Jk1, JkA N →
        (∀ q : List Ent, (∀ x ∈ q, x < e) → WPdS (q ++ (r ++ ks)) N) →
        WPdS (r ++ ks) (Jk1.two N V)) := by
  rw [WPdS]

/-- `⊥` の節（1 の枠）。 -/
theorem WPdS_c1 (ks : List Ent) (V : Jk1) :
    WPdS ((⊥ : Ent) :: ks) V ↔
      ∀ U : Jk1, FrmS ks U → WPdS ks U → WPdS ks (Jk1.one U V) := by
  rw [WPdS_cons]
  exact ⟨fun h => h.1 rfl, fun h => ⟨fun _ => h, fun hne => absurd rfl hne⟩⟩

/-- `e ≠ ⊥` の節（裸の 2 の枠）。 -/
theorem WPdS_c2 {e : Ent} (he : e ≠ ⊥) (ks : List Ent) (V : Jk1) :
    WPdS (e :: ks) V ↔
      ∀ (r : List Ent), (∀ x ∈ r, x < e) → ∀ N : Jk1, JkA N →
        (∀ q : List Ent, (∀ x ∈ q, x < e) → WPdS (q ++ (r ++ ks)) N) →
        WPdS (r ++ ks) (Jk1.two N V) := by
  rw [WPdS_cons]
  exact ⟨fun h => h.2 he, fun h => ⟨fun hb => absurd hb he, fun _ => h⟩⟩

def WCtxS {Ent : Type} [LinearOrder Ent] [OrderBot Ent] [WellFoundedLT Ent] :
    List Ent → List Frm → Prop
  | [], ctx => ctx = []
  | (e :: ks), ctx =>
      (e = ⊥ → ∃ (ctx' : List Frm) (U : Jk1), ctx = ctx' ++ [Frm.fone U] ∧
        WCtxS ks ctx' ∧ FrmS ks U ∧ WPdS ks U) ∧
      (e ≠ ⊥ → ∃ (r : List Ent) (_ : ∀ x ∈ r, x < e) (ctx' : List Frm) (N : Jk1),
        ctx = ctx' ++ [Frm.ftwo N] ∧ WCtxS (r ++ ks) ctx' ∧ JkA N ∧
        (∀ q : List Ent, (∀ x ∈ q, x < e) → WPdS (q ++ (r ++ ks)) N))
termination_by ks _ => ((ks : List Ent) : Multiset Ent)
decreasing_by
  all_goals
    first
      | exact dmT_cons _ _
      | exact dmT_app ks _ (by assumption)

theorem WCtxS_bnil (ctx : List Frm) : WCtxS ([] : List Ent) ctx ↔ ctx = [] := by
  rw [WCtxS]

theorem WCtxS_c1 (ks : List Ent) (ctx : List Frm) :
    WCtxS ((⊥ : Ent) :: ks) ctx ↔ ∃ (ctx' : List Frm) (U : Jk1),
      ctx = ctx' ++ [Frm.fone U] ∧ WCtxS ks ctx' ∧ FrmS ks U ∧ WPdS ks U := by
  rw [WCtxS]
  exact ⟨fun h => h.1 rfl, fun h => ⟨fun _ => h, fun hne => absurd rfl hne⟩⟩

theorem WCtxS_c2 {e : Ent} (he : e ≠ ⊥) (ks : List Ent) (ctx : List Frm) :
    WCtxS (e :: ks) ctx ↔ ∃ (r : List Ent) (_ : ∀ x ∈ r, x < e) (ctx' : List Frm) (N : Jk1),
      ctx = ctx' ++ [Frm.ftwo N] ∧ WCtxS (r ++ ks) ctx' ∧ JkA N ∧
      (∀ q : List Ent, (∀ x ∈ q, x < e) → WPdS (q ++ (r ++ ks)) N) := by
  rw [WCtxS]
  exact ⟨fun h => h.2 he, fun h => ⟨fun hb => absurd hb he, fun _ => h⟩⟩

theorem WPdS_iff : ∀ (ks : List Ent) (V : Jk1),
    WPdS ks V ↔ ∀ ctx : List Frm, WCtxS ks ctx → GOK (plug ctx V)
  | [], V => by
      rw [WPdS_bnil]
      constructor
      · intro h ctx hc
        rw [WCtxS_bnil] at hc
        subst hc
        exact h
      · intro h
        exact h [] ((WCtxS_bnil ([] : List Frm)).mpr rfl)
  | (e :: ks), V => by
      by_cases he : e = ⊥
      · subst he
        rw [WPdS_c1]
        constructor
        · intro h ctx hc
          rw [WCtxS_c1] at hc
          obtain ⟨ctx', U, rfl, hc', hU, hUk⟩ := hc
          rw [plug_snoc]
          exact (WPdS_iff ks (Jk1.one U V)).mp (h U hU hUk) ctx' hc'
        · intro h U hU hUk
          refine (WPdS_iff ks (Jk1.one U V)).mpr ?_
          intro ctx' hc'
          rw [← plug_snoc]
          exact h (ctx' ++ [Frm.fone U]) ((WCtxS_c1 ks _).mpr ⟨ctx', U, rfl, hc', hU, hUk⟩)
      · rw [WPdS_c2 he]
        constructor
        · intro h ctx hc
          rw [WCtxS_c2 he] at hc
          obtain ⟨r, hr, ctx', N, rfl, hc', hJN, hNt⟩ := hc
          rw [plug_snoc2]
          exact (WPdS_iff (r ++ ks) _).mp (h r hr N hJN hNt) ctx' hc'
        · intro h r hr N hJN hNt
          refine (WPdS_iff (r ++ ks) _).mpr ?_
          intro ctx' hc'
          rw [← plug_snoc2]
          exact h (ctx' ++ [Frm.ftwo N])
            ((WCtxS_c2 he ks _).mpr ⟨r, hr, ctx', N, rfl, hc', hJN, hNt⟩)
termination_by ks _ => ((ks : List Ent) : Multiset Ent)
decreasing_by
  all_goals
    first
      | exact dmT_cons _ _
      | exact dmT_app ks _ (by assumption)

theorem WPdS_congr : ∀ (ks : List Ent) {V1 V2 : Jk1},
    (∀ l, jk1 l V1 = jk1 l V2) → WPdS ks V1 → WPdS ks V2 := by
  intro ks V1 V2 h hA
  rw [WPdS_iff] at hA ⊢
  intro ctx hc
  exact GOK_congr (jk1_plug_congr ctx h) (hA ctx hc)

#print axioms WPdS
#print axioms WPdS_iff

/-! ### 形の妥当性 `SqOk`

一番外の枠が裸の `ftwo` だと行が 2 の記録で始まってしまう。
形の**末尾**（＝一番外）は `⊥` でなければならない。 -/

def SqOk : List Ent → Prop
  | [] => True
  | (e :: ks) => (ks = [] → e = ⊥) ∧ SqOk ks

theorem SqOk_nil : SqOk ([] : List Ent) := trivial

theorem SqOk_tail {e : Ent} {ks : List Ent} (h : SqOk (e :: ks)) : SqOk ks := h.2

theorem SqOk_ne {e : Ent} (he : e ≠ ⊥) {ks : List Ent} (h : SqOk (e :: ks)) : ks ≠ [] :=
  fun hnil => he (h.1 hnil)

theorem SqOk_cons_bot {ks : List Ent} (h : SqOk ks) : SqOk ((⊥ : Ent) :: ks) :=
  ⟨fun _ => rfl, h⟩

theorem SqOk_cons {e : Ent} {ks : List Ent} (hne : ks ≠ []) (h : SqOk ks) :
    SqOk (e :: ks) := ⟨fun hnil => absurd hnil hne, h⟩

theorem SqOk_append : ∀ (r ks : List Ent), ks ≠ [] → SqOk ks → SqOk (r ++ ks)
  | [], _, _, h => h
  | (a :: r), ks, hne, h => by
      refine SqOk_cons ?_ (SqOk_append r ks hne h)
      intro hc
      rcases List.append_eq_nil_iff.mp hc with ⟨-, h2⟩
      exact hne h2

#print axioms SqOk_append

/-! ### `WPdS` 層の小さい補題 -/

theorem FrmS_ne {ks : List Ent} (h : ks ≠ []) (X : Jk1) : FrmS ks X ↔ JkA X := by
  cases ks with
  | nil => exact absurd rfl h
  | cons a l => exact Iff.rfl

theorem FrmS_JkA : ∀ (ks : List Ent) (U : Jk1), FrmS ks U → JkA U
  | [], _, h => h.1
  | (_ :: _), _, h => h

theorem FrmS_nilA : ∀ ks : List Ent, FrmS ks Jk1.nil
  | [] => JkT_nil
  | (_ :: _) => trivial

theorem FrmS_one (ks : List Ent) (U X : Jk1) (hU : FrmS ks U) (hX : JkA X) :
    FrmS ks (Jk1.one U X) := by
  cases ks with
  | nil => exact ⟨⟨hU.1, hX⟩, hU.2⟩
  | cons b bs => exact ⟨hU, hX⟩

/-- `⊥` の節から `one` を継ぐ。 -/
theorem WPdS_step (ks : List Ent) {V W : Jk1} (hV : FrmS ks V) (hVk : WPdS ks V)
    (hW : WPdS ((⊥ : Ent) :: ks) W) : WPdS ks (Jk1.one V W) :=
  (WPdS_c1 ks W).mp hW V hV hVk

theorem WCtxS_fone {ks : List Ent} {ctx : List Frm} {U : Jk1}
    (hc : WCtxS ks ctx) (hU : FrmS ks U) (hUk : WPdS ks U) :
    WCtxS ((⊥ : Ent) :: ks) (ctx ++ [Frm.fone U]) :=
  (WCtxS_c1 ks _).mpr ⟨ctx, U, rfl, hc, hU, hUk⟩

theorem WCtxS_ftwo {e : Ent} (he : e ≠ ⊥) {ks : List Ent} {ctx : List Frm} {N : Jk1}
    (hc : WCtxS ks ctx) (hJN : JkA N)
    (hNt : ∀ q : List Ent, (∀ x ∈ q, x < e) → WPdS (q ++ ks) N) :
    WCtxS (e :: ks) (ctx ++ [Frm.ftwo N]) :=
  (WCtxS_c2 he ks _).mpr ⟨[], by simp, ctx, N, rfl, by simpa using hc, hJN,
    by simpa using hNt⟩

theorem WCtxS_JkT : ∀ (ks : List Ent), SqOk ks → ∀ ctx : List Frm, WCtxS ks ctx →
    ∀ X : Jk1, FrmS ks X → JkT (plug ctx X)
  | [], _, ctx, h, X, hX => by
      rw [WCtxS_bnil] at h
      subst h
      exact hX
  | (e :: ks), hs, ctx, h, X, hX => by
      by_cases he : e = ⊥
      · subst he
        rw [WCtxS_c1] at h
        obtain ⟨ctx', U, rfl, hc', hU, -⟩ := h
        rw [plug_snoc]
        exact WCtxS_JkT ks (SqOk_tail hs) ctx' hc' (Jk1.one U X) (FrmS_one ks U X hU hX)
      · have hkne : ks ≠ [] := SqOk_ne he hs
        rw [WCtxS_c2 he] at h
        obtain ⟨r, hr, ctx', N, rfl, hc', hJN, -⟩ := h
        have hrk : r ++ ks ≠ [] := by
          intro hc
          exact hkne (List.append_eq_nil_iff.mp hc).2
        rw [plug_snoc2]
        exact WCtxS_JkT (r ++ ks) (SqOk_append r ks hkne (SqOk_tail hs)) ctx' hc'
          (Jk1.two N X) ((FrmS_ne hrk _).mpr ⟨hJN, hX⟩)
termination_by ks _ => ((ks : List Ent) : Multiset Ent)
decreasing_by
  all_goals
    first
      | exact dmT_cons _ _
      | exact dmT_app ks _ (by assumption)

theorem WCtxS_split (ks : List Ent) (ctx : List Frm)
    (h : WCtxS ((⊥ : Ent) :: ks) ctx) :
    ∃ (ctx0 : List Frm) (V : Jk1), ctx = ctx0 ++ [Frm.fone V] ∧ WCtxS ks ctx0 ∧
      FrmS ks V ∧ GOK (plug ctx0 V) := by
  rw [WCtxS_c1] at h
  obtain ⟨ctx', U, rfl, hc', hU, hUk⟩ := h
  exact ⟨ctx', U, rfl, hc', hU, (WPdS_iff ks U).mp hUk ctx' hc'⟩

/-- 形の付け足し。 -/
theorem WPdS_shift {e : Ent} (he : e ≠ ⊥) {ks : List Ent} {T : Jk1}
    (h : WPdS (e :: ks) T) (a : List Ent) (ha : ∀ x ∈ a, x < e) :
    WPdS (e :: (a ++ ks)) T := by
  rw [WPdS_c2 he]
  intro r hr N hJN hNt
  have e2 : r ++ (a ++ ks) = (r ++ a) ++ ks := (List.append_assoc r a ks).symm
  rw [e2] at hNt ⊢
  refine (WPdS_c2 he ks T).mp h (r ++ a) ?_ N hJN hNt
  intro x hx
  rcases List.mem_append.mp hx with h1 | h1
  · exact hr x h1
  · exact ha x h1

#print axioms WCtxS_JkT
#print axioms WPdS_shift

/-! ### `⊥` の節の塔（`WPdT_twoNilGen` の移植） -/

theorem FrmS_repB (m : ℕ) (e : Ent) (ks : List Ent) (N : Jk1) :
    FrmS (List.replicate m (⊥ : Ent) ++ (e :: ks)) N ↔ JkA N := by
  cases m with
  | zero => exact Iff.rfl
  | succ m => exact Iff.rfl

theorem WCtxS_rep {N : Jk1} (hJN : JkA N) (ks : List Ent)
    (hNall : ∀ j : ℕ, WPdS (List.replicate j (⊥ : Ent) ++ ((⊥ : Ent) :: ks)) N) :
    ∀ (m : ℕ) (ctx : List Frm), WCtxS ((⊥ : Ent) :: ks) ctx →
      WCtxS (List.replicate m (⊥ : Ent) ++ ((⊥ : Ent) :: ks))
        (ctx ++ List.replicate m (Frm.fone N))
  | 0, ctx, hc => by simpa using hc
  | (m + 1), ctx, hc => by
      have h1 := WCtxS_rep hJN ks hNall m ctx hc
      have e : ctx ++ List.replicate (m + 1) (Frm.fone N)
          = (ctx ++ List.replicate m (Frm.fone N)) ++ [Frm.fone N] := by
        rw [List.replicate_succ']
        simp
      rw [e, repB_succ_cons, WCtxS_c1]
      exact ⟨ctx ++ List.replicate m (Frm.fone N), N, rfl, h1,
        (FrmS_repB m (⊥ : Ent) ks N).mpr hJN, hNall m⟩

theorem WPdS_plug_rep (N : Jk1) (hJN : JkA N) (ks : List Ent)
    (hNall : ∀ j : ℕ, WPdS (List.replicate j (⊥ : Ent) ++ ((⊥ : Ent) :: ks)) N) (m : ℕ) :
    WPdS ((⊥ : Ent) :: ks) (plug (List.replicate m (Frm.fone N)) N) := by
  rw [WPdS_iff]
  intro ctx hc
  rw [← plug_append]
  exact (WPdS_iff _ N).mp (hNall m) _ (WCtxS_rep hJN ks hNall m ctx hc)

theorem WPdS_twoNilGen {N : Jk1} (hJN : JkA N) (ks : List Ent) (hs : SqOk ks)
    (hNall : ∀ j : ℕ, WPdS (List.replicate j (⊥ : Ent) ++ ((⊥ : Ent) :: ks)) N) :
    WPdS ((⊥ : Ent) :: ks) (Jk1.two N Jk1.nil) := by
  rw [WPdS_iff]
  intro ctx hc
  obtain ⟨ctx0, V, rfl, hc0, hV, hGV⟩ := WCtxS_split ks ctx hc
  exact GOK_twoNilW_gen ctx0 V hJN
    (WCtxS_JkT ((⊥ : Ent) :: ks) (SqOk_cons_bot hs) _ hc (Jk1.two N Jk1.nil)
      (⟨hJN, trivial⟩ : FrmS ((⊥ : Ent) :: ks) (Jk1.two N Jk1.nil)))
    hGV
    (fun m => (WPdS_iff ((⊥ : Ent) :: ks) _).mp (WPdS_plug_rep N hJN ks hNall m) _ hc)

#print axioms WPdS_twoNilGen

end EntS

/-! ### 予算型 `Bw = Colex (ℕ →₀ ℕ)`（順序型 ω^ω）

`ow k m` が `ω^k · m`。荷が `k` 段入れ子になると走りの入れ子も `k` 段になり、
予算が `ω^k` 要る。全部の `k` を一様に扱うには `ω^ω` が要る。 -/

abbrev Bw : Type := Colex (ℕ →₀ ℕ)

noncomputable def ow (k m : ℕ) : Bw := toColex (Finsupp.single k m)

theorem bot_Bw : (⊥ : Bw) = 0 := rfl

theorem ow_zero (k : ℕ) : ow k 0 = (⊥ : Bw) := by
  show toColex (Finsupp.single k 0) = toColex (0 : ℕ →₀ ℕ)
  rw [Finsupp.single_zero]

theorem ow_ltR (k : ℕ) {m m' : ℕ} (h : m < m') : ow k m < ow k m' := by
  rw [ow, ow, Finsupp.Colex.lt_iff]
  refine ⟨k, ?_, ?_⟩
  · intro j hj
    show (Finsupp.single k m : ℕ →₀ ℕ) j = (Finsupp.single k m' : ℕ →₀ ℕ) j
    rw [Finsupp.single_apply, Finsupp.single_apply, if_neg (by omega : ¬ k = j),
      if_neg (by omega : ¬ k = j)]
  · show (Finsupp.single k m : ℕ →₀ ℕ) k < (Finsupp.single k m' : ℕ →₀ ℕ) k
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    exact h

theorem ow_ltL {k k' : ℕ} (h : k < k') (m : ℕ) {m' : ℕ} (hm : 0 < m') :
    ow k m < ow k' m' := by
  rw [ow, ow, Finsupp.Colex.lt_iff]
  refine ⟨k', ?_, ?_⟩
  · intro j hj
    show (Finsupp.single k m : ℕ →₀ ℕ) j = (Finsupp.single k' m' : ℕ →₀ ℕ) j
    rw [Finsupp.single_apply, Finsupp.single_apply, if_neg (by omega : ¬ k = j),
      if_neg (by omega : ¬ k' = j)]
  · show (Finsupp.single k m : ℕ →₀ ℕ) k' < (Finsupp.single k' m' : ℕ →₀ ℕ) k'
    rw [Finsupp.single_apply, Finsupp.single_eq_same, if_neg (by omega : ¬ k = k')]
    exact hm

theorem ow_add_lt {j k : ℕ} (h : j < k) (m m' : ℕ) :
    ow k m + ow j m' < ow k (m + 1) := by
  rw [Finsupp.Colex.lt_iff]
  refine ⟨k, ?_, ?_⟩
  · intro i hi
    show (Finsupp.single k m + Finsupp.single j m' : ℕ →₀ ℕ) i
        = (Finsupp.single k (m + 1) : ℕ →₀ ℕ) i
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (by omega : ¬ k = i), if_neg (by omega : ¬ j = i), if_neg (by omega : ¬ k = i)]
    rfl
  · show (Finsupp.single k m + Finsupp.single j m' : ℕ →₀ ℕ) k
        < (Finsupp.single k (m + 1) : ℕ →₀ ℕ) k
    rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply,
      Finsupp.single_eq_same, if_neg (by omega : ¬ j = k)]
    omega

theorem Bw_add_lt_left (b : Bw) {x y : Bw} (h : x < y) : b + x < b + y := by
  rw [add_comm b x, add_comm b y]
  exact add_lt_add_left h b

#print axioms ow_add_lt

/-! ### 荷を `k` 段入れ子にした木 `Zk k` -/

def Zk : ℕ → Jk1
  | 0 => Jk1.nil
  | (k + 1) => Jk1.pay (Zk k) [((0, 0, 0) : ℕ × ℕ × ℕ)]

theorem JkA_Zk : ∀ k : ℕ, JkA (Zk k)
  | 0 => trivial
  | (k + 1) => ⟨JkA_Zk k, Bok_zero⟩

theorem jk1_Zk : ∀ (k l : ℕ), jk1 l (Zk k) = List.replicate k ((l + 1, 0, 0) : ℕ × ℕ × ℕ)
  | 0, _ => rfl
  | (k + 1), l => by
      show jk1 l (Zk k) ++ shiftr01 (l + 1) 0 [((0, 0, 0) : ℕ × ℕ × ℕ)] = _
      rw [jk1_Zk k l, List.replicate_succ']
      simp [shiftr01]

theorem WPdT_Zk {Bud : Type} [LinearOrder Bud] [OrderBot Bud] [WellFoundedLT Bud] :
    ∀ (k : ℕ) (c : Bud) (ks : List Bud), WPdT (c :: ks) (Zk k)
  | 0, c, ks => WPdT_nilAll _
  | (k + 1), c, ks =>
      WPdT_payA (c :: ks) (Zk k) (JkA_Zk k) (WPdT_Zk k c ks) _ Bok_zero

/-- ★★★ `Zk k` を上に乗せた平らな走り `twoIt A (Zk k) m` は、
底 `A` の閾値 `β` の上 `β + ω^k·m` を超える予算に置ける。 -/
theorem WPdw_run : ∀ (k : ℕ) (β : Bw) (A : Jk1), JkA A →
    (∀ c : Bw, β < c → ∀ ks : List Bw, WPdT (c :: ks) A) →
    ∀ (m : ℕ) (c : Bw), β + ow k m < c → ∀ ks : List Bw,
      WPdT (c :: ks) (twoIt A (Zk k) m)
  | 0, β, A, _, hA, 0, c, hc, ks => hA c (by rwa [ow_zero, bot_Bw, add_zero] at hc) ks
  | (k + 1), β, A, _, hA, 0, c, hc, ks => hA c (by rwa [ow_zero, bot_Bw, add_zero] at hc) ks
  | 0, β, A, hJA, hA, (m + 1), c, hc, ks => by
      have hstep : β + ow 0 m < β + ow 0 (m + 1) := Bw_add_lt_left β (ow_ltR 0 (by omega))
      refine WPdT_twoA_runB (a := β + ow 0 (m + 1))
        (ne_bot_of_gt (lt_of_le_of_lt bot_le hstep)) hc
        (JkA_twoItP hJA (JkA_Zk 0) m) ?_ ks
      intro ks'
      exact WPdw_run 0 β A hJA hA m (β + ow 0 (m + 1)) hstep ks'
  | (k + 1), β, A, hJA, hA, (m + 1), c, hc, ks => by
      have hstep : β + ow (k + 1) m < β + ow (k + 1) (m + 1) :=
        Bw_add_lt_left β (ow_ltR (k + 1) (by omega))
      have hJA' : JkA (twoIt A (Zk (k + 1)) m) := JkA_twoItP hJA (JkA_Zk (k + 1)) m
      have hA' : ∀ c' : Bw, β + ow (k + 1) m < c' → ∀ ks' : List Bw,
          WPdT (c' :: ks') (twoIt A (Zk (k + 1)) m) :=
        fun c' hc' ks' => WPdw_run (k + 1) β A hJA hA m c' hc' ks'
      refine WPdT_twoAZ_top
        (S := ⟨fun i => (β + ow (k + 1) m) + ow k i,
          fun _ _ hij => Bw_add_lt_left _ (ow_ltR k hij)⟩)
        (t := c) ?_ hJA' (JkA_Zk k) ?_ ks
      · intro i
        show (β + ow (k + 1) m) + ow k i < c
        rw [add_assoc]
        exact lt_trans (Bw_add_lt_left β (ow_add_lt (by omega : k < k + 1) m i)) hc
      · intro m' c' hc' ks'
        exact WPdw_run k (β + ow (k + 1) m) (twoIt A (Zk (k + 1)) m) hJA' hA' m' c' hc' ks'
termination_by k _ _ _ _ m _ _ _ => (k, m)

#print axioms WPdw_run

/-! ### ★★★★★★★ `R600 ++ (6,0,0)^k`（全部の `k`） -/

def Xw (k : ℕ) : Jk1 := Jk1.two Jk1.nil (Jk1.two Jk1.nil (Zk (k + 1)))

theorem ow_pos_ne_bot (k m : ℕ) (hm : 0 < m) : ow (k + 1) m ≠ (⊥ : Bw) :=
  ne_bot_of_gt (show (⊥ : Bw) < ow (k + 1) m by
    rw [← ow_zero 0]
    exact ow_ltL (by omega) 0 hm)

theorem WPdw_twoZk (k : ℕ) (ks : List Bw) :
    WPdT (ow (k + 1) 1 :: ks) (Jk1.two Jk1.nil (Zk (k + 1))) := by
  refine WPdT_twoAZ_top (S := ⟨fun i => ow k i, fun _ _ hij => ow_ltR k hij⟩)
    (t := ow (k + 1) 1) (A := Jk1.nil) (Z := Zk k) ?_ trivial (JkA_Zk k) ?_ ks
  · intro i
    exact ow_ltL (by omega) i (by omega)
  · intro m c hc ks'
    exact WPdw_run k ⊥ Jk1.nil trivial (fun c' _ ks'' => WPdT_nilAll _) m c
      (by rwa [bot_Bw, zero_add]) ks'

theorem WPdw_Xw (k : ℕ) (ks : List Bw) : WPdT ((⊥ : Bw) :: ks) (Xw k) :=
  WPdT_twoOf (b := ow (k + 1) 1) (ow_pos_ne_bot k 1 (by omega)) trivial
    (fun q _ => WPdT_nilAll _) (WPdw_twoZk k ks)

theorem GOK_oneXw (k : ℕ) : GOK (Jk1.one Jk1.nil (Xw k)) :=
  (WPdT_bnil (Bud := Bw) _).mp
    (WPdT_step ([] : List Bw) (JkT_nil : FrmNT ([] : List Bw) Jk1.nil)
      ((WPdT_bnil (Bud := Bw) _).mpr GOK_nil) (WPdw_Xw k []))

theorem jk1_Xw (k l : ℕ) : jk1 l (Xw k)
    = ((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: ((l + 2, 2, 0) : ℕ × ℕ × ℕ)
      :: List.replicate (k + 1) ((l + 3, 0, 0) : ℕ × ℕ × ℕ) := by
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 2) (Zk (k + 1))))) = _
  rw [jk1_Zk (k + 1) (l + 2), show l + 2 + 1 = l + 3 from by omega]
  simp [jk1]

theorem R600_600rep_mem (k : ℕ) :
    R600 ++ List.replicate k ((6, 0, 0) : ℕ × ℕ × ℕ) ∈ W 0 := by
  have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (Xw k)]) := by
    simpa using GOK_oneXw k [] WOk_nil GoodFb_wordJ_nil
  have hh := rowJ_mem_genF Aok_R338 hG
  have e : jk1 2 (Jk1.one Jk1.nil (Xw k))
      = ((3, 1, 0) : ℕ × ℕ × ℕ) :: ((4, 2, 0) : ℕ × ℕ × ℕ) :: ((5, 2, 0) : ℕ × ℕ × ℕ)
        :: List.replicate (k + 1) ((6, 0, 0) : ℕ × ℕ × ℕ) := by
    show jk1 2 Jk1.nil ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (2 + 1) (Xw k)) = _
    rw [jk1_Xw k 3]
    simp [jk1]
  rw [wordJ_singleton, colJ, e] at hh
  simpa [R600, R375m, R373, R344, R341, R338, List.replicate_succ,
    List.append_assoc] using hh

#print axioms R600_600rep_mem

/-- ★★★★★★★ `R600 (7,0,0)`:
`(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,0,0)(7,0,0)` -/
theorem R600700_mem : R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hne : [((6, 0, 0) : ℕ × ℕ × ℕ)] ≠ [] := by simp
  have hhead : entry [((6, 0, 0) : ℕ × ℕ × ℕ)] 0 0 < 7 := by simp [entry]
  have htail : ∀ r, 1 ≤ r → r < ([((6, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq).length →
      7 ≤ entry [((6, 0, 0) : ℕ × ℕ × ℕ)] 0 r := by
    intro r hr1 hr2
    simp only [List.length_singleton] at hr2
    omega
  have htw : ∀ n : ℕ, R375m ++ (List.range n).flatMap
      (fun _ => [((6, 0, 0) : ℕ × ℕ × ℕ)]) ∈ W 0 := by
    intro n
    rw [flatMap_singleton_range]
    cases n with
    | zero => simpa using R375m_mem
    | succ n =>
        have h := R600_600rep_mem n
        rw [R600] at h
        simpa [List.replicate_succ, List.append_assoc] using h
  have hmem := flat_mem'' (Y0 := R375m) (M := [((6, 0, 0) : ℕ × ℕ × ℕ)]) (d := 7)
    hne hhead htail htw
  simpa [R600, List.append_assoc] using hmem

#print axioms R600700_mem

/-! ### `R600 (7,0,0)` の `Aok` を取って、族の台座をもう一段上げる -/

def Z700 : TrioSeq := R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ)]

theorem Z700_eq : Z700 = [((0, 0, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ),
    ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ),
    ((5, 2, 0) : ℕ × ℕ × ℕ),
    ((6, 0, 0) : ℕ × ℕ × ℕ),
    ((7, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [Z700, R600, R375m, R373, R344, R341, R338]

theorem Z700_ne : Z700 ≠ [] := by simp [Z700, R600, R375m, R373, R344, R341, R338]

theorem Z700_head : entry Z700 0 0 = 0 := by
  simp [Z700, R600, R375m, R373, R344, R341, R338, entry]

theorem Z700_tail : ∀ r, 1 ≤ r → r < Z700.length → 1 ≤ entry Z700 0 r := by
  intro r hr1 hrl
  simp only [Z700, R600, R375m, R373, R344, R341, R338, List.length_append,
    List.length_cons, List.length_nil] at hrl
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r <;>
    first
      | omega
      | simp [Z700, R600, R375m, R373, R344, R341, R338, entry]

theorem Aok_Z700 : Aok Z700 where
  mem := R600700_mem
  ne := Z700_ne
  deep := ⟨Z700_head, Z700_tail⟩
  zroot := by
    rw [Z700_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  mono := by
    rw [Z700_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem Z700_1122_mem :
    Z700 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa using Lv_snoc2 1 0 _ (Aok_Z700 : Lv 1 0 Z700)

/-- ★★★★★★ `R600 (7,0,0)` の上、輪を `n` 周した 4 パラメータの無限族。 -/
theorem LoopIt_Z700_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (j n : ℕ) :
    LoopIt Z700 m ws j n ∈ W 0 := (Aok_LoopIt Aok_Z700 m hw j n).mem

theorem LoopIt_Z700_nil_mem (m p j n : ℕ) :
    LoopIt Z700 m (List.replicate p (AltT 0)) j n ∈ W 0 :=
  LoopIt_Z700_mem m (WJ_rep_AltT 0 p) j n

#print axioms Aok_Z700
#print axioms LoopIt_Z700_nil_mem

/-! ### ★★ 枠の単位を「`fone` ＋ 走り」にした層 `WPdR`

`WPdS`（追記383）は枠を 1 つずつに分けたが、塔の階段が足すブロック

    [fone nil, ftwo N] ++ replicate p (ftwo nil)

が複数の入り目にまたがるので、兄弟の条件の尻が合わなくなった（追記384）。
ブロックを**1 つの入り目**にすれば合う。入り目は `(b, p) : Bud ×ₗ ℕ`:

    ⊥ = (⊥, 0)   … `[fone U]`
    (b, p)       … `[fone U, ftwo N] ++ replicate p (ftwo nil)`（N は予算 `< (b,p)`）

`p = 0` が `WPdT` の節。`p ≥ 1` で縦の走りが入る。
階段のブロックは入り目 `(b', p)`（`b' < b`）なので DM 測度が減る。 -/

section EkeyR

variable {Bud : Type} [LinearOrder Bud] [OrderBot Bud] [WellFoundedLT Bud]

abbrev Ekey (Bud : Type) [LinearOrder Bud] : Type := Bud ×ₗ ℕ

def erun (e : Ekey Bud) : ℕ := (ofLex e).2

def ebud (e : Ekey Bud) : Bud := (ofLex e).1

theorem bot_lt_ekey {e : Ekey Bud} (h : ebud e ≠ ⊥) : (⊥ : Ekey Bud) < e :=
  Prod.Lex.left 0 (erun e) (Ne.bot_lt' (Ne.symm h))

theorem ekey_ne_bot {e : Ekey Bud} (h : ebud e ≠ ⊥) : e ≠ ⊥ :=
  ne_bot_of_gt (bot_lt_ekey h)

theorem ekey_eq_bot {e : Ekey Bud} (h1 : ebud e = ⊥) (h2 : erun e = 0) : e = ⊥ := by
  have he : ofLex e = ((⊥ : Bud), 0) := Prod.ext h1 h2
  show toLex (ofLex e) = ⊥
  rw [he]
  rfl

theorem ebud_key (b : Bud) (p : ℕ) : ebud (toLex (b, p) : Ekey Bud) = b := rfl

def FrmR : List (Ekey Bud) → Jk1 → Prop := fun _ U => JkA U

def WPdR {Bud : Type} [LinearOrder Bud] [OrderBot Bud] [WellFoundedLT Bud] :
    List (Ekey Bud) → Jk1 → Prop
  | [], V => ∀ (bs : List Bool) (ctx : List Frm), GCtx (true :: bs) ctx → GOK (plug ctx V)
  | (e :: ks), V =>
      (e = ⊥ → ∀ U : Jk1, FrmR ks U → WPdR ks U → WPdR ks (Jk1.one U V)) ∧
      (ebud e = ⊥ → e ≠ ⊥ → WPdR ks (stkP (erun e) V)) ∧
      (ebud e ≠ ⊥ → ∀ (r : List (Ekey Bud)), (∀ x ∈ r, x < e) → ∀ (U N : Jk1),
        FrmR (r ++ ks) U → WPdR (r ++ ks) U → JkA N →
        (∀ q : List (Ekey Bud), (∀ x ∈ q, x < e) →
          WPdR ((⊥ : Ekey Bud) :: q ++ (r ++ ks)) N) →
        WPdR (r ++ ks) (Jk1.one U (Jk1.two N (stkP (erun e) V))))
termination_by ks _ => ((ks : List (Ekey Bud)) : Multiset (Ekey Bud))
decreasing_by
  all_goals
    first
      | exact dmT_cons _ _
      | exact dmT_app ks _ (by assumption)
      | (rw [show (⊥ : Ekey Bud) :: q ++ (r ++ ks)
              = ((⊥ : Ekey Bud) :: (q ++ r)) ++ ks from by simp]
         refine dmT_app ks ((⊥ : Ekey Bud) :: (q ++ r)) ?_
         intro x hx
         simp only [List.mem_cons, List.mem_append] at hx
         rcases hx with h1 | h1 | h1
         · subst h1
           exact bot_lt_ekey (by assumption)
         · exact (by assumption : ∀ x ∈ q, x < e) x h1
         · exact (by assumption : ∀ x ∈ r, x < e) x h1)

theorem WPdR_bnil0 (V : Jk1) :
    WPdR ([] : List (Ekey Bud)) V ↔
      ∀ (bs : List Bool) (ctx : List Frm), GCtx (true :: bs) ctx → GOK (plug ctx V) := by
  rw [WPdR]

theorem WPdR_cons (e : Ekey Bud) (ks : List (Ekey Bud)) (V : Jk1) :
    WPdR (e :: ks) V ↔
      (e = ⊥ → ∀ U : Jk1, FrmR ks U → WPdR ks U → WPdR ks (Jk1.one U V)) ∧
      (ebud e = ⊥ → e ≠ ⊥ → WPdR ks (stkP (erun e) V)) ∧
      (ebud e ≠ ⊥ → ∀ (r : List (Ekey Bud)), (∀ x ∈ r, x < e) → ∀ (U N : Jk1),
        FrmR (r ++ ks) U → WPdR (r ++ ks) U → JkA N →
        (∀ q : List (Ekey Bud), (∀ x ∈ q, x < e) →
          WPdR ((⊥ : Ekey Bud) :: q ++ (r ++ ks)) N) →
        WPdR (r ++ ks) (Jk1.one U (Jk1.two N (stkP (erun e) V)))) := by
  rw [WPdR]

theorem WPdR_c0 (ks : List (Ekey Bud)) (V : Jk1) :
    WPdR ((⊥ : Ekey Bud) :: ks) V ↔
      ∀ U : Jk1, FrmR ks U → WPdR ks U → WPdR ks (Jk1.one U V) := by
  rw [WPdR_cons]
  refine ⟨fun h => h.1 rfl, fun h => ⟨fun _ => h, fun _ hne => absurd rfl hne, ?_⟩⟩
  intro hne
  exact absurd rfl hne

/-- 裸の走りの節。 -/
theorem WPdR_cf {e : Ekey Bud} (hb : ebud e = ⊥) (he : e ≠ ⊥) (ks : List (Ekey Bud))
    (V : Jk1) : WPdR (e :: ks) V ↔ WPdR ks (stkP (erun e) V) := by
  rw [WPdR_cons]
  refine ⟨fun h => h.2.1 hb he, fun h => ⟨fun h1 => absurd h1 he, fun _ _ => h, ?_⟩⟩
  intro hne
  exact absurd hb hne

theorem WPdR_cb {e : Ekey Bud} (he : ebud e ≠ ⊥) (ks : List (Ekey Bud)) (V : Jk1) :
    WPdR (e :: ks) V ↔
      ∀ (r : List (Ekey Bud)), (∀ x ∈ r, x < e) → ∀ (U N : Jk1),
        FrmR (r ++ ks) U → WPdR (r ++ ks) U → JkA N →
        (∀ q : List (Ekey Bud), (∀ x ∈ q, x < e) →
          WPdR ((⊥ : Ekey Bud) :: q ++ (r ++ ks)) N) →
        WPdR (r ++ ks) (Jk1.one U (Jk1.two N (stkP (erun e) V))) := by
  rw [WPdR_cons]
  refine ⟨fun h => h.2.2 he, fun h => ⟨fun h1 => absurd ?_ he, fun hb => absurd hb he, fun _ => h⟩⟩
  · rw [h1]
    rfl

#print axioms WPdR

def WCtxR {Bud : Type} [LinearOrder Bud] [OrderBot Bud] [WellFoundedLT Bud] :
    List (Ekey Bud) → List Frm → Prop
  | [], ctx => ∃ bs : List Bool, GCtx (true :: bs) ctx
  | (e :: ks), ctx =>
      (e = ⊥ → ∃ (ctx' : List Frm) (U : Jk1), ctx = ctx' ++ [Frm.fone U] ∧
        WCtxR ks ctx' ∧ FrmR ks U ∧ WPdR ks U) ∧
      (ebud e = ⊥ → e ≠ ⊥ → ∃ ctx' : List Frm,
        ctx = ctx' ++ List.replicate (erun e) (Frm.ftwo Jk1.nil) ∧ WCtxR ks ctx') ∧
      (ebud e ≠ ⊥ → ∃ (r : List (Ekey Bud)) (_ : ∀ x ∈ r, x < e)
        (ctx' : List Frm) (U N : Jk1),
        ctx = (ctx' ++ [Frm.fone U, Frm.ftwo N])
          ++ List.replicate (erun e) (Frm.ftwo Jk1.nil) ∧
        WCtxR (r ++ ks) ctx' ∧ FrmR (r ++ ks) U ∧ WPdR (r ++ ks) U ∧ JkA N ∧
        (∀ q : List (Ekey Bud), (∀ x ∈ q, x < e) →
          WPdR ((⊥ : Ekey Bud) :: q ++ (r ++ ks)) N))
termination_by ks _ => ((ks : List (Ekey Bud)) : Multiset (Ekey Bud))
decreasing_by
  all_goals
    first
      | exact dmT_cons _ _
      | exact dmT_app ks _ (by assumption)

theorem WCtxR_bnil (ctx : List Frm) :
    WCtxR ([] : List (Ekey Bud)) ctx ↔ ∃ bs : List Bool, GCtx (true :: bs) ctx := by
  rw [WCtxR]

theorem WPdR_bnil (V : Jk1) :
    WPdR ([] : List (Ekey Bud)) V ↔
      ∀ ctx : List Frm, WCtxR ([] : List (Ekey Bud)) ctx → GOK (plug ctx V) := by
  rw [WPdR_bnil0]
  constructor
  · intro h ctx hc
    rw [WCtxR_bnil] at hc
    obtain ⟨bs, hb⟩ := hc
    exact h bs ctx hb
  · intro h bs ctx hb
    exact h ctx ((WCtxR_bnil ctx).mpr ⟨bs, hb⟩)

theorem WCtxR_c0 (ks : List (Ekey Bud)) (ctx : List Frm) :
    WCtxR ((⊥ : Ekey Bud) :: ks) ctx ↔ ∃ (ctx' : List Frm) (U : Jk1),
      ctx = ctx' ++ [Frm.fone U] ∧ WCtxR ks ctx' ∧ FrmR ks U ∧ WPdR ks U := by
  rw [WCtxR]
  refine ⟨fun h => h.1 rfl, fun h => ⟨fun _ => h, fun _ hne => absurd rfl hne, ?_⟩⟩
  intro hne
  exact absurd rfl hne

theorem WCtxR_cf {e : Ekey Bud} (hb : ebud e = ⊥) (he : e ≠ ⊥) (ks : List (Ekey Bud))
    (ctx : List Frm) :
    WCtxR (e :: ks) ctx ↔ ∃ ctx' : List Frm,
      ctx = ctx' ++ List.replicate (erun e) (Frm.ftwo Jk1.nil) ∧ WCtxR ks ctx' := by
  rw [WCtxR]
  refine ⟨fun h => h.2.1 hb he, fun h => ⟨fun h1 => absurd h1 he, fun _ _ => h, ?_⟩⟩
  intro hne
  exact absurd hb hne

theorem WCtxR_cb {e : Ekey Bud} (he : ebud e ≠ ⊥) (ks : List (Ekey Bud)) (ctx : List Frm) :
    WCtxR (e :: ks) ctx ↔ ∃ (r : List (Ekey Bud)) (_ : ∀ x ∈ r, x < e)
      (ctx' : List Frm) (U N : Jk1),
      ctx = (ctx' ++ [Frm.fone U, Frm.ftwo N])
        ++ List.replicate (erun e) (Frm.ftwo Jk1.nil) ∧
      WCtxR (r ++ ks) ctx' ∧ FrmR (r ++ ks) U ∧ WPdR (r ++ ks) U ∧ JkA N ∧
      (∀ q : List (Ekey Bud), (∀ x ∈ q, x < e) →
        WPdR ((⊥ : Ekey Bud) :: q ++ (r ++ ks)) N) := by
  rw [WCtxR]
  refine ⟨fun h => h.2.2 he, fun h => ⟨fun h1 => absurd ?_ he, fun hb => absurd hb he,
    fun _ => h⟩⟩
  · rw [h1]
    rfl

theorem plug_frameR (ctx : List Frm) (U N : Jk1) (p : ℕ) (V : Jk1) :
    plug ((ctx ++ [Frm.fone U, Frm.ftwo N]) ++ List.replicate p (Frm.ftwo Jk1.nil)) V
      = plug ctx (Jk1.one U (Jk1.two N (stkP p V))) := by
  rw [← plug_stkP_gen, plug_snoc12]

theorem WPdR_iff : ∀ (ks : List (Ekey Bud)) (V : Jk1),
    WPdR ks V ↔ ∀ ctx : List Frm, WCtxR ks ctx → GOK (plug ctx V)
  | [], V => WPdR_bnil V
  | (e :: ks), V => by
      by_cases he : e = ⊥
      · subst he
        rw [WPdR_c0]
        constructor
        · intro h ctx hc
          rw [WCtxR_c0] at hc
          obtain ⟨ctx', U, rfl, hc', hU, hUk⟩ := hc
          rw [plug_snoc]
          exact (WPdR_iff ks (Jk1.one U V)).mp (h U hU hUk) ctx' hc'
        · intro h U hU hUk
          refine (WPdR_iff ks (Jk1.one U V)).mpr ?_
          intro ctx' hc'
          rw [← plug_snoc]
          exact h (ctx' ++ [Frm.fone U]) ((WCtxR_c0 ks _).mpr ⟨ctx', U, rfl, hc', hU, hUk⟩)
      by_cases hb : ebud e = ⊥
      · rw [WPdR_cf hb he]
        constructor
        · intro h ctx hc
          rw [WCtxR_cf hb he] at hc
          obtain ⟨ctx', rfl, hc'⟩ := hc
          rw [← plug_stkP_gen]
          exact (WPdR_iff ks _).mp h ctx' hc'
        · intro h
          refine (WPdR_iff ks _).mpr ?_
          intro ctx' hc'
          rw [plug_stkP_gen]
          exact h _ ((WCtxR_cf hb he ks _).mpr ⟨ctx', rfl, hc'⟩)
      · rw [WPdR_cb hb]
        constructor
        · intro h ctx hc
          rw [WCtxR_cb hb] at hc
          obtain ⟨r, hr, ctx', U, N, rfl, hc', hU, hUk, hJN, hNt⟩ := hc
          rw [plug_frameR]
          exact (WPdR_iff (r ++ ks) _).mp (h r hr U N hU hUk hJN hNt) ctx' hc'
        · intro h r hr U N hU hUk hJN hNt
          refine (WPdR_iff (r ++ ks) _).mpr ?_
          intro ctx' hc'
          rw [← plug_frameR]
          exact h _ ((WCtxR_cb hb ks _).mpr ⟨r, hr, ctx', U, N, rfl, hc', hU, hUk, hJN, hNt⟩)
termination_by ks _ => ((ks : List (Ekey Bud)) : Multiset (Ekey Bud))
decreasing_by
  all_goals
    first
      | exact dmT_cons _ _
      | exact dmT_app ks _ (by assumption)

theorem WPdR_congr : ∀ (ks : List (Ekey Bud)) {V1 V2 : Jk1},
    (∀ l, jk1 l V1 = jk1 l V2) → WPdR ks V1 → WPdR ks V2 := by
  intro ks V1 V2 h hA
  rw [WPdR_iff] at hA ⊢
  intro ctx hc
  exact GOK_congr (jk1_plug_congr ctx h) (hA ctx hc)

#print axioms WPdR_iff

/-! ### `WPdR` 層の小さい補題 -/

theorem FrmR_JkA (ks : List (Ekey Bud)) (U : Jk1) (h : FrmR ks U) : JkA U := h

theorem FrmR_nilA (ks : List (Ekey Bud)) : FrmR ks Jk1.nil := trivial

theorem FrmR_one (ks : List (Ekey Bud)) (U X : Jk1) (hU : FrmR ks U) (hX : JkA X) :
    FrmR ks (Jk1.one U X) := ⟨hU, hX⟩

theorem WPdR_step (ks : List (Ekey Bud)) {V W : Jk1} (hV : FrmR ks V) (hVk : WPdR ks V)
    (hW : WPdR ((⊥ : Ekey Bud) :: ks) W) : WPdR ks (Jk1.one V W) :=
  (WPdR_c0 ks W).mp hW V hV hVk

theorem WCtxR_JkT : ∀ (ks : List (Ekey Bud)) (ctx : List Frm), WCtxR ks ctx →
    ∀ X : Jk1, FrmR ks X → JkT (plug ctx X)
  | [], ctx, h, X, hX => by
      rw [WCtxR_bnil] at h
      obtain ⟨bs, hb⟩ := h
      exact JkT_plug ctx (GCtx_CtxOk (true :: bs) ctx hb) X
        (GCtx_CtxX (true :: bs) ctx hb X hX trivial)
  | (e :: ks), ctx, h, X, hX => by
      by_cases he : e = ⊥
      · subst he
        rw [WCtxR_c0] at h
        obtain ⟨ctx', U, rfl, hc', hU, -⟩ := h
        rw [plug_snoc]
        exact WCtxR_JkT ks ctx' hc' (Jk1.one U X) (FrmR_one ks U X hU hX)
      by_cases hb : ebud e = ⊥
      · rw [WCtxR_cf hb he] at h
        obtain ⟨ctx', rfl, hc'⟩ := h
        rw [← plug_stkP_gen]
        exact WCtxR_JkT ks ctx' hc' (stkP (erun e) X) (JkA_stkP (erun e) hX)
      · rw [WCtxR_cb hb] at h
        obtain ⟨r, hr, ctx', U, N, rfl, hc', hU, hUk, hJN, hNt⟩ := h
        rw [plug_frameR]
        exact WCtxR_JkT (r ++ ks) ctx' hc'
          (Jk1.one U (Jk1.two N (stkP (erun e) X)))
          (FrmR_one (r ++ ks) U _ hU ⟨hJN, JkA_stkP (erun e) hX⟩)
termination_by ks _ => ((ks : List (Ekey Bud)) : Multiset (Ekey Bud))
decreasing_by
  all_goals
    first
      | exact dmT_cons _ _
      | exact dmT_app ks _ (by assumption)

theorem WCtxR_split (ks : List (Ekey Bud)) (ctx : List Frm)
    (h : WCtxR ((⊥ : Ekey Bud) :: ks) ctx) :
    ∃ (ctx0 : List Frm) (V : Jk1), ctx = ctx0 ++ [Frm.fone V] ∧ WCtxR ks ctx0 ∧
      FrmR ks V ∧ GOK (plug ctx0 V) := by
  rw [WCtxR_c0] at h
  obtain ⟨ctx', U, rfl, hc', hU, hUk⟩ := h
  exact ⟨ctx', U, rfl, hc', hU, (WPdR_iff ks U).mp hUk ctx' hc'⟩

theorem WPdR_two_of_ctx {kk : List (Ekey Bud)} {U W : Jk1}
    (hU : FrmR kk U) (hUk : WPdR kk U)
    (h : ∀ ctx : List Frm, WCtxR ((⊥ : Ekey Bud) :: kk) ctx → GOK (plug ctx W)) :
    WPdR kk (Jk1.one U W) := by
  rw [WPdR_iff]
  intro ctx0 hc0
  rw [← plug_snoc]
  exact h (ctx0 ++ [Frm.fone U]) ((WCtxR_c0 kk _).mpr ⟨ctx0, U, rfl, hc0, hU, hUk⟩)

theorem WPdR_ck_shift {e : Ekey Bud} (he : ebud e ≠ ⊥) {ks : List (Ekey Bud)} {T : Jk1}
    (h : WPdR (e :: ks) T) (a : List (Ekey Bud)) (ha : ∀ x ∈ a, x < e) :
    WPdR (e :: (a ++ ks)) T := by
  rw [WPdR_cb he]
  intro r hr U N hU hUk hJN hNt
  have e2 : r ++ (a ++ ks) = (r ++ a) ++ ks := (List.append_assoc r a ks).symm
  rw [e2] at hU hUk hNt ⊢
  refine (WPdR_cb he ks T).mp h (r ++ a) ?_ U N hU hUk hJN hNt
  intro x hx
  rcases List.mem_append.mp hx with h1 | h1
  · exact hr x h1
  · exact ha x h1

#print axioms WCtxR_JkT
#print axioms WPdR_ck_shift

/-! ### `WPdR` の `p = 0` の塔（`WPdT_twoNilGen` の移植） -/

theorem FrmR_repB (m : ℕ) (e : Ekey Bud) (ks : List (Ekey Bud)) (N : Jk1) :
    FrmR (List.replicate m (⊥ : Ekey Bud) ++ (e :: ks)) N ↔ JkA N := Iff.rfl

theorem WCtxR_rep {N : Jk1} (hJN : JkA N) (ks : List (Ekey Bud))
    (hNall : ∀ j : ℕ, WPdR (List.replicate j (⊥ : Ekey Bud) ++ ((⊥ : Ekey Bud) :: ks)) N) :
    ∀ (m : ℕ) (ctx : List Frm), WCtxR ((⊥ : Ekey Bud) :: ks) ctx →
      WCtxR (List.replicate m (⊥ : Ekey Bud) ++ ((⊥ : Ekey Bud) :: ks))
        (ctx ++ List.replicate m (Frm.fone N))
  | 0, ctx, hc => by simpa using hc
  | (m + 1), ctx, hc => by
      have h1 := WCtxR_rep hJN ks hNall m ctx hc
      have e : ctx ++ List.replicate (m + 1) (Frm.fone N)
          = (ctx ++ List.replicate m (Frm.fone N)) ++ [Frm.fone N] := by
        rw [List.replicate_succ']
        simp
      rw [e, repB_succ_cons, WCtxR_c0]
      exact ⟨ctx ++ List.replicate m (Frm.fone N), N, rfl, h1,
        (FrmR_repB m (⊥ : Ekey Bud) ks N).mpr hJN, hNall m⟩

theorem WPdR_plug_rep (N : Jk1) (hJN : JkA N) (ks : List (Ekey Bud))
    (hNall : ∀ j : ℕ, WPdR (List.replicate j (⊥ : Ekey Bud) ++ ((⊥ : Ekey Bud) :: ks)) N)
    (m : ℕ) :
    WPdR ((⊥ : Ekey Bud) :: ks) (plug (List.replicate m (Frm.fone N)) N) := by
  rw [WPdR_iff]
  intro ctx hc
  rw [← plug_append]
  exact (WPdR_iff _ N).mp (hNall m) _ (WCtxR_rep hJN ks hNall m ctx hc)

theorem WPdR_twoNilGen {N : Jk1} (hJN : JkA N) (ks : List (Ekey Bud))
    (hNall : ∀ j : ℕ, WPdR (List.replicate j (⊥ : Ekey Bud) ++ ((⊥ : Ekey Bud) :: ks)) N) :
    WPdR ((⊥ : Ekey Bud) :: ks) (Jk1.two N Jk1.nil) := by
  rw [WPdR_iff]
  intro ctx hc
  obtain ⟨ctx0, V, rfl, hc0, hV, hGV⟩ := WCtxR_split ks ctx hc
  exact GOK_twoNilW_gen ctx0 V hJN
    (WCtxR_JkT ((⊥ : Ekey Bud) :: ks) _ hc (Jk1.two N Jk1.nil)
      (⟨hJN, trivial⟩ : FrmR ((⊥ : Ekey Bud) :: ks) (Jk1.two N Jk1.nil)))
    hGV
    (fun m => (WPdR_iff ((⊥ : Ekey Bud) :: ks) _).mp (WPdR_plug_rep N hJN ks hNall m) _ hc)

theorem bot_lt_key {b : Bud} (hb : b ≠ ⊥) (p : ℕ) :
    (⊥ : Ekey Bud) < (toLex (b, p) : Ekey Bud) :=
  Prod.Lex.left _ _ (Ne.bot_lt' (Ne.symm hb))

theorem erun_key (b : Bud) (p : ℕ) : erun (toLex (b, p) : Ekey Bud) = p := rfl

/-- `p = 0` の場合: 空木はどの `(b,0)` の節にも差せる。 -/
theorem WPdR_nilF {b : Bud} (hb : b ≠ ⊥) (ks : List (Ekey Bud)) :
    WPdR ((toLex (b, 0) : Ekey Bud) :: ks) Jk1.nil := by
  refine (WPdR_cb (show ebud (toLex (b, 0) : Ekey Bud) ≠ ⊥ from hb) ks _).mpr ?_
  intro r hr U N hU hUk hJN hNt
  rw [erun_key]
  refine (WPdR_c0 (r ++ ks) _).mp ?_ U hU hUk
  refine WPdR_twoNilGen hJN (r ++ ks) (fun j => ?_)
  rw [repB_mid j (r ++ ks)]
  exact hNt (List.replicate j (⊥ : Ekey Bud)) (fun x hx => by
    rw [List.eq_of_mem_replicate hx]
    exact bot_lt_key hb 0)

#print axioms WPdR_nilF

/-! ### ★★★ 走り: `WPdR ((b,p)::ks) nil`（`p+1` 本の縦の走り） -/

theorem key_ne_bot {b : Bud} (hb : b ≠ ⊥) (p : ℕ) : (toLex (b, p) : Ekey Bud) ≠ ⊥ :=
  ne_bot_of_gt (bot_lt_key hb p)

theorem key_lt (b : Bud) {p p' : ℕ} (h : p < p') :
    (toLex (b, p) : Ekey Bud) < (toLex (b, p') : Ekey Bud) :=
  Prod.Lex.right _ h

/-- `GOK_stkW_gen` の階段。文脈を 1 節（`(b,p)` の枠）ずつ伸ばして同じ形に戻る。 -/
theorem WPdR_stairRun {b : Bud} (hb : b ≠ ⊥) {p : ℕ}
    (hIH : ∀ ks' : List (Ekey Bud), WPdR ((toLex (b, p) : Ekey Bud) :: ks') Jk1.nil)
    {N : Jk1} (hJN : JkA N) :
    ∀ (k : ℕ) (kk : List (Ekey Bud)),
      (∀ q : List (Ekey Bud), (∀ x ∈ q, x < (toLex (b, p + 1) : Ekey Bud)) →
        WPdR ((⊥ : Ekey Bud) :: q ++ kk) N) →
      ∀ ctx : List Frm, WCtxR ((⊥ : Ekey Bud) :: kk) ctx →
        GOK (plug ctx (Jk1.two N (stkP p (nstQ N p k))))
  | 0, kk, hNt, ctx, hc => by
      have hc' := hc
      rw [WCtxR_c0] at hc'
      obtain ⟨ctx0, V, rfl, hc0, hV, hVk⟩ := hc'
      have hkey : WPdR kk (Jk1.one V (Jk1.two N (stkP p (nstQ N p 0)))) := by
        have h := (WPdR_cb (show ebud (toLex (b, p) : Ekey Bud) ≠ ⊥ from hb) kk Jk1.nil).mp
          (hIH kk) [] (by simp) V N
          (by simpa using hV) (by simpa using hVk) hJN
          (fun q hq => by
            simpa using hNt q (fun x hx => lt_trans (hq x hx) (key_lt b (by omega))))
        rw [erun_key] at h
        simpa using h
      rw [plug_snoc]
      exact (WPdR_iff kk _).mp hkey ctx0 hc0
  | (k + 1), kk, hNt, ctx, hc => by
      have hc' := hc
      rw [WCtxR_c0] at hc'
      obtain ⟨ctx0, V, rfl, hc0, hV, hVk⟩ := hc'
      have hnew : WCtxR ((⊥ : Ekey Bud) :: (toLex (b, p) : Ekey Bud) :: kk)
          (((ctx0 ++ [Frm.fone V, Frm.ftwo N]) ++ List.replicate p (Frm.ftwo Jk1.nil))
            ++ [Frm.fone Jk1.nil]) := by
        rw [WCtxR_c0]
        refine ⟨_, Jk1.nil, rfl, ?_, FrmR_nilA _, hIH kk⟩
        rw [WCtxR_cb (show ebud (toLex (b, p) : Ekey Bud) ≠ ⊥ from hb)]
        refine ⟨[], by simp, ctx0, V, N, ?_, by simpa using hc0, by simpa using hV,
          by simpa using hVk, hJN, ?_⟩
        · rw [erun_key]
        · intro q hq
          simpa using hNt q (fun x hx => lt_trans (hq x hx) (key_lt b (by omega)))
      have hstep := WPdR_stairRun hb hIH hJN k ((toLex (b, p) : Ekey Bud) :: kk)
        (fun q hq => by
          have h := hNt (q ++ [(toLex (b, p) : Ekey Bud)]) (fun x hx => by
            rcases List.mem_append.mp hx with h1 | h1
            · exact hq x h1
            · rw [List.eq_of_mem_singleton h1]
              exact key_lt b (by omega))
          simpa using h) _ hnew
      have hplug : plug (ctx0 ++ [Frm.fone V]) (Jk1.two N (stkP p (nstQ N p (k + 1))))
          = plug (((ctx0 ++ [Frm.fone V, Frm.ftwo N])
              ++ List.replicate p (Frm.ftwo Jk1.nil)) ++ [Frm.fone Jk1.nil])
            (Jk1.two N (stkP p (nstQ N p k))) := by
        rw [show ((ctx0 ++ [Frm.fone V, Frm.ftwo N])
              ++ List.replicate p (Frm.ftwo Jk1.nil)) ++ [Frm.fone Jk1.nil]
            = (ctx0 ++ [Frm.fone V]) ++ ([Frm.ftwo N]
              ++ (List.replicate p (Frm.ftwo Jk1.nil) ++ [Frm.fone Jk1.nil])) from by simp]
        simp only [plug_append, plug_repF]
        rfl
      rw [hplug]
      exact hstep

/-- ★★★★★★★ 空木は `(b,p)` の節に差せる ＝ 長さ `p+1` の縦の走りが出る。 -/
theorem WPdR_nilRun {b : Bud} (hb : b ≠ ⊥) : ∀ (p : ℕ) (ks : List (Ekey Bud)),
    WPdR ((toLex (b, p) : Ekey Bud) :: ks) Jk1.nil
  | 0, ks => WPdR_nilF hb ks
  | (p + 1), ks => by
      refine (WPdR_cb (show ebud (toLex (b, p + 1) : Ekey Bud) ≠ ⊥ from hb) ks _).mpr ?_
      intro r hr U N hU hUk hJN hNt
      rw [erun_key]
      refine WPdR_two_of_ctx hU hUk ?_
      intro ctx hc
      have hc' := hc
      rw [WCtxR_c0] at hc'
      obtain ⟨ctx0, V, rfl, hc0, hV, hVk⟩ := hc'
      rw [show stkP (p + 1) Jk1.nil = stkP p (Jk1.two Jk1.nil Jk1.nil)
        from (stkP_comm p Jk1.nil).symm]
      refine GOK_stkW_gen ctx0 V p hJN ?_ ((WPdR_iff (r ++ ks) V).mp hVk ctx0 hc0) ?_
      · exact WCtxR_JkT ((⊥ : Ekey Bud) :: (r ++ ks)) _ hc
          (Jk1.two N (stkP p (Jk1.two Jk1.nil Jk1.nil)))
          (⟨hJN, JkA_stkP p (⟨trivial, trivial⟩ : JkA (Jk1.two Jk1.nil Jk1.nil))⟩ :
            FrmR ((⊥ : Ekey Bud) :: (r ++ ks))
              (Jk1.two N (stkP p (Jk1.two Jk1.nil Jk1.nil))))
      · intro k
        exact WPdR_stairRun hb (fun ks' => WPdR_nilRun hb p ks') hJN k (r ++ ks) hNt _ hc

#print axioms WPdR_nilRun

/-! ### `WPdR` 層の荷（`⊥` の節）。`AYdWT` の移植 -/

theorem WPdR_payE (V : Jk1) (hV : FrmR ([] : List (Ekey Bud)) V)
    (hVk : WPdR ([] : List (Ekey Bud)) V)
    (C : TrioSeq) (hC : Bok C) : WPdR ([] : List (Ekey Bud)) (Jk1.pay V C) := by
  rw [WPdR_bnil0]
  intro bs ctx hb
  refine (APd_iff (true :: bs) _).mp (APd_payT bs V hV ?_ C hC) ctx hb
  refine (APd_iff (true :: bs) V).mpr (fun ctx' hc' => ?_)
  exact (WPdR_bnil0 V).mp hVk bs ctx' hc'

theorem FrmR_itJ (ks : List (Ekey Bud)) {T : Jk1} (hT : JkA T) (n : ℕ) {X : Jk1}
    (h : FrmR ks X) : FrmR ks (itJ T n X) := JkA_itJ hT n h

theorem GOK_chainJdWR {ks : List (Ekey Bud)} {ctx : List Frm} (hc : WCtxR ks ctx) {X T : Jk1}
    (hXok : FrmR ks X) (hXk : WPdR ks X) (hTok : JkA T)
    (hstep : ∀ V : Jk1, FrmR ks V → WPdR ks V → WPdR ks (Jk1.one V T)) :
    ∀ n, GOK (plug ctx (itJ T n X)) ∧ WPdR ks (itJ T n X)
  | 0 => ⟨(WPdR_iff ks X).mp hXk ctx hc, hXk⟩
  | (n + 1) => by
      obtain ⟨h1, h2⟩ := GOK_chainJdWR hc hXok hXk hTok hstep n
      have hok := FrmR_itJ ks hTok n hXok
      have h3 := hstep (itJ T n X) hok h2
      exact ⟨(WPdR_iff ks _).mp h3 ctx hc, h3⟩

/-- 予算 `⊥` の荷（`AYdW` の `WPdR` 版）。 -/
theorem AYdWR : ∀ (Y : TrioSeq), Bok Y → ∀ (ks : List (Ekey Bud)) (Z : Jk1), JkA Z →
    WPdR ((⊥ : Ekey Bud) :: ks) Z →
    ∀ (X : Jk1), FrmR ks X → WPdR ks X → WPdR ks (Jk1.one X (Jk1.pay Z Y)) := by
  have key : W 0 ⊆ {Y : TrioSeq | Bok Y → ∀ (ks : List (Ekey Bud)) (Z : Jk1), JkA Z →
      WPdR ((⊥ : Ekey Bud) :: ks) Z →
      ∀ (X : Jk1), FrmR ks X → WPdR ks X → WPdR ks (Jk1.one X (Jk1.pay Z Y))} := by
    refine A2' ?_
    intro Y hY
    simp only [Set.mem_setOf_eq]
    intro hYb ks Z hZ hRZ X hX hXk
    by_cases hshort : Y.length ≤ 1
    · rcases (by omega : Y.length = 0 ∨ Y.length = 1) with h0 | h1
      · have hnil0 : Y = [] := List.length_eq_zero_iff.mp h0
        subst hnil0
        exact WPdR_congr ks (fun l => (jk1_one_pay_nil X Z l).symm) (WPdR_step ks hX hXk hRZ)
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hYb.root
        obtain ⟨hc1, hc2⟩ := hYb.zroot c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have hpres : ∀ V : Jk1, FrmR ks V → WPdR ks V →
            WPdR ks (Jk1.one V (Jk1.pay Z ([] : TrioSeq))) :=
          fun V hV hVk =>
            WPdR_congr ks (fun l => (jk1_one_pay_nil V Z l).symm) (WPdR_step ks hV hVk hRZ)
        have e : ([((0, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
            = ([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by simp
        rw [e, WPdR_iff]
        intro ctx hc ws hw hG
        refine GoodFb_snoc_dupJs0 hw
          (WCtxR_JkT ks ctx hc (Jk1.one X (Jk1.pay Z (([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))
            (FrmR_one ks X _ hX ⟨hZ, by simpa using hYb⟩))
          (by simpa using hYb) Bok_nil ?_
        intro n hn
        exact (GOK_chainJdWR (T := Jk1.pay Z ([] : TrioSeq)) hc hX hXk ⟨hZ, Bok_nil⟩
          hpres n).1 ws hw hG
    have hlen2 : 2 ≤ Y.length := by omega
    have hYne : Y ≠ [] := by intro hcc; rw [hcc] at hlen2; simp at hlen2
    rcases hY with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry Y 0 (Y.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hYb.zroot hlast
        have hcol : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) :=
          Prod.ext hlast (Prod.ext he1 he2)
        have hgl : Y.getLast hYne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : Y.getLast hYne = Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show Y.length - 1 < Y.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : Y = Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hYne).symm
        have hop : Y⟦1⟧ = Y.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) ⟨hlast, he1, he2⟩]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdb : Bok Y.dropLast := Bok_dropLast hYb
        have hpres : ∀ V : Jk1, FrmR ks V → WPdR ks V →
            WPdR ks (Jk1.one V (Jk1.pay Z Y.dropLast)) :=
          fun V hV hVk => hdl hdb ks Z hZ hRZ V hV hVk
        rw [hsplit, WPdR_iff]
        intro ctx hc ws hw hG
        refine GoodFb_snoc_dupJs0 hw
          (WCtxR_JkT ks ctx hc (Jk1.one X (Jk1.pay Z (Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))
            (FrmR_one ks X _ hX ⟨hZ, by rw [← hsplit]; exact hYb⟩))
          (by rw [← hsplit]; exact hYb) hdb ?_
        intro n hn
        exact (GOK_chainJdWR (T := Jk1.pay Z Y.dropLast) hc hX hXk ⟨hZ, hdb⟩
          hpres n).1 ws hw hG
      · have hnz : ¬ (entry Y 0 (Y.length - 1) = 0 ∧ entry Y 1 (Y.length - 1) = 0 ∧
            entry Y 2 (Y.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hYb.zroot hYb.mono hYb.root hlen2 hnz
        rw [WPdR_iff]
        intro ctx hc ws hw hG
        refine GoodFb_snoc_innerJs0 hw
          (WCtxR_JkT ks ctx hc (Jk1.one X (Jk1.pay Z Y)) (FrmR_one ks X _ hX ⟨hZ, hYb⟩))
          hYb hlen2 hp ?_
        intro n hn
        have hh := hnat n hn
        simp only [Set.mem_setOf_eq] at hh
        exact (WPdR_iff ks _).mp (hh (Bok_oper hYb hn) ks Z hZ hRZ X hX hXk) ctx hc ws hw hG
    · exact absurd hm (Nat.not_lt_zero m)
  intro Y hYb ks Z hZ hRZ X hX hXk
  exact key hYb.mem hYb ks Z hZ hRZ X hX hXk

theorem WPdR_payT (ks : List (Ekey Bud)) (V : Jk1) (hV : JkA V)
    (hVk : WPdR ((⊥ : Ekey Bud) :: ks) V) (C : TrioSeq) (hC : Bok C) :
    WPdR ((⊥ : Ekey Bud) :: ks) (Jk1.pay V C) :=
  (WPdR_c0 ks _).mpr (fun U hU hUk => AYdWR C hC ks V hV hVk U hU hUk)

#print axioms AYdWR

/-! ### `WPdR` 層の荷（`erun = 0` の節）。`AYdTWT` の移植 -/

theorem WPdR_twoOf {e : Ekey Bud} (he : ebud e ≠ ⊥) (h0 : erun e = 0)
    {ks : List (Ekey Bud)} {V N : Jk1} (hJN : JkA N)
    (hNt : ∀ q : List (Ekey Bud), (∀ x ∈ q, x < e) →
      WPdR ((⊥ : Ekey Bud) :: q ++ ks) N)
    (hV : WPdR (e :: ks) V) : WPdR ((⊥ : Ekey Bud) :: ks) (Jk1.two N V) :=
  (WPdR_c0 ks _).mpr (fun U hU hUk => by
    have h := (WPdR_cb he ks V).mp hV [] (by simp) U N (by simpa using hU)
      (by simpa using hUk) hJN (fun q hq => by simpa using hNt q hq)
    rw [h0] at h
    simpa using h)

theorem WPdR_chainT {b : Ekey Bud} {B : List (Ekey Bud)} {ctx : List Frm}
    (hc : WCtxR ((⊥ : Ekey Bud) :: B) ctx) {N T : Jk1}
    (hN : JkA N)
    (hNall : ∀ q : List (Ekey Bud), (∀ x ∈ q, x < b) →
      WPdR ((⊥ : Ekey Bud) :: q ++ B) N)
    (hT : JkA T)
    (hstep : ∀ N' : Jk1, JkA N' →
      (∀ q : List (Ekey Bud), (∀ x ∈ q, x < b) → WPdR ((⊥ : Ekey Bud) :: q ++ B) N') →
      ∀ q : List (Ekey Bud), (∀ x ∈ q, x < b) →
        WPdR ((⊥ : Ekey Bud) :: q ++ B) (Jk1.two N' T)) :
    ∀ n, GOK (plug ctx (twoIt N T n)) ∧ JkA (twoIt N T n) ∧
      (∀ q : List (Ekey Bud), (∀ x ∈ q, x < b) →
        WPdR ((⊥ : Ekey Bud) :: q ++ B) (twoIt N T n))
  | 0 => ⟨(WPdR_iff ((⊥ : Ekey Bud) :: B) N).mp (by simpa using hNall [] (by simp)) ctx hc,
      hN, hNall⟩
  | (n + 1) => by
      obtain ⟨-, h2, h3⟩ := WPdR_chainT hc hN hNall hT hstep n
      have h4 := hstep (twoIt N T n) h2 h3
      exact ⟨(WPdR_iff ((⊥ : Ekey Bud) :: B) _).mp (by simpa using h4 [] (by simp)) ctx hc,
        ⟨h2, hT⟩, h4⟩

theorem AYdTWR_hstep {b : Ekey Bud} (hb : ebud b ≠ ⊥) (h0 : erun b = 0)
    {ks r : List (Ekey Bud)}
    (hr : ∀ x ∈ r, x < b) {T : Jk1} (hTk : WPdR (b :: ks) T) :
    ∀ N' : Jk1, JkA N' →
      (∀ q : List (Ekey Bud), (∀ x ∈ q, x < b) →
        WPdR ((⊥ : Ekey Bud) :: q ++ (r ++ ks)) N') →
      ∀ q : List (Ekey Bud), (∀ x ∈ q, x < b) →
        WPdR ((⊥ : Ekey Bud) :: q ++ (r ++ ks)) (Jk1.two N' T) := by
  intro N' hN' hN'all q hq
  have e : (⊥ : Ekey Bud) :: q ++ (r ++ ks) = (⊥ : Ekey Bud) :: (q ++ r ++ ks) := by simp
  rw [e]
  refine WPdR_twoOf hb h0 hN' ?_ ?_
  · intro q' hq'
    have e2 : (⊥ : Ekey Bud) :: q' ++ (q ++ r ++ ks)
        = ((⊥ : Ekey Bud) :: (q' ++ q)) ++ (r ++ ks) := by simp
    rw [e2]
    refine hN'all (q' ++ q) ?_
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact hq' x h1
    · exact hq x h1
  · have hsh := WPdR_ck_shift hb hTk (q ++ r)
      (by
        intro x hx
        rcases List.mem_append.mp hx with h1 | h1
        · exact hq x h1
        · exact hr x h1)
    simpa using hsh

/-- 予算 `b ≠ ⊥` の荷（`AYdTW` の `WPdR` 版）。 -/
theorem AYdTWR : ∀ (Y : TrioSeq), Bok Y → ∀ (b : Ekey Bud), ebud b ≠ ⊥ → erun b = 0 →
    ∀ (ks : List (Ekey Bud)) (Z : Jk1), JkA Z →
    WPdR (b :: ks) Z → WPdR (b :: ks) (Jk1.pay Z Y) := by
  have key : W 0 ⊆ {Y : TrioSeq | Bok Y → ∀ (b : Ekey Bud), ebud b ≠ ⊥ → erun b = 0 →
      ∀ (ks : List (Ekey Bud)) (Z : Jk1), JkA Z →
      WPdR (b :: ks) Z → WPdR (b :: ks) (Jk1.pay Z Y)} := by
    refine A2' ?_
    intro Y hY
    simp only [Set.mem_setOf_eq]
    intro hYb b hb h0 ks Z hZ hZk
    by_cases hshort : Y.length ≤ 1
    · rcases (by omega : Y.length = 0 ∨ Y.length = 1) with h0 | h1
      · have hnil0 : Y = [] := List.length_eq_zero_iff.mp h0
        subst hnil0
        exact WPdR_congr (b :: ks) (fun l => (jk1_pay_nil l Z).symm) hZk
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hYb.root
        obtain ⟨hc1, hc2⟩ := hYb.zroot c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have hZnil : WPdR (b :: ks) (Jk1.pay Z ([] : TrioSeq)) :=
          WPdR_congr (b :: ks) (fun l => (jk1_pay_nil l Z).symm) hZk
        have e : ([((0, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
            = ([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by simp
        rw [e, WPdR_cb hb]
        intro r hr U N hU hUk hN hNt
        rw [h0]
        refine WPdR_two_of_ctx hU hUk ?_
        intro ctx hc ws hw hG
        refine GoodFb_snoc_dupJt0 hw
          (WCtxR_JkT ((⊥ : Ekey Bud) :: (r ++ ks)) ctx hc
            (Jk1.two N (Jk1.pay Z (([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))
            ⟨hN, hZ, by simpa using hYb⟩) ?_
        intro n hn
        exact (WPdR_chainT (T := Jk1.pay Z ([] : TrioSeq)) hc hN hNt ⟨hZ, Bok_nil⟩
          (AYdTWR_hstep hb h0 hr hZnil) n).1 ws hw hG
    have hlen2 : 2 ≤ Y.length := by omega
    have hYne : Y ≠ [] := by intro hcc; rw [hcc] at hlen2; simp at hlen2
    rcases hY with ⟨hl, -⟩ | hnat | ⟨mm, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry Y 0 (Y.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hYb.zroot hlast
        have hcol : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) :=
          Prod.ext hlast (Prod.ext he1 he2)
        have hgl : Y.getLast hYne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : Y.getLast hYne = Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show Y.length - 1 < Y.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : Y = Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hYne).symm
        have hop : Y⟦1⟧ = Y.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) ⟨hlast, he1, he2⟩]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdb : Bok Y.dropLast := Bok_dropLast hYb
        have hprev : WPdR (b :: ks) (Jk1.pay Z Y.dropLast) := hdl hdb b hb h0 ks Z hZ hZk
        rw [hsplit, WPdR_cb hb]
        intro r hr U N hU hUk hN hNt
        rw [h0]
        refine WPdR_two_of_ctx hU hUk ?_
        intro ctx hc ws hw hG
        refine GoodFb_snoc_dupJt0 hw
          (WCtxR_JkT ((⊥ : Ekey Bud) :: (r ++ ks)) ctx hc
            (Jk1.two N (Jk1.pay Z (Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))
            ⟨hN, hZ, by rw [← hsplit]; exact hYb⟩) ?_
        intro n hn
        exact (WPdR_chainT (T := Jk1.pay Z Y.dropLast) hc hN hNt ⟨hZ, hdb⟩
          (AYdTWR_hstep hb h0 hr hprev) n).1 ws hw hG
      · have hnz : ¬ (entry Y 0 (Y.length - 1) = 0 ∧ entry Y 1 (Y.length - 1) = 0 ∧
            entry Y 2 (Y.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hYb.zroot hYb.mono hYb.root hlen2 hnz
        rw [WPdR_cb hb]
        intro r hr U N hU hUk hN hNt
        rw [h0]
        refine WPdR_two_of_ctx hU hUk ?_
        intro ctx hc ws hw hG
        refine GoodFb_snoc_innerJt0 hw
          (WCtxR_JkT ((⊥ : Ekey Bud) :: (r ++ ks)) ctx hc
            (Jk1.two N (Jk1.pay Z Y)) ⟨hN, hZ, hYb⟩)
          hlen2 hp ?_
        intro n hn
        have hh := hnat n hn
        simp only [Set.mem_setOf_eq] at hh
        have hh2 := hh (Bok_oper hYb hn) b hb h0 ks Z hZ hZk
        have hc' := hc
        rw [WCtxR_c0] at hc'
        obtain ⟨ctx0, U', hce, hc0, hU', hU'k⟩ := hc'
        subst hce
        have h2 := (WPdR_cb hb ks _).mp hh2 r hr U' N hU' hU'k hN hNt
        rw [h0] at h2
        rw [plug_snoc]
        exact (WPdR_iff _ _).mp h2 ctx0 hc0 ws hw hG
    · exact absurd hm (Nat.not_lt_zero mm)
  intro Y hYb b hb h0 ks Z hZ hZk
  exact key hYb.mem hYb b hb h0 ks Z hZ hZk

/-- ★ 残る 1 点: 「縦の走りの上に荷」。`RHang2` に対応する。 -/
def RunPay : Prop := ∀ (e : Ekey Bud), erun e ≠ 0 →
  ∀ (ks : List (Ekey Bud)) (V : Jk1), JkA V → WPdR (e :: ks) V →
  ∀ C : TrioSeq, Bok C → WPdR (e :: ks) (Jk1.pay V C)

/-- ★★★★★ `WPdR` 層の荷（`RunPay` 1 点だけ仮定）。 -/
theorem WPdR_payA (hRP : RunPay (Bud := Bud)) :
    ∀ (ks : List (Ekey Bud)) (V : Jk1), FrmR ks V → WPdR ks V →
    ∀ C : TrioSeq, Bok C → WPdR ks (Jk1.pay V C)
  | [], V, hV, hVk, C, hC => WPdR_payE V hV hVk C hC
  | (b :: ks), V, hV, hVk, C, hC => by
      by_cases h0 : erun b = 0
      · by_cases heb : ebud b = ⊥
        · have hb : b = ⊥ := ekey_eq_bot heb h0
          subst hb
          exact WPdR_payT ks V (FrmR_JkA _ V hV) hVk C hC
        · exact AYdTWR C hC b heb h0 ks V (FrmR_JkA _ V hV) hVk
      · exact hRP b h0 ks V (FrmR_JkA _ V hV) hVk C hC


#print axioms AYdTWR

/-! ### `WPdR` の空木と、走りの塔の準備 -/

theorem WPdR_oneNil (hRP : RunPay (Bud := Bud)) (ks : List (Ekey Bud)) (V : Jk1)
    (hV : FrmR ks V) (hVk : WPdR ks V) : WPdR ks (Jk1.one V Jk1.nil) := by
  rw [WPdR_iff]
  intro ctx hc
  refine APnil_gen0 ctx V
    (WCtxR_JkT ks ctx hc (Jk1.one V Jk1.nil) (FrmR_one ks V Jk1.nil hV trivial))
    ((WPdR_iff ks V).mp hVk ctx hc) ?_
  intro C hC
  exact (WPdR_iff ks _).mp (WPdR_payA hRP ks V hV hVk C hC) ctx hc

theorem WPdR_nilT (hRP : RunPay (Bud := Bud)) (ks : List (Ekey Bud)) :
    WPdR ((⊥ : Ekey Bud) :: ks) Jk1.nil :=
  (WPdR_c0 ks _).mpr (fun U hU hUk => WPdR_oneNil hRP ks U hU hUk)

theorem WPdR_nilB : WPdR ([] : List (Ekey Bud)) Jk1.nil := by
  rw [WPdR_bnil0]
  intro bs ctx hb
  exact RNil_base hb

/-- 底の形の性質（`SBs` の `WPdR` 版）: 文脈が `fone` で終わり、空木が差せる。 -/
def SOkR (ks : List (Ekey Bud)) : Prop :=
  (∀ ctx : List Frm, WCtxR ks ctx →
      ∃ (ctx0 : List Frm) (V : Jk1), ctx = ctx0 ++ [Frm.fone V] ∧ GOK (plug ctx0 V)) ∧
    WPdR ks Jk1.nil

theorem SOkR_bnil : SOkR ([] : List (Ekey Bud)) := by
  refine ⟨?_, WPdR_nilB⟩
  intro ctx hc
  rw [WCtxR_bnil] at hc
  obtain ⟨bs, hb⟩ := hc
  exact GCtx_split bs ctx hb

theorem SOkR_bot (hRP : RunPay (Bud := Bud)) (ks : List (Ekey Bud)) :
    SOkR ((⊥ : Ekey Bud) :: ks) := by
  refine ⟨?_, WPdR_nilT hRP ks⟩
  intro ctx hc
  obtain ⟨ctx0, V, rfl, hc0, hV, hGV⟩ := WCtxR_split ks ctx hc
  exact ⟨ctx0, V, rfl, hGV⟩

/-- 形の前に「裸の走り `q` 本」を足す（`q = 0` なら何も足さない）。 -/
def preRun : ℕ → List (Ekey Bud) → List (Ekey Bud)
  | 0, ks => ks
  | (q + 1), ks => (toLex ((⊥ : Bud), q + 1) : Ekey Bud) :: ks

theorem WPdR_preRun : ∀ (q : ℕ) (ks : List (Ekey Bud)) (V : Jk1),
    WPdR ks (stkP q V) → WPdR (preRun q ks) V
  | 0, ks, V, h => h
  | (q + 1), ks, V, h => by
      have hne : (toLex ((⊥ : Bud), q + 1) : Ekey Bud) ≠ ⊥ := by
        intro hc
        have : (0 : ℕ) = q + 1 := congrArg (fun x => erun x) hc.symm
        omega
      show WPdR ((toLex ((⊥ : Bud), q + 1) : Ekey Bud) :: ks) V
      rw [WPdR_cf (show ebud (toLex ((⊥ : Bud), q + 1) : Ekey Bud) = ⊥ from rfl) hne]
      exact h

theorem WCtxR_preRun : ∀ (q : ℕ) {ks : List (Ekey Bud)} {D : List Frm}, WCtxR ks D →
    WCtxR (preRun q ks) (D ++ List.replicate q (Frm.ftwo Jk1.nil))
  | 0, ks, D, h => by simpa using h
  | (q + 1), ks, D, h => by
      have hne : (toLex ((⊥ : Bud), q + 1) : Ekey Bud) ≠ ⊥ := by
        intro hc
        have : (0 : ℕ) = q + 1 := congrArg (fun x => erun x) hc.symm
        omega
      show WCtxR ((toLex ((⊥ : Bud), q + 1) : Ekey Bud) :: ks)
        (D ++ List.replicate (q + 1) (Frm.ftwo Jk1.nil))
      rw [WCtxR_cf (show ebud (toLex ((⊥ : Bud), q + 1) : Ekey Bud) = ⊥ from rfl) hne]
      exact ⟨D, rfl, h⟩

#print axioms SOkR_bot
#print axioms WPdR_preRun

/-! ### ★★★ 走りの塔 `WPdR_stkS`（`SG_stkS` の移植） -/

def shRq (q : ℕ) (ks : List (Ekey Bud)) : ℕ → List (Ekey Bud)
  | 0 => preRun q ks
  | (i + 1) => preRun q ((⊥ : Ekey Bud) :: shRq q ks i)

theorem WCtxR_fone {ks : List (Ekey Bud)} {ctx : List Frm} {U : Jk1}
    (hc : WCtxR ks ctx) (hU : FrmR ks U) (hUk : WPdR ks U) :
    WCtxR ((⊥ : Ekey Bud) :: ks) (ctx ++ [Frm.fone U]) :=
  (WCtxR_c0 ks _).mpr ⟨ctx, U, rfl, hc, hU, hUk⟩

theorem WPdR_shR (hRP : RunPay (Bud := Bud)) (q : ℕ)
    (hq : ∀ ks' : List (Ekey Bud), SOkR ks' → WPdR ks' (stk q))
    (ks : List (Ekey Bud)) (hk : SOkR ks) :
    ∀ i : ℕ, WPdR (shRq q ks i) Jk1.nil
  | 0 => WPdR_preRun q ks Jk1.nil (hq ks hk)
  | (i + 1) => WPdR_preRun q _ Jk1.nil
      (hq ((⊥ : Ekey Bud) :: shRq q ks i) (SOkR_bot hRP _))

theorem WCtxR_blkR (hRP : RunPay (Bud := Bud)) (q : ℕ)
    (hq : ∀ ks' : List (Ekey Bud), SOkR ks' → WPdR ks' (stk q))
    {ks : List (Ekey Bud)} (hk : SOkR ks) {D : List Frm} (hD : WCtxR ks D) :
    ∀ i : ℕ, WCtxR (shRq q ks i)
      (D ++ List.replicate q (Frm.ftwo Jk1.nil)
        ++ blkR Jk1.nil (List.replicate q Jk1.nil) i)
  | 0 => by
      rw [blkR_zero, List.append_nil]
      exact WCtxR_preRun q hD
  | (i + 1) => by
      rw [blkR_snoc]
      have e : D ++ List.replicate q (Frm.ftwo Jk1.nil)
            ++ (blkR Jk1.nil (List.replicate q Jk1.nil) i
              ++ blkC Jk1.nil (List.replicate q Jk1.nil))
          = ((D ++ List.replicate q (Frm.ftwo Jk1.nil)
              ++ blkR Jk1.nil (List.replicate q Jk1.nil) i) ++ [Frm.fone Jk1.nil])
            ++ List.replicate q (Frm.ftwo Jk1.nil) := by
        rw [blkC_eq, ftw_rep]
        simp [List.append_assoc]
      rw [e]
      exact WCtxR_preRun q (WCtxR_fone (WCtxR_blkR hRP q hq hk hD i) (FrmR_nilA _)
        (WPdR_shR hRP q hq ks hk i))

/-- ★★★★★★★ 走りの塔。`SOkR` の形なら `stk q` はどの長さでも差せる。 -/
theorem WPdR_stkS (hRP : RunPay (Bud := Bud)) :
    ∀ (q : ℕ) (ks : List (Ekey Bud)), SOkR ks → WPdR ks (stk q)
  | 0, ks, hk => hk.2
  | (q + 1), ks, hk => by
      rw [WPdR_iff]
      intro D hD
      have hq : ∀ ks' : List (Ekey Bud), SOkR ks' → WPdR ks' (stk q) :=
        fun ks' hk' => WPdR_stkS hRP q ks' hk'
      obtain ⟨ctx, V, hDe, hGV⟩ := hk.1 D hD
      subst hDe
      have ec : ctx ++ blkC V (List.replicate q Jk1.nil)
          = (ctx ++ [Frm.fone V]) ++ List.replicate q (Frm.ftwo Jk1.nil) := by
        rw [blkC_eq, ftw_rep]
      have egoal : plug (ctx ++ blkC V (List.replicate q Jk1.nil))
            (Jk1.two Jk1.nil Jk1.nil)
          = plug (ctx ++ [Frm.fone V]) (stk (q + 1)) := by
        rw [ec, plug_append, plug_repF, stkP_two_nil_nil]
      rw [← egoal]
      refine GOK_runGNil_gen (V := V) (A := Jk1.nil) trivial
        (fun B hB => by rw [List.eq_of_mem_replicate hB]; trivial) ctx ?_ hGV ?_
      · rw [ec]
        exact WCtxR_JkT _ _ (WCtxR_preRun q hD) _ ⟨trivial, trivial⟩
      · intro i
        have hc := WCtxR_blkR hRP q hq hk hD i
        have hh := (WPdR_iff _ _).mp (WPdR_shR hRP q hq ks hk i) _ hc
        rw [ec]
        simpa [List.append_assoc] using hh

#print axioms WPdR_stkS

/-! ### ★★★ 走りのてっぺんの兄弟を鎖にする（`WPdR_stkS` の一般化）

`GOK_runGNil_gen` を `A := N` で使うと、階段の文脈は

    plug (ctx ++ blkC V Bs ++ blkR N Bs i) X = plug (ctx ++ [fone V]) (TwG N p i X)

    TwG N p 0 X = stkP p X,   TwG N p (i+1) X = TwG N p i (one N (stkP p X))

と書ける（`Bs = replicate p nil`）。だから階段の条件は
「`N` の塔 `TwG N p i N` が**同じ `ks`** に差せる」1 本で済む。
文脈の入り目が増えないので、鎖 `N` について循環しない。 -/

def TwG (N : Jk1) (p : ℕ) : ℕ → Jk1 → Jk1
  | 0, X => stkP p X
  | (i + 1), X => TwG N p i (Jk1.one N (stkP p X))

theorem JkA_TwG {N : Jk1} (hJN : JkA N) (p : ℕ) :
    ∀ (i : ℕ) {X : Jk1}, JkA X → JkA (TwG N p i X)
  | 0, _, hX => JkA_stkP p hX
  | (i + 1), _, hX => JkA_TwG hJN p i ⟨hJN, JkA_stkP p hX⟩

theorem plug_TwG (D : List Frm) (V N : Jk1) (p : ℕ) :
    ∀ (i : ℕ) (X : Jk1),
      plug (D ++ blkC V (List.replicate p Jk1.nil)
          ++ blkR N (List.replicate p Jk1.nil) i) X
        = plug (D ++ [Frm.fone V]) (TwG N p i X)
  | 0, X => by
      rw [blkR_zero, List.append_nil, blkC_eq, ftw_rep, plug_append, plug_repF]
      rfl
  | (i + 1), X => by
      have e1 : D ++ blkC V (List.replicate p Jk1.nil)
            ++ blkR N (List.replicate p Jk1.nil) (i + 1)
          = ((D ++ blkC V (List.replicate p Jk1.nil)
              ++ blkR N (List.replicate p Jk1.nil) i) ++ [Frm.fone N])
            ++ List.replicate p (Frm.ftwo Jk1.nil) := by
        rw [blkR_snoc, blkC_eq, ftw_rep]
        simp [blkC, ftw_rep, List.append_assoc]
      rw [e1, plug_append, plug_repF, plug_snoc, plug_TwG D V N p i]
      rfl

/-- ★★★★★★★ 走りのてっぺんの 2 の記録の兄弟を `N` にできる（階段は `N` の塔）。 -/
theorem WPdR_stkG (p : ℕ) (ks : List (Ekey Bud)) (hk : SOkR ks) {N : Jk1} (hJN : JkA N)
    (htw : ∀ i : ℕ, WPdR ks (TwG N p i N)) :
    WPdR ks (stkP p (Jk1.two N Jk1.nil)) := by
  rw [WPdR_iff]
  intro D hD
  obtain ⟨ctx, V, hDe, hGV⟩ := hk.1 D hD
  have egoal : plug (ctx ++ blkC V (List.replicate p Jk1.nil)) (Jk1.two N Jk1.nil)
      = plug D (stkP p (Jk1.two N Jk1.nil)) := by
    rw [blkC_eq, ftw_rep, hDe, plug_append, plug_repF]
  rw [← egoal]
  refine GOK_runGNil_gen (V := V) (A := N) hJN
    (fun B hB => by rw [List.eq_of_mem_replicate hB]; trivial) ctx ?_ hGV ?_
  · rw [egoal]
    exact WCtxR_JkT ks D hD (stkP p (Jk1.two N Jk1.nil))
      (JkA_stkP p (⟨hJN, trivial⟩ : JkA (Jk1.two N Jk1.nil)))
  · intro i
    rw [plug_TwG ctx V N p i N, ← hDe]
    exact (WPdR_iff ks _).mp (htw i) D hD

#print axioms WPdR_stkG

/-! ### ★★★★★★★★ `RunAll` は「走りの上に 1 の記録を載せる」1 文に落ちる

`WPdR_stkG` の階段の条件は `TwG nil q i nil` の族で、

    TwG N p (i+1) X = stkP p (one N (TwG N p i X))

だから、`i` の帰納の 1 段は「`stkP q (one nil Y)` を差す」だけ。入り目の列 `ks` は
**一段も伸びない**（`SOkR_bot` が要らない）。荷も鎖も出てこない。 -/

theorem TwG_succ (N : Jk1) (p : ℕ) : ∀ (i : ℕ) (X : Jk1),
    TwG N p (i + 1) X = stkP p (Jk1.one N (TwG N p i X))
  | 0, _ => rfl
  | (i + 1), X => by
      show TwG N p (i + 1) (Jk1.one N (stkP p X)) = _
      rw [TwG_succ N p i (Jk1.one N (stkP p X))]
      rfl

theorem WPdR_bnilA (V : Jk1) :
    WPdR ([] : List (Ekey Bud)) V ↔ ∀ bs : List Bool, APd (true :: bs) V := by
  rw [WPdR_bnil0]
  constructor
  · intro h bs
    exact (APd_iff (true :: bs) V).mpr (fun ctx hc => h bs ctx hc)
  · intro h bs ctx hc
    exact (APd_iff (true :: bs) V).mp (h bs) ctx hc

/-- ★ 残る 1 文: 走りのてっぺんに 1 の記録（兄弟は空木）を載せられる。
層も予算も鎖も荷も出てこない、`APd` だけの文。 -/
def OneRunA : Prop := ∀ (q : ℕ) (Y : Jk1), JkA Y →
  (∀ bs : List Bool, APd (true :: bs) Y) →
  ∀ bs : List Bool, APd (true :: bs) (stkP q (Jk1.one Jk1.nil Y))

theorem WPdR_stkO (hOR : OneRunA) :
    ∀ q : ℕ, WPdR ([] : List (Ekey Bud)) (stk q)
  | 0 => (SOkR_bnil (Bud := Bud)).2
  | (q + 1) => by
      have htw : ∀ i : ℕ, WPdR ([] : List (Ekey Bud)) (TwG Jk1.nil q i Jk1.nil) := by
        intro i
        induction i with
        | zero => exact WPdR_stkO hOR q
        | succ i ih =>
            rw [TwG_succ]
            refine (WPdR_bnilA _).mpr (hOR q _ (JkA_TwG (N := Jk1.nil) trivial q i trivial)
              ((WPdR_bnilA _).mp ih))
      have h := WPdR_stkG q ([] : List (Ekey Bud)) SOkR_bnil (N := Jk1.nil) trivial htw
      rw [stkP_two_nil_nil] at h
      exact h

/-- ★★★★★★★★ 行376 が `OneRunA` 1 文から出る。 -/
theorem RunAll_of_OneRunA (hOR : OneRunA) : RunAll :=
  fun q ks => (WPdR_bnilA (Bud := ℕ) (stk q)).mp (WPdR_stkO (Bud := ℕ) hOR q) ks

#print axioms WPdR_stkO
#print axioms RunAll_of_OneRunA

/-- ★★ 残る 1 文（これが一番小さい）: どの `true::bs` にも差せる木は、
2 の記録（兄弟は空木）1 段の上にも差せる。 -/
def TwoNilStep : Prop := ∀ Z : Jk1, JkA Z → (∀ bs : List Bool, APd (true :: bs) Z) →
  ∀ bs : List Bool, APd (true :: bs) (Jk1.two Jk1.nil Z)

theorem OneRunA_of_TwoNilStep (h : TwoNilStep) : OneRunA := by
  intro q Y hJY hY
  induction q with
  | zero =>
      intro bs
      exact (APd_ct (true :: bs) Y).mp (hY (true :: bs)) Jk1.nil (FrmJ_nilA _) trivial
        (APd_nilT bs)
  | succ q ih =>
      intro bs
      exact h (stkP q (Jk1.one Jk1.nil Y)) (JkA_stkP q ⟨trivial, hJY⟩) ih bs

#print axioms OneRunA_of_TwoNilStep

/-- ★★★★★★★★ 行376 が `RunPay`（走りの上の荷）1 文から出る。 -/
theorem RunAll_of_RunPay (hRP : RunPay (Bud := Bud)) : RunAll := by
  intro q ks
  rw [APd_iff]
  intro ctx hc
  exact (WPdR_bnil0 (stk q)).mp (WPdR_stkS hRP q [] SOkR_bnil) ks ctx hc

theorem R376_of_RunPay (hRP : RunPay (Bud := Bud)) :
    R373 ++ [((5, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  R376_of_RunAll (RunAll_of_RunPay hRP)

#print axioms R376_of_RunPay

/-! ### ★ `RunPay` を純粋な `GOK` の 1 文 `HtowR` に落とす

`GOK_twoPayZ_of`（鎖の族で荷の W 帰納を回す一般補題）を使うと、残るのは
「2 の記録の兄弟に荷の鎖 `VCh V` を置ける」1 点だけになる。 -/

def HtowR : Prop := ∀ (ctx : List Frm) (V : Jk1), JkA V →
  (∀ (N T : Jk1), JkA N → JkA T → JkT (plug ctx (Jk1.two N T))) →
  GOK (plug ctx (Jk1.two Jk1.nil V)) →
  ∀ N : Jk1, VCh V N → GOK (plug ctx (Jk1.two N V))

theorem RunPay_of_HtowR (h : HtowR) : RunPay (Bud := Bud) := by
  intro e he ks V hJV hVk C hC
  obtain ⟨p, hp⟩ : ∃ p, erun e = p + 1 := ⟨erun e - 1, by omega⟩
  by_cases hb : ebud e = ⊥
  · have hne : e ≠ ⊥ := fun hc => he (by rw [hc]; rfl)
    rw [WPdR_cf hb hne] at hVk ⊢
    rw [hp] at hVk ⊢
    rw [WPdR_iff]
    intro ctx hc
    have hJTg : ∀ N T : Jk1, JkA N → JkA T →
        JkT (plug (ctx ++ List.replicate p (Frm.ftwo Jk1.nil)) (Jk1.two N T)) := by
      intro N T hN hT
      rw [← plug_stkP_gen]
      exact WCtxR_JkT ks ctx hc (stkP p (Jk1.two N T)) (JkA_stkP p ⟨hN, hT⟩)
    have hbase : GOK (plug (ctx ++ List.replicate p (Frm.ftwo Jk1.nil))
        (Jk1.two Jk1.nil V)) := by
      rw [← plug_stkP_gen, stkP_comm]
      exact (WPdR_iff ks _).mp hVk ctx hc
    have hh := GOK_twoPayZ_of (ctx := ctx ++ List.replicate p (Frm.ftwo Jk1.nil))
      (VCh V) hJV (fun N hN => JkA_of_VCh hJV hN)
      (fun N hN Y hY k => VCh_twoIt hN hY k) hJTg
      (fun N hN => h _ V hJV hJTg hbase N hN) C hC Jk1.nil VCh.nil
    rw [← plug_stkP_gen, stkP_comm] at hh
    exact hh
  · rw [WPdR_cb hb] at hVk ⊢
    intro r hr U N0 hU hUk hJN0 hNt
    rw [hp]
    refine WPdR_two_of_ctx hU hUk ?_
    intro ctx hc
    have hJTg : ∀ N T : Jk1, JkA N → JkA T →
        JkT (plug ((ctx ++ [Frm.ftwo N0]) ++ List.replicate p (Frm.ftwo Jk1.nil))
          (Jk1.two N T)) := by
      intro N T hN hT
      rw [← plug_stkP_gen, plug_snoc2]
      exact WCtxR_JkT ((⊥ : Ekey Bud) :: (r ++ ks)) ctx hc
        (Jk1.two N0 (stkP p (Jk1.two N T))) ⟨hJN0, JkA_stkP p ⟨hN, hT⟩⟩
    have hbase : GOK (plug ((ctx ++ [Frm.ftwo N0])
        ++ List.replicate p (Frm.ftwo Jk1.nil)) (Jk1.two Jk1.nil V)) := by
      rw [← plug_stkP_gen, stkP_comm, plug_snoc2]
      have hbase' : WPdR ((⊥ : Ekey Bud) :: (r ++ ks))
          (Jk1.two N0 (stkP (p + 1) V)) := by
        refine (WPdR_c0 (r ++ ks) _).mpr (fun U2 hU2 hU2k => ?_)
        have hv := hVk r hr U2 N0 hU2 hU2k hJN0 hNt
        rw [hp] at hv
        exact hv
      exact (WPdR_iff ((⊥ : Ekey Bud) :: (r ++ ks)) _).mp hbase' ctx hc
    have hh := GOK_twoPayZ_of
      (ctx := (ctx ++ [Frm.ftwo N0]) ++ List.replicate p (Frm.ftwo Jk1.nil))
      (VCh V) hJV (fun N hN => JkA_of_VCh hJV hN)
      (fun N hN Y hY k => VCh_twoIt hN hY k) hJTg
      (fun N hN => h _ V hJV hJTg hbase N hN) C hC Jk1.nil VCh.nil
    rw [← plug_stkP_gen, stkP_comm, plug_snoc2] at hh
    exact hh

end EkeyR

/-- ★★★★★★★★ 行376 は `APd` だけの 1 文 `OneRunA` から出る。
「`Y` がどの `true::bs` の形にも差せるなら、`stkP q (one nil Y)`（走り `q` 本の上に
1 の記録）も差せる」。鎖も荷も予算も出てこない。 -/
theorem R376_of_OneRunA (h : OneRunA) : R373 ++ [((5, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  R376_of_RunAll (RunAll_of_OneRunA h)

/-- ★★★★★★★★ 行376 は「どの形にも差せる木の上に `two nil` を 1 段」だけで出る。 -/
theorem R376_of_TwoNilStep (h : TwoNilStep) : R373 ++ [((5, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  R376_of_OneRunA (OneRunA_of_TwoNilStep h)

#print axioms R376_of_OneRunA
#print axioms R376_of_TwoNilStep

/-- ★★★★★★★★ 行376 は純粋な `GOK` の 1 文 `HtowR` から出る。 -/
theorem R376_of_HtowR (h : HtowR) : R373 ++ [((5, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  R376_of_RunPay (Bud := ℕ) (RunPay_of_HtowR (Bud := ℕ) h)

#print axioms R376_of_HtowR

/-! ### ★★★ `APd` だけで閉じる形：`APd_twoTwoGen` を `stk q` に一般化する

`GOK_stkW_gen`（緑）は `two N (stkP p (two nil nil))` を、階段
`∀ k, GOK (plug (ctx0 ++ [fone V]) (two N (stkP p (nstQ N p k))))` から出す。
階段はどれも**同じ文脈** `ctx0 ++ [fone V]` に置くので `APd (true::ks)` の文で書ける。
`APd_cf` を `m = 0` で使えば `APd (false::ks) (stkP p (nstQ N p k))` に落ちる。

`p = 0` のときは `nstQ N 0 k = nstN N k` で、階段は `APd_nstN`（緑）そのもの。
つまり `p = 0`（= `stk 2`）は無条件。`p ≥ 1` だけが壁。 -/

/-- 走り 1 本は無条件（`APd (false::ks) nil` を `m = 0`, `N = nil` で使うだけ）。 -/
theorem APd_stk1 (ks : List Bool) : APd (true :: ks) (stk 1) :=
  (APd_ct ks _).mpr (fun U hU hR hUk =>
    (APd_cf ks Jk1.nil).mp (APd_nil (false :: ks)) 0 U Jk1.nil
      (by simpa using hU) (by simpa using hR) (by simpa using hUk) trivial
      (fun j => APd_nil _))

/-- ★★★ 階段さえあれば `two N (stk (p+1))` が出る（`APd_twoTwoGen` の `p` 一般化）。
階段は `GOK_stkW_gen` が要る形をそのまま `APd (true::ks)` で書いたもの。 -/
theorem APd_twoStkGen {N : Jk1} (hJN : JkA N) (p : ℕ) (ks : List Bool)
    (hst : ∀ k : ℕ, APd (true :: ks) (Jk1.two N (stkP p (nstQ N p k)))) :
    APd (true :: ks) (Jk1.two N (stkP p (Jk1.two Jk1.nil Jk1.nil))) := by
  rw [APd_iff]
  intro ctx hc
  have hcO : CtxOk ctx := GCtx_CtxOk (true :: ks) ctx hc
  obtain ⟨ctx0, V, rfl, hGV⟩ := GCtx_split ks ctx hc
  refine GOK_stkW_gen ctx0 V p hJN ?_ hGV ?_
  · exact JkT_plug _ hcO _ ((CtxX_snoc1 ctx0 V _).mpr
      ⟨hJN, JkA_stkP p (⟨trivial, trivial⟩ : JkA (Jk1.two Jk1.nil Jk1.nil))⟩)
  · intro k
    exact (APd_iff (true :: ks) _).mp (hst k) _ hc

/-- `p = 0` の階段は `APd_nstN`（緑）。だから `stk 2` は無条件。 -/
theorem APd_stk2 (ks : List Bool) : APd (true :: ks) (stk 2) := by
  have hh := APd_twoStkGen (N := Jk1.nil) trivial 0 ks (fun k => by
    rw [show stkP 0 (nstQ Jk1.nil 0 k) = nstN Jk1.nil k from nstQ_zero Jk1.nil k]
    refine (APd_ct ks _).mpr (fun U hU hR hUk => ?_)
    exact (APd_cf ks _).mp
      (APd_nstN (N := Jk1.nil) trivial (fun j kk => APd_nil _) k ks) 0 U Jk1.nil
      (by simpa using hU) (by simpa using hR) (by simpa using hUk) trivial
      (fun j => APd_nil _))
  rw [stkP_two_nil_nil] at hh
  exact hh

#print axioms APd_stk2

/-- ★ 残る 1 文（`APd` だけ）: 走りの塔 `stkP (p+1) (nstQ nil p k)` が差せる。
`k = 0` は `stk (p+1)`（`p` の帰納で前の段）なので、中身は `k` の段。 -/
def StQ : Prop := ∀ (p k : ℕ) (ks : List Bool),
  APd (true :: ks) (Jk1.two Jk1.nil (stkP p (nstQ Jk1.nil p k)))

theorem RunAll_of_StQ (h : StQ) : RunAll := by
  intro q ks
  match q with
  | 0 => exact APd_nilT ks
  | 1 => exact APd_stk1 ks
  | (p + 2) =>
      have hh := APd_twoStkGen (N := Jk1.nil) trivial p ks (fun k => h p k ks)
      rw [stkP_two_nil_nil] at hh
      exact hh

/-- ★ 壁の最小例。これが出れば `stk 3` が出る。 -/
theorem APd_stk3_of
    (hst : ∀ (k : ℕ) (ks : List Bool),
      APd (true :: ks) (Jk1.two Jk1.nil (stkP 1 (nstQ Jk1.nil 1 k)))) (ks : List Bool) :
    APd (true :: ks) (stk 3) := by
  have hh := APd_twoStkGen (N := Jk1.nil) trivial 1 ks (fun k => hst k ks)
  rw [stkP_two_nil_nil] at hh
  exact hh

#print axioms APd_stk3_of

/-! ### 既知の最短形 `StkStep` との接続

`SmallA` の `StkStep : ∀ q, TwoOk (stk q) → TwoOk (stk (q+1))` が今までの最短形。
`APd_twoStkGen` を使うと、その中身は**階段の `k` の段だけ**になる
（`k = 0` はちょうど `TwoOk (stk q)`）。 -/

def StkStair : Prop := ∀ (N : Jk1), JkA N →
  (∀ (j : ℕ) (kk : List Bool), APd (List.replicate j true ++ (true :: kk)) N) →
  ∀ q : ℕ, (∀ ks : List Bool, APd (true :: ks) (Jk1.two N (stk q))) →
  ∀ (k : ℕ) (ks : List Bool), APd (true :: ks) (Jk1.two N (stkP q (nstQ N q k)))

theorem StkStep_of_StkStair (h : StkStair) : StkStep := by
  intro q hq N hJN hNall j kk
  rw [rep_true_cons]
  have hbase : ∀ ks : List Bool, APd (true :: ks) (Jk1.two N (stk q)) := by
    intro ks
    simpa using hq N hJN hNall 0 ks
  have hh := APd_twoStkGen hJN q (List.replicate j true ++ kk)
    (fun k => h N hJN hNall q hbase k (List.replicate j true ++ kk))
  rw [stkP_two_nil_nil] at hh
  exact hh

/-- ★★★★★★★★ 行376 は階段の 1 文 `StkStair` から出る。 -/
theorem R376_of_StkStair (h : StkStair) : R373 ++ [((5, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  R376_of_StkStep (StkStep_of_StkStair h)

#print axioms StkStep_of_StkStair
#print axioms R376_of_StkStair

/-- ★★★★★★★★ 行376 は `APd` だけの 1 文 `StQ` から出る。 -/
theorem R376_of_StQ (h : StQ) : R373 ++ [((5, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  R376_of_RunAll (RunAll_of_StQ h)

#print axioms APd_stk1
#print axioms APd_twoStkGen
#print axioms R376_of_StQ

/-! ### ★★★ `GOK_stkW_gen` の「内側の兄弟が一般」版の準備

`two N (two W nil)` の語は

    Y0 ++ unQW N W D ++ [(D+2, 2, 0)],   unQW N W D = (D,1,0) :: jk1 D (two N W)

で、`snocYd_mem` を `L = D`, `y = 2`, `dl = 2` で使える（`W` に依らない）。
階段は `nstW N W 0 = two N W`, `nstW N W (k+1) = two N (one W (nstW N W k))`。 -/

/-- 階段の単位（内側の兄弟が `W`）。`unQW N (stkP p nil) D` は `unQ N p D` ではない
（あちらは縦の走り、こちらは `W` を 2 の記録の荷に置く）。 -/
def unQW (N W : Jk1) (D : ℕ) : TrioSeq :=
  ((D, 1, 0) : ℕ × ℕ × ℕ) :: jk1 D (Jk1.two N W)

/-- 階段（`k+1` 個の写し）。 -/
def nstW (N W : Jk1) : ℕ → Jk1
  | 0 => Jk1.two N W
  | (k + 1) => Jk1.two N (Jk1.one W (nstW N W k))

theorem unQW_eq3 (N W : Jk1) (D : ℕ) :
    unQW N W D = (((D, 1, 0) : ℕ × ℕ × ℕ) :: jk1 D N)
      ++ (((D + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (D + 1) W) := by
  show ((D, 1, 0) : ℕ × ℕ × ℕ) :: (jk1 D N ++ (((D + 1, 2, 0) : ℕ × ℕ × ℕ)
      :: jk1 (D + 1) W)) = _
  simp

theorem unQW_eq (N W : Jk1) (D : ℕ) :
    unQW N W D = unN N D ++ jk1 (D + 1) W := by
  rw [unQW_eq3]
  simp [unN, List.append_assoc]

theorem shift_unQW (N W : Jk1) (D s : ℕ) :
    shiftr01 s 0 (unQW N W D) = unQW N W (D + s) := by
  show shiftr01 s 0 ([((D, 1, 0) : ℕ × ℕ × ℕ)] ++ jk1 D (Jk1.two N W)) = _
  rw [shiftr01_append0, shift_col, jk1_shift]
  rfl

theorem JkA_nstW {N W : Jk1} (hJN : JkA N) (hJW : JkA W) : ∀ k : ℕ, JkA (nstW N W k)
  | 0 => ⟨hJN, hJW⟩
  | (k + 1) => ⟨hJN, hJW, JkA_nstW hJN hJW k⟩

theorem jk1_nstW (N W : Jk1) : ∀ (k l : ℕ),
    ((l, 1, 0) : ℕ × ℕ × ℕ) :: jk1 l (nstW N W k)
      = (List.range (k + 1)).flatMap (fun j => shiftr01 (2 * j) 0 (unQW N W l))
  | 0, l => by
      show ((l, 1, 0) : ℕ × ℕ × ℕ) :: jk1 l (Jk1.two N W) = _
      simp [unQW]
  | (k + 1), l => by
      have hstep : ((l, 1, 0) : ℕ × ℕ × ℕ) :: jk1 l (nstW N W (k + 1))
          = unQW N W l ++
            (((l + 2, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 2) (nstW N W k)) := by
        show ((l, 1, 0) : ℕ × ℕ × ℕ) ::
            (jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
              jk1 (l + 1) (Jk1.one W (nstW N W k)))) = _
        show ((l, 1, 0) : ℕ × ℕ × ℕ) ::
            (jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
              (jk1 (l + 1) W ++ (((l + 1 + 1, 2 - 1, 0) : ℕ × ℕ × ℕ) ::
                jk1 (l + 1 + 1) (nstW N W k))))) = _
        rw [unQW_eq3]
        simp [List.append_assoc, show l + 1 + 1 = l + 2 from rfl]
      rw [hstep, jk1_nstW N W k (l + 2),
        show List.range (k + 1 + 1) = 0 :: (List.range (k + 1)).map Nat.succ from
          List.range_succ_eq_map,
        List.flatMap_cons, List.flatMap_map]
      simp only [Nat.mul_zero, shiftr01_zero, Function.comp_def]
      refine congrArg _ ?_
      apply List.flatMap_congr
      intro j _
      rw [shift_unQW, shift_unQW, Nat.mul_succ]
      congr 1
      omega

#print axioms jk1_nstW

/-! #### `unQW` の `MidD` / `hMy` と、塔から末尾の 2 の記録を継ぐ補題 -/

theorem MidD_unQW {N W : Jk1} (hJN : JkA N) (hJW : JkA W) {D : ℕ} (hD : 1 ≤ D) :
    MidD (D + 1) (unQW N W D) := by
  rw [unQW_eq N W D]
  refine MidD_append (MidD_unN hJN hD) ?_ (jk1_mono W hJW (D + 1))
  intro c hc
  have := jk1_ge W (D + 1) c hc
  omega

theorem length_unQW (N W : Jk1) (D : ℕ) :
    (unQW N W D).length = (jk1 D N).length + 1 + ((jk1 (D + 1) W).length + 1) := by
  rw [unQW_eq3]
  simp
  omega

theorem entry_unQW_mid0 (N W : Jk1) (D : ℕ) :
    entry (unQW N W D) 0 ((jk1 D N).length + 1) = D + 1 := by
  rw [unQW_eq3, show (jk1 D N).length + 1
      = (((D, 1, 0) : ℕ × ℕ × ℕ) :: jk1 D N).length from by simp, entry_append_at]
  rfl

theorem entry_unQW_mid1 (N W : Jk1) (D : ℕ) :
    entry (unQW N W D) 1 ((jk1 D N).length + 1) = 2 := by
  rw [unQW_eq3, show (jk1 D N).length + 1
      = (((D, 1, 0) : ℕ × ℕ × ℕ) :: jk1 D N).length from by simp, entry_append_at]
  rfl

theorem entry_unQW_right (N W : Jk1) (D : ℕ) : ∀ t, (jk1 D N).length + 1 < t →
    t < (unQW N W D).length → D + 2 ≤ entry (unQW N W D) 0 t := by
  intro t ht1 ht2
  rw [length_unQW] at ht2
  obtain ⟨i, rfl⟩ : ∃ i, t = (((D, 1, 0) : ℕ × ℕ × ℕ) :: jk1 D N).length + (i + 1) :=
    ⟨t - ((jk1 D N).length + 2), by simp; omega⟩
  have hi : i < (jk1 (D + 1) W).length := by simp at ht2; omega
  rw [unQW_eq3, entry_append_right]
  show D + 2 ≤ ((((D + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (D + 1) W).getD (i + 1)
    ((0, 0, 0) : ℕ × ℕ × ℕ)).1
  rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]
  have := jk1_ge W (D + 1) _ (List.getElem_mem hi)
  omega

theorem hMy_unQW {N W : Jk1} (hJN : JkA N) (hJW : JkA W) {D : ℕ} (hD : 1 ≤ D) :
    ∀ t, 1 ≤ t → t < (unQW N W D).length → entry (unQW N W D) 0 t < D + 2 →
      (∀ i, t < i → i < (unQW N W D).length →
        entry (unQW N W D) 0 t < entry (unQW N W D) 0 i) →
      2 ≤ entry (unQW N W D) 1 t := by
  intro t ht1 htl hlt hrec
  rcases Nat.lt_trichotomy t ((jk1 D N).length + 1) with h | h | h
  · exfalso
    have hmidlen : (jk1 D N).length + 1 < (unQW N W D).length := by
      rw [length_unQW]; omega
    have h2 := hrec ((jk1 D N).length + 1) h hmidlen
    rw [entry_unQW_mid0] at h2
    have hge : D + 1 ≤ entry (unQW N W D) 0 t := (MidD_unQW hJN hJW hD).tail t ht1 htl
    omega
  · rw [h, entry_unQW_mid1]
  · exfalso
    have := entry_unQW_right N W D t h htl
    omega

/-- 塔（`k+1` 段）と底から、`unQW N W D` の末尾に 2 の記録を継ぐ。 -/
theorem snocW_of_tower {N Wt : Jk1} (hJN : JkA N) (hJW : JkA Wt) {D : ℕ} (hD : 1 ≤ D)
    {X : TrioSeq} (hne : X ≠ []) (h0 : X ∈ W 0)
    (htw : ∀ k : ℕ, Mtwd 2 X (unQW N Wt D) (k + 1) ∈ W 0) :
    (X ++ unQW N Wt D) ++ [((D + 2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine snocYd_mem (Y0 := X) (M := unQW N Wt D) (L := D) (y := 2) (dl := 2) hne
    (MidD_unQW hJN hJW hD) ?_ (hMy_unQW hJN hJW hD) (by omega) (by omega) ?_
  · have he : entry (unQW N Wt D) 1 0 = 1 := rfl
    omega
  · intro n
    match n with
    | 0 => simpa [Mtwd] using h0
    | (k + 1) => exact htw k

#print axioms snocW_of_tower

/-! #### 語の等式（目標側と階段側） -/

theorem unQW_target (N Wt : Jk1) (D : ℕ) :
    unQW N Wt D ++ [((D + 2, 2, 0) : ℕ × ℕ × ℕ)]
      = ((D, 1, 0) : ℕ × ℕ × ℕ) :: jk1 D (Jk1.two N (Jk1.two Wt Jk1.nil)) := by
  show (((D, 1, 0) : ℕ × ℕ × ℕ) :: jk1 D (Jk1.two N Wt)) ++ _ = _
  show ((D, 1, 0) : ℕ × ℕ × ℕ) :: ((jk1 D N ++ (((D + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      jk1 (D + 1) Wt)) ++ [((D + 2, 2, 0) : ℕ × ℕ × ℕ)])
    = ((D, 1, 0) : ℕ × ℕ × ℕ) :: (jk1 D N ++ (((D + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      jk1 (D + 1) (Jk1.two Wt Jk1.nil)))
  simp [jk1, List.append_assoc]

theorem colJ_plug_twoNWT (a b : ℕ) (ctx : List Frm) (V N Wt : Jk1) :
    colJ a b (plug (ctx ++ [Frm.fone V]) (Jk1.two N (Jk1.two Wt Jk1.nil)))
      = (colJ a b (plug ctx V) ++ unQW N Wt (a + dep ctx + 2))
        ++ [((a + dep ctx + 2 + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
  rw [plug_snoc, colJ_plug_one, ← unQW_target N Wt (a + dep ctx + 2)]
  simp [List.append_assoc]

theorem wordJ_snoc_twoNWT (a b : ℕ) (ws : List Jk1) (ctx : List Frm) (V N Wt : Jk1) :
    wordJ a b (ws ++ [plug (ctx ++ [Frm.fone V]) (Jk1.two N (Jk1.two Wt Jk1.nil))])
      = (wordJ a b (ws ++ [plug ctx V]) ++ unQW N Wt (a + dep ctx + 2))
        ++ [((a + dep ctx + 2 + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
  rw [wordJ_append, wordJ_singleton, colJ_plug_twoNWT, wordJ_append, wordJ_singleton]
  simp [List.append_assoc]

theorem colJ_plug_nstW (a b : ℕ) (ctx : List Frm) (V N Wt : Jk1) (k : ℕ) :
    colJ a b (plug (ctx ++ [Frm.fone V]) (nstW N Wt k))
      = colJ a b (plug ctx V)
        ++ (List.range (k + 1)).flatMap
            (fun j => shiftr01 (2 * j) 0 (unQW N Wt (a + dep ctx + 2))) := by
  rw [plug_snoc, colJ_plug_one, ← jk1_nstW N Wt k (a + dep ctx + 2)]

theorem wordJ_snoc_nstW (a b : ℕ) (ws : List Jk1) (ctx : List Frm) (V N Wt : Jk1) (k : ℕ) :
    wordJ a b (ws ++ [plug (ctx ++ [Frm.fone V]) (nstW N Wt k)])
      = Mtwd 2 (wordJ a b (ws ++ [plug ctx V])) (unQW N Wt (a + dep ctx + 2)) (k + 1) := by
  rw [wordJ_append, wordJ_singleton, colJ_plug_nstW, wordJ_append, wordJ_singleton, Mtwd]
  simp [List.append_assoc]

#print axioms wordJ_snoc_twoNWT
#print axioms wordJ_snoc_nstW

/-! #### ★★★ `GOK_stkW_gen` の内側兄弟一般版 -/

theorem GOK_twoNW_gen (ctx0 : List Frm) (V : Jk1) {N Wt : Jk1} (hJN : JkA N)
    (hJW : JkA Wt)
    (hJT : JkT (plug (ctx0 ++ [Frm.fone V]) (Jk1.two N (Jk1.two Wt Jk1.nil))))
    (hGV : GOK (plug ctx0 V))
    (hstair : ∀ k : ℕ, GOK (plug (ctx0 ++ [Frm.fone V]) (nstW N Wt k))) :
    GOK (plug (ctx0 ++ [Frm.fone V]) (Jk1.two N (Jk1.two Wt Jk1.nil))) := by
  intro ws hw hG
  have hwO : WOk (ws ++ [plug (ctx0 ++ [Frm.fone V])
      (Jk1.two N (Jk1.two Wt Jk1.nil))]) := WOk_append hw (WOk_singletonT hJT)
  have hbaseV : GoodFb (fun a b => wordJ a b (ws ++ [plug ctx0 V])) := hGV ws hw hG
  have hstG : ∀ k : ℕ,
      GoodFb (fun a b => wordJ a b
        (ws ++ [plug (ctx0 ++ [Frm.fone V]) (nstW N Wt k)])) :=
    fun k => hstair k ws hw hG
  refine ⟨fun a b => wordJ_ge a b _, fun a b => wordJ_mono hwO,
    fun a b s => wordJ_shift a b s _, ?_, ?_, ?_⟩
  · -- pu
    intro y c hy
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) (y + 1) _ x hx; omega, wordJ_mono hwO, ?_⟩
    intro E hE t Z hZ
    rw [wordJ_shift, wordJ_snoc_twoNWT]
    have h0 : Z ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ (c + 1 + t) (y + 1) (ws ++ [plug ctx0 V])) ∈ W 0 := by
      have h1 := (hbaseV.pu y c hy).2.2 E hE t Z hZ
      rw [wordJ_shift] at h1
      exact h1
    have htw : ∀ k : ℕ, Mtwd 2 (Z ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ (c + 1 + t) (y + 1) (ws ++ [plug ctx0 V])))
        (unQW N Wt (c + 1 + t + dep ctx0 + 2)) (k + 1) ∈ W 0 := by
      intro k
      have h1 := ((hstG k).pu y c hy).2.2 E hE t Z hZ
      rw [wordJ_shift, wordJ_snoc_nstW] at h1
      simpa [Mtwd, List.append_assoc] using h1
    have h := snocW_of_tower hJN hJW (D := c + 1 + t + dep ctx0 + 2) (by omega)
      (X := Z ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ (c + 1 + t) (y + 1) (ws ++ [plug ctx0 V]))) (by simp) h0 htw
    simpa [List.append_assoc] using h
  · -- pk
    intro c E hI
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) 2 _ x hx; omega, wordJ_mono hwO, ?_⟩
    intro j t Z hZ
    rw [wordJ_shift, wordJ_snoc_twoNWT]
    have h0 : Z ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++
        wordJ (c + 1 + t) 2 (ws ++ [plug ctx0 V])) ∈ W 0 := by
      have h1 := (hbaseV.pk c E hI).2.2 j t Z hZ
      rw [wordJ_shift] at h1
      exact h1
    have htw : ∀ k : ℕ, Mtwd 2 (Z ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++
        wordJ (c + 1 + t) 2 (ws ++ [plug ctx0 V])))
        (unQW N Wt (c + 1 + t + dep ctx0 + 2)) (k + 1) ∈ W 0 := by
      intro k
      have h1 := ((hstG k).pk c E hI).2.2 j t Z hZ
      rw [wordJ_shift, wordJ_snoc_nstW] at h1
      simpa [Mtwd, List.append_assoc] using h1
    have h := snocW_of_tower hJN hJW (D := c + 1 + t + dep ctx0 + 2) (by omega)
      (X := Z ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++
        wordJ (c + 1 + t) 2 (ws ++ [plug ctx0 V]))) (by simp) h0 htw
    simpa [List.append_assoc] using h
  · -- seg
    intro h
    have hmid : MidD (h + 2) (((h + 1, 1, 0) : ℕ × ℕ × ℕ) ::
        wordJ (h + 1) 1 (ws ++ [plug (ctx0 ++ [Frm.fone V])
          (Jk1.two N (Jk1.two Wt Jk1.nil))])) := by
      have h1 := MidD_wordJ (h + 1) 1 (by omega) (by omega) hwO
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    refine ⟨hmid, by simp [entry], ?_⟩
    intro P hP s A' hA'
    rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ (h + 1) 1
            (ws ++ [plug (ctx0 ++ [Frm.fone V]) (Jk1.two N (Jk1.two Wt Jk1.nil))])
        = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordJ (h + 1) 1
            (ws ++ [plug (ctx0 ++ [Frm.fone V]) (Jk1.two N (Jk1.two Wt Jk1.nil))])
        from rfl,
      shiftr01_append0, shift_col, wordJ_shift, wordJ_snoc_twoNWT]
    have h0 : A' ++ ([((h + 1 + s, 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ (h + 1 + s) 1 (ws ++ [plug ctx0 V])) ∈ W 0 := by
      have h1 := (hbaseV.seg (h + s)).reapp P hP 0 A' (by simpa using hA')
      rw [show ((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ (h + s + 1) 1 (ws ++ [plug ctx0 V])
          = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordJ (h + s + 1) 1 (ws ++ [plug ctx0 V])
          from rfl] at h1
      simpa [show h + s + 1 = h + 1 + s from by omega] using h1
    have htw : ∀ k : ℕ, Mtwd 2 (A' ++ ([((h + 1 + s, 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ (h + 1 + s) 1 (ws ++ [plug ctx0 V])))
        (unQW N Wt (h + 1 + s + dep ctx0 + 2)) (k + 1) ∈ W 0 := by
      intro k
      have h1 := ((hstG k).seg (h + s)).reapp P hP 0 A' (by simpa using hA')
      rw [show ((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ (h + s + 1) 1
              (ws ++ [plug (ctx0 ++ [Frm.fone V]) (nstW N Wt k)])
          = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordJ (h + s + 1) 1
              (ws ++ [plug (ctx0 ++ [Frm.fone V]) (nstW N Wt k)]) from rfl,
        wordJ_snoc_nstW] at h1
      simpa [Mtwd, show h + s + 1 = h + 1 + s from by omega, List.append_assoc] using h1
    have hh := snocW_of_tower hJN hJW (D := h + 1 + s + dep ctx0 + 2) (by omega)
      (X := A' ++ ([((h + 1 + s, 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ (h + 1 + s) 1 (ws ++ [plug ctx0 V]))) (by simp) h0 htw
    simpa [List.append_assoc] using hh



#print axioms GOK_twoNW_gen

/-! ### ★★★ `ChBase` は階段 `∀ k, LOk 1 (nstW N Wt k)` 1 本に落ちる

`GOK_twoNW_gen` の階段は `nstW N Wt k` で、

    nstW N Wt 0     = two N Wt              ← `TwoOk Wt` そのもの
    nstW N Wt (k+1) = two N (one Wt (nstW N Wt k))
                                            ← `TwoOk_one`（緑）で `LOk 1 (nstW N Wt k)` に落ちる

だから `ChBase` に残るのは `LOk 1 (nstW N Wt k)` だけ。 -/

def ChStair : Prop := ∀ (N Wt : Jk1), JkA N →
  (∀ (j : ℕ) (kk : List Bool), APd (List.replicate j true ++ (true :: kk)) N) →
  JkA Wt → TwoOk Wt → ∀ k : ℕ, LOk 1 (nstW N Wt k)

theorem ChBase_of_ChStair (h : ChStair) : ChBase := by
  intro X hJX hXk N hJN hNall j kk
  rw [rep_true_cons, APd_iff]
  intro ctx hc
  have hcO : CtxOk ctx := GCtx_CtxOk _ ctx hc
  obtain ⟨ctx0, V, rfl, hGV⟩ := GCtx_split (List.replicate j true ++ kk) ctx hc
  refine GOK_twoNW_gen ctx0 V hJN hJX ?_ hGV ?_
  · exact JkT_plug _ hcO _ ((CtxX_snoc1 ctx0 V _).mpr ⟨hJN, hJX, trivial⟩)
  · intro k
    refine (APd_iff (true :: (List.replicate j true ++ kk)) _).mp ?_ _ hc
    match k with
    | 0 =>
        have hh := hXk N hJN hNall j kk
        rw [rep_true_cons] at hh
        exact hh
    | (k + 1) =>
        have hone : TwoOk (Jk1.one X (nstW N X k)) :=
          TwoOk_one hJX hXk (h N X hJN hNall hJX hXk k)
        have hh := hone N hJN hNall j kk
        rw [rep_true_cons] at hh
        exact hh

/-- ★★★★★★ いま開いている最小の行列は `ChStair` 1 本から出る。 -/
theorem R375m61_of_ChStair (h : ChStair) :
    R375m ++ [((6, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  R375m61_of_ChBase (ChBase_of_ChStair h)

#print axioms ChBase_of_ChStair
#print axioms R375m61_of_ChStair

/-! ### ★★★ 階段 `nstW` は `TwOk` の梯子でそのまま登れる

`TwOk_two`（緑）は「直下が 1 の列の枠なら 2 の記録の枠を 1 枚足せる」で、
段 `r` が 1 上がる。`nstW N W (k+1) = two N (one W (nstW N W k))` は
2 の記録 1 枚と 1 の列の枠 1 枚なので、`TwOk_two` と `TwOk_one` を交互に使えば
`k` の帰納がそのまま回る（`r`, `m` は全称のまま）。 -/

theorem TwOk_nstW {N W : Jk1} (hJN : JkA N) (hJW : JkA W)
    (hN : ∀ r : ℕ, NTw r N) (hW : ∀ r : ℕ, TwOk (r + 1) 0 W) :
    ∀ (k r m : ℕ), Fter r m → TwOk r m (nstW N W k)
  | 0, r, m, hf => TwOk_two hJN (hN r) hf (hW r)
  | (k + 1), r, m, hf =>
      TwOk_two hJN (hN r) hf
        (TwOk_one (r + 1) 0 hJW (hW r)
          (TwOk_nstW hJN hJW hN hW k (r + 1) 1 (Fter_succ (r + 1) 0)))

/-- 階段の `LOk 1`（`ChStair` が要る形）。 -/
theorem LOk1_nstW {N W : Jk1} (hJN : JkA N) (hJW : JkA W)
    (hN : ∀ r : ℕ, NTw r N) (hW : ∀ r : ℕ, TwOk (r + 1) 0 W) (k : ℕ) :
    LOk 1 (nstW N W k) :=
  LOk_of_TwOk0 (TwOk_nstW hJN hJW hN hW k 0 0 (Fter_zero 0))

#print axioms TwOk_nstW
#print axioms LOk1_nstW

/-- ★★★ `ChBase` の「兄弟が梯子を登れる」版。`GOK_twoNW_gen` + `LOk1_nstW`。 -/
theorem TwoOk_twoWnil {N W : Jk1} (hJN : JkA N)
    (hNapd : ∀ (j : ℕ) (kk : List Bool), APd (List.replicate j true ++ (true :: kk)) N)
    (hNtw : ∀ r : ℕ, NTw r N) (hJW : JkA W) (hWok : TwoOk W)
    (hWtw : ∀ r : ℕ, TwOk (r + 1) 0 W) (j : ℕ) (kk : List Bool) :
    APd (List.replicate j true ++ (true :: kk)) (Jk1.two N (Jk1.two W Jk1.nil)) := by
  rw [rep_true_cons, APd_iff]
  intro ctx hc
  have hcO : CtxOk ctx := GCtx_CtxOk _ ctx hc
  obtain ⟨ctx0, V, rfl, hGV⟩ := GCtx_split (List.replicate j true ++ kk) ctx hc
  refine GOK_twoNW_gen ctx0 V hJN hJW ?_ hGV ?_
  · exact JkT_plug _ hcO _ ((CtxX_snoc1 ctx0 V _).mpr ⟨hJN, hJW, trivial⟩)
  · intro k
    refine (APd_iff (true :: (List.replicate j true ++ kk)) _).mp ?_ _ hc
    match k with
    | 0 =>
        have hh := hWok N hJN hNapd j kk
        rw [rep_true_cons] at hh
        exact hh
    | (k + 1) =>
        have hone : TwoOk (Jk1.one W (nstW N W k)) :=
          TwoOk_one hJW hWok (LOk1_nstW hJN hJW hNtw hWtw k)
        have hh := hone N hJN hNapd j kk
        rw [rep_true_cons] at hh
        exact hh

#print axioms TwoOk_twoWnil

/-! ### ★★★ 梯子の条件は `W ↦ two W nil` で閉じている

`TwSt (r+1) 0` の文脈は `TwSt r m'`（`Fter r m'` つき、＝ 1 の枠で終わる）の上に
2 の枠を 1 枚。だから `plug D (two W nil) = plug D' (two N (two W nil))` で
`GOK_twoNW_gen` がそのまま当たる。階段は `TwOk_nstW`。
**`Fter` は「2 の記録の直上に 2 の記録は置けない」だが、荷が `nil` のこの形は通る。** -/

theorem TwSt_fone : ∀ (r m : ℕ), Fter r m → ∀ D : List Frm, TwSt r m D →
    ∃ (ctx0 : List Frm) (V : Jk1), D = ctx0 ++ [Frm.fone V] ∧ GOK (plug ctx0 V)
  | 0, m, _, D, hD => by
      obtain ⟨D', U, rfl, hD', hJU, hU⟩ := (TwSt_z m D).mp hD
      exact ⟨D', U, rfl, hU D' hD'⟩
  | (r + 1), 0, hf, D, hD => by
      rcases hf with h | h
      · exact absurd h (by omega)
      · exact absurd h (by omega)
  | (r + 1), (m + 1), _, D, hD => by
      obtain ⟨D', U, rfl, hD', hJU, hU⟩ := (TwSt_f r m D).mp hD
      exact ⟨D', U, rfl, hU D' hD'⟩

/-- ★ 梯子を登れない理由: `TwSt (r+1) 0` の 2 の枠の兄弟 `N` に付く条件は
`NTw r N`（その段だけ）。ところが階段 `nstW N W k` は**同じ `N` を毎段使う**ので
`TwOk_nstW` は `∀ r, NTw r N` を要求する。ここが合わない。 -/
theorem TwSt_fone_note : True := trivial

#print axioms TwSt_fone

/-! ### ★★★ 階段を `APd` の世界で回す（形が伸びるので `N` の普遍性がそのまま効く）

`APd_cf` を `m = 0` で使うと

    APd (false::ks) V → (N は普遍) → APd (true::ks) (two N V)

`nstW N W (k+1) = two N (one W (nstW N W k))` なので、`APd_step` で
`one W ·` を剥がすと形が `false::ks` に伸びる。`N` は普遍なので伸びても効く。
**`LOk 1` の梯子を登る必要が無い。** 代わりに `W` に
「どの `false::ks` にも差せる」（`TwoOkF`）と `TopOk W` が要る。 -/

theorem APd_twoN_of_cf {ks : List Bool} {N V : Jk1} (hJN : JkA N)
    (hNall : ∀ (j : ℕ) (kk : List Bool), APd (List.replicate j true ++ (true :: kk)) N)
    (h : APd (false :: ks) V) : APd (true :: ks) (Jk1.two N V) := by
  rw [APd_ct]
  intro U hU hR hUk
  exact (APd_cf ks V).mp h 0 U N (by simpa using hU) (by simpa using hR)
    (by simpa using hUk) hJN (fun j => by simpa using hNall j ks)

/-- 「どの予算の節 `false::ks` にも差せる」。`TwoOk` より強い。 -/
def TwoOkF (W : Jk1) : Prop := ∀ ks : List Bool, APd (false :: ks) W

theorem TwoOkF_nil : TwoOkF Jk1.nil := fun ks => APd_nil (false :: ks)

theorem TwoOkF_pay {W : Jk1} (hJW : JkA W) (h : TwoOkF W) {Y : TrioSeq} (hY : Bok Y) :
    TwoOkF (Jk1.pay W Y) := fun ks => AYdT' Y hY ks W hJW (h ks)

theorem TwoOkF_oneNil {W : Jk1} (hJW : JkA W) (hTW : TopOk W) (h : TwoOkF W) :
    TwoOkF (Jk1.one W Jk1.nil) := fun ks =>
  APd_step (false :: ks) (hJW : FrmJ (false :: ks) W) (hTW : Rq (false :: ks) W)
    (h ks) (APd_nilT (false :: ks))

theorem TwoOk_of_TwoOkF {W : Jk1} (h : TwoOkF W) : TwoOk W := by
  intro N hJN hNall j kk
  rw [rep_true_cons]
  exact APd_twoN_of_cf hJN hNall (h (List.replicate j true ++ kk))

/-- 階段。形が `false::ks` に伸びるだけで `N` の条件は普遍なので効き続ける。 -/
theorem APd_nstW {N W : Jk1} (hJN : JkA N)
    (hNall : ∀ (j : ℕ) (kk : List Bool), APd (List.replicate j true ++ (true :: kk)) N)
    (hJW : JkA W) (hTW : TopOk W) (hWF : TwoOkF W) :
    ∀ (k : ℕ) (ks : List Bool), APd (true :: ks) (nstW N W k)
  | 0, ks => APd_twoN_of_cf hJN hNall (hWF ks)
  | (k + 1), ks =>
      APd_twoN_of_cf hJN hNall
        (APd_step (false :: ks) (hJW : FrmJ (false :: ks) W) (hTW : Rq (false :: ks) W)
          (hWF ks) (APd_nstW hJN hNall hJW hTW hWF k (false :: ks)))

/-- ★★★★★★ `TopOk` かつ「どの予算の節にも差せる」木は `two W nil` にできる。
`ChBase` の（兄弟を制限した）版。 -/
theorem TwoOk_twoWnilF {W : Jk1} (hJW : JkA W) (hTW : TopOk W) (hWF : TwoOkF W) :
    TwoOk (Jk1.two W Jk1.nil) := by
  intro N hJN hNall j kk
  rw [rep_true_cons, APd_iff]
  intro ctx hc
  have hcO : CtxOk ctx := GCtx_CtxOk _ ctx hc
  obtain ⟨ctx0, V, rfl, hGV⟩ := GCtx_split (List.replicate j true ++ kk) ctx hc
  refine GOK_twoNW_gen ctx0 V hJN hJW ?_ hGV ?_
  · exact JkT_plug _ hcO _ ((CtxX_snoc1 ctx0 V _).mpr ⟨hJN, hJW, trivial⟩)
  · intro k
    exact (APd_iff (true :: (List.replicate j true ++ kk)) _).mp
      (APd_nstW hJN hNall hJW hTW hWF k _) _ hc

#print axioms APd_nstW
#print axioms TwoOk_twoWnilF

/-! ### ★★★ 階段を文脈の族で書く（`TopOk` も `APd` の形も要らない）

`nstW N W (k+1) = two N (one W (nstW N W k))` は文脈でいうと枠 2 枚
`[ftwo N, fone W]` を足すだけ:

    plug D (nstW N W (k+1)) = plug (D ++ [ftwo N, fone W]) (nstW N W k)

だから階段は「`two N W` がブロック `[ftwo N, fone W]` を何個足した文脈でも良い」
（`SelfW` 型の自己塔）1 本になる。`APd` の形を経由しないので `Rq`（＝ `TopOk W`）が
要らない。 -/

def blkNW (N W : Jk1) : ℕ → List Frm
  | 0 => []
  | (i + 1) => [Frm.ftwo N, Frm.fone W] ++ blkNW N W i

theorem plug_blkNW_step (N W : Jk1) (D : List Frm) (Z : Jk1) :
    plug (D ++ [Frm.ftwo N, Frm.fone W]) Z = plug D (Jk1.two N (Jk1.one W Z)) := by
  rw [show D ++ [Frm.ftwo N, Frm.fone W] = (D ++ [Frm.ftwo N]) ++ [Frm.fone W] from by simp,
    plug_snoc, plug_snoc2]

theorem GOK_nstW_of {N W : Jk1} : ∀ (k : ℕ) (D : List Frm),
    (∀ i : ℕ, GOK (plug (D ++ blkNW N W i) (Jk1.two N W))) →
    GOK (plug D (nstW N W k))
  | 0, D, hbase => by simpa [blkNW] using hbase 0
  | (k + 1), D, hbase => by
      have e : plug D (nstW N W (k + 1))
          = plug (D ++ [Frm.ftwo N, Frm.fone W]) (nstW N W k) := by
        rw [plug_blkNW_step]
        rfl
      rw [e]
      refine GOK_nstW_of k (D ++ [Frm.ftwo N, Frm.fone W]) (fun i => ?_)
      have hh := hbase (i + 1)
      simpa [blkNW, List.append_assoc] using hh

/-- ★★★★★★ `two N (two W nil)` は「`two N W` の自己塔」1 本から出る。 -/
theorem GOK_twoNW_self (ctx0 : List Frm) (V : Jk1) {N W : Jk1} (hJN : JkA N) (hJW : JkA W)
    (hJT : JkT (plug (ctx0 ++ [Frm.fone V]) (Jk1.two N (Jk1.two W Jk1.nil))))
    (hGV : GOK (plug ctx0 V))
    (hself : ∀ i : ℕ,
      GOK (plug ((ctx0 ++ [Frm.fone V]) ++ blkNW N W i) (Jk1.two N W))) :
    GOK (plug (ctx0 ++ [Frm.fone V]) (Jk1.two N (Jk1.two W Jk1.nil))) :=
  GOK_twoNW_gen ctx0 V hJN hJW hJT hGV
    (fun k => GOK_nstW_of k (ctx0 ++ [Frm.fone V]) hself)

#print axioms GOK_nstW_of
#print axioms GOK_twoNW_self

/-! ### ★★★ 自己塔は「ブロックを 1 個差し込む」1 歩に落ちる

`blkNW` のブロックは全部同じなので後ろにも足せる。すると自己塔は

    GOK (plug D' (two N W)) → GOK (plug (D' ++ [ftwo N, fone W]) (two N W))

の 1 歩の反復。`plug (D' ++ [ftwo N, fone W]) (two N W)
= plug D' (two N (one W (two N W)))` なので、語で見ると
**ブロック `(l+2,1,0) [N↑] (l+3,2,0) [W↑]` を 1 個差し込む**だけ。 -/

theorem blkNW_snoc (N W : Jk1) : ∀ i : ℕ,
    blkNW N W (i + 1) = blkNW N W i ++ [Frm.ftwo N, Frm.fone W]
  | 0 => by simp [blkNW]
  | (i + 1) => by
      show [Frm.ftwo N, Frm.fone W] ++ blkNW N W (i + 1)
        = ([Frm.ftwo N, Frm.fone W] ++ blkNW N W i) ++ [Frm.ftwo N, Frm.fone W]
      rw [blkNW_snoc N W i, List.append_assoc]

theorem GOK_selfNW {N W : Jk1} (D : List Frm)
    (hbase : GOK (plug D (Jk1.two N W)))
    (hstep : ∀ D' : List Frm, GOK (plug D' (Jk1.two N W)) →
      GOK (plug (D' ++ [Frm.ftwo N, Frm.fone W]) (Jk1.two N W))) :
    ∀ i : ℕ, GOK (plug (D ++ blkNW N W i) (Jk1.two N W))
  | 0 => by simpa [blkNW] using hbase
  | (i + 1) => by
      rw [blkNW_snoc, ← List.append_assoc]
      exact hstep _ (GOK_selfNW D hbase hstep i)

/-- ★ 残る 1 文（`GOK` だけ）: 「`two N W` が良い**1 の枠で終わる**文脈には、
ブロック `[ftwo N, fone W]` を 1 枚足しても良い」。 -/
def SelfNW : Prop := ∀ (ctx : List Frm) (V N W : Jk1), JkA N →
  (∀ (j : ℕ) (kk : List Bool), APd (List.replicate j true ++ (true :: kk)) N) →
  JkA W → TwoOk W →
  GOK (plug (ctx ++ [Frm.fone V]) (Jk1.two N W)) →
  GOK (plug ((ctx ++ [Frm.fone V]) ++ [Frm.ftwo N, Frm.fone W]) (Jk1.two N W))

theorem GOK_selfNWf (h : SelfNW) {N W : Jk1} (hJN : JkA N)
    (hNall : ∀ (j : ℕ) (kk : List Bool), APd (List.replicate j true ++ (true :: kk)) N)
    (hJW : JkA W) (hWk : TwoOk W) :
    ∀ (i : ℕ) (ctx : List Frm) (V : Jk1),
      GOK (plug (ctx ++ [Frm.fone V]) (Jk1.two N W)) →
      GOK (plug ((ctx ++ [Frm.fone V]) ++ blkNW N W i) (Jk1.two N W))
  | 0, ctx, V, hb => by simpa [blkNW] using hb
  | (i + 1), ctx, V, hb => by
      have hb2 : GOK (plug ((ctx ++ [Frm.fone V, Frm.ftwo N]) ++ [Frm.fone W])
          (Jk1.two N W)) := by
        have hh := h ctx V N W hJN hNall hJW hWk hb
        simpa [List.append_assoc] using hh
      have hh := GOK_selfNWf h hJN hNall hJW hWk i (ctx ++ [Frm.fone V, Frm.ftwo N]) W hb2
      simpa [blkNW, List.append_assoc] using hh

theorem ChBase_of_SelfNW (h : SelfNW) : ChBase := by
  intro X hJX hXk N hJN hNall j kk
  rw [rep_true_cons, APd_iff]
  intro ctx hc
  have hcO : CtxOk ctx := GCtx_CtxOk _ ctx hc
  obtain ⟨ctx0, V, rfl, hGV⟩ := GCtx_split (List.replicate j true ++ kk) ctx hc
  have hb : GOK (plug (ctx0 ++ [Frm.fone V]) (Jk1.two N X)) := by
    have hh := hXk N hJN hNall j kk
    rw [rep_true_cons] at hh
    exact (APd_iff (true :: (List.replicate j true ++ kk)) _).mp hh _ hc
  refine GOK_twoNW_self ctx0 V hJN hJX ?_ hGV ?_
  · exact JkT_plug _ hcO _ ((CtxX_snoc1 ctx0 V _).mpr ⟨hJN, hJX, trivial⟩)
  · exact fun i => GOK_selfNWf h hJN hNall hJX hXk i ctx0 V hb

/-- ★★★★★★ いま開いている最小の行列は `SelfNW` 1 文から出る。 -/
theorem R375m61_of_SelfNW (h : SelfNW) :
    R375m ++ [((6, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  R375m61_of_ChBase (ChBase_of_SelfNW h)

#print axioms GOK_selfNWf

#print axioms ChBase_of_SelfNW
#print axioms R375m61_of_SelfNW

/-! ### ★★★ 予算の指数の型を一般にする（`ω^(ω+k)` を使うため）

`Bw = Colex (ℕ →₀ ℕ)` は `< ω^ω` までしか表せない。荷 `(0,0,0)(1,0,0)` は
`Y⟦n⟧ = (0,0,0)^n` に落ちて予算 `ω^n` を要求するので、その親には `ω^ω` が要る。
指数を `ℕ ×ₗ ℕ`（順序型 ω²）にすれば `ω^(ω+k) = owG (1,k) 1` が使える。 -/

section OwGen

variable {α : Type} [LinearOrder α]

abbrev BwG (α : Type) [LinearOrder α] : Type := Colex (α →₀ ℕ)

noncomputable def owG (k : α) (m : ℕ) : BwG α := toColex (Finsupp.single k m)

theorem bot_BwG : (⊥ : BwG α) = 0 := rfl

theorem owG_zero (k : α) : owG k 0 = (⊥ : BwG α) := by
  show toColex (Finsupp.single k 0) = toColex (0 : α →₀ ℕ)
  rw [Finsupp.single_zero]

theorem owG_ltR (k : α) {m m' : ℕ} (h : m < m') : owG k m < owG k m' := by
  rw [owG, owG, Finsupp.Colex.lt_iff]
  refine ⟨k, ?_, ?_⟩
  · intro j hj
    show (Finsupp.single k m : α →₀ ℕ) j = (Finsupp.single k m' : α →₀ ℕ) j
    rw [Finsupp.single_apply, Finsupp.single_apply, if_neg (ne_of_lt hj),
      if_neg (ne_of_lt hj)]
  · show (Finsupp.single k m : α →₀ ℕ) k < (Finsupp.single k m' : α →₀ ℕ) k
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    exact h

theorem owG_ltL {k k' : α} (h : k < k') (m : ℕ) {m' : ℕ} (hm : 0 < m') :
    owG k m < owG k' m' := by
  rw [owG, owG, Finsupp.Colex.lt_iff]
  refine ⟨k', ?_, ?_⟩
  · intro j hj
    show (Finsupp.single k m : α →₀ ℕ) j = (Finsupp.single k' m' : α →₀ ℕ) j
    rw [Finsupp.single_apply, Finsupp.single_apply, if_neg (ne_of_lt (lt_trans h hj)),
      if_neg (ne_of_lt hj)]
  · show (Finsupp.single k m : α →₀ ℕ) k' < (Finsupp.single k' m' : α →₀ ℕ) k'
    rw [Finsupp.single_apply, Finsupp.single_eq_same, if_neg (ne_of_lt h)]
    exact hm

theorem owG_add_lt {j k : α} (h : j < k) (m m' : ℕ) :
    owG k m + owG j m' < owG k (m + 1) := by
  rw [Finsupp.Colex.lt_iff]
  refine ⟨k, ?_, ?_⟩
  · intro i hi
    show (Finsupp.single k m + Finsupp.single j m' : α →₀ ℕ) i
        = (Finsupp.single k (m + 1) : α →₀ ℕ) i
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (ne_of_lt hi), if_neg (ne_of_lt (lt_trans h hi)), if_neg (ne_of_lt hi)]
    rfl
  · show (Finsupp.single k m + Finsupp.single j m' : α →₀ ℕ) k
        < (Finsupp.single k (m + 1) : α →₀ ℕ) k
    rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply,
      Finsupp.single_eq_same, if_neg (ne_of_lt h)]
    omega

theorem BwG_add_lt_left (b : BwG α) {x y : BwG α} (h : x < y) : b + x < b + y := by
  rw [add_comm b x, add_comm b y]
  exact add_lt_add_left h b

end OwGen

/-- 指数が `ℕ ×ₗ ℕ`（順序型 ω²）の予算。`ω^(ω·i + j) = owG (toLex (i,j)) 1`。 -/
abbrev Bw2 : Type := BwG (ℕ ×ₗ ℕ)

noncomputable def ex2 (i j : ℕ) : (ℕ ×ₗ ℕ) := toLex (i, j)

theorem ex2_lt_r (i : ℕ) {j j' : ℕ} (h : j < j') : ex2 i j < ex2 i j' :=
  Prod.Lex.right i h

theorem ex2_lt_l {i i' : ℕ} (h : i < i') (j j' : ℕ) : ex2 i j < ex2 i' j' :=
  Prod.Lex.left j j' h

example : WellFoundedLT Bw2 := inferInstance
example : OrderBot Bw2 := inferInstance
example : LinearOrder Bw2 := inferInstance

#print axioms owG_add_lt

theorem WPdw_run2 : ∀ (k : ℕ) (β : Bw2) (A : Jk1), JkA A →
    (∀ c : Bw2, β < c → ∀ ks : List Bw2, WPdT (c :: ks) A) →
    ∀ (m : ℕ) (c : Bw2), β + owG (ex2 0 k) m < c → ∀ ks : List Bw2,
      WPdT (c :: ks) (twoIt A (Zk k) m)
  | 0, β, A, _, hA, 0, c, hc, ks => hA c (by rwa [owG_zero, bot_BwG, add_zero] at hc) ks
  | (k + 1), β, A, _, hA, 0, c, hc, ks => hA c (by rwa [owG_zero, bot_BwG, add_zero] at hc) ks
  | 0, β, A, hJA, hA, (m + 1), c, hc, ks => by
      have hstep : β + owG (ex2 0 0) m < β + owG (ex2 0 0) (m + 1) := BwG_add_lt_left β (owG_ltR (ex2 0 0) (by omega))
      refine WPdT_twoA_runB (a := β + owG (ex2 0 0) (m + 1))
        (ne_bot_of_gt (lt_of_le_of_lt bot_le hstep)) hc
        (JkA_twoItP hJA (JkA_Zk 0) m) ?_ ks
      intro ks'
      exact WPdw_run2 0 β A hJA hA m (β + owG (ex2 0 0) (m + 1)) hstep ks'
  | (k + 1), β, A, hJA, hA, (m + 1), c, hc, ks => by
      have hstep : β + owG (ex2 0 (k + 1)) m < β + owG (ex2 0 (k + 1)) (m + 1) :=
        BwG_add_lt_left β (owG_ltR (ex2 0 (k + 1)) (by omega))
      have hJA' : JkA (twoIt A (Zk (k + 1)) m) := JkA_twoItP hJA (JkA_Zk (k + 1)) m
      have hA' : ∀ c' : Bw2, β + owG (ex2 0 (k + 1)) m < c' → ∀ ks' : List Bw2,
          WPdT (c' :: ks') (twoIt A (Zk (k + 1)) m) :=
        fun c' hc' ks' => WPdw_run2 (k + 1) β A hJA hA m c' hc' ks'
      refine WPdT_twoAZ_top
        (S := ⟨fun i => (β + owG (ex2 0 (k + 1)) m) + owG (ex2 0 k) i,
          fun _ _ hij => BwG_add_lt_left _ (owG_ltR (ex2 0 k) hij)⟩)
        (t := c) ?_ hJA' (JkA_Zk k) ?_ ks
      · intro i
        show (β + owG (ex2 0 (k + 1)) m) + owG (ex2 0 k) i < c
        rw [add_assoc]
        exact lt_trans (BwG_add_lt_left β (owG_add_lt (ex2_lt_r 0 (by omega : k < k + 1)) m i)) hc
      · intro m' c' hc' ks'
        exact WPdw_run2 k (β + owG (ex2 0 (k + 1)) m) (twoIt A (Zk (k + 1)) m) hJA' hA' m' c' hc' ks'
termination_by k _ _ _ _ m _ _ _ => (k, m)


#print axioms WPdw_run2

/-! ### ★★★ 荷 `Y1 = (0,0,0)(1,0,0)` とその展開

`R600(7,0,0)(6,0,0)^k = R375m ++ shiftr01 6 0 ((0,0,0)(1,0,0)(0,0,0)^k)` なので、
この荷が要る。`Y1⟦n⟧ = (0,0,0)^n` なので予算は `ω^n` の上限＝`ω^ω` が要る。 -/

def Y1 : TrioSeq := [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 0, 0) : ℕ × ℕ × ℕ)]

theorem Y1_len : Y1.length = 2 := by simp [Y1]

theorem Flat_Y1 : Flat Y1 := by
  intro c hc
  simp only [Y1, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem Bok_Y1 : Bok Y1 := Bok_flat Flat_Y1 (by simp [Y1, entry])

theorem Y1_srow : srow Y1 1 = 0 := by simp [srow, Y1, entry]

theorem Y1_hasParent : hasParent Y1 0 1 := by
  rw [hasParent_zero_iff (by rw [Y1_len]; omega)]
  exact ⟨0, by omega, by simp [Y1, entry]⟩

theorem Y1_parent : parent Y1 0 1 = 0 := by
  have h := parent_nextR Y1_hasParent
  rw [nextR, if_pos rfl] at h
  obtain ⟨-, -, hlt, hval, -⟩ := h
  omega

theorem oper_Y1 (n : ℕ) :
    Y1⟦n⟧ = (List.range n).flatMap fun _ => [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
  have h1 : Y1.length - 1 = 1 := by rw [Y1_len]
  simp only [oper, h1, Y1_srow, Y1_parent]
  rw [if_neg (by omega), if_neg (by simp [Y1, entry]),
    if_neg (by rw [h1, Y1_srow]; exact not_not_intro Y1_hasParent)]
  simp [Y1, entry, List.range']

#print axioms Bok_Y1
#print axioms oper_Y1

theorem jk1_payY1oper (n l : ℕ) :
    jk1 l (Jk1.pay Jk1.nil (Y1⟦n⟧)) = jk1 l (Zk n) := by
  show jk1 l Jk1.nil ++ shiftr01 (l + 1) 0 (Y1⟦n⟧) = _
  rw [oper_Y1 n, flatMap_singleton_range, jk1_Zk n l]
  simp [jk1, shiftr01]

/-- ★★★ 荷 `Y1` を乗せた 2 の記録。`Y1⟦n⟧ = (0,0,0)^n` なので
`Zk n` の鎖（予算 `ω^n`）を全部超える `ω^ω = owG (ex2 1 0) 1` が要る。 -/
theorem WPdT_twoAY1_at {A : Jk1} (hJA : JkA A) (β : Bw2)
    (hchain : ∀ (n m : ℕ) (c : Bw2), β + owG (ex2 0 n) m < c → ∀ ks : List Bw2,
      WPdT (c :: ks) (twoIt A (Zk n) m))
    {t : Bw2} (ht : β + owG (ex2 1 0) 1 ≤ t)
    {B : List Bw2} {N : Jk1} (hJN : JkA N)
    (hNt : ∀ q : List Bw2, (∀ x ∈ q, x < t) → WPdT ((⊥ : Bw2) :: q ++ B) N) :
    WPdT ((⊥ : Bw2) :: B) (Jk1.two N (Jk1.two A (Jk1.pay Jk1.nil Y1))) := by
  rw [WPdT_iff]
  intro ctx hc
  have hJT : JkT (plug (ctx ++ [Frm.ftwo N]) (Jk1.two A (Jk1.pay Jk1.nil Y1))) := by
    rw [plug_snoc2]
    exact WCtxU_JkT ((⊥ : Bw2) :: B) ctx hc
      (Jk1.two N (Jk1.two A (Jk1.pay Jk1.nil Y1)))
      (⟨hJN, hJA, trivial, Bok_Y1⟩ : FrmNT ((⊥ : Bw2) :: B)
        (Jk1.two N (Jk1.two A (Jk1.pay Jk1.nil Y1))))
  intro ws hw hG
  rw [← plug_snoc2]
  have hlen2 : 2 ≤ Y1.length := by rw [Y1_len]
  have hp : hasParent Y1 (srow Y1 (Y1.length - 1)) (Y1.length - 1) := by
    rw [Y1_len]
    simpa [Y1_srow] using Y1_hasParent
  refine GoodFb_snoc_innerJt0 hw hJT hlen2 hp ?_
  intro n hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hstep : ∀ m : ℕ, β + owG (ex2 0 n') m < β + owG (ex2 0 (n' + 1)) 1 :=
    fun m => BwG_add_lt_left β (owG_ltL (ex2_lt_r 0 (by omega)) m (by omega))
  have hle : β + owG (ex2 0 (n' + 1)) 1 ≤ t :=
    le_of_lt (lt_of_lt_of_le
      (BwG_add_lt_left β (owG_ltL (ex2_lt_l (by omega) (n' + 1) 0) 1 (by omega))) ht)
  have hw2 : WPdT ((⊥ : Bw2) :: B) (Jk1.two N (Jk1.two A (Zk (n' + 1)))) :=
    WPdT_twoAZ_at (S := ⟨fun i => β + owG (ex2 0 n') i,
        fun _ _ hij => BwG_add_lt_left β (owG_ltR (ex2 0 n') hij)⟩)
      (t := β + owG (ex2 0 (n' + 1)) 1) hstep hJA (JkA_Zk n')
      (fun m c hc' ks' => hchain n' m c hc' ks') hJN
      (fun q hq => hNt q (fun x hx => lt_of_lt_of_le (hq x hx) hle))
  have hw3 : WPdT ((⊥ : Bw2) :: B)
      (Jk1.two N (Jk1.two A (Jk1.pay Jk1.nil (Y1⟦n' + 1⟧)))) := by
    refine WPdT_congr ((⊥ : Bw2) :: B) (fun l => ?_) hw2
    show jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
        (jk1 (l + 1) A ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 2) (Zk (n' + 1)))))
      = jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
        (jk1 (l + 1) A ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) ::
          jk1 (l + 2) (Jk1.pay Jk1.nil (Y1⟦n' + 1⟧)))))
    rw [jk1_payY1oper]
  have hh := (WPdT_iff ((⊥ : Bw2) :: B) _).mp hw3 ctx hc ws hw hG
  rw [← plug_snoc2] at hh
  exact hh

#print axioms WPdT_twoAY1_at

theorem owG_add_same {α : Type} [LinearOrder α] (e : α) (m : ℕ) :
    owG e m + owG e 1 = owG e (m + 1) := by
  show toColex (Finsupp.single e m) + toColex (Finsupp.single e 1) = toColex _
  rw [show (toColex (Finsupp.single e m) + toColex (Finsupp.single e 1) : BwG α)
      = toColex (Finsupp.single e m + Finsupp.single e 1) from rfl,
    ← Finsupp.single_add]

theorem WPdT_twoAY1_top {A : Jk1} (hJA : JkA A) (β : Bw2)
    (hchain : ∀ (n m : ℕ) (c : Bw2), β + owG (ex2 0 n) m < c → ∀ ks : List Bw2,
      WPdT (c :: ks) (twoIt A (Zk n) m))
    {t : Bw2} (ht : β + owG (ex2 1 0) 1 < t) (ks : List Bw2) :
    WPdT (t :: ks) (Jk1.two A (Jk1.pay Jk1.nil Y1)) :=
  have htb : t ≠ ⊥ := ne_bot_of_gt (lt_of_le_of_lt bot_le ht)
  (WPdT_cb htb ks _).mpr (fun r hr U N hU hUk hJN hNt =>
    WPdT_two_of_ctx hU hUk
      (fun ctx hc => (WPdT_iff ((⊥ : Bw2) :: (r ++ ks)) _).mp
        (WPdT_twoAY1_at hJA β hchain (le_of_lt ht) hJN hNt) ctx hc))

/-! ### 荷 `Y1` を底にした入れ子 `Zy k` -/

def Zy : ℕ → Jk1
  | 0 => Jk1.pay Jk1.nil Y1
  | (k + 1) => Jk1.pay (Zy k) [((0, 0, 0) : ℕ × ℕ × ℕ)]

theorem JkA_Zy : ∀ k : ℕ, JkA (Zy k)
  | 0 => ⟨trivial, Bok_Y1⟩
  | (k + 1) => ⟨JkA_Zy k, Bok_zero⟩

theorem jk1_Zy : ∀ (k l : ℕ), jk1 l (Zy k)
    = ((l + 1, 0, 0) : ℕ × ℕ × ℕ) :: ((l + 2, 0, 0) : ℕ × ℕ × ℕ)
      :: List.replicate k ((l + 1, 0, 0) : ℕ × ℕ × ℕ)
  | 0, l => by
      show jk1 l Jk1.nil ++ shiftr01 (l + 1) 0 Y1 = _
      simp [jk1, Y1, shiftr01]
      omega
  | (k + 1), l => by
      show jk1 l (Zy k) ++ shiftr01 (l + 1) 0 [((0, 0, 0) : ℕ × ℕ × ℕ)] = _
      rw [jk1_Zy k l, List.replicate_succ']
      simp [shiftr01]

/-- ★★★ `Zy k` を上に乗せた走り `twoIt A (Zy k) m` は `β + ω^(ω+k)·m` を超える予算に置ける。 -/
theorem WPdw_runW : ∀ (k : ℕ) (β : Bw2) (A : Jk1), JkA A →
    (∀ c : Bw2, β < c → ∀ ks : List Bw2, WPdT (c :: ks) A) →
    ∀ (m : ℕ) (c : Bw2), β + owG (ex2 1 k) m < c → ∀ ks : List Bw2,
      WPdT (c :: ks) (twoIt A (Zy k) m)
  | 0, β, A, _, hA, 0, c, hc, ks => hA c (by rwa [owG_zero, bot_BwG, add_zero] at hc) ks
  | (k + 1), β, A, _, hA, 0, c, hc, ks => hA c (by rwa [owG_zero, bot_BwG, add_zero] at hc) ks
  | 0, β, A, hJA, hA, (m + 1), c, hc, ks => by
      have hJA' : JkA (twoIt A (Zy 0) m) := JkA_twoItP hJA (JkA_Zy 0) m
      have hA' : ∀ c' : Bw2, β + owG (ex2 1 0) m < c' → ∀ ks' : List Bw2,
          WPdT (c' :: ks') (twoIt A (Zy 0) m) :=
        fun c' hc' ks' => WPdw_runW 0 β A hJA hA m c' hc' ks'
      have hlt : (β + owG (ex2 1 0) m) + owG (ex2 1 0) 1 < c := by
        rw [add_assoc, owG_add_same]
        exact hc
      exact WPdT_twoAY1_top hJA' (β + owG (ex2 1 0) m)
        (fun n m' c' hc' ks' => WPdw_run2 n (β + owG (ex2 1 0) m) _ hJA' hA' m' c' hc' ks')
        hlt ks
  | (k + 1), β, A, hJA, hA, (m + 1), c, hc, ks => by
      have hstep : β + owG (ex2 1 (k + 1)) m < β + owG (ex2 1 (k + 1)) (m + 1) :=
        BwG_add_lt_left β (owG_ltR (ex2 1 (k + 1)) (by omega))
      have hJA' : JkA (twoIt A (Zy (k + 1)) m) := JkA_twoItP hJA (JkA_Zy (k + 1)) m
      have hA' : ∀ c' : Bw2, β + owG (ex2 1 (k + 1)) m < c' → ∀ ks' : List Bw2,
          WPdT (c' :: ks') (twoIt A (Zy (k + 1)) m) :=
        fun c' hc' ks' => WPdw_runW (k + 1) β A hJA hA m c' hc' ks'
      refine WPdT_twoAZ_top
        (S := ⟨fun i => (β + owG (ex2 1 (k + 1)) m) + owG (ex2 1 k) i,
          fun _ _ hij => BwG_add_lt_left _ (owG_ltR (ex2 1 k) hij)⟩)
        (t := c) ?_ hJA' (JkA_Zy k) ?_ ks
      · intro i
        show (β + owG (ex2 1 (k + 1)) m) + owG (ex2 1 k) i < c
        rw [add_assoc]
        exact lt_trans (BwG_add_lt_left β
          (owG_add_lt (ex2_lt_r 1 (by omega : k < k + 1)) m i)) hc
      · intro m' c' hc' ks'
        exact WPdw_runW k (β + owG (ex2 1 (k + 1)) m) (twoIt A (Zy (k + 1)) m)
          hJA' hA' m' c' hc' ks'
termination_by k _ _ _ _ m _ _ _ => (k, m)

#print axioms WPdw_runW

theorem owG_pos {α : Type} [LinearOrder α] (e : α) : (⊥ : BwG α) < owG e 1 := by
  rw [← owG_zero e]
  exact owG_ltR e (by omega)

theorem WPdw_twoZy : ∀ (k : ℕ) (ks : List Bw2),
    WPdT (owG (ex2 1 (k + 1)) 1 :: ks) (Jk1.two Jk1.nil (Zy k))
  | 0, ks => by
      refine WPdT_twoAY1_top (A := Jk1.nil) trivial ⊥
        (fun n m c hc ks' => WPdw_run2 n ⊥ Jk1.nil trivial
          (fun c' _ ks'' => WPdT_nilAll _) m c hc ks') ?_ ks
      rw [bot_BwG, zero_add]
      exact owG_ltL (ex2_lt_r 1 (by omega)) 1 (by omega)
  | (k + 1), ks => by
      refine WPdT_twoAZ_top (S := ⟨fun i => owG (ex2 1 k) i,
          fun _ _ hij => owG_ltR (ex2 1 k) hij⟩)
        (t := owG (ex2 1 (k + 2)) 1) (A := Jk1.nil) ?_ trivial (JkA_Zy k) ?_ ks
      · intro m
        exact owG_ltL (ex2_lt_r 1 (by omega)) m (by omega)
      · intro m c hc ks'
        exact WPdw_runW k ⊥ Jk1.nil trivial (fun c' _ ks'' => WPdT_nilAll _) m c
          (by rwa [bot_BwG, zero_add]) ks'

def Xy (k : ℕ) : Jk1 := Jk1.two Jk1.nil (Jk1.two Jk1.nil (Zy k))

theorem WPdw_Xy (k : ℕ) (ks : List Bw2) : WPdT ((⊥ : Bw2) :: ks) (Xy k) :=
  WPdT_twoOf (b := owG (ex2 1 (k + 1)) 1) (ne_bot_of_gt (owG_pos (ex2 1 (k + 1)))) trivial
    (fun q _ => WPdT_nilAll _) (WPdw_twoZy k ks)

theorem GOK_oneXy (k : ℕ) : GOK (Jk1.one Jk1.nil (Xy k)) :=
  (WPdT_bnil (Bud := Bw2) _).mp
    (WPdT_step ([] : List Bw2) (JkT_nil : FrmNT ([] : List Bw2) Jk1.nil)
      ((WPdT_bnil (Bud := Bw2) _).mpr GOK_nil) (WPdw_Xy k []))

theorem jk1_Xy (k l : ℕ) : jk1 l (Xy k)
    = ((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: ((l + 2, 2, 0) : ℕ × ℕ × ℕ)
      :: ((l + 3, 0, 0) : ℕ × ℕ × ℕ) :: ((l + 4, 0, 0) : ℕ × ℕ × ℕ)
      :: List.replicate k ((l + 3, 0, 0) : ℕ × ℕ × ℕ) := by
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 2) (Zy k)))) = _
  rw [jk1_Zy k (l + 2), show l + 2 + 1 = l + 3 from by omega,
    show l + 2 + 2 = l + 4 from by omega]
  simp [jk1]

/-- ★★★★★★★ `R600 (7,0,0)(6,0,0)^k`（どの `k` でも）。 -/
theorem R600_7_600rep_mem (k : ℕ) :
    R600 ++ ((7, 0, 0) : ℕ × ℕ × ℕ) :: List.replicate k ((6, 0, 0) : ℕ × ℕ × ℕ) ∈ W 0 := by
  have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (Xy k)]) := by
    simpa using GOK_oneXy k [] WOk_nil GoodFb_wordJ_nil
  have hh := rowJ_mem_genF Aok_R338 hG
  have e : jk1 2 (Jk1.one Jk1.nil (Xy k))
      = ((3, 1, 0) : ℕ × ℕ × ℕ) :: ((4, 2, 0) : ℕ × ℕ × ℕ) :: ((5, 2, 0) : ℕ × ℕ × ℕ)
        :: ((6, 0, 0) : ℕ × ℕ × ℕ) :: ((7, 0, 0) : ℕ × ℕ × ℕ)
        :: List.replicate k ((6, 0, 0) : ℕ × ℕ × ℕ) := by
    show jk1 2 Jk1.nil ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (2 + 1) (Xy k)) = _
    rw [jk1_Xy k 3]
    simp [jk1]
  rw [wordJ_singleton, colJ, e] at hh
  simpa [R600, R375m, R373, R344, R341, R338, List.append_assoc] using hh

#print axioms R600_7_600rep_mem

/-- ★★★★★★★ `R600 (7,0,0)(6,0,0)(7,0,0)`（`(6,0,0)^k` の極限）。 -/
theorem R600_7_600_700_mem :
    R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((6, 0, 0) : ℕ × ℕ × ℕ),
      ((7, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hne : [((6, 0, 0) : ℕ × ℕ × ℕ)] ≠ [] := by simp
  have hhead : entry [((6, 0, 0) : ℕ × ℕ × ℕ)] 0 0 < 7 := by simp [entry]
  have htail : ∀ r, 1 ≤ r → r < ([((6, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq).length →
      7 ≤ entry [((6, 0, 0) : ℕ × ℕ × ℕ)] 0 r := by
    intro r hr1 hr2
    simp only [List.length_singleton] at hr2
    omega
  have htw : ∀ n : ℕ, (R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ)]) ++ (List.range n).flatMap
      (fun _ => [((6, 0, 0) : ℕ × ℕ × ℕ)]) ∈ W 0 := by
    intro n
    rw [flatMap_singleton_range]
    simpa [List.append_assoc] using R600_7_600rep_mem n
  have hmem := flat_mem'' (Y0 := R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ)])
    (M := [((6, 0, 0) : ℕ × ℕ × ℕ)]) (d := 7) hne hhead htail htw
  simpa [List.append_assoc] using hmem

/-- 新しい台座 `R600 (7,0,0)(6,0,0)(7,0,0)`。 -/
def Z767 : TrioSeq :=
  R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ)]

theorem Z767_eq : Z767 = [((0, 0, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ),
    ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ),
    ((5, 2, 0) : ℕ × ℕ × ℕ),
    ((6, 0, 0) : ℕ × ℕ × ℕ),
    ((7, 0, 0) : ℕ × ℕ × ℕ),
    ((6, 0, 0) : ℕ × ℕ × ℕ),
    ((7, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [Z767, R600, R375m, R373, R344, R341, R338]

theorem Z767_ne : Z767 ≠ [] := by rw [Z767_eq]; simp

theorem Z767_head : entry Z767 0 0 = 0 := by rw [Z767_eq]; simp [entry]

theorem Z767_tail : ∀ r, 1 ≤ r → r < Z767.length → 1 ≤ entry Z767 0 r := by
  intro r hr1 hrl
  rw [Z767_eq] at hrl ⊢
  simp only [List.length_cons, List.length_nil] at hrl
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r <;>
    first
      | omega
      | simp [entry]

theorem Aok_Z767 : Aok Z767 where
  mem := R600_7_600_700_mem
  ne := Z767_ne
  deep := ⟨Z767_head, Z767_tail⟩
  zroot := by
    rw [Z767_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  mono := by
    rw [Z767_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

/-- ★★★★★★★ 新しい台座の上、輪を `n` 周した 4 パラメータの無限族。 -/
theorem LoopIt_Z767_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (j n : ℕ) :
    LoopIt Z767 m ws j n ∈ W 0 := (Aok_LoopIt Aok_Z767 m hw j n).mem

theorem LoopIt_Z767_nil_mem (m p j n : ℕ) :
    LoopIt Z767 m (List.replicate p (AltT 0)) j n ∈ W 0 :=
  LoopIt_Z767_mem m (WJ_rep_AltT 0 p) j n

#print axioms R600_7_600_700_mem
#print axioms LoopIt_Z767_nil_mem

/-! ### ★★★ 底を一般にした入れ子 `ZkO Z n` と、その走りの予算

`Zk n = ZkO nil n`。指数は `ex2 i j`（`i` は底 `Z` の段、`j` は `[(0,0,0)]` の段数）。 -/

def ZkO (Z : Jk1) : ℕ → Jk1
  | 0 => Z
  | (n + 1) => Jk1.pay (ZkO Z n) [((0, 0, 0) : ℕ × ℕ × ℕ)]

theorem JkA_ZkO {Z : Jk1} (hJZ : JkA Z) : ∀ n : ℕ, JkA (ZkO Z n)
  | 0 => hJZ
  | (n + 1) => ⟨JkA_ZkO hJZ n, Bok_zero⟩

theorem jk1_ZkO (Z : Jk1) : ∀ (n l : ℕ),
    jk1 l (ZkO Z n) = jk1 l Z ++ List.replicate n ((l + 1, 0, 0) : ℕ × ℕ × ℕ)
  | 0, l => by simp [ZkO]
  | (n + 1), l => by
      show jk1 l (ZkO Z n) ++ shiftr01 (l + 1) 0 [((0, 0, 0) : ℕ × ℕ × ℕ)] = _
      rw [jk1_ZkO Z n l, List.replicate_succ', List.append_assoc]
      simp [shiftr01]

theorem jk1_payZoper (Z : Jk1) (n l : ℕ) :
    jk1 l (Jk1.pay Z (Y1⟦n⟧)) = jk1 l (ZkO Z n) := by
  show jk1 l Z ++ shiftr01 (l + 1) 0 (Y1⟦n⟧) = _
  rw [oper_Y1 n, flatMap_singleton_range, jk1_ZkO Z n l]
  simp [shiftr01]

/-- 底 `Z` の走りが段 `ex2 i 0` で置けるなら、`ZkO Z n` の走りは段 `ex2 i n` で置ける。 -/
theorem WPdw_runO {Z : Jk1} (hJZ : JkA Z) (i : ℕ)
    (hZ : ∀ (A : Jk1), JkA A → ∀ (β : Bw2),
      (∀ c : Bw2, β < c → ∀ ks : List Bw2, WPdT (c :: ks) A) →
      ∀ (m : ℕ) (c : Bw2), β + owG (ex2 i 0) m < c → ∀ ks : List Bw2,
        WPdT (c :: ks) (twoIt A Z m)) :
    ∀ (n : ℕ) (β : Bw2) (A : Jk1), JkA A →
      (∀ c : Bw2, β < c → ∀ ks : List Bw2, WPdT (c :: ks) A) →
      ∀ (m : ℕ) (c : Bw2), β + owG (ex2 i n) m < c → ∀ ks : List Bw2,
        WPdT (c :: ks) (twoIt A (ZkO Z n) m)
  | 0, β, A, hJA, hA, m, c, hc, ks => hZ A hJA β hA m c hc ks
  | (n + 1), β, A, _, hA, 0, c, hc, ks =>
      hA c (by rwa [owG_zero, bot_BwG, add_zero] at hc) ks
  | (n + 1), β, A, hJA, hA, (m + 1), c, hc, ks => by
      have hJA' : JkA (twoIt A (ZkO Z (n + 1)) m) :=
        JkA_twoItP hJA (JkA_ZkO hJZ (n + 1)) m
      have hA' : ∀ c' : Bw2, β + owG (ex2 i (n + 1)) m < c' → ∀ ks' : List Bw2,
          WPdT (c' :: ks') (twoIt A (ZkO Z (n + 1)) m) :=
        fun c' hc' ks' => WPdw_runO hJZ i hZ (n + 1) β A hJA hA m c' hc' ks'
      refine WPdT_twoAZ_top
        (S := ⟨fun j => (β + owG (ex2 i (n + 1)) m) + owG (ex2 i n) j,
          fun _ _ hij => BwG_add_lt_left _ (owG_ltR (ex2 i n) hij)⟩)
        (t := c) ?_ hJA' (JkA_ZkO hJZ n) ?_ ks
      · intro j
        show (β + owG (ex2 i (n + 1)) m) + owG (ex2 i n) j < c
        rw [add_assoc]
        exact lt_trans (BwG_add_lt_left β
          (owG_add_lt (ex2_lt_r i (by omega : n < n + 1)) m j)) hc
      · intro m' c' hc' ks'
        exact WPdw_runO hJZ i hZ n (β + owG (ex2 i (n + 1)) m)
          (twoIt A (ZkO Z (n + 1)) m) hJA' hA' m' c' hc' ks'
termination_by n _ _ _ _ m _ _ _ => (n, m)

#print axioms WPdw_runO

theorem WPdT_twoAY1Z_at {A Z : Jk1} (hJA : JkA A) (hJZ : JkA Z) (i : ℕ) (β : Bw2)
    (hchain : ∀ (n m : ℕ) (c : Bw2), β + owG (ex2 i n) m < c → ∀ ks : List Bw2,
      WPdT (c :: ks) (twoIt A (ZkO Z n) m))
    {t : Bw2} (ht : β + owG (ex2 (i + 1) 0) 1 ≤ t)
    {B : List Bw2} {N : Jk1} (hJN : JkA N)
    (hNt : ∀ q : List Bw2, (∀ x ∈ q, x < t) → WPdT ((⊥ : Bw2) :: q ++ B) N) :
    WPdT ((⊥ : Bw2) :: B) (Jk1.two N (Jk1.two A (Jk1.pay Z Y1))) := by
  rw [WPdT_iff]
  intro ctx hc
  have hJT : JkT (plug (ctx ++ [Frm.ftwo N]) (Jk1.two A (Jk1.pay Z Y1))) := by
    rw [plug_snoc2]
    exact WCtxU_JkT ((⊥ : Bw2) :: B) ctx hc
      (Jk1.two N (Jk1.two A (Jk1.pay Z Y1)))
      (⟨hJN, hJA, hJZ, Bok_Y1⟩ : FrmNT ((⊥ : Bw2) :: B)
        (Jk1.two N (Jk1.two A (Jk1.pay Z Y1))))
  intro ws hw hG
  rw [← plug_snoc2]
  have hlen2 : 2 ≤ Y1.length := by rw [Y1_len]
  have hp : hasParent Y1 (srow Y1 (Y1.length - 1)) (Y1.length - 1) := by
    rw [Y1_len]
    simpa [Y1_srow] using Y1_hasParent
  refine GoodFb_snoc_innerJt0 hw hJT hlen2 hp ?_
  intro n hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hstep : ∀ m : ℕ, β + owG (ex2 i n') m < β + owG (ex2 i (n' + 1)) 1 :=
    fun m => BwG_add_lt_left β (owG_ltL (ex2_lt_r i (by omega)) m (by omega))
  have hle : β + owG (ex2 i (n' + 1)) 1 ≤ t :=
    le_of_lt (lt_of_lt_of_le
      (BwG_add_lt_left β (owG_ltL (ex2_lt_l (by omega : i < i + 1) (n' + 1) 0) 1 (by omega))) ht)
  have hw2 : WPdT ((⊥ : Bw2) :: B) (Jk1.two N (Jk1.two A (ZkO Z (n' + 1)))) :=
    WPdT_twoAZ_at (S := ⟨fun j => β + owG (ex2 i n') j,
        fun _ _ hij => BwG_add_lt_left β (owG_ltR (ex2 i n') hij)⟩)
      (t := β + owG (ex2 i (n' + 1)) 1) hstep hJA (JkA_ZkO hJZ n')
      (fun m c hc' ks' => hchain n' m c hc' ks') hJN
      (fun q hq => hNt q (fun x hx => lt_of_lt_of_le (hq x hx) hle))
  have hw3 : WPdT ((⊥ : Bw2) :: B)
      (Jk1.two N (Jk1.two A (Jk1.pay Z (Y1⟦n' + 1⟧)))) := by
    refine WPdT_congr ((⊥ : Bw2) :: B) (fun l => ?_) hw2
    show jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
        (jk1 (l + 1) A ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 2) (ZkO Z (n' + 1)))))
      = jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
        (jk1 (l + 1) A ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) ::
          jk1 (l + 2) (Jk1.pay Z (Y1⟦n' + 1⟧)))))
    rw [jk1_payZoper Z]
  have hh := (WPdT_iff ((⊥ : Bw2) :: B) _).mp hw3 ctx hc ws hw hG
  rw [← plug_snoc2] at hh
  exact hh


/-- ★★★ 底が一般の `two A (pay Z Y1)`。段 `ex2 (i+1) 0` を超える予算に置ける。 -/
theorem WPdT_twoAY1Z_top {A Z : Jk1} (hJA : JkA A) (hJZ : JkA Z) (i : ℕ) (β : Bw2)
    (hchain : ∀ (n m : ℕ) (c : Bw2), β + owG (ex2 i n) m < c → ∀ ks : List Bw2,
      WPdT (c :: ks) (twoIt A (ZkO Z n) m))
    {t : Bw2} (ht : β + owG (ex2 (i + 1) 0) 1 < t) (ks : List Bw2) :
    WPdT (t :: ks) (Jk1.two A (Jk1.pay Z Y1)) :=
  have htb : t ≠ ⊥ := ne_bot_of_gt (lt_of_le_of_lt bot_le ht)
  (WPdT_cb htb ks _).mpr (fun r hr U N hU hUk hJN hNt =>
    WPdT_two_of_ctx hU hUk
      (fun ctx hc => (WPdT_iff ((⊥ : Bw2) :: (r ++ ks)) _).mp
        (WPdT_twoAY1Z_at hJA hJZ i β hchain (le_of_lt ht) hJN hNt) ctx hc))

#print axioms WPdT_twoAY1Z_at
#print axioms WPdT_twoAY1Z_top

/-! ### ★★★★ 荷 `Y1` を `n` 段入れ子にした `Zq n` と `R600 (7,0,0)(7,0,0)` -/

def Zq : ℕ → Jk1
  | 0 => Jk1.nil
  | (n + 1) => Jk1.pay (Zq n) Y1

theorem JkA_Zn : ∀ n : ℕ, JkA (Zq n)
  | 0 => trivial
  | (n + 1) => ⟨JkA_Zn n, Bok_Y1⟩

theorem jk1_Zn : ∀ (n l : ℕ), jk1 l (Zq n)
    = (List.range n).flatMap
        (fun _ => [((l + 1, 0, 0) : ℕ × ℕ × ℕ), ((l + 2, 0, 0) : ℕ × ℕ × ℕ)])
  | 0, l => by simp [Zq, jk1]
  | (n + 1), l => by
      show jk1 l (Zq n) ++ shiftr01 (l + 1) 0 Y1 = _
      rw [jk1_Zn n l, List.range_succ, List.flatMap_append]
      simp [Y1, shiftr01]
      omega

theorem WPdw_chainZn : ∀ (n : ℕ) (A : Jk1), JkA A → ∀ (β : Bw2),
    (∀ c : Bw2, β < c → ∀ ks : List Bw2, WPdT (c :: ks) A) →
    ∀ (m : ℕ) (c : Bw2), β + owG (ex2 n 0) m < c → ∀ ks : List Bw2,
      WPdT (c :: ks) (twoIt A (Zq n) m)
  | 0, A, hJA, β, hA, m, c, hc, ks => WPdw_run2 0 β A hJA hA m c hc ks
  | (n + 1), A, _, β, hA, 0, c, hc, ks =>
      hA c (by rwa [owG_zero, bot_BwG, add_zero] at hc) ks
  | (n + 1), A, hJA, β, hA, (m + 1), c, hc, ks => by
      have hJA' : JkA (twoIt A (Zq (n + 1)) m) := JkA_twoItP hJA (JkA_Zn (n + 1)) m
      have hA' : ∀ c' : Bw2, β + owG (ex2 (n + 1) 0) m < c' → ∀ ks' : List Bw2,
          WPdT (c' :: ks') (twoIt A (Zq (n + 1)) m) :=
        fun c' hc' ks' => WPdw_chainZn (n + 1) A hJA β hA m c' hc' ks'
      have hlt : (β + owG (ex2 (n + 1) 0) m) + owG (ex2 (n + 1) 0) 1 < c := by
        rw [add_assoc, owG_add_same]
        exact hc
      exact WPdT_twoAY1Z_top hJA' (JkA_Zn n) n (β + owG (ex2 (n + 1) 0) m)
        (fun j m' c' hc' ks' => WPdw_runO (JkA_Zn n) n
          (fun A2 hJA2 β2 hA2 m2 c2 hc2 ks2 => WPdw_chainZn n A2 hJA2 β2 hA2 m2 c2 hc2 ks2)
          j (β + owG (ex2 (n + 1) 0) m) _ hJA' hA' m' c' hc' ks')
        hlt ks
termination_by n _ _ _ _ m _ _ _ => (n, m)

theorem WPdw_twoZn : ∀ (n : ℕ) (ks : List Bw2),
    WPdT (owG (ex2 (n + 1) 0) 1 :: ks) (Jk1.two Jk1.nil (Zq n))
  | 0, ks =>
      WPdT_twoA_runB (a := owG (ex2 0 0) 1) (A := Jk1.nil)
        (ne_bot_of_gt (owG_pos (ex2 0 0)))
        (owG_ltL (ex2_lt_l (by omega : 0 < 1) 0 0) 1 (by omega))
        trivial (fun ks' => WPdT_nilAll _) ks
  | (n + 1), ks => by
      refine WPdT_twoAY1Z_top (A := Jk1.nil) trivial (JkA_Zn n) n ⊥ ?_ ?_ ks
      · intro j m c hc ks'
        exact WPdw_runO (JkA_Zn n) n
          (fun A2 hJA2 β2 hA2 m2 c2 hc2 ks2 => WPdw_chainZn n A2 hJA2 β2 hA2 m2 c2 hc2 ks2)
          j ⊥ Jk1.nil trivial (fun c' _ ks'' => WPdT_nilAll _) m c hc ks'
      · rw [bot_BwG, zero_add]
        exact owG_ltL (ex2_lt_l (by omega) 0 0) 1 (by omega)

def Xq (n : ℕ) : Jk1 := Jk1.two Jk1.nil (Jk1.two Jk1.nil (Zq n))

theorem WPdw_Xn (n : ℕ) (ks : List Bw2) : WPdT ((⊥ : Bw2) :: ks) (Xq n) :=
  WPdT_twoOf (b := owG (ex2 (n + 1) 0) 1) (ne_bot_of_gt (owG_pos (ex2 (n + 1) 0))) trivial
    (fun q _ => WPdT_nilAll _) (WPdw_twoZn n ks)

theorem GOK_oneXn (n : ℕ) : GOK (Jk1.one Jk1.nil (Xq n)) :=
  (WPdT_bnil (Bud := Bw2) _).mp
    (WPdT_step ([] : List Bw2) (JkT_nil : FrmNT ([] : List Bw2) Jk1.nil)
      ((WPdT_bnil (Bud := Bw2) _).mpr GOK_nil) (WPdw_Xn n []))

theorem jk1_Xn (n l : ℕ) : jk1 l (Xq n)
    = ((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: ((l + 2, 2, 0) : ℕ × ℕ × ℕ)
      :: (List.range n).flatMap
        (fun _ => [((l + 3, 0, 0) : ℕ × ℕ × ℕ), ((l + 4, 0, 0) : ℕ × ℕ × ℕ)]) := by
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 2) (Zq n)))) = _
  rw [jk1_Zn n (l + 2), show l + 2 + 1 = l + 3 from by omega,
    show l + 2 + 2 = l + 4 from by omega]
  simp [jk1]

/-- ★★★★★★★ `R375m ++ ((6,0,0)(7,0,0))^n`（どの `n` でも）。 -/
theorem R375m_pair_rep_mem (n : ℕ) :
    R375m ++ (List.range n).flatMap
      (fun _ => [((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ)]) ∈ W 0 := by
  have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (Xq n)]) := by
    simpa using GOK_oneXn n [] WOk_nil GoodFb_wordJ_nil
  have hh := rowJ_mem_genF Aok_R338 hG
  have e : jk1 2 (Jk1.one Jk1.nil (Xq n))
      = ((3, 1, 0) : ℕ × ℕ × ℕ) :: ((4, 2, 0) : ℕ × ℕ × ℕ) :: ((5, 2, 0) : ℕ × ℕ × ℕ)
        :: (List.range n).flatMap
            (fun _ => [((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ)]) := by
    show jk1 2 Jk1.nil ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (2 + 1) (Xq n)) = _
    rw [jk1_Xn n 3]
    simp [jk1]
  rw [wordJ_singleton, colJ, e] at hh
  simpa [R375m, R373, R344, R341, R338, List.append_assoc] using hh

/-- ★★★★★★★★ 証明中の行 `R600 (7,0,0)(7,0,0)`。 -/
theorem R600_77_mem :
    R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hne : [((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ)] ≠ [] := by simp
  have hhead : entry [((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ)] 0 0 < 7 := by
    simp [entry]
  have htail : ∀ r, 1 ≤ r →
      r < ([((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq).length →
      7 ≤ entry [((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ)] 0 r := by
    intro r hr1 hr2
    simp only [List.length_cons, List.length_nil] at hr2
    have : r = 1 := by omega
    subst this
    simp [entry]
  have hmem := flat_mem'' (Y0 := R375m)
    (M := [((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ)]) (d := 7)
    hne hhead htail R375m_pair_rep_mem
  simpa [R600, List.append_assoc] using hmem

#print axioms R375m_pair_rep_mem
#print axioms R600_77_mem

/-- 新しい台座 `R600 (7,0,0)(7,0,0)`。 -/
def Z77 : TrioSeq :=
  R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ)]

theorem Z77_eq : Z77 = [((0, 0, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ),
    ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ),
    ((5, 2, 0) : ℕ × ℕ × ℕ),
    ((6, 0, 0) : ℕ × ℕ × ℕ),
    ((7, 0, 0) : ℕ × ℕ × ℕ),
    ((7, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [Z77, R600, R375m, R373, R344, R341, R338]

theorem Z77_ne : Z77 ≠ [] := by rw [Z77_eq]; simp

theorem Z77_head : entry Z77 0 0 = 0 := by rw [Z77_eq]; simp [entry]

theorem Z77_tail : ∀ r, 1 ≤ r → r < Z77.length → 1 ≤ entry Z77 0 r := by
  intro r hr1 hrl
  rw [Z77_eq] at hrl ⊢
  simp only [List.length_cons, List.length_nil] at hrl
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r <;>
    first
      | omega
      | simp [entry]

theorem Aok_Z77 : Aok Z77 where
  mem := R600_77_mem
  ne := Z77_ne
  deep := ⟨Z77_head, Z77_tail⟩
  zroot := by
    rw [Z77_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  mono := by
    rw [Z77_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

/-- ★★★★★★★★ 新しい台座の上、輪を `n` 周した 4 パラメータの無限族。 -/
theorem LoopIt_Z77_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (j n : ℕ) :
    LoopIt Z77 m ws j n ∈ W 0 := (Aok_LoopIt Aok_Z77 m hw j n).mem

theorem LoopIt_Z77_nil_mem (m p j n : ℕ) :
    LoopIt Z77 m (List.replicate p (AltT 0)) j n ∈ W 0 :=
  LoopIt_Z77_mem m (WJ_rep_AltT 0 p) j n

#print axioms Aok_Z77
#print axioms LoopIt_Z77_nil_mem


/-! ### ★★★★ 荷の階 `Yv j = (0,0,0)(1,0,0)^j`

`Yv 0 = [(0,0,0)]`、`Yv 1 = Y1`。`(Yv (j+1))⟦n⟧ = (Yv j)^n` なので、
階 `j` の荷は予算の指数 `ω^j` を要求する。 -/

def Yv (j : ℕ) : TrioSeq :=
  ((0, 0, 0) : ℕ × ℕ × ℕ) :: List.replicate j ((1, 0, 0) : ℕ × ℕ × ℕ)

theorem Yv_zero : Yv 0 = [((0, 0, 0) : ℕ × ℕ × ℕ)] := rfl

theorem Yv_one : Yv 1 = Y1 := rfl

theorem Yv_len (j : ℕ) : (Yv j).length = j + 1 := by simp [Yv]

theorem Flat_Yv (j : ℕ) : Flat (Yv j) := by
  intro c hc
  simp only [Yv, List.mem_cons, List.mem_replicate] at hc
  rcases hc with rfl | ⟨-, rfl⟩ <;> exact ⟨rfl, rfl⟩

theorem Bok_Yv (j : ℕ) : Bok (Yv j) := Bok_flat (Flat_Yv j) (by simp [Yv, entry])

theorem getD_rep (a d : ℕ × ℕ × ℕ) : ∀ (j i : ℕ),
    (List.replicate j a).getD i d = if i < j then a else d
  | 0, i => by simp
  | (j + 1), 0 => by simp [List.replicate_succ]
  | (j + 1), (i + 1) => by
      rw [List.replicate_succ, List.getD_cons_succ, getD_rep a d j i]
      by_cases h : i < j
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

theorem entry_Yv0 (j i : ℕ) :
    entry (Yv j) 0 i = if 1 ≤ i ∧ i ≤ j then 1 else 0 := by
  rcases i with _ | i
  · simp [entry, Yv]
  · show (((Yv j).getD (i + 1) ((0, 0, 0) : ℕ × ℕ × ℕ)).1) = _
    rw [show Yv j = ((0, 0, 0) : ℕ × ℕ × ℕ) :: List.replicate j ((1, 0, 0) : ℕ × ℕ × ℕ)
        from rfl, List.getD_cons_succ, getD_rep]
    by_cases h : i < j
    · rw [if_pos h, if_pos ⟨by omega, by omega⟩]
    · rw [if_neg h, if_neg (by omega)]

theorem entry_Yv12 (j i : ℕ) : entry (Yv j) 1 i = 0 ∧ entry (Yv j) 2 i = 0 :=
  Flat_entry (Flat_Yv j) i

theorem Yv_srow (j i : ℕ) : srow (Yv j) i = 0 := by
  simp [srow, (entry_Yv12 j i).1, (entry_Yv12 j i).2]

theorem Yv_hasParent (j : ℕ) : hasParent (Yv (j + 1)) 0 (j + 1) := by
  rw [hasParent_zero_iff (by rw [Yv_len]; omega)]
  refine ⟨0, by omega, ?_⟩
  rw [entry_Yv0, entry_Yv0, if_neg (by omega), if_pos ⟨by omega, by omega⟩]
  omega

theorem Yv_parent (j : ℕ) : parent (Yv (j + 1)) 0 (j + 1) = 0 := by
  have h := parent_nextR (Yv_hasParent j)
  rw [nextR, if_pos rfl] at h
  obtain ⟨-, -, hlt, hval, -⟩ := h
  by_contra hne
  rw [entry_Yv0, entry_Yv0, if_pos ⟨by omega, by omega⟩,
    if_pos ⟨by omega, by omega⟩] at hval
  omega

theorem Yv_take (j : ℕ) : (Yv (j + 1)).take (j + 1) = Yv j := by
  show (((0, 0, 0) : ℕ × ℕ × ℕ) ::
    List.replicate (j + 1) ((1, 0, 0) : ℕ × ℕ × ℕ)).take (j + 1) = _
  rw [List.take_succ_cons, List.take_replicate]
  simp [Yv]

theorem oper_Yv (j n : ℕ) :
    (Yv (j + 1))⟦n⟧ = (List.range n).flatMap (fun _ => Yv j) := by
  have h1 : (Yv (j + 1)).length - 1 = j + 1 := by rw [Yv_len]; omega
  simp only [oper, h1, Yv_srow, Yv_parent]
  rw [if_neg (by omega),
    if_neg (by rw [entry_Yv0, if_pos ⟨by omega, by omega⟩]; simp),
    if_neg (by rw [h1, Yv_srow]; exact not_not_intro (Yv_hasParent j))]
  simp only [Nat.lt_irrefl, show ¬ ((1 : ℕ) < 0) from by omega, if_false,
    Nat.sub_zero, Nat.mul_zero, Nat.add_zero, ite_self, List.take_zero,
    List.nil_append,
    map_range'_entry (M := Yv (j + 1)) (k := j + 1) (by rw [Yv_len]; omega),
    Yv_take]

#print axioms oper_Yv

/-- 予算型 `Bwx = BwG Bw`（順序型 `ω^(ω^ω)`）。指数が `Bw`（順序型 `ω^ω`）なので
階 `j` の荷が要求する指数 `ω^j·n = ow j n` が全部入る。 -/
abbrev Bwx : Type := BwG Bw

example : WellFoundedLT Bwx := inferInstance
example : OrderBot Bwx := inferInstance
example : LinearOrder Bwx := inferInstance

/-- 荷 `Y` を `n` 段 pay した木。`ZkO Z n = PayIt Z [(0,0,0)] n`。 -/
def PayIt (Z : Jk1) (Y : TrioSeq) : ℕ → Jk1
  | 0 => Z
  | (n + 1) => Jk1.pay (PayIt Z Y n) Y

theorem JkA_PayIt {Z : Jk1} {Y : TrioSeq} (hJZ : JkA Z) (hBY : Bok Y) :
    ∀ n : ℕ, JkA (PayIt Z Y n)
  | 0 => hJZ
  | (n + 1) => ⟨JkA_PayIt hJZ hBY n, hBY⟩

theorem jk1_PayIt (Z : Jk1) (Y : TrioSeq) : ∀ (n l : ℕ),
    jk1 l (PayIt Z Y n)
      = jk1 l Z ++ (List.range n).flatMap (fun _ => shiftr01 (l + 1) 0 Y)
  | 0, l => by simp [PayIt]
  | (n + 1), l => by
      show jk1 l (PayIt Z Y n) ++ shiftr01 (l + 1) 0 Y = _
      rw [jk1_PayIt Z Y n l, List.range_succ, List.flatMap_append,
        List.append_assoc]
      simp

theorem shiftr01_flatMap (k n : ℕ) (Y : TrioSeq) :
    shiftr01 k 0 ((List.range n).flatMap (fun _ => Y))
      = (List.range n).flatMap (fun _ => shiftr01 k 0 Y) := by
  show List.map _ (List.flatMap _ _) = _
  rw [List.map_flatMap]
  rfl

/-- 荷 `Yv (j+1)` の展開は `Yv j` を `n` 段 pay したのと同じ列を作る。 -/
theorem jk1_payYvOper (Z : Jk1) (j n l : ℕ) :
    jk1 l (Jk1.pay Z ((Yv (j + 1))⟦n⟧)) = jk1 l (PayIt Z (Yv j) n) := by
  show jk1 l Z ++ shiftr01 (l + 1) 0 ((Yv (j + 1))⟦n⟧) = _
  rw [oper_Yv j n, shiftr01_flatMap, jk1_PayIt Z (Yv j) n l]

/-- ★★★ 荷に依存しない「_at」。`Y⟦n+1⟧` の段が全部置けるなら `pay Z Y` も置ける。 -/
theorem WPdT_twoAY_at {Bud : Type} [LinearOrder Bud] [OrderBot Bud] [WellFoundedLT Bud]
    {A Z : Jk1} {Y : TrioSeq} (hJA : JkA A) (hJZ : JkA Z) (hBY : Bok Y)
    (hlen : 2 ≤ Y.length)
    (hp : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1))
    {B : List Bud} {N : Jk1} (hJN : JkA N)
    (hstep : ∀ n : ℕ,
      WPdT ((⊥ : Bud) :: B) (Jk1.two N (Jk1.two A (Jk1.pay Z (Y⟦n + 1⟧))))) :
    WPdT ((⊥ : Bud) :: B) (Jk1.two N (Jk1.two A (Jk1.pay Z Y))) := by
  rw [WPdT_iff]
  intro ctx hc
  have hJT : JkT (plug (ctx ++ [Frm.ftwo N]) (Jk1.two A (Jk1.pay Z Y))) := by
    rw [plug_snoc2]
    exact WCtxU_JkT ((⊥ : Bud) :: B) ctx hc (Jk1.two N (Jk1.two A (Jk1.pay Z Y)))
      (⟨hJN, hJA, hJZ, hBY⟩ : FrmNT ((⊥ : Bud) :: B)
        (Jk1.two N (Jk1.two A (Jk1.pay Z Y))))
  intro ws hw hG
  rw [← plug_snoc2]
  refine GoodFb_snoc_innerJt0 hw hJT hlen hp ?_
  intro n hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hh := (WPdT_iff ((⊥ : Bud) :: B) _).mp (hstep n') ctx hc ws hw hG
  rw [← plug_snoc2] at hh
  exact hh

#print axioms WPdT_twoAY_at
#print axioms jk1_payYvOper

/-! ### ★★★★★ 階の梯子

`RunJ Z e`: 底 `Z` の走り `twoIt A Z m` が `A` の閾値 `β` の上 `β + ω^e·m` を
超える予算に置ける。指数 `e : Bw`（順序型 ω^ω）なので階 `j` の `ω^j` が全部入る。

- `AStat j`: `RunJ Z e → RunJ (PayIt Z (Yv j) n) (e + ω^j·n)`（鎖）
- `BStat j`: `pay Z (Yv (j+1))` を `2` の記録の中に置ける（_at）
- `CStat j`: 同じものを予算 `t` の上に置ける（_top）

依存は `A(0) → B(0) → A(1) → B(1) → …` の一本道。 -/

theorem ow_add_same (k m : ℕ) : ow k m + ow k 1 = ow k (m + 1) := owG_add_same k m

def RunJ (Z : Jk1) (e : Bw) : Prop := ∀ (m : ℕ) (A : Jk1), JkA A → ∀ β : Bwx,
  (∀ c : Bwx, β < c → ∀ ks : List Bwx, WPdT (c :: ks) A) →
  ∀ c : Bwx, β + owG e m < c → ∀ ks : List Bwx,
    WPdT (c :: ks) (twoIt A Z m)

def AStat (j : ℕ) : Prop := ∀ (n : ℕ) (Z : Jk1), JkA Z → ∀ e : Bw, RunJ Z e →
  RunJ (PayIt Z (Yv j) n) (e + ow j n)

def BStat (j : ℕ) : Prop := ∀ Z : Jk1, JkA Z → ∀ e : Bw, RunJ Z e →
  ∀ A : Jk1, JkA A → ∀ β : Bwx,
    (∀ c : Bwx, β < c → ∀ ks : List Bwx, WPdT (c :: ks) A) →
    ∀ t : Bwx, β + owG (e + ow (j + 1) 1) 1 ≤ t →
    ∀ (B : List Bwx) (N : Jk1), JkA N →
      (∀ q : List Bwx, (∀ x ∈ q, x < t) → WPdT ((⊥ : Bwx) :: q ++ B) N) →
      WPdT ((⊥ : Bwx) :: B) (Jk1.two N (Jk1.two A (Jk1.pay Z (Yv (j + 1)))))

def CStat (j : ℕ) : Prop := ∀ Z : Jk1, JkA Z → ∀ e : Bw, RunJ Z e →
  ∀ A : Jk1, JkA A → ∀ β : Bwx,
    (∀ c : Bwx, β < c → ∀ ks : List Bwx, WPdT (c :: ks) A) →
    ∀ t : Bwx, β + owG (e + ow (j + 1) 1) 1 < t →
    ∀ ks : List Bwx, WPdT (t :: ks) (Jk1.two A (Jk1.pay Z (Yv (j + 1))))

theorem jk1_twotwo_congr {N A P1 P2 : Jk1} (h : ∀ l, jk1 l P1 = jk1 l P2) (l : ℕ) :
    jk1 l (Jk1.two N (Jk1.two A P1)) = jk1 l (Jk1.two N (Jk1.two A P2)) := by
  show jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1) A ++ (((l + 1 + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1 + 1) P1)))
    = jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1) A ++ (((l + 1 + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1 + 1) P2)))
  rw [h]

theorem hasParent_Yv_last (j : ℕ) :
    hasParent (Yv (j + 1)) (srow (Yv (j + 1)) ((Yv (j + 1)).length - 1))
      ((Yv (j + 1)).length - 1) := by
  rw [Yv_len, Yv_srow, show j + 1 + 1 - 1 = j + 1 from by omega]
  exact Yv_hasParent j

theorem AStat_zero : AStat 0 := by
  intro n
  induction n with
  | zero =>
      intro Z hJZ e hR m A hJA β hβ c hc ks
      exact hR m A hJA β hβ c (by rwa [ow_zero, bot_Bw, add_zero] at hc) ks
  | succ n ih =>
      intro Z hJZ e hR m
      induction m with
      | zero =>
          intro A hJA β hβ c hc ks
          exact hβ c (by rwa [owG_zero, bot_BwG, add_zero] at hc) ks
      | succ m ihm =>
          intro A hJA β hβ c hc ks
          have hJW : JkA (PayIt Z (Yv 0) (n + 1)) := JkA_PayIt hJZ (Bok_Yv 0) (n + 1)
          have hJA' : JkA (twoIt A (PayIt Z (Yv 0) (n + 1)) m) := JkA_twoItP hJA hJW m
          have hA' : ∀ c' : Bwx, β + owG (e + ow 0 (n + 1)) m < c' → ∀ ks' : List Bwx,
              WPdT (c' :: ks') (twoIt A (PayIt Z (Yv 0) (n + 1)) m) :=
            fun c' hc' ks' => ihm A hJA β hβ c' hc' ks'
          show WPdT (c :: ks) (Jk1.two (twoIt A (PayIt Z (Yv 0) (n + 1)) m)
            (Jk1.pay (PayIt Z (Yv 0) n) (Yv 0)))
          refine WPdT_twoAZ_top
            (S := ⟨fun i => (β + owG (e + ow 0 (n + 1)) m) + owG (e + ow 0 n) i,
              fun _ _ hij => BwG_add_lt_left _ (owG_ltR (e + ow 0 n) hij)⟩)
            (t := c) ?_ hJA' (JkA_PayIt hJZ (Bok_Yv 0) n) ?_ ks
          · intro i
            show (β + owG (e + ow 0 (n + 1)) m) + owG (e + ow 0 n) i < c
            rw [add_assoc]
            exact lt_trans (BwG_add_lt_left β
              (owG_add_lt (Bw_add_lt_left e (ow_ltR 0 (by omega : n < n + 1))) m i)) hc
          · intro m' c' hc' ks'
            exact ih Z hJZ e hR m' _ hJA' (β + owG (e + ow 0 (n + 1)) m) hA' c' hc' ks'

theorem CStat_of_BStat {j : ℕ} (hB : BStat j) : CStat j := by
  intro Z hJZ e hR A hJA β hβ t ht ks
  have htb : t ≠ ⊥ := ne_bot_of_gt (lt_of_le_of_lt bot_le ht)
  refine (WPdT_cb htb ks _).mpr (fun r hr U N hU hUk hJN hNt => ?_)
  refine WPdT_two_of_ctx hU hUk (fun ctx hc => ?_)
  exact (WPdT_iff ((⊥ : Bwx) :: (r ++ ks)) _).mp
    (hB Z hJZ e hR A hJA β hβ t (le_of_lt ht) (r ++ ks) N hJN hNt) ctx hc

theorem AStat_succ {j : ℕ} (hC : CStat j) : AStat (j + 1) := by
  intro n
  induction n with
  | zero =>
      intro Z hJZ e hR m A hJA β hβ c hc ks
      exact hR m A hJA β hβ c (by rwa [ow_zero, bot_Bw, add_zero] at hc) ks
  | succ n ih =>
      intro Z hJZ e hR m
      induction m with
      | zero =>
          intro A hJA β hβ c hc ks
          exact hβ c (by rwa [owG_zero, bot_BwG, add_zero] at hc) ks
      | succ m ihm =>
          intro A hJA β hβ c hc ks
          have hJW : JkA (PayIt Z (Yv (j + 1)) (n + 1)) :=
            JkA_PayIt hJZ (Bok_Yv (j + 1)) (n + 1)
          have hJA' : JkA (twoIt A (PayIt Z (Yv (j + 1)) (n + 1)) m) :=
            JkA_twoItP hJA hJW m
          have hA' : ∀ c' : Bwx, β + owG (e + ow (j + 1) (n + 1)) m < c' →
              ∀ ks' : List Bwx,
              WPdT (c' :: ks') (twoIt A (PayIt Z (Yv (j + 1)) (n + 1)) m) :=
            fun c' hc' ks' => ihm A hJA β hβ c' hc' ks'
          show WPdT (c :: ks) (Jk1.two (twoIt A (PayIt Z (Yv (j + 1)) (n + 1)) m)
            (Jk1.pay (PayIt Z (Yv (j + 1)) n) (Yv (j + 1))))
          refine hC (PayIt Z (Yv (j + 1)) n) (JkA_PayIt hJZ (Bok_Yv (j + 1)) n)
            (e + ow (j + 1) n) (ih Z hJZ e hR) _ hJA'
            (β + owG (e + ow (j + 1) (n + 1)) m) hA' c ?_ ks
          have he : (e + ow (j + 1) n) + ow (j + 1) 1 = e + ow (j + 1) (n + 1) := by
            rw [add_assoc, ow_add_same]
          rw [he, add_assoc, owG_add_same]
          exact hc

theorem BStat_zero (hA : AStat 0) : BStat 0 := by
  intro Z hJZ e hR A hJA β hβ t ht B N hJN hNt
  refine WPdT_twoAY_at hJA hJZ (Bok_Yv 1) (by rw [Yv_len]) (hasParent_Yv_last 0) hJN ?_
  intro n'
  refine WPdT_congr ((⊥ : Bwx) :: B)
    (fun l => jk1_twotwo_congr (fun l' => (jk1_payYvOper Z 0 (n' + 1) l').symm) l) ?_
  refine WPdT_twoAZ_at
    (S := ⟨fun i => β + owG (e + ow 0 n') i,
      fun _ _ hij => BwG_add_lt_left β (owG_ltR (e + ow 0 n') hij)⟩)
    (t := t) ?_ hJA (JkA_PayIt hJZ (Bok_Yv 0) n') ?_ hJN hNt
  · intro i
    show β + owG (e + ow 0 n') i < t
    refine lt_of_lt_of_le (BwG_add_lt_left β (owG_ltL ?_ i (by omega))) ht
    exact Bw_add_lt_left e (ow_ltL (by omega : 0 < 1) n' (by omega))
  · intro m' c' hc' ks'
    exact hA n' Z hJZ e hR m' A hJA β hβ c' hc' ks'

theorem BStat_succ {j : ℕ} (hA : AStat (j + 1)) (hB : BStat j) : BStat (j + 1) := by
  intro Z hJZ e hR A hJA β hβ t ht B N hJN hNt
  refine WPdT_twoAY_at hJA hJZ (Bok_Yv (j + 2)) (by rw [Yv_len]; omega)
    (hasParent_Yv_last (j + 1)) hJN ?_
  intro n'
  refine WPdT_congr ((⊥ : Bwx) :: B)
    (fun l => jk1_twotwo_congr (fun l' => (jk1_payYvOper Z (j + 1) (n' + 1) l').symm) l) ?_
  refine hB (PayIt Z (Yv (j + 1)) n') (JkA_PayIt hJZ (Bok_Yv (j + 1)) n')
    (e + ow (j + 1) n') (hA n' Z hJZ e hR) A hJA β hβ t ?_ B N hJN hNt
  have he : (e + ow (j + 1) n') + ow (j + 1) 1 = e + ow (j + 1) (n' + 1) := by
    rw [add_assoc, ow_add_same]
  rw [he]
  refine le_of_lt (lt_of_lt_of_le (BwG_add_lt_left β (owG_ltL ?_ 1 (by omega))) ht)
  exact Bw_add_lt_left e (ow_ltL (by omega : j + 1 < j + 1 + 1) (n' + 1) (by omega))

theorem BStat_all : ∀ j : ℕ, BStat j
  | 0 => BStat_zero AStat_zero
  | (j + 1) => BStat_succ (AStat_succ (CStat_of_BStat (BStat_all j))) (BStat_all j)

theorem AStat_all : ∀ j : ℕ, AStat j
  | 0 => AStat_zero
  | (j + 1) => AStat_succ (CStat_of_BStat (BStat_all j))

#print axioms AStat_all
#print axioms BStat_all

/-! ### ★★★★★★★★ 梯子の収穫: `R600 (7,0,0)^k`（どの `k` でも） -/

theorem RunJ_nil : RunJ Jk1.nil (⊥ : Bw) := by
  intro m
  induction m with
  | zero =>
      intro A hJA β hβ c hc ks
      exact hβ c (by rwa [owG_zero, bot_BwG, add_zero] at hc) ks
  | succ m ih =>
      intro A hJA β hβ c hc ks
      have hstep : β + owG (⊥ : Bw) m < β + owG (⊥ : Bw) (m + 1) :=
        BwG_add_lt_left β (owG_ltR (⊥ : Bw) (by omega))
      refine WPdT_twoA_runB (a := β + owG (⊥ : Bw) (m + 1))
        (ne_bot_of_gt (lt_of_le_of_lt bot_le hstep)) hc
        (JkA_twoItP (T := Jk1.nil) hJA trivial m) ?_ ks
      intro ks'
      exact ih A hJA β hβ (β + owG (⊥ : Bw) (m + 1)) hstep ks'

theorem owG_pos_succ {α : Type} [LinearOrder α] (e : α) (m : ℕ) :
    (⊥ : BwG α) < owG e (m + 1) := by
  rw [← owG_zero e]
  exact owG_ltR e (by omega)

theorem RunJ_PayNil (j n : ℕ) : RunJ (PayIt Jk1.nil (Yv j) n) (ow j n) := by
  have h := AStat_all j n Jk1.nil trivial ⊥ RunJ_nil
  rwa [bot_Bw, zero_add] at h

theorem WPdw_twoP (j n : ℕ) (ks : List Bwx) :
    WPdT (owG (ow (j + 1) (n + 1)) 2 :: ks)
      (Jk1.two Jk1.nil (PayIt Jk1.nil (Yv (j + 1)) (n + 1))) := by
  refine CStat_of_BStat (BStat_all j) (PayIt Jk1.nil (Yv (j + 1)) n)
    (JkA_PayIt (Z := Jk1.nil) trivial (Bok_Yv (j + 1)) n) (ow (j + 1) n)
    (RunJ_PayNil (j + 1) n)
    Jk1.nil trivial ⊥ (fun c _ ks' => WPdT_nilAll _) _ ?_ ks
  rw [bot_BwG, zero_add, ow_add_same]
  exact owG_ltR (ow (j + 1) (n + 1)) (by omega)

/-- `Xj j n` の列は `(l+1,2,0)(l+2,2,0)` の下に `((l+3,0,0)(l+4,0,0)^(j+1))^(n+1)`。 -/
def Xj (j n : ℕ) : Jk1 :=
  Jk1.two Jk1.nil (Jk1.two Jk1.nil (PayIt Jk1.nil (Yv (j + 1)) (n + 1)))

theorem WPdw_Xj (j n : ℕ) (ks : List Bwx) : WPdT ((⊥ : Bwx) :: ks) (Xj j n) :=
  WPdT_twoOf (b := owG (ow (j + 1) (n + 1)) 2)
    (ne_bot_of_gt (owG_pos_succ (ow (j + 1) (n + 1)) 1)) trivial
    (fun q _ => WPdT_nilAll _) (WPdw_twoP j n ks)

theorem GOK_oneXj (j n : ℕ) : GOK (Jk1.one Jk1.nil (Xj j n)) :=
  (WPdT_bnil (Bud := Bwx) _).mp
    (WPdT_step ([] : List Bwx) (JkT_nil : FrmNT ([] : List Bwx) Jk1.nil)
      ((WPdT_bnil (Bud := Bwx) _).mpr GOK_nil) (WPdw_Xj j n []))

theorem jk1_PayNil (j n l : ℕ) :
    jk1 l (PayIt Jk1.nil (Yv j) n)
      = (List.range n).flatMap (fun _ =>
          ((l + 1, 0, 0) : ℕ × ℕ × ℕ) :: List.replicate j ((l + 2, 0, 0) : ℕ × ℕ × ℕ)) := by
  rw [jk1_PayIt]
  have e : shiftr01 (l + 1) 0 (Yv j)
      = ((l + 1, 0, 0) : ℕ × ℕ × ℕ) :: List.replicate j ((l + 2, 0, 0) : ℕ × ℕ × ℕ) := by
    have h0 : ((0 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ)) = ((l + 1, 0, 0) : ℕ × ℕ × ℕ) := by
      rw [Nat.zero_add, Nat.zero_add]
    have h1 : ((1 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ)) = ((l + 2, 0, 0) : ℕ × ℕ × ℕ) := by
      rw [Nat.zero_add, show 1 + (l + 1) = l + 2 from by omega]
    show ((0 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ))
        :: List.map (fun p : ℕ × ℕ × ℕ => (p.1 + (l + 1), p.2.1 + 0, p.2.2))
             (List.replicate j ((1, 0, 0) : ℕ × ℕ × ℕ)) = _
    rw [List.map_replicate, h0]
    show ((l + 1, 0, 0) : ℕ × ℕ × ℕ)
        :: List.replicate j ((1 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ)) = _
    rw [h1]
  simp only [e, jk1, List.nil_append]

theorem jk1_Xj (j n l : ℕ) : jk1 l (Xj j n)
    = ((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: ((l + 2, 2, 0) : ℕ × ℕ × ℕ)
      :: (List.range (n + 1)).flatMap (fun _ =>
          ((l + 3, 0, 0) : ℕ × ℕ × ℕ)
            :: List.replicate (j + 1) ((l + 4, 0, 0) : ℕ × ℕ × ℕ)) := by
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ)
        :: jk1 (l + 2) (PayIt Jk1.nil (Yv (j + 1)) (n + 1))))) = _
  rw [jk1_PayNil (j + 1) (n + 1) (l + 2),
    show l + 2 + 1 = l + 3 from by omega, show l + 2 + 2 = l + 4 from by omega]
  simp [jk1]

theorem R375m_blk_rep_mem (j : ℕ) : ∀ n : ℕ,
    R375m ++ (List.range n).flatMap
      (fun _ => ((6, 0, 0) : ℕ × ℕ × ℕ)
        :: List.replicate (j + 1) ((7, 0, 0) : ℕ × ℕ × ℕ)) ∈ W 0
  | 0 => by simpa [R375m] using R375m_mem
  | (n + 1) => by
      have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (Xj j n)]) := by
        simpa using GOK_oneXj j n [] WOk_nil GoodFb_wordJ_nil
      have hh := rowJ_mem_genF Aok_R338 hG
      have e : jk1 2 (Jk1.one Jk1.nil (Xj j n))
          = ((3, 1, 0) : ℕ × ℕ × ℕ) :: ((4, 2, 0) : ℕ × ℕ × ℕ) :: ((5, 2, 0) : ℕ × ℕ × ℕ)
            :: (List.range (n + 1)).flatMap (fun _ => ((6, 0, 0) : ℕ × ℕ × ℕ)
                :: List.replicate (j + 1) ((7, 0, 0) : ℕ × ℕ × ℕ)) := by
        show jk1 2 Jk1.nil ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (2 + 1) (Xj j n)) = _
        rw [jk1_Xj j n 3]
        simp [jk1]
      rw [wordJ_singleton, colJ, e] at hh
      simpa [R375m, R373, R344, R341, R338, List.append_assoc] using hh

/-- ★★★★★★★★ `R600 (7,0,0)^k`（どの `k ≥ 2` でも）。 -/
theorem R600_7rep_mem (j : ℕ) :
    R600 ++ List.replicate (j + 2) ((7, 0, 0) : ℕ × ℕ × ℕ) ∈ W 0 := by
  have hne : (((6, 0, 0) : ℕ × ℕ × ℕ)
      :: List.replicate (j + 1) ((7, 0, 0) : ℕ × ℕ × ℕ)) ≠ [] := by simp
  have hhead : entry (((6, 0, 0) : ℕ × ℕ × ℕ)
      :: List.replicate (j + 1) ((7, 0, 0) : ℕ × ℕ × ℕ)) 0 0 < 7 := by
    simp [entry]
  have htail : ∀ r, 1 ≤ r →
      r < (((6, 0, 0) : ℕ × ℕ × ℕ)
        :: List.replicate (j + 1) ((7, 0, 0) : ℕ × ℕ × ℕ)).length →
      7 ≤ entry (((6, 0, 0) : ℕ × ℕ × ℕ)
        :: List.replicate (j + 1) ((7, 0, 0) : ℕ × ℕ × ℕ)) 0 r := by
    intro r h1 h2
    rcases r with _ | r
    · omega
    · have hr : r < j + 1 := by simpa using h2
      show 7 ≤ ((((6, 0, 0) : ℕ × ℕ × ℕ)
        :: List.replicate (j + 1) ((7, 0, 0) : ℕ × ℕ × ℕ)).getD (r + 1)
          ((0, 0, 0) : ℕ × ℕ × ℕ)).1
      rw [List.getD_cons_succ, getD_rep, if_pos hr]
  have hmem := flat_mem'' (Y0 := R375m)
    (M := ((6, 0, 0) : ℕ × ℕ × ℕ)
      :: List.replicate (j + 1) ((7, 0, 0) : ℕ × ℕ × ℕ)) (d := 7)
    hne hhead htail (R375m_blk_rep_mem j)
  have erep : List.replicate (j + 1) ((7, 0, 0) : ℕ × ℕ × ℕ)
      ++ [((7, 0, 0) : ℕ × ℕ × ℕ)] = List.replicate (j + 2) ((7, 0, 0) : ℕ × ℕ × ℕ) := by
    conv_rhs => rw [show j + 2 = (j + 1) + 1 from rfl, List.replicate_succ']
  rw [R600, List.append_assoc]
  rw [List.append_assoc, List.cons_append, erep] at hmem
  exact hmem

#print axioms R375m_blk_rep_mem
#print axioms R600_7rep_mem

/-- ★★★★★★★★★ 塔 `R600 (7,0,0)^k` の極限 `R600 (7,0,0)(8,0,0)`。 -/
theorem R600_78_mem :
    R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hne : [((7, 0, 0) : ℕ × ℕ × ℕ)] ≠ [] := by simp
  have hhead : entry [((7, 0, 0) : ℕ × ℕ × ℕ)] 0 0 < 8 := by simp [entry]
  have htail : ∀ r, 1 ≤ r → r < ([((7, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq).length →
      8 ≤ entry [((7, 0, 0) : ℕ × ℕ × ℕ)] 0 r := by
    intro r hr1 hr2
    simp only [List.length_singleton] at hr2
    omega
  have htw : ∀ n : ℕ, R600 ++ (List.range n).flatMap
      (fun _ => [((7, 0, 0) : ℕ × ℕ × ℕ)]) ∈ W 0 := by
    intro n
    rw [flatMap_singleton_range]
    match n with
    | 0 => simpa using Aok_R600.mem
    | 1 => simpa [List.replicate, Z700] using Aok_Z700.mem
    | (k + 2) => exact R600_7rep_mem k
  have hmem := flat_mem'' (Y0 := R600) (M := [((7, 0, 0) : ℕ × ℕ × ℕ)]) (d := 8)
    hne hhead htail htw
  simpa [List.append_assoc] using hmem

/-- 新しい台座 `R600 (7,0,0)(8,0,0)`。 -/
def Z78 : TrioSeq := R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)]

theorem Z78_eq : Z78 = [((0, 0, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ),
    ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ),
    ((5, 2, 0) : ℕ × ℕ × ℕ),
    ((6, 0, 0) : ℕ × ℕ × ℕ),
    ((7, 0, 0) : ℕ × ℕ × ℕ),
    ((8, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [Z78, R600, R375m, R373, R344, R341, R338]

theorem Z78_ne : Z78 ≠ [] := by rw [Z78_eq]; simp

theorem Z78_head : entry Z78 0 0 = 0 := by rw [Z78_eq]; simp [entry]

theorem Z78_tail : ∀ r, 1 ≤ r → r < Z78.length → 1 ≤ entry Z78 0 r := by
  intro r hr1 hrl
  rw [Z78_eq] at hrl ⊢
  simp only [List.length_cons, List.length_nil] at hrl
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r <;>
    first
      | omega
      | simp [entry]

theorem Aok_Z78 : Aok Z78 where
  mem := R600_78_mem
  ne := Z78_ne
  deep := ⟨Z78_head, Z78_tail⟩
  zroot := by
    rw [Z78_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  mono := by
    rw [Z78_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

/-- ★★★★★★★★★ 新しい台座の上、輪を `n` 周した 4 パラメータの無限族。 -/
theorem LoopIt_Z78_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (j n : ℕ) :
    LoopIt Z78 m ws j n ∈ W 0 := (Aok_LoopIt Aok_Z78 m hw j n).mem

theorem LoopIt_Z78_nil_mem (m p j n : ℕ) :
    LoopIt Z78 m (List.replicate p (AltT 0)) j n ∈ W 0 :=
  LoopIt_Z78_mem m (WJ_rep_AltT 0 p) j n

#print axioms R600_78_mem
#print axioms LoopIt_Z78_nil_mem

/-! ### ★★★★★★ 指数の型をパラメータにした階の梯子

指数の型 `α`、予算は `BwG α`。荷 `Y` ごとに 3 つの述語を持つ:

- `RunLd Y q`: `RnG Z e → RnG (PayIt Z Y n) (e + q n)`（鎖）
- `AtLd Y q1`: `two N (two A (pay Z Y))` を枠の中に置ける（_at）
- `TopLd Y q1`: 同じものを予算 `t` の上に置ける（_top）

`Bwx = BwG Bw` を指数にすると `ω^ω = owG (ow 1 1) 1` が使えて、
荷 `Ys = (0,0,0)(1,0,0)(2,0,0)`（`Ys⟦n⟧ = Yv n`）が入る。 -/

section LadG

variable {α : Type} [LinearOrder α] [WellFoundedLT α] [AddCommMonoid α]

def RnG (Z : Jk1) (e : α) : Prop := ∀ (m : ℕ) (A : Jk1), JkA A → ∀ β : BwG α,
  (∀ c : BwG α, β < c → ∀ ks : List (BwG α), WPdT (c :: ks) A) →
  ∀ c : BwG α, β + owG e m < c → ∀ ks : List (BwG α),
    WPdT (c :: ks) (twoIt A Z m)

def RunLd (Y : TrioSeq) (q : ℕ → α) : Prop :=
  ∀ (n : ℕ) (Z : Jk1), JkA Z → ∀ e : α, RnG Z e → RnG (PayIt Z Y n) (e + q n)

def AtLd (Y : TrioSeq) (q1 : α) : Prop :=
  ∀ Z : Jk1, JkA Z → ∀ e : α, RnG Z e → ∀ A : Jk1, JkA A → ∀ β : BwG α,
    (∀ c : BwG α, β < c → ∀ ks : List (BwG α), WPdT (c :: ks) A) →
    ∀ t : BwG α, β + owG (e + q1) 1 ≤ t →
    ∀ (B : List (BwG α)) (N : Jk1), JkA N →
      (∀ r : List (BwG α), (∀ x ∈ r, x < t) → WPdT ((⊥ : BwG α) :: r ++ B) N) →
      WPdT ((⊥ : BwG α) :: B) (Jk1.two N (Jk1.two A (Jk1.pay Z Y)))

def TopLd (Y : TrioSeq) (q1 : α) : Prop :=
  ∀ Z : Jk1, JkA Z → ∀ e : α, RnG Z e → ∀ A : Jk1, JkA A → ∀ β : BwG α,
    (∀ c : BwG α, β < c → ∀ ks : List (BwG α), WPdT (c :: ks) A) →
    ∀ t : BwG α, β + owG (e + q1) 1 < t →
    ∀ ks : List (BwG α), WPdT (t :: ks) (Jk1.two A (Jk1.pay Z Y))

theorem RunG_nil (e : α) : RnG Jk1.nil e := by
  intro m
  induction m with
  | zero =>
      intro A hJA β hβ c hc ks
      exact hβ c (by rwa [owG_zero, bot_BwG, add_zero] at hc) ks
  | succ m ih =>
      intro A hJA β hβ c hc ks
      have hstep : β + owG e m < β + owG e (m + 1) :=
        BwG_add_lt_left β (owG_ltR e (by omega))
      refine WPdT_twoA_runB (a := β + owG e (m + 1))
        (ne_bot_of_gt (lt_of_le_of_lt bot_le hstep)) hc
        (JkA_twoItP (T := Jk1.nil) hJA trivial m) ?_ ks
      intro ks'
      exact ih A hJA β hβ (β + owG e (m + 1)) hstep ks'

theorem TopLd_of_AtLd {Y : TrioSeq} {q1 : α} (hB : AtLd Y q1) : TopLd Y q1 := by
  intro Z hJZ e hR A hJA β hβ t ht ks
  have htb : t ≠ ⊥ := ne_bot_of_gt (lt_of_le_of_lt bot_le ht)
  refine (WPdT_cb htb ks _).mpr (fun r hr U N hU hUk hJN hNt => ?_)
  refine WPdT_two_of_ctx hU hUk (fun ctx hc => ?_)
  exact (WPdT_iff ((⊥ : BwG α) :: (r ++ ks)) _).mp
    (hB Z hJZ e hR A hJA β hβ t (le_of_lt ht) (r ++ ks) N hJN hNt) ctx hc

/-- 荷 `[(0,0,0)]` の鎖。段は `WPdT_twoAZ_top` が直に作る。 -/
theorem RunLd_zero {q : ℕ → α} (hq0 : q 0 = 0)
    (hqm : ∀ n : ℕ, q n < q (n + 1))
    (hadd : ∀ (b : α) {x y : α}, x < y → b + x < b + y) :
    RunLd (Yv 0) q := by
  intro n
  induction n with
  | zero =>
      intro Z hJZ e hR m A hJA β hβ c hc ks
      exact hR m A hJA β hβ c (by rwa [hq0, add_zero] at hc) ks
  | succ n ih =>
      intro Z hJZ e hR m
      induction m with
      | zero =>
          intro A hJA β hβ c hc ks
          exact hβ c (by rwa [owG_zero, bot_BwG, add_zero] at hc) ks
      | succ m ihm =>
          intro A hJA β hβ c hc ks
          have hJW : JkA (PayIt Z (Yv 0) (n + 1)) := JkA_PayIt hJZ (Bok_Yv 0) (n + 1)
          have hJA' : JkA (twoIt A (PayIt Z (Yv 0) (n + 1)) m) := JkA_twoItP hJA hJW m
          have hA' : ∀ c' : BwG α, β + owG (e + q (n + 1)) m < c' →
              ∀ ks' : List (BwG α),
              WPdT (c' :: ks') (twoIt A (PayIt Z (Yv 0) (n + 1)) m) :=
            fun c' hc' ks' => ihm A hJA β hβ c' hc' ks'
          show WPdT (c :: ks) (Jk1.two (twoIt A (PayIt Z (Yv 0) (n + 1)) m)
            (Jk1.pay (PayIt Z (Yv 0) n) (Yv 0)))
          refine WPdT_twoAZ_top
            (S := ⟨fun i => (β + owG (e + q (n + 1)) m) + owG (e + q n) i,
              fun _ _ hij => BwG_add_lt_left _ (owG_ltR (e + q n) hij)⟩)
            (t := c) ?_ hJA' (JkA_PayIt hJZ (Bok_Yv 0) n) ?_ ks
          · intro i
            show (β + owG (e + q (n + 1)) m) + owG (e + q n) i < c
            rw [add_assoc]
            exact lt_trans (BwG_add_lt_left β
              (owG_add_lt (hadd e (hqm n)) m i)) hc
          · intro m' c' hc' ks'
            exact ih Z hJZ e hR m' _ hJA' (β + owG (e + q (n + 1)) m) hA' c' hc' ks'

/-- 荷 `Y` の「_top」があれば `Y` の鎖ができる。 -/
theorem RunLd_of_TopLd {Y : TrioSeq} (hBY : Bok Y) {q : ℕ → α}
    (hq0 : q 0 = 0) (hqa : ∀ n : ℕ, q n + q 1 = q (n + 1))
    (hC : TopLd Y (q 1)) : RunLd Y q := by
  intro n
  induction n with
  | zero =>
      intro Z hJZ e hR m A hJA β hβ c hc ks
      exact hR m A hJA β hβ c (by rwa [hq0, add_zero] at hc) ks
  | succ n ih =>
      intro Z hJZ e hR m
      induction m with
      | zero =>
          intro A hJA β hβ c hc ks
          exact hβ c (by rwa [owG_zero, bot_BwG, add_zero] at hc) ks
      | succ m ihm =>
          intro A hJA β hβ c hc ks
          have hJW : JkA (PayIt Z Y (n + 1)) := JkA_PayIt hJZ hBY (n + 1)
          have hJA' : JkA (twoIt A (PayIt Z Y (n + 1)) m) := JkA_twoItP hJA hJW m
          have hA' : ∀ c' : BwG α, β + owG (e + q (n + 1)) m < c' →
              ∀ ks' : List (BwG α),
              WPdT (c' :: ks') (twoIt A (PayIt Z Y (n + 1)) m) :=
            fun c' hc' ks' => ihm A hJA β hβ c' hc' ks'
          show WPdT (c :: ks) (Jk1.two (twoIt A (PayIt Z Y (n + 1)) m)
            (Jk1.pay (PayIt Z Y n) Y))
          refine hC (PayIt Z Y n) (JkA_PayIt hJZ hBY n) (e + q n) (ih Z hJZ e hR)
            _ hJA' (β + owG (e + q (n + 1)) m) hA' c ?_ ks
          have he : (e + q n) + q 1 = e + q (n + 1) := by rw [add_assoc, hqa]
          rw [he, add_assoc, owG_add_same]
          exact hc

/-- 荷 `Yv 1 = (0,0,0)(1,0,0)` の「_at」。段は荷 `[(0,0,0)]` の鎖。 -/
theorem AtLd_one {q0 : ℕ → α} {q1 : α} (hR0 : RunLd (Yv 0) q0)
    (hlt : ∀ n : ℕ, q0 n < q1)
    (hadd : ∀ (b : α) {x y : α}, x < y → b + x < b + y) :
    AtLd (Yv 1) q1 := by
  intro Z hJZ e hR A hJA β hβ t ht B N hJN hNt
  refine WPdT_twoAY_at hJA hJZ (Bok_Yv 1) (by rw [Yv_len]) (hasParent_Yv_last 0) hJN ?_
  intro n'
  refine WPdT_congr ((⊥ : BwG α) :: B)
    (fun l => jk1_twotwo_congr (fun l' => (jk1_payYvOper Z 0 (n' + 1) l').symm) l) ?_
  refine WPdT_twoAZ_at
    (S := ⟨fun i => β + owG (e + q0 n') i,
      fun _ _ hij => BwG_add_lt_left β (owG_ltR (e + q0 n') hij)⟩)
    (t := t) ?_ hJA (JkA_PayIt hJZ (Bok_Yv 0) n') ?_ hJN hNt
  · intro i
    exact lt_of_lt_of_le
      (BwG_add_lt_left β (owG_ltL (hadd e (hlt n')) i (by omega))) ht
  · intro m' c' hc' ks'
    exact hR0 n' Z hJZ e hR m' A hJA β hβ c' hc' ks'

/-- `Y⟦n+1⟧` が下の荷 `Y'` の `n+1` 段なら、`Y` の「_at」は `Y'` の鎖と「_at」から出る。 -/
theorem AtLd_iter {Y Y' : TrioSeq} (hBY : Bok Y) (hBY' : Bok Y')
    (hlen : 2 ≤ Y.length)
    (hp : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1))
    (hop : ∀ (n l : ℕ) (Z : Jk1),
      jk1 l (Jk1.pay Z (Y⟦n + 1⟧)) = jk1 l (PayIt Z Y' (n + 1)))
    {q' : ℕ → α} {q'1 q1 : α}
    (hR' : RunLd Y' q') (hA' : AtLd Y' q'1)
    (hlt : ∀ n : ℕ, q' n + q'1 < q1)
    (hadd : ∀ (b : α) {x y : α}, x < y → b + x < b + y) :
    AtLd Y q1 := by
  intro Z hJZ e hR A hJA β hβ t ht B N hJN hNt
  refine WPdT_twoAY_at hJA hJZ hBY hlen hp hJN ?_
  intro n'
  refine WPdT_congr ((⊥ : BwG α) :: B)
    (fun l => jk1_twotwo_congr (fun l' => (hop n' l' Z).symm) l) ?_
  refine hA' (PayIt Z Y' n') (JkA_PayIt hJZ hBY' n') (e + q' n') (hR' n' Z hJZ e hR)
    A hJA β hβ t ?_ B N hJN hNt
  refine le_of_lt (lt_of_lt_of_le (BwG_add_lt_left β (owG_ltL ?_ 1 (by omega))) ht)
  rw [add_assoc]
  exact hadd e (hlt n')

/-- `Y⟦n+1⟧` が荷の族 `F n` なら、`Y` の「_at」は `F n` の「_at」たちから出る。 -/
theorem AtLd_fam {Y : TrioSeq} {F : ℕ → TrioSeq} (hBY : Bok Y)
    (hlen : 2 ≤ Y.length)
    (hp : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1))
    (hop : ∀ (n l : ℕ) (Z : Jk1),
      jk1 l (Jk1.pay Z (Y⟦n + 1⟧)) = jk1 l (Jk1.pay Z (F n)))
    {qf : ℕ → α} {q1 : α}
    (hAf : ∀ n : ℕ, AtLd (F n) (qf n))
    (hlt : ∀ n : ℕ, qf n < q1)
    (hadd : ∀ (b : α) {x y : α}, x < y → b + x < b + y) :
    AtLd Y q1 := by
  intro Z hJZ e hR A hJA β hβ t ht B N hJN hNt
  refine WPdT_twoAY_at hJA hJZ hBY hlen hp hJN ?_
  intro n'
  refine WPdT_congr ((⊥ : BwG α) :: B)
    (fun l => jk1_twotwo_congr (fun l' => (hop n' l' Z).symm) l) ?_
  refine hAf n' Z hJZ e hR A hJA β hβ t ?_ B N hJN hNt
  exact le_of_lt (lt_of_lt_of_le
    (BwG_add_lt_left β (owG_ltL (hadd e (hlt n')) 1 (by omega))) ht)

end LadG

/-- 指数の型 `α` の中の「`ω^j·m` の役をする族」。 -/
structure Pws (α : Type) [LinearOrder α] [AddCommMonoid α] where
  pw : ℕ → ℕ → α
  pw_zero : ∀ j : ℕ, pw j 0 = 0
  pw_add : ∀ j m : ℕ, pw j m + pw j 1 = pw j (m + 1)
  pw_ltR : ∀ (j : ℕ) {m m' : ℕ}, m < m' → pw j m < pw j m'
  pw_ltL : ∀ {j j' : ℕ}, j < j' → ∀ (m : ℕ) {m' : ℕ}, 0 < m' → pw j m < pw j' m'
  add_lt : ∀ (b : α) {x y : α}, x < y → b + x < b + y

/-- ★★★★★★ 階の梯子（指数の型が何でも回る）。 -/
theorem LadYv {α : Type} [LinearOrder α] [WellFoundedLT α] [AddCommMonoid α]
    (P : Pws α) : ∀ j : ℕ, RunLd (Yv j) (P.pw j) ∧ AtLd (Yv (j + 1)) (P.pw (j + 1) 1)
  | 0 =>
      have hR0 : RunLd (Yv 0) (P.pw 0) :=
        RunLd_zero (P.pw_zero 0) (fun n => P.pw_ltR 0 (by omega)) P.add_lt
      ⟨hR0, AtLd_one hR0 (fun n => P.pw_ltL (by omega) n (by omega)) P.add_lt⟩
  | (j + 1) =>
      have hA : AtLd (Yv (j + 1)) (P.pw (j + 1) 1) := (LadYv P j).2
      have hR : RunLd (Yv (j + 1)) (P.pw (j + 1)) :=
        RunLd_of_TopLd (Bok_Yv (j + 1)) (P.pw_zero (j + 1)) (P.pw_add (j + 1))
          (TopLd_of_AtLd hA)
      ⟨hR, AtLd_iter (Bok_Yv (j + 2)) (Bok_Yv (j + 1)) (by rw [Yv_len]; omega)
        (hasParent_Yv_last (j + 1))
        (fun n l Z => jk1_payYvOper Z (j + 1) (n + 1) l) hR hA
        (fun n => by rw [P.pw_add]; exact P.pw_ltL (by omega) (n + 1) (by omega))
        P.add_lt⟩

#print axioms LadYv

/-! ### ★★★★★★★ 荷 `Ys = (0,0,0)(1,0,0)(2,0,0)`（`Ys⟦n⟧ = Yv n`）

階の**上限**の荷。指数 `ω^ω` を要求するので、指数の型を `Bwx = BwG Bw` にする。
`ω^ω = owG (ow 1 1) 1 ∈ Bwx`。予算は `Bwy = BwG Bwx`（順序型 ω^(ω^(ω^ω))）。 -/

abbrev Bwy : Type := BwG Bwx

noncomputable def PwsX : Pws Bwx where
  pw j m := owG (ow 0 j) m
  pw_zero j := by rw [owG_zero, bot_BwG]
  pw_add j m := owG_add_same (ow 0 j) m
  pw_ltR := fun j {_ _} h => owG_ltR (ow 0 j) h
  pw_ltL := fun {_ _} h m {_} hm => owG_ltL (ow_ltR 0 h) m hm
  add_lt := fun b {_ _} h => BwG_add_lt_left b h

def Ys : TrioSeq :=
  [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 0, 0) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ)]

theorem Ys_len : Ys.length = 3 := by simp [Ys]

theorem Flat_Ys : Flat Ys := by
  intro c hc
  simp only [Ys, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem Bok_Ys : Bok Ys := Bok_flat Flat_Ys (by simp [Ys, entry])

theorem Ys_srow (i : ℕ) : srow Ys i = 0 := by
  simp [srow, (Flat_entry Flat_Ys i).1, (Flat_entry Flat_Ys i).2]

theorem Ys_hasParent : hasParent Ys 0 2 := by
  rw [hasParent_zero_iff (by rw [Ys_len]; omega)]
  exact ⟨1, by omega, by simp [Ys, entry]⟩

theorem Ys_parent : parent Ys 0 2 = 1 := by
  have h := parent_nextR Ys_hasParent
  rw [nextR, if_pos rfl] at h
  obtain ⟨-, -, hlt, hval, hmid⟩ := h
  rcases Nat.lt_or_ge (parent Ys 0 2) 1 with hp | hp
  · have hp0 : parent Ys 0 2 = 0 := by omega
    have := hmid 1 ⟨by omega, by omega⟩
    simp [Ys, entry] at this
  · omega

theorem oper_Ys (n : ℕ) : Ys⟦n⟧ = Yv n := by
  have h2 : Ys.length - 1 = 2 := by rw [Ys_len]
  simp only [oper, h2, Ys_srow, Ys_parent]
  rw [if_neg (by omega), if_neg (by simp [Ys, entry]),
    if_neg (by rw [h2, Ys_srow]; exact not_not_intro Ys_hasParent)]
  simp only [Nat.lt_irrefl, show ¬ ((1 : ℕ) < 0) from by omega, if_false,
    Nat.mul_zero, Nat.add_zero, ite_self]
  have e1 : (List.range' 1 (2 - 1)).map
      (fun j => ((entry Ys 0 j, entry Ys 1 j, entry Ys 2 j) : ℕ × ℕ × ℕ))
      = [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
    simp [Ys, entry, List.range']
  rw [show (Ys.take 1 : TrioSeq) = [((0, 0, 0) : ℕ × ℕ × ℕ)] from rfl, e1,
    flatMap_singleton_range]
  rfl

theorem hasParent_Ys_last :
    hasParent Ys (srow Ys (Ys.length - 1)) (Ys.length - 1) := by
  rw [Ys_len, Ys_srow]
  exact Ys_hasParent

theorem AtLd_Ys : AtLd (α := Bwx) Ys (owG (ow 1 1) 1) := by
  refine AtLd_fam (F := fun n => Yv (n + 1)) (qf := fun n => PwsX.pw (n + 1) 1)
    Bok_Ys (by rw [Ys_len]; omega) hasParent_Ys_last
    (fun n l Z => by rw [oper_Ys]) (fun n => (LadYv PwsX n).2) ?_ PwsX.add_lt
  intro n
  have h1 : ow 0 (n + 1) < ow 1 1 := ow_ltL (by omega) (n + 1) (by omega)
  show owG (ow 0 (n + 1)) 1 < owG (ow 1 1) 1
  exact owG_ltL h1 1 (by omega)

theorem TopLd_Ys : TopLd (α := Bwx) Ys (owG (ow 1 1) 1) := TopLd_of_AtLd AtLd_Ys

theorem RunLd_Ys : RunLd (α := Bwx) Ys (fun n => owG (ow 1 1) n) :=
  RunLd_of_TopLd Bok_Ys (by rw [owG_zero, bot_BwG])
    (fun n => owG_add_same (ow 1 1) n) TopLd_Ys

theorem WPdw_twoPs (n : ℕ) (ks : List Bwy) :
    WPdT (owG (owG (ow 1 1) (n + 1)) 2 :: ks)
      (Jk1.two Jk1.nil (PayIt Jk1.nil Ys (n + 1))) := by
  have hR : RnG (PayIt Jk1.nil Ys n) (owG (ow 1 1) n) := by
    have h := RunLd_Ys n Jk1.nil trivial 0 (RunG_nil (0 : Bwx))
    rwa [zero_add] at h
  refine TopLd_Ys (PayIt Jk1.nil Ys n) (JkA_PayIt (Z := Jk1.nil) trivial Bok_Ys n)
    (owG (ow 1 1) n) hR Jk1.nil trivial ⊥ (fun c _ ks' => WPdT_nilAll _) _ ?_ ks
  rw [bot_BwG, zero_add, owG_add_same]
  exact owG_ltR (owG (ow 1 1) (n + 1)) (by omega)

def Xt (n : ℕ) : Jk1 :=
  Jk1.two Jk1.nil (Jk1.two Jk1.nil (PayIt Jk1.nil Ys (n + 1)))

theorem WPdw_Xs (n : ℕ) (ks : List Bwy) : WPdT ((⊥ : Bwy) :: ks) (Xt n) :=
  WPdT_twoOf (b := owG (owG (ow 1 1) (n + 1)) 2)
    (ne_bot_of_gt (owG_pos_succ (owG (ow 1 1) (n + 1)) 1)) trivial
    (fun q _ => WPdT_nilAll _) (WPdw_twoPs n ks)

theorem GOK_oneXs (n : ℕ) : GOK (Jk1.one Jk1.nil (Xt n)) :=
  (WPdT_bnil (Bud := Bwy) _).mp
    (WPdT_step ([] : List Bwy) (JkT_nil : FrmNT ([] : List Bwy) Jk1.nil)
      ((WPdT_bnil (Bud := Bwy) _).mpr GOK_nil) (WPdw_Xs n []))

theorem jk1_PayNilYs (n l : ℕ) :
    jk1 l (PayIt Jk1.nil Ys n)
      = (List.range n).flatMap (fun _ => [((l + 1, 0, 0) : ℕ × ℕ × ℕ),
          ((l + 2, 0, 0) : ℕ × ℕ × ℕ), ((l + 3, 0, 0) : ℕ × ℕ × ℕ)]) := by
  rw [jk1_PayIt]
  have e : shiftr01 (l + 1) 0 Ys = [((l + 1, 0, 0) : ℕ × ℕ × ℕ),
      ((l + 2, 0, 0) : ℕ × ℕ × ℕ), ((l + 3, 0, 0) : ℕ × ℕ × ℕ)] := by
    show [((0 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ)),
        ((1 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ)),
        ((2 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ))] = _
    simp only [Nat.zero_add, show (1 : ℕ) + (l + 1) = l + 2 from by omega,
      show (2 : ℕ) + (l + 1) = l + 3 from by omega]
  simp only [e, jk1, List.nil_append]

theorem jk1_Xs (n l : ℕ) : jk1 l (Xt n)
    = ((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: ((l + 2, 2, 0) : ℕ × ℕ × ℕ)
      :: (List.range (n + 1)).flatMap (fun _ => [((l + 3, 0, 0) : ℕ × ℕ × ℕ),
          ((l + 4, 0, 0) : ℕ × ℕ × ℕ), ((l + 5, 0, 0) : ℕ × ℕ × ℕ)]) := by
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ)
        :: jk1 (l + 2) (PayIt Jk1.nil Ys (n + 1))))) = _
  rw [jk1_PayNilYs (n + 1) (l + 2), show l + 2 + 1 = l + 3 from by omega,
    show l + 2 + 2 = l + 4 from by omega, show l + 2 + 3 = l + 5 from by omega]
  simp [jk1]

theorem R375m_tri_rep_mem : ∀ n : ℕ,
    R375m ++ (List.range n).flatMap (fun _ => [((6, 0, 0) : ℕ × ℕ × ℕ),
      ((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)]) ∈ W 0
  | 0 => by simpa [R375m] using R375m_mem
  | (n + 1) => by
      have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (Xt n)]) := by
        simpa using GOK_oneXs n [] WOk_nil GoodFb_wordJ_nil
      have hh := rowJ_mem_genF Aok_R338 hG
      have e : jk1 2 (Jk1.one Jk1.nil (Xt n))
          = ((3, 1, 0) : ℕ × ℕ × ℕ) :: ((4, 2, 0) : ℕ × ℕ × ℕ) :: ((5, 2, 0) : ℕ × ℕ × ℕ)
            :: (List.range (n + 1)).flatMap (fun _ => [((6, 0, 0) : ℕ × ℕ × ℕ),
                ((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)]) := by
        show jk1 2 Jk1.nil ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (2 + 1) (Xt n)) = _
        rw [jk1_Xs n 3]
        simp [jk1]
      rw [wordJ_singleton, colJ, e] at hh
      simpa [R375m, R373, R344, R341, R338, List.append_assoc] using hh

/-- ★★★★★★★★★★ `R600 (7,0,0)(8,0,0)(7,0,0)`。 -/
theorem R600_787_mem :
    R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ),
      ((7, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hne : [((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ),
      ((8, 0, 0) : ℕ × ℕ × ℕ)] ≠ [] := by simp
  have hhead : entry [((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ),
      ((8, 0, 0) : ℕ × ℕ × ℕ)] 0 0 < 7 := by simp [entry]
  have htail : ∀ r, 1 ≤ r →
      r < ([((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ),
        ((8, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq).length →
      7 ≤ entry [((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ),
        ((8, 0, 0) : ℕ × ℕ × ℕ)] 0 r := by
    intro r h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    rcases r with _ | _ | _ | r
    · omega
    · simp [entry]
    · simp [entry]
    · omega
  have hmem := flat_mem'' (Y0 := R375m)
    (M := [((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ),
      ((8, 0, 0) : ℕ × ℕ × ℕ)]) (d := 7) hne hhead htail R375m_tri_rep_mem
  simpa [R600, List.append_assoc] using hmem

#print axioms oper_Ys
#print axioms R600_787_mem

/-! ### ★★★★★★★ 底を一般にした階の梯子 `Ap Y0 j = Y0 ++ (1,0,0)^j`

`Yv j = Ap [(0,0,0)] j`。底 `Y0` が「添字 1 以上の行 0 の値が全部 1 以上」なら
`(Ap Y0 (j+1))⟦n⟧ = (Ap Y0 j)^n`。 -/

def Ap (Y0 : TrioSeq) (j : ℕ) : TrioSeq := Y0 ++ List.replicate j ((1, 0, 0) : ℕ × ℕ × ℕ)

theorem Ap_zero (Y0 : TrioSeq) : Ap Y0 0 = Y0 := by simp [Ap]

theorem Ap_succ (Y0 : TrioSeq) (j : ℕ) :
    Ap Y0 (j + 1) = Ap Y0 j ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
  show Y0 ++ List.replicate (j + 1) ((1, 0, 0) : ℕ × ℕ × ℕ) = _
  rw [List.replicate_succ', ← List.append_assoc]
  rfl

theorem Ap_len (Y0 : TrioSeq) (j : ℕ) : (Ap Y0 j).length = Y0.length + j := by
  simp [Ap]

theorem Flat_Ap {Y0 : TrioSeq} (h : Flat Y0) (j : ℕ) : Flat (Ap Y0 j) := by
  intro c hc
  rw [Ap, List.mem_append] at hc
  rcases hc with hc | hc
  · exact h c hc
  · rw [List.mem_replicate] at hc
    rw [hc.2]
    exact ⟨rfl, rfl⟩

theorem entry_Ap_lt {Y0 : TrioSeq} {i : ℕ} (h : i < Y0.length) (j r : ℕ) :
    entry (Ap Y0 j) r i = entry Y0 r i := by
  have hg : (Ap Y0 j).getD i ((0, 0, 0) : ℕ × ℕ × ℕ)
      = Y0.getD i ((0, 0, 0) : ℕ × ℕ × ℕ) := by
    rw [Ap, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h]
  simp only [entry, hg]

theorem entry_Ap_ge {Y0 : TrioSeq} {j i : ℕ} (h1 : Y0.length ≤ i)
    (h2 : i < Y0.length + j) : entry (Ap Y0 j) 0 i = 1 := by
  have hg : (Ap Y0 j).getD i ((0, 0, 0) : ℕ × ℕ × ℕ) = ((1, 0, 0) : ℕ × ℕ × ℕ) := by
    rw [Ap, List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
      ← List.getD_eq_getElem?_getD, getD_rep, if_pos (by omega)]
  show ((Ap Y0 j).getD i ((0, 0, 0) : ℕ × ℕ × ℕ)).1 = 1
  rw [hg]

theorem Bok_Ap {Y0 : TrioSeq} (hf : Flat Y0) (hne : Y0 ≠ [])
    (hr : entry Y0 0 0 = 0) (j : ℕ) : Bok (Ap Y0 j) :=
  Bok_flat (Flat_Ap hf j)
    (by rw [entry_Ap_lt (List.length_pos_iff.mpr hne) j 0]; exact hr)

theorem Ap_srow {Y0 : TrioSeq} (hf : Flat Y0) (j i : ℕ) : srow (Ap Y0 j) i = 0 := by
  simp [srow, (Flat_entry (Flat_Ap hf j) i).1, (Flat_entry (Flat_Ap hf j) i).2]

theorem Ap_hasParent {Y0 : TrioSeq} (hne : Y0 ≠ []) (hr : entry Y0 0 0 = 0) (j : ℕ) :
    hasParent (Ap Y0 (j + 1)) 0 (Y0.length + j) := by
  have h0 : 0 < Y0.length := List.length_pos_iff.mpr hne
  rw [hasParent_zero_iff (by rw [Ap_len]; omega)]
  refine ⟨0, by omega, ?_⟩
  rw [entry_Ap_lt h0, hr, entry_Ap_ge (j := j + 1) (by omega) (by omega)]
  omega

theorem Ap_parent {Y0 : TrioSeq} (hne : Y0 ≠ []) (hr : entry Y0 0 0 = 0)
    (hpos : ∀ i, 1 ≤ i → i < Y0.length → 1 ≤ entry Y0 0 i) (j : ℕ) :
    parent (Ap Y0 (j + 1)) 0 (Y0.length + j) = 0 := by
  have h := parent_nextR (Ap_hasParent hne hr j)
  rw [nextR, if_pos rfl] at h
  obtain ⟨-, -, hlt, hval, -⟩ := h
  by_contra hneq
  have hp1 : 1 ≤ parent (Ap Y0 (j + 1)) 0 (Y0.length + j) := by omega
  have hge : 1 ≤ entry (Ap Y0 (j + 1)) 0 (parent (Ap Y0 (j + 1)) 0 (Y0.length + j)) := by
    rcases Nat.lt_or_ge (parent (Ap Y0 (j + 1)) 0 (Y0.length + j)) Y0.length with hlp | hlp
    · rw [entry_Ap_lt hlp]
      exact hpos _ hp1 hlp
    · rw [entry_Ap_ge hlp (by omega)]
  have hd : entry (Ap Y0 (j + 1)) 0 (Y0.length + j) = 1 :=
    entry_Ap_ge (by omega) (by omega)
  rw [hd] at hval
  omega

theorem Ap_take {Y0 : TrioSeq} (j : ℕ) :
    (Ap Y0 (j + 1)).take (Y0.length + j) = Ap Y0 j := by
  rw [Ap_succ, show Y0.length + j = (Ap Y0 j).length from (Ap_len Y0 j).symm,
    List.take_left]

theorem oper_Ap {Y0 : TrioSeq} (hf : Flat Y0) (hne : Y0 ≠ [])
    (hr : entry Y0 0 0 = 0)
    (hpos : ∀ i, 1 ≤ i → i < Y0.length → 1 ≤ entry Y0 0 i) (j n : ℕ) :
    (Ap Y0 (j + 1))⟦n⟧ = (List.range n).flatMap (fun _ => Ap Y0 j) := by
  have h0 : 0 < Y0.length := List.length_pos_iff.mpr hne
  have h2 : (Ap Y0 (j + 1)).length - 1 = Y0.length + j := by rw [Ap_len]; omega
  simp only [oper, h2, Ap_srow hf, Ap_parent hne hr hpos]
  rw [if_neg (by omega),
    if_neg (by rw [entry_Ap_ge (j := j + 1) (by omega) (by omega)]; simp),
    if_neg (by rw [h2, Ap_srow hf]; exact not_not_intro (Ap_hasParent hne hr j))]
  simp only [Nat.lt_irrefl, show ¬ ((1 : ℕ) < 0) from by omega, if_false,
    Nat.sub_zero, Nat.mul_zero, Nat.add_zero, ite_self, List.take_zero,
    List.nil_append,
    map_range'_entry (M := Ap Y0 (j + 1)) (k := Y0.length + j)
      (by rw [Ap_len]; omega),
    Ap_take]

theorem jk1_payOperRep (Z : Jk1) {Y Y' : TrioSeq} {n : ℕ}
    (h : Y⟦n⟧ = (List.range n).flatMap (fun _ => Y')) (l : ℕ) :
    jk1 l (Jk1.pay Z (Y⟦n⟧)) = jk1 l (PayIt Z Y' n) := by
  show jk1 l Z ++ shiftr01 (l + 1) 0 (Y⟦n⟧) = _
  rw [h, shiftr01_flatMap, jk1_PayIt]

theorem Ap_hp {Y0 : TrioSeq} (hf : Flat Y0) (hne : Y0 ≠ [])
    (hr : entry Y0 0 0 = 0) (j : ℕ) :
    hasParent (Ap Y0 (j + 1)) (srow (Ap Y0 (j + 1)) ((Ap Y0 (j + 1)).length - 1))
      ((Ap Y0 (j + 1)).length - 1) := by
  have h0 : 0 < Y0.length := List.length_pos_iff.mpr hne
  rw [show (Ap Y0 (j + 1)).length - 1 = Y0.length + j from by rw [Ap_len]; omega,
    Ap_srow hf]
  exact Ap_hasParent hne hr j

/-- ★★★★★★★ 底 `Y0` の上の階の梯子。 -/
theorem LadAp {α : Type} [LinearOrder α] [WellFoundedLT α] [AddCommMonoid α]
    (P : Pws α) {Y0 : TrioSeq} (hf : Flat Y0) (hne : Y0 ≠ [])
    (hr : entry Y0 0 0 = 0)
    (hpos : ∀ i, 1 ≤ i → i < Y0.length → 1 ≤ entry Y0 0 i)
    (hR0 : RunLd Y0 (P.pw 0)) (hA0 : AtLd Y0 (P.pw 0 1)) :
    ∀ j : ℕ, RunLd (Ap Y0 j) (P.pw j) ∧ AtLd (Ap Y0 (j + 1)) (P.pw (j + 1) 1)
  | 0 => by
      have h0 : 0 < Y0.length := List.length_pos_iff.mpr hne
      refine ⟨by rw [Ap_zero]; exact hR0, ?_⟩
      have hop : ∀ (n l : ℕ) (Z : Jk1),
          jk1 l (Jk1.pay Z ((Ap Y0 1)⟦n + 1⟧)) = jk1 l (PayIt Z Y0 (n + 1)) := by
        intro n l Z
        refine jk1_payOperRep Z ?_ l
        rw [oper_Ap hf hne hr hpos 0 (n + 1), Ap_zero]
      exact AtLd_iter (Bok_Ap hf hne hr 1) (Bok_flat hf hr)
        (by rw [Ap_len]; omega) (Ap_hp hf hne hr 0) hop hR0 hA0
        (fun n => by rw [P.pw_add]; exact P.pw_ltL (by omega) (n + 1) (by omega))
        P.add_lt
  | (j + 1) => by
      have h0 : 0 < Y0.length := List.length_pos_iff.mpr hne
      have hA : AtLd (Ap Y0 (j + 1)) (P.pw (j + 1) 1) :=
        (LadAp P hf hne hr hpos hR0 hA0 j).2
      have hR : RunLd (Ap Y0 (j + 1)) (P.pw (j + 1)) :=
        RunLd_of_TopLd (Bok_Ap hf hne hr (j + 1)) (P.pw_zero (j + 1))
          (P.pw_add (j + 1)) (TopLd_of_AtLd hA)
      exact ⟨hR, AtLd_iter (Bok_Ap hf hne hr (j + 2)) (Bok_Ap hf hne hr (j + 1))
        (by rw [Ap_len]; omega) (Ap_hp hf hne hr (j + 1))
        (fun n l Z => jk1_payOperRep Z (oper_Ap hf hne hr hpos (j + 1) (n + 1)) l)
        hR hA
        (fun n => by rw [P.pw_add]; exact P.pw_ltL (by omega) (n + 1) (by omega))
        P.add_lt⟩

#print axioms LadAp

/-! ### ★★★★★★★★ 底 `Ys` の階の梯子 → `R600(7,0,0)(8,0,0)(7,0,0)^k` -/

noncomputable def PwsW : Pws Bwx where
  pw j m := owG (ow 1 1 + ow 0 j) m
  pw_zero j := by rw [owG_zero, bot_BwG]
  pw_add := fun j m => owG_add_same (ow 1 1 + ow 0 j) m
  pw_ltR := fun j {_ _} h => owG_ltR (ow 1 1 + ow 0 j) h
  pw_ltL := fun {_ _} h m {_} hm =>
    owG_ltL (Bw_add_lt_left (ow 1 1) (ow_ltR 0 h)) m hm
  add_lt := fun b {_ _} h => BwG_add_lt_left b h

theorem pwW_zero_eq : (PwsW.pw 0) = (fun m => owG (ow 1 1) m) := by
  funext m
  show owG (ow 1 1 + ow 0 0) m = _
  rw [ow_zero, bot_Bw, add_zero]

theorem Ys_ne : Ys ≠ [] := by simp [Ys]

theorem Ys_root : entry Ys 0 0 = 0 := by simp [Ys, entry]

theorem Ys_pos : ∀ i, 1 ≤ i → i < Ys.length → 1 ≤ entry Ys 0 i := by
  intro i h1 h2
  rw [Ys_len] at h2
  rcases i with _ | _ | _ | i <;> first | omega | simp [Ys, entry]

theorem LadW : ∀ j : ℕ,
    RunLd (Ap Ys j) (PwsW.pw j) ∧ AtLd (Ap Ys (j + 1)) (PwsW.pw (j + 1) 1) :=
  LadAp PwsW Flat_Ys Ys_ne Ys_root Ys_pos
    (by rw [pwW_zero_eq]; exact RunLd_Ys)
    (by rw [show PwsW.pw 0 1 = owG (ow 1 1) 1 from congrFun pwW_zero_eq 1];
        exact AtLd_Ys)

theorem WPdw_twoAp (j n : ℕ) (ks : List Bwy) :
    WPdT (owG (PwsW.pw (j + 1) (n + 1)) 2 :: ks)
      (Jk1.two Jk1.nil (PayIt Jk1.nil (Ap Ys (j + 1)) (n + 1))) := by
  have hR0 := (LadW (j + 1)).1 n Jk1.nil trivial 0 (RunG_nil (0 : Bwx))
  rw [zero_add] at hR0
  refine TopLd_of_AtLd ((LadW j).2) (PayIt Jk1.nil (Ap Ys (j + 1)) n)
    (JkA_PayIt (Z := Jk1.nil) trivial (Bok_Ap Flat_Ys Ys_ne Ys_root (j + 1)) n)
    (PwsW.pw (j + 1) n) hR0 Jk1.nil trivial ⊥
    (fun c _ ks' => WPdT_nilAll _) _ ?_ ks
  rw [bot_BwG, zero_add, PwsW.pw_add]
  exact owG_ltR (PwsW.pw (j + 1) (n + 1)) (by omega)

def Xa (j n : ℕ) : Jk1 :=
  Jk1.two Jk1.nil (Jk1.two Jk1.nil (PayIt Jk1.nil (Ap Ys (j + 1)) (n + 1)))

theorem WPdw_Xa (j n : ℕ) (ks : List Bwy) : WPdT ((⊥ : Bwy) :: ks) (Xa j n) :=
  WPdT_twoOf (b := owG (PwsW.pw (j + 1) (n + 1)) 2)
    (ne_bot_of_gt (owG_pos_succ (PwsW.pw (j + 1) (n + 1)) 1)) trivial
    (fun q _ => WPdT_nilAll _) (WPdw_twoAp j n ks)

theorem GOK_oneXa (j n : ℕ) : GOK (Jk1.one Jk1.nil (Xa j n)) :=
  (WPdT_bnil (Bud := Bwy) _).mp
    (WPdT_step ([] : List Bwy) (JkT_nil : FrmNT ([] : List Bwy) Jk1.nil)
      ((WPdT_bnil (Bud := Bwy) _).mpr GOK_nil) (WPdw_Xa j n []))

theorem jk1_PayNilG (Y : TrioSeq) (n l : ℕ) :
    jk1 l (PayIt Jk1.nil Y n)
      = (List.range n).flatMap (fun _ => shiftr01 (l + 1) 0 Y) := by
  rw [jk1_PayIt]
  simp [jk1]

theorem shift_ApYs (j l : ℕ) : shiftr01 (l + 1) 0 (Ap Ys j)
    = [((l + 1, 0, 0) : ℕ × ℕ × ℕ), ((l + 2, 0, 0) : ℕ × ℕ × ℕ),
        ((l + 3, 0, 0) : ℕ × ℕ × ℕ)]
      ++ List.replicate j ((l + 2, 0, 0) : ℕ × ℕ × ℕ) := by
  show List.map _ (Ys ++ List.replicate j ((1, 0, 0) : ℕ × ℕ × ℕ)) = _
  rw [List.map_append, List.map_replicate]
  congr 1
  · show [((0 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ)),
        ((1 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ)),
        ((2 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ))] = _
    simp only [Nat.zero_add, show (1 : ℕ) + (l + 1) = l + 2 from by omega,
      show (2 : ℕ) + (l + 1) = l + 3 from by omega]
  · show List.replicate j ((1 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ)) = _
    simp only [Nat.zero_add, show (1 : ℕ) + (l + 1) = l + 2 from by omega]

theorem jk1_Xa (j n l : ℕ) : jk1 l (Xa j n)
    = ((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: ((l + 2, 2, 0) : ℕ × ℕ × ℕ)
      :: (List.range (n + 1)).flatMap (fun _ =>
          [((l + 3, 0, 0) : ℕ × ℕ × ℕ), ((l + 4, 0, 0) : ℕ × ℕ × ℕ),
            ((l + 5, 0, 0) : ℕ × ℕ × ℕ)]
          ++ List.replicate (j + 1) ((l + 4, 0, 0) : ℕ × ℕ × ℕ)) := by
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ)
        :: jk1 (l + 2) (PayIt Jk1.nil (Ap Ys (j + 1)) (n + 1))))) = _
  rw [jk1_PayNilG (Ap Ys (j + 1)) (n + 1) (l + 2), shift_ApYs,
    show l + 2 + 1 = l + 3 from by omega, show l + 2 + 2 = l + 4 from by omega,
    show l + 2 + 3 = l + 5 from by omega]
  simp [jk1]

/-- 塊 `M j = (6,0,0)(7,0,0)(8,0,0)(7,0,0)^j`。 -/
def Mb (j : ℕ) : TrioSeq :=
  [((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)]
    ++ List.replicate j ((7, 0, 0) : ℕ × ℕ × ℕ)

theorem entry_appRep_ge (A : TrioSeq) (x : ℕ × ℕ × ℕ) {j i : ℕ}
    (h1 : A.length ≤ i) (h2 : i < A.length + j) :
    entry (A ++ List.replicate j x) 0 i = x.1 := by
  have hg : (A ++ List.replicate j x).getD i ((0, 0, 0) : ℕ × ℕ × ℕ) = x := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
      ← List.getD_eq_getElem?_getD, getD_rep, if_pos (by omega)]
  show ((A ++ List.replicate j x).getD i ((0, 0, 0) : ℕ × ℕ × ℕ)).1 = x.1
  rw [hg]

theorem Mb_len (j : ℕ) : (Mb j).length = 3 + j := by simp [Mb]; omega

theorem Mb_head (j : ℕ) : entry (Mb j) 0 0 = 6 := by simp [Mb, entry]

theorem Mb_tail (j : ℕ) : ∀ r, 1 ≤ r → r < (Mb j).length → 7 ≤ entry (Mb j) 0 r := by
  intro r h1 h2
  rw [Mb_len] at h2
  rcases r with _ | _ | _ | r
  · omega
  · show 7 ≤ entry (Mb j) 0 1
    simp [Mb, entry]
  · show 7 ≤ entry (Mb j) 0 2
    simp [Mb, entry]
  · rw [Mb, entry_appRep_ge _ _ (by simp)
      (by simp only [List.length_cons, List.length_nil]; omega)]

theorem R375m_Mb_rep_mem (j : ℕ) : ∀ n : ℕ,
    R375m ++ (List.range n).flatMap (fun _ => Mb (j + 1)) ∈ W 0
  | 0 => by simpa [R375m] using R375m_mem
  | (n + 1) => by
      have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (Xa j n)]) := by
        simpa using GOK_oneXa j n [] WOk_nil GoodFb_wordJ_nil
      have hh := rowJ_mem_genF Aok_R338 hG
      have e : jk1 2 (Jk1.one Jk1.nil (Xa j n))
          = ((3, 1, 0) : ℕ × ℕ × ℕ) :: ((4, 2, 0) : ℕ × ℕ × ℕ) :: ((5, 2, 0) : ℕ × ℕ × ℕ)
            :: (List.range (n + 1)).flatMap (fun _ => Mb (j + 1)) := by
        show jk1 2 Jk1.nil ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (2 + 1) (Xa j n)) = _
        rw [jk1_Xa j n 3]
        simp [jk1, Mb]
      rw [wordJ_singleton, colJ, e] at hh
      simpa [R375m, R373, R344, R341, R338, List.append_assoc] using hh

/-- ★★★★★★★★★★ `R600 (7,0,0)(8,0,0)(7,0,0)^(k+2)`。 -/
theorem R600_78_7rep_mem (j : ℕ) :
    R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)]
      ++ List.replicate (j + 2) ((7, 0, 0) : ℕ × ℕ × ℕ) ∈ W 0 := by
  have hmem := flat_mem'' (Y0 := R375m) (M := Mb (j + 1)) (d := 7)
    (by simp [Mb]) (by rw [Mb_head]; omega) (Mb_tail (j + 1))
    (R375m_Mb_rep_mem j)
  have e : Mb (j + 1) ++ [((7, 0, 0) : ℕ × ℕ × ℕ)]
      = [((6, 0, 0) : ℕ × ℕ × ℕ), ((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)]
        ++ List.replicate (j + 2) ((7, 0, 0) : ℕ × ℕ × ℕ) := by
    rw [Mb, List.append_assoc]
    congr 1
    conv_rhs => rw [show j + 2 = (j + 1) + 1 from rfl, List.replicate_succ']
  rw [List.append_assoc] at hmem
  rw [e] at hmem
  simpa [R600, List.append_assoc] using hmem

#print axioms LadW
#print axioms R600_78_7rep_mem

/-- ★★★★★★★★★★★ 塔 `R600(7,0,0)(8,0,0)(7,0,0)^k` の極限。 -/
theorem R600_7878_mem :
    R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ),
      ((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hne : [((7, 0, 0) : ℕ × ℕ × ℕ)] ≠ [] := by simp
  have hhead : entry [((7, 0, 0) : ℕ × ℕ × ℕ)] 0 0 < 8 := by simp [entry]
  have htail : ∀ r, 1 ≤ r → r < ([((7, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq).length →
      8 ≤ entry [((7, 0, 0) : ℕ × ℕ × ℕ)] 0 r := by
    intro r hr1 hr2
    simp only [List.length_singleton] at hr2
    omega
  have htw : ∀ n : ℕ, (R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)])
      ++ (List.range n).flatMap (fun _ => [((7, 0, 0) : ℕ × ℕ × ℕ)]) ∈ W 0 := by
    intro n
    rw [flatMap_singleton_range]
    match n with
    | 0 => simpa using R600_78_mem
    | 1 => simpa [List.replicate, List.append_assoc] using R600_787_mem
    | (k + 2) => exact R600_78_7rep_mem k
  have hmem := flat_mem''
    (Y0 := R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)])
    (M := [((7, 0, 0) : ℕ × ℕ × ℕ)]) (d := 8) hne hhead htail htw
  simpa [List.append_assoc] using hmem

/-- 新しい台座 `R600 (7,0,0)(8,0,0)(7,0,0)(8,0,0)`。 -/
def Z7878 : TrioSeq :=
  R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ),
    ((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)]

theorem Z7878_eq : Z7878 = [((0, 0, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ),
    ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ),
    ((5, 2, 0) : ℕ × ℕ × ℕ),
    ((6, 0, 0) : ℕ × ℕ × ℕ),
    ((7, 0, 0) : ℕ × ℕ × ℕ),
    ((8, 0, 0) : ℕ × ℕ × ℕ),
    ((7, 0, 0) : ℕ × ℕ × ℕ),
    ((8, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [Z7878, R600, R375m, R373, R344, R341, R338]

theorem Z7878_ne : Z7878 ≠ [] := by rw [Z7878_eq]; simp

theorem Z7878_head : entry Z7878 0 0 = 0 := by rw [Z7878_eq]; simp [entry]

theorem Z7878_tail : ∀ r, 1 ≤ r → r < Z7878.length → 1 ≤ entry Z7878 0 r := by
  intro r hr1 hrl
  rw [Z7878_eq] at hrl ⊢
  simp only [List.length_cons, List.length_nil] at hrl
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r <;>
    first
      | omega
      | simp [entry]

theorem Aok_Z7878 : Aok Z7878 where
  mem := R600_7878_mem
  ne := Z7878_ne
  deep := ⟨Z7878_head, Z7878_tail⟩
  zroot := by
    rw [Z7878_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> decide
  mono := by
    rw [Z7878_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> decide

/-- ★★★★★★★★★★★ 新しい台座の上、輪を `n` 周した 4 パラメータの無限族。 -/
theorem LoopIt_Z7878_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (j n : ℕ) :
    LoopIt Z7878 m ws j n ∈ W 0 := (Aok_LoopIt Aok_Z7878 m hw j n).mem

theorem LoopIt_Z7878_nil_mem (m p j n : ℕ) :
    LoopIt Z7878 m (List.replicate p (AltT 0)) j n ∈ W 0 :=
  LoopIt_Z7878_mem m (WJ_rep_AltT 0 p) j n

#print axioms R600_7878_mem
#print axioms LoopIt_Z7878_nil_mem

/-! ### ★★★★★★★★ 段を 1 つ上げる荷 `Vs Y0 = Y0 (1,0,0)(2,0,0)`

`(Vs Y0)⟦n⟧ = Ap Y0 n`。`Ys = Vs [(0,0,0)]`。
`Y0` の `Ap` 梯子（`LadAp`）を全部使い切ると `Vs Y0` が置ける。 -/

def Vs (Y0 : TrioSeq) : TrioSeq := Ap Y0 1 ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]

theorem Vs_eq (Y0 : TrioSeq) :
    Vs Y0 = Y0 ++ [((1, 0, 0) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ)] := by
  show (Y0 ++ List.replicate 1 ((1, 0, 0) : ℕ × ℕ × ℕ))
      ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] = _
  simp [List.replicate]

theorem Vs_len (Y0 : TrioSeq) : (Vs Y0).length = Y0.length + 2 := by
  rw [Vs_eq]; simp

theorem Flat_Vs {Y0 : TrioSeq} (hf : Flat Y0) : Flat (Vs Y0) := by
  intro c hc
  rw [Vs_eq, List.mem_append] at hc
  rcases hc with hc | hc
  · exact hf c hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem entry_Vs_lt {Y0 : TrioSeq} {i : ℕ} (h : i < Y0.length + 1) (r : ℕ) :
    entry (Vs Y0) r i = entry (Ap Y0 1) r i :=
  entry_append_lt (by rw [Ap_len]; omega)

theorem entry_Vs_last (Y0 : TrioSeq) : entry (Vs Y0) 0 (Y0.length + 1) = 2 := by
  have h := (entry_append_last (P := Ap Y0 1) (c := ((2, 0, 0) : ℕ × ℕ × ℕ))).1
  rw [Ap_len] at h
  exact h

theorem entry_Vs_mid {Y0 : TrioSeq} (hne : Y0 ≠ []) :
    entry (Vs Y0) 0 Y0.length = 1 := by
  rw [entry_Vs_lt (by omega), entry_Ap_ge (le_refl _) (by omega)]

theorem Vs_root {Y0 : TrioSeq} (hne : Y0 ≠ []) (hr : entry Y0 0 0 = 0) :
    entry (Vs Y0) 0 0 = 0 := by
  have h0 : 0 < Y0.length := List.length_pos_iff.mpr hne
  rw [entry_Vs_lt (by omega), entry_Ap_lt h0, hr]

theorem Vs_pos {Y0 : TrioSeq} (hne : Y0 ≠ [])
    (hpos : ∀ i, 1 ≤ i → i < Y0.length → 1 ≤ entry Y0 0 i) :
    ∀ i, 1 ≤ i → i < (Vs Y0).length → 1 ≤ entry (Vs Y0) 0 i := by
  intro i h1 h2
  rw [Vs_len] at h2
  rcases Nat.lt_or_ge i Y0.length with hi | hi
  · rw [entry_Vs_lt (by omega), entry_Ap_lt hi]
    exact hpos i h1 hi
  · rcases Nat.lt_or_ge i (Y0.length + 1) with hi2 | hi2
    · rw [show i = Y0.length from by omega, entry_Vs_mid hne]
    · rw [show i = Y0.length + 1 from by omega, entry_Vs_last]
      omega

theorem Vs_srow {Y0 : TrioSeq} (hf : Flat Y0) (i : ℕ) : srow (Vs Y0) i = 0 := by
  simp [srow, (Flat_entry (Flat_Vs hf) i).1, (Flat_entry (Flat_Vs hf) i).2]

theorem Vs_hasParent {Y0 : TrioSeq} (hne : Y0 ≠ []) :
    hasParent (Vs Y0) 0 (Y0.length + 1) := by
  rw [hasParent_zero_iff (by rw [Vs_len]; omega)]
  exact ⟨Y0.length, by omega, by rw [entry_Vs_mid hne, entry_Vs_last]; omega⟩

theorem Vs_parent {Y0 : TrioSeq} (hne : Y0 ≠ []) :
    parent (Vs Y0) 0 (Y0.length + 1) = Y0.length := by
  have h := parent_nextR (Vs_hasParent hne)
  rw [nextR, if_pos rfl] at h
  obtain ⟨-, -, hlt, hval, hmid⟩ := h
  by_contra hneq
  have hlp : parent (Vs Y0) 0 (Y0.length + 1) < Y0.length := by omega
  have := hmid Y0.length ⟨hlp, by omega⟩
  rw [entry_Vs_mid hne, entry_Vs_last] at this
  omega

theorem Vs_take {Y0 : TrioSeq} : (Vs Y0).take Y0.length = Y0 := by
  rw [Vs_eq]
  conv_lhs => rw [show Y0.length = Y0.length from rfl]
  exact List.take_left

theorem oper_Vs {Y0 : TrioSeq} (hf : Flat Y0) (hne : Y0 ≠ []) (n : ℕ) :
    (Vs Y0)⟦n⟧ = Ap Y0 n := by
  have h0 : 0 < Y0.length := List.length_pos_iff.mpr hne
  have h2 : (Vs Y0).length - 1 = Y0.length + 1 := by rw [Vs_len]; omega
  simp only [oper, h2, Vs_srow hf, Vs_parent hne]
  rw [if_neg (by omega), if_neg (by rw [entry_Vs_last]; simp),
    if_neg (by rw [h2, Vs_srow hf]; exact not_not_intro (Vs_hasParent hne))]
  simp only [Nat.lt_irrefl, show ¬ ((1 : ℕ) < 0) from by omega, if_false,
    Nat.mul_zero, Nat.add_zero, ite_self]
  have e1 : (List.range' Y0.length (Y0.length + 1 - Y0.length)).map
      (fun j => ((entry (Vs Y0) 0 j, entry (Vs Y0) 1 j, entry (Vs Y0) 2 j)
        : ℕ × ℕ × ℕ)) = [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
    rw [show Y0.length + 1 - Y0.length = 1 from by omega,
      show List.range' Y0.length 1 = [Y0.length] from rfl]
    rw [List.map_cons, List.map_nil, entry_Vs_mid hne,
      (Flat_entry (Flat_Vs hf) Y0.length).1, (Flat_entry (Flat_Vs hf) Y0.length).2]
  rw [Vs_take, e1, flatMap_singleton_range]
  rfl

theorem Bok_Vs {Y0 : TrioSeq} (hf : Flat Y0) (hne : Y0 ≠ [])
    (hr : entry Y0 0 0 = 0) : Bok (Vs Y0) :=
  Bok_flat (Flat_Vs hf) (Vs_root hne hr)

/-- ★★★★★★★★ `Y0` の `Ap` 梯子を使い切ると `Vs Y0` が置ける。 -/
theorem AtLd_Vs {α : Type} [LinearOrder α] [WellFoundedLT α] [AddCommMonoid α]
    (P : Pws α) {Y0 : TrioSeq} (hf : Flat Y0) (hne : Y0 ≠ [])
    (hr : entry Y0 0 0 = 0)
    (hpos : ∀ i, 1 ≤ i → i < Y0.length → 1 ≤ entry Y0 0 i)
    (hR0 : RunLd Y0 (P.pw 0)) (hA0 : AtLd Y0 (P.pw 0 1))
    {q1 : α} (hlt : ∀ j : ℕ, P.pw (j + 1) 1 < q1) :
    AtLd (Vs Y0) q1 := by
  have h0 : 0 < Y0.length := List.length_pos_iff.mpr hne
  refine AtLd_fam (F := fun n => Ap Y0 (n + 1)) (qf := fun n => P.pw (n + 1) 1)
    (Bok_Vs hf hne hr) (by rw [Vs_len]; omega) ?_
    (fun n l Z => by rw [oper_Vs hf hne]) ?_ hlt P.add_lt
  · rw [show (Vs Y0).length - 1 = Y0.length + 1 from by rw [Vs_len]; omega,
      Vs_srow hf]
    exact Vs_hasParent hne
  · exact fun n => (LadAp P hf hne hr hpos hR0 hA0 n).2

#print axioms oper_Vs
#print axioms AtLd_Vs

/-! ### ★★★★★★★★★ 荷の族 `Vk k = (0,0,0)((1,0,0)(2,0,0))^(k+1)` -/

def Vk : ℕ → TrioSeq
  | 0 => Ys
  | (k + 1) => Vs (Vk k)

theorem Vk_eq : ∀ k : ℕ, Vk k = ((0, 0, 0) : ℕ × ℕ × ℕ)
    :: (List.range (k + 1)).flatMap
        (fun _ => [((1, 0, 0) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ)])
  | 0 => by simp [Vk, Ys]
  | (k + 1) => by
      show Vs (Vk k) = _
      rw [Vs_eq, Vk_eq k]
      conv_rhs => rw [List.range_succ, List.flatMap_append]
      simp

theorem Flat_Vk : ∀ k : ℕ, Flat (Vk k)
  | 0 => Flat_Ys
  | (k + 1) => Flat_Vs (Flat_Vk k)

theorem Vk_ne (k : ℕ) : Vk k ≠ [] := by rw [Vk_eq]; simp

theorem Vk_root : ∀ k : ℕ, entry (Vk k) 0 0 = 0
  | 0 => Ys_root
  | (k + 1) => Vs_root (Vk_ne k) (Vk_root k)

theorem Vk_pos : ∀ k : ℕ, ∀ i, 1 ≤ i → i < (Vk k).length → 1 ≤ entry (Vk k) 0 i
  | 0 => Ys_pos
  | (k + 1) => Vs_pos (Vk_ne k) (Vk_pos k)

theorem Bok_Vk (k : ℕ) : Bok (Vk k) := Bok_flat (Flat_Vk k) (Vk_root k)

noncomputable def PwsV (k : ℕ) : Pws Bwx where
  pw j m := owG (ow 1 (k + 1) + ow 0 j) m
  pw_zero j := by rw [owG_zero, bot_BwG]
  pw_add := fun j m => owG_add_same (ow 1 (k + 1) + ow 0 j) m
  pw_ltR := fun j {_ _} h => owG_ltR (ow 1 (k + 1) + ow 0 j) h
  pw_ltL := fun {_ _} h m {_} hm =>
    owG_ltL (Bw_add_lt_left (ow 1 (k + 1)) (ow_ltR 0 h)) m hm
  add_lt := fun b {_ _} h => BwG_add_lt_left b h

theorem pwV_zero_eq (k : ℕ) : (PwsV k).pw 0 = (fun m => owG (ow 1 (k + 1)) m) := by
  funext m
  show owG (ow 1 (k + 1) + ow 0 0) m = _
  rw [ow_zero, bot_Bw, add_zero]

theorem AtLd_Vk : ∀ k : ℕ, AtLd (Vk k) (owG (ow 1 (k + 1)) 1)
  | 0 => AtLd_Ys
  | (k + 1) => by
      have hA0 : AtLd (Vk k) ((PwsV k).pw 0 1) := by
        rw [show (PwsV k).pw 0 1 = owG (ow 1 (k + 1)) 1 from congrFun (pwV_zero_eq k) 1]
        exact AtLd_Vk k
      have hR0 : RunLd (Vk k) ((PwsV k).pw 0) :=
        RunLd_of_TopLd (Bok_Vk k) ((PwsV k).pw_zero 0) ((PwsV k).pw_add 0)
          (TopLd_of_AtLd hA0)
      refine AtLd_Vs (PwsV k) (Flat_Vk k) (Vk_ne k) (Vk_root k) (Vk_pos k)
        hR0 hA0 (fun j => ?_)
      show owG (ow 1 (k + 1) + ow 0 (j + 1)) 1 < owG (ow 1 (k + 1 + 1)) 1
      exact owG_ltL (owG_add_lt (show (0 : ℕ) < 1 by omega) (k + 1) (j + 1)) 1 (by omega)

theorem WPdw_twoVk (k : ℕ) (ks : List Bwy) :
    WPdT (owG (owG (ow 1 (k + 1)) 1) 2 :: ks)
      (Jk1.two Jk1.nil (Jk1.pay Jk1.nil (Vk k))) := by
  refine TopLd_of_AtLd (AtLd_Vk k) Jk1.nil trivial 0 (RunG_nil (0 : Bwx))
    Jk1.nil trivial ⊥ (fun c _ ks' => WPdT_nilAll _) _ ?_ ks
  rw [bot_BwG, zero_add, zero_add]
  exact owG_ltR (owG (ow 1 (k + 1)) 1) (by omega)

def Xv (k : ℕ) : Jk1 := Jk1.two Jk1.nil (Jk1.two Jk1.nil (Jk1.pay Jk1.nil (Vk k)))

theorem WPdw_Xv (k : ℕ) (ks : List Bwy) : WPdT ((⊥ : Bwy) :: ks) (Xv k) :=
  WPdT_twoOf (b := owG (owG (ow 1 (k + 1)) 1) 2)
    (ne_bot_of_gt (owG_pos_succ (owG (ow 1 (k + 1)) 1) 1)) trivial
    (fun q _ => WPdT_nilAll _) (WPdw_twoVk k ks)

theorem GOK_oneXv (k : ℕ) : GOK (Jk1.one Jk1.nil (Xv k)) :=
  (WPdT_bnil (Bud := Bwy) _).mp
    (WPdT_step ([] : List Bwy) (JkT_nil : FrmNT ([] : List Bwy) Jk1.nil)
      ((WPdT_bnil (Bud := Bwy) _).mpr GOK_nil) (WPdw_Xv k []))

theorem shift_Vk (k l : ℕ) : shiftr01 (l + 1) 0 (Vk k)
    = ((l + 1, 0, 0) : ℕ × ℕ × ℕ) :: (List.range (k + 1)).flatMap
        (fun _ => [((l + 2, 0, 0) : ℕ × ℕ × ℕ), ((l + 3, 0, 0) : ℕ × ℕ × ℕ)]) := by
  rw [Vk_eq]
  show List.map (fun p : ℕ × ℕ × ℕ => (p.1 + (l + 1), p.2.1 + 0, p.2.2))
      (((0, 0, 0) : ℕ × ℕ × ℕ) :: _) = _
  rw [List.map_cons, List.map_flatMap]
  refine congrArg₂ List.cons ?_ (congrArg (fun g => List.flatMap g (List.range (k + 1))) ?_)
  · show ((0 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ)) = _
    rw [Nat.zero_add, Nat.zero_add]
  · funext _
    show [((1 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ)),
      ((2 + (l + 1) : ℕ), (0 + 0 : ℕ), (0 : ℕ))] = _
    simp only [Nat.zero_add, show (1 : ℕ) + (l + 1) = l + 2 from by omega,
      show (2 : ℕ) + (l + 1) = l + 3 from by omega]

theorem jk1_Xv (k l : ℕ) : jk1 l (Xv k)
    = ((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: ((l + 2, 2, 0) : ℕ × ℕ × ℕ)
      :: ((l + 3, 0, 0) : ℕ × ℕ × ℕ)
      :: (List.range (k + 1)).flatMap
          (fun _ => [((l + 4, 0, 0) : ℕ × ℕ × ℕ), ((l + 5, 0, 0) : ℕ × ℕ × ℕ)]) := by
  show jk1 l Jk1.nil ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) ::
      (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ)
        :: jk1 (l + 2) (Jk1.pay Jk1.nil (Vk k))))) = _
  rw [show jk1 (l + 2) (Jk1.pay Jk1.nil (Vk k)) = shiftr01 (l + 2 + 1) 0 (Vk k) from by
      show jk1 (l + 2) Jk1.nil ++ _ = _; simp [jk1],
    show l + 2 + 1 = l + 3 from by omega, shift_Vk k (l + 2),
    show l + 2 + 1 = l + 3 from by omega, show l + 2 + 2 = l + 4 from by omega,
    show l + 2 + 3 = l + 5 from by omega]
  simp [jk1]

theorem R600_78rep_mem : ∀ n : ℕ,
    R600 ++ (List.range n).flatMap
      (fun _ => [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)]) ∈ W 0
  | 0 => by simpa using Aok_R600.mem
  | (k + 1) => by
      have hG : GoodFb (fun a b => wordJ a b [Jk1.one Jk1.nil (Xv k)]) := by
        simpa using GOK_oneXv k [] WOk_nil GoodFb_wordJ_nil
      have hh := rowJ_mem_genF Aok_R338 hG
      have e : jk1 2 (Jk1.one Jk1.nil (Xv k))
          = ((3, 1, 0) : ℕ × ℕ × ℕ) :: ((4, 2, 0) : ℕ × ℕ × ℕ) :: ((5, 2, 0) : ℕ × ℕ × ℕ)
            :: ((6, 0, 0) : ℕ × ℕ × ℕ)
            :: (List.range (k + 1)).flatMap (fun _ => [((7, 0, 0) : ℕ × ℕ × ℕ),
                ((8, 0, 0) : ℕ × ℕ × ℕ)]) := by
        show jk1 2 Jk1.nil ++ (((2 + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (2 + 1) (Xv k)) = _
        rw [jk1_Xv k 3]
        simp [jk1]
      rw [wordJ_singleton, colJ, e] at hh
      simpa [R600, R375m, R373, R344, R341, R338, List.append_assoc] using hh

/-- ★★★★★★★★★★★★ `R600 (7,0,0)(8,0,0)(8,0,0)`。 -/
theorem R600_788_mem :
    R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ),
      ((8, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hne : [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)] ≠ [] := by simp
  have hhead : entry [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)] 0 0 < 8 := by
    simp [entry]
  have htail : ∀ r, 1 ≤ r →
      r < ([((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq).length →
      8 ≤ entry [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)] 0 r := by
    intro r h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    rcases r with _ | _ | r
    · omega
    · simp [entry]
    · omega
  have hmem := flat_mem'' (Y0 := R600)
    (M := [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)]) (d := 8)
    hne hhead htail R600_78rep_mem
  simpa [List.append_assoc] using hmem

#print axioms AtLd_Vk
#print axioms R600_788_mem

/-- 新しい台座 `R600 (7,0,0)(8,0,0)(8,0,0)`。 -/
def Z788 : TrioSeq :=
  R600 ++ [((7, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ), ((8, 0, 0) : ℕ × ℕ × ℕ)]

theorem Z788_eq : Z788 = [((0, 0, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ),
    ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((1, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ),
    ((5, 2, 0) : ℕ × ℕ × ℕ),
    ((6, 0, 0) : ℕ × ℕ × ℕ),
    ((7, 0, 0) : ℕ × ℕ × ℕ),
    ((8, 0, 0) : ℕ × ℕ × ℕ),
    ((8, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [Z788, R600, R375m, R373, R344, R341, R338]

theorem Z788_ne : Z788 ≠ [] := by rw [Z788_eq]; simp

theorem Z788_head : entry Z788 0 0 = 0 := by rw [Z788_eq]; simp [entry]

theorem Z788_tail : ∀ r, 1 ≤ r → r < Z788.length → 1 ≤ entry Z788 0 r := by
  intro r hr1 hrl
  rw [Z788_eq] at hrl ⊢
  simp only [List.length_cons, List.length_nil] at hrl
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r <;>
    first
      | omega
      | simp [entry]

theorem Aok_Z788 : Aok Z788 where
  mem := R600_788_mem
  ne := Z788_ne
  deep := ⟨Z788_head, Z788_tail⟩
  zroot := by
    rw [Z788_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> decide
  mono := by
    rw [Z788_eq]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> decide

/-- ★★★★★★★★★★★★ 新しい台座の上、輪を `n` 周した 4 パラメータの無限族。 -/
theorem LoopIt_Z788_mem (m : ℕ) {ws : List Jk1} (hw : WJ ws) (j n : ℕ) :
    LoopIt Z788 m ws j n ∈ W 0 := (Aok_LoopIt Aok_Z788 m hw j n).mem

theorem LoopIt_Z788_nil_mem (m p j n : ℕ) :
    LoopIt Z788 m (List.replicate p (AltT 0)) j n ∈ W 0 :=
  LoopIt_Z788_mem m (WJ_rep_AltT 0 p) j n

#print axioms LoopIt_Z788_nil_mem

/-! ### 台座 `Z788` の上に `hang6_gen` で任意の `Bok` 荷を高さ 6 に吊るす

`hang6_gen` は `A ++ U375a1 ++ shiftr01 6 0 B`（`U375a1` の末尾 `(5,1,0)` が
`one` の枠を作るので荷が自由）。`A` に `LoopIt Z788 …` を入れても効く。 -/

theorem Z788_hang6 {B : TrioSeq} (hB : Bok B) :
    Z788 ++ U375a1 ++ shiftr01 6 0 B ∈ W 0 := hang6_gen Aok_Z788 hB

theorem Z788_hang6_LoopIt (m : ℕ) {ws : List Jk1} (hw : WJ ws) (j n : ℕ) :
    Z788 ++ U375a1 ++ shiftr01 6 0 (LoopIt Z788 m ws j n) ∈ W 0 :=
  hang6_gen Aok_Z788 (Aok_LoopIt Aok_Z788 m hw j n).toBok

theorem Z788_hang6_LoopIt_nil (m p j n : ℕ) :
    Z788 ++ U375a1 ++ shiftr01 6 0 (LoopIt Z788 m (List.replicate p (AltT 0)) j n)
      ∈ W 0 :=
  Z788_hang6_LoopIt m (WJ_rep_AltT 0 p) j n

#print axioms Z788_hang6_LoopIt_nil


end Small
end TRIO
