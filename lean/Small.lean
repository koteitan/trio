/-
Small.lean: `SmallA.lean` の続き。

ビルド時間を短くするため、安定した部分を `SmallA.lean` に分けた。
このファイルには新しく足す定理だけを書く。大きくなったらまた分ける。
-/
import SmallA

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

end EntS

end Small
end TRIO
