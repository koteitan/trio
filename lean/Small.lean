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

end Small
end TRIO
