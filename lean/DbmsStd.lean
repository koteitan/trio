/-
**像が DBMS 標準形であること** — `ST_PS M → ST_D (conC M)` の証明。

`Dbms.lean` で
  `conC` が読み `translate` を保ち（`readC_conC_ST`）、順序を保ち単射である
ことは済んでいる。残るのは「像が DBMS の標準形であること」だった。

## 道

素朴には `ST_PS` の帰納法（底 = 対角、段 = `conC (M⟦n⟧)`）だが、段が 1 手では
つながらない。`conC (M⟦n⟧)` が `conC M` の**基本列の項そのもの**になるとは限らず、
実測では 1〜7 手かかる（`tools/dbms/steps` 参照）。

そこで**対角からの降下**に切り替える。降下が像の外へ出ないこと、および降下の
停止性は、どちらも BMS 側の既証明（`pss_cofinality_holds`, `wf_olt_ST_PS_holds`）
から来る。要になるのは 1 つだけ:

    ReindexD : 像の基本列は BMS の基本列と絡み合う
               `(conC A)⟦m⟧ = conC (A⟦n'⟧)` かつ `A⟦n⟧ ≤ A⟦n'⟧`

これは `tools/dbms/reindex.py` が全数検査している式

    (conC A)⟦m⟧ = conC (A⟦g(A,m)⟧)

の帰結で、`g` の regime は 4 つしかない（BMS 標準形 44653 個 = ≤8 列、違反 0）:

    succ  : A の末尾列 = (0,0)      → g(m) = 0     （両側とも後続）
    id    : それ以外の大多数        → g(m) = m     （基本列が一致）
    shift : A の末尾列 = (1,1)      → g(m) = m + 1 （DBMS 側が 1 つ飛ばす）
    contr : 末尾で縮約が効いた場合   → g(m) = m - 1 （梯子の二役で 1 つずれる）

本ファイルは `ReindexD` を**仮定**として、そこから標準形性を完全に導く。
`Pair/ArgDom.lean` の `ArgDomCore` と同じ「要を 1 つの `Prop` に括り出す」流儀。

regime のうち **succ は証明済み**（`reindexD_succ`）:

    conC (M ++ [(0,0)]) = conC M ++ [(0,0)]        … convC_snoc_zero
    (M ++ [(0,0)])⟦n⟧   = M                        … oper_snoc_zero
    ⟹ (conC (M ++ [(0,0)]))⟦m⟧ = conC ((M ++ [(0,0)])⟦n⟧)   （m, n によらない）
       ⟹ ReindexD の形（m = 1, n' = n）

残るは id / shift / contr の 3 つ。
-/
import Dbms
import Pair.Final

namespace DBMS

open YAPSS Three

/-! ## 0. `≤o` の推移律 -/

theorem ole_refl (x : Three) : x ≤o x := Or.inr rfl

theorem ole_trans {x y z : Three} (hxy : x ≤o y) (hyz : y ≤o z) : x ≤o z := by
  rcases hxy with h | rfl
  · exact Or.inl (olt_ole_trans h hyz)
  · exact hyz

theorem ole_olt_trans {x y z : Three} (hxy : x ≤o y) (hyz : y <o z) : x <o z := by
  rcases hxy with h | rfl
  · exact olt_trans h hyz
  · exact hyz

/-! ## 1. 長さ 1 の標準形は最小 -/

/-- `[(0,0)]` より真に小さい標準形はない。 -/
theorem not_olt_len_one {M A : PairSeq} (hM : ST_PS M) (hA : A.length ≤ 1)
    (hAst : ST_PS A) (h : translate M <o translate A) : False := by
  have h1 : A = [(0, 0)] := Wset.stps_len_one hAst (by
    have := stps_len_pos hAst; omega)
  subst h1
  have hA0 : translate [((0 : ℕ), (0 : ℕ))] = P 0 Z Z := by
    rw [translate]; simp
  have hMne : M ≠ [] := Wset.stps_ne_nil hM
  match M, hMne with
  | p :: R, _ =>
    rw [hA0, translate] at h
    rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩
    · omega
    · exact not_olt_Z _ h
    · exact not_olt_Z _ h

/-! ## 2. 対角は標準形の中で共終 -/

/-- どの標準形も、ある BMS 対角以下。 -/
theorem diag_cofinal {M : PairSeq} (hM : ST_PS M) :
    ∃ v, translate M ≤o translate (diagSeq 0 v) := by
  induction hM with
  | diag v => exact ⟨v, ole_refl _⟩
  | @oper N n hN hn ih =>
      obtain ⟨v, hv⟩ := ih
      by_cases hL : 1 < N.length
      · exact ⟨v, ole_trans (Or.inl (m_step_decreases hL hn)) hv⟩
      · have : N⟦n⟧ = N := oper_eq_self_short n (by omega)
        rw [this]; exact ⟨v, hv⟩

/-! ## 2.5 succ regime — 末尾が `(0,0)` のとき -/

/-- 末尾に `(0,0)` を足しても、ユニットの本数は変わらない。 -/
theorem unitsLen_snoc {p c : ℕ × ℕ} (hc : ¬ (p.1 < c.1)) (hcp : ¬ (c = p)) :
    ∀ (n : ℕ) (B : PairSeq), B.length ≤ n → unitsLen p (B ++ [c]) = unitsLen p B := by
  intro n
  induction n with
  | zero =>
    intro B hB
    have : B = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [List.nil_append]
    rw [unitsLen_cons_neg hcp, unitsLen]
  | succ n ih =>
    intro B hB
    match B with
    | [] =>
      simp only [List.nil_append]
      rw [unitsLen_cons_neg hcp, unitsLen]
    | b :: r =>
      by_cases h : b = p
      · subst h
        obtain ⟨e1, e2⟩ := split_append_gen (dd := b.1) (Y := [c]) (Or.inr (by simpa using hc)) r
        have hlen : (r.dropWhile fun x => b.1 < x.1).length ≤ n := by
          have := List.length_dropWhile_le (fun x : ℕ × ℕ => b.1 < x.1) r
          simp only [List.length_cons] at hB; omega
        rw [List.cons_append, unitsLen_cons_pos, unitsLen_cons_pos, e1, e2,
          ih _ hlen]
      · rw [List.cons_append, unitsLen_cons_neg h, unitsLen_cons_neg h]

/-- 末尾に `(0,0)` を足しても、縮約の判定は（外の後続に `(0,0)` が付くだけで）変わらない。 -/
theorem contrLen_snoc {p : ℕ × ℕ} {B A : PairSeq} {k : ℕ}
    (hk : k = unitsLen p B) (hkle : k ≤ B.length) (hp1 : 0 < p.2) (hpc : p.2 ≤ p.1) :
    (contrLen p (B ++ [((0, 0) : ℕ × ℕ)]) k A
      = match contrLen p B k A with
        | none => none
        | some (rest2, Bq) => some (rest2, Bq ++ [((0, 0) : ℕ × ℕ)])) := by
  by_cases hlt : k < B.length
  · -- `B.drop k` は空でない
    have hdne : B.drop k ≠ [] := by
      intro he
      have := List.length_drop (l := B) (i := k)
      rw [he] at this
      simp at this
      omega
    match hde : B.drop k with
    | [] => exact absurd hde hdne
    | q :: r2 =>
      have hdrop : (B ++ [((0, 0) : ℕ × ℕ)]).drop k = q :: (r2 ++ [((0, 0) : ℕ × ℕ)]) := by
        rw [List.drop_append_of_le_length (by omega), hde, List.cons_append]
      obtain ⟨e1, e2⟩ := split_append_gen (dd := q.1) (Y := [((0, 0) : ℕ × ℕ)])
        (Or.inr (by simp)) r2
      have htake : (B ++ [((0, 0) : ℕ × ℕ)]).take k = B.take k :=
        List.take_append_of_le_length (by omega)
      unfold contrLen
      rw [hdrop, hde, htake]
      simp only [e1, e2]
      split
      · rfl
      · rfl
  · -- ユニットが `B` を使い切っている: `q = (0,0)` になるので発火しない
    have hkeq : k = B.length := by omega
    have hde : B.drop k = [] := by rw [hkeq]; simp
    have hdrop : (B ++ [((0, 0) : ℕ × ℕ)]).drop k = [((0, 0) : ℕ × ℕ)] := by
      rw [hkeq, List.drop_left]
    have hnone : contrLen p B k A = none := by unfold contrLen; rw [hde]
    rw [hnone]
    unfold contrLen
    rw [hdrop]
    simp only
    refine if_neg ?_
    rintro ⟨h1, h2, -⟩
    omega

/-- 末尾の `(0,0)` は変換でも末尾の `(0,0)` になる（深さは `d`）。 -/
theorem convC_snoc_zero : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n → colOK M →
    ∀ (d plev : ℕ) (first force : Bool),
      convC (M ++ [((0, 0) : ℕ × ℕ)]) d plev first force
        = convC M d plev first force ++ [((d, 0) : ℕ × ℕ)] := by
  intro n
  induction n with
  | zero =>
    intro M hM _ d plev first force
    have : M = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [List.nil_append, convC_nil]
    rw [convC_cons_nolad ((0, 0) : ℕ × ℕ) [] d plev first force (by simp [ladOf])]
    have : ddOf ((0, 0) : ℕ × ℕ).2 d plev first force = d := by
      unfold ddOf
      rw [if_neg (by simp [ladOf]), if_neg (by simp)]
    rw [this]
    simp
  | succ n ih =>
    intro M hM hc d plev first force
    match M with
    | [] =>
      simp only [List.nil_append, convC_nil]
      rw [convC_cons_nolad ((0, 0) : ℕ × ℕ) [] d plev first force (by simp [ladOf])]
      have : ddOf ((0, 0) : ℕ × ℕ).2 d plev first force = d := by
        unfold ddOf
        rw [if_neg (by simp [ladOf]), if_neg (by simp)]
      rw [this]
      simp
    | p :: r =>
      obtain ⟨e1, e2⟩ := split_append_gen (dd := p.1) (Y := [((0, 0) : ℕ × ℕ)])
        (Or.inr (by simp)) r
      have hlB : (r.dropWhile fun q => p.1 < q.1).length ≤ n := by
        have := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) r
        simp only [List.length_cons] at hM; omega
      have hcB : colOK (r.dropWhile fun q => p.1 < q.1) := fun c hcm =>
        hc c (List.mem_cons_of_mem _ ((List.dropWhile_sublist _).subset hcm))
      have hpc : p.2 ≤ p.1 := hc p (by simp)
      by_cases hl : ladOf p.2 d plev first force = true
      · have hp1 : 0 < p.2 := by
          have : p.2 = plev + 1 := by simp [ladOf] at hl; omega
          omega
        have hune : unitsLen p ((r.dropWhile fun q => p.1 < q.1) ++ [((0, 0) : ℕ × ℕ)])
            = unitsLen p (r.dropWhile fun q => p.1 < q.1) :=
          unitsLen_snoc (by simp) (by intro he; rw [← he] at hp1; simp at hp1)
            (r.dropWhile fun q => p.1 < q.1).length _ (Nat.le_refl _)
        have hkle : unitsLen p (r.dropWhile fun q => p.1 < q.1)
            ≤ (r.dropWhile fun q => p.1 < q.1).length :=
          unitsLen_le p _ _ (Nat.le_refl _)
        have hcs := contrLen_snoc (p := p) (B := r.dropWhile fun q => p.1 < q.1)
          (A := r.takeWhile fun q => p.1 < q.1)
          (k := unitsLen p (r.dropWhile fun q => p.1 < q.1)) rfl hkle hp1 hpc
        rcases hcc : contrLen p (r.dropWhile fun q => p.1 < q.1)
            (unitsLen p (r.dropWhile fun q => p.1 < q.1))
            (r.takeWhile fun q => p.1 < q.1) with _ | ⟨rest2, Bq⟩
        · -- 縮約なし
          rw [convC_cons_lad_none p r d plev first force hl hcc]
          rw [List.cons_append,
            convC_cons_lad_none p (r ++ [((0, 0) : ℕ × ℕ)]) d plev first force hl (by
              rw [e1, e2, hune, hcs, hcc])]
          rw [e1, e2, ih _ hlB hcB d p.2 false false]
          simp [List.append_assoc]
        · -- 縮約あり
          have hlbq : Bq.length ≤ n := by
            have := (contrLen_lt hcc).2
            have h2 := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) r
            simp only [List.length_cons] at hM
            omega
          have hcbq : colOK Bq := fun c hcm =>
            hcB c ((contrLen_sublists hcc).2.subset hcm)
          rw [convC_cons_lad_some p r d plev first force hl hcc]
          rw [List.cons_append,
            convC_cons_lad_some p (r ++ [((0, 0) : ℕ × ℕ)]) d plev first force hl (by
              rw [e1, e2, hune, hcs, hcc])]
          have htk : ((r.dropWhile fun q => p.1 < q.1) ++ [((0, 0) : ℕ × ℕ)]).take
                (unitsLen p (r.dropWhile fun q => p.1 < q.1))
              = (r.dropWhile fun q => p.1 < q.1).take
                (unitsLen p (r.dropWhile fun q => p.1 < q.1)) :=
            List.take_append_of_le_length hkle
          rw [e1, e2, hune, htk, ih Bq hlbq hcbq d p.2 false false]
          simp [List.append_assoc]
      · rw [convC_cons_nolad p r d plev first force (by simpa using hl)]
        rw [List.cons_append,
          convC_cons_nolad p (r ++ [((0, 0) : ℕ × ℕ)]) d plev first force (by simpa using hl)]
        rw [e1, e2, ih _ hlB hcB d p.2 false false]
        simp [List.append_assoc]

/-- 末尾が `(0,0)` の列は、どの `n` でも末尾を落とすだけ。 -/
theorem oper_snoc_zero {M : PairSeq} (hM : M ≠ []) (n : ℕ) :
    (M ++ [((0, 0) : ℕ × ℕ)])⟦n⟧ = M := by
  have hlen : (M ++ [((0, 0) : ℕ × ℕ)]).length = M.length + 1 := by simp
  have hpos : 0 < M.length := List.length_pos_of_ne_nil hM
  have hL : (M ++ [((0, 0) : ℕ × ℕ)]).length - 1 ≠ 0 := by omega
  have hidx : (M ++ [((0, 0) : ℕ × ℕ)]).length - 1 = M.length := by omega
  have hget : (M ++ [((0, 0) : ℕ × ℕ)]).getD ((M ++ [((0, 0) : ℕ × ℕ)]).length - 1) (0, 0)
      = ((0, 0) : ℕ × ℕ) := by
    rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp
  have hz : entry (M ++ [((0, 0) : ℕ × ℕ)]) 0 ((M ++ [((0, 0) : ℕ × ℕ)]).length - 1) = 0 ∧
      entry (M ++ [((0, 0) : ℕ × ℕ)]) 1 ((M ++ [((0, 0) : ℕ × ℕ)]).length - 1) = 0 := by
    constructor
    · rw [entry, if_pos rfl, hget]
    · rw [entry, if_neg (by omega), hget]
  rw [oper_eq_pred_of_zero n hL hz, Pred, if_neg (by omega)]
  simp

/-- **succ regime**: 末尾が `(0,0)` なら、両側とも「末尾を落とす」で一致する。 -/
theorem reindexD_succ {M : PairSeq} (hM : M ≠ []) (hc : colOK M) (m n : ℕ) :
    (conC (M ++ [((0, 0) : ℕ × ℕ)]))⟦m⟧ = conC ((M ++ [((0, 0) : ℕ × ℕ)])⟦n⟧) := by
  have hsnoc : conC (M ++ [((0, 0) : ℕ × ℕ)]) = conC M ++ [((0, 0) : ℕ × ℕ)] := by
    rw [conC, conC]
    exact convC_snoc_zero M.length M (Nat.le_refl _) hc 0 0 true false
  have hCne : conC M ≠ [] := by
    rw [conC, ne_eq, convC_eq_nil_iff]
    exact hM
  rw [hsnoc, oper_snoc_zero hCne m, oper_snoc_zero hM n]

/-- succ regime は `ReindexD` の形（`m = 1`, `n' = n`）を満たす。 -/
theorem reindexD_succ_shape {M : PairSeq} (hM : M ≠ []) (hc : colOK M) (n : ℕ) :
    ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (conC (M ++ [((0, 0) : ℕ × ℕ)]))⟦m⟧ = conC ((M ++ [((0, 0) : ℕ × ℕ)])⟦n'⟧) :=
  ⟨1, n, Nat.le_refl 1, Nat.le_refl n, reindexD_succ hM hc 1 n⟩

/-! ## 2.7 変換は末尾列の段を保つ -/

/-- 末尾が空でない `++` の `getLastD`。空なら左側。 -/
theorem getLastD_append_cases {A B : PairSeq} (dflt : ℕ × ℕ) :
    (A ++ B).getLastD dflt = if B = [] then A.getLastD dflt else B.getLastD dflt := by
  by_cases h : B = []
  · rw [if_pos h, h]; simp
  · rw [if_neg h]; exact getLastD_append_right h dflt

/-- **変換は末尾列の段を保つ。** これで `idx1` が両側で一致する。 -/
theorem convC_getLast_level : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n →
    ∀ (d plev : ℕ) (first force : Bool),
      ((convC M d plev first force).getLastD (0, 0)).2 = (M.getLastD (0, 0)).2 := by
  intro n
  induction n with
  | zero =>
    intro M hM d plev first force
    have : M = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [convC_nil]
  | succ n ih =>
    intro M hM d plev first force
    match M with
    | [] => rw [convC_nil]
    | p :: r =>
      set A := r.takeWhile (fun q => p.1 < q.1) with hA
      set B := r.dropWhile (fun q => p.1 < q.1) with hB
      have hAB : r = A ++ B := by rw [hA, hB, List.takeWhile_append_dropWhile]
      have hlA : A.length ≤ n := by
        have := (List.takeWhile_sublist (fun q : ℕ × ℕ => p.1 < q.1) (l := r)).length_le
        simp only [List.length_cons] at hM; rw [hA]; omega
      have hlB : B.length ≤ n := by
        have := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) r
        simp only [List.length_cons] at hM; rw [hB]; omega
      have hMlast : ((p :: r).getLastD (0, 0)).2
          = (if B = [] then (if A = [] then p else A.getLastD (0, 0)) else B.getLastD (0, 0)).2 := by
        rw [hAB]
        by_cases hBe : B = []
        · rw [hBe]
          simp only [List.append_nil, if_pos rfl]
          by_cases hAe : A = []
          · rw [hAe, if_pos rfl]; simp
          · rw [if_neg hAe, List.getLastD_cons]
            exact congrArg Prod.snd (getLastD_ne_nil_indep hAe _ _)
        · rw [if_neg hBe, List.getLastD_cons, getLastD_append_right hBe]
          exact congrArg Prod.snd (getLastD_ne_nil_indep hBe _ _)
      have key : ∀ (cs : PairSeq) (dA dB : ℕ) (fA fB gA gB : Bool),
          cs ≠ [] → (cs.getLastD (0, 0)).2 = p.2 →
          ((cs ++ (convC A dA p.2 fA gA ++ convC B dB p.2 fB gB)).getLastD (0, 0)).2
            = ((p :: r).getLastD (0, 0)).2 := by
        intro cs dA dB fA fB gA gB hcs hcsl
        rw [hMlast]
        by_cases hBe : B = []
        · rw [if_pos hBe, hBe, convC_nil, List.append_nil]
          by_cases hAe : A = []
          · rw [if_pos hAe, hAe, convC_nil, List.append_nil]
            exact hcsl
          · rw [if_neg hAe, getLastD_append_cases,
              if_neg (by simp only [convC_eq_nil_iff]; exact hAe)]
            exact ih A hlA dA p.2 fA gA
        · rw [if_neg hBe, ← List.append_assoc, getLastD_append_cases,
            if_neg (by simp only [convC_eq_nil_iff]; exact hBe)]
          exact ih B hlB dB p.2 fB gB
      by_cases hl : ladOf p.2 d plev first force = true
      · rcases hcc : contrLen p B (unitsLen p B) A with _ | ⟨rest2, Bq⟩
        · rw [convC_cons_lad_none p r d plev first force hl (by rw [← hA, ← hB]; exact hcc)]
          rw [← hA, ← hB, ← List.cons_append, ← List.cons_append]
          exact key [(d, plev), (d + 1, p.2)] (d + 2) d true false false false
            (by simp) (by simp)
        · -- 縮約あり: 末尾は `convC Bq`（空なら `convC rest2`）
          obtain ⟨q, r2, hdq, hq2, hq1, hAq, hBq, hr2ne, hr2d, hr2l⟩ := contrLen_spec hcc
          have hlr2 : rest2.length ≤ n := by
            have := (contrLen_lt hcc).1; omega
          have hlbq : Bq.length ≤ n := by
            have := (contrLen_lt hcc).2; omega
          have hBne : B ≠ [] := by
            intro he
            rw [he] at hdq
            simp at hdq
          -- 入力側の末尾
          have hlast : ((p :: r).getLastD (0, 0)).2
              = (if Bq = [] then rest2.getLastD (0, 0) else Bq.getLastD (0, 0)).2 := by
            rw [hMlast, if_neg hBne]
            have hBsplit : B = B.take (unitsLen p B) ++ (q :: r2) := by
              rw [← hdq, List.take_append_drop]
            have hr2split : r2 = (contrPre p (B.take (unitsLen p B)) A ++ rest2) ++ Bq := by
              conv_lhs => rw [← List.takeWhile_append_dropWhile
                (p := fun x : ℕ × ℕ => decide (q.1 < x.1)) (l := r2)]
              rw [hAq, hBq]
            have hqr2ne : (q :: r2) ≠ [] := by simp
            rw [hBsplit, getLastD_append_right hqr2ne, List.getLastD_cons]
            have hr2ne' : r2 ≠ [] := by
              intro he
              rw [he] at hr2split
              have : (contrPre p (B.take (unitsLen p B)) A ++ rest2) ++ Bq = [] := hr2split.symm
              simp only [List.append_eq_nil_iff] at this
              exact hr2ne this.1.2
            rw [getLastD_ne_nil_indep hr2ne' _ (0, 0), hr2split, getLastD_append_cases]
            by_cases hbq : Bq = []
            · rw [if_pos hbq, if_pos hbq, getLastD_append_right hr2ne]
            · rw [if_neg hbq, if_neg hbq]
          rw [convC_cons_lad_some p r d plev first force hl (by rw [← hA, ← hB]; exact hcc)]
          rw [← hA, ← hB, hlast]
          by_cases hbq : Bq = []
          · rw [if_pos hbq, hbq, convC_nil, List.append_nil]
            simp only [← List.cons_append, ← List.append_assoc]
            rw [getLastD_append_cases,
              if_neg (by simp only [convC_eq_nil_iff]; exact hr2ne)]
            exact ih rest2 hlr2 (d + 1) p.2 false false
          · rw [if_neg hbq]
            simp only [← List.cons_append, ← List.append_assoc]
            rw [getLastD_append_cases,
              if_neg (by simp only [convC_eq_nil_iff]; exact hbq)]
            exact ih Bq hlbq d p.2 false false
      · rw [convC_cons_nolad p r d plev first force (by simpa using hl)]
        rw [← hA, ← hB, ← List.cons_append]
        exact key [(ddOf p.2 d plev first force, p.2)]
          (ddOf p.2 d plev first force + 1) d true false (first && (p.2 == plev)) false
          (by simp) (by simp)

/-- 変換は末尾列の段を保つ（入口）。 -/
theorem conC_getLast_level (M : PairSeq) :
    ((conC M).getLastD (0, 0)).2 = (M.getLastD (0, 0)).2 :=
  convC_getLast_level M.length M (Nat.le_refl _) 0 0 true false

/-- 末尾の `entry` は `getLastD`。 -/
theorem entry_last {M : PairSeq} : entry M 1 (M.length - 1) = (M.getLastD (0, 0)).2 := by
  rw [entry, if_neg (by omega), getLastD_eq_getD]

theorem entry_last0 {M : PairSeq} : entry M 0 (M.length - 1) = (M.getLastD (0, 0)).1 := by
  rw [entry, if_pos rfl, getLastD_eq_getD]

theorem entry_zero0 {M : PairSeq} : entry M 0 0 = (M.headI).1 := by
  rw [entry, if_pos rfl]
  cases M with
  | nil => rfl
  | cons a t => rfl

/-- **`idx1` は両側で一致する。** `oper` がどちらの行で親を探すかが同じになる。 -/
theorem idx1_conC (M : PairSeq) :
    idx1 (conC M) ((conC M).length - 1) = idx1 M (M.length - 1) := by
  rw [idx1, idx1, entry_last, entry_last, conC_getLast_level]

/-! ## 2.75 長さ -/

theorem getLastD_mem {l : PairSeq} (h : l ≠ []) (dflt : ℕ × ℕ) : l.getLastD dflt ∈ l := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast (h := h)]
  simpa using List.getLast_mem h

/-- 2 列以上なら像も 2 列以上。 -/
theorem convC_length_ge_two {M : PairSeq} (h : 1 < M.length) (d plev : ℕ) (first force : Bool) :
    1 < (convC M d plev first force).length := by
  match M with
  | [] => simp at h
  | p :: r =>
    have hr : r ≠ [] := by
      intro he; rw [he] at h; simp at h
    have hAB : (r.takeWhile fun q => p.1 < q.1) ++ (r.dropWhile fun q => p.1 < q.1) = r :=
      List.takeWhile_append_dropWhile
    have hne : convC (r.takeWhile fun q => p.1 < q.1) (ddOf p.2 d plev first force + 1) p.2 true
          (first && (p.2 == plev))
        ++ convC (r.dropWhile fun q => p.1 < q.1) d p.2 false false ≠ [] := by
      intro he
      obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.1 he
      rw [convC_eq_nil_iff] at h1 h2
      rw [← hAB, h1, h2] at hr
      simp at hr
    by_cases hl : ladOf p.2 d plev first force = true
    · rcases hcc : contrLen p (r.dropWhile fun q => p.1 < q.1)
          (unitsLen p (r.dropWhile fun q => p.1 < q.1))
          (r.takeWhile fun q => p.1 < q.1) with _ | ⟨rest2, Bq⟩
      · rw [convC_cons_lad_none p r d plev first force hl hcc]
        simp only [List.length_cons]
        omega
      · rw [convC_cons_lad_some p r d plev first force hl hcc]
        simp only [List.length_cons]
        omega
    · rw [convC_cons_nolad p r d plev first force (by simpa using hl)]
      simp only [List.length_cons]
      have hpos := List.length_pos_of_ne_nil hne
      omega

/-- `conC` の像も 2 列以上。 -/
theorem conC_length_ge_two {M : PairSeq} (h : 1 < M.length) : 1 < (conC M).length :=
  convC_length_ge_two h 0 0 true false

/-! ## 2.76 兄弟の並び（コピーが素直な繰り返しになる場合） -/

/-- `first = false` の変換は親の段にも `force` にも依らない。 -/
theorem convC_plev : ∀ (n : ℕ) (L : PairSeq), L.length ≤ n → ∀ (d plev plev' : ℕ)
    (force force' : Bool),
    convC L d plev false force = convC L d plev' false force' := by
  intro n
  induction n with
  | zero =>
    intro L hL d plev plev' force force'
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [convC_nil, convC_nil]
  | succ n ih =>
    intro L hL d plev plev' force force'
    match L with
    | [] => rw [convC_nil, convC_nil]
    | p :: r =>
      have hnl : ∀ pv : ℕ, ∀ fo : Bool, ladOf p.2 d pv false fo = false := by
        intro pv fo; simp [ladOf]
      have hdd : ∀ pv : ℕ, ∀ fo : Bool, ddOf p.2 d pv false fo = ddOf p.2 d plev false force := by
        intro pv fo
        simp only [ddOf, hnl, Bool.false_eq_true, if_false]
      rw [convC_cons_nolad p r d plev false force (hnl plev force),
        convC_cons_nolad p r d plev' false force' (hnl plev' force')]
      rw [hdd plev' force']
      simp only [Bool.false_and]

/-- 同じブロックを `n` 本並べたあとに `rest` が続くとき、変換も同じ塊を `n` 本出す。 -/
theorem convC_run (p : ℕ × ℕ) (R rest : PairSeq) (hR : ∀ c ∈ R, p.1 < c.1)
    (hrest : rest = [] ∨ ¬ (p.1 < (rest.headI).1)) (d plev : ℕ) :
    ∀ n : ℕ, convC ((List.replicate n (p :: R)).flatten ++ rest) d plev false false
        = (List.replicate n ((ddOf p.2 d plev false false, p.2) ::
             convC R (ddOf p.2 d plev false false + 1) p.2 true false)).flatten
          ++ convC rest d plev false false := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hhd : ((List.replicate n (p :: R)).flatten ++ rest) = [] ∨
        ¬ (p.1 < (((List.replicate n (p :: R)).flatten ++ rest).headI).1) := by
      cases n with
      | zero => simpa using hrest
      | succ n' =>
        right
        rw [List.replicate_succ, List.flatten_cons, List.append_assoc, List.cons_append]
        simp
    obtain ⟨e1, e2⟩ := split_append (dd := p.1) hR hhd
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc, List.cons_append,
      convC_cons_nolad p (R ++ ((List.replicate n (p :: R)).flatten ++ rest)) d plev false false
        (by simp [ladOf]),
      e1, e2]
    simp only [Bool.false_and]
    rw [convC_plev ((List.replicate n (p :: R)).flatten ++ rest).length _ (Nat.le_refl _)
        d p.2 plev false false,
      ih, List.replicate_succ, List.flatten_cons]
    simp [List.append_assoc]

/-- 定数の `flatMap` は `replicate` の `flatten`。 -/
theorem flatMap_const (L : PairSeq) : ∀ n : ℕ,
    (List.range n).flatMap (fun _ => L) = (List.replicate n L).flatten := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ']
    simp

/-- **末尾列の段が 0 なら、基本列はブロックの素直な繰り返し**（`d0 = 0`）。 -/
theorem oper_repeat {M : PairSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1))
    (h0 : idx1 M (M.length - 1) = 0) :
    M⟦n⟧ = M.take (parent M (idx1 M (M.length - 1)) (M.length - 1))
      ++ (List.replicate n
            ((List.range' (parent M (idx1 M (M.length - 1)) (M.length - 1))
              (M.length - 1 - parent M (idx1 M (M.length - 1)) (M.length - 1))).map
              (fun j => ((entry M 0 j : ℕ), (entry M 1 j : ℕ))))).flatten := by
  rw [oper_bad_unfold n hL hz hp, h0]
  simp only [Nat.lt_irrefl, if_false, Nat.mul_zero, Nat.add_zero, h0]
  rw [flatMap_const]

/-- `d ≤ plev + 1` なら `force` は効かない（`d ≤ s` が自動で立つ）。 -/
theorem convC_force {L : PairSeq} {d plev : ℕ} (h : d ≤ plev + 1) (force force' : Bool) :
    convC L d plev true force = convC L d plev true force' := by
  match L with
  | [] => rw [convC_nil, convC_nil]
  | p :: r =>
    have hlad : ladOf p.2 d plev true force = ladOf p.2 d plev true force' := by
      unfold ladOf
      by_cases hs : p.2 = plev + 1
      · have hdp : d ≤ p.2 := by omega
        rw [decide_eq_true hdp]
        simp
      · rw [beq_eq_false_iff_ne.2 hs]
        simp
    have hdd : ddOf p.2 d plev true force = ddOf p.2 d plev true force' := by
      unfold ddOf; rw [hlad]
    by_cases hl : ladOf p.2 d plev true force = true
    · rcases hcc : contrLen p (r.dropWhile fun q => p.1 < q.1)
          (unitsLen p (r.dropWhile fun q => p.1 < q.1))
          (r.takeWhile fun q => p.1 < q.1) with _ | ⟨rest2, Bq⟩
      · rw [convC_cons_lad_none p r d plev true force hl hcc,
          convC_cons_lad_none p r d plev true force' (by rw [← hlad]; exact hl) hcc]
      · rw [convC_cons_lad_some p r d plev true force hl hcc,
          convC_cons_lad_some p r d plev true force' (by rw [← hlad]; exact hl) hcc]
    · rw [convC_cons_nolad p r d plev true force (by simpa using hl),
        convC_cons_nolad p r d plev true force' (by rw [← hlad]; simpa using hl), hdd]

/-- **根が `(0,0)` のブロックを `n` 本並べた列の変換**。`conC (blk^n) = blk'^n`。 -/
theorem conC_run_top (R : PairSeq) (hR : ∀ c ∈ R, 0 < c.1) : ∀ n : ℕ,
    conC ((List.replicate n (((0, 0) : ℕ × ℕ) :: R)).flatten)
      = (List.replicate n (((0, 0) : ℕ × ℕ) :: convC R 1 0 true false)).flatten := by
  intro n
  match n with
  | 0 => simp [conC]
  | m + 1 =>
    have hR' : ∀ c ∈ R, ((0, 0) : ℕ × ℕ).1 < c.1 := by
      intro c hc; simpa using hR c hc
    have hhd : ((List.replicate m (((0, 0) : ℕ × ℕ) :: R)).flatten) = [] ∨
        ¬ (((0, 0) : ℕ × ℕ).1 < (((List.replicate m (((0, 0) : ℕ × ℕ) :: R)).flatten).headI).1) := by
      cases m with
      | zero => exact Or.inl rfl
      | succ m' => right; rw [List.replicate_succ, List.flatten_cons, List.cons_append]; simp
    obtain ⟨e1, e2⟩ := split_append (dd := ((0, 0) : ℕ × ℕ).1) hR' hhd
    have hnl : ladOf ((0, 0) : ℕ × ℕ).2 0 0 true false = false := by simp [ladOf]
    have hde : ddOf ((0, 0) : ℕ × ℕ).2 0 0 true false = 0 := by
      unfold ddOf; rw [if_neg (by rw [hnl]; simp), if_neg (by simp)]
    have hde2 : ddOf ((0, 0) : ℕ × ℕ).2 0 0 false false = 0 := by
      unfold ddOf
      rw [if_neg (by simp [ladOf]), if_neg (by simp)]
    rw [List.replicate_succ, List.flatten_cons, List.cons_append, conC,
      convC_cons_nolad ((0, 0) : ℕ × ℕ) (R ++ (List.replicate m (((0, 0) : ℕ × ℕ) :: R)).flatten)
        0 0 true false hnl, hde, e1, e2]
    simp only [Bool.and_true, beq_self_eq_true]
    rw [convC_force (L := R) (d := 1) (plev := 0) (by omega) true false]
    have := convC_run ((0, 0) : ℕ × ℕ) R [] hR' (Or.inl rfl) 0 0 m
    simp only [List.append_nil, convC_nil, hde2] at this
    rw [this, List.replicate_succ, List.flatten_cons]
    simp

/-! ## 2.77 添字 1 の基本列は末尾を落とすだけ -/

theorem range_append_range' (j0 m : ℕ) :
    List.range j0 ++ List.range' j0 m = List.range (j0 + m) := by
  rw [List.range_eq_range', List.range_eq_range']
  simpa using List.range'_append (s := 0) (m := j0) (n := m) (step := 1)

theorem range'_map_entry (M : PairSeq) {j0 j1 : ℕ} (h0 : j0 ≤ j1) (h1 : j1 ≤ M.length) :
    (List.range' j0 (j1 - j0)).map (fun j => ((entry M 0 j : ℕ), (entry M 1 j : ℕ)))
      = (M.take j1).drop j0 := by
  have hj : j0 + (j1 - j0) = j1 := by omega
  have hr : List.range j0 ++ List.range' j0 (j1 - j0) = List.range j1 := by
    rw [range_append_range', hj]
  have hd : (List.range j1).drop j0 = List.range' j0 (j1 - j0) := by
    rw [← hr, List.drop_left' (by simp)]
  rw [← hd, List.map_drop, map_range_entry_eq_take M h1]

/-- **`M⟦1⟧` はいつでも末尾を 1 列落とすだけ。** -/
theorem oper_one {M : PairSeq} (hL : 1 < M.length) : M⟦1⟧ = M.dropLast := by
  have hL1 : M.length - 1 ≠ 0 := by omega
  have hdl : M.dropLast = M.take (M.length - 1) := List.dropLast_eq_take
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero 1 hL1 hz, Pred, if_neg (by omega)]
  by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
  · rw [oper_bad_unfold 1 hL1 hz hp]
    set j0 := parent M (idx1 M (M.length - 1)) (M.length - 1) with hj0
    set j1 := M.length - 1 with hj1
    have hlt : j0 < j1 := nextR_index_lt (parent_nextR hp)
    have hle : j1 ≤ M.length := by omega
    have h1 : (List.range 1).flatMap
        (fun k => (List.range' j0 (j1 - j0)).map
          (fun j => ((entry M 0 j + k * (if 0 < idx1 M j1
              then entry M 0 j1 - entry M 0 j0 else 0) : ℕ), (entry M 1 j : ℕ))))
        = (M.take j1).drop j0 := by
      simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        Nat.zero_mul, Nat.add_zero]
      exact range'_map_entry M (le_of_lt hlt) hle
    rw [h1, hdl]
    conv_rhs => rw [← List.take_append_drop j0 (M.take j1)]
    rw [List.take_take, Nat.min_eq_left (le_of_lt hlt)]
  · rw [oper_eq_pred_of_noParent 1 hL1 hz hp, Pred, if_neg (by omega)]

/-! ## 2.775 末尾列の深さ -/

/-- 変換の末尾列は必ず深さ `d` 以上。 -/
theorem convC_getLast_ge {M : PairSeq} (hM : M ≠ []) (d plev : ℕ) (first force : Bool) :
    d ≤ ((convC M d plev first force).getLastD (0, 0)).1 := by
  have hne : convC M d plev first force ≠ [] := by
    intro he; rw [convC_eq_nil_iff] at he; exact hM he
  exact convC_ge' M d plev first force _ (getLastD_mem hne (0, 0))

/-- **末尾列が根より深ければ、像の末尾列も `d` より深い。** -/
theorem convC_getLast_depth : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n →
    ∀ (bd d plev : ℕ) (first force : Bool), blockok bd M → bd < (M.getLastD (0, 0)).1 →
      d < ((convC M d plev first force).getLastD (0, 0)).1 := by
  intro n
  induction n with
  | zero =>
    intro M hM bd d plev first force _ hlast
    have : M = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact absurd hlast (by simp)
  | succ n ih =>
    intro M hM bd d plev first force hb hlast
    match M with
    | [] => exact absurd hlast (by simp)
    | p :: r =>
      have hp : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp]⟩
      set A := r.takeWhile (fun q => ((bd, y) : ℕ × ℕ).1 < q.1) with hA
      set B := r.dropWhile (fun q => ((bd, y) : ℕ × ℕ).1 < q.1) with hB
      have hAB : r = A ++ B := by rw [hA, hB, List.takeWhile_append_dropWhile]
      have hlA : A.length ≤ n := by
        have := (List.takeWhile_sublist
          (fun q : ℕ × ℕ => ((bd, y) : ℕ × ℕ).1 < q.1) (l := r)).length_le
        simp only [List.length_cons] at hM; rw [hA]; omega
      have hlB : B.length ≤ n := by
        have := List.length_dropWhile_le (fun q : ℕ × ℕ => ((bd, y) : ℕ × ℕ).1 < q.1) r
        simp only [List.length_cons] at hM; rw [hB]; omega
      have hbB : blockok bd B := by rw [hB]; exact blockok_tail hb
      have hMlast : ((bd, y) :: r).getLastD (0, 0)
          = if B = [] then (if A = [] then ((bd, y) : ℕ × ℕ) else A.getLastD (0, 0))
            else B.getLastD (0, 0) := by
        rw [hAB]
        by_cases hBe : B = []
        · rw [hBe]
          simp only [List.append_nil, if_pos rfl]
          by_cases hAe : A = []
          · rw [hAe, if_pos rfl]; simp
          · rw [if_neg hAe, List.getLastD_cons]
            exact getLastD_ne_nil_indep hAe _ _
        · rw [if_neg hBe, List.getLastD_cons, getLastD_append_right hBe]
          exact getLastD_ne_nil_indep hBe _ _
      have key : ∀ (cs : PairSeq) (dA dB : ℕ) (fA fB gA gB : Bool), d < dA → dB = d →
          d < ((cs ++ (convC A dA ((bd, y) : ℕ × ℕ).2 fA gA
              ++ convC B dB ((bd, y) : ℕ × ℕ).2 fB gB)).getLastD (0, 0)).1 := by
        intro cs dA dB fA fB gA gB hdA hdB
        by_cases hBe : B = []
        · rw [if_pos hBe] at hMlast
          by_cases hAe : A = []
          · exfalso
            rw [if_pos hAe] at hMlast
            rw [hMlast] at hlast
            simp only [] at hlast
            omega
          · rw [hBe, convC_nil, List.append_nil, getLastD_append_cases,
              if_neg (by simp only [convC_eq_nil_iff]; exact hAe)]
            have := convC_getLast_ge hAe dA ((bd, y) : ℕ × ℕ).2 fA gA
            omega
        · rw [if_neg hBe] at hMlast
          rw [← List.append_assoc, getLastD_append_cases,
            if_neg (by simp only [convC_eq_nil_iff]; exact hBe)]
          have hlB2 : bd < (B.getLastD (0, 0)).1 := by rw [← hMlast]; exact hlast
          have := ih B hlB bd dB ((bd, y) : ℕ × ℕ).2 fB gB hbB hlB2
          omega
      by_cases hl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
      · rcases hcc : contrLen ((bd, y) : ℕ × ℕ) B (unitsLen ((bd, y) : ℕ × ℕ) B) A with
          _ | ⟨rest2, Bq⟩
        · rw [convC_cons_lad_none ((bd, y) : ℕ × ℕ) r d plev first force hl
            (by rw [← hA, ← hB]; exact hcc)]
          rw [← hA, ← hB, ← List.cons_append, ← List.cons_append]
          exact key [(d, plev), (d + 1, ((bd, y) : ℕ × ℕ).2)] (d + 2) d true false false false
            (by omega) rfl
        · obtain ⟨q, r2, hdq, hq2, hq1, hAq, hBq, hr2ne, hr2d, hr2l⟩ := contrLen_spec hcc
          have hlbq : Bq.length ≤ n := by
            have := (contrLen_lt hcc).2; omega
          have hBne : B ≠ [] := by
            intro he; rw [he, List.drop_nil] at hdq; exact absurd hdq (by simp)
          have hqe : q = (bd, q.2) := by
            simp only [] at hq1
            rw [← hq1]
          have hbq0 : blockok bd (q :: r2) := by
            rw [← hdq]
            exact blockok_drop hbB (fun _ => by rw [hdq]; simpa using hq1)
          have hbbq : blockok bd Bq := by
            rw [← hBq]
            have h1 := blockok_tail (d := bd) (y := q.2) (by rw [← hqe]; exact hbq0)
            simp only [] at h1 hq1
            rw [← hq1] at h1 ⊢
            exact h1
          have hBsplit : B = B.take (unitsLen ((bd, y) : ℕ × ℕ) B) ++ (q :: r2) := by
            rw [← hdq, List.take_append_drop]
          have hr2split : r2 = (contrPre ((bd, y) : ℕ × ℕ)
              (B.take (unitsLen ((bd, y) : ℕ × ℕ) B)) A ++ rest2) ++ Bq := by
            conv_lhs => rw [← List.takeWhile_append_dropWhile
              (p := fun x : ℕ × ℕ => decide (q.1 < x.1)) (l := r2)]
            rw [hAq, hBq]
          have hMl2 : ((bd, y) :: r).getLastD (0, 0)
              = if Bq = [] then rest2.getLastD (0, 0) else Bq.getLastD (0, 0) := by
            rw [hMlast, if_neg hBne]
            conv_lhs => rw [hBsplit]
            rw [getLastD_append_right (by simp) (0, 0), List.getLastD_cons]
            have hr2ne' : r2 ≠ [] := by
              intro he
              rw [he] at hr2split
              have hc : (contrPre ((bd, y) : ℕ × ℕ)
                  (B.take (unitsLen ((bd, y) : ℕ × ℕ) B)) A ++ rest2) ++ Bq = [] := hr2split.symm
              simp only [List.append_eq_nil_iff] at hc
              exact hr2ne hc.1.2
            rw [getLastD_ne_nil_indep hr2ne' _ (0, 0), hr2split, getLastD_append_cases]
            by_cases hbq : Bq = []
            · rw [if_pos hbq, if_pos hbq, getLastD_append_right hr2ne]
            · rw [if_neg hbq, if_neg hbq]
          rw [convC_cons_lad_some ((bd, y) : ℕ × ℕ) r d plev first force hl
            (by rw [← hA, ← hB]; exact hcc)]
          rw [← hA, ← hB]
          simp only [← List.cons_append, ← List.append_assoc]
          by_cases hbq : Bq = []
          · rw [hbq, convC_nil, List.append_nil, getLastD_append_cases,
              if_neg (by simp only [convC_eq_nil_iff]; exact hr2ne)]
            have := convC_getLast_ge hr2ne (d + 1) y false false
            omega
          · rw [getLastD_append_cases, if_neg (by simp only [convC_eq_nil_iff]; exact hbq)]
            have hlq : bd < (Bq.getLastD (0, 0)).1 := by
              rw [hMl2, if_neg hbq] at hlast; exact hlast
            exact ih Bq hlbq bd d ((bd, y) : ℕ × ℕ).2 false false hbbq hlq
      · rw [convC_cons_nolad ((bd, y) : ℕ × ℕ) r d plev first force (by simpa using hl)]
        rw [← hA, ← hB, ← List.cons_append]
        exact key [(ddOf ((bd, y) : ℕ × ℕ).2 d plev first force, ((bd, y) : ℕ × ℕ).2)]
          (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1) d true false
          (first && (((bd, y) : ℕ × ℕ).2 == plev)) false
          (by have := le_ddOf ((bd, y) : ℕ × ℕ).2 d plev first force; omega) rfl

/-! ## 2.78 親が接尾辞にあるときの展開の局所化 -/

/-- 親が接尾辞の中にあるなら、`hasParent` と `parent` は接尾辞に移せる。
`Pair/Column.lean` の `hasParent_append_right` は `entry T 0 0 = 0` を仮定するが、
「親が接尾辞にある」だけで十分（一意性から、どの `nextR` の始点も接尾辞に入る）。 -/
theorem hasParent_append_of_parent_ge (A T : PairSeq) {i j1 : ℕ}
    (hp : hasParent (A ++ T) i (A.length + j1))
    (hge : A.length ≤ parent (A ++ T) i (A.length + j1)) :
    hasParent T i j1 ∧
      parent (A ++ T) i (A.length + j1) = A.length + parent T i j1 := by
  set j0 := parent (A ++ T) i (A.length + j1) with hj0
  have hnr : nextR (A ++ T) i j0 (A.length + j1) := parent_nextR hp
  obtain ⟨j0', hj0'⟩ : ∃ j0', j0 = A.length + j0' := ⟨j0 - A.length, by omega⟩
  have hnrT : nextR T i j0' j1 := by
    rw [← nextR_append_right A T i j0' j1]
    rw [hj0'] at hnr
    exact hnr
  have hunique : ∀ y, nextR T i y j1 → y = j0' := by
    intro y hy
    have h1 : nextR (A ++ T) i (A.length + y) (A.length + j1) :=
      (nextR_append_right A T i y j1).2 hy
    have := hp.unique h1 hnr
    omega
  have hpT : hasParent T i j1 := ⟨j0', hnrT, hunique⟩
  refine ⟨hpT, ?_⟩
  have : parent T i j1 = j0' := hunique _ (parent_nextR hpT)
  rw [this, ← hj0']

/-- `nextrel0` の `j0` は「`j1` より浅い最後の添字」。だから浅い列があれば親はそれ以降。 -/
theorem nextrel0_ge {N : PairSeq} {j0 j1 k : ℕ} (h : nextrel0 N j0 j1)
    (hk : k < j1) (hlt : entry N 0 k < entry N 0 j1) : k ≤ j0 := by
  by_contra hgt
  push_neg at hgt
  have := h.2.2.2.2 k ⟨hgt, hk⟩
  omega

/-- `nextrel1` の `j0` も同様（`le0` の鎖の上で「段がより小さい最後の添字」）。 -/
theorem nextrel1_ge {N : PairSeq} {j0 j1 k : ℕ} (h : nextrel1 N j0 j1)
    (hk : le0 N k j1) (hlt : entry N 1 k < entry N 1 j1) : k ≤ j0 := by
  by_contra hgt
  push_neg at hgt
  have := h.2.2.2.2.2 k ⟨hgt, hk⟩
  omega

/-- **浅い（段が小さい）列が 1 つあれば、親はその位置以降にある。**
`i = 0` なら深さ、`i = 1` なら段で測る。 -/
theorem parent_ge_of_shallow {N : PairSeq} {i j1 k : ℕ} (hp : hasParent N i j1)
    (hk0 : i = 0 → k < j1 ∧ entry N 0 k < entry N 0 j1)
    (hk1 : i ≠ 0 → le0 N k j1 ∧ entry N 1 k < entry N 1 j1) :
    k ≤ parent N i j1 := by
  have hnr : nextR N i (parent N i j1) j1 := parent_nextR hp
  unfold nextR at hnr
  by_cases hi : i = 0
  · rw [if_pos hi] at hnr
    obtain ⟨h1, h2⟩ := hk0 hi
    exact nextrel0_ge hnr h1 h2
  · rw [if_neg hi] at hnr
    obtain ⟨h1, h2⟩ := hk1 hi
    exact nextrel1_ge hnr h1 h2

/-- **接尾辞の中に `nextR` の証人が 1 つあれば、親は接尾辞にある。**
`hasParent` は一意性つきなので、証人がそのまま親になる。 -/
theorem parent_ge_of_witness (A T : PairSeq) {i j1 j0' : ℕ}
    (hp : hasParent (A ++ T) i (A.length + j1))
    (hw : nextR T i j0' j1) :
    A.length ≤ parent (A ++ T) i (A.length + j1) := by
  have h1 : nextR (A ++ T) i (A.length + j0') (A.length + j1) :=
    (nextR_append_right A T i j0' j1).2 hw
  have := hp.unique h1 (parent_nextR hp)
  omega

/-- **親が接尾辞にあるときの展開の局所化。** -/
theorem oper_append_of_parent_ge (A T : PairSeq) (n : ℕ) (hT : 2 ≤ T.length)
    (hz : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0))
    (hp : hasParent (A ++ T) (idx1 T (T.length - 1)) (A.length + (T.length - 1)))
    (hge : A.length ≤ parent (A ++ T) (idx1 T (T.length - 1)) (A.length + (T.length - 1))) :
    (A ++ T)⟦n⟧ = A ++ T⟦n⟧ := by
  have hlenAT : (A ++ T).length - 1 = A.length + (T.length - 1) := by
    rw [List.length_append]; omega
  set j1 := T.length - 1 with hj1
  have hne_AT : ¬ (A.length + j1 = 0) := by omega
  have hne_T : ¬ (j1 = 0) := by omega
  have he0 : entry (A ++ T) 0 (A.length + j1) = entry T 0 j1 := entry_append_right A T 0 j1
  have he1 : entry (A ++ T) 1 (A.length + j1) = entry T 1 j1 := entry_append_right A T 1 j1
  have hidx : idx1 (A ++ T) (A.length + j1) = idx1 T j1 := idx1_append_right A T j1
  obtain ⟨hpT, hpar⟩ := hasParent_append_of_parent_ge A T hp hge
  unfold oper
  rw [hlenAT, if_neg hne_AT, if_neg hne_T, he0, he1, if_neg hz, if_neg hz, hidx,
    if_neg (not_not.2 hp), if_neg (not_not.2 hpT), hpar]
  set j0 := parent T (idx1 T j1) j1 with hj0
  simp only []
  have hd0 : entry T 0 j1 - entry (A ++ T) 0 (A.length + j0) = entry T 0 j1 - entry T 0 j0 := by
    rw [entry_append_right]
  have hd1 : entry T 1 j1 - entry (A ++ T) 1 (A.length + j0) = entry T 1 j1 - entry T 1 j0 := by
    rw [entry_append_right]
  rw [hd0, hd1]
  have hrange : (A.length + j1) - (A.length + j0) = j1 - j0 := by omega
  rw [hrange, take_append_right, List.append_assoc]
  congr 1
  congr 1
  apply List.flatMap_congr
  intro k _
  exact copyblock_append A T j0 (j1 - j0) k _ _

/-- 証人から直接、展開の局所化を出す形。 -/
theorem oper_append_of_witness (A T : PairSeq) (n : ℕ) (hT : 2 ≤ T.length)
    (hz : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0))
    (hp : hasParent (A ++ T) (idx1 T (T.length - 1)) (A.length + (T.length - 1)))
    {j0' : ℕ} (hw : nextR T (idx1 T (T.length - 1)) j0' (T.length - 1)) :
    (A ++ T)⟦n⟧ = A ++ T⟦n⟧ :=
  oper_append_of_parent_ge A T n hT hz hp (parent_ge_of_witness A T hp hw)

/-! ### `le0`（行 0 の祖先）の道具 -/

/-- `j` 未満で `P` を満たすものがあるなら、そのうち最大のものがある。 -/
theorem exists_greatest_lt {P : ℕ → Prop} : ∀ (j : ℕ), (∃ i, i < j ∧ P i) →
    ∃ i, i < j ∧ P i ∧ ∀ i', i < i' → i' < j → ¬ P i' := by
  intro j
  induction j with
  | zero => rintro ⟨i, hi, -⟩; omega
  | succ j ih =>
    intro h
    by_cases hPj : P j
    · exact ⟨j, by omega, hPj, fun i' h1 h2 => by omega⟩
    · obtain ⟨i, hi, hPi⟩ := h
      have hij : i < j := by
        rcases Nat.lt_or_ge i j with h' | h'
        · exact h'
        · exfalso
          have hie : i = j := by omega
          rw [hie] at hPi; exact hPj hPi
      obtain ⟨i0, h1, h2, h3⟩ := ih ⟨i, hij, hPi⟩
      refine ⟨i0, by omega, h2, fun i' ha hb => ?_⟩
      rcases Nat.lt_or_ge i' j with hc | hc
      · exact h3 i' ha hc
      · have hie : i' = j := by omega
        rw [hie]; exact hPj

theorem entry_cons_succ (c : ℕ × ℕ) (R : PairSeq) (i j : ℕ) :
    entry (c :: R) i (j + 1) = entry R i j := by
  unfold entry
  rw [List.getD_cons_succ]

/-- **ブロックの頭は、その中のどの列の行 0 の祖先でもある。** -/
theorem le0_head {c : ℕ × ℕ} {R : PairSeq} (hR : ∀ x ∈ R, c.1 < x.1) :
    ∀ (j : ℕ), j < (c :: R).length → le0 (c :: R) 0 j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact ⟨by simp, by simp, Relation.ReflTransGen.refl⟩
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj'R : j' < R.length := by simp only [List.length_cons] at hj; omega
      have hmem : R.getD j' (0, 0) ∈ R := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'R]
        simpa using List.getElem_mem hj'R
      have h0 : entry (c :: R) 0 0 < entry (c :: R) 0 (j' + 1) := by
        rw [entry_cons_succ]
        have h1 : entry (c :: R) 0 0 = c.1 := by unfold entry; rw [if_pos rfl]; rfl
        have h2 : entry R 0 j' = (R.getD j' (0, 0)).1 := by unfold entry; rw [if_pos rfl]
        rw [h1, h2]
        exact hR _ hmem
      obtain ⟨i, hi1, hi2, hi3⟩ := exists_greatest_lt
        (P := fun i => entry (c :: R) 0 i < entry (c :: R) 0 (j' + 1)) (j' + 1) ⟨0, hpos, h0⟩
      have hnr : nextrel0 (c :: R) i (j' + 1) :=
        ⟨by omega, hj, hi1, hi2, fun k hk => by
          have := hi3 k hk.1 hk.2
          omega⟩
      have hle : le0 (c :: R) 0 i := ih i hi1 (by omega)
      exact ⟨hle.1, hj, hle.2.2.tail hnr⟩

/-- 接尾辞の中に「末尾より浅い列」があれば局所化できる（段 0 の場合）。 -/
theorem oper_append_of_shallow0 (A T : PairSeq) (n : ℕ) (hT : 2 ≤ T.length)
    (hz : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0))
    (hi : idx1 T (T.length - 1) = 0)
    (hp : hasParent (A ++ T) (idx1 T (T.length - 1)) (A.length + (T.length - 1)))
    {k : ℕ} (hk : k < T.length - 1)
    (hlt : entry T 0 k < entry T 0 (T.length - 1)) :
    (A ++ T)⟦n⟧ = A ++ T⟦n⟧ := by
  refine oper_append_of_parent_ge A T n hT hz hp ?_
  have h := parent_ge_of_shallow (N := A ++ T) (i := idx1 T (T.length - 1))
    (j1 := A.length + (T.length - 1)) (k := A.length + k) hp
    (fun _ => ⟨by omega, by rw [entry_append_right, entry_append_right]; exact hlt⟩)
    (fun hne => absurd hi hne)
  omega

/-- 接尾辞の中に「`le0` の鎖の上で段がより小さい列」があれば局所化できる（段 > 0 の場合）。 -/
theorem oper_append_of_shallow1 (A T : PairSeq) (n : ℕ) (hT : 2 ≤ T.length)
    (hz : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0))
    (hi : idx1 T (T.length - 1) ≠ 0)
    (hp : hasParent (A ++ T) (idx1 T (T.length - 1)) (A.length + (T.length - 1)))
    {k : ℕ} (hk : le0 T k (T.length - 1))
    (hlt : entry T 1 k < entry T 1 (T.length - 1)) :
    (A ++ T)⟦n⟧ = A ++ T⟦n⟧ := by
  refine oper_append_of_parent_ge A T n hT hz hp ?_
  have h := parent_ge_of_shallow (N := A ++ T) (i := idx1 T (T.length - 1))
    (j1 := A.length + (T.length - 1)) (k := A.length + k) hp
    (fun he => absurd he hi)
    (fun _ => ⟨le0_append_right_of A T hk,
      by rw [entry_append_right, entry_append_right]; exact hlt⟩)
  omega

/-- 像の先頭が深さ `d` なら、それが「末尾より浅い列」の証人になる。 -/
theorem convC_head_shallow {B : PairSeq} (hB : B ≠ []) {bd d plev : ℕ}
    (hb : blockok bd B) (hbd : bd < (B.getLastD (0, 0)).1)
    (hhd : ((convC B d plev false false).headI).1 = d) :
    entry (convC B d plev false false) 0 0
      < entry (convC B d plev false false) 0 ((convC B d plev false false).length - 1) := by
  rw [entry_zero0, entry_last0, hhd]
  exact convC_getLast_depth B.length B (Nat.le_refl _) bd d plev false false hb hbd

/-- **段 0 のときの証人の存在。** `B` の末尾が根より深ければ、
`convC B d plev false false` の中に「末尾より浅い列」がある。 -/
theorem convC_exists_shallow : ∀ (n : ℕ) (B : PairSeq), B.length ≤ n →
    ∀ (bd d plev : ℕ), blockok bd B → colOK B → descOK B → bd ≤ d →
    bd < (B.getLastD (0, 0)).1 →
    ∃ k, k < (convC B d plev false false).length - 1 ∧
      entry (convC B d plev false false) 0 k
        < entry (convC B d plev false false) 0 ((convC B d plev false false).length - 1) := by
  intro n
  induction n with
  | zero =>
    intro B hB bd d plev _ _ _ _ hlast
    have : B = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact absurd hlast (by simp)
  | succ n ih =>
    intro B hB bd d plev hb hc hd hbd hlast
    match B with
    | [] => exact absurd hlast (by simp)
    | p :: r =>
      have hp : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp]⟩
      have hy : y ≤ bd := hc (bd, y) (by simp)
      set A := r.takeWhile (fun q => ((bd, y) : ℕ × ℕ).1 < q.1) with hA
      set B' := r.dropWhile (fun q => ((bd, y) : ℕ × ℕ).1 < q.1) with hB'
      have hAB : r = A ++ B' := by rw [hA, hB', List.takeWhile_append_dropWhile]
      have hbB' : blockok bd B' := by rw [hB']; exact blockok_tail hb
      have hMlast : ((bd, y) :: r).getLastD (0, 0)
          = if B' = [] then (if A = [] then ((bd, y) : ℕ × ℕ) else A.getLastD (0, 0))
            else B'.getLastD (0, 0) := by
        rw [hAB]
        by_cases hBe : B' = []
        · rw [hBe]
          simp only [List.append_nil]
          by_cases hAe : A = []
          · rw [hAe, if_pos rfl]; simp
          · rw [if_neg hAe, List.getLastD_cons]
            exact getLastD_ne_nil_indep hAe _ _
        · rw [if_neg hBe, List.getLastD_cons, getLastD_append_right hBe]
          exact getLastD_ne_nil_indep hBe _ _
      have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev false false = false := by simp [ladOf]
      set dd := ddOf ((bd, y) : ℕ × ℕ).2 d plev false false with hdd
      set X := convC A (dd + 1) ((bd, y) : ℕ × ℕ).2 true false with hX
      set Y := convC B' d ((bd, y) : ℕ × ℕ).2 false false with hY
      have hout : convC ((bd, y) :: r) d plev false false
          = ((dd, ((bd, y) : ℕ × ℕ).2) :: X) ++ Y := by
        rw [convC_cons_nolad ((bd, y) : ℕ × ℕ) r d plev false false hnl]
        simp only [Bool.false_and]
        rw [← hA, ← hB', ← hdd, ← hX, ← hY, List.cons_append]
      have hlastdep : d < ((convC ((bd, y) :: r) d plev false false).getLastD (0, 0)).1 :=
        convC_getLast_depth ((bd, y) :: r).length _ (Nat.le_refl _) bd d plev false false hb hlast
      have hlen2 : 1 < ((bd, y) :: r).length := by
        by_contra hcon
        have : r = [] := by
          match r with
          | [] => rfl
          | _ :: _ => simp at hcon
        rw [this] at hlast
        simp only [List.getLastD_cons, List.getLastD_nil] at hlast
        omega
      have hOlen : 1 < (convC ((bd, y) :: r) d plev false false).length :=
        convC_length_ge_two hlen2 d plev false false
      by_cases hdc : dd = d
      · -- 先頭が深さ `d`: それが証人
        refine ⟨0, by omega, ?_⟩
        rw [entry_zero0, entry_last0]
        have hhd : ((convC ((bd, y) :: r) d plev false false).headI).1 = d := by
          rw [hout]
          simp only [List.cons_append, List.headI_cons]
          exact hdc
        rw [hhd]
        exact hlastdep
      · -- `dd = y + 1` で `y = bd = d`
        have hcase : 0 < y ∧ d ≤ y := by
          by_contra hcon
          rw [hdd] at hdc
          unfold ddOf at hdc
          rw [if_neg (by rw [hnl]; simp), if_neg (by simpa using hcon)] at hdc
          exact hdc rfl
        have hyd : y = d := by omega
        have hdd1 : dd = d + 1 := by
          rw [hdd]; unfold ddOf
          rw [if_neg (by rw [hnl]; simp), if_pos hcase]
          simp only []
          omega
        by_cases hBe : B' = []
        · -- 末尾は `X` の中（深さ ≥ dd+1）
          have hAe : A ≠ [] := by
            intro he
            rw [if_pos hBe, if_pos he] at hMlast
            rw [hMlast] at hlast
            simp only [] at hlast
            omega
          have hXne : X ≠ [] := by rw [hX]; intro he; rw [convC_eq_nil_iff] at he; exact hAe he
          have hYnil : Y = [] := by rw [hY, hBe, convC_nil]
          refine ⟨0, by omega, ?_⟩
          rw [entry_zero0, entry_last0, hout, hYnil, List.append_nil]
          simp only [List.headI_cons]
          have hlx : ((dd, ((bd, y) : ℕ × ℕ).2) :: X).getLastD (0, 0) = X.getLastD (0, 0) := by
            rw [List.getLastD_cons]
            exact getLastD_ne_nil_indep hXne _ _
          rw [hlx]
          have hmem : X.getLastD (0, 0) ∈ convC A (dd + 1) ((bd, y) : ℕ × ℕ).2 true false := by
            rw [← hX]; exact getLastD_mem hXne (0, 0)
          have := convC_ge' A (dd + 1) ((bd, y) : ℕ × ℕ).2 true false _ hmem
          omega
        · -- 末尾は `Y` の中: `B'` に帰納
          have hlB' : B'.length ≤ n := by
            have := List.length_dropWhile_le (fun q : ℕ × ℕ => ((bd, y) : ℕ × ℕ).1 < q.1) r
            simp only [List.length_cons] at hB; rw [hB']; omega
          have hcB' : colOK B' := fun cc hcm => hc cc
            (List.mem_cons_of_mem _ (by rw [hB'] at hcm; exact (List.dropWhile_sublist _).subset hcm))
          have hdB' : descOK B' := by rw [hB']; exact (descOK_cons.1 hd).2.2
          have hlB2 : bd < (B'.getLastD (0, 0)).1 := by
            rw [if_neg hBe] at hMlast; rw [← hMlast]; exact hlast
          obtain ⟨k, hk1, hk2⟩ := ih B' hlB' bd d ((bd, y) : ℕ × ℕ).2 hbB' hcB' hdB' hbd hlB2
          have hYne : Y ≠ [] := by rw [hY]; intro he; rw [convC_eq_nil_iff] at he; exact hBe he
          have hYlen : 0 < Y.length := List.length_pos_of_ne_nil hYne
          refine ⟨((dd, ((bd, y) : ℕ × ℕ).2) :: X).length + k, ?_, ?_⟩
          · rw [hout]
            simp only [List.length_append]
            rw [← hY] at hk1
            omega
          · rw [hout]
            have he1 : (((dd, ((bd, y) : ℕ × ℕ).2) :: X) ++ Y).length - 1
                = ((dd, ((bd, y) : ℕ × ℕ).2) :: X).length + (Y.length - 1) := by
              simp only [List.length_append]; omega
            rw [he1, entry_append_right, entry_append_right, hY]
            exact hk2

/-- **場合 (c) の段 0（完成形）**: `B` の末尾が根より深ければ、
`convC B` の像の上で展開は局所化できる。 -/
theorem oper_append_convC (A B : PairSeq) (n : ℕ) {bd d plev : ℕ}
    (hb : blockok bd B) (hc : colOK B) (hdo : descOK B) (hbd : bd ≤ d)
    (hlast : bd < (B.getLastD (0, 0)).1)
    (hT : 2 ≤ (convC B d plev false false).length)
    (hz : ¬ (entry (convC B d plev false false)
              0 ((convC B d plev false false).length - 1) = 0 ∧
             entry (convC B d plev false false)
              1 ((convC B d plev false false).length - 1) = 0))
    (hi : idx1 (convC B d plev false false) ((convC B d plev false false).length - 1) = 0)
    (hp : hasParent (A ++ convC B d plev false false)
            (idx1 (convC B d plev false false) ((convC B d plev false false).length - 1))
            (A.length + ((convC B d plev false false).length - 1))) :
    (A ++ convC B d plev false false)⟦n⟧ = A ++ (convC B d plev false false)⟦n⟧ := by
  obtain ⟨k, hk1, hk2⟩ :=
    convC_exists_shallow B.length B (Nat.le_refl _) bd d plev hb hc hdo hbd hlast
  exact oper_append_of_shallow0 A _ n hT hz hi hp hk1 hk2

/-- **浅い列が 1 つでもあれば、行 0 の親は存在する**（一意性は `nextrel0` の最大性から）。 -/
theorem hasParent0_of_exists {M : PairSeq} {j1 : ℕ} (hj : j1 < M.length)
    (h : ∃ i, i < j1 ∧ entry M 0 i < entry M 0 j1) : hasParent M 0 j1 := by
  obtain ⟨i, hi1, hi2, hi3⟩ := exists_greatest_lt
    (P := fun i => entry M 0 i < entry M 0 j1) j1 h
  have hnr : nextrel0 M i j1 :=
    ⟨by omega, hj, hi1, hi2, fun k hk => by
      have := hi3 k hk.1 hk.2
      omega⟩
  refine ⟨i, ?_, ?_⟩
  · show nextR M 0 i j1
    unfold nextR; rw [if_pos rfl]; exact hnr
  · intro y hy
    have hy' : nextrel0 M y j1 := by
      have : nextR M 0 y j1 := hy
      unfold nextR at this; rw [if_pos rfl] at this; exact this
    clear hy
    rename' hy' => hy
    have h1 : i ≤ y := nextrel0_ge hy hi1 hi2
    have h2 : y ≤ i := by
      by_contra hgt
      push_neg at hgt
      exact hi3 y hgt hy.2.2.1 hy.2.2.2.1
    omega

/-! ## 2.79 末尾ブロックが 1 列のときの dropLast -/

/-- 1 列だけの変換。`first = false` なら梯子も縮約も起きない。 -/
theorem convC_single (c : ℕ × ℕ) (d plev : ℕ) :
    convC [c] d plev false false = [(ddOf c.2 d plev false false, c.2)] := by
  rw [convC_cons_nolad c [] d plev false false (by simp [ladOf])]
  simp

/-- 末尾ブロックが 1 列なら、その 1 列は像でも 1 列。 -/
theorem convC_dropLast_singleton (p c : ℕ × ℕ) (A : PairSeq) (d plev : ℕ)
    (first force : Bool) (hA : ∀ x ∈ A, p.1 < x.1) (hc : ¬ (p.1 < c.1)) :
    convC (p :: (A ++ [c])) d plev first force
      = convC (p :: A) d plev first force ++ [(ddOf c.2 d p.2 false false, c.2)] := by
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := [c]) (dd := p.1) hA (Or.inr (by simpa using hc))
  obtain ⟨e3, e4⟩ := split_append (X := A) (Y := []) (dd := p.1) hA (Or.inl rfl)
  simp only [List.append_nil] at e3 e4
  -- どちらの側でも縮約は起きない
  have hnone2 : contrLen p [] (unitsLen p []) A = none := by
    unfold contrLen; simp
  have hnone1 : contrLen p [c] (unitsLen p [c]) A = none := by
    by_cases hcp : c = p
    · have hu : unitsLen p [c] = 1 := by
        subst hcp
        rw [unitsLen_cons_pos]
        simp [unitsLen]
      unfold contrLen
      rw [hu]; simp
    · have hu : unitsLen p [c] = 0 := unitsLen_cons_neg hcp
      unfold contrLen
      rw [hu]
      simp only [List.drop_zero, List.take_zero]
      refine if_neg ?_
      rintro ⟨-, -, h3, -⟩
      have hpre : contrPre p [] A ≠ [] := by simp [contrPre]
      simp only [List.takeWhile_nil, List.take_nil] at h3
      exact hpre h3.symm
  by_cases hl : ladOf p.2 d plev first force = true
  · rw [convC_cons_lad_none p (A ++ [c]) d plev first force hl (by rw [e1, e2]; exact hnone1),
      convC_cons_lad_none p A d plev first force hl (by rw [e3, e4]; exact hnone2),
      e1, e2, e3, e4, convC_nil, convC_single]
    simp [List.append_assoc]
  · rw [convC_cons_nolad p (A ++ [c]) d plev first force (by simpa using hl),
      convC_cons_nolad p A d plev first force (by simpa using hl),
      e1, e2, e3, e4, convC_nil, convC_single]
    simp [List.append_assoc]

theorem dropLast_cons_ne {α : Type*} {a : α} {l : List α} (h : l ≠ []) :
    (a :: l).dropLast = a :: l.dropLast := by
  match l with
  | [] => exact absurd rfl h
  | _ :: _ => rfl

/-- 引数ブロックへ降りる段。`B` が空なら縮約は起きないので、そのまま `A` に帰着する。 -/
theorem convC_dropLast_arg (p : ℕ × ℕ) (A : PairSeq) (d plev : ℕ) (first force : Bool)
    (hA : ∀ x ∈ A, p.1 < x.1) (hAne : A ≠ [])
    (ih : ∀ (dA : ℕ) (fo : Bool),
      convC (A.dropLast) dA p.2 true fo = (convC A dA p.2 true fo).dropLast) :
    convC (p :: A.dropLast) d plev first force
      = (convC (p :: A) d plev first force).dropLast := by
  have hAd : ∀ x ∈ A.dropLast, p.1 < x.1 :=
    fun x hx => hA x ((List.dropLast_sublist A).subset hx)
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := []) (dd := p.1) hA (Or.inl rfl)
  obtain ⟨e3, e4⟩ := split_append (X := A.dropLast) (Y := []) (dd := p.1) hAd (Or.inl rfl)
  simp only [List.append_nil] at e1 e2 e3 e4
  have hnone : contrLen p [] (unitsLen p []) A = none := by unfold contrLen; simp
  have hnone' : contrLen p [] (unitsLen p []) A.dropLast = none := by unfold contrLen; simp
  by_cases hl : ladOf p.2 d plev first force = true
  · have hXne : convC A (d + 2) p.2 true false ≠ [] := by
      intro he; rw [convC_eq_nil_iff] at he; exact hAne he
    rw [convC_cons_lad_none p A.dropLast d plev first force hl (by rw [e3, e4]; exact hnone'),
      convC_cons_lad_none p A d plev first force hl (by rw [e1, e2]; exact hnone),
      e1, e2, e3, e4, convC_nil]
    simp only [List.append_nil]
    rw [ih (d + 2) false, dropLast_cons_ne (by simp), dropLast_cons_ne hXne]
  · have hXne : convC A (ddOf p.2 d plev first force + 1) p.2 true (first && (p.2 == plev)) ≠ [] := by
      intro he; rw [convC_eq_nil_iff] at he; exact hAne he
    rw [convC_cons_nolad p A.dropLast d plev first force (by simpa using hl),
      convC_cons_nolad p A d plev first force (by simpa using hl),
      e1, e2, e3, e4, convC_nil]
    simp only [List.append_nil]
    rw [ih (ddOf p.2 d plev first force + 1) (first && (p.2 == plev)), dropLast_cons_ne hXne]

/-- 兄弟の鎖へ降りる段（梯子なし）。縮約は起きないので、そのまま `B` に帰着する。 -/
theorem convC_dropLast_tail (p : ℕ × ℕ) (A B : PairSeq) (d plev : ℕ) (first force : Bool)
    (hA : ∀ x ∈ A, p.1 < x.1) (hBne : B ≠ []) (hBd : B.dropLast ≠ [])
    (hBh : ¬ (p.1 < (B.headI).1))
    (hnl : ladOf p.2 d plev first force = false)
    (ih : convC (B.dropLast) d p.2 false false = (convC B d p.2 false false).dropLast) :
    convC (p :: (A ++ B.dropLast)) d plev first force
      = (convC (p :: (A ++ B)) d plev first force).dropLast := by
  have hhd : (B.dropLast).headI = B.headI := by
    rcases B with _ | ⟨b, _ | ⟨b2, B'⟩⟩
    · exact absurd rfl hBne
    · simp at hBd
    · rfl
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := B) (dd := p.1) hA (Or.inr hBh)
  obtain ⟨e3, e4⟩ := split_append (X := A) (Y := B.dropLast) (dd := p.1) hA
    (Or.inr (by rw [hhd]; exact hBh))
  have hYne : convC B d p.2 false false ≠ [] := by
    intro he; rw [convC_eq_nil_iff] at he; exact hBne he
  rw [convC_cons_nolad p (A ++ B.dropLast) d plev first force (by simpa using hnl),
    convC_cons_nolad p (A ++ B) d plev first force (by simpa using hnl),
    e1, e2, e3, e4, ih]
  rw [dropLast_cons_ne (by
    intro he
    obtain ⟨-, h2⟩ := List.append_eq_nil_iff.1 he
    exact hYne h2)]
  congr 1
  exact (List.dropLast_append_of_ne_nil hYne).symm

/-- 梯子ありで兄弟に降りる段（縮約が発火する場合）。`Bq ≠ []` なら縮約は消えない。 -/
theorem convC_dropLast_contr (p : ℕ × ℕ) (A B : PairSeq) (d plev : ℕ) (first force : Bool)
    (hA : ∀ x ∈ A, p.1 < x.1) (hBh : B = [] ∨ ¬ (p.1 < (B.headI).1))
    (hl : ladOf p.2 d plev first force = true)
    {rest2 Bq : PairSeq}
    (hcc : contrLen p B (unitsLen p B) A = some (rest2, Bq))
    (hBqne : Bq ≠ [])
    (ih : convC (Bq.dropLast) d p.2 false false = (convC Bq d p.2 false false).dropLast) :
    convC (p :: (A ++ B.dropLast)) d plev first force
      = (convC (p :: (A ++ B)) d plev first force).dropLast := by
  obtain ⟨q, r2, hdq, hq2, hq1, hAq, hBq, hr2ne, hr2d, hr2l⟩ := contrLen_spec hcc
  set k := unitsLen p B with hk
  set U := B.take k with hU
  have hkle : k ≤ B.length := unitsLen_le p B.length B (Nat.le_refl _)
  have hUlen : U.length = k := by rw [hU, List.length_take]; omega
  have hBsplit : B = U ++ (q :: r2) := by rw [hU, ← hdq, List.take_append_drop]
  have hr2split : r2 = (r2.takeWhile fun x => q.1 < x.1) ++ Bq := by
    conv_lhs => rw [← List.takeWhile_append_dropWhile
      (p := fun x : ℕ × ℕ => decide (q.1 < x.1)) (l := r2)]
    rw [hBq]
  have hr2ne' : r2 ≠ [] := by
    intro he
    rw [he] at hr2split
    exact hBqne (List.append_eq_nil_iff.1 hr2split.symm).2
  have hAqdeep : ∀ x ∈ (r2.takeWhile fun x => q.1 < x.1), q.1 < x.1 := by
    intro x hx
    have := List.mem_takeWhile_imp (p := fun x : ℕ × ℕ => decide (q.1 < x.1)) hx
    simpa using this
  have hBqh : Bq = [] ∨ ¬ (q.1 < (Bq.headI).1) := by
    rcases dropWhile_head_neg (a := q.1) r2 with h | h
    · rw [hBq] at h; exact Or.inl h
    · rw [hBq] at h; exact Or.inr h
  have hBqdh : Bq.dropLast = [] ∨ ¬ (q.1 < ((Bq.dropLast).headI).1) := by
    rcases hBqh with h | h
    · exact Or.inl (by rw [h]; rfl)
    · rcases Bq with _ | ⟨b, _ | ⟨b2, Bq'⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (by simpa using h)
  -- `B.dropLast` の分解
  have hBdrop : B.dropLast = U ++ (q :: r2.dropLast) := by
    rw [hBsplit, List.dropLast_append_of_ne_nil (by simp), dropLast_cons_ne hr2ne']
  have hr2drop : r2.dropLast = (r2.takeWhile fun x => q.1 < x.1) ++ Bq.dropLast := by
    conv_lhs => rw [hr2split]
    rw [List.dropLast_append_of_ne_nil hBqne]
  have hqp : ¬ (q = p) := by
    intro he; rw [he] at hq2; omega
  have hUnits : Units p U := by rw [hU, hk]; exact units_take p B.length B (Nat.le_refl _)
  have hu' : unitsLen p (B.dropLast) = k := by
    rw [hBdrop, unitsLen_append_units hUnits (Or.inr ⟨by simp only [List.headI_cons]; omega,
      by simp only [List.headI_cons]; exact hqp⟩), hUlen]
  -- 縮約は同じように発火する
  have hcc' : contrLen p (B.dropLast) (unitsLen p (B.dropLast)) A = some (rest2, Bq.dropLast) := by
    obtain ⟨eA, eB⟩ := split_append (X := (r2.takeWhile fun x => q.1 < x.1))
      (Y := Bq.dropLast) (dd := q.1) hAqdeep hBqdh
    have htk : (B.dropLast).take k = U := by rw [hBdrop, ← hUlen, List.take_left]
    have hdk : (B.dropLast).drop k = q :: r2.dropLast := by
      rw [hBdrop, ← hUlen, List.drop_left]
    unfold contrLen
    rw [hu', hdk, htk]
    simp only [hr2drop, eA, eB]
    have hpre : (r2.takeWhile fun x => q.1 < x.1) = contrPre p U A ++ rest2 := hAq
    rw [hpre]
    have hlen : (contrPre p U A ++ rest2).take (contrPre p U A).length = contrPre p U A := by
      rw [List.take_left]
    have hdrp : (contrPre p U A ++ rest2).drop (contrPre p U A).length = rest2 := by
      rw [List.drop_left]
    rw [if_pos ⟨hq2, hq1, hlen, by rw [hdrp]; exact hr2ne, by rw [hdrp]; exact hr2d,
      by rw [hdrp]; exact hr2l⟩, hdrp]
  -- 出力の比較
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := B) (dd := p.1) hA hBh
  have hBdh : B.dropLast = [] ∨ ¬ (p.1 < ((B.dropLast).headI).1) := by
    right
    rw [hBdrop]
    by_cases hUe : U = []
    · rw [hUe]; simp only [List.nil_append, List.headI_cons]; omega
    · rw [headI_append_left hUe]
      have hle : (U.headI).1 ≤ p.1 := by
        rcases hUnits.head_eq with h | h
        · exact absurd h hUe
        · rw [h]
      omega
  obtain ⟨e3, e4⟩ := split_append (X := A) (Y := B.dropLast) (dd := p.1) hA hBdh
  have hYne : convC Bq d p.2 false false ≠ [] := by
    intro he; rw [convC_eq_nil_iff] at he; exact hBqne he
  rw [convC_cons_lad_some p (A ++ B.dropLast) d plev first force hl (by rw [e3, e4]; exact hcc'),
    convC_cons_lad_some p (A ++ B) d plev first force hl (by rw [e1, e2]; exact hcc),
    e1, e2, e3, e4, hu', ← hk, ← hU]
  have htk : (B.dropLast).take k = U := by rw [hBdrop, ← hUlen, List.take_left]
  rw [htk, ih]
  rw [dropLast_cons_ne (by simp), dropLast_cons_ne (by
    intro he
    simp only [List.append_eq_nil_iff] at he
    exact hYne he.2)]
  congr 2
  exact (List.dropLast_append_of_ne_nil hYne).symm

/-- 梯子ありで縮約なしの、兄弟に降りる段。 -/
theorem convC_dropLast_lad_none (p : ℕ × ℕ) (A B : PairSeq) (d plev : ℕ) (first force : Bool)
    (hA : ∀ x ∈ A, p.1 < x.1) (hBne : B ≠ []) (hBd : B.dropLast ≠ [])
    (hBh : ¬ (p.1 < (B.headI).1))
    (hl : ladOf p.2 d plev first force = true)
    (hc1 : contrLen p B (unitsLen p B) A = none)
    (hc2 : contrLen p (B.dropLast) (unitsLen p (B.dropLast)) A = none)
    (ih : convC (B.dropLast) d p.2 false false = (convC B d p.2 false false).dropLast) :
    convC (p :: (A ++ B.dropLast)) d plev first force
      = (convC (p :: (A ++ B)) d plev first force).dropLast := by
  have hhd : (B.dropLast).headI = B.headI := by
    rcases B with _ | ⟨b, _ | ⟨b2, B'⟩⟩
    · exact absurd rfl hBne
    · simp at hBd
    · rfl
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := B) (dd := p.1) hA (Or.inr hBh)
  obtain ⟨e3, e4⟩ := split_append (X := A) (Y := B.dropLast) (dd := p.1) hA
    (Or.inr (by rw [hhd]; exact hBh))
  have hYne : convC B d p.2 false false ≠ [] := by
    intro he; rw [convC_eq_nil_iff] at he; exact hBne he
  rw [convC_cons_lad_none p (A ++ B.dropLast) d plev first force hl (by rw [e3, e4]; exact hc2),
    convC_cons_lad_none p (A ++ B) d plev first force hl (by rw [e1, e2]; exact hc1),
    e1, e2, e3, e4, ih]
  rw [dropLast_cons_ne (by simp), dropLast_cons_ne (by
    intro he
    obtain ⟨-, h2⟩ := List.append_eq_nil_iff.1 he
    exact hYne h2)]
  congr 2
  exact (List.dropLast_append_of_ne_nil hYne).symm

/-- 梯子ありで縮約あり、`Bq = []` の場合。`rest2` が 2 列以上なら縮約は消えない。 -/
theorem convC_dropLast_contr2 (p : ℕ × ℕ) (A B : PairSeq) (d plev : ℕ) (first force : Bool)
    (hA : ∀ x ∈ A, p.1 < x.1) (hBh : B = [] ∨ ¬ (p.1 < (B.headI).1))
    (hl : ladOf p.2 d plev first force = true)
    {rest2 : PairSeq}
    (hcc : contrLen p B (unitsLen p B) A = some (rest2, []))
    (hrd : rest2.dropLast ≠ [])
    (ih : convC (rest2.dropLast) (d + 1) p.2 false false
        = (convC rest2 (d + 1) p.2 false false).dropLast) :
    convC (p :: (A ++ B.dropLast)) d plev first force
      = (convC (p :: (A ++ B)) d plev first force).dropLast := by
  obtain ⟨q, r2, hdq, hq2, hq1, hAq, hBq, hr2ne, hr2d, hr2l⟩ := contrLen_spec hcc
  set k := unitsLen p B with hk
  set U := B.take k with hU
  have hkle : k ≤ B.length := unitsLen_le p B.length B (Nat.le_refl _)
  have hUlen : U.length = k := by rw [hU, List.length_take]; omega
  have hBsplit : B = U ++ (q :: r2) := by rw [hU, ← hdq, List.take_append_drop]
  have hr2eq : r2 = contrPre p U A ++ rest2 := by
    conv_lhs => rw [← List.takeWhile_append_dropWhile
      (p := fun x : ℕ × ℕ => decide (q.1 < x.1)) (l := r2)]
    rw [hAq, hBq]; simp
  have hr2deep : ∀ x ∈ r2, q.1 < x.1 := by
    intro x hx
    have hall : (r2.takeWhile fun x => q.1 < x.1) = r2 := by rw [hAq, ← hr2eq]
    have := List.mem_takeWhile_imp (p := fun x : ℕ × ℕ => decide (q.1 < x.1))
      (by rw [hall]; exact hx)
    simpa using this
  have hr2ne' : r2 ≠ [] := by
    intro he; rw [he] at hr2eq
    exact hr2ne (List.append_eq_nil_iff.1 hr2eq.symm).2
  have hr2drop : r2.dropLast = contrPre p U A ++ rest2.dropLast := by
    rw [hr2eq, List.dropLast_append_of_ne_nil hr2ne]
  have hqp : ¬ (q = p) := by intro he; rw [he] at hq2; omega
  have hUnits : Units p U := by rw [hU, hk]; exact units_take p B.length B (Nat.le_refl _)
  have hBdrop : B.dropLast = U ++ (q :: r2.dropLast) := by
    rw [hBsplit, List.dropLast_append_of_ne_nil (by simp), dropLast_cons_ne hr2ne']
  have hu' : unitsLen p (B.dropLast) = k := by
    rw [hBdrop, unitsLen_append_units hUnits (Or.inr ⟨by simp only [List.headI_cons]; omega,
      by simp only [List.headI_cons]; exact hqp⟩), hUlen]
  have hhd : (rest2.dropLast).headI = rest2.headI := by
    rcases rest2 with _ | ⟨b, _ | ⟨b2, R'⟩⟩
    · exact absurd rfl hr2ne
    · simp at hrd
    · rfl
  have htk : (B.dropLast).take k = U := by rw [hBdrop, ← hUlen, List.take_left]
  have hcc' : contrLen p (B.dropLast) (unitsLen p (B.dropLast)) A
      = some (rest2.dropLast, []) := by
    have hdk : (B.dropLast).drop k = q :: r2.dropLast := by
      rw [hBdrop, ← hUlen, List.drop_left]
    have hdeep : ∀ x ∈ r2.dropLast, q.1 < x.1 :=
      fun x hx => hr2deep x ((List.dropLast_sublist r2).subset hx)
    have hdeep' : ∀ x ∈ contrPre p U A ++ rest2.dropLast, q.1 < x.1 := by
      rw [← hr2drop]; exact hdeep
    obtain ⟨eA, eB⟩ := split_append (X := contrPre p U A ++ rest2.dropLast) (Y := [])
      (dd := q.1) hdeep' (Or.inl rfl)
    simp only [List.append_nil] at eA eB
    unfold contrLen
    rw [hu', hdk, htk]
    simp only [hr2drop, eA, eB]
    have hlen : (contrPre p U A ++ rest2.dropLast).take (contrPre p U A).length
        = contrPre p U A := by rw [List.take_left]
    have hdrp : (contrPre p U A ++ rest2.dropLast).drop (contrPre p U A).length
        = rest2.dropLast := by rw [List.drop_left]
    rw [if_pos ⟨hq2, hq1, hlen, by rw [hdrp]; exact hrd,
      by rw [hdrp, hhd]; exact hr2d, by rw [hdrp, hhd]; exact hr2l⟩, hdrp]
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := B) (dd := p.1) hA hBh
  have hBdh : B.dropLast = [] ∨ ¬ (p.1 < ((B.dropLast).headI).1) := by
    right
    rw [hBdrop]
    by_cases hUe : U = []
    · rw [hUe]; simp only [List.nil_append, List.headI_cons]; omega
    · rw [headI_append_left hUe]
      have hle : (U.headI).1 ≤ p.1 := by
        rcases hUnits.head_eq with h | h
        · exact absurd h hUe
        · rw [h]
      omega
  obtain ⟨e3, e4⟩ := split_append (X := A) (Y := B.dropLast) (dd := p.1) hA hBdh
  have hRne : convC rest2 (d + 1) p.2 false false ≠ [] := by
    intro he; rw [convC_eq_nil_iff] at he; exact hr2ne he
  rw [convC_cons_lad_some p (A ++ B.dropLast) d plev first force hl (by rw [e3, e4]; exact hcc'),
    convC_cons_lad_some p (A ++ B) d plev first force hl (by rw [e1, e2]; exact hcc),
    e1, e2, e3, e4, hu', ← hk, ← hU, htk, ih, convC_nil]
  simp only [List.append_nil]
  rw [dropLast_cons_ne (by simp), dropLast_cons_ne (by
    intro he
    simp only [List.append_eq_nil_iff] at he
    exact hRne he.2)]
  congr 2
  exact (List.dropLast_append_of_ne_nil hRne).symm

/-! ## 2.8 基本列の単調性 -/

open Three in
/-- 後ろに列を足すと `translate` は増える（`++` 版）。 -/
theorem translate_append_le (C : PairSeq) : ∀ D : PairSeq,
    translate C ≤o translate (C ++ D) := by
  intro D
  induction D using List.reverseRecOn with
  | nil => simp only [List.append_nil]; exact ole_refl _
  | append_singleton D m ih =>
      rw [← List.append_assoc]
      exact ole_trans ih (Or.inl (translate_snoc_increase (C ++ D) m))

/-- **基本列は添字について単調。** `n ≤ n'` なら `M⟦n⟧ ≤ M⟦n'⟧`。 -/
theorem oper_mono {M : PairSeq} {n n' : ℕ} (h : n ≤ n') :
    translate (M⟦n⟧) ≤o translate (M⟦n'⟧) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL, oper_eq_self_of_short n' hL]; exact ole_refl _
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz, oper_eq_pred_of_zero n' hL hz]; exact ole_refl _
  by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
  · rw [oper_bad_unfold n hL hz hp, oper_bad_unfold n' hL hz hp]
    set j0 := parent M (idx1 M (M.length - 1)) (M.length - 1)
    set j1 := M.length - 1
    set d0 := if 0 < idx1 M j1 then entry M 0 j1 - entry M 0 j0 else 0
    set d1 := if 1 < idx1 M j1 then entry M 1 j1 - entry M 1 j0 else 0
    set f := fun k => (List.range' j0 (j1 - j0)).map fun j =>
      ((entry M 0 j + k * d0 : ℕ), (entry M 1 j + k * d1 : ℕ)) with hf
    have hsplit : List.range n' = List.range n ++ List.range' n (n' - n) := by
      conv_lhs => rw [show n' = n + (n' - n) by omega]
      rw [List.range_eq_range', List.range_eq_range',
        ← List.range'_append (s := 0) (m := n) (n := n' - n) (step := 1)]
      simp
    rw [hsplit, List.flatMap_append, ← List.append_assoc]
    exact translate_append_le _ _
  · rw [oper_eq_pred_of_noParent n hL hz hp, oper_eq_pred_of_noParent n' hL hz hp]
    exact ole_refl _

/-! ## 3. 要 — REINDEX -/

/-- **REINDEX**: `conC` の像の基本列は、BMS 側の基本列と絡み合う。

`A` が標準形で長さ 2 以上、`n ≥ 1` のとき、DBMS の添字 `m ≥ 1` と
BMS の添字 `n' ≥ 1` があって

    (conC A)⟦m⟧ = conC (A⟦n'⟧)      … 像は展開で閉じている
    translate (A⟦n⟧) ≤o translate (A⟦n'⟧)   … BMS 側で追い越されない

`tools/dbms/reindex.py` が ≤8 列の BMS 標準形 44653 個・`m ≤ 5` で全数検査ずみ
（違反 0）。regime は succ / id / shift / contr の 4 つ。 -/
def ReindexD : Prop :=
  ∀ {A : PairSeq}, ST_PS A → 1 < A.length → ∀ n : ℕ, 1 ≤ n →
    ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧ (conC A)⟦m⟧ = conC (A⟦n'⟧)

/-! ## 4. 降下 -/

/-- 降下の本体: 標準形の像 `conC A` が DBMS 標準形なら、
`A` 以下の標準形の像もすべて DBMS 標準形。

`A` についての整礎帰納法（`wf_olt_ST_PS_holds`）。 -/
theorem ST_D_descend (H : ReindexD) :
    ∀ A : PairSeq, ST_PS A → ST_D (conC A) →
      ∀ M : PairSeq, ST_PS M → translate M ≤o translate A → ST_D (conC M) := by
  intro A
  induction A using (wf_olt_ST_PS_holds).induction with
  | _ A ih =>
    intro hA hSD M hM hle
    rcases hle with hlt | heq
    · -- `translate M <o translate A`: 一段降ろす
      have hL : 1 < A.length := by
        by_contra hL
        exact not_olt_len_one hM (by omega) hA hlt
      obtain ⟨n, hn, hMn⟩ := pss_cofinality_holds hA hM hlt
      obtain ⟨m, n', hm, hnn, heqC⟩ := H hA hL n hn
      have hn' : 1 ≤ n' := by omega
      have hmono : translate (A⟦n⟧) ≤o translate (A⟦n'⟧) := oper_mono hnn
      have hA' : ST_PS (A⟦n'⟧) := ST_PS.oper hA hn'
      have hSD' : ST_D (conC (A⟦n'⟧)) := by
        rw [← heqC]; exact ST_D.oper hSD hm
      have hlt' : translate (A⟦n'⟧) <o translate A := m_step_decreases hL hn'
      exact ih (A⟦n'⟧) ⟨hA', hA, hlt'⟩ hA' hSD' M hM (ole_trans hMn hmono)
    · -- `translate M = translate A`: `M = A`
      have : M = A := by
        by_contra hne
        rcases seqlex_total M A with he | hs | hs
        · exact hne he
        · exact olt_irrefl _ (heq ▸ (olt_ST_iff_seqlex hM hA hne).2 hs)
        · exact olt_irrefl _ (heq ▸ (olt_ST_iff_seqlex hA hM (Ne.symm hne)).2 hs)
      rw [this]; exact hSD

/-! ## 5. 主定理 -/

/-- **像は DBMS の標準形**（`ReindexD` を仮定）。 -/
theorem ST_D_conC (H : ReindexD) {M : PairSeq} (hM : ST_PS M) : ST_D (conC M) := by
  obtain ⟨v, hv⟩ := diag_cofinal hM
  exact ST_D_descend H (diagSeq 0 v) (ST_PS.diag v) (ST_D_conC_diagSeq v) M hM hv

/-! ## 2.85 場合 (b): 末尾列に親がないときの `dropLast`

`convC` の再帰の右端の道に沿って `dropLast` が可換になることを示す。
壊れるのは「梯子あり・縮約あり・`Bq = []` かつ `|rest2| = 1`」の 1 か所だけで、
そこでの末尾列は深さ `p.1 + 1`・段 `< p.2`。段が 0 なら行 0 の親が立って
「親がない」に矛盾するが、段が正の場合は局所の仮定だけでは排除できない。反例:

    M = (2,2)(2,1)(3,2)(3,1)   d = 2, plev = 1, first, ¬force
    blockok 2 / colOK / descOK / 末尾 (3,1) に親なし をすべて満たすが
    convC M = (2,1)(3,2)(3,1)、convC M.dropLast = (2,1)(3,2)(2,1)(3,2)

そこで「その形の縮約はどの接尾辞でも起きない」という仮定 `contrOK` を置く
（BMS 標準形では実測 0、`tools/dbms/badcontr.py` の 49 件はすべて段 0）。 -/

/-- 接尾辞の末尾列に親があれば、全体でも末尾列に親がある。 -/
theorem hasParent_last_append (G T : PairSeq) (hT : T ≠ [])
    (h : hasParent T (idx1 T (T.length - 1)) (T.length - 1)) :
    hasParent (G ++ T) (idx1 (G ++ T) ((G ++ T).length - 1)) ((G ++ T).length - 1) := by
  have hTl : 0 < T.length := List.length_pos_iff.mpr hT
  have hlen : (G ++ T).length - 1 = G.length + (T.length - 1) := by
    simp only [List.length_append]; omega
  rw [hlen, idx1_append_right]
  have hjl : T.length - 1 < T.length := by omega
  have hjl' : G.length + (T.length - 1) < (G ++ T).length := by
    simp only [List.length_append]; omega
  unfold idx1 at h ⊢
  by_cases hz : 0 < entry T 1 (T.length - 1)
  · rw [if_pos hz] at h ⊢
    rw [Wset.hasParent_one_iff hjl']
    rw [Wset.hasParent_one_iff hjl] at h
    obtain ⟨j0, hj1, hj2, hj3⟩ := h
    refine ⟨G.length + j0, by omega, (le0_append_right G T j0 (T.length - 1)).2 hj2, ?_⟩
    rw [entry_append_right, entry_append_right]; exact hj3
  · rw [if_neg hz] at h ⊢
    rw [Wset.hasParent_zero_iff hjl']
    rw [Wset.hasParent_zero_iff hjl] at h
    obtain ⟨k, hk1, hk2⟩ := h
    refine ⟨G.length + k, by omega, ?_⟩
    rw [entry_append_right, entry_append_right]; exact hk2

/-- 「末尾列に親がない」は末尾を含む接尾辞に遺伝する。 -/
theorem noParent_suffix {M T : PairSeq} (hT : T ≠ []) (hs : T <:+ M)
    (h : ¬ hasParent M (idx1 M (M.length - 1)) (M.length - 1)) :
    ¬ hasParent T (idx1 T (T.length - 1)) (T.length - 1) := by
  obtain ⟨G, hG⟩ := hs
  subst hG
  exact fun hpar => h (hasParent_last_append G T hT hpar)

/-- 縮約が「読み直しの先が 1 列だけ・その段が正・外の後続が空」という形で
発火することが、どの接尾辞でも起きない。`dropLast` が壊れる唯一の形。 -/
def contrOK (M : PairSeq) : Prop :=
  ∀ (t : ℕ) (p x : ℕ × ℕ) (r : PairSeq), M.drop t = p :: r →
    contrLen p (r.dropWhile fun q => p.1 < q.1)
      (unitsLen p (r.dropWhile fun q => p.1 < q.1))
      (r.takeWhile fun q => p.1 < q.1) = some ([x], []) → x.2 = 0

theorem drop_append_len (T : PairSeq) : ∀ (G : PairSeq) (t : ℕ),
    (G ++ T).drop (t + G.length) = T.drop t := by
  intro G
  induction G with
  | nil => intro t; simp
  | cons a G ih =>
    intro t
    have he : t + (a :: G).length = (t + G.length) + 1 := by
      simp only [List.length_cons]; omega
    rw [List.cons_append, he, List.drop_succ_cons, ih]

theorem contrOK_suffix {M T : PairSeq} (hs : T <:+ M) (h : contrOK M) : contrOK T := by
  obtain ⟨G, hG⟩ := hs
  subst hG
  intro t p x r hdr hcc
  refine h (t + G.length) p x r ?_ hcc
  rw [drop_append_len T G t]
  exact hdr

/-- 1 列だけのブロックで段が親の +1 でないなら、梯子は立たず像も 1 列。 -/
theorem convC_single_ne (c : ℕ × ℕ) (d plev : ℕ) (first force : Bool)
    (h : ¬ (c.2 = plev + 1)) :
    convC [c] d plev first force = [(ddOf c.2 d plev first force, c.2)] := by
  have hne : (c.2 == plev + 1) = false := by simpa using h
  have hl : ladOf c.2 d plev first force = false := by simp [ladOf, hne]
  rw [convC_cons_nolad c [] d plev first force hl]
  simp

/-- `B` が空で引数が 1 列のとき。段が親の +1 でなければ像も 1 列で `dropLast` が合う。 -/
theorem convC_dropLast_arg_single (p c : ℕ × ℕ) (d plev : ℕ) (first force : Bool)
    (hpc : p.1 < c.1) (hne : ¬ (c.2 = p.2 + 1)) :
    convC [p] d plev first force = (convC (p :: [c]) d plev first force).dropLast := by
  obtain ⟨e1, e2⟩ := split_append (X := ([c] : PairSeq)) (Y := ([] : PairSeq)) (dd := p.1)
    (by intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hpc) (Or.inl rfl)
  simp only [List.append_nil] at e1 e2
  have hn0 : ∀ X : PairSeq, contrLen p [] (unitsLen p []) X = none := by
    intro X; unfold contrLen; simp
  by_cases hl : ladOf p.2 d plev first force = true
  · rw [convC_cons_lad_none p [c] d plev first force hl (by rw [e1, e2]; exact hn0 _),
      convC_cons_lad_none p [] d plev first force hl
        (by simp only [List.takeWhile_nil, List.dropWhile_nil]; exact hn0 _),
      e1, e2]
    simp only [List.takeWhile_nil, List.dropWhile_nil, convC_nil, List.append_nil,
      List.nil_append]
    rw [convC_single_ne c (d + 2) p.2 true false hne]
    simp
  · rw [convC_cons_nolad p [c] d plev first force (by simpa using hl),
      convC_cons_nolad p [] d plev first force (by simpa using hl), e1, e2]
    simp only [List.takeWhile_nil, List.dropWhile_nil, convC_nil, List.append_nil]
    rw [convC_single_ne c (ddOf p.2 d plev first force + 1) p.2 true
      (first && (p.2 == plev)) hne]
    simp

/-- `convC_dropLast_arg` の、帰納法の仮定を必要な 2 つに絞った版。 -/
theorem convC_dropLast_arg' (p : ℕ × ℕ) (A : PairSeq) (d plev : ℕ) (first force : Bool)
    (hA : ∀ x ∈ A, p.1 < x.1) (hAne : A ≠ [])
    (ih1 : convC (A.dropLast) (d + 2) p.2 true false
        = (convC A (d + 2) p.2 true false).dropLast)
    (ih2 : convC (A.dropLast) (ddOf p.2 d plev first force + 1) p.2 true
             (first && (p.2 == plev))
        = (convC A (ddOf p.2 d plev first force + 1) p.2 true
             (first && (p.2 == plev))).dropLast) :
    convC (p :: A.dropLast) d plev first force
      = (convC (p :: A) d plev first force).dropLast := by
  have hAd : ∀ x ∈ A.dropLast, p.1 < x.1 :=
    fun x hx => hA x ((List.dropLast_sublist A).subset hx)
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := []) (dd := p.1) hA (Or.inl rfl)
  obtain ⟨e3, e4⟩ := split_append (X := A.dropLast) (Y := []) (dd := p.1) hAd (Or.inl rfl)
  simp only [List.append_nil] at e1 e2 e3 e4
  have hnone : contrLen p [] (unitsLen p []) A = none := by unfold contrLen; simp
  have hnone' : contrLen p [] (unitsLen p []) A.dropLast = none := by unfold contrLen; simp
  by_cases hl : ladOf p.2 d plev first force = true
  · have hXne : convC A (d + 2) p.2 true false ≠ [] := by
      intro he; rw [convC_eq_nil_iff] at he; exact hAne he
    rw [convC_cons_lad_none p A.dropLast d plev first force hl (by rw [e3, e4]; exact hnone'),
      convC_cons_lad_none p A d plev first force hl (by rw [e1, e2]; exact hnone),
      e1, e2, e3, e4, convC_nil]
    simp only [List.append_nil]
    rw [ih1, dropLast_cons_ne (by simp), dropLast_cons_ne hXne]
  · have hXne : convC A (ddOf p.2 d plev first force + 1) p.2 true
        (first && (p.2 == plev)) ≠ [] := by
      intro he; rw [convC_eq_nil_iff] at he; exact hAne he
    rw [convC_cons_nolad p A.dropLast d plev first force (by simpa using hl),
      convC_cons_nolad p A d plev first force (by simpa using hl),
      e1, e2, e3, e4, convC_nil]
    simp only [List.append_nil]
    rw [ih2, dropLast_cons_ne hXne]

/-- 縮約が起きないなら、末尾の 1 列を落としても起きない。 -/
theorem contrLen_dropLast_none (p : ℕ × ℕ) (A B : PairSeq)
    (h : contrLen p B (unitsLen p B) A = none) :
    contrLen p (B.dropLast) (unitsLen p (B.dropLast)) A = none := by
  rcases hd : contrLen p (B.dropLast) (unitsLen p (B.dropLast)) A with _ | ⟨R0, Q0⟩
  · rfl
  exfalso
  set D := B.dropLast with hD
  set k := unitsLen p D with hk
  obtain ⟨q, r2, hdq, hq2, hq1, hAq, hBq, hRne, hRd, hRl⟩ := contrLen_spec hd
  set U := D.take k with hU
  have hDne : D ≠ [] := by
    intro he; rw [he] at hdq; simp at hdq
  have hBne : B ≠ [] := by
    intro he; rw [hD, he] at hDne; simp at hDne
  have hklt : k < D.length := by
    have h1 : (D.drop k).length = D.length - k := List.length_drop
    rw [hdq] at h1
    simp only [List.length_cons] at h1
    omega
  have hUlen : U.length = k := by rw [hU, List.length_take]; omega
  have hUnits : Units p U := by rw [hU, hk]; exact units_take p D.length D (Nat.le_refl _)
  have hqp : ¬ (q = p) := by intro he; rw [he] at hq2; omega
  set z := B.getLast hBne with hz
  have hBz : B = D ++ [z] := by
    rw [hD, hz]; exact (List.dropLast_append_getLast hBne).symm
  have hDsplit : D = U ++ (q :: r2) := by rw [hU, ← hdq, List.take_append_drop]
  have hBsplit : B = U ++ (q :: (r2 ++ [z])) := by
    rw [hBz, hDsplit, List.append_assoc, List.cons_append]
  have hBtake : B.take k = U := by
    conv_lhs => rw [hBsplit]
    rw [← hUlen, List.take_left]
  have hBdrop : B.drop k = q :: (r2 ++ [z]) := by
    conv_lhs => rw [hBsplit]
    rw [← hUlen, List.drop_left]
  have hu : unitsLen p B = k := by
    conv_lhs => rw [hBsplit]
    rw [unitsLen_append_units hUnits
      (Or.inr ⟨by simp only [List.headI_cons]; omega,
        by simp only [List.headI_cons]; exact hqp⟩), hUlen]
  -- `r2 ++ [z]` の切り分け（3 通りとも同じ形にまとめる）
  have hkey : ∃ R V, ((r2 ++ [z]).takeWhile fun x => q.1 < x.1) = contrPre p U A ++ R ∧
      ((r2 ++ [z]).dropWhile fun x => q.1 < x.1) = V ∧ R ≠ [] ∧ R.headI = R0.headI := by
    by_cases hQ0 : Q0 = []
    · -- 兄弟が空: `r2` は全部深い
      have htw : (r2.takeWhile fun x => q.1 < x.1) = r2 := by
        conv_rhs => rw [← List.takeWhile_append_dropWhile
          (p := fun x : ℕ × ℕ => decide (q.1 < x.1)) (l := r2)]
        rw [hBq, hQ0, List.append_nil]
      have hall : ∀ x ∈ r2, q.1 < x.1 := by
        intro x hx
        have := List.mem_takeWhile_imp (p := fun x : ℕ × ℕ => decide (q.1 < x.1))
          (by rw [htw]; exact hx)
        simpa using this
      rw [htw] at hAq
      by_cases hzq : q.1 < z.1
      · have hallz : ∀ x ∈ r2 ++ [z], q.1 < x.1 := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hall x hx
          · simp only [List.mem_singleton] at hx; subst hx; exact hzq
        obtain ⟨f1, f2⟩ := split_append (X := r2 ++ [z]) (Y := ([] : PairSeq))
          (dd := q.1) hallz (Or.inl rfl)
        simp only [List.append_nil] at f1 f2
        refine ⟨R0 ++ [z], [], ?_, f2, by simp, ?_⟩
        · rw [f1, hAq, List.append_assoc]
        · rw [headI_append_left hRne]
      · obtain ⟨f1, f2⟩ := split_append (X := r2) (Y := ([z] : PairSeq))
          (dd := q.1) hall (Or.inr (by simpa using hzq))
        exact ⟨R0, [z], by rw [f1, hAq], f2, hRne, rfl⟩
    · -- 兄弟が空でない: 切れ目は `Q0` の頭のまま
      have hQ0h : ¬ (q.1 < (Q0.headI).1) := by
        rcases dropWhile_head_neg (a := q.1) r2 with hh | hh
        · rw [hBq] at hh; exact absurd hh hQ0
        · rw [hBq] at hh; exact hh
      have hdeep : ∀ x ∈ (r2.takeWhile fun x => q.1 < x.1), q.1 < x.1 := by
        intro x hx
        have := List.mem_takeWhile_imp (p := fun x : ℕ × ℕ => decide (q.1 < x.1)) hx
        simpa using this
      have hsp : r2 ++ [z] = (r2.takeWhile fun x => q.1 < x.1) ++ (Q0 ++ [z]) := by
        conv_lhs => rw [← List.takeWhile_append_dropWhile
          (p := fun x : ℕ × ℕ => decide (q.1 < x.1)) (l := r2)]
        rw [hBq, List.append_assoc]
      obtain ⟨f1, f2⟩ := split_append (X := r2.takeWhile fun x => q.1 < x.1)
        (Y := Q0 ++ [z]) (dd := q.1) hdeep
        (Or.inr (by rw [headI_append_left hQ0]; exact hQ0h))
      refine ⟨R0, Q0 ++ [z], ?_, ?_, hRne, rfl⟩
      · rw [hsp, f1, hAq]
      · rw [hsp, f2]
  obtain ⟨R, V, hW, hV, hRne', hRhd⟩ := hkey
  have ht : (contrPre p U A ++ R).take (contrPre p U A).length = contrPre p U A := by
    rw [List.take_left]
  have hdr : (contrPre p U A ++ R).drop (contrPre p U A).length = R := by
    rw [List.drop_left]
  have hsome : contrLen p B (unitsLen p B) A = some (R, V) := by
    unfold contrLen
    rw [hu, hBdrop, hBtake]
    simp only [hW, hV]
    rw [if_pos ⟨hq2, hq1, ht, by rw [hdr]; exact hRne',
      by rw [hdr, hRhd]; exact hRd, by rw [hdr, hRhd]; exact hRl⟩, hdr]
  rw [h] at hsome
  simp at hsome

theorem getLastD_snoc (G : PairSeq) (x dflt : ℕ × ℕ) : (G ++ [x]).getLastD dflt = x := by
  simp

/-- 頭 `p` に対する引数／後続の切り分けを、`takeWhile` を隠した形で取り出す。 -/
theorem split_takeWhile (p : ℕ × ℕ) (r : PairSeq) :
    ∃ A B : PairSeq, A ++ B = r ∧ (∀ x ∈ A, p.1 < x.1) ∧
      (B = [] ∨ ¬ (p.1 < (B.headI).1)) := by
  refine ⟨r.takeWhile fun q => p.1 < q.1, r.dropWhile fun q => p.1 < q.1,
    List.takeWhile_append_dropWhile, ?_, dropWhile_head_neg r⟩
  intro x hx
  have := List.mem_takeWhile_imp (p := fun q : ℕ × ℕ => decide (p.1 < q.1)) hx
  simpa using this

/-- **場合 (b)**: 末尾列に親がなければ `convC` は `dropLast` と可換
（壊れる 1 か所を除く仮定 `contrOK` のもとで）。 -/
theorem convC_dropLast_noParent_aux : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n → 1 < M.length →
    ∀ (d plev : ℕ) (first force : Bool),
      contrOK M →
      ¬ hasParent M (idx1 M (M.length - 1)) (M.length - 1) →
      convC (M.dropLast) d plev first force = (convC M d plev first force).dropLast := by
  intro n
  induction n with
  | zero =>
    intro M hM h1 _ _ _ _ _ _
    omega
  | succ n ih =>
    intro M hM h1 d plev first force hco hnp
    match M with
    | [] => simp at h1
    | p :: r =>
      obtain ⟨A, B, rfl, hAd, hBh⟩ := split_takeWhile p r
      by_cases hBe : B = []
      · -- 兄弟が空: 引数ブロック `A` に降りる
        subst hBe
        simp only [List.append_nil] at hco hnp ⊢
        have hAlen : A.length ≤ n := by
          simp only [List.length_cons, List.length_append, List.length_nil] at hM; omega
        have hApos : 1 < A.length + 1 := by
          simp only [List.length_cons, List.length_append, List.length_nil] at h1; omega
        have hAne : A ≠ [] := by
          intro he; rw [he] at hApos; simp at hApos
        by_cases hA1 : A.length = 1
        · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 hA1
          have hpc : p.1 < c.1 := hAd c (by simp)
          have he00 : entry (p :: [c] : PairSeq) 0 0 = p.1 := by simp [entry]
          have he01 : entry (p :: [c] : PairSeq) 0 1 = c.1 := by simp [entry]
          have he10 : entry (p :: [c] : PairSeq) 1 0 = p.2 := by simp [entry]
          have he11 : entry (p :: [c] : PairSeq) 1 1 = c.2 := by simp [entry]
          have hne : ¬ (c.2 = p.2 + 1) := by
            intro heq
            refine hnp ?_
            have hlen : (p :: [c] : PairSeq).length - 1 = 1 := by simp
            rw [hlen]
            have hidx : idx1 (p :: [c] : PairSeq) 1 = 1 := by
              unfold idx1; rw [if_pos (by rw [he11, heq]; omega)]
            rw [hidx, Wset.hasParent_one_iff (by simp)]
            refine ⟨0, by omega, ⟨by simp, by simp, ?_⟩, ?_⟩
            · exact Relation.ReflTransGen.single
                ⟨by simp, by simp, by omega, by rw [he00, he01]; exact hpc,
                  fun j hj => by omega⟩
            · rw [he10, he11, heq]; omega
          have hdl : (p :: [c] : PairSeq).dropLast = [p] := rfl
          rw [hdl]
          exact convC_dropLast_arg_single p c d plev first force hpc hne
        · have hA2 : 1 < A.length := by omega
          have hcoA : contrOK A := contrOK_suffix ⟨[p], rfl⟩ hco
          have hnpA : ¬ hasParent A (idx1 A (A.length - 1)) (A.length - 1) :=
            noParent_suffix hAne ⟨[p], rfl⟩ hnp
          rw [dropLast_cons_ne hAne]
          exact convC_dropLast_arg' p A d plev first force hAd hAne
            (ih A hAlen hA2 (d + 2) p.2 true false hcoA hnpA)
            (ih A hAlen hA2 (ddOf p.2 d plev first force + 1) p.2 true
              (first && (p.2 == plev)) hcoA hnpA)
      · -- 兄弟が空でない: 末尾列は `B` の中
        have hBhne : ¬ (p.1 < (B.headI).1) := hBh.resolve_left hBe
        have hABne : A ++ B ≠ [] := by
          intro he; exact hBe (List.append_eq_nil_iff.1 he).2
        rw [dropLast_cons_ne hABne, List.dropLast_append_of_ne_nil hBe]
        by_cases hB1 : B.length = 1
        · obtain ⟨w, rfl⟩ := List.length_eq_one_iff.1 hB1
          have hdl : ([w] : PairSeq).dropLast = [] := rfl
          rw [hdl, List.append_nil]
          have hw : ¬ (p.1 < w.1) := by simpa using hBhne
          rw [convC_dropLast_singleton p w A d plev first force hAd hw]
          simp
        · have hB2 : 1 < B.length := by
            have h0 : 0 < B.length := List.length_pos_iff.mpr hBe
            omega
          have hBlen : B.length ≤ n := by
            simp only [List.length_cons, List.length_append] at hM; omega
          have hBdlen : (B.dropLast).length = B.length - 1 := by simp
          have hBdne : B.dropLast ≠ [] := by
            intro he
            rw [he] at hBdlen
            simp only [List.length_nil] at hBdlen
            omega
          have hcoB : contrOK B := contrOK_suffix ⟨p :: A, rfl⟩ hco
          have hnpB : ¬ hasParent B (idx1 B (B.length - 1)) (B.length - 1) :=
            noParent_suffix hBe ⟨p :: A, rfl⟩ hnp
          have ihB := ih B hBlen hB2 d p.2 false false hcoB hnpB
          by_cases hl : ladOf p.2 d plev first force = true
          · rcases hcc : contrLen p B (unitsLen p B) A with _ | ⟨rest2, Bq⟩
            · exact convC_dropLast_lad_none p A B d plev first force hAd hBe hBdne hBhne hl
                hcc (contrLen_dropLast_none p A B hcc) ihB
            · obtain ⟨q, r2, hdq, hq2, hq1, hAq2, hBq2, hr2ne, hr2d, hr2l⟩ := contrLen_spec hcc
              have hr2suf : r2 <:+ B := ⟨B.take (unitsLen p B) ++ [q], by
                rw [List.append_assoc, List.singleton_append, ← hdq, List.take_append_drop]⟩
              have hBsuf : B <:+ (p :: (A ++ B)) := ⟨p :: A, rfl⟩
              by_cases hBqe : Bq = []
              · subst hBqe
                have hr2eq : r2 = contrPre p (B.take (unitsLen p B)) A ++ rest2 := by
                  conv_lhs => rw [← List.takeWhile_append_dropWhile
                    (p := fun x : ℕ × ℕ => decide (q.1 < x.1)) (l := r2)]
                  rw [hAq2, hBq2, List.append_nil]
                have hRsuf0 : rest2 <:+ r2 :=
                  ⟨contrPre p (B.take (unitsLen p B)) A, hr2eq.symm⟩
                have hRsuf : rest2 <:+ (p :: (A ++ B)) :=
                  (hRsuf0.trans hr2suf).trans hBsuf
                by_cases hR1 : rest2.length = 1
                · -- 壊れる形。`contrOK` から段は 0、そこで行 0 の親が立って矛盾
                  exfalso
                  obtain ⟨x, hrest⟩ := List.length_eq_one_iff.1 hR1
                  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := B) (dd := p.1) hAd hBh
                  have hx0 : x.2 = 0 := by
                    refine hco 0 p x (A ++ B) (by simp) ?_
                    rw [e2, e1, hcc, hrest]
                  have hx1 : x.1 = p.1 + 1 := by
                    rw [hrest] at hr2d; simpa using hr2d
                  have hBform : B = B.take (unitsLen p B)
                      ++ (q :: (contrPre p (B.take (unitsLen p B)) A ++ [x])) := by
                    conv_lhs => rw [← List.take_append_drop (unitsLen p B) B]
                    rw [hdq, hr2eq, hrest]
                  have hMform : (p :: (A ++ B) : PairSeq)
                      = (p :: (A ++ (B.take (unitsLen p B)
                          ++ (q :: contrPre p (B.take (unitsLen p B)) A)))) ++ [x] := by
                    conv_lhs => rw [hBform]
                    simp [List.append_assoc]
                  have hlastx : ((p :: (A ++ B) : PairSeq).getLastD (0, 0)) = x := by
                    rw [hMform]; exact getLastD_snoc _ x (0, 0)
                  have hMlen : 2 < (p :: (A ++ B) : PairSeq).length := by
                    simp only [List.length_cons, List.length_append]; omega
                  have hj : (p :: (A ++ B) : PairSeq).length - 1
                      < (p :: (A ++ B) : PairSeq).length := by omega
                  have hz : ¬ (0 < entry (p :: (A ++ B) : PairSeq) 1
                      ((p :: (A ++ B) : PairSeq).length - 1)) := by
                    rw [entry_last, hlastx, hx0]; omega
                  have hidx : idx1 (p :: (A ++ B) : PairSeq)
                      ((p :: (A ++ B) : PairSeq).length - 1) = 0 := by
                    unfold idx1; rw [if_neg hz]
                  refine hnp ?_
                  rw [hidx]
                  refine hasParent0_of_exists hj ⟨0, by omega, ?_⟩
                  rw [entry_zero0, entry_last0, hlastx]
                  simp only [List.headI_cons]
                  omega
                · have h0 : 0 < rest2.length := List.length_pos_iff.mpr hr2ne
                  have hRdlen : (rest2.dropLast).length = rest2.length - 1 := by simp
                  have hRd : rest2.dropLast ≠ [] := by
                    intro he
                    rw [he] at hRdlen
                    simp only [List.length_nil] at hRdlen
                    omega
                  have hRlen : rest2.length ≤ n := by
                    have := (contrLen_lt hcc).1; omega
                  exact convC_dropLast_contr2 p A B d plev first force hAd hBh hl hcc hRd
                    (ih rest2 hRlen (by omega) (d + 1) p.2 false false
                      (contrOK_suffix hRsuf hco) (noParent_suffix hr2ne hRsuf hnp))
              · have hQsuf0 : Bq <:+ r2 :=
                  ⟨r2.takeWhile fun x => q.1 < x.1, by
                    rw [← hBq2]; exact List.takeWhile_append_dropWhile⟩
                have hQsuf : Bq <:+ (p :: (A ++ B)) :=
                  (hQsuf0.trans hr2suf).trans hBsuf
                have ihQ : convC (Bq.dropLast) d p.2 false false
                    = (convC Bq d p.2 false false).dropLast := by
                  by_cases hQ1 : Bq.length = 1
                  · obtain ⟨w, hw⟩ := List.length_eq_one_iff.1 hQ1
                    rw [hw]
                    have hdl : ([w] : PairSeq).dropLast = [] := rfl
                    rw [hdl, convC_nil, convC_single]
                    simp
                  · have h0 : 0 < Bq.length := List.length_pos_iff.mpr hBqe
                    have hQlen : Bq.length ≤ n := by
                      have := (contrLen_lt hcc).2; omega
                    exact ih Bq hQlen (by omega) d p.2 false false
                      (contrOK_suffix hQsuf hco) (noParent_suffix hBqe hQsuf hnp)
                exact convC_dropLast_contr p A B d plev first force hAd hBh hl hcc hBqe ihQ
          · exact convC_dropLast_tail p A B d plev first force hAd hBe hBdne hBhne
              (by simpa using hl) ihB

/-- 計画書の形（`blockok` / `colOK` / `descOK` / `bd ≤ d` つき）。
本体はそれらを使わない `convC_dropLast_noParent_aux`。 -/
theorem convC_dropLast_noParent : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n → 1 < M.length →
    ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd M → colOK M → descOK M → bd ≤ d → contrOK M →
      ¬ hasParent M (idx1 M (M.length - 1)) (M.length - 1) →
      convC (M.dropLast) d plev first force = (convC M d plev first force).dropLast :=
  fun n M hM h1 _ d plev first force _ _ _ _ hco hnp =>
    convC_dropLast_noParent_aux n M hM h1 d plev first force hco hnp

/-- **場合 (b) の REINDEX**: 末尾列に親がなければ `m = 1`, `n' = n` で取れる。 -/
theorem reindexD_noParent {M : PairSeq} (n : ℕ) (hL : 1 < M.length) (hco : contrOK M)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (hnp : ¬ hasParent M (idx1 M (M.length - 1)) (M.length - 1)) :
    ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧ (conC M)⟦m⟧ = conC (M⟦n'⟧) := by
  refine ⟨1, n, Nat.le_refl 1, Nat.le_refl n, ?_⟩
  rw [oper_one (conC_length_ge_two hL),
    oper_eq_pred_of_noParent n (by omega) hz hnp, Pred, if_neg (by omega)]
  unfold conC
  exact (convC_dropLast_noParent_aux M.length M (Nat.le_refl _) hL 0 0 true false hco hnp).symm

/-! ## 2.85 段 > 0 での証人（場合 (c) の段 > 0）

`convC_exists_shallow` の段 > 0 版。証人は「`le0` の鎖の上で段が末尾より小さい列」。
道具は 3 つ:

* `rtg_lt_of_floor` / `le0_ge_of_append` … **床の補題**。深さ `bd` の柱を
  行 0 の鎖は越えられないので、BMS 側の証人は必ず末尾と同じブロックの中にある。
* `shallow1_step` … 接尾辞に証人が移れば、像の接尾辞にも移る。
* `shallow1_nil` … 兄弟が空なら、節点の列そのものが証人になれる。
-/

/-- **床の補題**（鎖の形）。`g` 番の深さが `bd` で、その手前が全部 `bd` 以上なら、
`g` より手前から始まる行 0 の鎖は `g` に届かない。 -/
theorem rtg_lt_of_floor {M : PairSeq} {g bd : ℕ}
    (hlow : ∀ i, i < g → bd ≤ entry M 0 i) (hpiv : entry M 0 g = bd) :
    ∀ {b c}, Relation.ReflTransGen (nextrel0 M) b c → b < g → c < g := by
  intro b c h
  induction h with
  | refl => exact id
  | @tail x z hbx hxz ihx =>
    intro hb
    have hx : x < g := ihx hb
    have hlx := hlow x hx
    by_contra hz
    have hgz : g ≤ z := by omega
    have h4 := hxz.2.2.2.1
    rcases Nat.eq_or_lt_of_le hgz with he | hlt
    · rw [← he, hpiv] at h4; omega
    · have h5 := hxz.2.2.2.2 g ⟨hx, hlt⟩
      rw [hpiv] at h5; omega

/-- **床の補題**（`le0` の形）。`T` の頭が深さ `bd`、`G` が全部深さ `bd` 以上なら、
`T` の中への `le0` の始点は `T` の中にある。 -/
theorem le0_ge_of_append {G T : PairSeq} {bd : ℕ} (hTne : T ≠ [])
    (hlowG : ∀ c ∈ G, bd ≤ c.1) (hhead : (T.headI).1 = bd)
    {k j : ℕ} (h : le0 (G ++ T) k j) (hj : G.length ≤ j) : G.length ≤ k := by
  by_contra hk
  have hk' : k < G.length := by omega
  have hlow : ∀ i, i < G.length → bd ≤ entry (G ++ T) 0 i := by
    intro i hi
    rw [entry, if_pos rfl, getD_append_left hi]
    exact hlowG _ (getD_mem hi)
  have hpiv : entry (G ++ T) 0 G.length = bd := by
    rw [entry, if_pos rfl, getD_append_right (Nat.le_refl _), Nat.sub_self, ← hhead]
    match T with
    | [] => exact absurd rfl hTne
    | c :: t => rfl
  exact absurd (rtg_lt_of_floor hlow hpiv h.2.2 hk') (by omega)

/-- 像の末尾の段は元の末尾の段（`convC_getLast_level` の `entry` 版）。 -/
theorem convC_entry_last (M : PairSeq) (d plev : ℕ) (first force : Bool) :
    entry (convC M d plev first force) 1 ((convC M d plev first force).length - 1)
      = entry M 1 (M.length - 1) := by
  rw [entry_last, entry_last, convC_getLast_level M.length M (Nat.le_refl _)]

/-- 証人が接尾辞 `T` の中にあるなら、像の接尾辞 `Y` の中の証人に移せる。 -/
theorem shallow1_step {G T C Y : PairSeq} (hT : T ≠ []) (hY : Y ≠ [])
    {k : ℕ} (hkge : G.length ≤ k)
    (hk1 : le0 (G ++ T) k ((G ++ T).length - 1))
    (hk2 : entry (G ++ T) 1 k < entry (G ++ T) 1 ((G ++ T).length - 1))
    (hrec : ∀ k0, le0 T k0 (T.length - 1) → entry T 1 k0 < entry T 1 (T.length - 1) →
      ∃ k', le0 Y k' (Y.length - 1) ∧ entry Y 1 k' < entry Y 1 (Y.length - 1)) :
    ∃ k', le0 (C ++ Y) k' ((C ++ Y).length - 1) ∧
      entry (C ++ Y) 1 k' < entry (C ++ Y) 1 ((C ++ Y).length - 1) := by
  have hTlen : 0 < T.length := List.length_pos_of_ne_nil hT
  have hYlen : 0 < Y.length := List.length_pos_of_ne_nil hY
  have hlen : (G ++ T).length - 1 = G.length + (T.length - 1) := by
    simp only [List.length_append]; omega
  obtain ⟨k0, rfl⟩ : ∃ k0, k = G.length + k0 := ⟨k - G.length, by omega⟩
  rw [hlen, le0_append_right] at hk1
  rw [hlen, entry_append_right, entry_append_right] at hk2
  obtain ⟨k', h1, h2⟩ := hrec k0 hk1 hk2
  have hlenD : (C ++ Y).length - 1 = C.length + (Y.length - 1) := by
    simp only [List.length_append]; omega
  refine ⟨C.length + k', ?_, ?_⟩
  · rw [hlenD]; exact le0_append_right_of C Y h1
  · rw [hlenD, entry_append_right, entry_append_right]; exact h2

/-- 節点の列そのものが証人になる形。`cols` の頭は後ろ全部より浅い。 -/
theorem shallow1_headw {cols X : PairSeq} (hne : cols ≠ [])
    (hdeep : ∀ x ∈ cols.tail ++ X, (cols.headI).1 < x.1)
    (hlt : (cols.headI).2 < entry (cols ++ X) 1 ((cols ++ X).length - 1)) :
    ∃ k', le0 (cols ++ X) k' ((cols ++ X).length - 1) ∧
      entry (cols ++ X) 1 k' < entry (cols ++ X) 1 ((cols ++ X).length - 1) := by
  obtain ⟨c, cs, rfl⟩ : ∃ c cs, cols = c :: cs := by
    match cols with
    | [] => exact absurd rfl hne
    | c :: cs => exact ⟨c, cs, rfl⟩
  simp only [List.tail_cons, List.headI_cons] at hdeep hlt ⊢
  rw [List.cons_append] at hlt ⊢
  refine ⟨0, le0_head hdeep _ (by simp), ?_⟩
  have he : entry (c :: (cs ++ X)) 1 0 = c.2 := by
    unfold entry; rw [if_neg one_ne_zero]; rfl
  rw [he]; exact hlt

/-- 兄弟が空のときの 1 段。証人が節点なら `cols` の頭、引数の中なら `X` へ帰納。 -/
theorem shallow1_nil {p : ℕ × ℕ} {A cols X : PairSeq} (hne : cols ≠ [])
    (hlv : (cols.headI).2 ≤ p.2)
    (hdeep : ∀ x ∈ cols.tail ++ X, (cols.headI).1 < x.1)
    (hlast : entry (cols ++ X) 1 ((cols ++ X).length - 1)
      = entry (p :: A) 1 ((p :: A).length - 1))
    (hXne : A ≠ [] → X ≠ [])
    {k : ℕ}
    (hk1 : le0 (p :: A) k ((p :: A).length - 1))
    (hk2 : entry (p :: A) 1 k < entry (p :: A) 1 ((p :: A).length - 1))
    (hrec : ∀ k0, le0 A k0 (A.length - 1) → entry A 1 k0 < entry A 1 (A.length - 1) →
      ∃ k', le0 X k' (X.length - 1) ∧ entry X 1 k' < entry X 1 (X.length - 1)) :
    ∃ k', le0 (cols ++ X) k' ((cols ++ X).length - 1) ∧
      entry (cols ++ X) 1 k' < entry (cols ++ X) 1 ((cols ++ X).length - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine shallow1_headw hne hdeep ?_
    rw [hlast]
    have hpe : entry (p :: A) 1 0 = p.2 := by unfold entry; rw [if_neg one_ne_zero]; rfl
    rw [hpe] at hk2
    omega
  · have hAne : A ≠ [] := by
      intro he
      rw [he] at hk1
      have hlt := hk1.1
      simp only [List.length_cons, List.length_nil] at hlt
      omega
    have hpA : (p :: A) = [p] ++ A := rfl
    rw [hpA] at hk1 hk2
    exact shallow1_step hAne (hXne hAne) (by simpa using hk) hk1 hk2 hrec

/-- **段 > 0 のときの証人の存在**（場合 (c) の段 > 0）。`B` の中に
「`le0` の鎖の上で段が末尾より小さい列」があれば、像の中にもある。 -/
theorem convC_exists_shallow1 : ∀ (n : ℕ) (B : PairSeq), B.length ≤ n →
    ∀ (bd d plev : ℕ) (first force : Bool), blockok bd B →
    (∃ k, le0 B k (B.length - 1) ∧ entry B 1 k < entry B 1 (B.length - 1)) →
    ∃ k', le0 (convC B d plev first force) k' ((convC B d plev first force).length - 1) ∧
      entry (convC B d plev first force) 1 k'
        < entry (convC B d plev first force) 1 ((convC B d plev first force).length - 1) := by
  intro n
  induction n with
  | zero =>
    intro B hB bd d plev first force _ hw
    obtain ⟨k, hk1, -⟩ := hw
    have hBe : B = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hBe] at hk1
    exact absurd hk1.1 (by simp)
  | succ n ih =>
    intro B hB bd d plev first force hb hw
    match B with
    | [] =>
      obtain ⟨k, hk1, -⟩ := hw
      exact absurd hk1.1 (by simp)
    | p :: r =>
      obtain ⟨k, hk1, hk2⟩ := hw
      have hp : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨yy, rfl⟩ : ∃ yy, p = (bd, yy) := ⟨p.2, by rw [← hp]⟩
      have hmem : ∀ c ∈ ((bd, yy) : ℕ × ℕ) :: r, bd ≤ c.1 := hb.2.1
      have hlastD0 := convC_entry_last (((bd, yy) : ℕ × ℕ) :: r) d plev first force
      set A := r.takeWhile (fun q => ((bd, yy) : ℕ × ℕ).1 < q.1) with hA
      set B' := r.dropWhile (fun q => ((bd, yy) : ℕ × ℕ).1 < q.1) with hB'
      have hAB : r = A ++ B' := by rw [hA, hB', List.takeWhile_append_dropWhile]
      have hcons : (((bd, yy) : ℕ × ℕ) :: r) = (((bd, yy) : ℕ × ℕ) :: A) ++ B' := by
        rw [hAB]; rfl
      have hlr : r.length ≤ n := by simp only [List.length_cons] at hB; omega
      have hlA : A.length ≤ n := by
        have h1 := (List.takeWhile_sublist
          (fun q : ℕ × ℕ => ((bd, yy) : ℕ × ℕ).1 < q.1) (l := r)).length_le
        rw [hA]; omega
      have hlB' : B'.length ≤ n := by
        have h1 := List.length_dropWhile_le (fun q : ℕ × ℕ => ((bd, yy) : ℕ × ℕ).1 < q.1) r
        rw [hB']; omega
      have hbA : blockok (bd + 1) A := by rw [hA]; exact blockok_arg hb
      have hbB' : blockok bd B' := by rw [hB']; exact blockok_tail hb
      have hmemA : ∀ c ∈ ((bd, yy) : ℕ × ℕ) :: A, bd ≤ c.1 := by
        intro c hc
        exact hmem c (by rw [hcons]; exact List.mem_append_left _ hc)
      by_cases hl : ladOf ((bd, yy) : ℕ × ℕ).2 d plev first force = true
      · -- 梯子あり
        have hly : yy = plev + 1 := by
          have h1 := hl
          simp only [ladOf, Bool.and_eq_true, beq_iff_eq] at h1
          exact h1.1.2
        rcases hcc : contrLen ((bd, yy) : ℕ × ℕ) B'
            (unitsLen ((bd, yy) : ℕ × ℕ) B') A with _ | ⟨rest2, Bq⟩
        · -- 縮約なし
          set X := convC A (d + 2) ((bd, yy) : ℕ × ℕ).2 true false with hX
          set Y := convC B' d ((bd, yy) : ℕ × ℕ).2 false false with hY
          have hout : convC (((bd, yy) : ℕ × ℕ) :: r) d plev first force
              = ((d, plev) :: (d + 1, yy) :: X) ++ Y := by
            rw [convC_cons_lad_none ((bd, yy) : ℕ × ℕ) r d plev first force hl
              (by rw [← hA, ← hB']; exact hcc)]
            rw [← hA, ← hB', ← hX, ← hY]
            simp only [List.cons_append]
          have hXdeep : ∀ x ∈ X, d < x.1 := by
            intro x hx
            rw [hX] at hx
            have h1 := convC_ge' A (d + 2) ((bd, yy) : ℕ × ℕ).2 true false x hx
            omega
          rw [hout] at hlastD0 ⊢
          by_cases hBe : B' = []
          · -- 兄弟なし
            have hYn : Y = [] := by rw [hY, hBe, convC_nil]
            have hrA : r = A := by rw [hAB, hBe, List.append_nil]
            rw [hYn, List.append_nil] at hlastD0 ⊢
            rw [hrA] at hk1 hk2 hlastD0
            have hshape : ((d, plev) :: (d + 1, yy) :: X)
                = [((d, plev) : ℕ × ℕ), ((d + 1, yy) : ℕ × ℕ)] ++ X := rfl
            rw [hshape] at hlastD0 ⊢
            refine shallow1_nil (p := ((bd, yy) : ℕ × ℕ)) (A := A) (by simp)
              (by show plev ≤ yy; omega) ?_ hlastD0 ?_ hk1 hk2 ?_
            · intro x hx
              show d < x.1
              simp only [List.tail_cons, List.singleton_append, List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact Nat.lt_succ_self d
              · exact hXdeep x hx
            · intro hAne he
              rw [hX, convC_eq_nil_iff] at he
              exact hAne he
            · intro k0 h1 h2
              rw [hX]
              exact ih A hlA (bd + 1) (d + 2) ((bd, yy) : ℕ × ℕ).2 true false hbA ⟨k0, h1, h2⟩
          · -- 兄弟あり
            have hYne : Y ≠ [] := by
              rw [hY]; intro he; rw [convC_eq_nil_iff] at he; exact hBe he
            rw [hcons] at hk1 hk2
            have hkge : (((bd, yy) : ℕ × ℕ) :: A).length ≤ k := by
              refine le0_ge_of_append (bd := bd) hBe hmemA (hbB'.1 hBe) hk1 ?_
              have h1 : 0 < B'.length := List.length_pos_of_ne_nil hBe
              simp only [List.length_append]; omega
            refine shallow1_step hBe hYne hkge hk1 hk2 ?_
            intro k0 h1 h2
            rw [hY]
            exact ih B' hlB' bd d ((bd, yy) : ℕ × ℕ).2 false false hbB' ⟨k0, h1, h2⟩
        · -- 縮約あり
          obtain ⟨q, r2, hdq, hq2, hq1, hAq, hBq, hr2ne, hr2d, hr2l⟩ := contrLen_spec hcc
          have hq1' : q.1 = bd := hq1
          have hq2' : q.2 = plev := by
            have : q.2 + 1 = yy := hq2
            omega
          have hr2d' : (rest2.headI).1 = bd + 1 := hr2d
          set U := B'.take (unitsLen ((bd, yy) : ℕ × ℕ) B') with hU
          set pre := contrPre ((bd, yy) : ℕ × ℕ) U A with hpre
          have hB'split : B' = U ++ (q :: r2) := by
            rw [hU, ← hdq, List.take_append_drop]
          have hr2split : r2 = (pre ++ rest2) ++ Bq := by
            conv_lhs => rw [← List.takeWhile_append_dropWhile
              (p := fun x : ℕ × ℕ => decide (q.1 < x.1)) (l := r2)]
            rw [hAq, hBq]
          have hAqmem : ∀ c ∈ pre ++ rest2, bd < c.1 := by
            intro c hc
            rw [← hAq] at hc
            have h1 := List.mem_takeWhile_imp hc
            simp only [decide_eq_true_eq] at h1
            omega
          set G0 := (((bd, yy) : ℕ × ℕ) :: A) ++ U with hG0
          set Gq := G0 ++ [q] with hGq
          set G2 := Gq ++ pre with hG2
          have hdec0 : (((bd, yy) : ℕ × ℕ) :: r) = G0 ++ (q :: ((pre ++ rest2) ++ Bq)) := by
            rw [hG0, hcons, hB'split, ← hr2split]
            simp only [List.append_assoc, List.cons_append]
          have hdec2 : (((bd, yy) : ℕ × ℕ) :: r) = (G2 ++ rest2) ++ Bq := by
            rw [hG2, hGq, hdec0]
            simp only [List.append_assoc, List.cons_append, List.nil_append]
          set X := convC A (d + 2) ((bd, yy) : ℕ × ℕ).2 true false with hX
          set U' := convC U (d + 1) ((bd, yy) : ℕ × ℕ).2 false false with hU'
          set R2' := convC rest2 (d + 1) ((bd, yy) : ℕ × ℕ).2 false false with hR2'
          set Y'' := convC Bq d ((bd, yy) : ℕ × ℕ).2 false false with hY''
          have hout : convC (((bd, yy) : ℕ × ℕ) :: r) d plev first force
              = (d, plev) :: (d + 1, yy) :: (((X ++ U') ++ R2') ++ Y'') := by
            rw [convC_cons_lad_some ((bd, yy) : ℕ × ℕ) r d plev first force hl
              (by rw [← hA, ← hB']; exact hcc)]
          have hXdeep : ∀ x ∈ X, d + 1 < x.1 := by
            intro x hx
            rw [hX] at hx
            have h1 := convC_ge' A (d + 2) ((bd, yy) : ℕ × ℕ).2 true false x hx
            omega
          have hU'deep : ∀ x ∈ U', d < x.1 := by
            intro x hx
            rw [hU'] at hx
            have h1 := convC_ge' U (d + 1) ((bd, yy) : ℕ × ℕ).2 false false x hx
            omega
          have hR2'deep : ∀ x ∈ R2', d < x.1 := by
            intro x hx
            rw [hR2'] at hx
            have h1 := convC_ge' rest2 (d + 1) ((bd, yy) : ℕ × ℕ).2 false false x hx
            omega
          have hlrest2 : rest2.length ≤ n := by
            have h1 := (contrLen_lt hcc).1; omega
          have hlBq : Bq.length ≤ n := by
            have h1 := (contrLen_lt hcc).2; omega
          rw [hout] at hlastD0 ⊢
          by_cases hbqe : Bq = []
          · -- `Bq` が空: 末尾は `R2'` の中
            have hY''n : Y'' = [] := by rw [hY'', hbqe, convC_nil]
            have hR2ne : R2' ≠ [] := by
              rw [hR2']; intro he; rw [convC_eq_nil_iff] at he; exact hr2ne he
            have hdec0' : (((bd, yy) : ℕ × ℕ) :: r) = G0 ++ (q :: (pre ++ rest2)) := by
              rw [hdec0, hbqe, List.append_nil]
            have hkge0 : G0.length ≤ k := by
              rw [hdec0'] at hk1
              refine le0_ge_of_append (bd := bd) (by simp) ?_
                (by show q.1 = bd; exact hq1') hk1 ?_
              · intro c hc
                exact hmem c (by rw [hdec0']; exact List.mem_append_left _ hc)
              · simp only [List.length_append, List.length_cons]; omega
            rw [hY'', hbqe, convC_nil, List.append_nil] at hlastD0 ⊢
            rcases Nat.eq_or_lt_of_le hkge0 with hkeq | hklt
            · -- 証人は `q`: 像では影の列
              have hshape : ((d, plev) :: (d + 1, yy) :: ((X ++ U') ++ R2'))
                  = [((d, plev) : ℕ × ℕ)] ++ ((d + 1, yy) :: ((X ++ U') ++ R2')) := rfl
              rw [hshape] at hlastD0 ⊢
              refine shallow1_headw (by simp) ?_ ?_
              · intro x hx
                show d < x.1
                simp only [List.tail_cons, List.nil_append, List.mem_cons,
                  List.mem_append] at hx
                rcases hx with rfl | hx
                · exact Nat.lt_succ_self d
                · rcases hx with hx | hx
                  · rcases hx with hx | hx
                    · have := hXdeep x hx; omega
                    · exact hU'deep x hx
                  · exact hR2'deep x hx
              · simp only [List.headI_cons]
                rw [hlastD0, hdec0']
                rw [hdec0'] at hk2
                have hke : k = G0.length + 0 := by omega
                rw [hke, entry_append_right] at hk2
                have hq2e : entry (q :: (pre ++ rest2)) 1 0 = q.2 := by
                  unfold entry; rw [if_neg one_ne_zero]; rfl
                rw [hq2e, hq2'] at hk2
                exact hk2
            · -- 証人は `rest2` の中
              have hdec2' : (((bd, yy) : ℕ × ℕ) :: r) = G2 ++ rest2 := by
                rw [hdec2, hbqe, List.append_nil]
              have hdecq : (((bd, yy) : ℕ × ℕ) :: r) = Gq ++ (pre ++ rest2) := by
                rw [hdec2', hG2, List.append_assoc]
              have hGqlen : Gq.length = G0.length + 1 := by
                rw [hGq]; simp only [List.length_append, List.length_singleton]
              rw [hdecq] at hk1 hk2
              obtain ⟨k0, hk0e⟩ : ∃ k0, k = Gq.length + k0 := ⟨k - Gq.length, by omega⟩
              subst hk0e
              have hWne : (pre ++ rest2) ≠ [] := by
                intro he
                simp only [List.append_eq_nil_iff] at he
                exact hr2ne he.2
              have hWlen : 0 < (pre ++ rest2).length := List.length_pos_of_ne_nil hWne
              have hlen : (Gq ++ (pre ++ rest2)).length - 1
                  = Gq.length + ((pre ++ rest2).length - 1) := by
                simp only [List.length_append] at hWlen ⊢; omega
              rw [hlen, le0_append_right] at hk1
              rw [hlen, entry_append_right, entry_append_right] at hk2
              have hprege : pre.length ≤ k0 := by
                refine le0_ge_of_append (bd := bd + 1) hr2ne ?_ hr2d' hk1 ?_
                · intro c hc
                  have := hAqmem c (List.mem_append_left _ hc); omega
                · have h1 : 0 < rest2.length := List.length_pos_of_ne_nil hr2ne
                  simp only [List.length_append]; omega
              have hshape : ((d, plev) :: (d + 1, yy) :: ((X ++ U') ++ R2'))
                  = ((d, plev) :: (d + 1, yy) :: (X ++ U')) ++ R2' := by
                simp only [List.cons_append]
              rw [hshape] at hlastD0 ⊢
              have hbrest2 : blockok (bd + 1) rest2 := by
                refine ⟨fun _ => hr2d', fun c hc => ?_, ?_⟩
                · have := hAqmem c (List.mem_append_right _ hc); omega
                · have hdrop : (((bd, yy) : ℕ × ℕ) :: r).drop G2.length = rest2 := by
                    conv_lhs => rw [hdec2']
                    simp
                  have h1 := steps1_drop G2.length hb.2.2
                  rwa [hdrop] at h1
              refine shallow1_step hr2ne hR2ne hprege hk1 hk2 ?_
              intro k1 h1 h2
              rw [hR2']
              exact ih rest2 hlrest2 (bd + 1) (d + 1) ((bd, yy) : ℕ × ℕ).2 false false
                hbrest2 ⟨k1, h1, h2⟩
          · -- `Bq` が空でない: 末尾は `Y''` の中
            have hY''ne : Y'' ≠ [] := by
              rw [hY'']; intro he; rw [convC_eq_nil_iff] at he; exact hbqe he
            have hBqhead : (Bq.headI).1 = bd := by
              have h1 := dropWhile_head_neg (a := q.1) r2
              rw [hBq] at h1
              rcases h1 with h1 | h1
              · exact absurd h1 hbqe
              · have h2 : bd ≤ (Bq.headI).1 :=
                  hmem _ (by rw [hdec2]; exact List.mem_append_right _ (headI_mem' hbqe))
                omega
            have hbBq : blockok bd Bq := by
              have hdrop : (((bd, yy) : ℕ × ℕ) :: r).drop ((G2 ++ rest2).length) = Bq := by
                conv_lhs => rw [hdec2]
                simp
              have h1 := blockok_drop (n := (G2 ++ rest2).length) hb (by rw [hdrop]; exact fun _ => hBqhead)
              rwa [hdrop] at h1
            rw [hdec2] at hk1 hk2
            have hkge : (G2 ++ rest2).length ≤ k := by
              refine le0_ge_of_append (bd := bd) hbqe ?_ hBqhead hk1 ?_
              · intro c hc
                exact hmem c (by rw [hdec2]; exact List.mem_append_left _ hc)
              · have h1 : 0 < Bq.length := List.length_pos_of_ne_nil hbqe
                simp only [List.length_append]; omega
            have hshape : ((d, plev) :: (d + 1, yy) :: (((X ++ U') ++ R2') ++ Y''))
                = ((d, plev) :: (d + 1, yy) :: ((X ++ U') ++ R2')) ++ Y'' := by
              simp only [List.cons_append]
            rw [hshape] at hlastD0 ⊢
            refine shallow1_step hbqe hY''ne hkge hk1 hk2 ?_
            intro k1 h1 h2
            rw [hY'']
            exact ih Bq hlBq bd d ((bd, yy) : ℕ × ℕ).2 false false hbBq ⟨k1, h1, h2⟩
      · -- 梯子なし
        have hl' : ladOf ((bd, yy) : ℕ × ℕ).2 d plev first force = false := by simpa using hl
        set dd := ddOf ((bd, yy) : ℕ × ℕ).2 d plev first force with hdd
        set X := convC A (dd + 1) ((bd, yy) : ℕ × ℕ).2 true
          (first && (((bd, yy) : ℕ × ℕ).2 == plev)) with hX
        set Y := convC B' d ((bd, yy) : ℕ × ℕ).2 false false with hY
        have hout : convC (((bd, yy) : ℕ × ℕ) :: r) d plev first force
            = ((dd, yy) :: X) ++ Y := by
          rw [convC_cons_nolad ((bd, yy) : ℕ × ℕ) r d plev first force hl']
          rw [← hA, ← hB', ← hdd, ← hX, ← hY]
          simp only [List.cons_append]
        have hXdeep : ∀ x ∈ X, dd < x.1 := by
          intro x hx
          rw [hX] at hx
          have h1 := convC_ge' A (dd + 1) ((bd, yy) : ℕ × ℕ).2 true
            (first && (((bd, yy) : ℕ × ℕ).2 == plev)) x hx
          omega
        rw [hout] at hlastD0 ⊢
        by_cases hBe : B' = []
        · -- 兄弟なし
          have hYn : Y = [] := by rw [hY, hBe, convC_nil]
          have hrA : r = A := by rw [hAB, hBe, List.append_nil]
          rw [hYn, List.append_nil] at hlastD0 ⊢
          rw [hrA] at hk1 hk2 hlastD0
          have hshape : (((dd, yy) : ℕ × ℕ) :: X) = [((dd, yy) : ℕ × ℕ)] ++ X := rfl
          rw [hshape] at hlastD0 ⊢
          refine shallow1_nil (p := ((bd, yy) : ℕ × ℕ)) (A := A) (by simp) (by simp) ?_
            hlastD0 ?_ hk1 hk2 ?_
          · intro x hx
            show dd < x.1
            simp only [List.tail_cons, List.nil_append] at hx
            exact hXdeep x hx
          · intro hAne he
            rw [hX, convC_eq_nil_iff] at he
            exact hAne he
          · intro k0 h1 h2
            rw [hX]
            exact ih A hlA (bd + 1) (dd + 1) ((bd, yy) : ℕ × ℕ).2 true
              (first && (((bd, yy) : ℕ × ℕ).2 == plev)) hbA ⟨k0, h1, h2⟩
        · -- 兄弟あり
          have hYne : Y ≠ [] := by
            rw [hY]; intro he; rw [convC_eq_nil_iff] at he; exact hBe he
          rw [hcons] at hk1 hk2
          have hkge : (((bd, yy) : ℕ × ℕ) :: A).length ≤ k := by
            refine le0_ge_of_append (bd := bd) hBe hmemA (hbB'.1 hBe) hk1 ?_
            have h1 : 0 < B'.length := List.length_pos_of_ne_nil hBe
            simp only [List.length_append]; omega
          refine shallow1_step hBe hYne hkge hk1 hk2 ?_
          intro k0 h1 h2
          rw [hY]
          exact ih B' hlB' bd d ((bd, yy) : ℕ × ℕ).2 false false hbB' ⟨k0, h1, h2⟩

/-- BMS 側で末尾列に行 1 の親があれば、証人が 1 つ取れる。 -/
theorem exists_shallow1_of_hasParent {B : PairSeq} (h : hasParent B 1 (B.length - 1)) :
    ∃ k, le0 B k (B.length - 1) ∧ entry B 1 k < entry B 1 (B.length - 1) := by
  obtain ⟨j0, hj0, -⟩ := h
  have h1 : nextrel1 B j0 (B.length - 1) := by
    have h2 : nextR B 1 j0 (B.length - 1) := hj0
    unfold nextR at h2
    rw [if_neg one_ne_zero] at h2
    exact h2
  exact ⟨j0, h1.2.2.2.2.1, h1.2.2.2.1⟩

/-- **場合 (c) の段 > 0（完成形）**: BMS 側に証人があれば、
`convC B` の像の上で展開は局所化できる。 -/
theorem oper_append_convC1 (A B : PairSeq) (n : ℕ) {bd d plev : ℕ} {first force : Bool}
    (hb : blockok bd B)
    (hw : ∃ k, le0 B k (B.length - 1) ∧ entry B 1 k < entry B 1 (B.length - 1))
    (hT : 2 ≤ (convC B d plev first force).length)
    (hz : ¬ (entry (convC B d plev first force)
              0 ((convC B d plev first force).length - 1) = 0 ∧
             entry (convC B d plev first force)
              1 ((convC B d plev first force).length - 1) = 0))
    (hi : idx1 (convC B d plev first force)
            ((convC B d plev first force).length - 1) ≠ 0)
    (hp : hasParent (A ++ convC B d plev first force)
            (idx1 (convC B d plev first force) ((convC B d plev first force).length - 1))
            (A.length + ((convC B d plev first force).length - 1))) :
    (A ++ convC B d plev first force)⟦n⟧ = A ++ (convC B d plev first force)⟦n⟧ := by
  obtain ⟨k', hk1, hk2⟩ :=
    convC_exists_shallow1 B.length B (Nat.le_refl _) bd d plev first force hb hw
  exact oper_append_of_shallow1 A _ n hT hz hi hp hk1 hk2

/-- 系: BMS 側の末尾列に行 1 の親があるときの形。 -/
theorem oper_append_convC1' (A B : PairSeq) (n : ℕ) {bd d plev : ℕ} {first force : Bool}
    (hb : blockok bd B) (hpB : hasParent B 1 (B.length - 1))
    (hT : 2 ≤ (convC B d plev first force).length)
    (hz : ¬ (entry (convC B d plev first force)
              0 ((convC B d plev first force).length - 1) = 0 ∧
             entry (convC B d plev first force)
              1 ((convC B d plev first force).length - 1) = 0))
    (hi : idx1 (convC B d plev first force)
            ((convC B d plev first force).length - 1) ≠ 0)
    (hp : hasParent (A ++ convC B d plev first force)
            (idx1 (convC B d plev first force) ((convC B d plev first force).length - 1))
            (A.length + ((convC B d plev first force).length - 1))) :
    (A ++ convC B d plev first force)⟦n⟧ = A ++ (convC B d plev first force)⟦n⟧ :=
  oper_append_convC1 A B n hb (exists_shallow1_of_hasParent hpB) hT hz hi hp

/-! ## 2.9 場合 (d): 親が節点そのもの（段 0）

親が節点（index 0）なら `G = []` で、`M⟦n⟧` は `M.dropLast` のコピー `n` 個。
段 0（`idx1 = 0`、`d0 = 0`）なら素直な繰り返しになるので、`oper_repeat` /
`conC_run_top` がそのまま使える。DBMS 側も `idx1_conC` から段 0 で、
親は先頭の `(0,0)`。要るのは 2 つ:

* `convC_getLast_min` … 末尾列が最浅で段 0 なら、像の末尾列の深さはちょうど `d`
  （これで DBMS 側の親が先頭の `(0,0)` だとわかる）
* `convC_dropLast_noParent_aux` … 引数ブロック `A` の末尾列には親がないので
  （`A` の列は全部末尾と同じかそれより深い）、`dropLast` が可換
-/

/-- 列は添字で読める。 -/
theorem entry_of_mem {L : PairSeq} {c : ℕ × ℕ} (h : c ∈ L) :
    ∃ i, i < L.length ∧ entry L 0 i = c.1 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  refine ⟨i, hi, ?_⟩
  unfold entry
  rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- 空でない末尾の `getLastD` は頭を無視する。 -/
theorem getLastD_cons_ne (a : ℕ × ℕ) {l : PairSeq} (h : l ≠ []) (dflt : ℕ × ℕ) :
    (a :: l).getLastD dflt = l.getLastD dflt :=
  getLastD_append_right (A := [a]) h dflt

/-- **末尾列がいちばん浅く、その段が 0 なら、像の末尾列の深さはちょうど `d`。**

右端の道に沿った帰納。`B = []`（兄弟が空）なら引数も空でなければならない
（引数の列は節点より深いのに、末尾は最浅だから）。縮約の枝でも同じ理由で
`Bq = []` は起きない（`rest2` の列は節点より深い）。 -/
theorem convC_getLast_min : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n → M ≠ [] →
    (∀ c ∈ M, (M.getLastD (0, 0)).1 ≤ c.1) → (M.getLastD (0, 0)).2 = 0 →
    ∀ (d plev : ℕ) (first force : Bool),
      ((convC M d plev first force).getLastD (0, 0)).1 = d := by
  intro n
  induction n with
  | zero =>
    intro M hM hne _ _ d plev first force
    exact absurd (List.eq_nil_of_length_eq_zero (by omega)) hne
  | succ n ih =>
    intro M hM hne hmin hlev d plev first force
    match M with
    | [] => exact absurd rfl hne
    | p :: r =>
      set A := r.takeWhile (fun q => p.1 < q.1) with hA
      set B := r.dropWhile (fun q => p.1 < q.1) with hB
      have hAB : r = A ++ B := by rw [hA, hB, List.takeWhile_append_dropWhile]
      have hlA : A.length ≤ n := by
        have := (List.takeWhile_sublist (fun q : ℕ × ℕ => p.1 < q.1) (l := r)).length_le
        simp only [List.length_cons] at hM; rw [hA]; omega
      have hlB : B.length ≤ n := by
        have := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) r
        simp only [List.length_cons] at hM; rw [hB]; omega
      have hMlast : (p :: r).getLastD (0, 0)
          = if B = [] then (if A = [] then p else A.getLastD (0, 0)) else B.getLastD (0, 0) := by
        by_cases hBe : B = []
        · rw [if_pos hBe, hAB, hBe, List.append_nil]
          by_cases hAe : A = []
          · rw [if_pos hAe, hAe]; simp
          · rw [if_neg hAe, List.getLastD_cons]
            exact getLastD_ne_nil_indep hAe _ _
        · rw [if_neg hBe, hAB, List.getLastD_cons, getLastD_append_right hBe]
          exact getLastD_ne_nil_indep hBe _ _
      have hple : ((p :: r).getLastD (0, 0)).1 ≤ p.1 := hmin p (by simp)
      by_cases hBe : B = []
      · -- 兄弟が空 → 引数も空（末尾が最浅だから）
        have hAe : A = [] := by
          by_contra hAe
          have hlast : (p :: r).getLastD (0, 0) = A.getLastD (0, 0) := by
            rw [hMlast, if_pos hBe, if_neg hAe]
          have hmemA : A.getLastD (0, 0) ∈ A := getLastD_mem hAe _
          rw [hA] at hmemA
          have h1 : p.1 < (A.getLastD (0, 0)).1 := by
            simpa using List.mem_takeWhile_imp hmemA
          rw [hlast] at hple
          omega
        have hp2 : p.2 = 0 := by
          rw [hMlast, if_pos hBe, if_pos hAe] at hlev; exact hlev
        have hl0 : ladOf p.2 d plev first force = false := by
          rw [hp2]; simp [ladOf]
        have hdd : ddOf p.2 d plev first force = d := by
          unfold ddOf
          rw [if_neg (by rw [hl0]; simp), if_neg (by rw [hp2]; simp)]
        rw [convC_cons_nolad p r d plev first force hl0, ← hA, ← hB, hAe, hBe]
        simp [hdd]
      · have hlastB : (p :: r).getLastD (0, 0) = B.getLastD (0, 0) := by
          rw [hMlast, if_neg hBe]
        have hmemB : ∀ c ∈ B, c ∈ p :: r := by
          intro c hc
          rw [hAB]
          exact List.mem_cons_of_mem _ (List.mem_append_right _ hc)
        have hminB : ∀ c ∈ B, (B.getLastD (0, 0)).1 ≤ c.1 := by
          intro c hc; rw [← hlastB]; exact hmin c (hmemB c hc)
        have hlevB : (B.getLastD (0, 0)).2 = 0 := by rw [← hlastB]; exact hlev
        have key : ∀ (cs : PairSeq) (dA : ℕ) (fA gA : Bool),
            ((cs ++ (convC A dA p.2 fA gA
              ++ convC B d p.2 false false)).getLastD (0, 0)).1 = d := by
          intro cs dA fA gA
          rw [← List.append_assoc, getLastD_append_cases,
            if_neg (by simp only [convC_eq_nil_iff]; exact hBe)]
          exact ih B hlB hBe hminB hlevB d p.2 false false
        by_cases hl : ladOf p.2 d plev first force = true
        · rcases hcc : contrLen p B (unitsLen p B) A with _ | ⟨rest2, Bq⟩
          · rw [convC_cons_lad_none p r d plev first force hl (by rw [← hA, ← hB]; exact hcc)]
            rw [← hA, ← hB, ← List.cons_append, ← List.cons_append]
            exact key [(d, plev), (d + 1, p.2)] (d + 2) true false
          · obtain ⟨q, r2, hdq, hq2, hq1, hAq, hBq, hr2ne, hr2d, hr2l⟩ := contrLen_spec hcc
            have hlbq : Bq.length ≤ n := by
              have := (contrLen_lt hcc).2; omega
            have hBsplit : B = B.take (unitsLen p B) ++ (q :: r2) := by
              rw [← hdq, List.take_append_drop]
            have hr2split : r2 = (contrPre p (B.take (unitsLen p B)) A ++ rest2) ++ Bq := by
              conv_lhs => rw [← List.takeWhile_append_dropWhile
                (p := fun x : ℕ × ℕ => decide (q.1 < x.1)) (l := r2)]
              rw [hAq, hBq]
            have hMl2 : (p :: r).getLastD (0, 0)
                = if Bq = [] then rest2.getLastD (0, 0) else Bq.getLastD (0, 0) := by
              rw [hMlast, if_neg hBe]
              conv_lhs => rw [hBsplit]
              rw [getLastD_append_right (by simp) (0, 0), List.getLastD_cons]
              have hr2ne' : r2 ≠ [] := by
                intro he
                rw [he] at hr2split
                have hc : (contrPre p (B.take (unitsLen p B)) A ++ rest2) ++ Bq = [] :=
                  hr2split.symm
                simp only [List.append_eq_nil_iff] at hc
                exact hr2ne hc.1.2
              rw [getLastD_ne_nil_indep hr2ne' _ (0, 0), hr2split, getLastD_append_cases]
              by_cases hbq : Bq = []
              · rw [if_pos hbq, if_pos hbq, getLastD_append_right hr2ne]
              · rw [if_neg hbq, if_neg hbq]
            have hbqne : Bq ≠ [] := by
              intro hbq
              have hmem : rest2.getLastD (0, 0) ∈ rest2 := getLastD_mem hr2ne _
              have hmem2 : rest2.getLastD (0, 0) ∈ r2.takeWhile (fun x => q.1 < x.1) := by
                rw [hAq]; exact List.mem_append_right _ hmem
              have hqlt : q.1 < (rest2.getLastD (0, 0)).1 := by
                simpa using List.mem_takeWhile_imp hmem2
              rw [hMl2, if_pos hbq] at hple
              omega
            have hmemBq : ∀ c ∈ Bq, c ∈ p :: r := by
              intro c hc
              have h1 : c ∈ r2 := by rw [hr2split]; exact List.mem_append_right _ hc
              have h2 : c ∈ B := by
                rw [hBsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1)
              exact hmemB c h2
            have hlastBq : (p :: r).getLastD (0, 0) = Bq.getLastD (0, 0) := by
              rw [hMl2, if_neg hbqne]
            have hminBq : ∀ c ∈ Bq, (Bq.getLastD (0, 0)).1 ≤ c.1 := by
              intro c hc; rw [← hlastBq]; exact hmin c (hmemBq c hc)
            have hlevBq : (Bq.getLastD (0, 0)).2 = 0 := by rw [← hlastBq]; exact hlev
            rw [convC_cons_lad_some p r d plev first force hl (by rw [← hA, ← hB]; exact hcc)]
            rw [← hA, ← hB]
            simp only [← List.cons_append, ← List.append_assoc]
            rw [getLastD_append_cases, if_neg (by simp only [convC_eq_nil_iff]; exact hbqne)]
            exact ih Bq hlbq hbqne hminBq hlevBq d p.2 false false
        · rw [convC_cons_nolad p r d plev first force (by simpa using hl)]
          rw [← hA, ← hB, ← List.cons_append]
          exact key [(ddOf p.2 d plev first force, p.2)]
            (ddOf p.2 d plev first force + 1) true (first && (p.2 == plev))

/-- **親が先頭の列で段が 0 なら、基本列は `dropLast` の素直な繰り返し。** -/
theorem oper_repeat_root {M : PairSeq} (n : ℕ) (hL : 1 < M.length)
    (hlev : entry M 1 (M.length - 1) = 0)
    (hnr : nextrel0 M 0 (M.length - 1)) :
    M⟦n⟧ = (List.replicate n M.dropLast).flatten := by
  have hi1 : idx1 M (M.length - 1) = 0 := by
    rw [idx1, if_neg (by rw [hlev]; omega)]
  have ha : 0 < entry M 0 (M.length - 1) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hnr.2.2.2.1
  have hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0) := by
    rintro ⟨h1, -⟩; omega
  have hp : hasParent M 0 (M.length - 1) :=
    hasParent0_of_exists (by omega) ⟨0, hnr.2.2.1, hnr.2.2.2.1⟩
  have hnR : nextR M 0 0 (M.length - 1) := by
    unfold nextR; rw [if_pos rfl]; exact hnr
  have hj0 : parent M 0 (M.length - 1) = 0 := hp.unique (parent_nextR hp) hnR
  have hmap : (List.range' 0 (M.length - 1 - 0)).map
      (fun j => ((entry M 0 j : ℕ), (entry M 1 j : ℕ))) = M.dropLast := by
    rw [range'_map_entry M (Nat.zero_le (M.length - 1)) (by omega), List.drop_zero,
      List.dropLast_eq_take]
  have h := oper_repeat (M := M) n (by omega) hz (by rw [hi1]; exact hp) hi1
  rw [hi1, hj0, hmap] at h
  rw [h]
  simp

/-- 先頭が `(0,0)`、残りが全部深いなら `conC` は先頭を切り出す。 -/
theorem conC_cons_zero {L : PairSeq} (hL : ∀ c ∈ L, 0 < c.1) :
    conC (((0, 0) : ℕ × ℕ) :: L) = ((0, 0) : ℕ × ℕ) :: convC L 1 0 true false := by
  have hL' : ∀ c ∈ L, ((0, 0) : ℕ × ℕ).1 < c.1 := by
    intro c hc; simpa using hL c hc
  obtain ⟨e1, e2⟩ := split_append (X := L) (Y := []) (dd := ((0, 0) : ℕ × ℕ).1) hL' (Or.inl rfl)
  simp only [List.append_nil] at e1 e2
  have hnl : ladOf ((0, 0) : ℕ × ℕ).2 0 0 true false = false := by simp [ladOf]
  have hde : ddOf ((0, 0) : ℕ × ℕ).2 0 0 true false = 0 := by
    unfold ddOf
    rw [if_neg (by rw [hnl]; simp), if_neg (by simp)]
  rw [conC, convC_cons_nolad ((0, 0) : ℕ × ℕ) L 0 0 true false hnl, hde, e1, e2]
  simp only [Bool.and_true, beq_self_eq_true, convC_nil, List.append_nil, Nat.zero_add]
  rw [convC_force (L := L) (d := 1) (plev := 0) (by omega) true false]

/-- **場合 (d) の段 0**: 先頭が `(0,0)`、末尾列の親が先頭で段が 0 なら、
`m = n`, `n' = n` で像の基本列が一致する。 -/
theorem reindexD_node0 {M : PairSeq} (n : ℕ) (hL : 1 < M.length)
    (hco : contrOK M) (hhd : M.headI = ((0, 0) : ℕ × ℕ))
    (hlev : entry M 1 (M.length - 1) = 0)
    (hnr : nextrel0 M 0 (M.length - 1)) :
    (conC M)⟦n⟧ = conC (M⟦n⟧) := by
  obtain ⟨A, hMA⟩ : ∃ A, M = ((0, 0) : ℕ × ℕ) :: A := by
    match M with
    | [] => simp at hL
    | p :: A =>
      refine ⟨A, ?_⟩
      have hp : p = ((0, 0) : ℕ × ℕ) := hhd
      rw [hp]
  have hMlen : M.length = A.length + 1 := by rw [hMA]; simp
  have hAne : A ≠ [] := by
    intro he; rw [he] at hMlen; simp at hMlen; omega
  have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
  have hshift : ∀ i : ℕ, entry M i (M.length - 1) = entry A i (A.length - 1) := by
    intro i
    have h1 : M.length - 1 = (A.length - 1) + 1 := by omega
    rw [h1, hMA, entry_cons_succ]
  -- `A` の列はどれも末尾列と同じかそれより深い
  have hAidx : ∀ i, i < A.length → entry M 0 (M.length - 1) ≤ entry A 0 i := by
    intro i hi
    have he : entry A 0 i = entry M 0 (i + 1) := by rw [hMA, entry_cons_succ]
    rcases Nat.lt_or_ge (i + 1) (M.length - 1) with hlt | hge
    · rw [he]; exact hnr.2.2.2.2 (i + 1) ⟨by omega, hlt⟩
    · have : i + 1 = M.length - 1 := by omega
      rw [he, this]
  have hAdeep : ∀ c ∈ A, entry M 0 (M.length - 1) ≤ c.1 := by
    intro c hc
    obtain ⟨i, hi, hei⟩ := entry_of_mem hc
    rw [← hei]; exact hAidx i hi
  have ha : 0 < entry M 0 (M.length - 1) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hnr.2.2.2.1
  have hA0 : ∀ c ∈ A, 0 < c.1 := fun c hc => Nat.lt_of_lt_of_le ha (hAdeep c hc)
  have hR0 : ∀ c ∈ A.dropLast, 0 < c.1 :=
    fun c hc => hA0 c ((List.dropLast_sublist A).subset hc)
  -- 像の形
  have hconCM : conC M = ((0, 0) : ℕ × ℕ) :: convC A 1 0 true false := by
    rw [hMA]; exact conC_cons_zero hA0
  have hXne : convC A 1 0 true false ≠ [] := by
    rw [ne_eq, convC_eq_nil_iff]; exact hAne
  -- `A` に対する `convC_getLast_min` の仮定
  have hminA : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1 := by
    intro c hc
    have : (A.getLastD (0, 0)).1 = entry M 0 (M.length - 1) := by
      rw [hshift 0, entry_last0]
    rw [this]; exact hAdeep c hc
  have hlevA : (A.getLastD (0, 0)).2 = 0 := by
    rw [← entry_last, ← hshift 1]; exact hlev
  -- `A` の末尾列には親がない（どの列も末尾と同じかそれより深いから）
  have hlastA : entry A 0 (A.length - 1) = entry M 0 (M.length - 1) := (hshift 0).symm
  have hiA : idx1 A (A.length - 1) = 0 := by
    rw [idx1, if_neg (by rw [← hshift 1, hlev]; omega)]
  have hnpA : ¬ hasParent A (idx1 A (A.length - 1)) (A.length - 1) := by
    rw [hiA]
    rintro ⟨j0, hj0, -⟩
    have hj0' : nextrel0 A j0 (A.length - 1) := by
      have h : nextR A 0 j0 (A.length - 1) := hj0
      unfold nextR at h; rw [if_pos rfl] at h; exact h
    have h1 : entry M 0 (M.length - 1) ≤ entry A 0 j0 := hAidx j0 hj0'.1
    have h2 : entry A 0 j0 < entry A 0 (A.length - 1) := hj0'.2.2.2.1
    rw [hlastA] at h2
    omega
  -- `dropLast` の可換
  have hX : convC (A.dropLast) 1 0 true false = (convC A 1 0 true false).dropLast := by
    by_cases hA2 : 1 < A.length
    · have hsuf : A <:+ M := by rw [hMA]; exact List.suffix_cons _ _
      exact convC_dropLast_noParent_aux A.length A (Nat.le_refl _) hA2 1 0 true false
        (contrOK_suffix hsuf hco) hnpA
    · obtain ⟨lp, hlp⟩ : ∃ lp, A = [lp] := List.length_eq_one_iff.1 (by omega)
      have hlp2 : lp.2 = 0 := by
        have := hlevA
        rw [hlp] at this
        simpa using this
      have hnl : ladOf lp.2 1 0 true false = false := by rw [hlp2]; simp [ladOf]
      rw [hlp]
      simp [convC_cons_nolad lp [] 1 0 true false hnl]
  -- DBMS 側の親も先頭の (0,0)
  have hNlen : (conC M).length = (convC A 1 0 true false).length + 1 := by
    rw [hconCM]; simp
  have hNle : 1 < (conC M).length := conC_length_ge_two hL
  have hNlast : (conC M).getLastD (0, 0) = (convC A 1 0 true false).getLastD (0, 0) := by
    rw [hconCM]; exact getLastD_cons_ne _ hXne (0, 0)
  have hN0 : entry (conC M) 0 ((conC M).length - 1) = 1 := by
    rw [entry_last0, hNlast]
    exact convC_getLast_min A.length A (Nat.le_refl _) hAne hminA hlevA 1 0 true false
  have hN1 : entry (conC M) 1 ((conC M).length - 1) = 0 := by
    rw [entry_last, conC_getLast_level, ← entry_last]; exact hlev
  have hhd0 : entry (conC M) 0 0 = 0 := by
    rw [entry_zero0, hconCM]; rfl
  have hNnr : nextrel0 (conC M) 0 ((conC M).length - 1) := by
    refine ⟨by omega, by omega, by omega, by rw [hhd0, hN0]; omega, ?_⟩
    rintro j ⟨hj1, hj2⟩
    rw [hN0]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj' : j' < (convC A 1 0 true false).length := by omega
    have hmem : (convC A 1 0 true false).getD j' (0, 0) ∈ convC A 1 0 true false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
      simpa using List.getElem_mem hj'
    have h1 := convC_ge' A 1 0 true false _ hmem
    rw [hconCM, entry_cons_succ, entry, if_pos rfl]
    exact h1
  -- 両側を組み立てる
  have hbms : M⟦n⟧ = (List.replicate n M.dropLast).flatten :=
    oper_repeat_root n hL hlev hnr
  have hdbms : (conC M)⟦n⟧ = (List.replicate n (conC M).dropLast).flatten :=
    oper_repeat_root n hNle hN1 hNnr
  have hMdl : M.dropLast = ((0, 0) : ℕ × ℕ) :: A.dropLast := by
    rw [hMA, dropLast_cons_ne hAne]
  have hdl : (conC M).dropLast = ((0, 0) : ℕ × ℕ) :: convC (A.dropLast) 1 0 true false := by
    rw [hconCM, dropLast_cons_ne hXne, hX]
  rw [hdbms, hbms, hdl, hMdl, conC_run_top (A.dropLast) hR0 n]

/-- 場合 (d) の段 0 は `ReindexD` の形（`m = n`, `n' = n`）を満たす。 -/
theorem reindexD_node0_shape {M : PairSeq} (n : ℕ) (hn : 1 ≤ n) (hL : 1 < M.length)
    (hco : contrOK M) (hhd : M.headI = ((0, 0) : ℕ × ℕ))
    (hlev : entry M 1 (M.length - 1) = 0)
    (hnr : nextrel0 M 0 (M.length - 1)) :
    ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧ (conC M)⟦m⟧ = conC (M⟦n'⟧) :=
  ⟨n, n, hn, Nat.le_refl n, reindexD_node0 n hL hco hhd hlev hnr⟩


/-! ## 2.95 場合 (d) の段 > 0 に向けて: 引数ブロックの `dropLast`

段 > 0（`idx1 = 1`）で親が節点（index 0）なら、**引数ブロック `A = M.tail` の
末尾列には親がない**。行 0 の鎖は接尾辞から全体へ持ち上がる（`le0_append_right_of`）
ので、`A` の中の親候補は `M` でも行 1 の祖先になり、`nextrel1 M 0 (|M|-1)` の
最小性（`0 < j` かつ `le0 M j (|M|-1)` なら `entry M 1 (|M|-1) ≤ entry M 1 j`）に
反するからである。したがって (b) の `convC_dropLast_noParent_aux` がそのまま効く。 -/

/-- **場合 (d) の段 > 0**: 引数ブロックの末尾列には親がない。 -/
theorem noParent_arg_node1 {M A : PairSeq} (hMA : M = ((0, 0) : ℕ × ℕ) :: A) (hAne : A ≠ [])
    (hlev : 0 < entry M 1 (M.length - 1))
    (hnr : nextrel1 M 0 (M.length - 1)) :
    ¬ hasParent A (idx1 A (A.length - 1)) (A.length - 1) := by
  have hMlen : M.length = A.length + 1 := by rw [hMA]; simp
  have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
  have hshift : ∀ i : ℕ, entry M i (M.length - 1) = entry A i (A.length - 1) := by
    intro i
    have h1 : M.length - 1 = (A.length - 1) + 1 := by omega
    rw [h1, hMA, entry_cons_succ]
  have hlift : ∀ j0 j1 : ℕ, le0 A j0 j1 → le0 M (j0 + 1) (j1 + 1) := by
    intro j0 j1 h
    have h2 := le0_append_right_of [((0, 0) : ℕ × ℕ)] A h
    have e0 : ([((0, 0) : ℕ × ℕ)]).length + j0 = j0 + 1 := by
      simp only [List.length_cons, List.length_nil]; omega
    have e1 : ([((0, 0) : ℕ × ℕ)]).length + j1 = j1 + 1 := by
      simp only [List.length_cons, List.length_nil]; omega
    rw [e0, e1] at h2
    rw [hMA]
    exact h2
  have hiA : idx1 A (A.length - 1) = 1 := by
    rw [idx1, if_pos (by rw [← hshift 1]; exact hlev)]
  rw [hiA]
  rintro ⟨j0, hj0, -⟩
  have hj0' : nextrel1 A j0 (A.length - 1) := by
    have h : nextR A 1 j0 (A.length - 1) := hj0
    unfold nextR at h; rw [if_neg (by omega)] at h; exact h
  have hle : le0 M (j0 + 1) ((A.length - 1) + 1) := hlift j0 (A.length - 1) hj0'.2.2.2.2.1
  have hidx : (A.length - 1) + 1 = M.length - 1 := by omega
  rw [hidx] at hle
  have hmin := hnr.2.2.2.2.2 (j0 + 1) ⟨by omega, hle⟩
  have hent : entry M 1 (j0 + 1) = entry A 1 j0 := by rw [hMA, entry_cons_succ]
  rw [hent, hshift 1] at hmin
  have := hj0'.2.2.2.1
  omega

/-- 場合 (d) の段 > 0 でも `dropLast` は可換（引数ブロックの側）。 -/
theorem convC_dropLast_node1 {M A : PairSeq} (hMA : M = ((0, 0) : ℕ × ℕ) :: A)
    (hA2 : 1 < A.length) (hco : contrOK M)
    (hlev : 0 < entry M 1 (M.length - 1))
    (hnr : nextrel1 M 0 (M.length - 1)) :
    convC (A.dropLast) 1 0 true false = (convC A 1 0 true false).dropLast :=
  convC_dropLast_noParent_aux A.length A (Nat.le_refl _) hA2 1 0 true false
    (contrOK_suffix (by rw [hMA]; exact List.suffix_cons _ _) hco)
    (noParent_arg_node1 hMA (by intro he; rw [he] at hA2; simp at hA2) hlev hnr)

/-- 場合 (d) の段 > 0 での `conC` の `dropLast` 可換（`m = 1`, `n' = 1` の形）。 -/
theorem conC_dropLast_node1 {M A : PairSeq} (hMA : M = ((0, 0) : ℕ × ℕ) :: A)
    (hA2 : 1 < A.length) (hco : contrOK M) (hA0 : ∀ c ∈ A, 0 < c.1)
    (hlev : 0 < entry M 1 (M.length - 1))
    (hnr : nextrel1 M 0 (M.length - 1)) :
    conC (M.dropLast) = (conC M).dropLast := by
  have hAne : A ≠ [] := by intro he; rw [he] at hA2; simp at hA2
  have hR0 : ∀ c ∈ A.dropLast, 0 < c.1 :=
    fun c hc => hA0 c ((List.dropLast_sublist A).subset hc)
  have hXne : convC A 1 0 true false ≠ [] := by
    rw [ne_eq, convC_eq_nil_iff]; exact hAne
  rw [hMA, dropLast_cons_ne hAne, conC_cons_zero hR0, conC_cons_zero hA0,
    dropLast_cons_ne hXne, convC_dropLast_node1 hMA hA2 hco hlev hnr]

/-! ## 3. 組み立て（その 1）: `contrOK` は段 0 では自動

`contrOK M` は「縮約が『読み直しの先が 1 列・外の後続が空』の形で発火するなら
その段は 0」だった。ところがこの形で発火したときの `x` は **`M` の末尾列そのもの**
である（`rest2 = [x]` と `Bq = []` から `r2 = pre ++ [x]` で、`x` より後ろには
何もない）。したがって

    末尾列の段が 0  ⟹  contrOK M

が無条件に出る。これで場合 (b)(d) の仮定 `contrOK` は、段 0 の場合には消える。 -/

/-- `M.drop t` が `x` で終わるなら `M` も `x` で終わる。 -/
theorem getLastD_of_drop_snoc {M : PairSeq} {t : ℕ} {x dflt : ℕ × ℕ}
    (h : ∃ Z : PairSeq, M.drop t = Z ++ [x]) : M.getLastD dflt = x := by
  obtain ⟨Z, hZ⟩ := h
  have hM : M = (M.take t ++ Z) ++ [x] := by
    conv_lhs => rw [← List.take_append_drop t M]
    rw [hZ, List.append_assoc]
  rw [hM]
  simp

/-- `B` の途中から先が `x` で終わるなら、`p :: (A ++ B)` も `x` で終わる。 -/
theorem snoc_of_drop {p q x : ℕ × ℕ} {A B pre : PairSeq} {k : ℕ}
    (hB : B.drop k = q :: (pre ++ [x])) :
    p :: (A ++ B) = (p :: (A ++ (B.take k ++ (q :: pre)))) ++ [x] := by
  conv_lhs => rw [← List.take_append_drop k B, hB]
  simp [List.append_assoc]

/-- **縮約が `some ([x], [])` の形で発火したなら、`x` は `M` の末尾列。** -/
theorem contr_single_getLast {M : PairSeq} {t : ℕ} {p x : ℕ × ℕ} {r : PairSeq}
    (ht : M.drop t = p :: r)
    (hc : contrLen p (r.dropWhile fun q => p.1 < q.1)
            (unitsLen p (r.dropWhile fun q => p.1 < q.1))
            (r.takeWhile fun q => p.1 < q.1) = some ([x], [])) :
    M.getLastD (0, 0) = x := by
  obtain ⟨q, r2, hdr, -, -, hAq, hBq, -, -, -⟩ := contrLen_spec hc
  have hr2 : r2 = (contrPre p ((r.dropWhile fun z => p.1 < z.1).take
        (unitsLen p (r.dropWhile fun z => p.1 < z.1)))
        (r.takeWhile fun z => p.1 < z.1)) ++ [x] := by
    have hsp := List.takeWhile_append_dropWhile
      (l := r2) (p := fun z : ℕ × ℕ => decide (q.1 < z.1))
    rw [hAq, hBq, List.append_nil] at hsp
    exact hsp.symm
  have hdr2 : (r.dropWhile fun z => p.1 < z.1).drop
      (unitsLen p (r.dropWhile fun z => p.1 < z.1))
      = q :: ((contrPre p ((r.dropWhile fun z => p.1 < z.1).take
          (unitsLen p (r.dropWhile fun z => p.1 < z.1)))
          (r.takeWhile fun z => p.1 < z.1)) ++ [x]) := by
    rw [hdr, hr2]
  have hsplit : r = (r.takeWhile fun z => p.1 < z.1) ++ (r.dropWhile fun z => p.1 < z.1) :=
    (List.takeWhile_append_dropWhile).symm
  refine getLastD_of_drop_snoc (t := t) ?_
  rw [ht, hsplit]
  exact ⟨_, snoc_of_drop hdr2⟩

/-- **末尾列の段が 0 なら `contrOK` は自動的に成り立つ。** -/
theorem contrOK_of_last_zero {M : PairSeq} (h : entry M 1 (M.length - 1) = 0) : contrOK M := by
  intro t p x r ht hc
  rw [entry_last, contr_single_getLast ht hc] at h
  exact h

/-! ## 3.1 組み立て（その 2）: 標準形の頭は `(0,0)` -/

theorem headI_zero_of_ST {M : PairSeq} (hM : ST_PS M) (hne : M ≠ []) :
    M.headI = ((0, 0) : ℕ × ℕ) := by
  have h1 : (M.headI).1 = 0 := (blockok_ST_PS hM).1 hne
  have hg : M.getD 0 (0, 0) = M.headI := by
    cases M with
    | nil => exact absurd rfl hne
    | cons a l => simp
  have h2 : (M.headI).2 = 0 := by
    rw [← hg]
    exact z0ok_ST_PS hM 0 (List.length_pos_of_ne_nil hne) (by rw [hg]; exact h1)
  have : M.headI = ((M.headI).1, (M.headI).2) := rfl
  rw [this, h1, h2]

/-! ## 3.2 組み立て（その 3）: 場合 (a) と場合 (d) の段 0 -/

/-- **場合 (a)**（`succ` regime）を `ReindexD` の形で。 -/
theorem reindexD_last_zero {M : PairSeq} (hM : ST_PS M) (hL : 1 < M.length) (n : ℕ)
    (hz : M.getLastD (0, 0) = ((0, 0) : ℕ × ℕ)) :
    ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧ (conC M)⟦m⟧ = conC (M⟦n'⟧) := by
  have hne : M ≠ [] := by intro he; rw [he] at hL; simp at hL
  have hg : M.getLast hne = ((0, 0) : ℕ × ℕ) := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast (h := hne)] at hz
    simpa using hz
  have hsplit : M.dropLast ++ [((0, 0) : ℕ × ℕ)] = M := by
    rw [← hg]; exact List.dropLast_append_getLast hne
  have hdne : M.dropLast ≠ [] := by
    intro he
    have hlen : M.dropLast.length = M.length - 1 := List.length_dropLast
    rw [he] at hlen
    simp at hlen
    omega
  have hc : colOK M.dropLast := colOK_sublist (List.dropLast_sublist M) (colOK_ST_PS hM)
  obtain ⟨m, n', h1, h2, h3⟩ := reindexD_succ_shape hdne hc n
  rw [hsplit] at h3
  exact ⟨m, n', h1, h2, h3⟩

/-- **場合 (d) の段 0** を `ReindexD` の形で（`contrOK` の仮定はもう要らない）。 -/
theorem reindexD_root_zero {M : PairSeq} (hM : ST_PS M) (hL : 1 < M.length) (n : ℕ) (hn : 1 ≤ n)
    (hlev : entry M 1 (M.length - 1) = 0)
    (hnr : nextrel0 M 0 (M.length - 1)) :
    ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧ (conC M)⟦m⟧ = conC (M⟦n'⟧) :=
  reindexD_node0_shape n hn hL (contrOK_of_last_zero hlev)
    (headI_zero_of_ST hM (by intro he; rw [he] at hL; simp at hL)) hlev hnr

/-! ## 3.3 組み立て（その 4）: 残っている場合

場合 (a)（末尾 = `(0,0)`）と場合 (d) の段 0（親が根で末尾列の段が 0）は
上で片付いた。残るのは「末尾列が `(0,0)` でなく、しかも『段 0 かつ親が根』でない」
場合、すなわち計画書の場合 (c)（親がブロックの中）と場合 (d) の段 > 0 である。 -/

/-- `ReindexD` に残っている場合（場合 (c) と場合 (d) の段 > 0）。 -/
def ReindexD_mid : Prop :=
  ∀ {A : PairSeq}, ST_PS A → 1 < A.length →
    A.getLastD (0, 0) ≠ ((0, 0) : ℕ × ℕ) →
    ¬ (entry A 1 (A.length - 1) = 0 ∧ nextrel0 A 0 (A.length - 1)) →
    ∀ n : ℕ, 1 ≤ n →
      ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧ (conC A)⟦m⟧ = conC (A⟦n'⟧)

/-- **組み立て**: 残っている場合さえ埋まれば `ReindexD` が出る。 -/
theorem reindexD_holds_of (H : ReindexD_mid) : ReindexD := by
  intro A hA hL n hn
  by_cases hz : A.getLastD (0, 0) = ((0, 0) : ℕ × ℕ)
  · exact reindexD_last_zero hA hL n hz
  · by_cases hd : entry A 1 (A.length - 1) = 0 ∧ nextrel0 A 0 (A.length - 1)
    · exact reindexD_root_zero hA hL n hn hd.1 hd.2
    · exact H hA hL hz hd n hn

/-- **主定理の組み立て**: 残っている場合さえ埋まれば像は DBMS 標準形。 -/
theorem ST_D_conC_holds_of (H : ReindexD_mid) {M : PairSeq} (hM : ST_PS M) :
    ST_D (conC M) := ST_D_conC (reindexD_holds_of H) hM

end DBMS

#print axioms DBMS.ST_D_conC
#print axioms DBMS.ST_D_descend
#print axioms DBMS.diag_cofinal
#print axioms DBMS.reindexD_succ
#print axioms DBMS.convC_snoc_zero
#print axioms DBMS.convC_getLast_level
#print axioms DBMS.idx1_conC
#print axioms DBMS.oper_mono
#print axioms DBMS.reindexD_succ_shape
#print axioms DBMS.conC_length_ge_two
#print axioms DBMS.convC_run
#print axioms DBMS.oper_repeat
#print axioms DBMS.convC_force
#print axioms DBMS.conC_run_top
#print axioms DBMS.oper_one
#print axioms DBMS.oper_append_of_parent_ge
#print axioms DBMS.convC_getLast_depth
#print axioms DBMS.oper_append_of_witness
#print axioms DBMS.parent_ge_of_shallow
#print axioms DBMS.oper_append_of_shallow0
#print axioms DBMS.convC_head_shallow
#print axioms DBMS.convC_exists_shallow
#print axioms DBMS.oper_append_convC
#print axioms DBMS.oper_append_of_shallow1
#print axioms DBMS.le0_head
#print axioms DBMS.convC_dropLast_singleton
#print axioms DBMS.convC_dropLast_arg
#print axioms DBMS.convC_dropLast_tail
#print axioms DBMS.convC_dropLast_contr
#print axioms DBMS.convC_dropLast_lad_none
#print axioms DBMS.convC_dropLast_contr2
#print axioms DBMS.hasParent0_of_exists
#print axioms DBMS.hasParent_last_append
#print axioms DBMS.noParent_suffix
#print axioms DBMS.contrOK_suffix
#print axioms DBMS.convC_single_ne
#print axioms DBMS.convC_dropLast_arg_single
#print axioms DBMS.convC_dropLast_arg'
#print axioms DBMS.contrLen_dropLast_none
#print axioms DBMS.convC_dropLast_noParent_aux
#print axioms DBMS.convC_dropLast_noParent
#print axioms DBMS.reindexD_noParent
#print axioms DBMS.rtg_lt_of_floor
#print axioms DBMS.le0_ge_of_append
#print axioms DBMS.convC_entry_last
#print axioms DBMS.shallow1_step
#print axioms DBMS.shallow1_headw
#print axioms DBMS.shallow1_nil
#print axioms DBMS.convC_exists_shallow1
#print axioms DBMS.exists_shallow1_of_hasParent
#print axioms DBMS.oper_append_convC1
#print axioms DBMS.oper_append_convC1'
#print axioms DBMS.entry_of_mem
#print axioms DBMS.convC_getLast_min
#print axioms DBMS.oper_repeat_root
#print axioms DBMS.conC_cons_zero
#print axioms DBMS.reindexD_node0
#print axioms DBMS.reindexD_node0_shape
#print axioms DBMS.noParent_arg_node1
#print axioms DBMS.convC_dropLast_node1
#print axioms DBMS.conC_dropLast_node1
#print axioms DBMS.contr_single_getLast
#print axioms DBMS.contrOK_of_last_zero
#print axioms DBMS.headI_zero_of_ST
#print axioms DBMS.reindexD_last_zero
#print axioms DBMS.reindexD_root_zero
#print axioms DBMS.reindexD_holds_of
#print axioms DBMS.ST_D_conC_holds_of
