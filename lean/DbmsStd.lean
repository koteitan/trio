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

/-- **`idx1` は両側で一致する。** `oper` がどちらの行で親を探すかが同じになる。 -/
theorem idx1_conC (M : PairSeq) :
    idx1 (conC M) ((conC M).length - 1) = idx1 M (M.length - 1) := by
  rw [idx1, idx1, entry_last, entry_last, conC_getLast_level]

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
