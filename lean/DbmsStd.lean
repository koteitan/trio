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
