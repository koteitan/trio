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

/-! ## 4. 場合 (c) の帰納の道具

`convC` の 1 段は、梯子が立たなければ **`T` に依らない前置き `C`** で因子化できる:

    convC (p :: (Arg ++ T)) d plev first force = C ++ convC T d p.2 false false

`T` を `T⟦n⟧` に取り替えても `C` は変わらない（展開は先頭列を変えないから）。
あとは両側の局所化を合わせれば、右端の道に沿って 1 段降りられる。 -/

/-- **展開は先頭列を変えない。** -/
theorem oper_headI {T : PairSeq} (hL : 1 < T.length) {n : ℕ} (hn : 1 ≤ n) :
    (T⟦n⟧).headI = T.headI := by
  obtain ⟨R, hR, -⟩ := oper_eq_dropLast_append hL hn
  obtain ⟨a, l, rfl⟩ : ∃ a l, T = a :: l := by
    cases T with
    | nil => simp at hL
    | cons a l => exact ⟨a, l, rfl⟩
  have hlne : l ≠ [] := by
    intro he; rw [he] at hL; simp at hL
  rw [hR, dropLast_cons_ne hlne]
  simp

/-- 展開は先頭列の深さを変えない。 -/
theorem oper_head_depth {T : PairSeq} (hL : 1 < T.length) {n : ℕ} (hn : 1 ≤ n) :
    ((T⟦n⟧).headI).1 = (T.headI).1 := by rw [oper_headI hL hn]

/-- **行 1 版の `hasParent0_of_exists`**: `le0` の鎖の上に段のより小さい列が
1 つでもあれば、行 1 の親は存在する（最大のものが親になる）。 -/
theorem hasParent1_of_exists {M : PairSeq} {j1 : ℕ} (hj : j1 < M.length)
    (h : ∃ k, le0 M k j1 ∧ entry M 1 k < entry M 1 j1) : hasParent M 1 j1 := by
  classical
  have h' : ∃ i, i < j1 ∧ (le0 M i j1 ∧ entry M 1 i < entry M 1 j1) := by
    obtain ⟨k, hk1, hk2⟩ := h
    have hkle : k ≤ j1 := le0_le hk1
    have hne : k ≠ j1 := by intro he; rw [he] at hk2; omega
    exact ⟨k, by omega, hk1, hk2⟩
  obtain ⟨i, hi1, ⟨hi2, hi3⟩, hi4⟩ := exists_greatest_lt
    (P := fun i => le0 M i j1 ∧ entry M 1 i < entry M 1 j1) j1 h'
  have hnr : nextrel1 M i j1 := by
    refine ⟨by omega, hj, hi1, hi3, hi2, ?_⟩
    rintro j ⟨hj1, hj2⟩
    rcases Nat.lt_or_ge j j1 with hlt | hge
    · rcases Nat.lt_or_ge (entry M 1 j) (entry M 1 j1) with hc | hc
      · exact absurd ⟨hj2, hc⟩ (hi4 j hj1 hlt)
      · exact hc
    · have hle : j ≤ j1 := le0_le hj2
      have hje : j = j1 := by omega
      rw [hje]
  refine ⟨i, ?_, ?_⟩
  · show nextR M 1 i j1
    unfold nextR; rw [if_neg one_ne_zero]; exact hnr
  · intro y hy
    have hy' : nextrel1 M y j1 := by
      have h2 : nextR M 1 y j1 := hy
      unfold nextR at h2; rw [if_neg one_ne_zero] at h2; exact h2
    have hle1 : i ≤ y := nextrel1_ge hy' hi2 hi3
    have hle2 : y ≤ i := by
      by_contra hgt
      push_neg at hgt
      exact hi4 y hgt hy'.2.2.1 ⟨hy'.2.2.2.2.1, hy'.2.2.2.1⟩
    omega

/-- `idx1` は `convC` で保たれる（`idx1_conC` の一般版）。 -/
theorem idx1_convC (M : PairSeq) (d plev : ℕ) (first force : Bool) :
    idx1 (convC M d plev first force) ((convC M d plev first force).length - 1)
      = idx1 M (M.length - 1) := by
  rw [idx1, idx1, entry_last, entry_last,
    convC_getLast_level M.length M (Nat.le_refl _) d plev first force]

/-- **兄弟への因子化。** 前置き `C` は `T` に依らない。 -/
theorem convC_factor_sib (p : ℕ × ℕ) (Arg T : PairSeq) (d plev : ℕ) (first force : Bool)
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hT : T = [] ∨ ¬ (p.1 < (T.headI).1))
    (hlad : ladOf p.2 d plev first force = false) :
    convC (p :: (Arg ++ T)) d plev first force
      = ((ddOf p.2 d plev first force, p.2)
          :: convC Arg (ddOf p.2 d plev first force + 1) p.2 true (first && (p.2 == plev)))
        ++ convC T d p.2 false false := by
  obtain ⟨e1, e2⟩ := split_append (dd := p.1) hArg hT
  rw [convC_cons_nolad p (Arg ++ T) d plev first force hlad, e1, e2]
  simp

/-- **引数への因子化**（兄弟が空のとき）。 -/
theorem convC_factor_arg (p : ℕ × ℕ) (Arg : PairSeq) (d plev : ℕ) (first force : Bool)
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hlad : ladOf p.2 d plev first force = false) :
    convC (p :: Arg) d plev first force
      = [(ddOf p.2 d plev first force, p.2)]
        ++ convC Arg (ddOf p.2 d plev first force + 1) p.2 true (first && (p.2 == plev)) := by
  have h := convC_factor_sib p Arg [] d plev first force hArg (Or.inl rfl) hlad
  simpa using h

/-- 段 0 の局所化。親の存在も証人から作るので、仮定に要らない。 -/
theorem oper_append_convC_auto (A B : PairSeq) (n : ℕ) {bd d plev : ℕ}
    (hb : blockok bd B) (hc : colOK B) (hdo : descOK B) (hbd : bd ≤ d)
    (hlast : bd < (B.getLastD (0, 0)).1)
    (hT : 2 ≤ (convC B d plev false false).length)
    (hz : ¬ (entry (convC B d plev false false)
              0 ((convC B d plev false false).length - 1) = 0 ∧
             entry (convC B d plev false false)
              1 ((convC B d plev false false).length - 1) = 0))
    (hi : idx1 (convC B d plev false false)
            ((convC B d plev false false).length - 1) = 0) :
    (A ++ convC B d plev false false)⟦n⟧ = A ++ (convC B d plev false false)⟦n⟧ := by
  obtain ⟨k, hk1, hk2⟩ :=
    convC_exists_shallow B.length B (Nat.le_refl _) bd d plev hb hc hdo hbd hlast
  have hp : hasParent (A ++ convC B d plev false false) 0
      (A.length + ((convC B d plev false false).length - 1)) := by
    refine hasParent0_of_exists (by rw [List.length_append]; omega)
      ⟨A.length + k, by omega, ?_⟩
    rw [entry_append_right, entry_append_right]
    exact hk2
  exact oper_append_convC A B n hb hc hdo hbd hlast hT hz hi (by rw [hi]; exact hp)

/-- 段 > 0 の局所化。親の存在も証人から作る。 -/
theorem oper_append_convC1_auto (A B : PairSeq) (n : ℕ) {bd d plev : ℕ} {first force : Bool}
    (hb : blockok bd B) (hpB : hasParent B 1 (B.length - 1))
    (hT : 2 ≤ (convC B d plev first force).length)
    (hz : ¬ (entry (convC B d plev first force)
              0 ((convC B d plev first force).length - 1) = 0 ∧
             entry (convC B d plev first force)
              1 ((convC B d plev first force).length - 1) = 0))
    (hi : idx1 (convC B d plev first force)
            ((convC B d plev first force).length - 1) ≠ 0) :
    (A ++ convC B d plev first force)⟦n⟧ = A ++ (convC B d plev first force)⟦n⟧ := by
  obtain ⟨k, hk1, hk2⟩ := convC_exists_shallow1 B.length B (Nat.le_refl _) bd d plev first force
    hb (exists_shallow1_of_hasParent hpB)
  have hp : hasParent (A ++ convC B d plev first force) 1
      (A.length + ((convC B d plev first force).length - 1)) := by
    refine hasParent1_of_exists (by rw [List.length_append]; omega) ⟨A.length + k, ?_, ?_⟩
    · exact le0_append_right_of A _ hk1
    · rw [entry_append_right, entry_append_right]; exact hk2
  have hi1 : idx1 (convC B d plev first force)
      ((convC B d plev first force).length - 1) = 1 := by
    have := idx1_le1 (convC B d plev first force)
      ((convC B d plev first force).length - 1)
    omega
  exact oper_append_convC1' A B n hb hpB hT hz hi (by rw [hi1]; exact hp)

/-- **降下の骨格。** 因子化・両側の局所化・帰納法の仮定を合わせる。 -/
theorem reindexD_descend {M T G C : PairSeq} {d plev d' plev' : ℕ}
    {first force first' force' : Bool}
    (hconv : convC M d plev first force = C ++ convC T d' plev' first' force')
    (hconv' : ∀ n : ℕ, 1 ≤ n → convC (G ++ T⟦n⟧) d plev first force
                = C ++ convC (T⟦n⟧) d' plev' first' force')
    (hBMS : ∀ n : ℕ, M⟦n⟧ = G ++ T⟦n⟧)
    (hDBMS : ∀ m : ℕ, (C ++ convC T d' plev' first' force')⟦m⟧
                = C ++ (convC T d' plev' first' force')⟦m⟧)
    (IH : ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
            (convC T d' plev' first' force')⟦m⟧ = convC (T⟦n'⟧) d' plev' first' force') :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC M d plev first force)⟦m⟧ = convC (M⟦n'⟧) d plev first force := by
  intro n hn
  obtain ⟨m, n', hm, hnn, heq⟩ := IH n hn
  refine ⟨m, n', hm, hnn, ?_⟩
  rw [hconv, hDBMS, heq, hBMS, hconv' n' (le_trans hn hnn)]

/-! ## 4.1 場合 (c): 兄弟ブロックへ 1 段降りる

`M = (p :: Arg) ++ T`（`Arg` は `p` の引数、`T` は兄弟ブロック）で、
BMS の親が `T` の中にあるとき、両側とも `T` / `convC T` に局所化できる。
必要な仮定は「梯子が立たない」（`first = false` なら自動）とブロックの規律だけ。 -/

/-- **場合 (c) の 1 段（兄弟ブロックへ降りる）。** -/
theorem reindexD_sib_step {p : ℕ × ℕ} {Arg T : PairSeq} {d plev : ℕ} {first force : Bool}
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hTh : ¬ (p.1 < (T.headI).1))
    (hlad : ladOf p.2 d plev first force = false)
    (hb : blockok p.1 T) (hcT : colOK T) (hdT : descOK T) (hbd : p.1 ≤ d)
    (hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0))
    (hpB : hasParent ((p :: Arg) ++ T) (idx1 T (T.length - 1))
             ((p :: Arg).length + (T.length - 1)))
    (hgeB : (p :: Arg).length ≤ parent ((p :: Arg) ++ T) (idx1 T (T.length - 1))
             ((p :: Arg).length + (T.length - 1)))
    (IH : ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
            (convC T d p.2 false false)⟦m⟧ = convC (T⟦n'⟧) d p.2 false false) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC ((p :: Arg) ++ T) d plev first force)⟦m⟧
        = convC (((p :: Arg) ++ T)⟦n'⟧) d plev first force := by
  have hlt := nextR_index_lt (parent_nextR hpB)
  have hT2 : 2 ≤ T.length := by omega
  have hT1 : 1 < T.length := by omega
  obtain ⟨hpT, -⟩ := hasParent_append_of_parent_ge (p :: Arg) T hpB hgeB
  have hDlen : 2 ≤ (convC T d p.2 false false).length := by
    have := convC_length_ge_two hT1 d p.2 false false; omega
  refine reindexD_descend (T := T) (G := p :: Arg) (d' := d) (plev' := p.2)
    (first' := false) (force' := false)
    (C := (ddOf p.2 d plev first force, p.2)
            :: convC Arg (ddOf p.2 d plev first force + 1) p.2 true (first && (p.2 == plev)))
    ?_ ?_ ?_ ?_ IH
  · rw [List.cons_append]
    exact convC_factor_sib p Arg T d plev first force hArg (Or.inr hTh) hlad
  · intro n hn
    rw [List.cons_append]
    exact convC_factor_sib p Arg (T⟦n⟧) d plev first force hArg
      (Or.inr (by rw [oper_headI hT1 hn]; exact hTh)) hlad
  · intro n
    exact oper_append_of_parent_ge (p :: Arg) T n hT2 hzT hpB hgeB
  · intro m
    by_cases h0 : idx1 T (T.length - 1) = 0
    · have hlast : p.1 < (T.getLastD (0, 0)).1 := by
        obtain ⟨j0, hj0, -⟩ := hpT
        rw [h0] at hj0
        have hnr : nextrel0 T j0 (T.length - 1) := by
          unfold nextR at hj0; rw [if_pos rfl] at hj0; exact hj0
        have hmem : T.getD j0 (0, 0) ∈ T := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnr.1]
          simpa using List.getElem_mem hnr.1
        have hge : p.1 ≤ entry T 0 j0 := by
          rw [entry, if_pos rfl]; exact hb.2.1 _ hmem
        have hgt := hnr.2.2.2.1
        rw [entry_last0] at hgt
        omega
      have hz : ¬ (entry (convC T d p.2 false false)
                    0 ((convC T d p.2 false false).length - 1) = 0 ∧
                   entry (convC T d p.2 false false)
                    1 ((convC T d p.2 false false).length - 1) = 0) := by
        rintro ⟨h1, -⟩
        have hgt := convC_getLast_depth T.length T (Nat.le_refl _) p.1 d p.2 false false hb hlast
        rw [entry_last0] at h1
        omega
      exact oper_append_convC_auto _ T m hb hcT hdT hbd hlast hDlen hz
        (by rw [idx1_convC]; exact h0)
    · have h1T : 0 < entry T 1 (T.length - 1) := by
        by_contra hc
        exact h0 (by rw [idx1, if_neg (by omega)])
      have hpT1 : hasParent T 1 (T.length - 1) := by
        have he : idx1 T (T.length - 1) = 1 := by rw [idx1, if_pos h1T]
        rw [he] at hpT; exact hpT
      have hz : ¬ (entry (convC T d p.2 false false)
                    0 ((convC T d p.2 false false).length - 1) = 0 ∧
                   entry (convC T d p.2 false false)
                    1 ((convC T d p.2 false false).length - 1) = 0) := by
        rintro ⟨-, h2⟩
        rw [entry_last,
          convC_getLast_level T.length T (Nat.le_refl _) d p.2 false false] at h2
        rw [entry_last] at h1T
        omega
      exact oper_append_convC1_auto _ T m hb hpT1 hDlen hz
        (by rw [idx1_convC]; exact h0)

/-! ## 4.2 段 0 の証人（`first` / `force` が一般の場合）

`convC_exists_shallow` は `first = false` の呼び出しにしか使えなかったが、
引数ブロックへ降りるときは `first = true` で呼ばれる。証明はほとんど同じで、
**梯子が立つときは像の先頭が影の列 `(d, plev)` なので、先頭がそのまま証人**になる。
残るのは「梯子なしで先頭が深さ `y + 1` に置かれる」場合だけで、
これは `y = d = bd` に限られる（もとの証明と同じ）。 -/

theorem convC_exists_shallow_gen : ∀ (n : ℕ) (B : PairSeq), B.length ≤ n →
    ∀ (bd d plev : ℕ) (first force : Bool),
    blockok bd B → colOK B → descOK B → bd ≤ d →
    bd < (B.getLastD (0, 0)).1 →
    ∃ k, k < (convC B d plev first force).length - 1 ∧
      entry (convC B d plev first force) 0 k
        < entry (convC B d plev first force) 0 ((convC B d plev first force).length - 1) := by
  intro n
  induction n with
  | zero =>
    intro B hB bd d plev first force _ _ _ _ hlast
    have : B = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact absurd hlast (by simp)
  | succ n ih =>
    intro B hB bd d plev first force hb hc hd hbd hlast
    match B with
    | [] => exact absurd hlast (by simp)
    | p :: r =>
      have hp : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp]⟩
      have hy : y ≤ bd := hc (bd, y) (by simp)
      have hlen2 : 1 < ((bd, y) :: r).length := by
        by_contra hcon
        have hr : r = [] := by
          match r with
          | [] => rfl
          | _ :: _ => simp at hcon
        rw [hr] at hlast
        simp only [List.getLastD_cons, List.getLastD_nil] at hlast
        omega
      have hOlen : 1 < (convC ((bd, y) :: r) d plev first force).length :=
        convC_length_ge_two hlen2 d plev first force
      have hlastdep : d < ((convC ((bd, y) :: r) d plev first force).getLastD (0, 0)).1 :=
        convC_getLast_depth ((bd, y) :: r).length _ (Nat.le_refl _) bd d plev first force hb hlast
      by_cases hhd : ((convC ((bd, y) :: r) d plev first force).headI).1 = d
      · refine ⟨0, by omega, ?_⟩
        rw [entry_zero0, entry_last0, hhd]
        exact hlastdep
      · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
          by_cases hcon : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
          · exact absurd (by rw [convC_headI, if_pos hcon] : _ = d) hhd
          · simpa using hcon
        set dd := ddOf ((bd, y) : ℕ × ℕ).2 d plev first force with hdd
        have hhd2 : ((convC ((bd, y) :: r) d plev first force).headI).1 = dd := by
          rw [convC_headI, if_neg (by rw [hnl]; simp)]
        have hdc : dd ≠ d := fun he => hhd (by rw [hhd2, he])
        have hcase : 0 < y ∧ d ≤ y := by
          by_contra hcon
          apply hdc
          rw [hdd]
          unfold ddOf
          rw [if_neg (by rw [hnl]; simp), if_neg (by simpa using hcon)]
        have hyd : y = d := by omega
        have hdd1 : dd = d + 1 := by
          rw [hdd]
          unfold ddOf
          rw [if_neg (by rw [hnl]; simp), if_pos hcase]
          omega
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
        set X := convC A (dd + 1) ((bd, y) : ℕ × ℕ).2 true
          (first && (((bd, y) : ℕ × ℕ).2 == plev)) with hX
        set Y := convC B' d ((bd, y) : ℕ × ℕ).2 false false with hY
        have hout : convC ((bd, y) :: r) d plev first force
            = ((dd, ((bd, y) : ℕ × ℕ).2) :: X) ++ Y := by
          rw [convC_cons_nolad ((bd, y) : ℕ × ℕ) r d plev first force hnl]
          rw [← hA, ← hB', ← hdd, ← hX, ← hY, List.cons_append]
        by_cases hBe : B' = []
        · have hAe : A ≠ [] := by
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
          have hmem : X.getLastD (0, 0) ∈ convC A (dd + 1) ((bd, y) : ℕ × ℕ).2 true
              (first && (((bd, y) : ℕ × ℕ).2 == plev)) := by
            rw [← hX]; exact getLastD_mem hXne (0, 0)
          have := convC_ge' A (dd + 1) ((bd, y) : ℕ × ℕ).2 true
            (first && (((bd, y) : ℕ × ℕ).2 == plev)) _ hmem
          omega
        · have hlB' : B'.length ≤ n := by
            have := List.length_dropWhile_le (fun q : ℕ × ℕ => ((bd, y) : ℕ × ℕ).1 < q.1) r
            simp only [List.length_cons] at hB; rw [hB']; omega
          have hcB' : colOK B' := fun cc hcm => hc cc
            (List.mem_cons_of_mem _ (by rw [hB'] at hcm; exact (List.dropWhile_sublist _).subset hcm))
          have hdB' : descOK B' := by rw [hB']; exact (descOK_cons.1 hd).2.2
          have hlB2 : bd < (B'.getLastD (0, 0)).1 := by
            rw [if_neg hBe] at hMlast; rw [← hMlast]; exact hlast
          obtain ⟨k, hk1, hk2⟩ := ih B' hlB' bd d ((bd, y) : ℕ × ℕ).2 false false
            hbB' hcB' hdB' hbd hlB2
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

/-- 段 0 の局所化（`first` / `force` が一般の場合）。 -/
theorem oper_append_convC_gen (A B : PairSeq) (n : ℕ) {bd d plev : ℕ} {first force : Bool}
    (hb : blockok bd B) (hc : colOK B) (hdo : descOK B) (hbd : bd ≤ d)
    (hlast : bd < (B.getLastD (0, 0)).1)
    (hT : 2 ≤ (convC B d plev first force).length)
    (hz : ¬ (entry (convC B d plev first force)
              0 ((convC B d plev first force).length - 1) = 0 ∧
             entry (convC B d plev first force)
              1 ((convC B d plev first force).length - 1) = 0))
    (hi : idx1 (convC B d plev first force)
            ((convC B d plev first force).length - 1) = 0) :
    (A ++ convC B d plev first force)⟦n⟧ = A ++ (convC B d plev first force)⟦n⟧ := by
  obtain ⟨k, hk1, hk2⟩ := convC_exists_shallow_gen B.length B (Nat.le_refl _) bd d plev
    first force hb hc hdo hbd hlast
  have hp : hasParent (A ++ convC B d plev first force) 0
      (A.length + ((convC B d plev first force).length - 1)) := by
    refine hasParent0_of_exists (by rw [List.length_append]; omega)
      ⟨A.length + k, by omega, ?_⟩
    rw [entry_append_right, entry_append_right]
    exact hk2
  exact oper_append_of_shallow0 A _ n hT hz hi (by rw [hi]; exact hp) hk1 hk2

/-! ## 4.3 場合 (c): 引数ブロックへ 1 段降りる -/

/-- 展開は列を深くしかしない。 -/
theorem oper_depth_gt {M : PairSeq} {a : ℕ} (h : ∀ x ∈ M, a < x.1) (n : ℕ) :
    ∀ x ∈ M⟦n⟧, a < x.1 := by
  classical
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]; exact h
  have hlen : 1 < M.length := by omega
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz, Pred, if_neg (by omega)]
    exact fun x hx => h x ((List.dropLast_sublist M).subset hx)
  by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
  · rw [oper_bad_unfold n hL hz hp]
    have hlt : parent M (idx1 M (M.length - 1)) (M.length - 1) < M.length - 1 :=
      nextR_index_lt (parent_nextR hp)
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact h x ((List.take_sublist _ M).subset hx)
    · rw [List.mem_flatMap] at hx
      obtain ⟨k, -, hx⟩ := hx
      rw [List.mem_map] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      have hjr := List.mem_range'.1 hj
      have hjlt : j < M.length := by omega
      have hmem : M.getD j (0, 0) ∈ M := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt]
        simpa using List.getElem_mem hjlt
      have hgt : a < entry M 0 j := by
        rw [entry, if_pos rfl]; exact h _ hmem
      simp only []
      omega
  · rw [oper_eq_pred_of_noParent n hL hz hp, Pred, if_neg (by omega)]
    exact fun x hx => h x ((List.dropLast_sublist M).subset hx)

/-- **場合 (c) の 1 段（引数ブロックへ降りる）。** -/
theorem reindexD_arg_step {p : ℕ × ℕ} {Arg : PairSeq} {d plev : ℕ} {first force : Bool}
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hlad : ladOf p.2 d plev first force = false)
    (hb : blockok (p.1 + 1) Arg) (hcA : colOK Arg) (hdA : descOK Arg) (hbd : p.1 ≤ d)
    (hpB : hasParent ([p] ++ Arg) (idx1 Arg (Arg.length - 1))
             (([p] : PairSeq).length + (Arg.length - 1)))
    (hgeB : ([p] : PairSeq).length ≤ parent ([p] ++ Arg) (idx1 Arg (Arg.length - 1))
             (([p] : PairSeq).length + (Arg.length - 1)))
    (IH : ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC Arg (ddOf p.2 d plev first force + 1) p.2 true (first && (p.2 == plev)))⟦m⟧
          = convC (Arg⟦n'⟧) (ddOf p.2 d plev first force + 1) p.2 true
              (first && (p.2 == plev))) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC ([p] ++ Arg) d plev first force)⟦m⟧
        = convC (([p] ++ Arg)⟦n'⟧) d plev first force := by
  have hlt := nextR_index_lt (parent_nextR hpB)
  have hlen1 : ([p] : PairSeq).length = 1 := rfl
  rw [hlen1] at hlt hgeB
  have hT2 : 2 ≤ Arg.length := by omega
  have hT1 : 1 < Arg.length := by omega
  have hAne : Arg ≠ [] := by intro he; rw [he] at hT1; simp at hT1
  obtain ⟨hpT, -⟩ := hasParent_append_of_parent_ge [p] Arg hpB hgeB
  have hlastmem : Arg.getLastD (0, 0) ∈ Arg := getLastD_mem hAne (0, 0)
  have hzA : ¬ (entry Arg 0 (Arg.length - 1) = 0 ∧ entry Arg 1 (Arg.length - 1) = 0) := by
    rintro ⟨h1, -⟩
    rw [entry_last0] at h1
    have := hArg _ hlastmem
    omega
  have hbd' : p.1 + 1 ≤ ddOf p.2 d plev first force + 1 := by
    have := le_ddOf p.2 d plev first force
    omega
  have hDlen : 2 ≤ (convC Arg (ddOf p.2 d plev first force + 1) p.2 true
      (first && (p.2 == plev))).length := by
    have := convC_length_ge_two hT1 (ddOf p.2 d plev first force + 1) p.2 true
      (first && (p.2 == plev))
    omega
  refine reindexD_descend (T := Arg) (G := [p])
    (d' := ddOf p.2 d plev first force + 1) (plev' := p.2)
    (first' := true) (force' := first && (p.2 == plev))
    (C := [(ddOf p.2 d plev first force, p.2)])
    ?_ ?_ ?_ ?_ IH
  · exact convC_factor_arg p Arg d plev first force hArg hlad
  · intro n hn
    exact convC_factor_arg p (Arg⟦n⟧) d plev first force (oper_depth_gt hArg n) hlad
  · intro n
    exact oper_append_of_parent_ge [p] Arg n hT2 hzA hpB hgeB
  · intro m
    by_cases h0 : idx1 Arg (Arg.length - 1) = 0
    · have hlast : p.1 + 1 < (Arg.getLastD (0, 0)).1 := by
        obtain ⟨j0, hj0, -⟩ := hpT
        rw [h0] at hj0
        have hnr : nextrel0 Arg j0 (Arg.length - 1) := by
          unfold nextR at hj0; rw [if_pos rfl] at hj0; exact hj0
        have hmem : Arg.getD j0 (0, 0) ∈ Arg := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnr.1]
          simpa using List.getElem_mem hnr.1
        have hge : p.1 + 1 ≤ entry Arg 0 j0 := by
          rw [entry, if_pos rfl]; exact hb.2.1 _ hmem
        have hgt := hnr.2.2.2.1
        rw [entry_last0] at hgt
        omega
      have hz : ¬ (entry (convC Arg (ddOf p.2 d plev first force + 1) p.2 true
                     (first && (p.2 == plev))) 0
                     ((convC Arg (ddOf p.2 d plev first force + 1) p.2 true
                       (first && (p.2 == plev))).length - 1) = 0 ∧
                   entry (convC Arg (ddOf p.2 d plev first force + 1) p.2 true
                     (first && (p.2 == plev))) 1
                     ((convC Arg (ddOf p.2 d plev first force + 1) p.2 true
                       (first && (p.2 == plev))).length - 1) = 0) := by
        rintro ⟨h1, -⟩
        have hgt := convC_getLast_depth Arg.length Arg (Nat.le_refl _) (p.1 + 1)
          (ddOf p.2 d plev first force + 1) p.2 true (first && (p.2 == plev)) hb hlast
        rw [entry_last0] at h1
        omega
      exact oper_append_convC_gen _ Arg m hb hcA hdA hbd' hlast hDlen hz
        (by rw [idx1_convC]; exact h0)
    · have h1T : 0 < entry Arg 1 (Arg.length - 1) := by
        by_contra hc
        exact h0 (by rw [idx1, if_neg (by omega)])
      have hpT1 : hasParent Arg 1 (Arg.length - 1) := by
        have he : idx1 Arg (Arg.length - 1) = 1 := by rw [idx1, if_pos h1T]
        rw [he] at hpT; exact hpT
      have hz : ¬ (entry (convC Arg (ddOf p.2 d plev first force + 1) p.2 true
                     (first && (p.2 == plev))) 0
                     ((convC Arg (ddOf p.2 d plev first force + 1) p.2 true
                       (first && (p.2 == plev))).length - 1) = 0 ∧
                   entry (convC Arg (ddOf p.2 d plev first force + 1) p.2 true
                     (first && (p.2 == plev))) 1
                     ((convC Arg (ddOf p.2 d plev first force + 1) p.2 true
                       (first && (p.2 == plev))).length - 1) = 0) := by
        rintro ⟨-, h2⟩
        rw [entry_last, convC_getLast_level Arg.length Arg (Nat.le_refl _)
          (ddOf p.2 d plev first force + 1) p.2 true (first && (p.2 == plev))] at h2
        rw [entry_last] at h1T
        omega
      exact oper_append_convC1_auto _ Arg m hb hpT1 hDlen hz
        (by rw [idx1_convC]; exact h0)

/-! ## 4.4 1 段降りる補題（統一形）

兄弟へ降りる場合と引数へ降りる場合の違いは、因子化が成り立つための
「`T` についての条件 `P`」だけである（兄弟なら「先頭が浅い」、
引数なら「全部深い」）。どちらも展開 `T ↦ T⟦n⟧` で保たれるので、
1 つの補題にまとめられる。 -/

/-- **右端の道を 1 段降りる（統一形）。** -/
theorem reindexD_step_gen {G T C : PairSeq} {bd d plev d' plev' : ℕ}
    {first force first' force' : Bool} {P : PairSeq → Prop}
    (hfac : ∀ L : PairSeq, P L →
        convC (G ++ L) d plev first force = C ++ convC L d' plev' first' force')
    (hPT : P T) (hPop : 1 < T.length → ∀ n : ℕ, 1 ≤ n → P (T⟦n⟧))
    (hb : blockok bd T) (hcT : colOK T) (hdT : descOK T) (hbd : bd ≤ d')
    (hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0))
    (hpB : hasParent (G ++ T) (idx1 T (T.length - 1)) (G.length + (T.length - 1)))
    (hgeB : G.length ≤ parent (G ++ T) (idx1 T (T.length - 1)) (G.length + (T.length - 1)))
    (IH : ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
            (convC T d' plev' first' force')⟦m⟧ = convC (T⟦n'⟧) d' plev' first' force') :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (G ++ T) d plev first force)⟦m⟧ = convC ((G ++ T)⟦n'⟧) d plev first force := by
  have hlt := nextR_index_lt (parent_nextR hpB)
  have hT2 : 2 ≤ T.length := by omega
  have hT1 : 1 < T.length := by omega
  obtain ⟨hpT, -⟩ := hasParent_append_of_parent_ge G T hpB hgeB
  have hDlen : 2 ≤ (convC T d' plev' first' force').length := by
    have := convC_length_ge_two hT1 d' plev' first' force'; omega
  refine reindexD_descend (T := T) (G := G) (C := C)
    (d' := d') (plev' := plev') (first' := first') (force' := force')
    (hfac T hPT) (fun n hn => hfac (T⟦n⟧) (hPop hT1 n hn))
    (fun n => oper_append_of_parent_ge G T n hT2 hzT hpB hgeB) ?_ IH
  intro m
  by_cases h0 : idx1 T (T.length - 1) = 0
  · have hlast : bd < (T.getLastD (0, 0)).1 := by
      obtain ⟨j0, hj0, -⟩ := hpT
      rw [h0] at hj0
      have hnr : nextrel0 T j0 (T.length - 1) := by
        unfold nextR at hj0; rw [if_pos rfl] at hj0; exact hj0
      have hmem : T.getD j0 (0, 0) ∈ T := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnr.1]
        simpa using List.getElem_mem hnr.1
      have hge : bd ≤ entry T 0 j0 := by
        rw [entry, if_pos rfl]; exact hb.2.1 _ hmem
      have hgt := hnr.2.2.2.1
      rw [entry_last0] at hgt
      omega
    have hz : ¬ (entry (convC T d' plev' first' force')
                  0 ((convC T d' plev' first' force').length - 1) = 0 ∧
                 entry (convC T d' plev' first' force')
                  1 ((convC T d' plev' first' force').length - 1) = 0) := by
      rintro ⟨h1, -⟩
      have hgt := convC_getLast_depth T.length T (Nat.le_refl _) bd d' plev'
        first' force' hb hlast
      rw [entry_last0] at h1
      omega
    exact oper_append_convC_gen _ T m hb hcT hdT hbd hlast hDlen hz
      (by rw [idx1_convC]; exact h0)
  · have h1T : 0 < entry T 1 (T.length - 1) := by
      by_contra hc
      exact h0 (by rw [idx1, if_neg (by omega)])
    have hpT1 : hasParent T 1 (T.length - 1) := by
      have he : idx1 T (T.length - 1) = 1 := by rw [idx1, if_pos h1T]
      rw [he] at hpT; exact hpT
    have hz : ¬ (entry (convC T d' plev' first' force')
                  0 ((convC T d' plev' first' force').length - 1) = 0 ∧
                 entry (convC T d' plev' first' force')
                  1 ((convC T d' plev' first' force').length - 1) = 0) := by
      rintro ⟨-, h2⟩
      rw [entry_last, convC_getLast_level T.length T (Nat.le_refl _) d' plev'
        first' force'] at h2
      rw [entry_last] at h1T
      omega
    exact oper_append_convC1_auto _ T m hb hpT1 hDlen hz
      (by rw [idx1_convC]; exact h0)

/-! ## 4.5 梯子が立つ段での因子化

梯子が立つ段では像の頭が影の列 `(d, plev)` になる。兄弟が空なら縮約は
起こりようがない（`contrLen p [] k A = none`）ので、引数へは無条件に降りられる。 -/

theorem contrLen_nil (p : ℕ × ℕ) (k : ℕ) (A : PairSeq) : contrLen p [] k A = none := by
  rw [contrLen]
  simp

/-- **梯子つきの引数への因子化。** -/
theorem convC_factor_arg_lad (p : ℕ × ℕ) (Arg : PairSeq) (d plev : ℕ) (first force : Bool)
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hlad : ladOf p.2 d plev first force = true) :
    convC (p :: Arg) d plev first force
      = [(d, plev), (d + 1, p.2)] ++ convC Arg (d + 2) p.2 true false := by
  obtain ⟨e1, e2⟩ := split_append (dd := p.1) hArg (Or.inl (rfl : ([] : PairSeq) = []))
  have hAt : (Arg.takeWhile fun q => p.1 < q.1) = Arg := by simpa using e1
  have hAe : (Arg.dropWhile fun q => p.1 < q.1) = [] := by simpa using e2
  rw [convC_cons_lad_none p Arg d plev first force hlad
      (by rw [hAe]; exact contrLen_nil _ _ _), hAe, hAt]
  simp

/-- **梯子つきの兄弟への因子化**（縮約が起きない場合）。 -/
theorem convC_factor_sib_lad (p : ℕ × ℕ) (Arg T : PairSeq) (d plev : ℕ) (first force : Bool)
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hT : T = [] ∨ ¬ (p.1 < (T.headI).1))
    (hlad : ladOf p.2 d plev first force = true)
    (hnc : contrLen p T (unitsLen p T) Arg = none) :
    convC (p :: (Arg ++ T)) d plev first force
      = ((d, plev) :: (d + 1, p.2) :: convC Arg (d + 2) p.2 true false)
        ++ convC T d p.2 false false := by
  obtain ⟨e1, e2⟩ := split_append (dd := p.1) hArg hT
  rw [convC_cons_lad_none p (Arg ++ T) d plev first force hlad (by rw [e1, e2]; exact hnc),
    e1, e2]
  simp

/-! ## 4.6 4 通りの降下

`convC` の再帰の 1 段で降りる先は「引数」か「兄弟」、
その段で梯子が立つか立たないかで 4 通り。縮約が発火する段だけが残る。 -/

/-- 梯子なしで引数へ。 -/
theorem reindexD_arg_nolad {p : ℕ × ℕ} {Arg : PairSeq} {d plev : ℕ} {first force : Bool}
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hlad : ladOf p.2 d plev first force = false)
    (hb : blockok (p.1 + 1) Arg) (hcA : colOK Arg) (hdA : descOK Arg) (hbd : p.1 ≤ d)
    (hzA : ¬ (entry Arg 0 (Arg.length - 1) = 0 ∧ entry Arg 1 (Arg.length - 1) = 0))
    (hpB : hasParent ([p] ++ Arg) (idx1 Arg (Arg.length - 1))
             (([p] : PairSeq).length + (Arg.length - 1)))
    (hgeB : ([p] : PairSeq).length ≤ parent ([p] ++ Arg) (idx1 Arg (Arg.length - 1))
             (([p] : PairSeq).length + (Arg.length - 1)))
    (IH : ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC Arg (ddOf p.2 d plev first force + 1) p.2 true (first && (p.2 == plev)))⟦m⟧
          = convC (Arg⟦n'⟧) (ddOf p.2 d plev first force + 1) p.2 true
              (first && (p.2 == plev))) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC ([p] ++ Arg) d plev first force)⟦m⟧
        = convC (([p] ++ Arg)⟦n'⟧) d plev first force :=
  reindexD_step_gen (P := fun L => ∀ x ∈ L, p.1 < x.1)
    (fun L hL => convC_factor_arg p L d plev first force hL hlad)
    hArg (fun _ n => fun _ => oper_depth_gt hArg n)
    hb hcA hdA (by have := le_ddOf p.2 d plev first force; omega) hzA hpB hgeB IH

/-- 梯子つきで引数へ（縮約は起こりようがない）。 -/
theorem reindexD_arg_lad {p : ℕ × ℕ} {Arg : PairSeq} {d plev : ℕ} {first force : Bool}
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hlad : ladOf p.2 d plev first force = true)
    (hb : blockok (p.1 + 1) Arg) (hcA : colOK Arg) (hdA : descOK Arg) (hbd : p.1 ≤ d)
    (hzA : ¬ (entry Arg 0 (Arg.length - 1) = 0 ∧ entry Arg 1 (Arg.length - 1) = 0))
    (hpB : hasParent ([p] ++ Arg) (idx1 Arg (Arg.length - 1))
             (([p] : PairSeq).length + (Arg.length - 1)))
    (hgeB : ([p] : PairSeq).length ≤ parent ([p] ++ Arg) (idx1 Arg (Arg.length - 1))
             (([p] : PairSeq).length + (Arg.length - 1)))
    (IH : ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC Arg (d + 2) p.2 true false)⟦m⟧ = convC (Arg⟦n'⟧) (d + 2) p.2 true false) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC ([p] ++ Arg) d plev first force)⟦m⟧
        = convC (([p] ++ Arg)⟦n'⟧) d plev first force :=
  reindexD_step_gen (P := fun L => ∀ x ∈ L, p.1 < x.1)
    (fun L hL => convC_factor_arg_lad p L d plev first force hL hlad)
    hArg (fun _ n => fun _ => oper_depth_gt hArg n)
    hb hcA hdA (by omega) hzA hpB hgeB IH

/-- 梯子なしで兄弟へ。 -/
theorem reindexD_sib_nolad {p : ℕ × ℕ} {Arg T : PairSeq} {d plev : ℕ} {first force : Bool}
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hTh : ¬ (p.1 < (T.headI).1))
    (hlad : ladOf p.2 d plev first force = false)
    (hb : blockok p.1 T) (hcT : colOK T) (hdT : descOK T) (hbd : p.1 ≤ d)
    (hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0))
    (hpB : hasParent ((p :: Arg) ++ T) (idx1 T (T.length - 1))
             ((p :: Arg).length + (T.length - 1)))
    (hgeB : (p :: Arg).length ≤ parent ((p :: Arg) ++ T) (idx1 T (T.length - 1))
             ((p :: Arg).length + (T.length - 1)))
    (IH : ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
            (convC T d p.2 false false)⟦m⟧ = convC (T⟦n'⟧) d p.2 false false) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC ((p :: Arg) ++ T) d plev first force)⟦m⟧
        = convC (((p :: Arg) ++ T)⟦n'⟧) d plev first force :=
  reindexD_step_gen (G := p :: Arg) (T := T) (P := fun L => ¬ (p.1 < (L.headI).1))
    (fun L hL => by
      rw [List.cons_append]
      exact convC_factor_sib p Arg L d plev first force hArg (Or.inr hL) hlad)
    hTh (fun hL n hn => by
      show ¬ (p.1 < ((T⟦n⟧).headI).1)
      rw [oper_headI hL hn]; exact hTh)
    hb hcT hdT hbd hzT hpB hgeB IH

/-- 梯子つきで兄弟へ（その段で縮約が起きない場合）。 -/
theorem reindexD_sib_lad {p : ℕ × ℕ} {Arg T : PairSeq} {d plev : ℕ} {first force : Bool}
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hTh : ¬ (p.1 < (T.headI).1))
    (hlad : ladOf p.2 d plev first force = true)
    (hnc : ∀ L : PairSeq, contrLen p L (unitsLen p L) Arg = none)
    (hb : blockok p.1 T) (hcT : colOK T) (hdT : descOK T) (hbd : p.1 ≤ d)
    (hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0))
    (hpB : hasParent ((p :: Arg) ++ T) (idx1 T (T.length - 1))
             ((p :: Arg).length + (T.length - 1)))
    (hgeB : (p :: Arg).length ≤ parent ((p :: Arg) ++ T) (idx1 T (T.length - 1))
             ((p :: Arg).length + (T.length - 1)))
    (IH : ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
            (convC T d p.2 false false)⟦m⟧ = convC (T⟦n'⟧) d p.2 false false) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC ((p :: Arg) ++ T) d plev first force)⟦m⟧
        = convC (((p :: Arg) ++ T)⟦n'⟧) d plev first force :=
  reindexD_step_gen (G := p :: Arg) (T := T) (P := fun L => ¬ (p.1 < (L.headI).1))
    (fun L hL => by
      rw [List.cons_append]
      exact convC_factor_sib_lad p Arg L d plev first force hArg (Or.inr hL) hlad (hnc L))
    hTh (fun hL n hn => by
      show ¬ (p.1 < ((T⟦n⟧).headI).1)
      rw [oper_headI hL hn]; exact hTh)
    hb hcT hdT hbd hzT hpB hgeB IH

/-! ## 4.7 降下が止まる場合（ブロック版）

右端の道を降りていくと、いつかは「親がこのブロックの中にない」ところで止まる。
止まり方は 3 通り: 末尾が `(0,0)`（(a)）、親がない（(b)）、親が節点そのもの（(d)）。
(a) と (b) はブロックのままで片付く。 -/

/-- **場合 (a) のブロック版**（`d = 0`、つまり深さ 0 のブロック）。 -/
theorem reindexD_succ_gen {B : PairSeq} (plev : ℕ) (first force : Bool)
    (hB : B ≠ []) (hc : colOK B) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (B ++ [((0, 0) : ℕ × ℕ)]) 0 plev first force)⟦m⟧
        = convC ((B ++ [((0, 0) : ℕ × ℕ)])⟦n'⟧) 0 plev first force := by
  intro n hn
  refine ⟨1, n, Nat.le_refl 1, Nat.le_refl n, ?_⟩
  have hsnoc : convC (B ++ [((0, 0) : ℕ × ℕ)]) 0 plev first force
      = convC B 0 plev first force ++ [((0, 0) : ℕ × ℕ)] :=
    convC_snoc_zero B.length B (Nat.le_refl _) hc 0 plev first force
  have hCne : convC B 0 plev first force ≠ [] := by
    rw [ne_eq, convC_eq_nil_iff]; exact hB
  rw [hsnoc, oper_snoc_zero hCne 1, oper_snoc_zero hB n]

/-- **場合 (b) のブロック版**: 末尾列に親がなければ `m = 1`, `n' = n`。 -/
theorem reindexD_noParent_gen {B : PairSeq} (d plev : ℕ) (first force : Bool)
    (hL : 1 < B.length) (hco : contrOK B)
    (hz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0))
    (hnp : ¬ hasParent B (idx1 B (B.length - 1)) (B.length - 1)) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force := by
  intro n _
  refine ⟨1, n, Nat.le_refl 1, Nat.le_refl n, ?_⟩
  rw [oper_one (convC_length_ge_two hL d plev first force),
    oper_eq_pred_of_noParent n (by omega) hz hnp, Pred, if_neg (by omega)]
  exact (convC_dropLast_noParent_aux B.length B (Nat.le_refl _) hL d plev first force
    hco hnp).symm

/-- 段 0 なら `contrOK` は自動なので、場合 (b) は仮定なしで片付く。 -/
theorem reindexD_noParent_zero {B : PairSeq} (d plev : ℕ) (first force : Bool)
    (hL : 1 < B.length) (hlev : entry B 1 (B.length - 1) = 0)
    (hz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0))
    (hnp : ¬ hasParent B (idx1 B (B.length - 1)) (B.length - 1)) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force :=
  reindexD_noParent_gen d plev first force hL (contrOK_of_last_zero hlev) hz hnp


/-! ## 4.8 場合 (d) のブロック版（段 0・梯子なし）

節点 `p` の列が親で末尾列の段が 0 なら、兄弟は空（`T = []`）でなければならない。
実際、行 0 の親が index 0 なら途中の列は全部末尾列より深く、兄弟の頭は `p` より
浅いからである。したがってブロックは `B = p :: A`（`A` は全部 `p` より深い）で、
`B⟦n⟧` は `B.dropLast` の素直な繰り返しになる。像も同じ形になるので `m = n`,
`n' = n` で一致する。

梯子が立つ段（`shift` regime の正体）と、引数への `force` が最初のコピーだけ
`true` になる場合は除く（仮定 `hnl` / `hfr`）。 -/

/-- **最初のコピーだけ `first` / `force` を受け取る繰り返しの補題**（梯子なし版）。

`convC_run` は `first = false` 版だったので、`conC` のように `first = true` で
始まる並びには使えなかった。梯子が立たず、引数への `force` も立たなければ、
最初のコピーも 2 番目以降と同じ塊に写る。 -/
theorem convC_run_first (p : ℕ × ℕ) (R : PairSeq) (hR : ∀ c ∈ R, p.1 < c.1)
    (d plev : ℕ) (first force : Bool)
    (hnl : ladOf p.2 d plev first force = false)
    (hfr : (first && (p.2 == plev)) = false) : ∀ n : ℕ,
    convC ((List.replicate n (p :: R)).flatten) d plev first force
      = (List.replicate n ((ddOf p.2 d plev first force, p.2)
          :: convC R (ddOf p.2 d plev first force + 1) p.2 true false)).flatten := by
  have hnl' : ladOf p.2 d p.2 false false = false := by simp [ladOf]
  have hdd : ddOf p.2 d p.2 false false = ddOf p.2 d plev first force := by
    unfold ddOf; rw [hnl', hnl]
  intro n
  match n with
  | 0 => simp
  | k + 1 =>
    have hrest : (List.replicate k (p :: R)).flatten = [] ∨
        ¬ (p.1 < (((List.replicate k (p :: R)).flatten).headI).1) := by
      cases k with
      | zero => exact Or.inl rfl
      | succ k' =>
        right
        rw [List.replicate_succ, List.flatten_cons, List.cons_append]
        simp
    obtain ⟨e1, e2⟩ := split_append (X := R) (dd := p.1) hR hrest
    have hrun := convC_run p R [] hR (Or.inl rfl) d p.2 k
    simp only [List.append_nil, convC_nil] at hrun
    rw [hdd] at hrun
    have hflat : (List.replicate (k + 1) (p :: R)).flatten
        = p :: (R ++ (List.replicate k (p :: R)).flatten) := by
      rw [List.replicate_succ, List.flatten_cons, List.cons_append]
    rw [hflat, convC_cons_nolad p _ d plev first force hnl, e1, e2, hfr, hrun,
      List.replicate_succ, List.flatten_cons, List.cons_append]

/-- **場合 (d) のブロック版（段 0・梯子なし）**: 節点が親なら両側とも
`dropLast` の繰り返しになる。 -/
theorem reindexD_node0_gen {p : ℕ × ℕ} {A : PairSeq} (hAne : A ≠ [])
    (hA : ∀ c ∈ A, p.1 < c.1)
    (hmin : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1)
    (hlev : (A.getLastD (0, 0)).2 = 0)
    (d plev : ℕ) (first force : Bool)
    (hnl : ladOf p.2 d plev first force = false)
    (hfr : (first && (p.2 == plev)) = false) (n : ℕ) :
    (convC (p :: A) d plev first force)⟦n⟧ = convC ((p :: A)⟦n⟧) d plev first force := by
  have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
  have hMlen : (p :: A).length = A.length + 1 := by simp
  have hL : 1 < (p :: A).length := by omega
  have hlmem : A.getLastD (0, 0) ∈ A := getLastD_mem hAne _
  have hplt : p.1 < (A.getLastD (0, 0)).1 := hA _ hlmem
  -- `A` の列は添字で読める
  have hgetA : ∀ j, j < A.length → (A.getLastD (0, 0)).1 ≤ entry A 0 j := by
    intro j hj
    have hmem : A.getD j (0, 0) ∈ A := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      simpa using List.getElem_mem hj
    rw [entry, if_pos rfl]
    exact hmin _ hmem
  -- 像の形
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := []) (dd := p.1) hA (Or.inl rfl)
  simp only [List.append_nil] at e1 e2
  have hconv : convC (p :: A) d plev first force
      = (ddOf p.2 d plev first force, p.2)
          :: convC A (ddOf p.2 d plev first force + 1) p.2 true false := by
    rw [convC_cons_nolad p A d plev first force hnl, e1, e2, hfr]
    simp only [convC_nil, List.append_nil]
  -- BMS 側
  have hlastM : ((p :: A).getLastD (0, 0)) = A.getLastD (0, 0) := getLastD_cons_ne p hAne _
  have hlevM : entry (p :: A) 1 ((p :: A).length - 1) = 0 := by
    rw [entry_last, hlastM]; exact hlev
  have hnrM : nextrel0 (p :: A) 0 ((p :: A).length - 1) := by
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [entry_zero0, entry_last0, hlastM]
      exact hplt
    · rintro j ⟨hj1, hj2⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [entry_last0, hlastM, entry_cons_succ]
      exact hgetA j' (by omega)
  have hbms : (p :: A)⟦n⟧ = (List.replicate n ((p :: A).dropLast)).flatten :=
    oper_repeat_root n hL hlevM hnrM
  have hMdl : (p :: A).dropLast = p :: A.dropLast := dropLast_cons_ne hAne
  -- DBMS 側
  have hXne : convC A (ddOf p.2 d plev first force + 1) p.2 true false ≠ [] := by
    rw [ne_eq, convC_eq_nil_iff]; exact hAne
  have hX1 : 1 ≤ (convC A (ddOf p.2 d plev first force + 1) p.2 true false).length :=
    List.length_pos_of_ne_nil hXne
  have hXd : ((convC A (ddOf p.2 d plev first force + 1) p.2 true false).getLastD (0, 0)).1
      = ddOf p.2 d plev first force + 1 :=
    convC_getLast_min A.length A (Nat.le_refl _) hAne hmin hlev _ p.2 true false
  have hXl : ((convC A (ddOf p.2 d plev first force + 1) p.2 true false).getLastD (0, 0)).2
      = 0 := by
    rw [convC_getLast_level A.length A (Nat.le_refl _) _ p.2 true false]; exact hlev
  have hDlen : ((ddOf p.2 d plev first force, p.2)
      :: convC A (ddOf p.2 d plev first force + 1) p.2 true false).length
      = (convC A (ddOf p.2 d plev first force + 1) p.2 true false).length + 1 := by simp
  have hDL : 1 < ((ddOf p.2 d plev first force, p.2)
      :: convC A (ddOf p.2 d plev first force + 1) p.2 true false).length := by omega
  have hDlast : (((ddOf p.2 d plev first force, p.2)
      :: convC A (ddOf p.2 d plev first force + 1) p.2 true false).getLastD (0, 0))
      = (convC A (ddOf p.2 d plev first force + 1) p.2 true false).getLastD (0, 0) :=
    getLastD_cons_ne _ hXne _
  have hDlev : entry ((ddOf p.2 d plev first force, p.2)
      :: convC A (ddOf p.2 d plev first force + 1) p.2 true false) 1
      (((ddOf p.2 d plev first force, p.2)
        :: convC A (ddOf p.2 d plev first force + 1) p.2 true false).length - 1) = 0 := by
    rw [entry_last, hDlast]; exact hXl
  have hDnr : nextrel0 ((ddOf p.2 d plev first force, p.2)
      :: convC A (ddOf p.2 d plev first force + 1) p.2 true false) 0
      (((ddOf p.2 d plev first force, p.2)
        :: convC A (ddOf p.2 d plev first force + 1) p.2 true false).length - 1) := by
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [entry_zero0, entry_last0, hDlast, hXd]
      simp
    · rintro j ⟨hj1, hj2⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [entry_last0, hDlast, hXd, entry_cons_succ]
      have hj' : j' < (convC A (ddOf p.2 d plev first force + 1) p.2 true false).length := by
        rw [hDlen] at hj2; omega
      have hmem : (convC A (ddOf p.2 d plev first force + 1) p.2 true false).getD j' (0, 0)
          ∈ convC A (ddOf p.2 d plev first force + 1) p.2 true false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
        simpa using List.getElem_mem hj'
      rw [entry, if_pos rfl]
      exact convC_ge' A _ p.2 true false _ hmem
  have hdbms : ((ddOf p.2 d plev first force, p.2)
      :: convC A (ddOf p.2 d plev first force + 1) p.2 true false)⟦n⟧
      = (List.replicate n (((ddOf p.2 d plev first force, p.2)
          :: convC A (ddOf p.2 d plev first force + 1) p.2 true false).dropLast)).flatten :=
    oper_repeat_root n hDL hDlev hDnr
  -- `dropLast` の可換
  have hXdl : (convC A (ddOf p.2 d plev first force + 1) p.2 true false).dropLast
      = convC (A.dropLast) (ddOf p.2 d plev first force + 1) p.2 true false := by
    by_cases hA2 : 1 < A.length
    · have hco : contrOK A := contrOK_of_last_zero (by rw [entry_last]; exact hlev)
      have hiA : idx1 A (A.length - 1) = 0 := by
        rw [idx1, if_neg (by rw [entry_last, hlev]; omega)]
      have hnp : ¬ hasParent A (idx1 A (A.length - 1)) (A.length - 1) := by
        rw [hiA]
        rintro ⟨j0, hj0, -⟩
        have hj0' : nextrel0 A j0 (A.length - 1) := by
          have h : nextR A 0 j0 (A.length - 1) := hj0
          unfold nextR at h; rw [if_pos rfl] at h; exact h
        have h1 := hgetA j0 hj0'.1
        have h2 := hj0'.2.2.2.1
        rw [entry_last0] at h2
        omega
      exact (convC_dropLast_noParent_aux A.length A (Nat.le_refl _) hA2 _ p.2 true false
        hco hnp).symm
    · obtain ⟨lp, hlp⟩ : ∃ lp, A = [lp] := List.length_eq_one_iff.1 (by omega)
      have hlp2 : lp.2 = 0 := by rw [hlp] at hlev; simpa using hlev
      have hnl2 : ladOf lp.2 (ddOf p.2 d plev first force + 1) p.2 true false = false := by
        rw [hlp2]; simp [ladOf]
      rw [hlp]
      simp [convC_cons_nolad lp [] (ddOf p.2 d plev first force + 1) p.2 true false hnl2]
  -- 仕上げ
  have hRdeep : ∀ c ∈ A.dropLast, p.1 < c.1 :=
    fun c hc => hA c ((List.dropLast_sublist A).subset hc)
  rw [hconv, hdbms, hbms, hMdl, dropLast_cons_ne hXne, hXdl,
    convC_run_first p (A.dropLast) hRdeep d plev first force hnl hfr n]

/-- 場合 (d) のブロック版（段 0・梯子なし）を `ReindexD` の形で。 -/
theorem reindexD_node0_gen_shape {p : ℕ × ℕ} {A : PairSeq} (hAne : A ≠ [])
    (hA : ∀ c ∈ A, p.1 < c.1)
    (hmin : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1)
    (hlev : (A.getLastD (0, 0)).2 = 0)
    (d plev : ℕ) (first force : Bool)
    (hnl : ladOf p.2 d plev first force = false)
    (hfr : (first && (p.2 == plev)) = false) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: A) d plev first force)⟦m⟧ = convC ((p :: A)⟦n'⟧) d plev first force :=
  fun n hn => ⟨n, n, hn, Nat.le_refl n,
    reindexD_node0_gen hAne hA hmin hlev d plev first force hnl hfr n⟩

/-! ## 4.9 場合 (d) のブロック版（段 0・梯子あり）

梯子が立つ段では像の頭が影の列 `(d, plev)` になるので、DBMS 側の親は
**index 1（梯子の本体 `(d+1, p.2)`）** になる。そこで `oper_repeat` を
一般の親の位置で使えるようにしておく。

このとき `ddOf p.2 d p.2 false false = p.2 + 1` なので、2 番目以降のコピーの頭が
最初のコピーの本体 `(d+1, p.2)` と一致するには `d = p.2` が要る。これは
`colOK`（`p.2 ≤ p.1`）・`blockok bd`（`bd = p.1`）・`bd ≤ d` と梯子の条件
`d ≤ p.2` を合わせると

    p.1 ≤ d ≤ p.2 ≤ p.1     すなわち     d = p.2 = p.1 = bd

として自動的に出る（`force` 経由で梯子が立つ場合だけが残る）。 -/

/-- **親の位置が一般の場合の `oper_repeat`。** 末尾列の段が 0 で行 0 の親が `j0` なら、
基本列は「頭 `j0` 列 + `dropLast.drop j0` の繰り返し」。 -/
theorem oper_repeat_at {M : PairSeq} (j0 n : ℕ) (hL : 1 < M.length)
    (hlev : entry M 1 (M.length - 1) = 0)
    (hnr : nextrel0 M j0 (M.length - 1)) :
    M⟦n⟧ = M.take j0 ++ (List.replicate n (M.dropLast.drop j0)).flatten := by
  have hi1 : idx1 M (M.length - 1) = 0 := by
    rw [idx1, if_neg (by rw [hlev]; omega)]
  have ha : 0 < entry M 0 (M.length - 1) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hnr.2.2.2.1
  have hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0) := by
    rintro ⟨h1, -⟩; omega
  have hp : hasParent M 0 (M.length - 1) :=
    hasParent0_of_exists (by omega) ⟨j0, hnr.2.2.1, hnr.2.2.2.1⟩
  have hnR : nextR M 0 j0 (M.length - 1) := by
    unfold nextR; rw [if_pos rfl]; exact hnr
  have hj0 : parent M 0 (M.length - 1) = j0 := hp.unique (parent_nextR hp) hnR
  have hj0lt : j0 < M.length - 1 := hnr.2.2.1
  have hmap : (List.range' j0 (M.length - 1 - j0)).map
      (fun j => ((entry M 0 j : ℕ), (entry M 1 j : ℕ))) = M.dropLast.drop j0 := by
    rw [range'_map_entry M (by omega) (by omega), List.dropLast_eq_take]
  have h := oper_repeat (M := M) n (by omega) hz (by rw [hi1]; exact hp) hi1
  rw [hi1, hj0, hmap] at h
  exact h

/-- **同じブロックの並びはユニットで埋め尽くされる。** -/
theorem unitsLen_replicate (p : ℕ × ℕ) (R : PairSeq) (hR : ∀ c ∈ R, p.1 < c.1) : ∀ k : ℕ,
    unitsLen p ((List.replicate k (p :: R)).flatten)
      = ((List.replicate k (p :: R)).flatten).length := by
  intro k
  induction k with
  | zero => simp [unitsLen]
  | succ k ih =>
    have hrest : (List.replicate k (p :: R)).flatten = [] ∨
        ¬ (p.1 < (((List.replicate k (p :: R)).flatten).headI).1) := by
      cases k with
      | zero => exact Or.inl rfl
      | succ k' =>
        right
        rw [List.replicate_succ, List.flatten_cons, List.cons_append]
        simp
    obtain ⟨e1, e2⟩ := split_append (X := R) (dd := p.1) hR hrest
    have hflat : (List.replicate (k + 1) (p :: R)).flatten
        = p :: (R ++ (List.replicate k (p :: R)).flatten) := by
      rw [List.replicate_succ, List.flatten_cons, List.cons_append]
    rw [hflat, unitsLen_cons_pos, e1, e2, ih]
    simp only [List.length_cons, List.length_append]
    omega

/-- ユニットで埋め尽くされていれば縮約は起きない。 -/
theorem contrLen_of_drop_nil (p : ℕ × ℕ) (B : PairSeq) (k : ℕ) (A : PairSeq)
    (h : B.drop k = []) : contrLen p B k A = none := by
  rw [contrLen, h]

/-- 末尾列がいちばん浅く段が 0 なら、`dropLast` は像と可換。 -/
theorem convC_dropLast_min {A : PairSeq} (hAne : A ≠ [])
    (hmin : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1)
    (hlev : (A.getLastD (0, 0)).2 = 0) (d plev : ℕ) (first force : Bool) :
    (convC A d plev first force).dropLast = convC (A.dropLast) d plev first force := by
  have hgetA : ∀ j, j < A.length → (A.getLastD (0, 0)).1 ≤ entry A 0 j := by
    intro j hj
    have hmem : A.getD j (0, 0) ∈ A := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      simpa using List.getElem_mem hj
    rw [entry, if_pos rfl]
    exact hmin _ hmem
  by_cases hA2 : 1 < A.length
  · have hco : contrOK A := contrOK_of_last_zero (by rw [entry_last]; exact hlev)
    have hiA : idx1 A (A.length - 1) = 0 := by
      rw [idx1, if_neg (by rw [entry_last, hlev]; omega)]
    have hnp : ¬ hasParent A (idx1 A (A.length - 1)) (A.length - 1) := by
      rw [hiA]
      rintro ⟨j0, hj0, -⟩
      have hj0' : nextrel0 A j0 (A.length - 1) := by
        have h : nextR A 0 j0 (A.length - 1) := hj0
        unfold nextR at h; rw [if_pos rfl] at h; exact h
      have h1 := hgetA j0 hj0'.1
      have h2 := hj0'.2.2.2.1
      rw [entry_last0] at h2
      omega
    exact (convC_dropLast_noParent_aux A.length A (Nat.le_refl _) hA2 d plev first force
      hco hnp).symm
  · have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
    obtain ⟨lp, hlp⟩ : ∃ lp, A = [lp] := List.length_eq_one_iff.1 (by omega)
    have hlp2 : lp.2 = 0 := by rw [hlp] at hlev; simpa using hlev
    have hnl2 : ladOf lp.2 d plev first force = false := by rw [hlp2]; simp [ladOf]
    rw [hlp]
    simp [convC_cons_nolad lp [] d plev first force hnl2]

/-- **梯子つきの繰り返しの補題**（`d = p.2` のとき）。 -/
theorem convC_run_lad (p : ℕ × ℕ) (R : PairSeq) (hR : ∀ c ∈ R, p.1 < c.1)
    (d plev : ℕ) (first force : Bool)
    (hlad : ladOf p.2 d plev first force = true) (hdp : d = p.2) : ∀ k : ℕ,
    convC ((List.replicate (k + 1) (p :: R)).flatten) d plev first force
      = (d, plev)
        :: (List.replicate (k + 1) ((d + 1, p.2) :: convC R (d + 2) p.2 true false)).flatten := by
  have hs : p.2 = plev + 1 := by
    by_contra hne
    rw [ladOf, beq_eq_false_iff_ne.2 hne] at hlad
    simp at hlad
  have hdd0 : ddOf p.2 d p.2 false false = d + 1 := by
    unfold ddOf
    rw [if_neg (by simp [ladOf]), if_pos ⟨by omega, by omega⟩]
    omega
  have hd2 : d + 1 + 1 = d + 2 := rfl
  intro k
  have hrest : (List.replicate k (p :: R)).flatten = [] ∨
      ¬ (p.1 < (((List.replicate k (p :: R)).flatten).headI).1) := by
    cases k with
    | zero => exact Or.inl rfl
    | succ k' =>
      right
      rw [List.replicate_succ, List.flatten_cons, List.cons_append]
      simp
  obtain ⟨e1, e2⟩ := split_append (X := R) (dd := p.1) hR hrest
  have hcn : contrLen p ((List.replicate k (p :: R)).flatten)
      (unitsLen p ((List.replicate k (p :: R)).flatten)) R = none :=
    contrLen_of_drop_nil _ _ _ _ (by rw [unitsLen_replicate p R hR k]; simp)
  have hrun := convC_run p R [] hR (Or.inl rfl) d p.2 k
  simp only [List.append_nil, convC_nil] at hrun
  rw [hdd0, hd2] at hrun
  have hflat : (List.replicate (k + 1) (p :: R)).flatten
      = p :: (R ++ (List.replicate k (p :: R)).flatten) := by
    rw [List.replicate_succ, List.flatten_cons, List.cons_append]
  rw [hflat, convC_cons_lad_none p _ d plev first force hlad (by rw [e1, e2]; exact hcn),
    e1, e2, hrun, List.replicate_succ, List.flatten_cons, List.cons_append]

/-- **場合 (d) のブロック版（段 0・梯子あり）**: `d = p.2` なら `m = n`, `n' = n`。 -/
theorem reindexD_node0_lad {p : ℕ × ℕ} {A : PairSeq} (hAne : A ≠ [])
    (hA : ∀ c ∈ A, p.1 < c.1)
    (hmin : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1)
    (hlev : (A.getLastD (0, 0)).2 = 0)
    (d plev : ℕ) (first force : Bool)
    (hlad : ladOf p.2 d plev first force = true) (hdp : d = p.2) (n : ℕ) (hn : 1 ≤ n) :
    (convC (p :: A) d plev first force)⟦n⟧ = convC ((p :: A)⟦n⟧) d plev first force := by
  have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
  have hMlen : (p :: A).length = A.length + 1 := by simp
  have hL : 1 < (p :: A).length := by omega
  have hlmem : A.getLastD (0, 0) ∈ A := getLastD_mem hAne _
  have hplt : p.1 < (A.getLastD (0, 0)).1 := hA _ hlmem
  have hgetA : ∀ j, j < A.length → (A.getLastD (0, 0)).1 ≤ entry A 0 j := by
    intro j hj
    have hmem : A.getD j (0, 0) ∈ A := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      simpa using List.getElem_mem hj
    rw [entry, if_pos rfl]
    exact hmin _ hmem
  -- 像の形
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := []) (dd := p.1) hA (Or.inl rfl)
  simp only [List.append_nil] at e1 e2
  have hconv : convC (p :: A) d plev first force
      = (d, plev) :: (d + 1, p.2) :: convC A (d + 2) p.2 true false := by
    rw [convC_cons_lad_none p A d plev first force hlad (by rw [e1, e2]; exact contrLen_nil _ _ _),
      e1, e2]
    simp only [convC_nil, List.append_nil]
  -- BMS 側
  have hlastM : ((p :: A).getLastD (0, 0)) = A.getLastD (0, 0) := getLastD_cons_ne p hAne _
  have hlevM : entry (p :: A) 1 ((p :: A).length - 1) = 0 := by
    rw [entry_last, hlastM]; exact hlev
  have hnrM : nextrel0 (p :: A) 0 ((p :: A).length - 1) := by
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [entry_zero0, entry_last0, hlastM]; exact hplt
    · rintro j ⟨hj1, hj2⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [entry_last0, hlastM, entry_cons_succ]
      exact hgetA j' (by omega)
  have hbms : (p :: A)⟦n⟧ = (List.replicate n ((p :: A).dropLast)).flatten :=
    oper_repeat_root n hL hlevM hnrM
  have hMdl : (p :: A).dropLast = p :: A.dropLast := dropLast_cons_ne hAne
  -- DBMS 側
  have hXne : convC A (d + 2) p.2 true false ≠ [] := by
    rw [ne_eq, convC_eq_nil_iff]; exact hAne
  have hX1 : 1 ≤ (convC A (d + 2) p.2 true false).length := List.length_pos_of_ne_nil hXne
  have hXd : ((convC A (d + 2) p.2 true false).getLastD (0, 0)).1 = d + 2 :=
    convC_getLast_min A.length A (Nat.le_refl _) hAne hmin hlev _ p.2 true false
  have hXl : ((convC A (d + 2) p.2 true false).getLastD (0, 0)).2 = 0 := by
    rw [convC_getLast_level A.length A (Nat.le_refl _) _ p.2 true false]; exact hlev
  have hYne : ((d + 1, p.2) :: convC A (d + 2) p.2 true false) ≠ [] := by simp
  have hDlen : ((d, plev) :: (d + 1, p.2) :: convC A (d + 2) p.2 true false).length
      = (convC A (d + 2) p.2 true false).length + 2 := by simp
  have hDL : 1 < ((d, plev) :: (d + 1, p.2) :: convC A (d + 2) p.2 true false).length := by omega
  have hDlast : (((d, plev) :: (d + 1, p.2) :: convC A (d + 2) p.2 true false).getLastD (0, 0))
      = (convC A (d + 2) p.2 true false).getLastD (0, 0) := by
    rw [getLastD_cons_ne _ hYne, getLastD_cons_ne _ hXne]
  have hDlev : entry ((d, plev) :: (d + 1, p.2) :: convC A (d + 2) p.2 true false) 1
      (((d, plev) :: (d + 1, p.2) :: convC A (d + 2) p.2 true false).length - 1) = 0 := by
    rw [entry_last, hDlast]; exact hXl
  have hDnr : nextrel0 ((d, plev) :: (d + 1, p.2) :: convC A (d + 2) p.2 true false) 1
      (((d, plev) :: (d + 1, p.2) :: convC A (d + 2) p.2 true false).length - 1) := by
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [entry_last0, hDlast, hXd, entry_cons_succ, entry_zero0]
      simp
    · rintro j ⟨hj1, hj2⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      rw [entry_last0, hDlast, hXd, entry_cons_succ, entry_cons_succ]
      have hj' : j' < (convC A (d + 2) p.2 true false).length := by
        rw [hDlen] at hj2; omega
      have hmem : (convC A (d + 2) p.2 true false).getD j' (0, 0)
          ∈ convC A (d + 2) p.2 true false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
        simpa using List.getElem_mem hj'
      rw [entry, if_pos rfl]
      exact convC_ge' A _ p.2 true false _ hmem
  have hdbms := oper_repeat_at (M := (d, plev) :: (d + 1, p.2) :: convC A (d + 2) p.2 true false)
    1 n hDL hDlev hDnr
  have hDdl : ((d, plev) :: (d + 1, p.2) :: convC A (d + 2) p.2 true false).dropLast.drop 1
      = (d + 1, p.2) :: (convC A (d + 2) p.2 true false).dropLast := by
    rw [dropLast_cons_ne hYne, dropLast_cons_ne hXne]
    simp
  have hDtake : ((d, plev) :: (d + 1, p.2) :: convC A (d + 2) p.2 true false).take 1
      = [((d, plev) : ℕ × ℕ)] := by simp
  rw [hDdl, hDtake] at hdbms
  -- 仕上げ
  have hRdeep : ∀ c ∈ A.dropLast, p.1 < c.1 :=
    fun c hc => hA c ((List.dropLast_sublist A).subset hc)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hconv, hdbms, hbms, hMdl, convC_dropLast_min hAne hmin hlev (d + 2) p.2 true false,
    convC_run_lad p (A.dropLast) hRdeep d plev first force hlad hdp k]
  simp

/-- 場合 (d) のブロック版（段 0・梯子あり）を `ReindexD` の形で。 -/
theorem reindexD_node0_lad_shape {p : ℕ × ℕ} {A : PairSeq} (hAne : A ≠ [])
    (hA : ∀ c ∈ A, p.1 < c.1)
    (hmin : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1)
    (hlev : (A.getLastD (0, 0)).2 = 0)
    (d plev : ℕ) (first force : Bool)
    (hlad : ladOf p.2 d plev first force = true) (hdp : d = p.2) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: A) d plev first force)⟦m⟧ = convC ((p :: A)⟦n'⟧) d plev first force :=
  fun n hn => ⟨n, n, hn, Nat.le_refl n,
    reindexD_node0_lad hAne hA hmin hlev d plev first force hlad hdp n hn⟩

/-! ## 4.10 段 0 の組み立て（右端の道に沿った帰納）

末尾列の段が 0 なら `contrOK` は自動なので、止まり方 (a)(b)(d) はすべて
無条件に片付く。したがって残るのは 2 つだけ:

* 梯子つきの段で縮約が起こりうる場合（`contr` regime。実測 ≤10 列で 180 個）
* 場合 (d)（親が節点）で `force`、またはその引数への持ち越し
  `first && (p.2 == plev)` が立っている場合（BMS 標準形が
  「節点の段 = 親の段 かつ その引数の頭の段 = 節点の段 + 1」を禁じることを
  使わないと消せない）

この 2 つを `RDzeroRes` に括り出して、それ以外を右端の道に沿った帰納で閉じる。 -/

/-- `dropWhile` の先頭は述語を満たさない。 -/
theorem dropWhile_head_not (a : ℕ) (r : PairSeq) :
    (r.dropWhile fun q => a < q.1) = [] ∨
      ¬ (a < (((r.dropWhile fun q => a < q.1)).headI).1) := by
  rcases h : (r.dropWhile fun q => a < q.1) with _ | ⟨x, xs⟩
  · exact Or.inl h
  · right
    rw [h]
    have hh := List.head?_dropWhile_not (fun q : ℕ × ℕ => decide (a < q.1)) r
    rw [h] at hh
    simpa using hh

/-- **段 0 で残っている 2 つの場合。** -/
def RDzeroRes : Prop :=
  ∀ (p : ℕ × ℕ) (A T : PairSeq) (bd d plev : ℕ) (first force : Bool),
    blockok bd (p :: (A ++ T)) → colOK (p :: (A ++ T)) → descOK (p :: (A ++ T)) →
    bd ≤ d → p.1 = bd →
    (∀ x ∈ A, p.1 < x.1) → (T = [] ∨ ¬ (p.1 < (T.headI).1)) →
    entry (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) = 0 →
    ((ladOf p.2 d plev first force = true ∧
        ¬ (∀ L : PairSeq, contrLen p L (unitsLen p L) A = none))
      ∨ (T = [] ∧ ((first && (p.2 == plev)) = true ∨ force = true))) →
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ T)) d plev first force)⟦m⟧
        = convC ((p :: (A ++ T))⟦n'⟧) d plev first force

/-- **段 0 の組み立て**（ブロック版）。 -/
theorem reindexD_zero_block (H : RDzeroRes) :
    ∀ (N : ℕ) (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → (bd = 0 → d = 0) →
      entry B 1 (B.length - 1) = 0 →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force := by
  intro N
  induction N with
  | zero =>
    intro B hB bd d plev first force _ _ _ _ _ _ n hn
    have hBe : B = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hBe
    exact ⟨1, n, Nat.le_refl 1, Nat.le_refl n, by
      rw [convC_nil, oper_eq_self_short n (by simp), convC_nil,
        oper_eq_self_short 1 (by simp)]⟩
  | succ N ih =>
    intro B hB bd d plev first force hb hc hd hbd hz0 hlev n hn
    cases B with
    | nil =>
      exact ⟨1, n, Nat.le_refl 1, Nat.le_refl n, by
        rw [convC_nil, oper_eq_self_short n (by simp), convC_nil,
          oper_eq_self_short 1 (by simp)]⟩
    | cons p r =>
      have hp1 : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp1]⟩
      -- 引数ブロックと兄弟ブロックに割る
      obtain ⟨A, T, hAd, hTd⟩ :
          ∃ A T, A = (r.takeWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) ∧
                 T = (r.dropWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) := ⟨_, _, rfl, rfl⟩
      have hrAT : r = A ++ T := by
        rw [hAd, hTd]; exact (List.takeWhile_append_dropWhile).symm
      subst hrAT
      have hAdeep : ∀ x ∈ A, ((bd, y) : ℕ × ℕ).1 < x.1 := by
        intro x hx
        rw [hAd] at hx
        simpa using List.mem_takeWhile_imp hx
      have hThd : T = [] ∨ ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
        rw [hTd]; exact dropWhile_head_not _ _
      obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := ((bd, y) : ℕ × ℕ).1)
        hAdeep hThd
      -- 不変量を割る
      have hbA : blockok (bd + 1) A := by rw [← e1]; exact blockok_arg hb
      have hbT : blockok bd T := by rw [← e2]; exact blockok_tail hb
      have hcA : colOK A := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_left A T))) hc
      have hcT : colOK T := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_right A T))) hc
      obtain ⟨hdh, hdA, hdT⟩ := descOK_cons.1 hd
      rw [e1] at hdA
      rw [e2] at hdh hdT
      have hlAT : A.length + T.length ≤ N := by
        simp only [List.length_cons, List.length_append] at hB
        omega
      -- 末尾列
      have hBne : ((bd, y) :: (A ++ T)) ≠ [] := by simp
      have hlplev : (((bd, y) :: (A ++ T)).getLastD (0, 0)).2 = 0 := by
        rw [← entry_last]; exact hlev
      by_cases hrne : A ++ T = []
      · -- 1 列のブロック
        obtain ⟨hAe, hTe⟩ := List.append_eq_nil_iff.1 hrne
        subst hAe; subst hTe
        have hy : y = 0 := by
          have h := hlplev
          simp only [List.append_nil, List.getLastD] at h
          simpa using h
        subst hy
        refine ⟨1, n, Nat.le_refl 1, Nat.le_refl n, ?_⟩
        have hnl : ladOf ((bd, 0) : ℕ × ℕ).2 d plev first force = false := by simp [ladOf]
        rw [List.append_nil, oper_eq_self_short n (by simp),
          convC_cons_nolad ((bd, 0) : ℕ × ℕ) [] d plev first force hnl]
        simp only [List.takeWhile_nil, List.dropWhile_nil, convC_nil, List.append_nil]
        exact oper_eq_self_short 1 (by simp)
      · have hL2 : 1 < ((bd, y) :: (A ++ T)).length := by
          simp only [List.length_cons]
          have := List.length_pos_of_ne_nil hrne
          omega
        have hlpmem : ((bd, y) :: (A ++ T)).getLastD (0, 0) ∈ ((bd, y) :: (A ++ T)) :=
          getLastD_mem hBne _
        by_cases hlp0 : (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 = 0
        · -- 場合 (a): 末尾列 = (0,0)
          have hbd0 : bd = 0 := by
            have := hb.2.1 _ hlpmem
            omega
          have hd0 : d = 0 := hz0 hbd0
          subst hd0
          have hlpeq : ((bd, y) :: (A ++ T)).getLastD (0, 0) = ((0, 0) : ℕ × ℕ) :=
            Prod.ext hlp0 hlplev
          have hg : ((bd, y) :: (A ++ T)).getLast hBne = ((0, 0) : ℕ × ℕ) := by
            rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast (h := hBne)] at hlpeq
            simpa using hlpeq
          have hsplit : ((bd, y) :: (A ++ T)).dropLast ++ [((0, 0) : ℕ × ℕ)]
              = ((bd, y) :: (A ++ T)) := by
            rw [← hg]; exact List.dropLast_append_getLast hBne
          have hdne : ((bd, y) :: (A ++ T)).dropLast ≠ [] := by
            intro he
            have hl : ((bd, y) :: (A ++ T)).dropLast.length
                = ((bd, y) :: (A ++ T)).length - 1 := List.length_dropLast
            rw [he] at hl
            simp only [List.length_nil] at hl
            omega
          have hcdl : colOK (((bd, y) :: (A ++ T)).dropLast) :=
            colOK_sublist (List.dropLast_sublist _) hc
          obtain ⟨m, n', h1, h2, h3⟩ := reindexD_succ_gen plev first force hdne hcdl n hn
          rw [hsplit] at h3
          exact ⟨m, n', h1, h2, h3⟩
        · -- 末尾列の深さは正
          have hlpos : 0 < (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 := by omega
          have hz : ¬ (entry ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1) = 0 ∧
                       entry ((bd, y) :: (A ++ T)) 1
                         (((bd, y) :: (A ++ T)).length - 1) = 0) := by
            rintro ⟨h1, -⟩
            rw [entry_last0] at h1
            omega
          have hi1 : idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1) = 0 := by
            rw [idx1, if_neg (by rw [hlev]; omega)]
          by_cases hpar : hasParent ((bd, y) :: (A ++ T))
              (idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1))
              (((bd, y) :: (A ++ T)).length - 1)
          · -- 親がある
            rw [hi1] at hpar
            have hnrp : nextrel0 ((bd, y) :: (A ++ T))
                (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1))
                (((bd, y) :: (A ++ T)).length - 1) := by
              have h := parent_nextR hpar
              unfold nextR at h; rw [if_pos rfl] at h; exact h
            have hj0ge : bd ≤ entry ((bd, y) :: (A ++ T)) 0
                (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1)) := by
              have hj := hnrp.1
              have hmem : ((bd, y) :: (A ++ T)).getD
                  (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1)) (0, 0)
                  ∈ ((bd, y) :: (A ++ T)) := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
                simpa using List.getElem_mem hj
              rw [entry, if_pos rfl]
              exact hb.2.1 _ hmem
            have hlpgt : bd < (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 := by
              have h1 := hnrp.2.2.2.1
              rw [entry_last0] at h1
              omega
            by_cases hTe : T = []
            · -- 兄弟が空: ブロックは p :: A
              subst hTe
              have hAne : A ≠ [] := by
                intro he; rw [he] at hrne; simp at hrne
              have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
              have hAlen : ((bd, y) :: (A ++ [])).length = A.length + 1 := by simp
              have hlastA : ((bd, y) :: (A ++ [])).getLastD (0, 0) = A.getLastD (0, 0) := by
                rw [List.append_nil]; exact getLastD_cons_ne _ hAne _
              have hlevA : entry A 1 (A.length - 1) = 0 := by
                rw [entry_last, ← hlastA]; exact hlplev
              have hiA : idx1 A (A.length - 1) = 0 := by
                rw [idx1, if_neg (by rw [hlevA]; omega)]
              have hzA : ¬ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0) := by
                rintro ⟨h1, -⟩
                rw [entry_last0, ← hlastA] at h1
                omega
              have hidx : ((bd, y) :: (A ++ [])).length - 1
                  = ([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1) := by
                simp only [List.length_cons, List.length_nil, List.append_nil]
                omega
              have hBeq : ((bd, y) :: (A ++ [])) = [((bd, y) : ℕ × ℕ)] ++ A := by simp
              by_cases hj00 : parent ((bd, y) :: (A ++ []))
                  0 (((bd, y) :: (A ++ [])).length - 1) = 0
              · -- 場合 (d): 親が節点
                have hnr0 : nextrel0 ((bd, y) :: (A ++ [])) 0
                    (((bd, y) :: (A ++ [])).length - 1) := by
                  rw [← hj00]; exact hnrp
                have hBA : ((bd, y) :: (A ++ [])) = (((bd, y) : ℕ × ℕ) :: A) := by simp
                have hmin : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1 := by
                  intro c hcm
                  obtain ⟨i, hi, hei⟩ := entry_of_mem hcm
                  rw [hBA] at hnr0
                  have key : entry (((bd, y) : ℕ × ℕ) :: A) 0
                      ((((bd, y) : ℕ × ℕ) :: A).length - 1)
                      ≤ entry (((bd, y) : ℕ × ℕ) :: A) 0 (i + 1) := by
                    rcases Nat.lt_or_ge (i + 1) ((((bd, y) : ℕ × ℕ) :: A).length - 1)
                      with hlt | hge
                    · exact hnr0.2.2.2.2 (i + 1) ⟨by omega, hlt⟩
                    · have hie : i + 1 = (((bd, y) : ℕ × ℕ) :: A).length - 1 := by
                        simp only [List.length_cons] at hge ⊢
                        omega
                      rw [hie]
                  have h1 : entry (((bd, y) : ℕ × ℕ) :: A) 0 (i + 1) = entry A 0 i :=
                    entry_cons_succ _ _ _ _
                  have h2 : entry (((bd, y) : ℕ × ℕ) :: A) 0 ((A.length - 1) + 1)
                      = entry A 0 (A.length - 1) := entry_cons_succ _ _ _ _
                  have h3 : (((bd, y) : ℕ × ℕ) :: A).length - 1 = (A.length - 1) + 1 := by
                    simp only [List.length_cons]
                    omega
                  rw [h3, h2, h1] at key
                  rw [← hei, ← entry_last0]
                  exact key
                have hlevA' : (A.getLastD (0, 0)).2 = 0 := by rw [← hlastA]; exact hlplev
                by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
                · by_cases hfc : force = true
                  · exact H ((bd, y) : ℕ × ℕ) A [] bd d plev first force hb hc hd hbd rfl
                      hAdeep (Or.inl rfl) hlev (Or.inr ⟨rfl, Or.inr hfc⟩) n hn
                  · have hfc' : force = false := by
                      cases force with
                      | false => rfl
                      | true => exact absurd rfl hfc
                    subst hfc'
                    have hdy : d ≤ ((bd, y) : ℕ × ℕ).2 := by
                      unfold ladOf at hlad
                      by_contra hgt
                      rw [decide_eq_false (by omega)] at hlad
                      simp at hlad
                    have hyd : ((bd, y) : ℕ × ℕ).2 ≤ ((bd, y) : ℕ × ℕ).1 :=
                      hc _ (by simp)
                    have hdp : d = ((bd, y) : ℕ × ℕ).2 := by
                      simp only [] at hdy hyd ⊢
                      omega
                    have h := reindexD_node0_lad_shape hAne hAdeep hmin hlevA'
                      d plev first false hlad hdp n hn
                    obtain ⟨m, n', k1, k2, k3⟩ := h
                    exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
                · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                    cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                    | false => rfl
                    | true => exact absurd hx hlad
                  by_cases hfr : (first && (((bd, y) : ℕ × ℕ).2 == plev)) = true
                  · exact H ((bd, y) : ℕ × ℕ) A [] bd d plev first force hb hc hd hbd rfl
                      hAdeep (Or.inl rfl) hlev (Or.inr ⟨rfl, Or.inl hfr⟩) n hn
                  · have hfr' : (first && (((bd, y) : ℕ × ℕ).2 == plev)) = false := by
                      cases hx : (first && (((bd, y) : ℕ × ℕ).2 == plev)) with
                      | false => rfl
                      | true => exact absurd hx hfr
                    obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_gen_shape hAne hAdeep hmin
                      hlevA' d plev first force hnl hfr' n hn
                    exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
              · -- 場合 (c): 引数ブロックへ降りる
                have hge1 : 1 ≤ parent ((bd, y) :: (A ++ [])) 0
                    (((bd, y) :: (A ++ [])).length - 1) := by omega
                have hpB : hasParent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                    (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
                  rw [hiA, ← hidx, ← hBeq]; exact hpar
                have hgeB : ([((bd, y) : ℕ × ℕ)] : PairSeq).length
                    ≤ parent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                        (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
                  rw [hiA, ← hidx, ← hBeq]
                  simpa using hge1
                by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
                · have hIH := ih A (by omega) (bd + 1) (d + 2) ((bd, y) : ℕ × ℕ).2 true false
                    hbA hcA hdA (by omega) (by omega) hlevA
                  have hres := reindexD_arg_lad (p := ((bd, y) : ℕ × ℕ)) hAdeep hlad hbA hcA hdA
                    (by omega) hzA hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
                · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                    cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                    | false => rfl
                    | true => exact absurd hx hlad
                  have hIH := ih A (by omega) (bd + 1)
                    (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
                    ((bd, y) : ℕ × ℕ).2 true (first && (((bd, y) : ℕ × ℕ).2 == plev))
                    hbA hcA hdA
                    (by have := le_ddOf ((bd, y) : ℕ × ℕ).2 d plev first force; omega)
                    (by omega) hlevA
                  have hres := reindexD_arg_nolad (p := ((bd, y) : ℕ × ℕ)) hAdeep hnl hbA hcA hdA
                    (by omega) hzA hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
            · -- 兄弟が空でない: 親は兄弟の中にある
              have hTne : T ≠ [] := hTe
              have hT1 : 1 ≤ T.length := List.length_pos_of_ne_nil hTne
              have hTh : ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
                rcases hThd with h | h
                · exact absurd h hTne
                · exact h
              have hBeq : ((bd, y) :: (A ++ T))
                  = (((bd, y) : ℕ × ℕ) :: A) ++ T := by simp
              have hidx : ((bd, y) :: (A ++ T)).length - 1
                  = (((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1) := by
                simp only [List.length_cons, List.length_append]
                omega
              have hlastT : ((bd, y) :: (A ++ T)).getLastD (0, 0) = T.getLastD (0, 0) := by
                rw [hBeq]; exact getLastD_append_right hTne _
              have hlevT : entry T 1 (T.length - 1) = 0 := by
                rw [entry_last, ← hlastT]; exact hlplev
              have hiT : idx1 T (T.length - 1) = 0 := by
                rw [idx1, if_neg (by rw [hlevT]; omega)]
              have hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0) := by
                rintro ⟨h1, -⟩
                rw [entry_last0, ← hlastT] at h1
                omega
              -- 親は `p :: A` より後ろ
              have hgeT : (((bd, y) : ℕ × ℕ) :: A).length
                  ≤ parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1) := by
                by_contra hlt
                have hlt' : parent ((bd, y) :: (A ++ T)) 0
                    (((bd, y) :: (A ++ T)).length - 1)
                    < (((bd, y) : ℕ × ℕ) :: A).length := by omega
                have hhead : entry ((bd, y) :: (A ++ T)) 0
                    ((((bd, y) : ℕ × ℕ) :: A).length) = (T.headI).1 := by
                  rw [hBeq,
                    show (((bd, y) : ℕ × ℕ) :: A).length
                      = (((bd, y) : ℕ × ℕ) :: A).length + 0 by omega,
                    entry_append_right, entry_zero0]
                have hthead : (T.headI).1 ≤ bd := by omega
                rcases Nat.lt_or_ge ((((bd, y) : ℕ × ℕ) :: A).length)
                    (((bd, y) :: (A ++ T)).length - 1) with hcase | hcase
                · have := hnrp.2.2.2.2 ((((bd, y) : ℕ × ℕ) :: A).length) ⟨by omega, hcase⟩
                  rw [entry_last0, hhead] at this
                  omega
                · have heq : (((bd, y) : ℕ × ℕ) :: A).length
                      = ((bd, y) :: (A ++ T)).length - 1 := by
                    simp only [List.length_cons, List.length_append] at hcase ⊢
                    omega
                  rw [heq, entry_last0] at hhead
                  omega
              have hpB : hasParent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                  ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
                rw [hiT, ← hidx, ← hBeq]; exact hpar
              have hgeB : (((bd, y) : ℕ × ℕ) :: A).length
                  ≤ parent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                      ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
                rw [hiT, ← hidx, ← hBeq]; exact hgeT
              have hIH := ih T (by omega) bd d ((bd, y) : ℕ × ℕ).2 false false
                hbT hcT hdT hbd hz0 hlevT
              by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
              · by_cases hnc : ∀ L : PairSeq,
                    contrLen ((bd, y) : ℕ × ℕ) L (unitsLen ((bd, y) : ℕ × ℕ) L) A = none
                · have hres := reindexD_sib_lad (p := ((bd, y) : ℕ × ℕ)) hAdeep hTh hlad hnc
                    hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  rw [← hBeq] at k3
                  exact ⟨m, n', k1, k2, k3⟩
                · exact H ((bd, y) : ℕ × ℕ) A T bd d plev first force hb hc hd hbd rfl
                    hAdeep hThd hlev (Or.inl ⟨hlad, hnc⟩) n hn
              · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                  cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                  | false => rfl
                  | true => exact absurd hx hlad
                have hres := reindexD_sib_nolad (p := ((bd, y) : ℕ × ℕ)) hAdeep hTh hnl
                  hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
                obtain ⟨m, n', k1, k2, k3⟩ := hres
                rw [← hBeq] at k3
                exact ⟨m, n', k1, k2, k3⟩
          · -- 場合 (b): 親がない
            exact reindexD_noParent_zero d plev first force hL2 hlev hz hpar n hn

/-- **段 0 の組み立て（入口）**: 標準形の末尾列の段が 0 なら、`RDzeroRes` だけで
`ReindexD` の形が出る。 -/
theorem reindexD_zero (H : RDzeroRes) {M : PairSeq} (hM : ST_PS M)
    (hlev : entry M 1 (M.length - 1) = 0) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧ (conC M)⟦m⟧ = conC (M⟦n'⟧) := by
  intro n hn
  have h := reindexD_zero_block H M.length M (Nat.le_refl _) 0 0 0 true false
    (blockok_ST_PS hM) (colOK_ST_PS hM) (descOK_ST_PS hM) (Nat.le_refl 0)
    (fun _ => rfl) hlev n hn
  obtain ⟨m, n', h1, h2, h3⟩ := h
  exact ⟨m, n', h1, h2, by rw [conC, conC]; exact h3⟩

/-- 残るのは末尾列の段が正の場合だけ。 -/
def ReindexD_pos : Prop :=
  ∀ {A : PairSeq}, ST_PS A → 1 < A.length → 0 < entry A 1 (A.length - 1) →
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧ (conC A)⟦m⟧ = conC (A⟦n'⟧)

/-- **いまの到達点**: `ReindexD` は
  * 段 0 で残った 2 つの場合（`RDzeroRes`）
  * 段が正の場合すべて（`ReindexD_pos`）
の 2 つだけに絞られた。 -/
theorem reindexD_holds_of_zero (H : RDzeroRes) (Hp : ReindexD_pos) : ReindexD := by
  intro A hA hL n hn
  by_cases hz : entry A 1 (A.length - 1) = 0
  · exact reindexD_zero H hA hz n hn
  · exact Hp hA hL (by omega) n hn

/-- 同じ形で主定理まで。 -/
theorem ST_D_conC_holds_of_zero (H : RDzeroRes) (Hp : ReindexD_pos)
    {M : PairSeq} (hM : ST_PS M) : ST_D (conC M) :=
  ST_D_conC (reindexD_holds_of_zero H Hp) hM

/-! ## 4.11 段が正の場合の組み立て

段 0 と違い、止まり方 (b)（親なし）と (d)（親が節点）はどちらも局所では
閉じない:

* (b) は `contrOK B` が要る（段 0 では `contrOK_of_last_zero` で自動だった）
* (d) はコピーが入れ子になる（`shift` regime）ので「ずれたコピーの補題」が要る

そこでこの 2 つと、梯子つきの段での縮約を `RDposRes` に括り出す。
右端の道の場合分けそのものは閉じる。要は**床の補題** `le0_ge_of_append`:
末尾が兄弟ブロックの中にあるなら、行 1 の親（行 0 の祖先でもある）は
節点や引数ブロックの中には入れない。 -/

/-- **段が正のときに残っている 3 つの場合。** -/
def RDposRes : Prop :=
  ∀ (p : ℕ × ℕ) (A T : PairSeq) (bd d plev : ℕ) (first force : Bool),
    blockok bd (p :: (A ++ T)) → colOK (p :: (A ++ T)) → descOK (p :: (A ++ T)) →
    bd ≤ d → p.1 = bd → 2 ≤ (p :: (A ++ T)).length →
    (∀ x ∈ A, p.1 < x.1) → (T = [] ∨ ¬ (p.1 < (T.headI).1)) →
    0 < entry (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) →
    ((ladOf p.2 d plev first force = true ∧
        ¬ (∀ L : PairSeq, contrLen p L (unitsLen p L) A = none))
      ∨ ¬ hasParent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1)
      ∨ (T = [] ∧ parent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) = 0)) →
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ T)) d plev first force)⟦m⟧
        = convC ((p :: (A ++ T))⟦n'⟧) d plev first force

/-- **段が正の場合の組み立て**（ブロック版）。 -/
theorem reindexD_pos_block (H : RDposRes) :
    ∀ (N : ℕ) (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → 2 ≤ B.length →
      0 < entry B 1 (B.length - 1) →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force := by
  intro N
  induction N with
  | zero =>
    intro B hB bd d plev first force _ _ _ _ h2 _ n hn
    exact absurd hB (by omega)
  | succ N ih =>
    intro B hB bd d plev first force hb hc hd hbd h2 hlev n hn
    cases B with
    | nil => exact absurd h2 (by simp)
    | cons p r =>
      have hp1 : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp1]⟩
      obtain ⟨A, T, hAd, hTd⟩ :
          ∃ A T, A = (r.takeWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) ∧
                 T = (r.dropWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) := ⟨_, _, rfl, rfl⟩
      have hrAT : r = A ++ T := by
        rw [hAd, hTd]; exact (List.takeWhile_append_dropWhile).symm
      subst hrAT
      have hAdeep : ∀ x ∈ A, ((bd, y) : ℕ × ℕ).1 < x.1 := by
        intro x hx
        rw [hAd] at hx
        simpa using List.mem_takeWhile_imp hx
      have hThd : T = [] ∨ ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
        rw [hTd]; exact dropWhile_head_not _ _
      obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := ((bd, y) : ℕ × ℕ).1)
        hAdeep hThd
      have hbA : blockok (bd + 1) A := by rw [← e1]; exact blockok_arg hb
      have hbT : blockok bd T := by rw [← e2]; exact blockok_tail hb
      have hcA : colOK A := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_left A T))) hc
      have hcT : colOK T := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_right A T))) hc
      obtain ⟨hdh, hdA, hdT⟩ := descOK_cons.1 hd
      rw [e1] at hdA
      rw [e2] at hdh hdT
      have hlAT : A.length + T.length ≤ N := by
        simp only [List.length_cons, List.length_append] at hB
        omega
      have hlen : ((bd, y) :: (A ++ T)).length = A.length + T.length + 1 := by simp
      have hi1 : idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1) = 1 := by
        rw [idx1, if_pos hlev]
      by_cases hpar : hasParent ((bd, y) :: (A ++ T)) 1
          (((bd, y) :: (A ++ T)).length - 1)
      · have hnr1 : nextrel1 ((bd, y) :: (A ++ T))
            (parent ((bd, y) :: (A ++ T)) 1 (((bd, y) :: (A ++ T)).length - 1))
            (((bd, y) :: (A ++ T)).length - 1) := by
          have h := parent_nextR hpar
          unfold nextR at h; rw [if_neg (by omega)] at h; exact h
        by_cases hTe : T = []
        · -- 兄弟が空: ブロックは p :: A
          subst hTe
          have hAne : A ≠ [] := by
            intro he
            rw [he] at h2
            simp at h2
          have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
          have hlastA : ((bd, y) :: (A ++ [])).getLastD (0, 0) = A.getLastD (0, 0) := by
            rw [List.append_nil]; exact getLastD_cons_ne _ hAne _
          have hlevA : 0 < entry A 1 (A.length - 1) := by
            rw [entry_last, ← hlastA, ← entry_last]; exact hlev
          have hiA : idx1 A (A.length - 1) = 1 := by rw [idx1, if_pos hlevA]
          have hzA : ¬ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0) := by
            rintro ⟨-, h1⟩
            omega
          have hidx : ((bd, y) :: (A ++ [])).length - 1
              = ([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1) := by
            simp only [List.length_cons, List.length_nil, List.append_nil]
            omega
          have hBeq : ((bd, y) :: (A ++ [])) = [((bd, y) : ℕ × ℕ)] ++ A := by simp
          by_cases hj00 : parent ((bd, y) :: (A ++ []))
              1 (((bd, y) :: (A ++ [])).length - 1) = 0
          · -- 場合 (d): 親が節点（段 > 0 は未証明）
            exact H ((bd, y) : ℕ × ℕ) A [] bd d plev first force hb hc hd hbd rfl h2
              hAdeep (Or.inl rfl) hlev (Or.inr (Or.inr ⟨rfl, hj00⟩)) n hn
          · -- 場合 (c): 引数ブロックへ降りる
            have hlenA : ((bd, y) :: (A ++ [])).length - 1 = A.length := by simp
            have hA2 : 2 ≤ A.length := by
              have hj0lt := hnr1.2.2.1
              have hj0ne : parent ((bd, y) :: (A ++ [])) 1
                  (((bd, y) :: (A ++ [])).length - 1) ≠ 0 := hj00
              omega
            have hpB : hasParent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
              rw [hiA, ← hidx, ← hBeq]; exact hpar
            have hgeB : ([((bd, y) : ℕ × ℕ)] : PairSeq).length
                ≤ parent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                    (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
              rw [hiA, ← hidx, ← hBeq]
              show 1 ≤ parent ((bd, y) :: (A ++ [])) 1 (((bd, y) :: (A ++ [])).length - 1)
              omega
            by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
            · have hIH := ih A (by omega) (bd + 1) (d + 2) ((bd, y) : ℕ × ℕ).2 true false
                hbA hcA hdA (by omega) hA2 hlevA
              obtain ⟨m, n', k1, k2, k3⟩ := reindexD_arg_lad (p := ((bd, y) : ℕ × ℕ))
                hAdeep hlad hbA hcA hdA (by omega) hzA hpB hgeB hIH n hn
              exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
            · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                | false => rfl
                | true => exact absurd hx hlad
              have hIH := ih A (by omega) (bd + 1)
                (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
                ((bd, y) : ℕ × ℕ).2 true (first && (((bd, y) : ℕ × ℕ).2 == plev))
                hbA hcA hdA
                (by have := le_ddOf ((bd, y) : ℕ × ℕ).2 d plev first force; omega)
                hA2 hlevA
              obtain ⟨m, n', k1, k2, k3⟩ := reindexD_arg_nolad (p := ((bd, y) : ℕ × ℕ))
                hAdeep hnl hbA hcA hdA (by omega) hzA hpB hgeB hIH n hn
              exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
        · -- 兄弟が空でない: 床の補題で親は兄弟の中
          have hTne : T ≠ [] := hTe
          have hT1 : 1 ≤ T.length := List.length_pos_of_ne_nil hTne
          have hTh : ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
            rcases hThd with h | h
            · exact absurd h hTne
            · exact h
          have hBeq : ((bd, y) :: (A ++ T)) = (((bd, y) : ℕ × ℕ) :: A) ++ T := by simp
          have hidx : ((bd, y) :: (A ++ T)).length - 1
              = (((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1) := by
            simp only [List.length_cons, List.length_append]
            omega
          have hlastT : ((bd, y) :: (A ++ T)).getLastD (0, 0) = T.getLastD (0, 0) := by
            rw [hBeq]; exact getLastD_append_right hTne _
          have hlevT : 0 < entry T 1 (T.length - 1) := by
            rw [entry_last, ← hlastT, ← entry_last]; exact hlev
          have hiT : idx1 T (T.length - 1) = 1 := by rw [idx1, if_pos hlevT]
          have hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0) := by
            rintro ⟨-, h1⟩
            omega
          -- 床の補題
          have hlowG : ∀ c ∈ (((bd, y) : ℕ × ℕ) :: A), bd ≤ c.1 := by
            intro c hcm
            refine hb.2.1 c ?_
            rw [hBeq]
            exact List.mem_append_left _ hcm
          have hhead : (T.headI).1 = bd := hbT.1 hTne
          have hle0 : le0 ((((bd, y) : ℕ × ℕ) :: A) ++ T)
              (parent ((bd, y) :: (A ++ T)) 1 (((bd, y) :: (A ++ T)).length - 1))
              (((bd, y) :: (A ++ T)).length - 1) := by
            rw [← hBeq]; exact hnr1.2.2.2.2.1
          have hgeT : (((bd, y) : ℕ × ℕ) :: A).length
              ≤ parent ((bd, y) :: (A ++ T)) 1 (((bd, y) :: (A ++ T)).length - 1) :=
            le0_ge_of_append hTne hlowG hhead hle0 (by rw [hidx]; omega)
          have hj0lt := hnr1.2.2.1
          have hT2 : 2 ≤ T.length := by
            simp only [List.length_cons, List.length_append] at hj0lt hgeT
            omega
          have hpB : hasParent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
              ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
            rw [hiT, ← hidx, ← hBeq]; exact hpar
          have hgeB : (((bd, y) : ℕ × ℕ) :: A).length
              ≤ parent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                  ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
            rw [hiT, ← hidx, ← hBeq]; exact hgeT
          have hIH := ih T (by omega) bd d ((bd, y) : ℕ × ℕ).2 false false
            hbT hcT hdT hbd hT2 hlevT
          by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
          · by_cases hnc : ∀ L : PairSeq,
                contrLen ((bd, y) : ℕ × ℕ) L (unitsLen ((bd, y) : ℕ × ℕ) L) A = none
            · obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_lad (p := ((bd, y) : ℕ × ℕ))
                hAdeep hTh hlad hnc hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
              rw [← hBeq] at k3
              exact ⟨m, n', k1, k2, k3⟩
            · exact H ((bd, y) : ℕ × ℕ) A T bd d plev first force hb hc hd hbd rfl h2
                hAdeep hThd hlev (Or.inl ⟨hlad, hnc⟩) n hn
          · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
              cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
              | false => rfl
              | true => exact absurd hx hlad
            obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_nolad (p := ((bd, y) : ℕ × ℕ))
              hAdeep hTh hnl hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
            rw [← hBeq] at k3
            exact ⟨m, n', k1, k2, k3⟩
      · -- 場合 (b): 親がない（段 > 0 では contrOK が要る）
        exact H ((bd, y) : ℕ × ℕ) A T bd d plev first force hb hc hd hbd rfl h2
          hAdeep hThd hlev (Or.inr (Or.inl hpar)) n hn

/-- 段が正の場合も `RDposRes` だけに絞られた。 -/
theorem reindexD_pos_of (H : RDposRes) : ReindexD_pos := by
  intro A hA hL hlev n hn
  have h := reindexD_pos_block H A.length A (Nat.le_refl _) 0 0 0 true false
    (blockok_ST_PS hA) (colOK_ST_PS hA) (descOK_ST_PS hA) (Nat.le_refl 0)
    (by omega) hlev n hn
  obtain ⟨m, n', h1, h2, h3⟩ := h
  exact ⟨m, n', h1, h2, by rw [conC, conC]; exact h3⟩

/-- **到達点**: `ReindexD` は 2 つの残り `RDzeroRes` / `RDposRes` だけに絞られた。 -/
theorem reindexD_holds_of_res (H0 : RDzeroRes) (H1 : RDposRes) : ReindexD :=
  reindexD_holds_of_zero H0 (reindexD_pos_of H1)

/-- 同じ形で主定理まで。 -/
theorem ST_D_conC_holds_of_res (H0 : RDzeroRes) (H1 : RDposRes)
    {M : PairSeq} (hM : ST_PS M) : ST_D (conC M) :=
  ST_D_conC (reindexD_holds_of_res H0 H1) hM

/-! ## 4.12 BMS 標準形の局所的な事実: 隣り合う 3 列の禁止形

計画書に残っていた「BMS 標準形のより強い性質」に当たるもの。

    深さが狭義に増える隣り合う 3 列で、真ん中の段が左と同じ・右の段がそれ + 1

という形（`(0,0)(1,1)(2,1)(3,2)` 型）は BMS 2 行標準形には現れない。
これは
「節点の段 = その親の段 かつ その引数ブロックの頭の段 = 節点の段 + 1」
の**隣接による言い換え**である（節点が引数ブロックの頭なら親は直前の列、
その節点の引数ブロックの頭は直後の列）。`convC` の `force` が効くのは
この形のときだけなので、これが残り 2 つ（場合 (d) の `force` と、
段 > 0 の `contrOK`）の核になる。

実測: `tools/dbms` の全数走査で ≤10 列 2073826 個、違反 0。

証明は `oper` についての帰納。コピーの内側では形がそのまま元の行列に移り、
コピーの境をまたぐ形は
「末尾列の直前の列が末尾列の行 0 の親になる」→ `le0` → `nextrel1` の最小性
で潰れる。 -/

/-- 隣り合う 3 列の禁止形。 -/
def adj3 (M : PairSeq) (i : ℕ) : Prop :=
  (M.getD i (0, 0)).1 < (M.getD (i + 1) (0, 0)).1 ∧
  (M.getD (i + 1) (0, 0)).1 < (M.getD (i + 2) (0, 0)).1 ∧
  (M.getD (i + 1) (0, 0)).2 = (M.getD i (0, 0)).2 ∧
  (M.getD (i + 2) (0, 0)).2 = (M.getD (i + 1) (0, 0)).2 + 1

/-- 禁止形がどこにも現れない。 -/
def noAdj3 (M : PairSeq) : Prop := ∀ i, i + 2 < M.length → ¬ adj3 M i

/-- 列が一致する短い列に遺伝する。 -/
theorem noAdj3_of_agree {M N : PairSeq} (hlen : N.length ≤ M.length)
    (hag : ∀ i, i < N.length → N.getD i (0, 0) = M.getD i (0, 0))
    (hM : noAdj3 M) : noAdj3 N := by
  intro i hi hadj
  refine hM i (by omega) ?_
  have e0 := hag i (by omega)
  have e1 := hag (i + 1) (by omega)
  have e2 := hag (i + 2) (by omega)
  unfold adj3 at hadj ⊢
  rw [e0, e1, e2] at hadj
  exact hadj

/-- 接頭辞に遺伝する。 -/
theorem noAdj3_take {M : PairSeq} (k : ℕ) (hM : noAdj3 M) : noAdj3 (M.take k) := by
  refine noAdj3_of_agree (by rw [List.length_take]; omega) (fun i hi => ?_) hM
  rw [List.length_take] at hi
  exact getD_take (by omega)

/-- 対角には現れない（段が 1 ずつ上がるので真ん中と左の段が違う）。 -/
theorem noAdj3_diagSeq (v : ℕ) : noAdj3 (diagSeq 0 v) := by
  intro i hi hadj
  rw [diagSeq0_length] at hi
  obtain ⟨-, -, h3, -⟩ := hadj
  rw [diagSeq0_getD (show i < v + 1 by omega),
    diagSeq0_getD (show i + 1 < v + 1 by omega)] at h3
  simp at h3

/-- 末尾列の直前の列が末尾列より浅ければ、それは末尾列の行 0 の親であり、
`nextrel1` の最小性で段が押さえられる。 -/
theorem entry1_last_le_of_lt {M : PairSeq} {j0 j1 : ℕ}
    (h1 : nextrel1 M j0 j1) (hj : j0 < j1 - 1) (hlt : entry M 0 (j1 - 1) < entry M 0 j1) :
    entry M 1 j1 ≤ entry M 1 (j1 - 1) := by
  have hj1 : j1 < M.length := h1.2.1
  have hne0 : nextrel0 M (j1 - 1) j1 := by
    refine ⟨by omega, hj1, by omega, hlt, ?_⟩
    intro j hjj
    omega
  have hle : le0 M (j1 - 1) j1 := ⟨by omega, hj1, Relation.ReflTransGen.single hne0⟩
  exact h1.2.2.2.2.2 (j1 - 1) ⟨by omega, hle⟩

/-- **BMS 2 行標準形には隣り合う 3 列の禁止形が現れない。** -/
theorem noAdj3_ST_PS {M : PairSeq} (hM : ST_PS M) : noAdj3 M := by
  induction hM with
  | diag v => exact noAdj3_diagSeq v
  | @oper M0 n hM0 hn ih =>
    by_cases hL : M0.length - 1 = 0
    · rw [oper_eq_self_of_short n hL]; exact ih
    have hL2 : 1 < M0.length := by omega
    have hPred : Pred M0 = M0.take (M0.length - 1) := by
      unfold Pred
      rw [if_neg (by omega), List.dropLast_eq_take]
    by_cases hz : entry M0 0 (M0.length - 1) = 0 ∧ entry M0 1 (M0.length - 1) = 0
    · rw [oper_eq_pred_of_zero n hL hz, hPred]; exact noAdj3_take _ ih
    by_cases hp : hasParent M0 (idx1 M0 (M0.length - 1)) (M0.length - 1)
    · obtain ⟨G, v0, w0, R, d0, lp, hMeq, hWeq, hR, hlp, hcase, -⟩ :=
        oper_bad_blocks hL2 hz hp hn
      have hMlen : M0.length = G.length + ((v0, w0) :: R).length + 1 := by
        rw [hMeq]; exact hostM_length _ _ _
      have hbpge : 1 ≤ ((v0, w0) :: R).length := by simp
      have hMpre : ∀ u, u < G.length → M0.getD u (0, 0) = G.getD u (0, 0) := by
        intro u hu; rw [hMeq]; exact hostM_getD_pre hu
      have hMblk : ∀ t, t < ((v0, w0) :: R).length →
          M0.getD (G.length + t) (0, 0) = ((v0, w0) :: R).getD t (0, 0) := by
        intro t ht; rw [hMeq]; exact hostM_getD_blk ht
      have hMhead : M0.getD (G.length + 0) (0, 0) = (v0, w0) := by
        rw [hMblk 0 (by simp)]; rfl
      have hMlast : M0.getD (G.length + ((v0, w0) :: R).length) (0, 0) = lp := by
        rw [hMeq, getD_append_right (by simp)]
        simp
      have hW : M0⟦n⟧ = copyExp G ((v0, w0) :: R) d0 n := by
        unfold copyExp; exact hWeq
      rw [hW]
      intro i hi hadj
      rw [copyExp_length] at hi
      have hWpre : ∀ u, u < G.length →
          (copyExp G ((v0, w0) :: R) d0 n).getD u (0, 0) = M0.getD u (0, 0) := by
        intro u hu; rw [copyExp_getD_pre hu, hMpre u hu]
      have hWcopy : ∀ k t, k < n → t < ((v0, w0) :: R).length →
          (copyExp G ((v0, w0) :: R) d0 n).getD
              (G.length + (k * ((v0, w0) :: R).length + t)) (0, 0)
            = ((M0.getD (G.length + t) (0, 0)).1 + k * d0,
               (M0.getD (G.length + t) (0, 0)).2) := by
        intro k t hk ht
        rw [copyExp_getD_copy hk ht, hMblk t ht]
      have hWlow : ∀ u, u < G.length + ((v0, w0) :: R).length →
          (copyExp G ((v0, w0) :: R) d0 n).getD u (0, 0) = M0.getD u (0, 0) := by
        intro u hu
        by_cases hug : u < G.length
        · exact hWpre u hug
        · have ht : u - G.length < ((v0, w0) :: R).length := by omega
          have hc := hWcopy 0 (u - G.length) (by omega) ht
          rw [show G.length + (0 * ((v0, w0) :: R).length + (u - G.length)) = u by omega,
            show G.length + (u - G.length) = u by omega] at hc
          rw [hc]
          simp
      by_cases hlow : i + 2 < G.length + ((v0, w0) :: R).length
      · refine ih i (by omega) ?_
        unfold adj3 at hadj ⊢
        rw [hWlow i (by omega), hWlow (i + 1) (by omega), hWlow (i + 2) (by omega)] at hadj
        exact hadj
      · by_cases hbp1 : ((v0, w0) :: R).length = 1
        · -- コピーが 1 列ずつ: 行 1 は全部 `w0` なので `+1` にはなれない
          have hrow1 : ∀ u, G.length ≤ u → u < G.length + n →
              ((copyExp G ((v0, w0) :: R) d0 n).getD u (0, 0)).2 = w0 := by
            intro u h1 h2
            have hc := hWcopy (u - G.length) 0 (by omega) (by omega)
            rw [show G.length + ((u - G.length) * ((v0, w0) :: R).length + 0) = u by
                rw [hbp1]; omega, hMhead] at hc
            rw [hc]
          rw [hbp1] at hi hlow
          obtain ⟨-, -, -, h4⟩ := hadj
          rw [hrow1 (i + 1) (by omega) (by omega),
            hrow1 (i + 2) (by omega) (by omega)] at h4
          omega
        · have hbp2 : 2 ≤ ((v0, w0) :: R).length := by omega
          have hRne : R ≠ [] := by
            intro h; rw [h] at hbp2; simp at hbp2
          have hig : G.length ≤ i := by omega
          obtain ⟨k, t, hk, ht, hkt⟩ :=
            index_decomp (L := ((v0, w0) :: R).length) (n := n) (i := i - G.length)
              (by omega) (by omega)
          have henext : (k + 1) * ((v0, w0) :: R).length
              = k * ((v0, w0) :: R).length + ((v0, w0) :: R).length := by
                rw [Nat.succ_mul]
          have hlastmem : M0.getD (G.length + (((v0, w0) :: R).length - 1)) (0, 0) ∈ R := by
            have hb : ((v0, w0) :: R).length - 1 = R.length := by simp
            rw [hb, hMblk R.length (by simp)]
            obtain ⟨m, hm⟩ : ∃ m, R.length = m + 1 :=
              ⟨R.length - 1, by have := List.length_pos_of_ne_nil hRne; omega⟩
            rw [hm, List.getD_cons_succ]
            exact getD_mem (by omega)
          have hkey : (M0.getD (G.length + (((v0, w0) :: R).length - 1)) (0, 0)).1 < v0 + d0 →
              w0 < (M0.getD (G.length + (((v0, w0) :: R).length - 1)) (0, 0)).2 := by
            intro hlt
            rcases hcase with ⟨hd0, -⟩ | ⟨hd0, -, hlpe, hnr1⟩
            · exfalso
              have hv := hR _ hlastmem
              omega
            · have hj1 : M0.length - 1 = G.length + ((v0, w0) :: R).length := by omega
              have he0 : entry M0 0 (M0.length - 1 - 1)
                  = (M0.getD (G.length + (((v0, w0) :: R).length - 1)) (0, 0)).1 := by
                rw [entry, if_pos rfl, hj1,
                  show G.length + ((v0, w0) :: R).length - 1
                    = G.length + (((v0, w0) :: R).length - 1) by omega]
              have he1 : entry M0 0 (M0.length - 1) = v0 + d0 := by
                rw [entry, if_pos rfl, hj1, hMlast, hlpe]
              have he2 : entry M0 1 (M0.length - 1 - 1)
                  = (M0.getD (G.length + (((v0, w0) :: R).length - 1)) (0, 0)).2 := by
                rw [entry, if_neg (by omega), hj1,
                  show G.length + ((v0, w0) :: R).length - 1
                    = G.length + (((v0, w0) :: R).length - 1) by omega]
              have hg1 : entry M0 1 G.length = w0 := by
                rw [entry, if_neg (by omega),
                  show G.length = G.length + 0 by omega, hMhead]
              have hstep := entry1_last_le_of_lt (M := M0) (j0 := G.length)
                (j1 := M0.length - 1) hnr1 (by omega) (by rw [he0, he1]; exact hlt)
              have hlt1 : entry M0 1 G.length < entry M0 1 (M0.length - 1) := hnr1.2.2.2.1
              rw [hg1] at hlt1
              rw [he2] at hstep
              omega
          by_cases htlow : t + 2 < ((v0, w0) :: R).length
          · -- コピーの内側
            refine ih (G.length + t) (by omega) ?_
            have A0f : ((copyExp G ((v0, w0) :: R) d0 n).getD i (0, 0)).1
                = (M0.getD (G.length + t) (0, 0)).1 + k * d0 := by
              rw [show i = G.length + (k * ((v0, w0) :: R).length + t) by omega,
                hWcopy k t hk (by omega)]
            have A0s : ((copyExp G ((v0, w0) :: R) d0 n).getD i (0, 0)).2
                = (M0.getD (G.length + t) (0, 0)).2 := by
              rw [show i = G.length + (k * ((v0, w0) :: R).length + t) by omega,
                hWcopy k t hk (by omega)]
            have hc1 := hWcopy k (t + 1) hk (by omega)
            rw [show G.length + (k * ((v0, w0) :: R).length + (t + 1)) = i + 1 by omega,
              show G.length + (t + 1) = G.length + t + 1 by omega] at hc1
            have hc2 := hWcopy k (t + 2) hk (by omega)
            rw [show G.length + (k * ((v0, w0) :: R).length + (t + 2)) = i + 2 by omega,
              show G.length + (t + 2) = G.length + t + 2 by omega] at hc2
            have A1f : ((copyExp G ((v0, w0) :: R) d0 n).getD (i + 1) (0, 0)).1
                = (M0.getD (G.length + t + 1) (0, 0)).1 + k * d0 := by rw [hc1]
            have A1s : ((copyExp G ((v0, w0) :: R) d0 n).getD (i + 1) (0, 0)).2
                = (M0.getD (G.length + t + 1) (0, 0)).2 := by rw [hc1]
            have A2f : ((copyExp G ((v0, w0) :: R) d0 n).getD (i + 2) (0, 0)).1
                = (M0.getD (G.length + t + 2) (0, 0)).1 + k * d0 := by rw [hc2]
            have A2s : ((copyExp G ((v0, w0) :: R) d0 n).getD (i + 2) (0, 0)).2
                = (M0.getD (G.length + t + 2) (0, 0)).2 := by rw [hc2]
            obtain ⟨h1, h2, h3, h4⟩ := hadj
            rw [A0f, A1f] at h1
            rw [A1f, A2f] at h2
            rw [A1s, A0s] at h3
            rw [A2s, A1s] at h4
            unfold adj3
            exact ⟨by omega, by omega, h3, h4⟩
          · -- コピーの境をまたぐ
            have hkn : k + 1 < n := by
              by_contra hcon
              have hle : n ≤ k + 1 := by omega
              have hmul : n * ((v0, w0) :: R).length
                  ≤ (k + 1) * ((v0, w0) :: R).length := Nat.mul_le_mul hle (le_refl _)
              omega
            have C1f : ((copyExp G ((v0, w0) :: R) d0 n).getD
                  (G.length + ((k + 1) * ((v0, w0) :: R).length + 0)) (0, 0)).1
                = v0 + (k + 1) * d0 := by
              rw [hWcopy (k + 1) 0 hkn (by omega), hMhead]
            have C1s : ((copyExp G ((v0, w0) :: R) d0 n).getD
                  (G.length + ((k + 1) * ((v0, w0) :: R).length + 0)) (0, 0)).2 = w0 := by
              rw [hWcopy (k + 1) 0 hkn (by omega), hMhead]
            have Lf : ((copyExp G ((v0, w0) :: R) d0 n).getD
                  (G.length + (k * ((v0, w0) :: R).length
                    + (((v0, w0) :: R).length - 1))) (0, 0)).1
                = (M0.getD (G.length + (((v0, w0) :: R).length - 1)) (0, 0)).1 + k * d0 := by
              rw [hWcopy k (((v0, w0) :: R).length - 1) hk (by omega)]
            have Ls : ((copyExp G ((v0, w0) :: R) d0 n).getD
                  (G.length + (k * ((v0, w0) :: R).length
                    + (((v0, w0) :: R).length - 1))) (0, 0)).2
                = (M0.getD (G.length + (((v0, w0) :: R).length - 1)) (0, 0)).2 := by
              rw [hWcopy k (((v0, w0) :: R).length - 1) hk (by omega)]
            have hd0e : (k + 1) * d0 = k * d0 + d0 := by rw [Nat.succ_mul]
            by_cases htA : t + 1 = ((v0, w0) :: R).length
            · rw [show G.length + (k * ((v0, w0) :: R).length
                  + (((v0, w0) :: R).length - 1)) = i by omega] at Lf Ls
              rw [show G.length + ((k + 1) * ((v0, w0) :: R).length + 0) = i + 1 by
                omega] at C1f C1s
              obtain ⟨h1, -, h3, -⟩ := hadj
              rw [Lf, C1f] at h1
              rw [C1s, Ls] at h3
              have := hkey (by omega)
              omega
            · have htB : t + 2 = ((v0, w0) :: R).length := by omega
              rw [show G.length + (k * ((v0, w0) :: R).length
                  + (((v0, w0) :: R).length - 1)) = i + 1 by omega] at Lf Ls
              rw [show G.length + ((k + 1) * ((v0, w0) :: R).length + 0) = i + 2 by
                omega] at C1f C1s
              obtain ⟨-, h2, -, h4⟩ := hadj
              rw [Lf, C1f] at h2
              rw [C1s, Ls] at h4
              have := hkey (by omega)
              omega
    · rw [oper_eq_pred_of_noParent n hL hz hp, hPred]; exact noAdj3_take _ ih


/-! ## 4.13 `noAdj3` を `convC` の `force` に繋ぐ

`convC` で `force` が効くのは、ある節点 `p` について

* `p` が引数ブロックの頭（`first = true`）で `p.2 = plev`（親と同じ段）
* `p` の引数ブロックの頭の段が `p.2 + 1`

の 2 つが同時に成り立つときだけである。この形は `noAdj3` そのものなので、
標準形では起こらない（根だけは `d = 0` で `convC_force` が使えるので別扱い）。

ここでは
* `noAdj3` が連続部分列に遺伝すること（`noAdj3_infix`）
* 各節点でその条件を述べる遺伝的な述語 `argPatOK`（`argPatOK_ST_PS`）
* `force` が効かないための弱い十分条件（`convC_force_head`）と
  `argPatOK` からその条件を出す補題（`convC_arg_force_eq`）
を用意する。ブロックの再帰に沿って `argPatOK` を運べば、
場合 (d) の `force` と段 > 0 の `contrOK` が消える見込み。 -/

/-- `noAdj3` は連続部分列に遺伝する。 -/
theorem noAdj3_infix {L M : PairSeq} (h : L.IsInfix M) (hM : noAdj3 M) : noAdj3 L := by
  obtain ⟨X, Y, hXY⟩ := h
  have hlen : M.length = X.length + L.length + Y.length := by
    rw [← hXY]; simp; omega
  have hg : ∀ j, j < L.length → M.getD (X.length + j) (0, 0) = L.getD j (0, 0) := by
    intro j hj
    rw [← hXY, getD_append_left (by rw [List.length_append]; omega),
      getD_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  intro i hi hadj
  refine hM (X.length + i) (by omega) ?_
  unfold adj3 at hadj ⊢
  rw [show X.length + i + 1 = X.length + (i + 1) by omega,
    show X.length + i + 2 = X.length + (i + 2) by omega,
    hg i (by omega), hg (i + 1) (by omega), hg (i + 2) (by omega)]
  exact hadj

/-- ブロック `B` の頭が親と同じ段なら、その引数ブロックの頭の段は「頭の段 + 1」ではない。 -/
def headPatOK (B : PairSeq) (plev : ℕ) : Prop :=
  ∀ p r, B = p :: r → p.2 = plev →
    (r.takeWhile fun x => p.1 < x.1) ≠ [] →
    ((r.takeWhile fun x => p.1 < x.1).headI).2 ≠ p.2 + 1

/-- どの節点でも、その引数ブロックについて `headPatOK` が成り立つ。 -/
def argPatOK : PairSeq → Prop
  | [] => True
  | p :: r =>
      headPatOK (r.takeWhile fun q => p.1 < q.1) p.2 ∧
      argPatOK (r.takeWhile fun q => p.1 < q.1) ∧
      argPatOK (r.dropWhile fun q => p.1 < q.1)
  termination_by M => M.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ r)

theorem argPatOK_nil : argPatOK [] := by rw [argPatOK]; trivial

theorem argPatOK_cons {p : ℕ × ℕ} {r : PairSeq} :
    argPatOK (p :: r) ↔
      headPatOK (r.takeWhile fun q => p.1 < q.1) p.2 ∧
      argPatOK (r.takeWhile fun q => p.1 < q.1) ∧
      argPatOK (r.dropWhile fun q => p.1 < q.1) := by
  rw [argPatOK]

theorem takeWhile_infix_cons (p : ℕ × ℕ) (r : PairSeq) :
    ((r.takeWhile fun q => p.1 < q.1)).IsInfix (p :: r) :=
  ⟨[p], r.dropWhile fun q => p.1 < q.1, by
    simp only [List.singleton_append, List.cons_append, List.cons.injEq, true_and]
    exact List.takeWhile_append_dropWhile⟩

theorem dropWhile_infix_cons (p : ℕ × ℕ) (r : PairSeq) :
    ((r.dropWhile fun q => p.1 < q.1)).IsInfix (p :: r) :=
  ⟨p :: (r.takeWhile fun q => p.1 < q.1), [], by
    simp only [List.append_nil, List.cons_append, List.cons.injEq, true_and]
    exact List.takeWhile_append_dropWhile⟩

/-- **`noAdj3` から `argPatOK` が出る。** -/
theorem argPatOK_of_noAdj3 : ∀ (N : ℕ) (M : PairSeq), M.length ≤ N → noAdj3 M → argPatOK M := by
  intro N
  induction N with
  | zero =>
    intro M hMl _
    have : M = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; exact argPatOK_nil
  | succ N ih =>
    intro M hMl hM
    match M with
    | [] => exact argPatOK_nil
    | p :: r =>
      have hA : (r.takeWhile fun q => p.1 < q.1).length ≤ N := by
        have := (List.takeWhile_sublist (fun q : ℕ × ℕ => p.1 < q.1) (l := r)).length_le
        simp only [List.length_cons] at hMl
        omega
      have hT : (r.dropWhile fun q => p.1 < q.1).length ≤ N := by
        have := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) r
        simp only [List.length_cons] at hMl
        omega
      refine argPatOK_cons.2 ⟨?_, ih _ hA (noAdj3_infix (takeWhile_infix_cons p r) hM),
        ih _ hT (noAdj3_infix (dropWhile_infix_cons p r) hM)⟩
      -- `headPatOK`: `noAdj3` を先頭の 3 列に当てる
      intro a s hAeq ha2 hne
      cases r with
      | nil => simp at hAeq
      | cons x r' =>
        by_cases hx : p.1 < x.1
        · rw [List.takeWhile_cons_of_pos (by simpa using hx)] at hAeq
          injection hAeq with hxa hs
          subst hxa
          subst hs
          cases r' with
          | nil => simp at hne
          | cons y r'' =>
            by_cases hy : p.1 < y.1
            · rw [List.takeWhile_cons_of_pos (by simpa using hy)] at hne ⊢
              by_cases hay : x.1 < y.1
              · rw [List.takeWhile_cons_of_pos (by simpa using hay)]
                intro hcon
                have g0 : ((p :: x :: y :: r'').getD 0 (0, 0)) = p := rfl
                have g1 : ((p :: x :: y :: r'').getD 1 (0, 0)) = x := rfl
                have g2 : ((p :: x :: y :: r'').getD 2 (0, 0)) = y := rfl
                refine hM 0 (by simp) ?_
                unfold adj3
                rw [show (0 : ℕ) + 1 = 1 from rfl, show (0 : ℕ) + 2 = 2 from rfl,
                  g0, g1, g2]
                exact ⟨hx, hay, ha2, by simpa using hcon⟩
              · rw [List.takeWhile_cons_of_neg (by simpa using hay)] at hne
                simp at hne
            · rw [List.takeWhile_cons_of_neg (by simpa using hy)] at hne
              simp at hne
        · rw [List.takeWhile_cons_of_neg (by simpa using hx)] at hAeq
          simp at hAeq

/-- **BMS 2 行標準形は `argPatOK`。** -/
theorem argPatOK_ST_PS {M : PairSeq} (hM : ST_PS M) : argPatOK M :=
  argPatOK_of_noAdj3 M.length M (Nat.le_refl _) (noAdj3_ST_PS hM)

/-- `force` が効かないための弱い十分条件（頭の列だけで済む）。 -/
theorem convC_force_head {L : PairSeq} {d plev : ℕ}
    (h : ∀ p r, L = p :: r → p.2 = plev + 1 → d ≤ p.2) (force force' : Bool) :
    convC L d plev true force = convC L d plev true force' := by
  match L with
  | [] => rw [convC_nil, convC_nil]
  | p :: r =>
    have hlad : ladOf p.2 d plev true force = ladOf p.2 d plev true force' := by
      unfold ladOf
      by_cases hs : p.2 = plev + 1
      · have hdp : d ≤ p.2 := h p r rfl hs
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

/-- **`headPatOK` があれば、節点 `p` から引数ブロックへ渡る `force` は効かない。** -/
theorem convC_arg_force_eq {p : ℕ × ℕ} {r : PairSeq} {plev dd : ℕ}
    (hhd : headPatOK (p :: r) plev) (hp : p.2 = plev) (b b' : Bool) :
    convC (r.takeWhile fun q => p.1 < q.1) dd p.2 true b
      = convC (r.takeWhile fun q => p.1 < q.1) dd p.2 true b' := by
  refine convC_force_head ?_ b b'
  intro a s hAeq ha
  exfalso
  have hne : (r.takeWhile fun x => p.1 < x.1) ≠ [] := by rw [hAeq]; simp
  have hkey := hhd p r rfl hp hne
  rw [hAeq] at hkey
  exact hkey (by simpa using ha)


/-- 頭の段が `plev + 1` でなければ梯子は立たない。 -/
theorem ladOf_false_of_ne {s d plev : ℕ} (first force : Bool) (h : s ≠ plev + 1) :
    ladOf s d plev first force = false := by
  unfold ladOf
  rw [beq_eq_false_iff_ne.2 h]
  simp

/-- 頭の段が `plev + 1` でなければ `force` は（`first` に依らず）効かない。
`argPatOK` の系として、ブロックへ入ってくる `force` はこれで消える。 -/
theorem convC_force_ne {L : PairSeq} {d plev : ℕ} (first force force' : Bool)
    (h : ∀ p r, L = p :: r → p.2 ≠ plev + 1) :
    convC L d plev first force = convC L d plev first force' := by
  match L with
  | [] => rw [convC_nil, convC_nil]
  | p :: r =>
    have hne : p.2 ≠ plev + 1 := h p r rfl
    have hl0 : ladOf p.2 d plev first force = false := ladOf_false_of_ne first force hne
    have hl0' : ladOf p.2 d plev first force' = false := ladOf_false_of_ne first force' hne
    have hdd : ddOf p.2 d plev first force = ddOf p.2 d plev first force' := by
      unfold ddOf; rw [hl0, hl0']
    rw [convC_cons_nolad p r d plev first force hl0,
      convC_cons_nolad p r d plev first force' hl0', hdd]

/-- **`headPatOK` は、引数ブロックへ入ってくる `force` を消す。**
節点 `p` が親と同じ段（`p.2 = plev`）なら、その引数ブロックの頭の段は
`p.2 + 1` ではないので、そこで梯子は立たず `force` は効かない。 -/
theorem convC_force_arg_ne {p : ℕ × ℕ} {r : PairSeq} {plev dd : ℕ}
    (hhd : headPatOK (p :: r) plev) (hp : p.2 = plev) (first force force' : Bool) :
    convC (r.takeWhile fun q => p.1 < q.1) dd p.2 first force
      = convC (r.takeWhile fun q => p.1 < q.1) dd p.2 first force' := by
  refine convC_force_ne first force force' ?_
  intro a s hAeq
  have hne : (r.takeWhile fun x => p.1 < x.1) ≠ [] := by rw [hAeq]; simp
  have hkey := hhd p r rfl hp hne
  rw [hAeq] at hkey
  simpa using hkey


/-! ## 4.13 不変量つきの右端の道の帰納（作り直し）

`RDposRes` はそのままでは偽だった（反例 `(1,1)(2,2)(2,1)(3,2)(3,1)`）。原因は
「節点の段 = 親の段 かつ その引数ブロックの頭の段 = 節点の段 + 1」という
BMS 標準形には現れない形（`noAdj3` で禁じた形）を排除していなかったこと。
そこで右端の道の帰納に

    hAP : argPatOK B                     子孫のブロックへ遺伝する
    hHP : first = true → headPatOK B plev ∨ 根の形
    hFC : force = true → その force は効かない

の 3 つの不変量を足して作り直す。根 `(0,0)` では `headPatOK` は**偽**なので
（引数の頭 `(1,1)` の段が `0 + 1`）、根の形 `d = 0 ∧ plev = 0 ∧ force = false` を
第 2 の枝として持たせ、根に着いた枝だけ別の道具で片付ける。 -/

/-- ブロックへ入ってくる `force` が効かないための十分条件。 -/
def fOK (B : PairSeq) (d plev : ℕ) (force : Bool) : Prop :=
  force = true → ((∀ a s, B = a :: s → a.2 ≠ plev + 1) ∨ d ≤ plev + 1)

/-- 頭の形の不変量。根だけ `headPatOK` が偽なので、根の形を第 2 の枝に持たせる。 -/
def hpOK (B : PairSeq) (d plev : ℕ) (first force : Bool) : Prop :=
  first = true → (headPatOK B plev ∨ (d = 0 ∧ plev = 0 ∧ force = false))

/-- `dropLast` が空でなければ先頭の列は変わらない。 -/
theorem headI_of_dropLast {A : PairSeq} {a : ℕ × ℕ} {s : PairSeq}
    (h : A.dropLast = a :: s) : A.headI = a := by
  obtain ⟨t, ht⟩ := List.dropLast_prefix A
  rw [h] at ht
  rw [← ht]
  rfl

/-- `colOK` なら `z0ok`（深さ 0 の列は段も 0）。 -/
theorem z0ok_of_colOK {M : PairSeq} (h : colOK M) : z0ok M := by
  intro j hj h0
  have hmem : M.getD j (0, 0) ∈ M := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simpa using List.getElem_mem hj
  have := h _ hmem
  omega

/-- `convC_run_first` の `hfr` を「引数ブロックの頭の段が `p.2 + 1` でない」に弱めた版。 -/
theorem convC_run_first2 (p : ℕ × ℕ) (R : PairSeq) (hR : ∀ c ∈ R, p.1 < c.1)
    (d plev : ℕ) (first force : Bool)
    (hnl : ladOf p.2 d plev first force = false)
    (hne : ∀ a s, R = a :: s → a.2 ≠ p.2 + 1) : ∀ n : ℕ,
    convC ((List.replicate n (p :: R)).flatten) d plev first force
      = (List.replicate n ((ddOf p.2 d plev first force, p.2)
          :: convC R (ddOf p.2 d plev first force + 1) p.2 true false)).flatten := by
  have hnl' : ladOf p.2 d p.2 false false = false := by simp [ladOf]
  have hdd : ddOf p.2 d p.2 false false = ddOf p.2 d plev first force := by
    unfold ddOf; rw [hnl', hnl]
  have hfe : convC R (ddOf p.2 d plev first force + 1) p.2 true (first && (p.2 == plev))
      = convC R (ddOf p.2 d plev first force + 1) p.2 true false :=
    convC_force_ne (L := R) (d := ddOf p.2 d plev first force + 1) (plev := p.2)
      true (first && (p.2 == plev)) false hne
  intro n
  match n with
  | 0 => simp
  | k + 1 =>
    have hrest : (List.replicate k (p :: R)).flatten = [] ∨
        ¬ (p.1 < (((List.replicate k (p :: R)).flatten).headI).1) := by
      cases k with
      | zero => exact Or.inl rfl
      | succ k' =>
        right
        rw [List.replicate_succ, List.flatten_cons, List.cons_append]
        simp
    obtain ⟨e1, e2⟩ := split_append (X := R) (dd := p.1) hR hrest
    have hrun := convC_run p R [] hR (Or.inl rfl) d p.2 k
    simp only [List.append_nil, convC_nil] at hrun
    rw [hdd] at hrun
    have hflat : (List.replicate (k + 1) (p :: R)).flatten
        = p :: (R ++ (List.replicate k (p :: R)).flatten) := by
      rw [List.replicate_succ, List.flatten_cons, List.cons_append]
    rw [hflat, convC_cons_nolad p _ d plev first force hnl, e1, e2, hfe, hrun,
      List.replicate_succ, List.flatten_cons, List.cons_append]


theorem reindexD_node0_gen2 {p : ℕ × ℕ} {A : PairSeq} (hAne : A ≠ [])
    (hA : ∀ c ∈ A, p.1 < c.1)
    (hmin : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1)
    (hlev : (A.getLastD (0, 0)).2 = 0)
    (d plev : ℕ) (first force : Bool)
    (hnl : ladOf p.2 d plev first force = false)
    (hne : ((A.headI).2) ≠ p.2 + 1) (n : ℕ) :
    (convC (p :: A) d plev first force)⟦n⟧ = convC ((p :: A)⟦n⟧) d plev first force := by
  have hneA : ∀ a s, A = a :: s → a.2 ≠ p.2 + 1 := by
    intro a s hs
    have hh : A.headI = a := by simp [hs]
    rw [hh] at hne; exact hne
  have hneR : ∀ a s, A.dropLast = a :: s → a.2 ≠ p.2 + 1 := by
    intro a s hs
    have hh : A.headI = a := headI_of_dropLast hs
    rw [hh] at hne; exact hne
  have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
  have hMlen : (p :: A).length = A.length + 1 := by simp
  have hL : 1 < (p :: A).length := by omega
  have hlmem : A.getLastD (0, 0) ∈ A := getLastD_mem hAne _
  have hplt : p.1 < (A.getLastD (0, 0)).1 := hA _ hlmem
  -- `A` の列は添字で読める
  have hgetA : ∀ j, j < A.length → (A.getLastD (0, 0)).1 ≤ entry A 0 j := by
    intro j hj
    have hmem : A.getD j (0, 0) ∈ A := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      simpa using List.getElem_mem hj
    rw [entry, if_pos rfl]
    exact hmin _ hmem
  -- 像の形
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := []) (dd := p.1) hA (Or.inl rfl)
  simp only [List.append_nil] at e1 e2
  have hconv : convC (p :: A) d plev first force
      = (ddOf p.2 d plev first force, p.2)
          :: convC A (ddOf p.2 d plev first force + 1) p.2 true false := by
    have hfe : convC A (ddOf p.2 d plev first force + 1) p.2 true (first && (p.2 == plev))
        = convC A (ddOf p.2 d plev first force + 1) p.2 true false :=
      convC_force_ne (L := A) (d := ddOf p.2 d plev first force + 1) (plev := p.2)
        true (first && (p.2 == plev)) false hneA
    rw [convC_cons_nolad p A d plev first force hnl, e1, e2, hfe]
    simp only [convC_nil, List.append_nil]
  -- BMS 側
  have hlastM : ((p :: A).getLastD (0, 0)) = A.getLastD (0, 0) := getLastD_cons_ne p hAne _
  have hlevM : entry (p :: A) 1 ((p :: A).length - 1) = 0 := by
    rw [entry_last, hlastM]; exact hlev
  have hnrM : nextrel0 (p :: A) 0 ((p :: A).length - 1) := by
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [entry_zero0, entry_last0, hlastM]
      exact hplt
    · rintro j ⟨hj1, hj2⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [entry_last0, hlastM, entry_cons_succ]
      exact hgetA j' (by omega)
  have hbms : (p :: A)⟦n⟧ = (List.replicate n ((p :: A).dropLast)).flatten :=
    oper_repeat_root n hL hlevM hnrM
  have hMdl : (p :: A).dropLast = p :: A.dropLast := dropLast_cons_ne hAne
  -- DBMS 側
  have hXne : convC A (ddOf p.2 d plev first force + 1) p.2 true false ≠ [] := by
    rw [ne_eq, convC_eq_nil_iff]; exact hAne
  have hX1 : 1 ≤ (convC A (ddOf p.2 d plev first force + 1) p.2 true false).length :=
    List.length_pos_of_ne_nil hXne
  have hXd : ((convC A (ddOf p.2 d plev first force + 1) p.2 true false).getLastD (0, 0)).1
      = ddOf p.2 d plev first force + 1 :=
    convC_getLast_min A.length A (Nat.le_refl _) hAne hmin hlev _ p.2 true false
  have hXl : ((convC A (ddOf p.2 d plev first force + 1) p.2 true false).getLastD (0, 0)).2
      = 0 := by
    rw [convC_getLast_level A.length A (Nat.le_refl _) _ p.2 true false]; exact hlev
  have hDlen : ((ddOf p.2 d plev first force, p.2)
      :: convC A (ddOf p.2 d plev first force + 1) p.2 true false).length
      = (convC A (ddOf p.2 d plev first force + 1) p.2 true false).length + 1 := by simp
  have hDL : 1 < ((ddOf p.2 d plev first force, p.2)
      :: convC A (ddOf p.2 d plev first force + 1) p.2 true false).length := by omega
  have hDlast : (((ddOf p.2 d plev first force, p.2)
      :: convC A (ddOf p.2 d plev first force + 1) p.2 true false).getLastD (0, 0))
      = (convC A (ddOf p.2 d plev first force + 1) p.2 true false).getLastD (0, 0) :=
    getLastD_cons_ne _ hXne _
  have hDlev : entry ((ddOf p.2 d plev first force, p.2)
      :: convC A (ddOf p.2 d plev first force + 1) p.2 true false) 1
      (((ddOf p.2 d plev first force, p.2)
        :: convC A (ddOf p.2 d plev first force + 1) p.2 true false).length - 1) = 0 := by
    rw [entry_last, hDlast]; exact hXl
  have hDnr : nextrel0 ((ddOf p.2 d plev first force, p.2)
      :: convC A (ddOf p.2 d plev first force + 1) p.2 true false) 0
      (((ddOf p.2 d plev first force, p.2)
        :: convC A (ddOf p.2 d plev first force + 1) p.2 true false).length - 1) := by
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [entry_zero0, entry_last0, hDlast, hXd]
      simp
    · rintro j ⟨hj1, hj2⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [entry_last0, hDlast, hXd, entry_cons_succ]
      have hj' : j' < (convC A (ddOf p.2 d plev first force + 1) p.2 true false).length := by
        rw [hDlen] at hj2; omega
      have hmem : (convC A (ddOf p.2 d plev first force + 1) p.2 true false).getD j' (0, 0)
          ∈ convC A (ddOf p.2 d plev first force + 1) p.2 true false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
        simpa using List.getElem_mem hj'
      rw [entry, if_pos rfl]
      exact convC_ge' A _ p.2 true false _ hmem
  have hdbms : ((ddOf p.2 d plev first force, p.2)
      :: convC A (ddOf p.2 d plev first force + 1) p.2 true false)⟦n⟧
      = (List.replicate n (((ddOf p.2 d plev first force, p.2)
          :: convC A (ddOf p.2 d plev first force + 1) p.2 true false).dropLast)).flatten :=
    oper_repeat_root n hDL hDlev hDnr
  -- `dropLast` の可換
  have hXdl : (convC A (ddOf p.2 d plev first force + 1) p.2 true false).dropLast
      = convC (A.dropLast) (ddOf p.2 d plev first force + 1) p.2 true false := by
    by_cases hA2 : 1 < A.length
    · have hco : contrOK A := contrOK_of_last_zero (by rw [entry_last]; exact hlev)
      have hiA : idx1 A (A.length - 1) = 0 := by
        rw [idx1, if_neg (by rw [entry_last, hlev]; omega)]
      have hnp : ¬ hasParent A (idx1 A (A.length - 1)) (A.length - 1) := by
        rw [hiA]
        rintro ⟨j0, hj0, -⟩
        have hj0' : nextrel0 A j0 (A.length - 1) := by
          have h : nextR A 0 j0 (A.length - 1) := hj0
          unfold nextR at h; rw [if_pos rfl] at h; exact h
        have h1 := hgetA j0 hj0'.1
        have h2 := hj0'.2.2.2.1
        rw [entry_last0] at h2
        omega
      exact (convC_dropLast_noParent_aux A.length A (Nat.le_refl _) hA2 _ p.2 true false
        hco hnp).symm
    · obtain ⟨lp, hlp⟩ : ∃ lp, A = [lp] := List.length_eq_one_iff.1 (by omega)
      have hlp2 : lp.2 = 0 := by rw [hlp] at hlev; simpa using hlev
      have hnl2 : ladOf lp.2 (ddOf p.2 d plev first force + 1) p.2 true false = false := by
        rw [hlp2]; simp [ladOf]
      rw [hlp]
      simp [convC_cons_nolad lp [] (ddOf p.2 d plev first force + 1) p.2 true false hnl2]
  -- 仕上げ
  have hRdeep : ∀ c ∈ A.dropLast, p.1 < c.1 :=
    fun c hc => hA c ((List.dropLast_sublist A).subset hc)
  rw [hconv, hdbms, hbms, hMdl, dropLast_cons_ne hXne, hXdl,
    convC_run_first2 p (A.dropLast) hRdeep d plev first force hnl hneR n]

/-- `reindexD_node0_gen2` を `ReindexD` の形で。 -/
theorem reindexD_node0_gen2_shape {p : ℕ × ℕ} {A : PairSeq} (hAne : A ≠ [])
    (hA : ∀ c ∈ A, p.1 < c.1)
    (hmin : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1)
    (hlev : (A.getLastD (0, 0)).2 = 0)
    (d plev : ℕ) (first force : Bool)
    (hnl : ladOf p.2 d plev first force = false)
    (hne : ((A.headI).2) ≠ p.2 + 1) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: A) d plev first force)⟦m⟧ = convC ((p :: A)⟦n'⟧) d plev first force :=
  fun n hn => ⟨n, n, hn, Nat.le_refl n,
    reindexD_node0_gen2 hAne hA hmin hlev d plev first force hnl hne n⟩


/-- `first = false` のブロックでは頭の形の不変量は自明。 -/
theorem hpOK_false {B : PairSeq} {d plev : ℕ} {force : Bool} : hpOK B d plev false force := by
  intro h; exact absurd h (by simp)

/-- `force = false` なら `fOK` は自明。 -/
theorem fOK_false {B : PairSeq} {d plev : ℕ} : fOK B d plev false := by
  intro h; exact absurd h (by simp)

/-- `headPatOK` があれば `hpOK`。 -/
theorem hpOK_of_headPatOK {B : PairSeq} {d plev : ℕ} {first force : Bool}
    (h : headPatOK B plev) : hpOK B d plev first force := fun _ => Or.inl h

/-- **不変量つきの段 0 で残っている 1 つの場合**（梯子つきの段での縮約）。 -/
def RDzeroRes2 : Prop :=
  ∀ (p : ℕ × ℕ) (A T : PairSeq) (bd d plev : ℕ) (first force : Bool),
    blockok bd (p :: (A ++ T)) → colOK (p :: (A ++ T)) → descOK (p :: (A ++ T)) →
    bd ≤ d → p.1 = bd →
    (∀ x ∈ A, p.1 < x.1) → (T = [] ∨ ¬ (p.1 < (T.headI).1)) →
    entry (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) = 0 →
    argPatOK (p :: (A ++ T)) →
    (first = true → headPatOK (p :: (A ++ T)) plev) →
    fOK (p :: (A ++ T)) d plev force →
    ladOf p.2 d plev first force = true →
    ¬ (∀ L : PairSeq, contrLen p L (unitsLen p L) A = none) →
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ T)) d plev first force)⟦m⟧
        = convC ((p :: (A ++ T))⟦n'⟧) d plev first force

/-- **段 0 の組み立て**（ブロック版・不変量つき）。残りは「梯子つきの段での縮約」1 つだけ。 -/
theorem reindexD_zero_block2 (H : RDzeroRes2) :
    ∀ (N : ℕ) (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → (bd = 0 → d = 0) →
      entry B 1 (B.length - 1) = 0 →
      argPatOK B → hpOK B d plev first force → fOK B d plev force →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force := by
  intro N
  induction N with
  | zero =>
    intro B hB bd d plev first force _ _ _ _ _ _ _ _ _ n hn
    have hBe : B = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hBe
    exact ⟨1, n, Nat.le_refl 1, Nat.le_refl n, by
      rw [convC_nil, oper_eq_self_short n (by simp), convC_nil,
        oper_eq_self_short 1 (by simp)]⟩
  | succ N ih =>
    intro B hB bd d plev first force hb hc hd hbd hz0 hlev hAP hHP hFC n hn
    cases B with
    | nil =>
      exact ⟨1, n, Nat.le_refl 1, Nat.le_refl n, by
        rw [convC_nil, oper_eq_self_short n (by simp), convC_nil,
          oper_eq_self_short 1 (by simp)]⟩
    | cons p r =>
      have hp1 : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp1]⟩
      -- 引数ブロックと兄弟ブロックに割る
      obtain ⟨A, T, hAd, hTd⟩ :
          ∃ A T, A = (r.takeWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) ∧
                 T = (r.dropWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) := ⟨_, _, rfl, rfl⟩
      have hrAT : r = A ++ T := by
        rw [hAd, hTd]; exact (List.takeWhile_append_dropWhile).symm
      subst hrAT
      have hAdeep : ∀ x ∈ A, ((bd, y) : ℕ × ℕ).1 < x.1 := by
        intro x hx
        rw [hAd] at hx
        simpa using List.mem_takeWhile_imp hx
      have hThd : T = [] ∨ ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
        rw [hTd]; exact dropWhile_head_not _ _
      obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := ((bd, y) : ℕ × ℕ).1)
        hAdeep hThd
      -- 新しい不変量を割る
      obtain ⟨hAPh, hAPa, hAPt⟩ := argPatOK_cons.1 hAP
      rw [e1] at hAPh hAPa
      rw [e2] at hAPt
      have hfA : fOK A (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
          ((bd, y) : ℕ × ℕ).2 (first && (((bd, y) : ℕ × ℕ).2 == plev)) := by
        intro hft
        have hf1 : first = true := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.1
        have hpl : ((bd, y) : ℕ × ℕ).2 = plev := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.2
        rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
        · left
          intro a s hs
          have hkey := hh ((bd, y) : ℕ × ℕ) (A ++ T) rfl hpl (by rw [e1, hs]; simp)
          rw [e1, hs] at hkey
          simpa using hkey
        · right
          subst hd0; subst hpl0; subst hfc0
          have hy0 : y = 0 := by simpa using hpl
          subst hy0
          simp [ddOf, ladOf]
      -- 不変量を割る
      have hbA : blockok (bd + 1) A := by rw [← e1]; exact blockok_arg hb
      have hbT : blockok bd T := by rw [← e2]; exact blockok_tail hb
      have hcA : colOK A := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_left A T))) hc
      have hcT : colOK T := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_right A T))) hc
      obtain ⟨hdh, hdA, hdT⟩ := descOK_cons.1 hd
      rw [e1] at hdA
      rw [e2] at hdh hdT
      have hlAT : A.length + T.length ≤ N := by
        simp only [List.length_cons, List.length_append] at hB
        omega
      -- 末尾列
      have hBne : ((bd, y) :: (A ++ T)) ≠ [] := by simp
      have hlplev : (((bd, y) :: (A ++ T)).getLastD (0, 0)).2 = 0 := by
        rw [← entry_last]; exact hlev
      by_cases hrne : A ++ T = []
      · -- 1 列のブロック
        obtain ⟨hAe, hTe⟩ := List.append_eq_nil_iff.1 hrne
        subst hAe; subst hTe
        have hy : y = 0 := by
          have h := hlplev
          simp only [List.append_nil, List.getLastD] at h
          simpa using h
        subst hy
        refine ⟨1, n, Nat.le_refl 1, Nat.le_refl n, ?_⟩
        have hnl : ladOf ((bd, 0) : ℕ × ℕ).2 d plev first force = false := by simp [ladOf]
        rw [List.append_nil, oper_eq_self_short n (by simp),
          convC_cons_nolad ((bd, 0) : ℕ × ℕ) [] d plev first force hnl]
        simp only [List.takeWhile_nil, List.dropWhile_nil, convC_nil, List.append_nil]
        exact oper_eq_self_short 1 (by simp)
      · have hL2 : 1 < ((bd, y) :: (A ++ T)).length := by
          simp only [List.length_cons]
          have := List.length_pos_of_ne_nil hrne
          omega
        have hlpmem : ((bd, y) :: (A ++ T)).getLastD (0, 0) ∈ ((bd, y) :: (A ++ T)) :=
          getLastD_mem hBne _
        by_cases hlp0 : (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 = 0
        · -- 場合 (a): 末尾列 = (0,0)
          have hbd0 : bd = 0 := by
            have := hb.2.1 _ hlpmem
            omega
          have hd0 : d = 0 := hz0 hbd0
          subst hd0
          have hlpeq : ((bd, y) :: (A ++ T)).getLastD (0, 0) = ((0, 0) : ℕ × ℕ) :=
            Prod.ext hlp0 hlplev
          have hg : ((bd, y) :: (A ++ T)).getLast hBne = ((0, 0) : ℕ × ℕ) := by
            rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast (h := hBne)] at hlpeq
            simpa using hlpeq
          have hsplit : ((bd, y) :: (A ++ T)).dropLast ++ [((0, 0) : ℕ × ℕ)]
              = ((bd, y) :: (A ++ T)) := by
            rw [← hg]; exact List.dropLast_append_getLast hBne
          have hdne : ((bd, y) :: (A ++ T)).dropLast ≠ [] := by
            intro he
            have hl : ((bd, y) :: (A ++ T)).dropLast.length
                = ((bd, y) :: (A ++ T)).length - 1 := List.length_dropLast
            rw [he] at hl
            simp only [List.length_nil] at hl
            omega
          have hcdl : colOK (((bd, y) :: (A ++ T)).dropLast) :=
            colOK_sublist (List.dropLast_sublist _) hc
          obtain ⟨m, n', h1, h2, h3⟩ := reindexD_succ_gen plev first force hdne hcdl n hn
          rw [hsplit] at h3
          exact ⟨m, n', h1, h2, h3⟩
        · -- 末尾列の深さは正
          have hlpos : 0 < (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 := by omega
          have hz : ¬ (entry ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1) = 0 ∧
                       entry ((bd, y) :: (A ++ T)) 1
                         (((bd, y) :: (A ++ T)).length - 1) = 0) := by
            rintro ⟨h1, -⟩
            rw [entry_last0] at h1
            omega
          have hi1 : idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1) = 0 := by
            rw [idx1, if_neg (by rw [hlev]; omega)]
          by_cases hpar : hasParent ((bd, y) :: (A ++ T))
              (idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1))
              (((bd, y) :: (A ++ T)).length - 1)
          · -- 親がある
            rw [hi1] at hpar
            have hnrp : nextrel0 ((bd, y) :: (A ++ T))
                (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1))
                (((bd, y) :: (A ++ T)).length - 1) := by
              have h := parent_nextR hpar
              unfold nextR at h; rw [if_pos rfl] at h; exact h
            have hj0ge : bd ≤ entry ((bd, y) :: (A ++ T)) 0
                (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1)) := by
              have hj := hnrp.1
              have hmem : ((bd, y) :: (A ++ T)).getD
                  (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1)) (0, 0)
                  ∈ ((bd, y) :: (A ++ T)) := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
                simpa using List.getElem_mem hj
              rw [entry, if_pos rfl]
              exact hb.2.1 _ hmem
            have hlpgt : bd < (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 := by
              have h1 := hnrp.2.2.2.1
              rw [entry_last0] at h1
              omega
            by_cases hTe : T = []
            · -- 兄弟が空: ブロックは p :: A
              subst hTe
              have hAne : A ≠ [] := by
                intro he; rw [he] at hrne; simp at hrne
              have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
              have hAlen : ((bd, y) :: (A ++ [])).length = A.length + 1 := by simp
              have hlastA : ((bd, y) :: (A ++ [])).getLastD (0, 0) = A.getLastD (0, 0) := by
                rw [List.append_nil]; exact getLastD_cons_ne _ hAne _
              have hlevA : entry A 1 (A.length - 1) = 0 := by
                rw [entry_last, ← hlastA]; exact hlplev
              have hiA : idx1 A (A.length - 1) = 0 := by
                rw [idx1, if_neg (by rw [hlevA]; omega)]
              have hzA : ¬ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0) := by
                rintro ⟨h1, -⟩
                rw [entry_last0, ← hlastA] at h1
                omega
              have hidx : ((bd, y) :: (A ++ [])).length - 1
                  = ([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1) := by
                simp only [List.length_cons, List.length_nil, List.append_nil]
                omega
              have hBeq : ((bd, y) :: (A ++ [])) = [((bd, y) : ℕ × ℕ)] ++ A := by simp
              by_cases hj00 : parent ((bd, y) :: (A ++ []))
                  0 (((bd, y) :: (A ++ [])).length - 1) = 0
              · -- 場合 (d): 親が節点
                have hnr0 : nextrel0 ((bd, y) :: (A ++ [])) 0
                    (((bd, y) :: (A ++ [])).length - 1) := by
                  rw [← hj00]; exact hnrp
                have hBA : ((bd, y) :: (A ++ [])) = (((bd, y) : ℕ × ℕ) :: A) := by simp
                have hmin : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1 := by
                  intro c hcm
                  obtain ⟨i, hi, hei⟩ := entry_of_mem hcm
                  rw [hBA] at hnr0
                  have key : entry (((bd, y) : ℕ × ℕ) :: A) 0
                      ((((bd, y) : ℕ × ℕ) :: A).length - 1)
                      ≤ entry (((bd, y) : ℕ × ℕ) :: A) 0 (i + 1) := by
                    rcases Nat.lt_or_ge (i + 1) ((((bd, y) : ℕ × ℕ) :: A).length - 1)
                      with hlt | hge
                    · exact hnr0.2.2.2.2 (i + 1) ⟨by omega, hlt⟩
                    · have hie : i + 1 = (((bd, y) : ℕ × ℕ) :: A).length - 1 := by
                        simp only [List.length_cons] at hge ⊢
                        omega
                      rw [hie]
                  have h1 : entry (((bd, y) : ℕ × ℕ) :: A) 0 (i + 1) = entry A 0 i :=
                    entry_cons_succ _ _ _ _
                  have h2 : entry (((bd, y) : ℕ × ℕ) :: A) 0 ((A.length - 1) + 1)
                      = entry A 0 (A.length - 1) := entry_cons_succ _ _ _ _
                  have h3 : (((bd, y) : ℕ × ℕ) :: A).length - 1 = (A.length - 1) + 1 := by
                    simp only [List.length_cons]
                    omega
                  rw [h3, h2, h1] at key
                  rw [← hei, ← entry_last0]
                  exact key
                have hlevA' : (A.getLastD (0, 0)).2 = 0 := by rw [← hlastA]; exact hlplev
                by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
                · -- 梯子つき: `fOK` が `force` を潰し、`d = p.2` が出る
                  have hlad2 : first = true ∧ ((bd, y) : ℕ × ℕ).2 = plev + 1
                      ∧ (d ≤ ((bd, y) : ℕ × ℕ).2 ∨ force = true) := by
                    unfold ladOf at hlad
                    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
                      decide_eq_true_eq] at hlad
                    exact ⟨hlad.1.1, hlad.1.2, hlad.2⟩
                  have hdy : d ≤ ((bd, y) : ℕ × ℕ).2 := by
                    rcases hlad2.2.2 with hh | hh
                    · exact hh
                    · rcases hFC hh with h1 | h2
                      · exact absurd hlad2.2.1 (h1 ((bd, y) : ℕ × ℕ) (A ++ []) rfl)
                      · have hpp := hlad2.2.1
                        simp only [] at hpp ⊢
                        omega
                  have hyd : ((bd, y) : ℕ × ℕ).2 ≤ ((bd, y) : ℕ × ℕ).1 :=
                    hc _ (by simp)
                  have hdp : d = ((bd, y) : ℕ × ℕ).2 := by
                    simp only [] at hdy hyd ⊢
                    omega
                  obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_lad_shape hAne hAdeep hmin
                    hlevA' d plev first force hlad hdp n hn
                  exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
                · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                    cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                    | false => rfl
                    | true => exact absurd hx hlad
                  by_cases hfr : (first && (((bd, y) : ℕ × ℕ).2 == plev)) = true
                  · -- `hpOK` で潰す枝
                    have hf1 : first = true := by
                      simp only [Bool.and_eq_true, beq_iff_eq] at hfr; exact hfr.1
                    have hpl : ((bd, y) : ℕ × ℕ).2 = plev := by
                      simp only [Bool.and_eq_true, beq_iff_eq] at hfr; exact hfr.2
                    rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
                    · have hkey := hh ((bd, y) : ℕ × ℕ) (A ++ []) rfl hpl
                        (by rw [e1]; exact hAne)
                      rw [e1] at hkey
                      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_gen2_shape hAne hAdeep
                        hmin hlevA' d plev first force hnl hkey n hn
                      exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
                    · -- 根: `conC` そのものなので `reindexD_node0` が効く
                      subst hd0; subst hpl0; subst hfc0; subst hf1
                      have hbd0 : bd = 0 := by omega
                      have hy0 : y = 0 := by
                        have hyc := hc ((bd, y) : ℕ × ℕ) (by simp)
                        simp only [] at hyc
                        omega
                      have hhd0 : ((bd, y) :: (A ++ [])).headI = ((0, 0) : ℕ × ℕ) := by
                        show ((bd, y) : ℕ × ℕ) = ((0, 0) : ℕ × ℕ)
                        rw [hbd0, hy0]
                      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_shape n hn hL2
                        (contrOK_of_last_zero hlev) hhd0 hlev hnr0
                      simp only [conC] at k3
                      exact ⟨m, n', k1, k2, k3⟩
                  · have hfr' : (first && (((bd, y) : ℕ × ℕ).2 == plev)) = false := by
                      cases hx : (first && (((bd, y) : ℕ × ℕ).2 == plev)) with
                      | false => rfl
                      | true => exact absurd hx hfr
                    obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_gen_shape hAne hAdeep hmin
                      hlevA' d plev first force hnl hfr' n hn
                    exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
              · -- 場合 (c): 引数ブロックへ降りる
                have hge1 : 1 ≤ parent ((bd, y) :: (A ++ [])) 0
                    (((bd, y) :: (A ++ [])).length - 1) := by omega
                have hpB : hasParent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                    (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
                  rw [hiA, ← hidx, ← hBeq]; exact hpar
                have hgeB : ([((bd, y) : ℕ × ℕ)] : PairSeq).length
                    ≤ parent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                        (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
                  rw [hiA, ← hidx, ← hBeq]
                  simpa using hge1
                by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
                · have hIH := ih A (by omega) (bd + 1) (d + 2) ((bd, y) : ℕ × ℕ).2 true false
                    hbA hcA hdA (by omega) (by omega) hlevA hAPa
                    (hpOK_of_headPatOK hAPh) fOK_false
                  have hres := reindexD_arg_lad (p := ((bd, y) : ℕ × ℕ)) hAdeep hlad hbA hcA hdA
                    (by omega) hzA hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
                · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                    cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                    | false => rfl
                    | true => exact absurd hx hlad
                  have hIH := ih A (by omega) (bd + 1)
                    (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
                    ((bd, y) : ℕ × ℕ).2 true (first && (((bd, y) : ℕ × ℕ).2 == plev))
                    hbA hcA hdA
                    (by have := le_ddOf ((bd, y) : ℕ × ℕ).2 d plev first force; omega)
                    (by omega) hlevA hAPa (hpOK_of_headPatOK hAPh) hfA
                  have hres := reindexD_arg_nolad (p := ((bd, y) : ℕ × ℕ)) hAdeep hnl hbA hcA hdA
                    (by omega) hzA hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
            · -- 兄弟が空でない: 親は兄弟の中にある
              have hTne : T ≠ [] := hTe
              have hT1 : 1 ≤ T.length := List.length_pos_of_ne_nil hTne
              have hTh : ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
                rcases hThd with h | h
                · exact absurd h hTne
                · exact h
              have hBeq : ((bd, y) :: (A ++ T))
                  = (((bd, y) : ℕ × ℕ) :: A) ++ T := by simp
              have hidx : ((bd, y) :: (A ++ T)).length - 1
                  = (((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1) := by
                simp only [List.length_cons, List.length_append]
                omega
              have hlastT : ((bd, y) :: (A ++ T)).getLastD (0, 0) = T.getLastD (0, 0) := by
                rw [hBeq]; exact getLastD_append_right hTne _
              have hlevT : entry T 1 (T.length - 1) = 0 := by
                rw [entry_last, ← hlastT]; exact hlplev
              have hiT : idx1 T (T.length - 1) = 0 := by
                rw [idx1, if_neg (by rw [hlevT]; omega)]
              have hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0) := by
                rintro ⟨h1, -⟩
                rw [entry_last0, ← hlastT] at h1
                omega
              -- 親は `p :: A` より後ろ
              have hgeT : (((bd, y) : ℕ × ℕ) :: A).length
                  ≤ parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1) := by
                by_contra hlt
                have hlt' : parent ((bd, y) :: (A ++ T)) 0
                    (((bd, y) :: (A ++ T)).length - 1)
                    < (((bd, y) : ℕ × ℕ) :: A).length := by omega
                have hhead : entry ((bd, y) :: (A ++ T)) 0
                    ((((bd, y) : ℕ × ℕ) :: A).length) = (T.headI).1 := by
                  rw [hBeq,
                    show (((bd, y) : ℕ × ℕ) :: A).length
                      = (((bd, y) : ℕ × ℕ) :: A).length + 0 by omega,
                    entry_append_right, entry_zero0]
                have hthead : (T.headI).1 ≤ bd := by omega
                rcases Nat.lt_or_ge ((((bd, y) : ℕ × ℕ) :: A).length)
                    (((bd, y) :: (A ++ T)).length - 1) with hcase | hcase
                · have := hnrp.2.2.2.2 ((((bd, y) : ℕ × ℕ) :: A).length) ⟨by omega, hcase⟩
                  rw [entry_last0, hhead] at this
                  omega
                · have heq : (((bd, y) : ℕ × ℕ) :: A).length
                      = ((bd, y) :: (A ++ T)).length - 1 := by
                    simp only [List.length_cons, List.length_append] at hcase ⊢
                    omega
                  rw [heq, entry_last0] at hhead
                  omega
              have hpB : hasParent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                  ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
                rw [hiT, ← hidx, ← hBeq]; exact hpar
              have hgeB : (((bd, y) : ℕ × ℕ) :: A).length
                  ≤ parent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                      ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
                rw [hiT, ← hidx, ← hBeq]; exact hgeT
              have hIH := ih T (by omega) bd d ((bd, y) : ℕ × ℕ).2 false false
                hbT hcT hdT hbd hz0 hlevT hAPt hpOK_false fOK_false
              by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
              · have hlad2 : first = true ∧ ((bd, y) : ℕ × ℕ).2 = plev + 1
                    ∧ (d ≤ ((bd, y) : ℕ × ℕ).2 ∨ force = true) := by
                  unfold ladOf at hlad
                  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
                    decide_eq_true_eq] at hlad
                  exact ⟨hlad.1.1, hlad.1.2, hlad.2⟩
                have hHP2 : first = true → headPatOK ((bd, y) :: (A ++ T)) plev := by
                  intro hf1
                  rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
                  · exact hh
                  · exfalso
                    have hyc := hc ((bd, y) : ℕ × ℕ) (by simp)
                    have hpp := hlad2.2.1
                    simp only [] at hyc hpp
                    omega
                by_cases hnc : ∀ L : PairSeq,
                    contrLen ((bd, y) : ℕ × ℕ) L (unitsLen ((bd, y) : ℕ × ℕ) L) A = none
                · have hres := reindexD_sib_lad (p := ((bd, y) : ℕ × ℕ)) hAdeep hTh hlad hnc
                    hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  rw [← hBeq] at k3
                  exact ⟨m, n', k1, k2, k3⟩
                · exact H ((bd, y) : ℕ × ℕ) A T bd d plev first force hb hc hd hbd rfl
                    hAdeep hThd hlev hAP hHP2 hFC hlad hnc n hn
              · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                  cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                  | false => rfl
                  | true => exact absurd hx hlad
                have hres := reindexD_sib_nolad (p := ((bd, y) : ℕ × ℕ)) hAdeep hTh hnl
                  hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
                obtain ⟨m, n', k1, k2, k3⟩ := hres
                rw [← hBeq] at k3
                exact ⟨m, n', k1, k2, k3⟩
          · -- 場合 (b): 親がない
            exact reindexD_noParent_zero d plev first force hL2 hlev hz hpar n hn


/-- **段 0 の組み立て（入口・不変量つき）**。根では `d = 0 ∧ plev = 0 ∧ force = false`
なので `hpOK` の第 2 の枝が使える。 -/
theorem reindexD_zero2 (H : RDzeroRes2) {M : PairSeq} (hM : ST_PS M)
    (hlev : entry M 1 (M.length - 1) = 0) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧ (conC M)⟦m⟧ = conC (M⟦n'⟧) := by
  intro n hn
  have h := reindexD_zero_block2 H M.length M (Nat.le_refl _) 0 0 0 true false
    (blockok_ST_PS hM) (colOK_ST_PS hM) (descOK_ST_PS hM) (Nat.le_refl 0)
    (fun _ => rfl) hlev (argPatOK_ST_PS hM)
    (fun _ => Or.inr ⟨rfl, rfl, rfl⟩) fOK_false n hn
  obtain ⟨m, n', h1, h2, h3⟩ := h
  exact ⟨m, n', h1, h2, by rw [conC, conC]; exact h3⟩


/-! ## 4.14 段 > 0 の右端の道の帰納を不変量つきで作り直す

旧版の残余 `RDposRes` は**偽**だった（計画書「続き 3」の反例
`B = (1,1)(2,2)(2,1)(3,2)(3,1)`）。段 0 側（`reindexD_zero_block2`）と同じように
不変量を足して作り直す。段 0 で足りた `argPatOK` / `hpOK` / `fOK` に加えて、
段 > 0 では次の 3 つが要る（`tools/dbms` の全数検査で反例を見つけて足したもの）:

* `adjLev`     隣り合う 2 列で深さが 1 上がるとき段は高々 1 しか上がらない
               （`r1ok` の隣接版。無いと `(1,0)(2,2)` のようなブロックが混ざる）
* `dpOK`       `d = bd` のときの親の段の制限
               （無いと `(2,2)(2,1)(3,2)(3,1)` を `d = 2` で呼べてしまう）
* `ctrHeadOK`  縮約の前置きが揃えば縮約は必ず発火する
               （無いと `(1,1)(1,0)(2,1)(2,1)` を梯子の位置で呼べてしまう）

最後のものだけ BMS 標準形の性質として未証明なので `CtrRes` に括り出す
（`Pair/ArgDom.lean` の `ArgDomCore` から出るはず。実測は ≤9 列 295014 個で違反 0）。 -/

/-- 隣り合う 2 列で深さが 1 上がるなら、段は高々 1 しか上がらない（`r1ok` の隣接版）。 -/
def adjLev (M : PairSeq) : Prop :=
  ∀ i, i + 1 < M.length →
    (M.getD (i + 1) (0, 0)).1 = (M.getD i (0, 0)).1 + 1 →
    (M.getD (i + 1) (0, 0)).2 ≤ (M.getD i (0, 0)).2 + 1

/-- `r1ok` の証人は「深さがちょうど 1 下で間に谷なし」なので、隣なら証人は隣。 -/
theorem adjLev_of_r1ok {M : PairSeq} (h : r1ok M) : adjLev M := by
  intro i hi hd
  have hpos : 0 < (M.getD (i + 1) (0, 0)).1 := by omega
  obtain ⟨k, hk, hk1, hk2, hk3⟩ := h (i + 1) hi hpos
  have hki : k = i := by
    by_contra hne
    have hlt : k < i := by omega
    have h2 := hk2 i hlt (by omega)
    omega
  subst hki
  exact hk3

theorem adjLev_ST_PS {M : PairSeq} (hM : ST_PS M) : adjLev M :=
  adjLev_of_r1ok (r1ok_ST_PS hM)

/-- `adjLev` は連続部分列に遺伝する。 -/
theorem adjLev_infix {L M : PairSeq} (h : L.IsInfix M) (hM : adjLev M) : adjLev L := by
  obtain ⟨X, Y, hXY⟩ := h
  have hlen : M.length = X.length + L.length + Y.length := by
    rw [← hXY]; simp; omega
  have hg : ∀ j, j < L.length → M.getD (X.length + j) (0, 0) = L.getD j (0, 0) := by
    intro j hj
    rw [← hXY, getD_append_left (by rw [List.length_append]; omega),
      getD_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  intro i hi hd
  have e0 := hg i (by omega)
  have e1 := hg (i + 1) (by omega)
  have key := hM (X.length + i) (by omega)
    (by rw [show X.length + i + 1 = X.length + (i + 1) by omega, e0, e1]; exact hd)
  rw [show X.length + i + 1 = X.length + (i + 1) by omega, e0, e1] at key
  exact key

/-- `d = bd` のときの親の段の制限。引数ブロックへ降りるときだけ意味を持つ。 -/
def dpOK (bd d plev : ℕ) (first : Bool) : Prop :=
  first = true → d = bd → (plev = 0 ∨ plev + 1 < bd)

theorem dpOK_false {bd d plev : ℕ} : dpOK bd d plev false := by
  intro h; exact absurd h (by simp)

/-- 引数ブロックへ降りるとき `dpOK` は保たれる。 -/
theorem dpOK_arg {p : ℕ × ℕ} {bd d plev : ℕ} {first force : Bool}
    (hp1 : p.1 = bd) (hbd : bd ≤ d) (hcol : p.2 ≤ p.1) :
    dpOK (bd + 1) (ddOf p.2 d plev first force + 1) p.2 true := by
  intro _ he
  have hle := le_ddOf p.2 d plev first force
  have hdd : ddOf p.2 d plev first force = bd := by omega
  have hdbd : d = bd := by omega
  unfold ddOf at hdd
  by_cases hlad : ladOf p.2 d plev first force = true
  · rw [if_pos hlad] at hdd; omega
  · rw [if_neg hlad] at hdd
    by_cases hs : 0 < p.2 ∧ d ≤ p.2
    · rw [if_pos hs] at hdd; omega
    · rcases Nat.eq_zero_or_pos p.2 with h0 | h0
      · exact Or.inl h0
      · right
        have hnd : ¬ (d ≤ p.2) := fun hh => hs ⟨h0, hh⟩
        omega

/-- `contrLen` から「前置きの次の列の段が下がる」条件だけ外した版。 -/
def contrLen' (p : ℕ × ℕ) (B : PairSeq) (k : ℕ) (A : PairSeq) : Option (PairSeq × PairSeq) :=
  match B.drop k with
  | [] => none
  | q :: r2 =>
      let Aq := r2.takeWhile fun x => q.1 < x.1
      let Bq := r2.dropWhile fun x => q.1 < x.1
      let pre := contrPre p (B.take k) A
      let rest2 := Aq.drop pre.length
      if q.2 + 1 = p.2 ∧ q.1 = p.1 ∧ Aq.take pre.length = pre ∧
          rest2 ≠ [] ∧ (rest2.headI).1 = p.1 + 1 then
        some (rest2, Bq)
      else none

/-- **縮約の前置きが揃えば縮約は必ず発火する**（段が下がる条件は自動）。
梯子が立つのは頭の段が親の段 + 1 のときだけなので、その場合だけ課す。 -/
def ctrHeadOK (B : PairSeq) (plev : ℕ) : Prop :=
  ∀ p r, B = p :: r → p.2 = plev + 1 →
    contrLen' p (r.dropWhile fun x => p.1 < x.1)
        (unitsLen p (r.dropWhile fun x => p.1 < x.1)) (r.takeWhile fun x => p.1 < x.1)
      = contrLen p (r.dropWhile fun x => p.1 < x.1)
        (unitsLen p (r.dropWhile fun x => p.1 < x.1)) (r.takeWhile fun x => p.1 < x.1)

/-- どの節点でも、その引数ブロックについて `ctrHeadOK` が成り立つ。 -/
def argCtrOK : PairSeq → Prop
  | [] => True
  | p :: r =>
      ctrHeadOK (r.takeWhile fun q => p.1 < q.1) p.2 ∧
      argCtrOK (r.takeWhile fun q => p.1 < q.1) ∧
      argCtrOK (r.dropWhile fun q => p.1 < q.1)
  termination_by M => M.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ r)

theorem argCtrOK_nil : argCtrOK [] := by rw [argCtrOK]; trivial

theorem argCtrOK_cons {p : ℕ × ℕ} {r : PairSeq} :
    argCtrOK (p :: r) ↔
      ctrHeadOK (r.takeWhile fun q => p.1 < q.1) p.2 ∧
      argCtrOK (r.takeWhile fun q => p.1 < q.1) ∧
      argCtrOK (r.dropWhile fun q => p.1 < q.1) := by
  rw [argCtrOK]

/-- ブロックの頭についての `ctrHeadOK`（`first = false` なら自明）。 -/
def hcOK (B : PairSeq) (plev : ℕ) (first : Bool) : Prop :=
  first = true → ctrHeadOK B plev

theorem hcOK_false {B : PairSeq} {plev : ℕ} : hcOK B plev false := by
  intro h; exact absurd h (by simp)

/-- 根では `ctrHeadOK` は自明（頭が `(0,0)` なので段が `0 + 1` にならない）。 -/
theorem ctrHeadOK_root {M : PairSeq} (hb : blockok 0 M) (hcol : colOK M) :
    ctrHeadOK M 0 := by
  intro p r hM hp
  exfalso
  have h1 : p.1 = 0 := by
    have hh := hb.1 (by rw [hM]; simp)
    rw [hM] at hh; simpa using hh
  have h2 : p.2 ≤ p.1 := hcol p (by rw [hM]; simp)
  omega

/-- **`argCtrOK` は BMS 標準形の性質**（未証明。`ArgDomCore` から出るはず）。 -/
def CtrRes : Prop := ∀ {M : PairSeq}, ST_PS M → argCtrOK M



/-! ### 段 > 0 で残っている 3 つの場合

不変量を足したので、旧 `RDposRes`（偽）と違いどれも**実際に真**である
（`tools/dbms` の全数検査: ブロック ≤5 列・`bd ≤ 2`・`plev ≤ 3` で反例 0、
`RDlad2` 710 件 / `RDnopar` 77950 件 / `RDnode` 14827 件）。 -/

/-- **1. 梯子つきで兄弟へ降りる段で縮約が起こりうる**（contr regime）。 -/
def RDlad2 : Prop :=
  ∀ (p : ℕ × ℕ) (A T : PairSeq) (bd d plev : ℕ) (first force : Bool),
    blockok bd (p :: (A ++ T)) → colOK (p :: (A ++ T)) → descOK (p :: (A ++ T)) →
    bd ≤ d → p.1 = bd → 2 ≤ (p :: (A ++ T)).length →
    (∀ x ∈ A, p.1 < x.1) → (T = [] ∨ ¬ (p.1 < (T.headI).1)) →
    0 < entry (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) →
    argPatOK (p :: (A ++ T)) → argCtrOK (p :: (A ++ T)) → adjLev (p :: (A ++ T)) →
    hpOK (p :: (A ++ T)) d plev first force → fOK (p :: (A ++ T)) d plev force →
    dpOK bd d plev first → hcOK (p :: (A ++ T)) plev first →
    T ≠ [] →
    ladOf p.2 d plev first force = true →
    ¬ (∀ L : PairSeq, contrLen p L (unitsLen p L) A = none) →
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ T)) d plev first force)⟦m⟧
        = convC ((p :: (A ++ T))⟦n'⟧) d plev first force

/-- **2. 末尾列に行 1 の親がない**（弱めた `contrOK` が要る）。 -/
def RDnopar : Prop :=
  ∀ (p : ℕ × ℕ) (A T : PairSeq) (bd d plev : ℕ) (first force : Bool),
    blockok bd (p :: (A ++ T)) → colOK (p :: (A ++ T)) → descOK (p :: (A ++ T)) →
    bd ≤ d → p.1 = bd → 2 ≤ (p :: (A ++ T)).length →
    (∀ x ∈ A, p.1 < x.1) → (T = [] ∨ ¬ (p.1 < (T.headI).1)) →
    0 < entry (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) →
    argPatOK (p :: (A ++ T)) → argCtrOK (p :: (A ++ T)) → adjLev (p :: (A ++ T)) →
    hpOK (p :: (A ++ T)) d plev first force → fOK (p :: (A ++ T)) d plev force →
    dpOK bd d plev first → hcOK (p :: (A ++ T)) plev first →
    ¬ hasParent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) →
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ T)) d plev first force)⟦m⟧
        = convC ((p :: (A ++ T))⟦n'⟧) d plev first force

/-- **3. 末尾列の親が節点そのもの**（ずれたコピーの補題が要る。shift regime）。 -/
def RDnode : Prop :=
  ∀ (p : ℕ × ℕ) (A T : PairSeq) (bd d plev : ℕ) (first force : Bool),
    blockok bd (p :: (A ++ T)) → colOK (p :: (A ++ T)) → descOK (p :: (A ++ T)) →
    bd ≤ d → p.1 = bd → 2 ≤ (p :: (A ++ T)).length →
    (∀ x ∈ A, p.1 < x.1) → (T = [] ∨ ¬ (p.1 < (T.headI).1)) →
    0 < entry (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) →
    argPatOK (p :: (A ++ T)) → argCtrOK (p :: (A ++ T)) → adjLev (p :: (A ++ T)) →
    hpOK (p :: (A ++ T)) d plev first force → fOK (p :: (A ++ T)) d plev force →
    dpOK bd d plev first → hcOK (p :: (A ++ T)) plev first →
    (T = [] ∧ parent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) = 0) →
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ T)) d plev first force)⟦m⟧
        = convC ((p :: (A ++ T))⟦n'⟧) d plev first force

/-- **段が正の場合の組み立て**（ブロック版・不変量つき）。 -/
theorem reindexD_pos_block2 (Hl : RDlad2) (Hn : RDnopar) (Hd : RDnode) :
    ∀ (N : ℕ) (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → 2 ≤ B.length →
      0 < entry B 1 (B.length - 1) →
      argPatOK B → argCtrOK B → adjLev B →
      hpOK B d plev first force → fOK B d plev force →
      dpOK bd d plev first → hcOK B plev first →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force := by
  intro N
  induction N with
  | zero =>
    intro B hB bd d plev first force _ _ _ _ h2 _ _ _ _ _ _ _ _ n hn
    exact absurd hB (by omega)
  | succ N ih =>
    intro B hB bd d plev first force hb hc hd hbd h2 hlev hAP hAC hLB hHP hFC hDP hHC n hn
    cases B with
    | nil => exact absurd h2 (by simp)
    | cons p r =>
      have hp1 : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp1]⟩
      obtain ⟨A, T, hAd, hTd⟩ :
          ∃ A T, A = (r.takeWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) ∧
                 T = (r.dropWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) := ⟨_, _, rfl, rfl⟩
      have hrAT : r = A ++ T := by
        rw [hAd, hTd]; exact (List.takeWhile_append_dropWhile).symm
      subst hrAT
      have hAdeep : ∀ x ∈ A, ((bd, y) : ℕ × ℕ).1 < x.1 := by
        intro x hx
        rw [hAd] at hx
        simpa using List.mem_takeWhile_imp hx
      have hThd : T = [] ∨ ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
        rw [hTd]; exact dropWhile_head_not _ _
      obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := ((bd, y) : ℕ × ℕ).1)
        hAdeep hThd
      -- 新しい不変量を割る
      obtain ⟨hAPh, hAPa, hAPt⟩ := argPatOK_cons.1 hAP
      rw [e1] at hAPh hAPa
      rw [e2] at hAPt
      obtain ⟨hACh, hACa, hACt⟩ := argCtrOK_cons.1 hAC
      rw [e1] at hACh hACa
      rw [e2] at hACt
      have hLA : adjLev A := by
        have hx := adjLev_infix (takeWhile_infix_cons ((bd, y) : ℕ × ℕ) (A ++ T)) hLB
        rw [e1] at hx; exact hx
      have hLT : adjLev T := by
        have hx := adjLev_infix (dropWhile_infix_cons ((bd, y) : ℕ × ℕ) (A ++ T)) hLB
        rw [e2] at hx; exact hx
      have hycol : ((bd, y) : ℕ × ℕ).2 ≤ ((bd, y) : ℕ × ℕ).1 := hc _ (by simp)
      have hfA : fOK A (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
          ((bd, y) : ℕ × ℕ).2 (first && (((bd, y) : ℕ × ℕ).2 == plev)) := by
        intro hft
        have hf1 : first = true := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.1
        have hpl : ((bd, y) : ℕ × ℕ).2 = plev := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.2
        rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
        · left
          intro a s hs
          have hkey := hh ((bd, y) : ℕ × ℕ) (A ++ T) rfl hpl (by rw [e1, hs]; simp)
          rw [e1, hs] at hkey
          simpa using hkey
        · right
          subst hd0; subst hpl0; subst hfc0
          have hy0 : y = 0 := by simpa using hpl
          subst hy0
          simp [ddOf, ladOf]
      have hbA : blockok (bd + 1) A := by rw [← e1]; exact blockok_arg hb
      have hbT : blockok bd T := by rw [← e2]; exact blockok_tail hb
      have hcA : colOK A := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_left A T))) hc
      have hcT : colOK T := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_right A T))) hc
      obtain ⟨hdh, hdA, hdT⟩ := descOK_cons.1 hd
      rw [e1] at hdA
      rw [e2] at hdh hdT
      have hlAT : A.length + T.length ≤ N := by
        simp only [List.length_cons, List.length_append] at hB
        omega
      have hlen : ((bd, y) :: (A ++ T)).length = A.length + T.length + 1 := by simp
      have hi1 : idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1) = 1 := by
        rw [idx1, if_pos hlev]
      by_cases hpar : hasParent ((bd, y) :: (A ++ T)) 1
          (((bd, y) :: (A ++ T)).length - 1)
      · have hnr1 : nextrel1 ((bd, y) :: (A ++ T))
            (parent ((bd, y) :: (A ++ T)) 1 (((bd, y) :: (A ++ T)).length - 1))
            (((bd, y) :: (A ++ T)).length - 1) := by
          have h := parent_nextR hpar
          unfold nextR at h; rw [if_neg (by omega)] at h; exact h
        by_cases hTe : T = []
        · -- 兄弟が空: ブロックは p :: A
          subst hTe
          have hAne : A ≠ [] := by
            intro he
            rw [he] at h2
            simp at h2
          have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
          have hlastA : ((bd, y) :: (A ++ [])).getLastD (0, 0) = A.getLastD (0, 0) := by
            rw [List.append_nil]; exact getLastD_cons_ne _ hAne _
          have hlevA : 0 < entry A 1 (A.length - 1) := by
            rw [entry_last, ← hlastA, ← entry_last]; exact hlev
          have hiA : idx1 A (A.length - 1) = 1 := by rw [idx1, if_pos hlevA]
          have hzA : ¬ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0) := by
            rintro ⟨-, h1⟩
            omega
          have hidx : ((bd, y) :: (A ++ [])).length - 1
              = ([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1) := by
            simp only [List.length_cons, List.length_nil, List.append_nil]
            omega
          have hBeq : ((bd, y) :: (A ++ [])) = [((bd, y) : ℕ × ℕ)] ++ A := by simp
          by_cases hj00 : parent ((bd, y) :: (A ++ []))
              1 (((bd, y) :: (A ++ [])).length - 1) = 0
          · -- 場合 (d): 親が節点（ずれたコピーの補題が要る）
            exact Hd ((bd, y) : ℕ × ℕ) A [] bd d plev first force hb hc hd hbd rfl h2
              hAdeep (Or.inl rfl) hlev hAP hAC hLB hHP hFC hDP hHC ⟨rfl, hj00⟩ n hn
          · -- 場合 (c): 引数ブロックへ降りる
            have hlenA : ((bd, y) :: (A ++ [])).length - 1 = A.length := by simp
            have hA2 : 2 ≤ A.length := by
              have hj0lt := hnr1.2.2.1
              have hj0ne : parent ((bd, y) :: (A ++ [])) 1
                  (((bd, y) :: (A ++ [])).length - 1) ≠ 0 := hj00
              omega
            have hpB : hasParent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
              rw [hiA, ← hidx, ← hBeq]; exact hpar
            have hgeB : ([((bd, y) : ℕ × ℕ)] : PairSeq).length
                ≤ parent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                    (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
              rw [hiA, ← hidx, ← hBeq]
              show 1 ≤ parent ((bd, y) :: (A ++ [])) 1 (((bd, y) :: (A ++ [])).length - 1)
              omega
            by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
            · have hIH := ih A (by omega) (bd + 1) (d + 2) ((bd, y) : ℕ × ℕ).2 true false
                hbA hcA hdA (by omega) hA2 hlevA hAPa hACa hLA
                (hpOK_of_headPatOK hAPh) fOK_false
                (fun _ he => absurd he (by omega)) (fun _ => hACh)
              obtain ⟨m, n', k1, k2, k3⟩ := reindexD_arg_lad (p := ((bd, y) : ℕ × ℕ))
                hAdeep hlad hbA hcA hdA (by omega) hzA hpB hgeB hIH n hn
              exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
            · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                | false => rfl
                | true => exact absurd hx hlad
              have hIH := ih A (by omega) (bd + 1)
                (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
                ((bd, y) : ℕ × ℕ).2 true (first && (((bd, y) : ℕ × ℕ).2 == plev))
                hbA hcA hdA
                (by have := le_ddOf ((bd, y) : ℕ × ℕ).2 d plev first force; omega)
                hA2 hlevA hAPa hACa hLA (hpOK_of_headPatOK hAPh) hfA
                (dpOK_arg (p := ((bd, y) : ℕ × ℕ)) rfl hbd hycol) (fun _ => hACh)
              obtain ⟨m, n', k1, k2, k3⟩ := reindexD_arg_nolad (p := ((bd, y) : ℕ × ℕ))
                hAdeep hnl hbA hcA hdA (by omega) hzA hpB hgeB hIH n hn
              exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
        · -- 兄弟が空でない: 床の補題で親は兄弟の中
          have hTne : T ≠ [] := hTe
          have hT1 : 1 ≤ T.length := List.length_pos_of_ne_nil hTne
          have hTh : ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
            rcases hThd with h | h
            · exact absurd h hTne
            · exact h
          have hBeq : ((bd, y) :: (A ++ T)) = (((bd, y) : ℕ × ℕ) :: A) ++ T := by simp
          have hidx : ((bd, y) :: (A ++ T)).length - 1
              = (((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1) := by
            simp only [List.length_cons, List.length_append]
            omega
          have hlastT : ((bd, y) :: (A ++ T)).getLastD (0, 0) = T.getLastD (0, 0) := by
            rw [hBeq]; exact getLastD_append_right hTne _
          have hlevT : 0 < entry T 1 (T.length - 1) := by
            rw [entry_last, ← hlastT, ← entry_last]; exact hlev
          have hiT : idx1 T (T.length - 1) = 1 := by rw [idx1, if_pos hlevT]
          have hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0) := by
            rintro ⟨-, h1⟩
            omega
          -- 床の補題
          have hlowG : ∀ c ∈ (((bd, y) : ℕ × ℕ) :: A), bd ≤ c.1 := by
            intro c hcm
            refine hb.2.1 c ?_
            rw [hBeq]
            exact List.mem_append_left _ hcm
          have hhead : (T.headI).1 = bd := hbT.1 hTne
          have hle0 : le0 ((((bd, y) : ℕ × ℕ) :: A) ++ T)
              (parent ((bd, y) :: (A ++ T)) 1 (((bd, y) :: (A ++ T)).length - 1))
              (((bd, y) :: (A ++ T)).length - 1) := by
            rw [← hBeq]; exact hnr1.2.2.2.2.1
          have hgeT : (((bd, y) : ℕ × ℕ) :: A).length
              ≤ parent ((bd, y) :: (A ++ T)) 1 (((bd, y) :: (A ++ T)).length - 1) :=
            le0_ge_of_append hTne hlowG hhead hle0 (by rw [hidx]; omega)
          have hj0lt := hnr1.2.2.1
          have hT2 : 2 ≤ T.length := by
            simp only [List.length_cons, List.length_append] at hj0lt hgeT
            omega
          have hpB : hasParent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
              ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
            rw [hiT, ← hidx, ← hBeq]; exact hpar
          have hgeB : (((bd, y) : ℕ × ℕ) :: A).length
              ≤ parent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                  ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
            rw [hiT, ← hidx, ← hBeq]; exact hgeT
          have hIH := ih T (by omega) bd d ((bd, y) : ℕ × ℕ).2 false false
            hbT hcT hdT hbd hT2 hlevT hAPt hACt hLT hpOK_false fOK_false
            dpOK_false hcOK_false
          by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
          · by_cases hnc : ∀ L : PairSeq,
                contrLen ((bd, y) : ℕ × ℕ) L (unitsLen ((bd, y) : ℕ × ℕ) L) A = none
            · obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_lad (p := ((bd, y) : ℕ × ℕ))
                hAdeep hTh hlad hnc hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
              rw [← hBeq] at k3
              exact ⟨m, n', k1, k2, k3⟩
            · exact Hl ((bd, y) : ℕ × ℕ) A T bd d plev first force hb hc hd hbd rfl h2
                hAdeep hThd hlev hAP hAC hLB hHP hFC hDP hHC hTne hlad hnc n hn
          · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
              cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
              | false => rfl
              | true => exact absurd hx hlad
            obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_nolad (p := ((bd, y) : ℕ × ℕ))
              hAdeep hTh hnl hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
            rw [← hBeq] at k3
            exact ⟨m, n', k1, k2, k3⟩
      · -- 場合 (b): 親がない（弱めた contrOK が要る）
        exact Hn ((bd, y) : ℕ × ℕ) A T bd d plev first force hb hc hd hbd rfl h2
          hAdeep hThd hlev hAP hAC hLB hHP hFC hDP hHC hpar n hn


/-- 段が正の場合も 3 つの残余だけに絞られた（`argCtrOK` は `CtrRes` から）。 -/
theorem reindexD_pos_of2 (Hc : CtrRes) (Hl : RDlad2) (Hn : RDnopar) (Hd : RDnode) :
    ReindexD_pos := by
  intro A hA hL hlev n hn
  have h := reindexD_pos_block2 Hl Hn Hd A.length A (Nat.le_refl _) 0 0 0 true false
    (blockok_ST_PS hA) (colOK_ST_PS hA) (descOK_ST_PS hA) (Nat.le_refl 0)
    (by omega) hlev (argPatOK_ST_PS hA) (Hc hA) (adjLev_ST_PS hA)
    (fun _ => Or.inr ⟨rfl, rfl, rfl⟩) fOK_false (fun _ _ => Or.inl rfl)
    (fun _ => ctrHeadOK_root (blockok_ST_PS hA) (colOK_ST_PS hA)) n hn
  obtain ⟨m, n', h1, h2, h3⟩ := h
  exact ⟨m, n', h1, h2, by rw [conC, conC]; exact h3⟩

/-- 段 > 0 で残っている 3 つをまとめたもの。 -/
def RDposRes2 : Prop := RDlad2 ∧ RDnopar ∧ RDnode

/-- **到達点**: `ReindexD` は
  * `CtrRes`（BMS 標準形は `argCtrOK`）
  * `RDzeroRes2`（段 0 の梯子つきの段での縮約）
  * `RDposRes2`（段 > 0 の 3 つ）
だけに絞られた。旧 `RDposRes` は偽だったが、こちらは全数検査で反例 0。 -/
theorem reindexD_holds_of_res2 (Hc : CtrRes) (H0 : RDzeroRes2) (H1 : RDposRes2) :
    ReindexD := by
  intro A hA hL n hn
  by_cases hz : entry A 1 (A.length - 1) = 0
  · exact reindexD_zero2 H0 hA hz n hn
  · exact reindexD_pos_of2 Hc H1.1 H1.2.1 H1.2.2 hA hL (by omega) n hn

/-- 同じ形で主定理まで。 -/
theorem ST_D_conC_holds_of_res2 (Hc : CtrRes) (H0 : RDzeroRes2) (H1 : RDposRes2)
    {M : PairSeq} (hM : ST_PS M) : ST_D (conC M) :=
  ST_D_conC (reindexD_holds_of_res2 Hc H0 H1) hM



/-- 縮約の前置きは「節点 + 引数 + 兄弟ユニット」を丸ごと 1 段深くしたもの。
`ArgDomCore` から `CtrRes` を出すときの最初の一歩（`ArgDomCore` の結論
`sle B (shiftr0 e (A1 ++ (u+e,w) :: (B ++ A2)))` の `A1` が
ちょうど `p :: (A ++ U)` になる）。 -/
theorem contrPre_eq_shiftr0 (p : ℕ × ℕ) (U A : PairSeq) :
    contrPre p U A = shiftr0 1 (p :: (A ++ U)) := by
  unfold contrPre shift1 shiftr0
  simp [List.map_append]


/-! ## 4.15 縮約が発火する段の因子化（contr regime）

梯子が立つ段で縮約が発火するとき、兄弟ブロック `T` はかならず

    T = U ++ q :: ((pre ++ rest2) ++ L)

の形をしている（`U` は `p` のユニット列、`q` は段が 1 つ低い同じ深さの兄弟、
`pre = contrPre p U Arg`、`L` は `q` の兄弟ブロック）。
`L` をどう取り替えても縮約はまったく同じように発火するので、
像は `L` の手前で因子化できる。これで `reindexD_step_gen` に乗る。 -/

/-- 縮約が発火する形。 -/
theorem contrLen_of_shape {p q : ℕ × ℕ} {Arg U pre rest2 L : PairSeq}
    (hU : Units p U)
    (hq2 : q.2 + 1 = p.2) (hq1 : q.1 = p.1)
    (hpre : pre = contrPre p U Arg)
    (hpd : ∀ x ∈ pre, p.1 < x.1)
    (hrd : ∀ x ∈ rest2, p.1 < x.1)
    (hrne : rest2 ≠ []) (hrh1 : (rest2.headI).1 = p.1 + 1) (hrh2 : (rest2.headI).2 < p.2)
    (hL : L = [] ∨ ¬ (p.1 < (L.headI).1)) :
    contrLen p (U ++ q :: ((pre ++ rest2) ++ L))
        (unitsLen p (U ++ q :: ((pre ++ rest2) ++ L))) Arg = some (rest2, L) := by
  have hqp : ¬ (q = p) := by
    intro h; rw [h] at hq2; omega
  have hk : unitsLen p (U ++ q :: ((pre ++ rest2) ++ L)) = U.length :=
    unitsLen_append_units hU (Or.inr ⟨by simp only [List.headI]; omega,
      by simp only [List.headI]; exact hqp⟩)
  have hdrop : (U ++ q :: ((pre ++ rest2) ++ L)).drop U.length
      = q :: ((pre ++ rest2) ++ L) := by simp
  have htake : (U ++ q :: ((pre ++ rest2) ++ L)).take U.length = U := by simp
  have hall : ∀ x ∈ (pre ++ rest2), q.1 < x.1 := by
    intro x hx
    rw [hq1]
    rcases List.mem_append.1 hx with h | h
    · exact hpd x h
    · exact hrd x h
  have hLh : L = [] ∨ ¬ (q.1 < (L.headI).1) := by rw [hq1]; exact hL
  obtain ⟨e1, e2⟩ := split_append (dd := q.1) hall hLh
  rw [contrLen, hk, hdrop]
  simp only [htake, e1, e2, ← hpre]
  rw [if_pos ⟨hq2, hq1, by simp, by simpa using hrne, by simpa using hrh1,
    by simpa using hrh2⟩]
  simp

/-- **縮約が発火する段の因子化**。 -/
theorem convC_factor_contr {p q : ℕ × ℕ} {Arg U pre rest2 L : PairSeq} {d plev : ℕ}
    {first force : Bool}
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hU : Units p U)
    (hq2 : q.2 + 1 = p.2) (hq1 : q.1 = p.1)
    (hpre : pre = contrPre p U Arg)
    (hpd : ∀ x ∈ pre, p.1 < x.1)
    (hrd : ∀ x ∈ rest2, p.1 < x.1)
    (hrne : rest2 ≠ []) (hrh1 : (rest2.headI).1 = p.1 + 1) (hrh2 : (rest2.headI).2 < p.2)
    (hL : L = [] ∨ ¬ (p.1 < (L.headI).1))
    (hlad : ladOf p.2 d plev first force = true) :
    convC (p :: (Arg ++ (U ++ q :: ((pre ++ rest2) ++ L)))) d plev first force
      = ((d, plev) :: (d + 1, p.2) :: (convC Arg (d + 2) p.2 true false
          ++ convC U (d + 1) p.2 false false
          ++ convC rest2 (d + 1) p.2 false false))
        ++ convC L d p.2 false false := by
  have hTh : (U ++ q :: ((pre ++ rest2) ++ L)) = [] ∨
      ¬ (p.1 < ((U ++ q :: ((pre ++ rest2) ++ L)).headI).1) := by
    right
    by_cases hUe : U = []
    · rw [hUe]; simp only [List.nil_append, List.headI]; omega
    · rw [headI_append_left hUe]
      rcases hU.head_eq with h | h
      · exact absurd h hUe
      · rw [h]; omega
  obtain ⟨e1, e2⟩ := split_append (dd := p.1) hArg hTh
  have hcc := contrLen_of_shape (Arg := Arg) hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 hL
  have hk : unitsLen p (U ++ q :: ((pre ++ rest2) ++ L)) = U.length :=
    unitsLen_append_units hU (Or.inr ⟨by simp only [List.headI]; omega,
      by simp only [List.headI]; intro h; rw [h] at hq2; omega⟩)
  have htake : (U ++ q :: ((pre ++ rest2) ++ L)).take U.length = U := by simp
  rw [convC_cons_lad_some p (Arg ++ (U ++ q :: ((pre ++ rest2) ++ L))) d plev first force hlad
    (by rw [e1, e2]; exact hcc), e1, e2, hk, htake]
  simp [List.append_assoc]

/-- **縮約が発火する段で `q` の兄弟ブロックへ降りる**（`Bq ≠ []` の場合）。 -/
theorem reindexD_sib_contr {p q : ℕ × ℕ} {Arg U pre rest2 T : PairSeq} {d plev : ℕ}
    {first force : Bool}
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hU : Units p U) (hq2 : q.2 + 1 = p.2) (hq1 : q.1 = p.1)
    (hpre : pre = contrPre p U Arg)
    (hpd : ∀ x ∈ pre, p.1 < x.1) (hrd : ∀ x ∈ rest2, p.1 < x.1)
    (hrne : rest2 ≠ []) (hrh1 : (rest2.headI).1 = p.1 + 1) (hrh2 : (rest2.headI).2 < p.2)
    (hTh : ¬ (p.1 < (T.headI).1))
    (hlad : ladOf p.2 d plev first force = true)
    (hb : blockok p.1 T) (hcT : colOK T) (hdT : descOK T) (hbd : p.1 ≤ d)
    (hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0))
    (hpB : hasParent ((p :: (Arg ++ (U ++ q :: (pre ++ rest2)))) ++ T)
             (idx1 T (T.length - 1))
             ((p :: (Arg ++ (U ++ q :: (pre ++ rest2)))).length + (T.length - 1)))
    (hgeB : (p :: (Arg ++ (U ++ q :: (pre ++ rest2)))).length
             ≤ parent ((p :: (Arg ++ (U ++ q :: (pre ++ rest2)))) ++ T)
                 (idx1 T (T.length - 1))
                 ((p :: (Arg ++ (U ++ q :: (pre ++ rest2)))).length + (T.length - 1)))
    (IH : ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
            (convC T d p.2 false false)⟦m⟧ = convC (T⟦n'⟧) d p.2 false false) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC ((p :: (Arg ++ (U ++ q :: (pre ++ rest2)))) ++ T) d plev first force)⟦m⟧
        = convC (((p :: (Arg ++ (U ++ q :: (pre ++ rest2)))) ++ T)⟦n'⟧) d plev first force :=
  reindexD_step_gen (G := p :: (Arg ++ (U ++ q :: (pre ++ rest2)))) (T := T)
    (C := (d, plev) :: (d + 1, p.2) :: (convC Arg (d + 2) p.2 true false
            ++ convC U (d + 1) p.2 false false
            ++ convC rest2 (d + 1) p.2 false false))
    (d' := d) (plev' := p.2) (first' := false) (force' := false)
    (P := fun L => ¬ (p.1 < (L.headI).1))
    (fun L hL => by
      have hshape : (p :: (Arg ++ (U ++ q :: (pre ++ rest2)))) ++ L
          = p :: (Arg ++ (U ++ q :: ((pre ++ rest2) ++ L))) := by
        simp [List.append_assoc]
      rw [hshape]
      exact convC_factor_contr hArg hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 (Or.inr hL) hlad)
    hTh (fun hL n hn => by
      show ¬ (p.1 < ((T⟦n⟧).headI).1)
      rw [oper_headI hL hn]; exact hTh)
    hb hcT hdT hbd hzT hpB hgeB IH

/-- **縮約が発火する段で `rest2` へ降りる**（`Bq = []` の場合）。 -/
theorem reindexD_rest_contr {p q : ℕ × ℕ} {Arg U pre T : PairSeq} {d plev : ℕ}
    {first force : Bool}
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hU : Units p U) (hq2 : q.2 + 1 = p.2) (hq1 : q.1 = p.1)
    (hpre : pre = contrPre p U Arg)
    (hpd : ∀ x ∈ pre, p.1 < x.1) (hrd : ∀ x ∈ T, p.1 < x.1)
    (hrne : T ≠ []) (hrh1 : (T.headI).1 = p.1 + 1) (hrh2 : (T.headI).2 < p.2)
    (hlad : ladOf p.2 d plev first force = true)
    (hb : blockok (p.1 + 1) T) (hcT : colOK T) (hdT : descOK T) (hbd : p.1 + 1 ≤ d + 1)
    (hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0))
    (hpB : hasParent ((p :: (Arg ++ (U ++ q :: pre))) ++ T)
             (idx1 T (T.length - 1))
             ((p :: (Arg ++ (U ++ q :: pre))).length + (T.length - 1)))
    (hgeB : (p :: (Arg ++ (U ++ q :: pre))).length
             ≤ parent ((p :: (Arg ++ (U ++ q :: pre))) ++ T)
                 (idx1 T (T.length - 1))
                 ((p :: (Arg ++ (U ++ q :: pre))).length + (T.length - 1)))
    (IH : ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
            (convC T (d + 1) p.2 false false)⟦m⟧ = convC (T⟦n'⟧) (d + 1) p.2 false false) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC ((p :: (Arg ++ (U ++ q :: pre))) ++ T) d plev first force)⟦m⟧
        = convC (((p :: (Arg ++ (U ++ q :: pre))) ++ T)⟦n'⟧) d plev first force :=
  reindexD_step_gen (G := p :: (Arg ++ (U ++ q :: pre))) (T := T)
    (C := (d, plev) :: (d + 1, p.2) :: (convC Arg (d + 2) p.2 true false
            ++ convC U (d + 1) p.2 false false))
    (d' := d + 1) (plev' := p.2) (first' := false) (force' := false)
    (P := fun L => (∀ x ∈ L, p.1 < x.1) ∧ L ≠ [] ∧
            (L.headI).1 = p.1 + 1 ∧ (L.headI).2 < p.2)
    (fun L hL => by
      have h := convC_factor_contr (rest2 := L) (L := ([] : PairSeq)) hArg hU hq2 hq1 hpre hpd
        hL.1 hL.2.1 hL.2.2.1 hL.2.2.2 (Or.inl rfl) hlad
      have hshape : (p :: (Arg ++ (U ++ q :: pre))) ++ L
          = p :: (Arg ++ (U ++ q :: ((pre ++ L) ++ ([] : PairSeq)))) := by
        simp [List.append_assoc]
      rw [hshape, h]
      simp [List.append_assoc])
    ⟨hrd, hrne, hrh1, hrh2⟩
    (fun hL n hn => by
      refine ⟨oper_depth_gt hrd n, ?_, ?_, ?_⟩
      · obtain ⟨R, hR, -⟩ := oper_eq_dropLast_append hL hn
        intro he
        rw [hR] at he
        have : T.dropLast = [] := (List.append_eq_nil_iff.1 he).1
        have hlen : T.dropLast.length = T.length - 1 := List.length_dropLast
        rw [this] at hlen
        simp only [List.length_nil] at hlen
        omega
      · rw [oper_headI hL hn]; exact hrh1
      · rw [oper_headI hL hn]; exact hrh2)
    hb hcT hdT hbd hzT hpB hgeB IH

/-- **梯子つきで兄弟へ（縮約が `T` でも `T⟦n⟧` でも起きない場合）。**
旧 `reindexD_sib_lad` は「どんな `L` でも縮約が起きない」を要求したが、
因子化に実際に要るのは `T` と `T⟦n⟧` の 2 つだけである。 -/
theorem reindexD_sib_lad2 {p : ℕ × ℕ} {Arg T : PairSeq} {d plev : ℕ} {first force : Bool}
    (hArg : ∀ x ∈ Arg, p.1 < x.1)
    (hTh : ¬ (p.1 < (T.headI).1))
    (hlad : ladOf p.2 d plev first force = true)
    (hncT : contrLen p T (unitsLen p T) Arg = none)
    (hncE : ∀ n : ℕ, 1 ≤ n → contrLen p (T⟦n⟧) (unitsLen p (T⟦n⟧)) Arg = none)
    (hb : blockok p.1 T) (hcT : colOK T) (hdT : descOK T) (hbd : p.1 ≤ d)
    (hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0))
    (hpB : hasParent ((p :: Arg) ++ T) (idx1 T (T.length - 1))
             ((p :: Arg).length + (T.length - 1)))
    (hgeB : (p :: Arg).length ≤ parent ((p :: Arg) ++ T) (idx1 T (T.length - 1))
             ((p :: Arg).length + (T.length - 1)))
    (IH : ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
            (convC T d p.2 false false)⟦m⟧ = convC (T⟦n'⟧) d p.2 false false) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC ((p :: Arg) ++ T) d plev first force)⟦m⟧
        = convC (((p :: Arg) ++ T)⟦n'⟧) d plev first force :=
  reindexD_step_gen (G := p :: Arg) (T := T)
    (C := (d, plev) :: (d + 1, p.2) :: convC Arg (d + 2) p.2 true false)
    (d' := d) (plev' := p.2) (first' := false) (force' := false)
    (P := fun L => ¬ (p.1 < (L.headI).1) ∧ contrLen p L (unitsLen p L) Arg = none)
    (fun L hL => by
      rw [List.cons_append]
      exact convC_factor_sib_lad p Arg L d plev first force hArg (Or.inr hL.1) hlad hL.2)
    ⟨hTh, hncT⟩
    (fun hL n hn => ⟨by
      show ¬ (p.1 < ((T⟦n⟧).headI).1)
      rw [oper_headI hL hn]; exact hTh, hncE n hn⟩)
    hb hcT hdT hbd hzT hpB hgeB IH

/-- 深さで切れる前置きを剥がしても `argPatOK` は残る（`descOK_units` の類似）。 -/
theorem argPatOK_drop (a : ℕ) (L : PairSeq) (hL : L = [] ∨ ¬ (a < (L.headI).1)) :
    ∀ (n : ℕ) (V : PairSeq), V.length ≤ n → (∀ c ∈ V, a ≤ c.1) → (V = [] ∨ (V.headI).1 ≤ a) →
    argPatOK (V ++ L) → argPatOK L := by
  intro n
  induction n with
  | zero =>
      intro V hV _ _ h
      have : V = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simpa using h
  | succ n ih =>
      intro V hV hall hhd h
      match V with
      | [] => simpa using h
      | p :: rest =>
          have hp : p.1 = a := by
            have h1 : a ≤ p.1 := hall p (by simp)
            have h2 : p.1 ≤ a := by
              rcases hhd with hh | hh
              · exact absurd hh (by simp)
              · simpa using hh
            omega
          have hrest : ∀ c ∈ rest, a ≤ c.1 := fun c hc => hall c (by simp [hc])
          obtain ⟨e1, e2⟩ := split_append_gen (dd := p.1) (Y := L) (by rw [hp]; exact hL) rest
          have hlen : (rest.dropWhile fun q => p.1 < q.1).length ≤ n := by
            have := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) rest
            simp only [List.length_cons] at hV
            omega
          have hall' : ∀ c ∈ (rest.dropWhile fun q => p.1 < q.1), a ≤ c.1 :=
            fun c hc => hrest c ((List.dropWhile_sublist _).subset hc)
          have hhd' : (rest.dropWhile fun q => p.1 < q.1) = [] ∨
              ((rest.dropWhile fun q => p.1 < q.1).headI).1 ≤ a := by
            rcases dropWhile_head_neg (a := p.1) rest with hh | hh
            · exact Or.inl hh
            · exact Or.inr (by omega)
          rw [List.cons_append] at h
          have h2 := (argPatOK_cons.1 h).2.2
          rw [e2] at h2
          exact ih _ hlen hall' hhd' h2

/-- ユニット列の要素は深さが `p.1` 以上（`Units.ge` の言い換え）。 -/
theorem Units.head_le {p : ℕ × ℕ} {U : PairSeq} (h : Units p U) :
    U = [] ∨ (U.headI).1 ≤ p.1 := by
  rcases h.head_eq with he | he
  · exact Or.inl he
  · exact Or.inr (by rw [he])

/-- 縮約が発火したときの兄弟ブロックの形。 -/
theorem contrLen_shape {p : ℕ × ℕ} {T Arg rest2 Bq : PairSeq}
    (h : contrLen p T (unitsLen p T) Arg = some (rest2, Bq)) :
    ∃ (q : ℕ × ℕ) (U pre : PairSeq), Units p U ∧ T = U ++ q :: ((pre ++ rest2) ++ Bq) ∧
      q.2 + 1 = p.2 ∧ q.1 = p.1 ∧ pre = contrPre p U Arg ∧
      (∀ x ∈ pre, p.1 < x.1) ∧ (∀ x ∈ rest2, p.1 < x.1) ∧
      (Bq = [] ∨ ¬ (p.1 < (Bq.headI).1)) ∧
      rest2 ≠ [] ∧ (rest2.headI).1 = p.1 + 1 ∧ (rest2.headI).2 < p.2 := by
  obtain ⟨q, r2, hdr, hq2, hq1, hAq, hBq, hrne, hrh1, hrh2⟩ := contrLen_spec h
  refine ⟨q, T.take (unitsLen p T), contrPre p (T.take (unitsLen p T)) Arg,
    units_take p T.length T (Nat.le_refl _), ?_, hq2, hq1, rfl, ?_, ?_, ?_, hrne, hrh1, hrh2⟩
  · conv_lhs => rw [← List.take_append_drop (unitsLen p T) T]
    rw [hdr]
    rw [← hAq, ← hBq, List.takeWhile_append_dropWhile]
  · intro x hx
    have hm : x ∈ (r2.takeWhile fun x => q.1 < x.1) := by
      rw [hAq]; exact List.mem_append_left _ hx
    have h2 := List.mem_takeWhile_imp hm
    simp only [decide_eq_true_eq] at h2
    omega
  · intro x hx
    have hm : x ∈ (r2.takeWhile fun x => q.1 < x.1) := by
      rw [hAq]; exact List.mem_append_right _ hx
    have h2 := List.mem_takeWhile_imp hm
    simp only [decide_eq_true_eq] at h2
    omega
  · rw [← hBq, ← hq1]
    exact dropWhile_head_not _ _

/-- 空でない列の先頭は元の列に属する。 -/
theorem headI_mem {l : PairSeq} (h : l ≠ []) : l.headI ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => simp

/-- **縮約が発火して、しかも末尾列の親が縮約の内側にある場合**（コピー regime）。
`Bq = []`（`q` に兄弟がない）で、末尾列の親が `p :: (A ++ (U ++ q :: pre))` より
前にあるとき。実測では標準形 ≤9 列の右端の道でこれが 67 節点。 -/
def RDzeroStop : Prop :=
  ∀ (p q : ℕ × ℕ) (A U pre rest2 : PairSeq) (bd d plev : ℕ) (first force : Bool),
    blockok bd (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    colOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    descOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    bd ≤ d → p.1 = bd → (∀ x ∈ A, p.1 < x.1) →
    Units p U → q.2 + 1 = p.2 → q.1 = p.1 → pre = contrPre p U A →
    (∀ x ∈ pre, p.1 < x.1) → (∀ x ∈ rest2, p.1 < x.1) →
    rest2 ≠ [] → (rest2.headI).1 = p.1 + 1 → (rest2.headI).2 < p.2 →
    entry (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 1
      ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1) = 0 →
    argPatOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    ladOf p.2 d plev first force = true →
    ¬ ((p :: (A ++ (U ++ q :: pre))).length
        ≤ parent (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 0
            ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1)) →
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ (U ++ q :: (pre ++ rest2)))) d plev first force)⟦m⟧
        = convC ((p :: (A ++ (U ++ q :: (pre ++ rest2))))⟦n'⟧) d plev first force

/-- **縮約が発火する段（段 0）**。`Bq ≠ []` なら `q` の兄弟へ、`Bq = []` なら
`rest2` へ降りる。降りられないのは「親が縮約の内側」のときだけ（`RDzeroStop`）。 -/
theorem reindexD_zero_fire (Hs : RDzeroStop) (N : ℕ)
    (ih : ∀ (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → (bd = 0 → d = 0) →
      entry B 1 (B.length - 1) = 0 →
      argPatOK B → hpOK B d plev first force → fOK B d plev force →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force)
    {p q : ℕ × ℕ} {A T U pre rest2 Bq : PairSeq} {bd d plev : ℕ} {first force : Bool}
    (hlenN : (p :: (A ++ T)).length ≤ N + 1)
    (hb : blockok bd (p :: (A ++ T))) (hc : colOK (p :: (A ++ T)))
    (hd : descOK (p :: (A ++ T))) (hbd : bd ≤ d) (hz0 : bd = 0 → d = 0)
    (hp1 : p.1 = bd)
    (hlev : entry (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) = 0)
    (hAP : argPatOK (p :: (A ++ T)))
    (hAdeep : ∀ x ∈ A, p.1 < x.1)
    (hlad : ladOf p.2 d plev first force = true)
    (hpar : hasParent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1))
    (hU : Units p U) (hTeq : T = U ++ q :: ((pre ++ rest2) ++ Bq))
    (hq2 : q.2 + 1 = p.2) (hq1 : q.1 = p.1) (hpre : pre = contrPre p U A)
    (hpd : ∀ x ∈ pre, p.1 < x.1) (hrd : ∀ x ∈ rest2, p.1 < x.1)
    (hBqh : Bq = [] ∨ ¬ (p.1 < (Bq.headI).1))
    (hrne : rest2 ≠ []) (hrh1 : (rest2.headI).1 = p.1 + 1) (hrh2 : (rest2.headI).2 < p.2) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ T)) d plev first force)⟦m⟧
        = convC ((p :: (A ++ T))⟦n'⟧) d plev first force := by
  intro n hn
  -- 共通の下ごしらえ
  have hnrp : nextrel0 (p :: (A ++ T))
      (parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1))
      ((p :: (A ++ T)).length - 1) := by
    have h := parent_nextR hpar
    unfold nextR at h; rw [if_pos rfl] at h; exact h
  have hj0ge : bd ≤ entry (p :: (A ++ T)) 0
      (parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1)) := by
    have hj := hnrp.1
    have hmem : (p :: (A ++ T)).getD
        (parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1)) (0, 0) ∈ (p :: (A ++ T)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      simpa using List.getElem_mem hj
    rw [entry, if_pos rfl]
    exact hb.2.1 _ hmem
  have hlpgt : bd < ((p :: (A ++ T)).getLastD (0, 0)).1 := by
    have h1 := hnrp.2.2.2.1
    rw [entry_last0] at h1
    omega
  have hlplev : ((p :: (A ++ T)).getLastD (0, 0)).2 = 0 := by
    rw [← entry_last]; exact hlev
  have hTdeep : ∀ x ∈ (pre ++ rest2), p.1 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hpd x h
    · exact hrd x h
  have hpreh : (pre.headI).1 = p.1 + 1 := by rw [hpre]; simp [contrPre, shift1]
  have hThd : T = [] ∨ ¬ (p.1 < (T.headI).1) := by
    right
    rw [hTeq]
    by_cases hUe : U = []
    · rw [hUe]; simp only [List.nil_append, List.headI]; omega
    · rw [headI_append_left hUe]
      rcases hU.head_eq with h | h
      · exact absurd h hUe
      · rw [h]; omega
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := p.1) hAdeep hThd
  have hdT : descOK T := by
    have hx := (descOK_cons.1 hd).2.2
    rw [e2] at hx; exact hx
  have hAPt : argPatOK T := by
    have hx := (argPatOK_cons.1 hAP).2.2
    rw [e2] at hx; exact hx
  have hqL : (q :: ((pre ++ rest2) ++ Bq)) = []
      ∨ ¬ (p.1 < ((q :: ((pre ++ rest2) ++ Bq)).headI).1) := by
    right; simp only [List.headI]; omega
  have hdQ : descOK (q :: ((pre ++ rest2) ++ Bq)) :=
    descOK_units p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hdT)
  have hAPq : argPatOK (q :: ((pre ++ rest2) ++ Bq)) :=
    argPatOK_drop p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hAPt)
  obtain ⟨f1, f2⟩ := split_append (X := (pre ++ rest2)) (Y := Bq) (dd := q.1)
    (by rw [hq1]; exact hTdeep) (by rw [hq1]; exact hBqh)
  have hdBq : descOK Bq := by
    have hx := (descOK_cons.1 hdQ).2.2
    rw [f2] at hx; exact hx
  have hAPBq : argPatOK Bq := by
    have hx := (argPatOK_cons.1 hAPq).2.2
    rw [f2] at hx; exact hx
  have hdPR : descOK (pre ++ rest2) := by
    have hx := (descOK_cons.1 hdQ).2.1
    rw [f1] at hx; exact hx
  have hAPPR : argPatOK (pre ++ rest2) := by
    have hx := (argPatOK_cons.1 hAPq).2.1
    rw [f1] at hx; exact hx
  have hrestL : rest2 = [] ∨ ¬ (p.1 + 1 < (rest2.headI).1) := Or.inr (by rw [hrh1]; omega)
  have hpreall : ∀ c ∈ pre, p.1 + 1 ≤ c.1 := fun c hcc => by have := hpd c hcc; omega
  have hpreh' : pre = [] ∨ (pre.headI).1 ≤ p.1 + 1 := Or.inr (by rw [hpreh])
  have hdR : descOK rest2 :=
    descOK_units (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hdPR
  have hAPR : argPatOK rest2 :=
    argPatOK_drop (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hAPPR
  have hmemBq : ∀ c ∈ Bq, c ∈ (p :: (A ++ T)) := by
    intro c hcc
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    rw [hTeq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hcc))
  have hmemR : ∀ c ∈ rest2, c ∈ (p :: (A ++ T)) := by
    intro c hcc
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    rw [hTeq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_right _ hcc)))
  have hcBq : colOK Bq := fun cc hcc => hc cc (hmemBq cc hcc)
  have hcR : colOK rest2 := fun cc hcc => hc cc (hmemR cc hcc)
  by_cases hBqe : Bq = []
  · -- `Bq = []`: `rest2` へ降りるか、残余
    obtain ⟨G2, hG2⟩ : ∃ G2 : PairSeq, G2 = p :: (A ++ (U ++ q :: pre)) := ⟨_, rfl⟩
    have hBeq2 : (p :: (A ++ T)) = G2 ++ rest2 := by
      rw [hG2, hTeq, hBqe]; simp [List.append_assoc]
    have hBeq3 : (p :: (A ++ T)) = p :: (A ++ (U ++ q :: (pre ++ rest2))) := by
      rw [hTeq, hBqe]; simp [List.append_assoc]
    have hG2len : 1 ≤ G2.length := by rw [hG2]; simp
    have hlenB2 : (p :: (A ++ T)).length = G2.length + rest2.length := by
      rw [hBeq2]; simp
    have hlast : (p :: (A ++ T)).getLastD (0, 0) = rest2.getLastD (0, 0) := by
      rw [hBeq2]; exact getLastD_append_right hrne _
    have hlevR : entry rest2 1 (rest2.length - 1) = 0 := by
      rw [entry_last, ← hlast]; exact hlplev
    have hzR : ¬ (entry rest2 0 (rest2.length - 1) = 0 ∧ entry rest2 1 (rest2.length - 1) = 0) := by
      rintro ⟨h1, -⟩
      rw [entry_last0, ← hlast] at h1
      omega
    have hbR : blockok (p.1 + 1) rest2 := by
      refine ⟨fun _ => hrh1, fun cc hcc => by have := hrd cc hcc; omega, ?_⟩
      exact (steps1_append.1 (by rw [← hBeq2]; exact hb.2.2)).2.1
    by_cases hge2 : G2.length ≤ parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1)
    · have hiR : idx1 rest2 (rest2.length - 1) = 0 := by
        rw [idx1, if_neg (by rw [hlevR]; omega)]
      have hR1 : 1 ≤ rest2.length := List.length_pos_of_ne_nil hrne
      have hidx : (p :: (A ++ T)).length - 1 = G2.length + (rest2.length - 1) := by omega
      have hpB : hasParent (G2 ++ rest2) (idx1 rest2 (rest2.length - 1))
          (G2.length + (rest2.length - 1)) := by
        rw [hiR, ← hidx, ← hBeq2]; exact hpar
      have hgeB : G2.length ≤ parent (G2 ++ rest2) (idx1 rest2 (rest2.length - 1))
          (G2.length + (rest2.length - 1)) := by
        rw [hiR, ← hidx, ← hBeq2]; exact hge2
      rw [hG2] at hpB hgeB
      have hIH := ih rest2 (by omega) (p.1 + 1) (d + 1) p.2 false false hbR hcR hdR
        (by omega) (by omega) hlevR hAPR hpOK_false fOK_false
      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_rest_contr (Arg := A) (T := rest2)
        hAdeep hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 hlad hbR hcR hdR (by omega) hzR
        hpB hgeB hIH n hn
      refine ⟨m, n', k1, k2, ?_⟩
      rw [← hG2, ← hBeq2] at k3
      exact k3
    · rw [hBeq3]
      refine Hs p q A U pre rest2 bd d plev first force ?_ ?_ ?_ hbd hp1 hAdeep hU hq2 hq1
        hpre hpd hrd hrne hrh1 hrh2 ?_ ?_ hlad ?_ n hn
      · rw [← hBeq3]; exact hb
      · rw [← hBeq3]; exact hc
      · rw [← hBeq3]; exact hd
      · rw [← hBeq3]; exact hlev
      · rw [← hBeq3]; exact hAP
      · rw [← hBeq3, ← hG2]; exact hge2
  · -- `Bq ≠ []`: `q` の兄弟へ降りる
    have hBqh' : ¬ (p.1 < (Bq.headI).1) := by
      rcases hBqh with h | h
      · exact absurd h hBqe
      · exact h
    obtain ⟨G1, hG1⟩ : ∃ G1 : PairSeq, G1 = p :: (A ++ (U ++ q :: (pre ++ rest2))) := ⟨_, rfl⟩
    have hBeq1 : (p :: (A ++ T)) = G1 ++ Bq := by
      rw [hG1, hTeq]; simp [List.append_assoc]
    have hG1len : 1 ≤ G1.length := by rw [hG1]; simp
    have hBq1 : 1 ≤ Bq.length := List.length_pos_of_ne_nil hBqe
    have hlenB1 : (p :: (A ++ T)).length = G1.length + Bq.length := by
      rw [hBeq1]; simp
    have hlast : (p :: (A ++ T)).getLastD (0, 0) = Bq.getLastD (0, 0) := by
      rw [hBeq1]; exact getLastD_append_right hBqe _
    have hlevBq : entry Bq 1 (Bq.length - 1) = 0 := by
      rw [entry_last, ← hlast]; exact hlplev
    have hzBq : ¬ (entry Bq 0 (Bq.length - 1) = 0 ∧ entry Bq 1 (Bq.length - 1) = 0) := by
      rintro ⟨h1, -⟩
      rw [entry_last0, ← hlast] at h1
      omega
    have hbBq : blockok bd Bq := by
      refine ⟨?_, fun cc hcc => hb.2.1 cc (hmemBq cc hcc), ?_⟩
      · intro hne
        have h1 : bd ≤ (Bq.headI).1 := hb.2.1 _ (hmemBq _ (headI_mem hne))
        omega
      · exact (steps1_append.1 (by rw [← hBeq1]; exact hb.2.2)).2.1
    have hgeG1 : G1.length ≤ parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1) := by
      by_contra hlt
      have hhead : entry (p :: (A ++ T)) 0 G1.length = (Bq.headI).1 := by
        rw [hBeq1, show G1.length = G1.length + 0 by omega, entry_append_right, entry_zero0]
      have hthead : (Bq.headI).1 ≤ bd := by omega
      rcases Nat.lt_or_ge G1.length ((p :: (A ++ T)).length - 1) with hcase | hcase
      · have hx := hnrp.2.2.2.2 G1.length ⟨by omega, hcase⟩
        rw [entry_last0, hhead] at hx
        omega
      · have heq : G1.length = (p :: (A ++ T)).length - 1 := by omega
        rw [heq, entry_last0] at hhead
        omega
    have hiBq : idx1 Bq (Bq.length - 1) = 0 := by
      rw [idx1, if_neg (by rw [hlevBq]; omega)]
    have hidx : (p :: (A ++ T)).length - 1 = G1.length + (Bq.length - 1) := by omega
    have hpB : hasParent (G1 ++ Bq) (idx1 Bq (Bq.length - 1))
        (G1.length + (Bq.length - 1)) := by
      rw [hiBq, ← hidx, ← hBeq1]; exact hpar
    have hgeB : G1.length ≤ parent (G1 ++ Bq) (idx1 Bq (Bq.length - 1))
        (G1.length + (Bq.length - 1)) := by
      rw [hiBq, ← hidx, ← hBeq1]; exact hgeG1
    rw [hG1] at hpB hgeB
    have hIH := ih Bq (by omega) bd d p.2 false false hbBq hcBq hdBq hbd hz0 hlevBq hAPBq
      hpOK_false fOK_false
    obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_contr (Arg := A) (T := Bq)
      hAdeep hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 hBqh' hlad (by rw [hp1]; exact hbBq)
      hcBq hdBq (by omega) hzBq
      hpB hgeB hIH n hn
    refine ⟨m, n', k1, k2, ?_⟩
    rw [← hG1, ← hBeq1] at k3
    exact k3

/-- **縮約が発火しない状態は展開で保たれる**（未証明の残余。
実測: 標準形 ≤10 列の右端の道の全節点で反例 0）。 -/
def CtrPres : Prop :=
  ∀ (p : ℕ × ℕ) (A T : PairSeq) (bd : ℕ),
    blockok bd (p :: (A ++ T)) → colOK (p :: (A ++ T)) → descOK (p :: (A ++ T)) →
    p.1 = bd → (∀ x ∈ A, p.1 < x.1) → (T = [] ∨ ¬ (p.1 < (T.headI).1)) →
    contrLen p T (unitsLen p T) A = none →
    ∀ n : ℕ, 1 ≤ n → contrLen p (T⟦n⟧) (unitsLen p (T⟦n⟧)) A = none

/-- **段 0 の組み立て（縮約つき）**。残余は `CtrPres` と `RDzeroStop` の 2 つ。 -/
theorem reindexD_zero_block3 (Hp : CtrPres) (Hs : RDzeroStop) :
    ∀ (N : ℕ) (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → (bd = 0 → d = 0) →
      entry B 1 (B.length - 1) = 0 →
      argPatOK B → hpOK B d plev first force → fOK B d plev force →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force := by
  intro N
  induction N with
  | zero =>
    intro B hB bd d plev first force _ _ _ _ _ _ _ _ _ n hn
    have hBe : B = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hBe
    exact ⟨1, n, Nat.le_refl 1, Nat.le_refl n, by
      rw [convC_nil, oper_eq_self_short n (by simp), convC_nil,
        oper_eq_self_short 1 (by simp)]⟩
  | succ N ih =>
    intro B hB bd d plev first force hb hc hd hbd hz0 hlev hAP hHP hFC n hn
    cases B with
    | nil =>
      exact ⟨1, n, Nat.le_refl 1, Nat.le_refl n, by
        rw [convC_nil, oper_eq_self_short n (by simp), convC_nil,
          oper_eq_self_short 1 (by simp)]⟩
    | cons p r =>
      have hp1 : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp1]⟩
      -- 引数ブロックと兄弟ブロックに割る
      obtain ⟨A, T, hAd, hTd⟩ :
          ∃ A T, A = (r.takeWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) ∧
                 T = (r.dropWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) := ⟨_, _, rfl, rfl⟩
      have hrAT : r = A ++ T := by
        rw [hAd, hTd]; exact (List.takeWhile_append_dropWhile).symm
      subst hrAT
      have hAdeep : ∀ x ∈ A, ((bd, y) : ℕ × ℕ).1 < x.1 := by
        intro x hx
        rw [hAd] at hx
        simpa using List.mem_takeWhile_imp hx
      have hThd : T = [] ∨ ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
        rw [hTd]; exact dropWhile_head_not _ _
      obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := ((bd, y) : ℕ × ℕ).1)
        hAdeep hThd
      -- 新しい不変量を割る
      obtain ⟨hAPh, hAPa, hAPt⟩ := argPatOK_cons.1 hAP
      rw [e1] at hAPh hAPa
      rw [e2] at hAPt
      have hfA : fOK A (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
          ((bd, y) : ℕ × ℕ).2 (first && (((bd, y) : ℕ × ℕ).2 == plev)) := by
        intro hft
        have hf1 : first = true := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.1
        have hpl : ((bd, y) : ℕ × ℕ).2 = plev := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.2
        rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
        · left
          intro a s hs
          have hkey := hh ((bd, y) : ℕ × ℕ) (A ++ T) rfl hpl (by rw [e1, hs]; simp)
          rw [e1, hs] at hkey
          simpa using hkey
        · right
          subst hd0; subst hpl0; subst hfc0
          have hy0 : y = 0 := by simpa using hpl
          subst hy0
          simp [ddOf, ladOf]
      -- 不変量を割る
      have hbA : blockok (bd + 1) A := by rw [← e1]; exact blockok_arg hb
      have hbT : blockok bd T := by rw [← e2]; exact blockok_tail hb
      have hcA : colOK A := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_left A T))) hc
      have hcT : colOK T := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_right A T))) hc
      obtain ⟨hdh, hdA, hdT⟩ := descOK_cons.1 hd
      rw [e1] at hdA
      rw [e2] at hdh hdT
      have hlAT : A.length + T.length ≤ N := by
        simp only [List.length_cons, List.length_append] at hB
        omega
      -- 末尾列
      have hBne : ((bd, y) :: (A ++ T)) ≠ [] := by simp
      have hlplev : (((bd, y) :: (A ++ T)).getLastD (0, 0)).2 = 0 := by
        rw [← entry_last]; exact hlev
      by_cases hrne : A ++ T = []
      · -- 1 列のブロック
        obtain ⟨hAe, hTe⟩ := List.append_eq_nil_iff.1 hrne
        subst hAe; subst hTe
        have hy : y = 0 := by
          have h := hlplev
          simp only [List.append_nil, List.getLastD] at h
          simpa using h
        subst hy
        refine ⟨1, n, Nat.le_refl 1, Nat.le_refl n, ?_⟩
        have hnl : ladOf ((bd, 0) : ℕ × ℕ).2 d plev first force = false := by simp [ladOf]
        rw [List.append_nil, oper_eq_self_short n (by simp),
          convC_cons_nolad ((bd, 0) : ℕ × ℕ) [] d plev first force hnl]
        simp only [List.takeWhile_nil, List.dropWhile_nil, convC_nil, List.append_nil]
        exact oper_eq_self_short 1 (by simp)
      · have hL2 : 1 < ((bd, y) :: (A ++ T)).length := by
          simp only [List.length_cons]
          have := List.length_pos_of_ne_nil hrne
          omega
        have hlpmem : ((bd, y) :: (A ++ T)).getLastD (0, 0) ∈ ((bd, y) :: (A ++ T)) :=
          getLastD_mem hBne _
        by_cases hlp0 : (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 = 0
        · -- 場合 (a): 末尾列 = (0,0)
          have hbd0 : bd = 0 := by
            have := hb.2.1 _ hlpmem
            omega
          have hd0 : d = 0 := hz0 hbd0
          subst hd0
          have hlpeq : ((bd, y) :: (A ++ T)).getLastD (0, 0) = ((0, 0) : ℕ × ℕ) :=
            Prod.ext hlp0 hlplev
          have hg : ((bd, y) :: (A ++ T)).getLast hBne = ((0, 0) : ℕ × ℕ) := by
            rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast (h := hBne)] at hlpeq
            simpa using hlpeq
          have hsplit : ((bd, y) :: (A ++ T)).dropLast ++ [((0, 0) : ℕ × ℕ)]
              = ((bd, y) :: (A ++ T)) := by
            rw [← hg]; exact List.dropLast_append_getLast hBne
          have hdne : ((bd, y) :: (A ++ T)).dropLast ≠ [] := by
            intro he
            have hl : ((bd, y) :: (A ++ T)).dropLast.length
                = ((bd, y) :: (A ++ T)).length - 1 := List.length_dropLast
            rw [he] at hl
            simp only [List.length_nil] at hl
            omega
          have hcdl : colOK (((bd, y) :: (A ++ T)).dropLast) :=
            colOK_sublist (List.dropLast_sublist _) hc
          obtain ⟨m, n', h1, h2, h3⟩ := reindexD_succ_gen plev first force hdne hcdl n hn
          rw [hsplit] at h3
          exact ⟨m, n', h1, h2, h3⟩
        · -- 末尾列の深さは正
          have hlpos : 0 < (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 := by omega
          have hz : ¬ (entry ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1) = 0 ∧
                       entry ((bd, y) :: (A ++ T)) 1
                         (((bd, y) :: (A ++ T)).length - 1) = 0) := by
            rintro ⟨h1, -⟩
            rw [entry_last0] at h1
            omega
          have hi1 : idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1) = 0 := by
            rw [idx1, if_neg (by rw [hlev]; omega)]
          by_cases hpar : hasParent ((bd, y) :: (A ++ T))
              (idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1))
              (((bd, y) :: (A ++ T)).length - 1)
          · -- 親がある
            rw [hi1] at hpar
            have hnrp : nextrel0 ((bd, y) :: (A ++ T))
                (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1))
                (((bd, y) :: (A ++ T)).length - 1) := by
              have h := parent_nextR hpar
              unfold nextR at h; rw [if_pos rfl] at h; exact h
            have hj0ge : bd ≤ entry ((bd, y) :: (A ++ T)) 0
                (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1)) := by
              have hj := hnrp.1
              have hmem : ((bd, y) :: (A ++ T)).getD
                  (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1)) (0, 0)
                  ∈ ((bd, y) :: (A ++ T)) := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
                simpa using List.getElem_mem hj
              rw [entry, if_pos rfl]
              exact hb.2.1 _ hmem
            have hlpgt : bd < (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 := by
              have h1 := hnrp.2.2.2.1
              rw [entry_last0] at h1
              omega
            by_cases hTe : T = []
            · -- 兄弟が空: ブロックは p :: A
              subst hTe
              have hAne : A ≠ [] := by
                intro he; rw [he] at hrne; simp at hrne
              have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
              have hAlen : ((bd, y) :: (A ++ [])).length = A.length + 1 := by simp
              have hlastA : ((bd, y) :: (A ++ [])).getLastD (0, 0) = A.getLastD (0, 0) := by
                rw [List.append_nil]; exact getLastD_cons_ne _ hAne _
              have hlevA : entry A 1 (A.length - 1) = 0 := by
                rw [entry_last, ← hlastA]; exact hlplev
              have hiA : idx1 A (A.length - 1) = 0 := by
                rw [idx1, if_neg (by rw [hlevA]; omega)]
              have hzA : ¬ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0) := by
                rintro ⟨h1, -⟩
                rw [entry_last0, ← hlastA] at h1
                omega
              have hidx : ((bd, y) :: (A ++ [])).length - 1
                  = ([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1) := by
                simp only [List.length_cons, List.length_nil, List.append_nil]
                omega
              have hBeq : ((bd, y) :: (A ++ [])) = [((bd, y) : ℕ × ℕ)] ++ A := by simp
              by_cases hj00 : parent ((bd, y) :: (A ++ []))
                  0 (((bd, y) :: (A ++ [])).length - 1) = 0
              · -- 場合 (d): 親が節点
                have hnr0 : nextrel0 ((bd, y) :: (A ++ [])) 0
                    (((bd, y) :: (A ++ [])).length - 1) := by
                  rw [← hj00]; exact hnrp
                have hBA : ((bd, y) :: (A ++ [])) = (((bd, y) : ℕ × ℕ) :: A) := by simp
                have hmin : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1 := by
                  intro c hcm
                  obtain ⟨i, hi, hei⟩ := entry_of_mem hcm
                  rw [hBA] at hnr0
                  have key : entry (((bd, y) : ℕ × ℕ) :: A) 0
                      ((((bd, y) : ℕ × ℕ) :: A).length - 1)
                      ≤ entry (((bd, y) : ℕ × ℕ) :: A) 0 (i + 1) := by
                    rcases Nat.lt_or_ge (i + 1) ((((bd, y) : ℕ × ℕ) :: A).length - 1)
                      with hlt | hge
                    · exact hnr0.2.2.2.2 (i + 1) ⟨by omega, hlt⟩
                    · have hie : i + 1 = (((bd, y) : ℕ × ℕ) :: A).length - 1 := by
                        simp only [List.length_cons] at hge ⊢
                        omega
                      rw [hie]
                  have h1 : entry (((bd, y) : ℕ × ℕ) :: A) 0 (i + 1) = entry A 0 i :=
                    entry_cons_succ _ _ _ _
                  have h2 : entry (((bd, y) : ℕ × ℕ) :: A) 0 ((A.length - 1) + 1)
                      = entry A 0 (A.length - 1) := entry_cons_succ _ _ _ _
                  have h3 : (((bd, y) : ℕ × ℕ) :: A).length - 1 = (A.length - 1) + 1 := by
                    simp only [List.length_cons]
                    omega
                  rw [h3, h2, h1] at key
                  rw [← hei, ← entry_last0]
                  exact key
                have hlevA' : (A.getLastD (0, 0)).2 = 0 := by rw [← hlastA]; exact hlplev
                by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
                · -- 梯子つき: `fOK` が `force` を潰し、`d = p.2` が出る
                  have hlad2 : first = true ∧ ((bd, y) : ℕ × ℕ).2 = plev + 1
                      ∧ (d ≤ ((bd, y) : ℕ × ℕ).2 ∨ force = true) := by
                    unfold ladOf at hlad
                    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
                      decide_eq_true_eq] at hlad
                    exact ⟨hlad.1.1, hlad.1.2, hlad.2⟩
                  have hdy : d ≤ ((bd, y) : ℕ × ℕ).2 := by
                    rcases hlad2.2.2 with hh | hh
                    · exact hh
                    · rcases hFC hh with h1 | h2
                      · exact absurd hlad2.2.1 (h1 ((bd, y) : ℕ × ℕ) (A ++ []) rfl)
                      · have hpp := hlad2.2.1
                        simp only [] at hpp ⊢
                        omega
                  have hyd : ((bd, y) : ℕ × ℕ).2 ≤ ((bd, y) : ℕ × ℕ).1 :=
                    hc _ (by simp)
                  have hdp : d = ((bd, y) : ℕ × ℕ).2 := by
                    simp only [] at hdy hyd ⊢
                    omega
                  obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_lad_shape hAne hAdeep hmin
                    hlevA' d plev first force hlad hdp n hn
                  exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
                · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                    cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                    | false => rfl
                    | true => exact absurd hx hlad
                  by_cases hfr : (first && (((bd, y) : ℕ × ℕ).2 == plev)) = true
                  · -- `hpOK` で潰す枝
                    have hf1 : first = true := by
                      simp only [Bool.and_eq_true, beq_iff_eq] at hfr; exact hfr.1
                    have hpl : ((bd, y) : ℕ × ℕ).2 = plev := by
                      simp only [Bool.and_eq_true, beq_iff_eq] at hfr; exact hfr.2
                    rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
                    · have hkey := hh ((bd, y) : ℕ × ℕ) (A ++ []) rfl hpl
                        (by rw [e1]; exact hAne)
                      rw [e1] at hkey
                      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_gen2_shape hAne hAdeep
                        hmin hlevA' d plev first force hnl hkey n hn
                      exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
                    · -- 根: `conC` そのものなので `reindexD_node0` が効く
                      subst hd0; subst hpl0; subst hfc0; subst hf1
                      have hbd0 : bd = 0 := by omega
                      have hy0 : y = 0 := by
                        have hyc := hc ((bd, y) : ℕ × ℕ) (by simp)
                        simp only [] at hyc
                        omega
                      have hhd0 : ((bd, y) :: (A ++ [])).headI = ((0, 0) : ℕ × ℕ) := by
                        show ((bd, y) : ℕ × ℕ) = ((0, 0) : ℕ × ℕ)
                        rw [hbd0, hy0]
                      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_shape n hn hL2
                        (contrOK_of_last_zero hlev) hhd0 hlev hnr0
                      simp only [conC] at k3
                      exact ⟨m, n', k1, k2, k3⟩
                  · have hfr' : (first && (((bd, y) : ℕ × ℕ).2 == plev)) = false := by
                      cases hx : (first && (((bd, y) : ℕ × ℕ).2 == plev)) with
                      | false => rfl
                      | true => exact absurd hx hfr
                    obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_gen_shape hAne hAdeep hmin
                      hlevA' d plev first force hnl hfr' n hn
                    exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
              · -- 場合 (c): 引数ブロックへ降りる
                have hge1 : 1 ≤ parent ((bd, y) :: (A ++ [])) 0
                    (((bd, y) :: (A ++ [])).length - 1) := by omega
                have hpB : hasParent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                    (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
                  rw [hiA, ← hidx, ← hBeq]; exact hpar
                have hgeB : ([((bd, y) : ℕ × ℕ)] : PairSeq).length
                    ≤ parent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                        (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
                  rw [hiA, ← hidx, ← hBeq]
                  simpa using hge1
                by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
                · have hIH := ih A (by omega) (bd + 1) (d + 2) ((bd, y) : ℕ × ℕ).2 true false
                    hbA hcA hdA (by omega) (by omega) hlevA hAPa
                    (hpOK_of_headPatOK hAPh) fOK_false
                  have hres := reindexD_arg_lad (p := ((bd, y) : ℕ × ℕ)) hAdeep hlad hbA hcA hdA
                    (by omega) hzA hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
                · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                    cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                    | false => rfl
                    | true => exact absurd hx hlad
                  have hIH := ih A (by omega) (bd + 1)
                    (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
                    ((bd, y) : ℕ × ℕ).2 true (first && (((bd, y) : ℕ × ℕ).2 == plev))
                    hbA hcA hdA
                    (by have := le_ddOf ((bd, y) : ℕ × ℕ).2 d plev first force; omega)
                    (by omega) hlevA hAPa (hpOK_of_headPatOK hAPh) hfA
                  have hres := reindexD_arg_nolad (p := ((bd, y) : ℕ × ℕ)) hAdeep hnl hbA hcA hdA
                    (by omega) hzA hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
            · -- 兄弟が空でない: 親は兄弟の中にある
              have hTne : T ≠ [] := hTe
              have hT1 : 1 ≤ T.length := List.length_pos_of_ne_nil hTne
              have hTh : ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
                rcases hThd with h | h
                · exact absurd h hTne
                · exact h
              have hBeq : ((bd, y) :: (A ++ T))
                  = (((bd, y) : ℕ × ℕ) :: A) ++ T := by simp
              have hidx : ((bd, y) :: (A ++ T)).length - 1
                  = (((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1) := by
                simp only [List.length_cons, List.length_append]
                omega
              have hlastT : ((bd, y) :: (A ++ T)).getLastD (0, 0) = T.getLastD (0, 0) := by
                rw [hBeq]; exact getLastD_append_right hTne _
              have hlevT : entry T 1 (T.length - 1) = 0 := by
                rw [entry_last, ← hlastT]; exact hlplev
              have hiT : idx1 T (T.length - 1) = 0 := by
                rw [idx1, if_neg (by rw [hlevT]; omega)]
              have hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0) := by
                rintro ⟨h1, -⟩
                rw [entry_last0, ← hlastT] at h1
                omega
              -- 親は `p :: A` より後ろ
              have hgeT : (((bd, y) : ℕ × ℕ) :: A).length
                  ≤ parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1) := by
                by_contra hlt
                have hlt' : parent ((bd, y) :: (A ++ T)) 0
                    (((bd, y) :: (A ++ T)).length - 1)
                    < (((bd, y) : ℕ × ℕ) :: A).length := by omega
                have hhead : entry ((bd, y) :: (A ++ T)) 0
                    ((((bd, y) : ℕ × ℕ) :: A).length) = (T.headI).1 := by
                  rw [hBeq,
                    show (((bd, y) : ℕ × ℕ) :: A).length
                      = (((bd, y) : ℕ × ℕ) :: A).length + 0 by omega,
                    entry_append_right, entry_zero0]
                have hthead : (T.headI).1 ≤ bd := by omega
                rcases Nat.lt_or_ge ((((bd, y) : ℕ × ℕ) :: A).length)
                    (((bd, y) :: (A ++ T)).length - 1) with hcase | hcase
                · have := hnrp.2.2.2.2 ((((bd, y) : ℕ × ℕ) :: A).length) ⟨by omega, hcase⟩
                  rw [entry_last0, hhead] at this
                  omega
                · have heq : (((bd, y) : ℕ × ℕ) :: A).length
                      = ((bd, y) :: (A ++ T)).length - 1 := by
                    simp only [List.length_cons, List.length_append] at hcase ⊢
                    omega
                  rw [heq, entry_last0] at hhead
                  omega
              have hpB : hasParent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                  ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
                rw [hiT, ← hidx, ← hBeq]; exact hpar
              have hgeB : (((bd, y) : ℕ × ℕ) :: A).length
                  ≤ parent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                      ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
                rw [hiT, ← hidx, ← hBeq]; exact hgeT
              have hIH := ih T (by omega) bd d ((bd, y) : ℕ × ℕ).2 false false
                hbT hcT hdT hbd hz0 hlevT hAPt hpOK_false fOK_false
              by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
              · have hlad2 : first = true ∧ ((bd, y) : ℕ × ℕ).2 = plev + 1
                    ∧ (d ≤ ((bd, y) : ℕ × ℕ).2 ∨ force = true) := by
                  unfold ladOf at hlad
                  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
                    decide_eq_true_eq] at hlad
                  exact ⟨hlad.1.1, hlad.1.2, hlad.2⟩
                by_cases hnc : contrLen ((bd, y) : ℕ × ℕ) T
                    (unitsLen ((bd, y) : ℕ × ℕ) T) A = none
                · have hres := reindexD_sib_lad2 (p := ((bd, y) : ℕ × ℕ)) hAdeep hTh hlad hnc
                    (fun k hk => Hp ((bd, y) : ℕ × ℕ) A T bd hb hc hd rfl hAdeep hThd hnc k hk)
                    hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  rw [← hBeq] at k3
                  exact ⟨m, n', k1, k2, k3⟩
                · obtain ⟨rest2, Bq, hcc⟩ : ∃ rest2 Bq, contrLen ((bd, y) : ℕ × ℕ) T
                      (unitsLen ((bd, y) : ℕ × ℕ) T) A = some (rest2, Bq) := by
                    rcases hx : contrLen ((bd, y) : ℕ × ℕ) T
                        (unitsLen ((bd, y) : ℕ × ℕ) T) A with _ | ⟨r2, bq⟩
                    · exact absurd hx hnc
                    · exact ⟨r2, bq, rfl⟩
                  obtain ⟨qq, U, pre, hU, hTeq, hq2, hq1, hpre, hpd, hrd, hBqh,
                    hrne, hrh1, hrh2⟩ := contrLen_shape hcc
                  exact reindexD_zero_fire Hs N ih hB hb hc hd hbd hz0 rfl hlev hAP hAdeep
                    hlad hpar hU hTeq hq2 hq1 hpre hpd hrd hBqh hrne hrh1 hrh2 n hn
              · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                  cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                  | false => rfl
                  | true => exact absurd hx hlad
                have hres := reindexD_sib_nolad (p := ((bd, y) : ℕ × ℕ)) hAdeep hTh hnl
                  hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
                obtain ⟨m, n', k1, k2, k3⟩ := hres
                rw [← hBeq] at k3
                exact ⟨m, n', k1, k2, k3⟩
          · -- 場合 (b): 親がない
            exact reindexD_noParent_zero d plev first force hL2 hlev hz hpar n hn


/-- **段 0 の組み立て（入口・縮約つき）**。 -/
theorem reindexD_zero3 (Hp : CtrPres) (Hs : RDzeroStop) {M : PairSeq} (hM : ST_PS M)
    (hlev : entry M 1 (M.length - 1) = 0) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧ (conC M)⟦m⟧ = conC (M⟦n'⟧) := by
  intro n hn
  have h := reindexD_zero_block3 Hp Hs M.length M (Nat.le_refl _) 0 0 0 true false
    (blockok_ST_PS hM) (colOK_ST_PS hM) (descOK_ST_PS hM) (Nat.le_refl 0)
    (fun _ => rfl) hlev (argPatOK_ST_PS hM)
    (fun _ => Or.inr ⟨rfl, rfl, rfl⟩) fOK_false n hn
  obtain ⟨m, n', h1, h2, h3⟩ := h
  exact ⟨m, n', h1, h2, by rw [conC, conC]; exact h3⟩

/-- 段 0 の残余は `RDzeroRes2` 1 つから `CtrPres` と `RDzeroStop` の 2 つに割れた
（どちらも旧 `RDzeroRes2` よりずっと狭い）。 -/
theorem reindexD_holds_of_res3 (Hc : CtrRes) (Hp : CtrPres) (Hs : RDzeroStop)
    (H1 : RDposRes2) : ReindexD := by
  intro A hA hL n hn
  by_cases hz : entry A 1 (A.length - 1) = 0
  · exact reindexD_zero3 Hp Hs hA hz n hn
  · exact reindexD_pos_of2 Hc H1.1 H1.2.1 H1.2.2 hA hL (by omega) n hn

/-- 同じ形で主定理まで。 -/
theorem ST_D_conC_holds_of_res3 (Hc : CtrRes) (Hp : CtrPres) (Hs : RDzeroStop)
    (H1 : RDposRes2) {M : PairSeq} (hM : ST_PS M) : ST_D (conC M) :=
  ST_D_conC (reindexD_holds_of_res3 Hc Hp Hs H1) hM


/-- 深さで切れる前置きを剥がしても `argCtrOK` は残る。 -/
theorem argCtrOK_drop (a : ℕ) (L : PairSeq) (hL : L = [] ∨ ¬ (a < (L.headI).1)) :
    ∀ (n : ℕ) (V : PairSeq), V.length ≤ n → (∀ c ∈ V, a ≤ c.1) → (V = [] ∨ (V.headI).1 ≤ a) →
    argCtrOK (V ++ L) → argCtrOK L := by
  intro n
  induction n with
  | zero =>
      intro V hV _ _ h
      have : V = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simpa using h
  | succ n ih =>
      intro V hV hall hhd h
      match V with
      | [] => simpa using h
      | p :: rest =>
          have hp : p.1 = a := by
            have h1 : a ≤ p.1 := hall p (by simp)
            have h2 : p.1 ≤ a := by
              rcases hhd with hh | hh
              · exact absurd hh (by simp)
              · simpa using hh
            omega
          have hrest : ∀ c ∈ rest, a ≤ c.1 := fun c hc => hall c (by simp [hc])
          obtain ⟨e1, e2⟩ := split_append_gen (dd := p.1) (Y := L) (by rw [hp]; exact hL) rest
          have hlen : (rest.dropWhile fun q => p.1 < q.1).length ≤ n := by
            have := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) rest
            simp only [List.length_cons] at hV
            omega
          have hall' : ∀ c ∈ (rest.dropWhile fun q => p.1 < q.1), a ≤ c.1 :=
            fun c hc => hrest c ((List.dropWhile_sublist _).subset hc)
          have hhd' : (rest.dropWhile fun q => p.1 < q.1) = [] ∨
              ((rest.dropWhile fun q => p.1 < q.1).headI).1 ≤ a := by
            rcases dropWhile_head_neg (a := p.1) rest with hh | hh
            · exact Or.inl hh
            · exact Or.inr (by omega)
          rw [List.cons_append] at h
          have h2 := (argCtrOK_cons.1 h).2.2
          rw [e2] at h2
          exact ih _ hlen hall' hhd' h2

/-- **`CtrPres` は偽だった**（反例 `B = (1,1)(1,0)(2,1)(2,1)`, `n = 2`: `T` では段が
下がらないので発火しないが、`T⟦2⟧` では下がる）。`ctrHeadOK`（縮約の前置きが揃えば
必ず発火する）を足すと反例は消える（ブロック ≤7 列・`bd ≤ 2` の 447 万例で 0）。 -/
def CtrPres2 : Prop :=
  ∀ (p : ℕ × ℕ) (A T : PairSeq) (bd : ℕ),
    blockok bd (p :: (A ++ T)) → colOK (p :: (A ++ T)) → descOK (p :: (A ++ T)) →
    p.1 = bd → (∀ x ∈ A, p.1 < x.1) → (T = [] ∨ ¬ (p.1 < (T.headI).1)) →
    contrLen' p T (unitsLen p T) A = contrLen p T (unitsLen p T) A →
    contrLen p T (unitsLen p T) A = none →
    ∀ n : ℕ, 1 ≤ n → contrLen p (T⟦n⟧) (unitsLen p (T⟦n⟧)) A = none

/-- `RDzeroStop` に `argCtrOK` を足した版。 -/
def RDzeroStop2 : Prop :=
  ∀ (p q : ℕ × ℕ) (A U pre rest2 : PairSeq) (bd d plev : ℕ) (first force : Bool),
    blockok bd (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    colOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    descOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    bd ≤ d → p.1 = bd → (∀ x ∈ A, p.1 < x.1) →
    Units p U → q.2 + 1 = p.2 → q.1 = p.1 → pre = contrPre p U A →
    (∀ x ∈ pre, p.1 < x.1) → (∀ x ∈ rest2, p.1 < x.1) →
    rest2 ≠ [] → (rest2.headI).1 = p.1 + 1 → (rest2.headI).2 < p.2 →
    entry (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 1
      ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1) = 0 →
    argPatOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    argCtrOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    ladOf p.2 d plev first force = true →
    ¬ ((p :: (A ++ (U ++ q :: pre))).length
        ≤ parent (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 0
            ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1)) →
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ (U ++ q :: (pre ++ rest2)))) d plev first force)⟦m⟧
        = convC ((p :: (A ++ (U ++ q :: (pre ++ rest2))))⟦n'⟧) d plev first force

/-- **縮約が発火する段（段 0）**。`Bq ≠ []` なら `q` の兄弟へ、`Bq = []` なら
`rest2` へ降りる。降りられないのは「親が縮約の内側」のときだけ（`RDzeroStop`）。 -/
theorem reindexD_zero_fire2 (Hs : RDzeroStop2) (N : ℕ)
    (ih : ∀ (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → (bd = 0 → d = 0) →
      entry B 1 (B.length - 1) = 0 →
      argPatOK B → hpOK B d plev first force → fOK B d plev force →
      argCtrOK B → hcOK B plev first →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force)
    {p q : ℕ × ℕ} {A T U pre rest2 Bq : PairSeq} {bd d plev : ℕ} {first force : Bool}
    (hlenN : (p :: (A ++ T)).length ≤ N + 1)
    (hb : blockok bd (p :: (A ++ T))) (hc : colOK (p :: (A ++ T)))
    (hd : descOK (p :: (A ++ T))) (hbd : bd ≤ d) (hz0 : bd = 0 → d = 0)
    (hp1 : p.1 = bd)
    (hlev : entry (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) = 0)
    (hAP : argPatOK (p :: (A ++ T))) (hAC : argCtrOK (p :: (A ++ T)))
    (hAdeep : ∀ x ∈ A, p.1 < x.1)
    (hlad : ladOf p.2 d plev first force = true)
    (hpar : hasParent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1))
    (hU : Units p U) (hTeq : T = U ++ q :: ((pre ++ rest2) ++ Bq))
    (hq2 : q.2 + 1 = p.2) (hq1 : q.1 = p.1) (hpre : pre = contrPre p U A)
    (hpd : ∀ x ∈ pre, p.1 < x.1) (hrd : ∀ x ∈ rest2, p.1 < x.1)
    (hBqh : Bq = [] ∨ ¬ (p.1 < (Bq.headI).1))
    (hrne : rest2 ≠ []) (hrh1 : (rest2.headI).1 = p.1 + 1) (hrh2 : (rest2.headI).2 < p.2) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ T)) d plev first force)⟦m⟧
        = convC ((p :: (A ++ T))⟦n'⟧) d plev first force := by
  intro n hn
  -- 共通の下ごしらえ
  have hnrp : nextrel0 (p :: (A ++ T))
      (parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1))
      ((p :: (A ++ T)).length - 1) := by
    have h := parent_nextR hpar
    unfold nextR at h; rw [if_pos rfl] at h; exact h
  have hj0ge : bd ≤ entry (p :: (A ++ T)) 0
      (parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1)) := by
    have hj := hnrp.1
    have hmem : (p :: (A ++ T)).getD
        (parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1)) (0, 0) ∈ (p :: (A ++ T)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      simpa using List.getElem_mem hj
    rw [entry, if_pos rfl]
    exact hb.2.1 _ hmem
  have hlpgt : bd < ((p :: (A ++ T)).getLastD (0, 0)).1 := by
    have h1 := hnrp.2.2.2.1
    rw [entry_last0] at h1
    omega
  have hlplev : ((p :: (A ++ T)).getLastD (0, 0)).2 = 0 := by
    rw [← entry_last]; exact hlev
  have hTdeep : ∀ x ∈ (pre ++ rest2), p.1 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hpd x h
    · exact hrd x h
  have hpreh : (pre.headI).1 = p.1 + 1 := by rw [hpre]; simp [contrPre, shift1]
  have hThd : T = [] ∨ ¬ (p.1 < (T.headI).1) := by
    right
    rw [hTeq]
    by_cases hUe : U = []
    · rw [hUe]; simp only [List.nil_append, List.headI]; omega
    · rw [headI_append_left hUe]
      rcases hU.head_eq with h | h
      · exact absurd h hUe
      · rw [h]; omega
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := p.1) hAdeep hThd
  have hdT : descOK T := by
    have hx := (descOK_cons.1 hd).2.2
    rw [e2] at hx; exact hx
  have hAPt : argPatOK T := by
    have hx := (argPatOK_cons.1 hAP).2.2
    rw [e2] at hx; exact hx
  have hqL : (q :: ((pre ++ rest2) ++ Bq)) = []
      ∨ ¬ (p.1 < ((q :: ((pre ++ rest2) ++ Bq)).headI).1) := by
    right; simp only [List.headI]; omega
  have hdQ : descOK (q :: ((pre ++ rest2) ++ Bq)) :=
    descOK_units p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hdT)
  have hAPq : argPatOK (q :: ((pre ++ rest2) ++ Bq)) :=
    argPatOK_drop p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hAPt)
  obtain ⟨f1, f2⟩ := split_append (X := (pre ++ rest2)) (Y := Bq) (dd := q.1)
    (by rw [hq1]; exact hTdeep) (by rw [hq1]; exact hBqh)
  have hdBq : descOK Bq := by
    have hx := (descOK_cons.1 hdQ).2.2
    rw [f2] at hx; exact hx
  have hAPBq : argPatOK Bq := by
    have hx := (argPatOK_cons.1 hAPq).2.2
    rw [f2] at hx; exact hx
  have hdPR : descOK (pre ++ rest2) := by
    have hx := (descOK_cons.1 hdQ).2.1
    rw [f1] at hx; exact hx
  have hAPPR : argPatOK (pre ++ rest2) := by
    have hx := (argPatOK_cons.1 hAPq).2.1
    rw [f1] at hx; exact hx
  have hrestL : rest2 = [] ∨ ¬ (p.1 + 1 < (rest2.headI).1) := Or.inr (by rw [hrh1]; omega)
  have hpreall : ∀ c ∈ pre, p.1 + 1 ≤ c.1 := fun c hcc => by have := hpd c hcc; omega
  have hpreh' : pre = [] ∨ (pre.headI).1 ≤ p.1 + 1 := Or.inr (by rw [hpreh])
  have hdR : descOK rest2 :=
    descOK_units (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hdPR
  have hAPR : argPatOK rest2 :=
    argPatOK_drop (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hAPPR
  have hACt : argCtrOK T := by
    have hx := (argCtrOK_cons.1 hAC).2.2
    rw [e2] at hx; exact hx
  have hACq : argCtrOK (q :: ((pre ++ rest2) ++ Bq)) :=
    argCtrOK_drop p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hACt)
  have hACBq : argCtrOK Bq := by
    have hx := (argCtrOK_cons.1 hACq).2.2
    rw [f2] at hx; exact hx
  have hACPR : argCtrOK (pre ++ rest2) := by
    have hx := (argCtrOK_cons.1 hACq).2.1
    rw [f1] at hx; exact hx
  have hACR : argCtrOK rest2 :=
    argCtrOK_drop (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hACPR
  have hmemBq : ∀ c ∈ Bq, c ∈ (p :: (A ++ T)) := by
    intro c hcc
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    rw [hTeq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hcc))
  have hmemR : ∀ c ∈ rest2, c ∈ (p :: (A ++ T)) := by
    intro c hcc
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    rw [hTeq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_right _ hcc)))
  have hcBq : colOK Bq := fun cc hcc => hc cc (hmemBq cc hcc)
  have hcR : colOK rest2 := fun cc hcc => hc cc (hmemR cc hcc)
  by_cases hBqe : Bq = []
  · -- `Bq = []`: `rest2` へ降りるか、残余
    obtain ⟨G2, hG2⟩ : ∃ G2 : PairSeq, G2 = p :: (A ++ (U ++ q :: pre)) := ⟨_, rfl⟩
    have hBeq2 : (p :: (A ++ T)) = G2 ++ rest2 := by
      rw [hG2, hTeq, hBqe]; simp [List.append_assoc]
    have hBeq3 : (p :: (A ++ T)) = p :: (A ++ (U ++ q :: (pre ++ rest2))) := by
      rw [hTeq, hBqe]; simp [List.append_assoc]
    have hG2len : 1 ≤ G2.length := by rw [hG2]; simp
    have hlenB2 : (p :: (A ++ T)).length = G2.length + rest2.length := by
      rw [hBeq2]; simp
    have hlast : (p :: (A ++ T)).getLastD (0, 0) = rest2.getLastD (0, 0) := by
      rw [hBeq2]; exact getLastD_append_right hrne _
    have hlevR : entry rest2 1 (rest2.length - 1) = 0 := by
      rw [entry_last, ← hlast]; exact hlplev
    have hzR : ¬ (entry rest2 0 (rest2.length - 1) = 0 ∧ entry rest2 1 (rest2.length - 1) = 0) := by
      rintro ⟨h1, -⟩
      rw [entry_last0, ← hlast] at h1
      omega
    have hbR : blockok (p.1 + 1) rest2 := by
      refine ⟨fun _ => hrh1, fun cc hcc => by have := hrd cc hcc; omega, ?_⟩
      exact (steps1_append.1 (by rw [← hBeq2]; exact hb.2.2)).2.1
    by_cases hge2 : G2.length ≤ parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1)
    · have hiR : idx1 rest2 (rest2.length - 1) = 0 := by
        rw [idx1, if_neg (by rw [hlevR]; omega)]
      have hR1 : 1 ≤ rest2.length := List.length_pos_of_ne_nil hrne
      have hidx : (p :: (A ++ T)).length - 1 = G2.length + (rest2.length - 1) := by omega
      have hpB : hasParent (G2 ++ rest2) (idx1 rest2 (rest2.length - 1))
          (G2.length + (rest2.length - 1)) := by
        rw [hiR, ← hidx, ← hBeq2]; exact hpar
      have hgeB : G2.length ≤ parent (G2 ++ rest2) (idx1 rest2 (rest2.length - 1))
          (G2.length + (rest2.length - 1)) := by
        rw [hiR, ← hidx, ← hBeq2]; exact hge2
      rw [hG2] at hpB hgeB
      have hIH := ih rest2 (by omega) (p.1 + 1) (d + 1) p.2 false false hbR hcR hdR
        (by omega) (by omega) hlevR hAPR hpOK_false fOK_false hACR hcOK_false
      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_rest_contr (Arg := A) (T := rest2)
        hAdeep hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 hlad hbR hcR hdR (by omega) hzR
        hpB hgeB hIH n hn
      refine ⟨m, n', k1, k2, ?_⟩
      rw [← hG2, ← hBeq2] at k3
      exact k3
    · rw [hBeq3]
      refine Hs p q A U pre rest2 bd d plev first force ?_ ?_ ?_ hbd hp1 hAdeep hU hq2 hq1
        hpre hpd hrd hrne hrh1 hrh2 ?_ ?_ ?_ hlad ?_ n hn
      · rw [← hBeq3]; exact hb
      · rw [← hBeq3]; exact hc
      · rw [← hBeq3]; exact hd
      · rw [← hBeq3]; exact hlev
      · rw [← hBeq3]; exact hAP
      · rw [← hBeq3]; exact hAC
      · rw [← hBeq3, ← hG2]; exact hge2
  · -- `Bq ≠ []`: `q` の兄弟へ降りる
    have hBqh' : ¬ (p.1 < (Bq.headI).1) := by
      rcases hBqh with h | h
      · exact absurd h hBqe
      · exact h
    obtain ⟨G1, hG1⟩ : ∃ G1 : PairSeq, G1 = p :: (A ++ (U ++ q :: (pre ++ rest2))) := ⟨_, rfl⟩
    have hBeq1 : (p :: (A ++ T)) = G1 ++ Bq := by
      rw [hG1, hTeq]; simp [List.append_assoc]
    have hG1len : 1 ≤ G1.length := by rw [hG1]; simp
    have hBq1 : 1 ≤ Bq.length := List.length_pos_of_ne_nil hBqe
    have hlenB1 : (p :: (A ++ T)).length = G1.length + Bq.length := by
      rw [hBeq1]; simp
    have hlast : (p :: (A ++ T)).getLastD (0, 0) = Bq.getLastD (0, 0) := by
      rw [hBeq1]; exact getLastD_append_right hBqe _
    have hlevBq : entry Bq 1 (Bq.length - 1) = 0 := by
      rw [entry_last, ← hlast]; exact hlplev
    have hzBq : ¬ (entry Bq 0 (Bq.length - 1) = 0 ∧ entry Bq 1 (Bq.length - 1) = 0) := by
      rintro ⟨h1, -⟩
      rw [entry_last0, ← hlast] at h1
      omega
    have hbBq : blockok bd Bq := by
      refine ⟨?_, fun cc hcc => hb.2.1 cc (hmemBq cc hcc), ?_⟩
      · intro hne
        have h1 : bd ≤ (Bq.headI).1 := hb.2.1 _ (hmemBq _ (headI_mem hne))
        omega
      · exact (steps1_append.1 (by rw [← hBeq1]; exact hb.2.2)).2.1
    have hgeG1 : G1.length ≤ parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1) := by
      by_contra hlt
      have hhead : entry (p :: (A ++ T)) 0 G1.length = (Bq.headI).1 := by
        rw [hBeq1, show G1.length = G1.length + 0 by omega, entry_append_right, entry_zero0]
      have hthead : (Bq.headI).1 ≤ bd := by omega
      rcases Nat.lt_or_ge G1.length ((p :: (A ++ T)).length - 1) with hcase | hcase
      · have hx := hnrp.2.2.2.2 G1.length ⟨by omega, hcase⟩
        rw [entry_last0, hhead] at hx
        omega
      · have heq : G1.length = (p :: (A ++ T)).length - 1 := by omega
        rw [heq, entry_last0] at hhead
        omega
    have hiBq : idx1 Bq (Bq.length - 1) = 0 := by
      rw [idx1, if_neg (by rw [hlevBq]; omega)]
    have hidx : (p :: (A ++ T)).length - 1 = G1.length + (Bq.length - 1) := by omega
    have hpB : hasParent (G1 ++ Bq) (idx1 Bq (Bq.length - 1))
        (G1.length + (Bq.length - 1)) := by
      rw [hiBq, ← hidx, ← hBeq1]; exact hpar
    have hgeB : G1.length ≤ parent (G1 ++ Bq) (idx1 Bq (Bq.length - 1))
        (G1.length + (Bq.length - 1)) := by
      rw [hiBq, ← hidx, ← hBeq1]; exact hgeG1
    rw [hG1] at hpB hgeB
    have hIH := ih Bq (by omega) bd d p.2 false false hbBq hcBq hdBq hbd hz0 hlevBq hAPBq
      hpOK_false fOK_false hACBq hcOK_false
    obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_contr (Arg := A) (T := Bq)
      hAdeep hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 hBqh' hlad (by rw [hp1]; exact hbBq)
      hcBq hdBq (by omega) hzBq
      hpB hgeB hIH n hn
    refine ⟨m, n', k1, k2, ?_⟩
    rw [← hG1, ← hBeq1] at k3
    exact k3


/-- **段 0 の組み立て（不変量 `argCtrOK` / `hcOK` つき）**。
残余は `CtrPres2` と `RDzeroStop2` の 2 つ。 -/
theorem reindexD_zero_block4 (Hp : CtrPres2) (Hs : RDzeroStop2) :
    ∀ (N : ℕ) (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → (bd = 0 → d = 0) →
      entry B 1 (B.length - 1) = 0 →
      argPatOK B → hpOK B d plev first force → fOK B d plev force →
      argCtrOK B → hcOK B plev first →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force := by
  intro N
  induction N with
  | zero =>
    intro B hB bd d plev first force _ _ _ _ _ _ _ _ _ _ _ n hn
    have hBe : B = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hBe
    exact ⟨1, n, Nat.le_refl 1, Nat.le_refl n, by
      rw [convC_nil, oper_eq_self_short n (by simp), convC_nil,
        oper_eq_self_short 1 (by simp)]⟩
  | succ N ih =>
    intro B hB bd d plev first force hb hc hd hbd hz0 hlev hAP hHP hFC hAC hHC n hn
    cases B with
    | nil =>
      exact ⟨1, n, Nat.le_refl 1, Nat.le_refl n, by
        rw [convC_nil, oper_eq_self_short n (by simp), convC_nil,
          oper_eq_self_short 1 (by simp)]⟩
    | cons p r =>
      have hp1 : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp1]⟩
      -- 引数ブロックと兄弟ブロックに割る
      obtain ⟨A, T, hAd, hTd⟩ :
          ∃ A T, A = (r.takeWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) ∧
                 T = (r.dropWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) := ⟨_, _, rfl, rfl⟩
      have hrAT : r = A ++ T := by
        rw [hAd, hTd]; exact (List.takeWhile_append_dropWhile).symm
      subst hrAT
      have hAdeep : ∀ x ∈ A, ((bd, y) : ℕ × ℕ).1 < x.1 := by
        intro x hx
        rw [hAd] at hx
        simpa using List.mem_takeWhile_imp hx
      have hThd : T = [] ∨ ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
        rw [hTd]; exact dropWhile_head_not _ _
      obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := ((bd, y) : ℕ × ℕ).1)
        hAdeep hThd
      -- 新しい不変量を割る
      obtain ⟨hAPh, hAPa, hAPt⟩ := argPatOK_cons.1 hAP
      rw [e1] at hAPh hAPa
      rw [e2] at hAPt
      obtain ⟨hACh, hACa, hACt⟩ := argCtrOK_cons.1 hAC
      rw [e1] at hACh hACa
      rw [e2] at hACt
      have hfA : fOK A (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
          ((bd, y) : ℕ × ℕ).2 (first && (((bd, y) : ℕ × ℕ).2 == plev)) := by
        intro hft
        have hf1 : first = true := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.1
        have hpl : ((bd, y) : ℕ × ℕ).2 = plev := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.2
        rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
        · left
          intro a s hs
          have hkey := hh ((bd, y) : ℕ × ℕ) (A ++ T) rfl hpl (by rw [e1, hs]; simp)
          rw [e1, hs] at hkey
          simpa using hkey
        · right
          subst hd0; subst hpl0; subst hfc0
          have hy0 : y = 0 := by simpa using hpl
          subst hy0
          simp [ddOf, ladOf]
      -- 不変量を割る
      have hbA : blockok (bd + 1) A := by rw [← e1]; exact blockok_arg hb
      have hbT : blockok bd T := by rw [← e2]; exact blockok_tail hb
      have hcA : colOK A := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_left A T))) hc
      have hcT : colOK T := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_right A T))) hc
      obtain ⟨hdh, hdA, hdT⟩ := descOK_cons.1 hd
      rw [e1] at hdA
      rw [e2] at hdh hdT
      have hlAT : A.length + T.length ≤ N := by
        simp only [List.length_cons, List.length_append] at hB
        omega
      -- 末尾列
      have hBne : ((bd, y) :: (A ++ T)) ≠ [] := by simp
      have hlplev : (((bd, y) :: (A ++ T)).getLastD (0, 0)).2 = 0 := by
        rw [← entry_last]; exact hlev
      by_cases hrne : A ++ T = []
      · -- 1 列のブロック
        obtain ⟨hAe, hTe⟩ := List.append_eq_nil_iff.1 hrne
        subst hAe; subst hTe
        have hy : y = 0 := by
          have h := hlplev
          simp only [List.append_nil, List.getLastD] at h
          simpa using h
        subst hy
        refine ⟨1, n, Nat.le_refl 1, Nat.le_refl n, ?_⟩
        have hnl : ladOf ((bd, 0) : ℕ × ℕ).2 d plev first force = false := by simp [ladOf]
        rw [List.append_nil, oper_eq_self_short n (by simp),
          convC_cons_nolad ((bd, 0) : ℕ × ℕ) [] d plev first force hnl]
        simp only [List.takeWhile_nil, List.dropWhile_nil, convC_nil, List.append_nil]
        exact oper_eq_self_short 1 (by simp)
      · have hL2 : 1 < ((bd, y) :: (A ++ T)).length := by
          simp only [List.length_cons]
          have := List.length_pos_of_ne_nil hrne
          omega
        have hlpmem : ((bd, y) :: (A ++ T)).getLastD (0, 0) ∈ ((bd, y) :: (A ++ T)) :=
          getLastD_mem hBne _
        by_cases hlp0 : (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 = 0
        · -- 場合 (a): 末尾列 = (0,0)
          have hbd0 : bd = 0 := by
            have := hb.2.1 _ hlpmem
            omega
          have hd0 : d = 0 := hz0 hbd0
          subst hd0
          have hlpeq : ((bd, y) :: (A ++ T)).getLastD (0, 0) = ((0, 0) : ℕ × ℕ) :=
            Prod.ext hlp0 hlplev
          have hg : ((bd, y) :: (A ++ T)).getLast hBne = ((0, 0) : ℕ × ℕ) := by
            rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast (h := hBne)] at hlpeq
            simpa using hlpeq
          have hsplit : ((bd, y) :: (A ++ T)).dropLast ++ [((0, 0) : ℕ × ℕ)]
              = ((bd, y) :: (A ++ T)) := by
            rw [← hg]; exact List.dropLast_append_getLast hBne
          have hdne : ((bd, y) :: (A ++ T)).dropLast ≠ [] := by
            intro he
            have hl : ((bd, y) :: (A ++ T)).dropLast.length
                = ((bd, y) :: (A ++ T)).length - 1 := List.length_dropLast
            rw [he] at hl
            simp only [List.length_nil] at hl
            omega
          have hcdl : colOK (((bd, y) :: (A ++ T)).dropLast) :=
            colOK_sublist (List.dropLast_sublist _) hc
          obtain ⟨m, n', h1, h2, h3⟩ := reindexD_succ_gen plev first force hdne hcdl n hn
          rw [hsplit] at h3
          exact ⟨m, n', h1, h2, h3⟩
        · -- 末尾列の深さは正
          have hlpos : 0 < (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 := by omega
          have hz : ¬ (entry ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1) = 0 ∧
                       entry ((bd, y) :: (A ++ T)) 1
                         (((bd, y) :: (A ++ T)).length - 1) = 0) := by
            rintro ⟨h1, -⟩
            rw [entry_last0] at h1
            omega
          have hi1 : idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1) = 0 := by
            rw [idx1, if_neg (by rw [hlev]; omega)]
          by_cases hpar : hasParent ((bd, y) :: (A ++ T))
              (idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1))
              (((bd, y) :: (A ++ T)).length - 1)
          · -- 親がある
            rw [hi1] at hpar
            have hnrp : nextrel0 ((bd, y) :: (A ++ T))
                (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1))
                (((bd, y) :: (A ++ T)).length - 1) := by
              have h := parent_nextR hpar
              unfold nextR at h; rw [if_pos rfl] at h; exact h
            have hj0ge : bd ≤ entry ((bd, y) :: (A ++ T)) 0
                (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1)) := by
              have hj := hnrp.1
              have hmem : ((bd, y) :: (A ++ T)).getD
                  (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1)) (0, 0)
                  ∈ ((bd, y) :: (A ++ T)) := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
                simpa using List.getElem_mem hj
              rw [entry, if_pos rfl]
              exact hb.2.1 _ hmem
            have hlpgt : bd < (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 := by
              have h1 := hnrp.2.2.2.1
              rw [entry_last0] at h1
              omega
            by_cases hTe : T = []
            · -- 兄弟が空: ブロックは p :: A
              subst hTe
              have hAne : A ≠ [] := by
                intro he; rw [he] at hrne; simp at hrne
              have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
              have hAlen : ((bd, y) :: (A ++ [])).length = A.length + 1 := by simp
              have hlastA : ((bd, y) :: (A ++ [])).getLastD (0, 0) = A.getLastD (0, 0) := by
                rw [List.append_nil]; exact getLastD_cons_ne _ hAne _
              have hlevA : entry A 1 (A.length - 1) = 0 := by
                rw [entry_last, ← hlastA]; exact hlplev
              have hiA : idx1 A (A.length - 1) = 0 := by
                rw [idx1, if_neg (by rw [hlevA]; omega)]
              have hzA : ¬ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0) := by
                rintro ⟨h1, -⟩
                rw [entry_last0, ← hlastA] at h1
                omega
              have hidx : ((bd, y) :: (A ++ [])).length - 1
                  = ([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1) := by
                simp only [List.length_cons, List.length_nil, List.append_nil]
                omega
              have hBeq : ((bd, y) :: (A ++ [])) = [((bd, y) : ℕ × ℕ)] ++ A := by simp
              by_cases hj00 : parent ((bd, y) :: (A ++ []))
                  0 (((bd, y) :: (A ++ [])).length - 1) = 0
              · -- 場合 (d): 親が節点
                have hnr0 : nextrel0 ((bd, y) :: (A ++ [])) 0
                    (((bd, y) :: (A ++ [])).length - 1) := by
                  rw [← hj00]; exact hnrp
                have hBA : ((bd, y) :: (A ++ [])) = (((bd, y) : ℕ × ℕ) :: A) := by simp
                have hmin : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1 := by
                  intro c hcm
                  obtain ⟨i, hi, hei⟩ := entry_of_mem hcm
                  rw [hBA] at hnr0
                  have key : entry (((bd, y) : ℕ × ℕ) :: A) 0
                      ((((bd, y) : ℕ × ℕ) :: A).length - 1)
                      ≤ entry (((bd, y) : ℕ × ℕ) :: A) 0 (i + 1) := by
                    rcases Nat.lt_or_ge (i + 1) ((((bd, y) : ℕ × ℕ) :: A).length - 1)
                      with hlt | hge
                    · exact hnr0.2.2.2.2 (i + 1) ⟨by omega, hlt⟩
                    · have hie : i + 1 = (((bd, y) : ℕ × ℕ) :: A).length - 1 := by
                        simp only [List.length_cons] at hge ⊢
                        omega
                      rw [hie]
                  have h1 : entry (((bd, y) : ℕ × ℕ) :: A) 0 (i + 1) = entry A 0 i :=
                    entry_cons_succ _ _ _ _
                  have h2 : entry (((bd, y) : ℕ × ℕ) :: A) 0 ((A.length - 1) + 1)
                      = entry A 0 (A.length - 1) := entry_cons_succ _ _ _ _
                  have h3 : (((bd, y) : ℕ × ℕ) :: A).length - 1 = (A.length - 1) + 1 := by
                    simp only [List.length_cons]
                    omega
                  rw [h3, h2, h1] at key
                  rw [← hei, ← entry_last0]
                  exact key
                have hlevA' : (A.getLastD (0, 0)).2 = 0 := by rw [← hlastA]; exact hlplev
                by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
                · -- 梯子つき: `fOK` が `force` を潰し、`d = p.2` が出る
                  have hlad2 : first = true ∧ ((bd, y) : ℕ × ℕ).2 = plev + 1
                      ∧ (d ≤ ((bd, y) : ℕ × ℕ).2 ∨ force = true) := by
                    unfold ladOf at hlad
                    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
                      decide_eq_true_eq] at hlad
                    exact ⟨hlad.1.1, hlad.1.2, hlad.2⟩
                  have hdy : d ≤ ((bd, y) : ℕ × ℕ).2 := by
                    rcases hlad2.2.2 with hh | hh
                    · exact hh
                    · rcases hFC hh with h1 | h2
                      · exact absurd hlad2.2.1 (h1 ((bd, y) : ℕ × ℕ) (A ++ []) rfl)
                      · have hpp := hlad2.2.1
                        simp only [] at hpp ⊢
                        omega
                  have hyd : ((bd, y) : ℕ × ℕ).2 ≤ ((bd, y) : ℕ × ℕ).1 :=
                    hc _ (by simp)
                  have hdp : d = ((bd, y) : ℕ × ℕ).2 := by
                    simp only [] at hdy hyd ⊢
                    omega
                  obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_lad_shape hAne hAdeep hmin
                    hlevA' d plev first force hlad hdp n hn
                  exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
                · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                    cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                    | false => rfl
                    | true => exact absurd hx hlad
                  by_cases hfr : (first && (((bd, y) : ℕ × ℕ).2 == plev)) = true
                  · -- `hpOK` で潰す枝
                    have hf1 : first = true := by
                      simp only [Bool.and_eq_true, beq_iff_eq] at hfr; exact hfr.1
                    have hpl : ((bd, y) : ℕ × ℕ).2 = plev := by
                      simp only [Bool.and_eq_true, beq_iff_eq] at hfr; exact hfr.2
                    rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
                    · have hkey := hh ((bd, y) : ℕ × ℕ) (A ++ []) rfl hpl
                        (by rw [e1]; exact hAne)
                      rw [e1] at hkey
                      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_gen2_shape hAne hAdeep
                        hmin hlevA' d plev first force hnl hkey n hn
                      exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
                    · -- 根: `conC` そのものなので `reindexD_node0` が効く
                      subst hd0; subst hpl0; subst hfc0; subst hf1
                      have hbd0 : bd = 0 := by omega
                      have hy0 : y = 0 := by
                        have hyc := hc ((bd, y) : ℕ × ℕ) (by simp)
                        simp only [] at hyc
                        omega
                      have hhd0 : ((bd, y) :: (A ++ [])).headI = ((0, 0) : ℕ × ℕ) := by
                        show ((bd, y) : ℕ × ℕ) = ((0, 0) : ℕ × ℕ)
                        rw [hbd0, hy0]
                      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_shape n hn hL2
                        (contrOK_of_last_zero hlev) hhd0 hlev hnr0
                      simp only [conC] at k3
                      exact ⟨m, n', k1, k2, k3⟩
                  · have hfr' : (first && (((bd, y) : ℕ × ℕ).2 == plev)) = false := by
                      cases hx : (first && (((bd, y) : ℕ × ℕ).2 == plev)) with
                      | false => rfl
                      | true => exact absurd hx hfr
                    obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_gen_shape hAne hAdeep hmin
                      hlevA' d plev first force hnl hfr' n hn
                    exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
              · -- 場合 (c): 引数ブロックへ降りる
                have hge1 : 1 ≤ parent ((bd, y) :: (A ++ [])) 0
                    (((bd, y) :: (A ++ [])).length - 1) := by omega
                have hpB : hasParent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                    (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
                  rw [hiA, ← hidx, ← hBeq]; exact hpar
                have hgeB : ([((bd, y) : ℕ × ℕ)] : PairSeq).length
                    ≤ parent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                        (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
                  rw [hiA, ← hidx, ← hBeq]
                  simpa using hge1
                by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
                · have hIH := ih A (by omega) (bd + 1) (d + 2) ((bd, y) : ℕ × ℕ).2 true false
                    hbA hcA hdA (by omega) (by omega) hlevA hAPa
                    (hpOK_of_headPatOK hAPh) fOK_false hACa (fun _ => hACh)
                  have hres := reindexD_arg_lad (p := ((bd, y) : ℕ × ℕ)) hAdeep hlad hbA hcA hdA
                    (by omega) hzA hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
                · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                    cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                    | false => rfl
                    | true => exact absurd hx hlad
                  have hIH := ih A (by omega) (bd + 1)
                    (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
                    ((bd, y) : ℕ × ℕ).2 true (first && (((bd, y) : ℕ × ℕ).2 == plev))
                    hbA hcA hdA
                    (by have := le_ddOf ((bd, y) : ℕ × ℕ).2 d plev first force; omega)
                    (by omega) hlevA hAPa (hpOK_of_headPatOK hAPh) hfA hACa (fun _ => hACh)
                  have hres := reindexD_arg_nolad (p := ((bd, y) : ℕ × ℕ)) hAdeep hnl hbA hcA hdA
                    (by omega) hzA hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
            · -- 兄弟が空でない: 親は兄弟の中にある
              have hTne : T ≠ [] := hTe
              have hT1 : 1 ≤ T.length := List.length_pos_of_ne_nil hTne
              have hTh : ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
                rcases hThd with h | h
                · exact absurd h hTne
                · exact h
              have hBeq : ((bd, y) :: (A ++ T))
                  = (((bd, y) : ℕ × ℕ) :: A) ++ T := by simp
              have hidx : ((bd, y) :: (A ++ T)).length - 1
                  = (((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1) := by
                simp only [List.length_cons, List.length_append]
                omega
              have hlastT : ((bd, y) :: (A ++ T)).getLastD (0, 0) = T.getLastD (0, 0) := by
                rw [hBeq]; exact getLastD_append_right hTne _
              have hlevT : entry T 1 (T.length - 1) = 0 := by
                rw [entry_last, ← hlastT]; exact hlplev
              have hiT : idx1 T (T.length - 1) = 0 := by
                rw [idx1, if_neg (by rw [hlevT]; omega)]
              have hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0) := by
                rintro ⟨h1, -⟩
                rw [entry_last0, ← hlastT] at h1
                omega
              -- 親は `p :: A` より後ろ
              have hgeT : (((bd, y) : ℕ × ℕ) :: A).length
                  ≤ parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1) := by
                by_contra hlt
                have hlt' : parent ((bd, y) :: (A ++ T)) 0
                    (((bd, y) :: (A ++ T)).length - 1)
                    < (((bd, y) : ℕ × ℕ) :: A).length := by omega
                have hhead : entry ((bd, y) :: (A ++ T)) 0
                    ((((bd, y) : ℕ × ℕ) :: A).length) = (T.headI).1 := by
                  rw [hBeq,
                    show (((bd, y) : ℕ × ℕ) :: A).length
                      = (((bd, y) : ℕ × ℕ) :: A).length + 0 by omega,
                    entry_append_right, entry_zero0]
                have hthead : (T.headI).1 ≤ bd := by omega
                rcases Nat.lt_or_ge ((((bd, y) : ℕ × ℕ) :: A).length)
                    (((bd, y) :: (A ++ T)).length - 1) with hcase | hcase
                · have := hnrp.2.2.2.2 ((((bd, y) : ℕ × ℕ) :: A).length) ⟨by omega, hcase⟩
                  rw [entry_last0, hhead] at this
                  omega
                · have heq : (((bd, y) : ℕ × ℕ) :: A).length
                      = ((bd, y) :: (A ++ T)).length - 1 := by
                    simp only [List.length_cons, List.length_append] at hcase ⊢
                    omega
                  rw [heq, entry_last0] at hhead
                  omega
              have hpB : hasParent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                  ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
                rw [hiT, ← hidx, ← hBeq]; exact hpar
              have hgeB : (((bd, y) : ℕ × ℕ) :: A).length
                  ≤ parent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                      ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
                rw [hiT, ← hidx, ← hBeq]; exact hgeT
              have hIH := ih T (by omega) bd d ((bd, y) : ℕ × ℕ).2 false false
                hbT hcT hdT hbd hz0 hlevT hAPt hpOK_false fOK_false hACt hcOK_false
              by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
              · have hlad2 : first = true ∧ ((bd, y) : ℕ × ℕ).2 = plev + 1
                    ∧ (d ≤ ((bd, y) : ℕ × ℕ).2 ∨ force = true) := by
                  unfold ladOf at hlad
                  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
                    decide_eq_true_eq] at hlad
                  exact ⟨hlad.1.1, hlad.1.2, hlad.2⟩
                have hcth : contrLen' ((bd, y) : ℕ × ℕ) T (unitsLen ((bd, y) : ℕ × ℕ) T) A
                    = contrLen ((bd, y) : ℕ × ℕ) T (unitsLen ((bd, y) : ℕ × ℕ) T) A := by
                  have hx := hHC hlad2.1 ((bd, y) : ℕ × ℕ) (A ++ T) rfl hlad2.2.1
                  rw [e1, e2] at hx
                  exact hx
                by_cases hnc : contrLen ((bd, y) : ℕ × ℕ) T
                    (unitsLen ((bd, y) : ℕ × ℕ) T) A = none
                · have hres := reindexD_sib_lad2 (p := ((bd, y) : ℕ × ℕ)) hAdeep hTh hlad hnc
                    (fun k hk => Hp ((bd, y) : ℕ × ℕ) A T bd hb hc hd rfl hAdeep hThd hcth
                      hnc k hk)
                    hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  rw [← hBeq] at k3
                  exact ⟨m, n', k1, k2, k3⟩
                · obtain ⟨rest2, Bq, hcc⟩ : ∃ rest2 Bq, contrLen ((bd, y) : ℕ × ℕ) T
                      (unitsLen ((bd, y) : ℕ × ℕ) T) A = some (rest2, Bq) := by
                    rcases hx : contrLen ((bd, y) : ℕ × ℕ) T
                        (unitsLen ((bd, y) : ℕ × ℕ) T) A with _ | ⟨r2, bq⟩
                    · exact absurd hx hnc
                    · exact ⟨r2, bq, rfl⟩
                  obtain ⟨qq, U, pre, hU, hTeq, hq2, hq1, hpre, hpd, hrd, hBqh,
                    hrne, hrh1, hrh2⟩ := contrLen_shape hcc
                  exact reindexD_zero_fire2 Hs N ih hB hb hc hd hbd hz0 rfl hlev hAP hAC
                    hAdeep hlad hpar hU hTeq hq2 hq1 hpre hpd hrd hBqh hrne hrh1 hrh2 n hn
              · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                  cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                  | false => rfl
                  | true => exact absurd hx hlad
                have hres := reindexD_sib_nolad (p := ((bd, y) : ℕ × ℕ)) hAdeep hTh hnl
                  hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
                obtain ⟨m, n', k1, k2, k3⟩ := hres
                rw [← hBeq] at k3
                exact ⟨m, n', k1, k2, k3⟩
          · -- 場合 (b): 親がない
            exact reindexD_noParent_zero d plev first force hL2 hlev hz hpar n hn

/-- **段 0 の入口（不変量つき）**。`argCtrOK` は `CtrRes` から、根の `hcOK` は
`ctrHeadOK_root` から。 -/
theorem reindexD_zero4 (Hc : CtrRes) (Hp : CtrPres2) (Hs : RDzeroStop2)
    {M : PairSeq} (hM : ST_PS M) (hlev : entry M 1 (M.length - 1) = 0) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧ (conC M)⟦m⟧ = conC (M⟦n'⟧) := by
  intro n hn
  have h := reindexD_zero_block4 Hp Hs M.length M (Nat.le_refl _) 0 0 0 true false
    (blockok_ST_PS hM) (colOK_ST_PS hM) (descOK_ST_PS hM) (Nat.le_refl 0)
    (fun _ => rfl) hlev (argPatOK_ST_PS hM)
    (fun _ => Or.inr ⟨rfl, rfl, rfl⟩) fOK_false (Hc hM)
    (fun _ => ctrHeadOK_root (blockok_ST_PS hM) (colOK_ST_PS hM)) n hn
  obtain ⟨m, n', h1, h2, h3⟩ := h
  exact ⟨m, n', h1, h2, by rw [conC, conC]; exact h3⟩

/-- 段 0 の残余は `CtrPres2` と `RDzeroStop2` の 2 つ（どちらも実測で反例 0）。 -/
theorem reindexD_holds_of_res4 (Hc : CtrRes) (Hp : CtrPres2) (Hs : RDzeroStop2)
    (H1 : RDposRes2) : ReindexD := by
  intro A hA hL n hn
  by_cases hz : entry A 1 (A.length - 1) = 0
  · exact reindexD_zero4 Hc Hp Hs hA hz n hn
  · exact reindexD_pos_of2 Hc H1.1 H1.2.1 H1.2.2 hA hL (by omega) n hn

/-- 同じ形で主定理まで。 -/
theorem ST_D_conC_holds_of_res4 (Hc : CtrRes) (Hp : CtrPres2) (Hs : RDzeroStop2)
    (H1 : RDposRes2) {M : PairSeq} (hM : ST_PS M) : ST_D (conC M) :=
  ST_D_conC (reindexD_holds_of_res4 Hc Hp Hs H1) hM

/-- **段 > 0 で「縮約が発火して、しかも親が縮約の内側」の場合**（コピー regime）。 -/
def RDposStop : Prop :=
  ∀ (p q : ℕ × ℕ) (A U pre rest2 : PairSeq) (bd d plev : ℕ) (first force : Bool),
    blockok bd (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    colOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    descOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    bd ≤ d → p.1 = bd → (∀ x ∈ A, p.1 < x.1) →
    Units p U → q.2 + 1 = p.2 → q.1 = p.1 → pre = contrPre p U A →
    (∀ x ∈ pre, p.1 < x.1) → (∀ x ∈ rest2, p.1 < x.1) →
    rest2 ≠ [] → (rest2.headI).1 = p.1 + 1 → (rest2.headI).2 < p.2 →
    0 < entry (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 1
      ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1) →
    argPatOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    argCtrOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    adjLev (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    ladOf p.2 d plev first force = true →
    ¬ ((p :: (A ++ (U ++ q :: pre))).length
        ≤ parent (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 1
            ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1)) →
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ (U ++ q :: (pre ++ rest2)))) d plev first force)⟦m⟧
        = convC ((p :: (A ++ (U ++ q :: (pre ++ rest2))))⟦n'⟧) d plev first force

/-- **縮約が発火する段（段 > 0）**。段 0 と同じく `Bq ≠ []` なら `q` の兄弟へ、
`Bq = []` なら `rest2` へ降りる。 -/
theorem reindexD_pos_fire (Hs : RDposStop) (N : ℕ)
    (ih : ∀ (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → 2 ≤ B.length →
      0 < entry B 1 (B.length - 1) →
      argPatOK B → argCtrOK B → adjLev B →
      hpOK B d plev first force → fOK B d plev force →
      dpOK bd d plev first → hcOK B plev first →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force)
    {p q : ℕ × ℕ} {A T U pre rest2 Bq : PairSeq} {bd d plev : ℕ} {first force : Bool}
    (hlenN : (p :: (A ++ T)).length ≤ N + 1)
    (hb : blockok bd (p :: (A ++ T))) (hc : colOK (p :: (A ++ T)))
    (hd : descOK (p :: (A ++ T))) (hbd : bd ≤ d)
    (hp1 : p.1 = bd)
    (hlev : 0 < entry (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1))
    (hAP : argPatOK (p :: (A ++ T))) (hAC : argCtrOK (p :: (A ++ T)))
    (hLB : adjLev (p :: (A ++ T)))
    (hAdeep : ∀ x ∈ A, p.1 < x.1)
    (hlad : ladOf p.2 d plev first force = true)
    (hpar : hasParent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1))
    (hU : Units p U) (hTeq : T = U ++ q :: ((pre ++ rest2) ++ Bq))
    (hq2 : q.2 + 1 = p.2) (hq1 : q.1 = p.1) (hpre : pre = contrPre p U A)
    (hpd : ∀ x ∈ pre, p.1 < x.1) (hrd : ∀ x ∈ rest2, p.1 < x.1)
    (hBqh : Bq = [] ∨ ¬ (p.1 < (Bq.headI).1))
    (hrne : rest2 ≠ []) (hrh1 : (rest2.headI).1 = p.1 + 1) (hrh2 : (rest2.headI).2 < p.2) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ T)) d plev first force)⟦m⟧
        = convC ((p :: (A ++ T))⟦n'⟧) d plev first force := by
  intro n hn
  have hnr1 : nextrel1 (p :: (A ++ T))
      (parent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1))
      ((p :: (A ++ T)).length - 1) := by
    have h := parent_nextR hpar
    unfold nextR at h; rw [if_neg (by simp)] at h; exact h
  have hjlt : parent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1)
      < (p :: (A ++ T)).length - 1 := hnr1.2.2.1
  have hTdeep : ∀ x ∈ (pre ++ rest2), p.1 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hpd x h
    · exact hrd x h
  have hpreh : (pre.headI).1 = p.1 + 1 := by rw [hpre]; simp [contrPre, shift1]
  have hThd : T = [] ∨ ¬ (p.1 < (T.headI).1) := by
    right
    rw [hTeq]
    by_cases hUe : U = []
    · rw [hUe]; simp only [List.nil_append, List.headI]; omega
    · rw [headI_append_left hUe]
      rcases hU.head_eq with h | h
      · exact absurd h hUe
      · rw [h]; omega
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := p.1) hAdeep hThd
  have hdT : descOK T := by
    have hx := (descOK_cons.1 hd).2.2
    rw [e2] at hx; exact hx
  have hAPt : argPatOK T := by
    have hx := (argPatOK_cons.1 hAP).2.2
    rw [e2] at hx; exact hx
  have hACt : argCtrOK T := by
    have hx := (argCtrOK_cons.1 hAC).2.2
    rw [e2] at hx; exact hx
  have hqL : (q :: ((pre ++ rest2) ++ Bq)) = []
      ∨ ¬ (p.1 < ((q :: ((pre ++ rest2) ++ Bq)).headI).1) := by
    right; simp only [List.headI]; omega
  have hdQ : descOK (q :: ((pre ++ rest2) ++ Bq)) :=
    descOK_units p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hdT)
  have hAPq : argPatOK (q :: ((pre ++ rest2) ++ Bq)) :=
    argPatOK_drop p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hAPt)
  have hACq : argCtrOK (q :: ((pre ++ rest2) ++ Bq)) :=
    argCtrOK_drop p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hACt)
  obtain ⟨f1, f2⟩ := split_append (X := (pre ++ rest2)) (Y := Bq) (dd := q.1)
    (by rw [hq1]; exact hTdeep) (by rw [hq1]; exact hBqh)
  have hdBq : descOK Bq := by
    have hx := (descOK_cons.1 hdQ).2.2
    rw [f2] at hx; exact hx
  have hAPBq : argPatOK Bq := by
    have hx := (argPatOK_cons.1 hAPq).2.2
    rw [f2] at hx; exact hx
  have hACBq : argCtrOK Bq := by
    have hx := (argCtrOK_cons.1 hACq).2.2
    rw [f2] at hx; exact hx
  have hdPR : descOK (pre ++ rest2) := by
    have hx := (descOK_cons.1 hdQ).2.1
    rw [f1] at hx; exact hx
  have hAPPR : argPatOK (pre ++ rest2) := by
    have hx := (argPatOK_cons.1 hAPq).2.1
    rw [f1] at hx; exact hx
  have hACPR : argCtrOK (pre ++ rest2) := by
    have hx := (argCtrOK_cons.1 hACq).2.1
    rw [f1] at hx; exact hx
  have hrestL : rest2 = [] ∨ ¬ (p.1 + 1 < (rest2.headI).1) := Or.inr (by rw [hrh1]; omega)
  have hpreall : ∀ c ∈ pre, p.1 + 1 ≤ c.1 := fun c hcc => by have := hpd c hcc; omega
  have hpreh' : pre = [] ∨ (pre.headI).1 ≤ p.1 + 1 := Or.inr (by rw [hpreh])
  have hdR : descOK rest2 :=
    descOK_units (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hdPR
  have hAPR : argPatOK rest2 :=
    argPatOK_drop (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hAPPR
  have hACR : argCtrOK rest2 :=
    argCtrOK_drop (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hACPR
  have hmemBq : ∀ c ∈ Bq, c ∈ (p :: (A ++ T)) := by
    intro c hcc
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    rw [hTeq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hcc))
  have hmemR : ∀ c ∈ rest2, c ∈ (p :: (A ++ T)) := by
    intro c hcc
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    rw [hTeq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_right _ hcc)))
  have hcBq : colOK Bq := fun cc hcc => hc cc (hmemBq cc hcc)
  have hcR : colOK rest2 := fun cc hcc => hc cc (hmemR cc hcc)
  by_cases hBqe : Bq = []
  · -- `Bq = []`: `rest2` へ降りるか、残余
    obtain ⟨G2, hG2⟩ : ∃ G2 : PairSeq, G2 = p :: (A ++ (U ++ q :: pre)) := ⟨_, rfl⟩
    have hBeq2 : (p :: (A ++ T)) = G2 ++ rest2 := by
      rw [hG2, hTeq, hBqe]; simp [List.append_assoc]
    have hBeq3 : (p :: (A ++ T)) = p :: (A ++ (U ++ q :: (pre ++ rest2))) := by
      rw [hTeq, hBqe]; simp [List.append_assoc]
    have hG2len : 1 ≤ G2.length := by rw [hG2]; simp
    have hR1 : 1 ≤ rest2.length := List.length_pos_of_ne_nil hrne
    have hlenB2 : (p :: (A ++ T)).length = G2.length + rest2.length := by
      rw [hBeq2]; simp
    have hlast : (p :: (A ++ T)).getLastD (0, 0) = rest2.getLastD (0, 0) := by
      rw [hBeq2]; exact getLastD_append_right hrne _
    have hlevR : 0 < entry rest2 1 (rest2.length - 1) := by
      rw [entry_last, ← hlast, ← entry_last]; exact hlev
    have hzR : ¬ (entry rest2 0 (rest2.length - 1) = 0 ∧ entry rest2 1 (rest2.length - 1) = 0) := by
      rintro ⟨-, h1⟩
      omega
    have hbR : blockok (p.1 + 1) rest2 := by
      refine ⟨fun _ => hrh1, fun cc hcc => by have := hrd cc hcc; omega, ?_⟩
      exact (steps1_append.1 (by rw [← hBeq2]; exact hb.2.2)).2.1
    have hLR : adjLev rest2 :=
      adjLev_infix ⟨G2, [], by rw [List.append_nil]; exact hBeq2.symm⟩ hLB
    by_cases hge2 : G2.length ≤ parent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1)
    · have hiR : idx1 rest2 (rest2.length - 1) = 1 := by rw [idx1, if_pos hlevR]
      have hR2 : 2 ≤ rest2.length := by omega
      have hidx : (p :: (A ++ T)).length - 1 = G2.length + (rest2.length - 1) := by omega
      have hpB : hasParent (G2 ++ rest2) (idx1 rest2 (rest2.length - 1))
          (G2.length + (rest2.length - 1)) := by
        rw [hiR, ← hidx, ← hBeq2]; exact hpar
      have hgeB : G2.length ≤ parent (G2 ++ rest2) (idx1 rest2 (rest2.length - 1))
          (G2.length + (rest2.length - 1)) := by
        rw [hiR, ← hidx, ← hBeq2]; exact hge2
      rw [hG2] at hpB hgeB
      have hIH := ih rest2 (by omega) (p.1 + 1) (d + 1) p.2 false false hbR hcR hdR
        (by omega) hR2 hlevR hAPR hACR hLR hpOK_false fOK_false dpOK_false hcOK_false
      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_rest_contr (Arg := A) (T := rest2)
        hAdeep hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 hlad hbR hcR hdR (by omega) hzR
        hpB hgeB hIH n hn
      refine ⟨m, n', k1, k2, ?_⟩
      rw [← hG2, ← hBeq2] at k3
      exact k3
    · rw [hBeq3]
      refine Hs p q A U pre rest2 bd d plev first force ?_ ?_ ?_ hbd hp1 hAdeep hU hq2 hq1
        hpre hpd hrd hrne hrh1 hrh2 ?_ ?_ ?_ ?_ hlad ?_ n hn
      · rw [← hBeq3]; exact hb
      · rw [← hBeq3]; exact hc
      · rw [← hBeq3]; exact hd
      · rw [← hBeq3]; exact hlev
      · rw [← hBeq3]; exact hAP
      · rw [← hBeq3]; exact hAC
      · rw [← hBeq3]; exact hLB
      · rw [← hBeq3, ← hG2]; exact hge2
  · -- `Bq ≠ []`: `q` の兄弟へ降りる
    have hBqh' : ¬ (p.1 < (Bq.headI).1) := by
      rcases hBqh with h | h
      · exact absurd h hBqe
      · exact h
    obtain ⟨G1, hG1⟩ : ∃ G1 : PairSeq, G1 = p :: (A ++ (U ++ q :: (pre ++ rest2))) := ⟨_, rfl⟩
    have hBeq1 : (p :: (A ++ T)) = G1 ++ Bq := by
      rw [hG1, hTeq]; simp [List.append_assoc]
    have hG1len : 1 ≤ G1.length := by rw [hG1]; simp
    have hBq1 : 1 ≤ Bq.length := List.length_pos_of_ne_nil hBqe
    have hlenB1 : (p :: (A ++ T)).length = G1.length + Bq.length := by
      rw [hBeq1]; simp
    have hlast : (p :: (A ++ T)).getLastD (0, 0) = Bq.getLastD (0, 0) := by
      rw [hBeq1]; exact getLastD_append_right hBqe _
    have hlevBq : 0 < entry Bq 1 (Bq.length - 1) := by
      rw [entry_last, ← hlast, ← entry_last]; exact hlev
    have hzBq : ¬ (entry Bq 0 (Bq.length - 1) = 0 ∧ entry Bq 1 (Bq.length - 1) = 0) := by
      rintro ⟨-, h1⟩
      omega
    have hbBq : blockok bd Bq := by
      refine ⟨?_, fun cc hcc => hb.2.1 cc (hmemBq cc hcc), ?_⟩
      · intro hne
        have h1 : bd ≤ (Bq.headI).1 := hb.2.1 _ (hmemBq _ (headI_mem hne))
        omega
      · exact (steps1_append.1 (by rw [← hBeq1]; exact hb.2.2)).2.1
    have hLBq : adjLev Bq :=
      adjLev_infix ⟨G1, [], by rw [List.append_nil]; exact hBeq1.symm⟩ hLB
    have hlowG1 : ∀ c ∈ G1, bd ≤ c.1 := by
      intro c hcm
      exact hb.2.1 c (by rw [hBeq1]; exact List.mem_append_left _ hcm)
    have hidx : (p :: (A ++ T)).length - 1 = G1.length + (Bq.length - 1) := by omega
    have hle0 : le0 (G1 ++ Bq) (parent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1))
        (G1.length + (Bq.length - 1)) := by
      rw [← hidx, ← hBeq1]; exact hnr1.2.2.2.2.1
    have hgeG1 : G1.length ≤ parent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) :=
      le0_ge_of_append hBqe hlowG1 (hbBq.1 hBqe) hle0 (by omega)
    have hBq2 : 2 ≤ Bq.length := by omega
    have hiBq : idx1 Bq (Bq.length - 1) = 1 := by rw [idx1, if_pos hlevBq]
    have hpB : hasParent (G1 ++ Bq) (idx1 Bq (Bq.length - 1))
        (G1.length + (Bq.length - 1)) := by
      rw [hiBq, ← hidx, ← hBeq1]; exact hpar
    have hgeB : G1.length ≤ parent (G1 ++ Bq) (idx1 Bq (Bq.length - 1))
        (G1.length + (Bq.length - 1)) := by
      rw [hiBq, ← hidx, ← hBeq1]; exact hgeG1
    rw [hG1] at hpB hgeB
    have hIH := ih Bq (by omega) bd d p.2 false false hbBq hcBq hdBq hbd hBq2 hlevBq hAPBq
      hACBq hLBq hpOK_false fOK_false dpOK_false hcOK_false
    obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_contr (Arg := A) (T := Bq)
      hAdeep hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 hBqh' hlad (by rw [hp1]; exact hbBq)
      hcBq hdBq (by omega) hzBq hpB hgeB hIH n hn
    refine ⟨m, n', k1, k2, ?_⟩
    rw [← hG1, ← hBeq1] at k3
    exact k3


/-- **段 > 0 の組み立て（縮約つき）**。梯子つきの縮約は `CtrPres2` と `RDposStop` に
割れたので、残余は `CtrPres2` / `RDposStop` / `RDnopar` / `RDnode` の 4 つ。 -/
theorem reindexD_pos_block3 (Hp : CtrPres2) (Hs : RDposStop) (Hn : RDnopar) (Hd : RDnode) :
    ∀ (N : ℕ) (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → 2 ≤ B.length →
      0 < entry B 1 (B.length - 1) →
      argPatOK B → argCtrOK B → adjLev B →
      hpOK B d plev first force → fOK B d plev force →
      dpOK bd d plev first → hcOK B plev first →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force := by
  intro N
  induction N with
  | zero =>
    intro B hB bd d plev first force _ _ _ _ h2 _ _ _ _ _ _ _ _ n hn
    exact absurd hB (by omega)
  | succ N ih =>
    intro B hB bd d plev first force hb hc hd hbd h2 hlev hAP hAC hLB hHP hFC hDP hHC n hn
    cases B with
    | nil => exact absurd h2 (by simp)
    | cons p r =>
      have hp1 : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp1]⟩
      obtain ⟨A, T, hAd, hTd⟩ :
          ∃ A T, A = (r.takeWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) ∧
                 T = (r.dropWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) := ⟨_, _, rfl, rfl⟩
      have hrAT : r = A ++ T := by
        rw [hAd, hTd]; exact (List.takeWhile_append_dropWhile).symm
      subst hrAT
      have hAdeep : ∀ x ∈ A, ((bd, y) : ℕ × ℕ).1 < x.1 := by
        intro x hx
        rw [hAd] at hx
        simpa using List.mem_takeWhile_imp hx
      have hThd : T = [] ∨ ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
        rw [hTd]; exact dropWhile_head_not _ _
      obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := ((bd, y) : ℕ × ℕ).1)
        hAdeep hThd
      -- 新しい不変量を割る
      obtain ⟨hAPh, hAPa, hAPt⟩ := argPatOK_cons.1 hAP
      rw [e1] at hAPh hAPa
      rw [e2] at hAPt
      obtain ⟨hACh, hACa, hACt⟩ := argCtrOK_cons.1 hAC
      rw [e1] at hACh hACa
      rw [e2] at hACt
      have hLA : adjLev A := by
        have hx := adjLev_infix (takeWhile_infix_cons ((bd, y) : ℕ × ℕ) (A ++ T)) hLB
        rw [e1] at hx; exact hx
      have hLT : adjLev T := by
        have hx := adjLev_infix (dropWhile_infix_cons ((bd, y) : ℕ × ℕ) (A ++ T)) hLB
        rw [e2] at hx; exact hx
      have hycol : ((bd, y) : ℕ × ℕ).2 ≤ ((bd, y) : ℕ × ℕ).1 := hc _ (by simp)
      have hfA : fOK A (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
          ((bd, y) : ℕ × ℕ).2 (first && (((bd, y) : ℕ × ℕ).2 == plev)) := by
        intro hft
        have hf1 : first = true := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.1
        have hpl : ((bd, y) : ℕ × ℕ).2 = plev := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.2
        rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
        · left
          intro a s hs
          have hkey := hh ((bd, y) : ℕ × ℕ) (A ++ T) rfl hpl (by rw [e1, hs]; simp)
          rw [e1, hs] at hkey
          simpa using hkey
        · right
          subst hd0; subst hpl0; subst hfc0
          have hy0 : y = 0 := by simpa using hpl
          subst hy0
          simp [ddOf, ladOf]
      have hbA : blockok (bd + 1) A := by rw [← e1]; exact blockok_arg hb
      have hbT : blockok bd T := by rw [← e2]; exact blockok_tail hb
      have hcA : colOK A := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_left A T))) hc
      have hcT : colOK T := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_right A T))) hc
      obtain ⟨hdh, hdA, hdT⟩ := descOK_cons.1 hd
      rw [e1] at hdA
      rw [e2] at hdh hdT
      have hlAT : A.length + T.length ≤ N := by
        simp only [List.length_cons, List.length_append] at hB
        omega
      have hlen : ((bd, y) :: (A ++ T)).length = A.length + T.length + 1 := by simp
      have hi1 : idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1) = 1 := by
        rw [idx1, if_pos hlev]
      by_cases hpar : hasParent ((bd, y) :: (A ++ T)) 1
          (((bd, y) :: (A ++ T)).length - 1)
      · have hnr1 : nextrel1 ((bd, y) :: (A ++ T))
            (parent ((bd, y) :: (A ++ T)) 1 (((bd, y) :: (A ++ T)).length - 1))
            (((bd, y) :: (A ++ T)).length - 1) := by
          have h := parent_nextR hpar
          unfold nextR at h; rw [if_neg (by omega)] at h; exact h
        by_cases hTe : T = []
        · -- 兄弟が空: ブロックは p :: A
          subst hTe
          have hAne : A ≠ [] := by
            intro he
            rw [he] at h2
            simp at h2
          have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
          have hlastA : ((bd, y) :: (A ++ [])).getLastD (0, 0) = A.getLastD (0, 0) := by
            rw [List.append_nil]; exact getLastD_cons_ne _ hAne _
          have hlevA : 0 < entry A 1 (A.length - 1) := by
            rw [entry_last, ← hlastA, ← entry_last]; exact hlev
          have hiA : idx1 A (A.length - 1) = 1 := by rw [idx1, if_pos hlevA]
          have hzA : ¬ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0) := by
            rintro ⟨-, h1⟩
            omega
          have hidx : ((bd, y) :: (A ++ [])).length - 1
              = ([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1) := by
            simp only [List.length_cons, List.length_nil, List.append_nil]
            omega
          have hBeq : ((bd, y) :: (A ++ [])) = [((bd, y) : ℕ × ℕ)] ++ A := by simp
          by_cases hj00 : parent ((bd, y) :: (A ++ []))
              1 (((bd, y) :: (A ++ [])).length - 1) = 0
          · -- 場合 (d): 親が節点（ずれたコピーの補題が要る）
            exact Hd ((bd, y) : ℕ × ℕ) A [] bd d plev first force hb hc hd hbd rfl h2
              hAdeep (Or.inl rfl) hlev hAP hAC hLB hHP hFC hDP hHC ⟨rfl, hj00⟩ n hn
          · -- 場合 (c): 引数ブロックへ降りる
            have hlenA : ((bd, y) :: (A ++ [])).length - 1 = A.length := by simp
            have hA2 : 2 ≤ A.length := by
              have hj0lt := hnr1.2.2.1
              have hj0ne : parent ((bd, y) :: (A ++ [])) 1
                  (((bd, y) :: (A ++ [])).length - 1) ≠ 0 := hj00
              omega
            have hpB : hasParent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
              rw [hiA, ← hidx, ← hBeq]; exact hpar
            have hgeB : ([((bd, y) : ℕ × ℕ)] : PairSeq).length
                ≤ parent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                    (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
              rw [hiA, ← hidx, ← hBeq]
              show 1 ≤ parent ((bd, y) :: (A ++ [])) 1 (((bd, y) :: (A ++ [])).length - 1)
              omega
            by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
            · have hIH := ih A (by omega) (bd + 1) (d + 2) ((bd, y) : ℕ × ℕ).2 true false
                hbA hcA hdA (by omega) hA2 hlevA hAPa hACa hLA
                (hpOK_of_headPatOK hAPh) fOK_false
                (fun _ he => absurd he (by omega)) (fun _ => hACh)
              obtain ⟨m, n', k1, k2, k3⟩ := reindexD_arg_lad (p := ((bd, y) : ℕ × ℕ))
                hAdeep hlad hbA hcA hdA (by omega) hzA hpB hgeB hIH n hn
              exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
            · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                | false => rfl
                | true => exact absurd hx hlad
              have hIH := ih A (by omega) (bd + 1)
                (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
                ((bd, y) : ℕ × ℕ).2 true (first && (((bd, y) : ℕ × ℕ).2 == plev))
                hbA hcA hdA
                (by have := le_ddOf ((bd, y) : ℕ × ℕ).2 d plev first force; omega)
                hA2 hlevA hAPa hACa hLA (hpOK_of_headPatOK hAPh) hfA
                (dpOK_arg (p := ((bd, y) : ℕ × ℕ)) rfl hbd hycol) (fun _ => hACh)
              obtain ⟨m, n', k1, k2, k3⟩ := reindexD_arg_nolad (p := ((bd, y) : ℕ × ℕ))
                hAdeep hnl hbA hcA hdA (by omega) hzA hpB hgeB hIH n hn
              exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
        · -- 兄弟が空でない: 床の補題で親は兄弟の中
          have hTne : T ≠ [] := hTe
          have hT1 : 1 ≤ T.length := List.length_pos_of_ne_nil hTne
          have hTh : ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
            rcases hThd with h | h
            · exact absurd h hTne
            · exact h
          have hBeq : ((bd, y) :: (A ++ T)) = (((bd, y) : ℕ × ℕ) :: A) ++ T := by simp
          have hidx : ((bd, y) :: (A ++ T)).length - 1
              = (((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1) := by
            simp only [List.length_cons, List.length_append]
            omega
          have hlastT : ((bd, y) :: (A ++ T)).getLastD (0, 0) = T.getLastD (0, 0) := by
            rw [hBeq]; exact getLastD_append_right hTne _
          have hlevT : 0 < entry T 1 (T.length - 1) := by
            rw [entry_last, ← hlastT, ← entry_last]; exact hlev
          have hiT : idx1 T (T.length - 1) = 1 := by rw [idx1, if_pos hlevT]
          have hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0) := by
            rintro ⟨-, h1⟩
            omega
          -- 床の補題
          have hlowG : ∀ c ∈ (((bd, y) : ℕ × ℕ) :: A), bd ≤ c.1 := by
            intro c hcm
            refine hb.2.1 c ?_
            rw [hBeq]
            exact List.mem_append_left _ hcm
          have hhead : (T.headI).1 = bd := hbT.1 hTne
          have hle0 : le0 ((((bd, y) : ℕ × ℕ) :: A) ++ T)
              (parent ((bd, y) :: (A ++ T)) 1 (((bd, y) :: (A ++ T)).length - 1))
              (((bd, y) :: (A ++ T)).length - 1) := by
            rw [← hBeq]; exact hnr1.2.2.2.2.1
          have hgeT : (((bd, y) : ℕ × ℕ) :: A).length
              ≤ parent ((bd, y) :: (A ++ T)) 1 (((bd, y) :: (A ++ T)).length - 1) :=
            le0_ge_of_append hTne hlowG hhead hle0 (by rw [hidx]; omega)
          have hj0lt := hnr1.2.2.1
          have hT2 : 2 ≤ T.length := by
            simp only [List.length_cons, List.length_append] at hj0lt hgeT
            omega
          have hpB : hasParent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
              ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
            rw [hiT, ← hidx, ← hBeq]; exact hpar
          have hgeB : (((bd, y) : ℕ × ℕ) :: A).length
              ≤ parent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                  ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
            rw [hiT, ← hidx, ← hBeq]; exact hgeT
          have hIH := ih T (by omega) bd d ((bd, y) : ℕ × ℕ).2 false false
            hbT hcT hdT hbd hT2 hlevT hAPt hACt hLT hpOK_false fOK_false
            dpOK_false hcOK_false
          by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
          · have hlad2 : first = true ∧ ((bd, y) : ℕ × ℕ).2 = plev + 1 := by
              unfold ladOf at hlad
              simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
                decide_eq_true_eq] at hlad
              exact ⟨hlad.1.1, hlad.1.2⟩
            have hcth : contrLen' ((bd, y) : ℕ × ℕ) T (unitsLen ((bd, y) : ℕ × ℕ) T) A
                = contrLen ((bd, y) : ℕ × ℕ) T (unitsLen ((bd, y) : ℕ × ℕ) T) A := by
              have hx := hHC hlad2.1 ((bd, y) : ℕ × ℕ) (A ++ T) rfl hlad2.2
              rw [e1, e2] at hx
              exact hx
            by_cases hnc : contrLen ((bd, y) : ℕ × ℕ) T
                (unitsLen ((bd, y) : ℕ × ℕ) T) A = none
            · obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_lad2 (p := ((bd, y) : ℕ × ℕ))
                hAdeep hTh hlad hnc
                (fun k hk => Hp ((bd, y) : ℕ × ℕ) A T bd hb hc hd rfl hAdeep hThd hcth
                  hnc k hk)
                hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
              rw [← hBeq] at k3
              exact ⟨m, n', k1, k2, k3⟩
            · obtain ⟨rest2, Bq, hcc⟩ : ∃ rest2 Bq, contrLen ((bd, y) : ℕ × ℕ) T
                  (unitsLen ((bd, y) : ℕ × ℕ) T) A = some (rest2, Bq) := by
                rcases hx : contrLen ((bd, y) : ℕ × ℕ) T
                    (unitsLen ((bd, y) : ℕ × ℕ) T) A with _ | ⟨r2, bq⟩
                · exact absurd hx hnc
                · exact ⟨r2, bq, rfl⟩
              obtain ⟨qq, U, pre, hU, hTeq, hq2, hq1, hpre, hpd, hrd, hBqh,
                hrne, hrh1, hrh2⟩ := contrLen_shape hcc
              exact reindexD_pos_fire Hs N ih hB hb hc hd hbd rfl hlev hAP hAC hLB
                hAdeep hlad hpar hU hTeq hq2 hq1 hpre hpd hrd hBqh hrne hrh1 hrh2 n hn
          · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
              cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
              | false => rfl
              | true => exact absurd hx hlad
            obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_nolad (p := ((bd, y) : ℕ × ℕ))
              hAdeep hTh hnl hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
            rw [← hBeq] at k3
            exact ⟨m, n', k1, k2, k3⟩
      · -- 場合 (b): 親がない（弱めた contrOK が要る）
        exact Hn ((bd, y) : ℕ × ℕ) A T bd d plev first force hb hc hd hbd rfl h2
          hAdeep hThd hlev hAP hAC hLB hHP hFC hDP hHC hpar n hn

/-- 段が正の場合の入口（縮約つき）。 -/
theorem reindexD_pos_of3 (Hc : CtrRes) (Hp : CtrPres2) (Hs : RDposStop)
    (Hn : RDnopar) (Hd : RDnode) : ReindexD_pos := by
  intro A hA hL hlev n hn
  have h := reindexD_pos_block3 Hp Hs Hn Hd A.length A (Nat.le_refl _) 0 0 0 true false
    (blockok_ST_PS hA) (colOK_ST_PS hA) (descOK_ST_PS hA) (Nat.le_refl 0)
    (by omega) hlev (argPatOK_ST_PS hA) (Hc hA) (adjLev_ST_PS hA)
    (fun _ => Or.inr ⟨rfl, rfl, rfl⟩) fOK_false (fun _ _ => Or.inl rfl)
    (fun _ => ctrHeadOK_root (blockok_ST_PS hA) (colOK_ST_PS hA)) n hn
  obtain ⟨m, n', h1, h2, h3⟩ := h
  exact ⟨m, n', h1, h2, by rw [conC, conC]; exact h3⟩

/-- **到達点（縮約つき）**: `ReindexD` は
  * `CtrRes`（BMS 標準形は `argCtrOK`）
  * `CtrPres2`（縮約が発火しない状態は展開で保たれる）
  * `RDzeroStop2` / `RDposStop`（縮約が発火して親が縮約の内側にある場合）
  * `RDnopar` / `RDnode`（段 > 0 の降下が止まる 2 つ）
だけに絞られた。梯子つきの縮約（旧 `RDzeroRes2` / `RDlad2`）は
`CtrPres2` と 2 つの `Stop` に置き換わった。 -/
theorem reindexD_holds_of_res5 (Hc : CtrRes) (Hp : CtrPres2) (H0 : RDzeroStop2)
    (Hs : RDposStop) (Hn : RDnopar) (Hd : RDnode) : ReindexD := by
  intro A hA hL n hn
  by_cases hz : entry A 1 (A.length - 1) = 0
  · exact reindexD_zero4 Hc Hp H0 hA hz n hn
  · exact reindexD_pos_of3 Hc Hp Hs Hn Hd hA hL (by omega) n hn

/-- 同じ形で主定理まで。 -/
theorem ST_D_conC_holds_of_res5 (Hc : CtrRes) (Hp : CtrPres2) (H0 : RDzeroStop2)
    (Hs : RDposStop) (Hn : RDnopar) (Hd : RDnode)
    {M : PairSeq} (hM : ST_PS M) : ST_D (conC M) :=
  ST_D_conC (reindexD_holds_of_res5 Hc Hp H0 Hs Hn Hd) hM

theorem entry_zero1 {M : PairSeq} : entry M 1 0 = (M.headI).2 := by
  rw [entry, if_neg (by omega)]
  cases M with
  | nil => rfl
  | cons a t => rfl

/-- **`descOK` は「同じ深さの鎖では段が増えない」**: ブロックの中で頭と同じ深さの列は
どれも頭より段が高くない。 -/
theorem descOK_level_le_head : ∀ (N a : ℕ) (L : PairSeq), L.length ≤ N →
    blockok a L → descOK L → ∀ j, j < L.length → entry L 0 j = a →
      entry L 1 j ≤ (L.headI).2 := by
  intro N
  induction N with
  | zero =>
    intro a L hL _ _ j hj _
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp at hj
  | succ N ih =>
    intro a L hL hb hd j hj hj0
    match L with
    | [] => simp at hj
    | c :: r =>
      have hc1 : c.1 = a := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, c = (a, y) := ⟨c.2, by rw [← hc1]⟩
      have hLr : r.length + 1 ≤ N + 1 := by simpa using hL
      cases j with
      | zero => rw [entry_zero1]
      | succ j' =>
        obtain ⟨hdh, hdA, hdS⟩ := descOK_cons.1 hd
        obtain ⟨Ar, Sb, hAr, hSb⟩ : ∃ Ar Sb,
            Ar = (r.takeWhile fun q => ((a, y) : ℕ × ℕ).1 < q.1) ∧
            Sb = (r.dropWhile fun q => ((a, y) : ℕ × ℕ).1 < q.1) := ⟨_, _, rfl, rfl⟩
        rw [← hSb] at hdh hdS
        rw [← hAr] at hdA
        have hsplit : Ar ++ Sb = r := by
          rw [hAr, hSb]; exact List.takeWhile_append_dropWhile
        have hlens : Ar.length + Sb.length = r.length := by
          rw [← List.length_append, hsplit]
        have hjr : j' < r.length := by simp only [List.length_cons] at hj; omega
        rw [entry_cons_succ] at hj0 ⊢
        rcases Nat.lt_or_ge j' Ar.length with hlt | hge
        · exfalso
          have hmem : Ar.getD j' (0, 0) ∈ Ar := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
            simpa using List.getElem_mem hlt
          have hdeep : ((a, y) : ℕ × ℕ).1 < (Ar.getD j' (0, 0)).1 := by
            have hmem' : Ar.getD j' (0, 0)
                ∈ (r.takeWhile fun q => ((a, y) : ℕ × ℕ).1 < q.1) := by
              rw [← hAr]; exact hmem
            have hx := List.mem_takeWhile_imp hmem'
            simpa using hx
          have he : entry r 0 j' = (Ar.getD j' (0, 0)).1 := by
            conv_lhs => rw [← hsplit]
            rw [entry, if_pos rfl, getD_append_left hlt]
          rw [he] at hj0
          simp only [] at hdeep
          omega
        · obtain ⟨j'', rfl⟩ : ∃ j'', j' = Ar.length + j'' := ⟨j' - Ar.length, by omega⟩
          have hlenS : j'' < Sb.length := by omega
          have hSne : Sb ≠ [] := by
            intro he; rw [he] at hlenS; simp at hlenS
          have he0 : entry r 0 (Ar.length + j'') = entry Sb 0 j'' := by
            conv_lhs => rw [← hsplit]
            exact entry_append_right Ar Sb 0 j''
          have he1 : entry r 1 (Ar.length + j'') = entry Sb 1 j'' := by
            conv_lhs => rw [← hsplit]
            exact entry_append_right Ar Sb 1 j''
          rw [he0] at hj0
          rw [he1]
          have hbS : blockok a Sb := by rw [hSb]; exact blockok_tail hb
          have hkey := ih a Sb (by omega) hbS hdS j'' hlenS hj0
          exact le_trans hkey (hdh hSne)

/-- `RDposStop` に「末尾列に行 1 の親がある」を足した版（`reindexD_pos_fire` の枝では
実際に親がある）。**この形なら仮定が矛盾するので定理として証明できる。** -/
def RDposStop2 : Prop :=
  ∀ (p q : ℕ × ℕ) (A U pre rest2 : PairSeq) (bd d plev : ℕ) (first force : Bool),
    blockok bd (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    colOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    descOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    bd ≤ d → p.1 = bd → (∀ x ∈ A, p.1 < x.1) →
    Units p U → q.2 + 1 = p.2 → q.1 = p.1 → pre = contrPre p U A →
    (∀ x ∈ pre, p.1 < x.1) → (∀ x ∈ rest2, p.1 < x.1) →
    rest2 ≠ [] → (rest2.headI).1 = p.1 + 1 → (rest2.headI).2 < p.2 →
    0 < entry (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 1
      ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1) →
    argPatOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    argCtrOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    adjLev (p :: (A ++ (U ++ q :: (pre ++ rest2)))) →
    ladOf p.2 d plev first force = true →
    hasParent (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 1
      ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1) →
    ¬ ((p :: (A ++ (U ++ q :: pre))).length
        ≤ parent (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 1
            ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1)) →
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ (U ++ q :: (pre ++ rest2)))) d plev first force)⟦m⟧
        = convC ((p :: (A ++ (U ++ q :: (pre ++ rest2))))⟦n'⟧) d plev first force

/-- **段 > 0 の「縮約の内側に親がある」場合は起こらない**。
末尾列の段が正なら行 1 の親は `q` より後ろの `rest2` の中に入る:
`q` は深さ `bd` なのでブロックの中に行 0 の親を持たず、`pre` の列は深さが `bd+1`
以上なので `le0` の谷の条件で潰れる。`q` 自身が親だとすると `descOK`
（同じ深さの鎖では段が増えない）と `rest2` の頭の段 < `p.2` から矛盾する。 -/
theorem rdPosStop2 : RDposStop2 := by
  intro p q A U pre rest2 bd d plev first force hb hc hd hbd hp1 hAdeep hU hq2 hq1 hpre
    hpd hrd hrne hrh1 hrh2 hlev hAP hAC hLB hlad hpar hge n hn
  exfalso
  obtain ⟨B, hBdef⟩ : ∃ B, B = p :: (A ++ (U ++ q :: (pre ++ rest2))) := ⟨_, rfl⟩
  rw [← hBdef] at hb hc hd hlev hpar hge
  obtain ⟨G0, hG0⟩ : ∃ G0, G0 = p :: (A ++ U) := ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2, G2 = p :: (A ++ (U ++ q :: pre)) := ⟨_, rfl⟩
  rw [← hG2] at hge
  have hB0 : B = G0 ++ (q :: (pre ++ rest2)) := by
    rw [hBdef, hG0]; simp [List.append_assoc]
  have hB2 : B = G2 ++ rest2 := by rw [hBdef, hG2]; simp [List.append_assoc]
  have hlen02 : G2.length = G0.length + 1 + pre.length := by
    rw [hG0, hG2]; simp only [List.length_cons, List.length_append]; omega
  have hR1 : 1 ≤ rest2.length := List.length_pos_of_ne_nil hrne
  have hBlen : B.length = G2.length + rest2.length := by rw [hB2]; simp
  have hG0len : 1 ≤ G0.length := by rw [hG0]; simp
  have hprene : pre ≠ [] := by rw [hpre]; simp [contrPre]
  have hpreh : (pre.headI).1 = p.1 + 1 := by rw [hpre]; simp [contrPre, shift1]
  -- 添字を変数に固定する
  obtain ⟨x, hx⟩ : ∃ x, x = B.length - 1 := ⟨_, rfl⟩
  rw [← hx] at hpar hge hlev
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 = parent B 1 x := ⟨_, rfl⟩
  rw [← hj0] at hge
  have hnr1 : nextrel1 B j0 x := by
    rw [hj0]
    have h := parent_nextR hpar
    unfold nextR at h; rw [if_neg (by simp)] at h; exact h
  have hxlt : x < B.length := hnr1.2.1
  have hxval : x = G2.length + (rest2.length - 1) := by omega
  have hj0lt : j0 < G2.length := by omega
  -- 行 1 の親は `q` の位置より前には来ない
  have hlowG0 : ∀ c ∈ G0, bd ≤ c.1 := by
    intro c hcm; exact hb.2.1 c (by rw [hB0]; exact List.mem_append_left _ hcm)
  have hle0B : le0 (G0 ++ (q :: (pre ++ rest2))) j0 x := by
    rw [← hB0]; exact hnr1.2.2.2.2.1
  have hgeq : G0.length ≤ j0 :=
    le0_ge_of_append (by simp) hlowG0 (by simp only [List.headI]; omega) hle0B (by omega)
  -- `rest2` の頭の深さ
  have hheadR : entry B 0 G2.length = bd + 1 := by
    rw [hB2, show G2.length = G2.length + 0 by omega, entry_append_right, entry_zero0, hrh1]
    omega
  -- `j0` の深さは `bd`
  have hlt1 : entry B 0 j0 < bd + 1 := by
    rw [← hheadR]
    exact le0_interval_gt hnr1.2.2.2.2.1.2.2 G2.length ⟨hj0lt, by omega⟩
  have hge1 : bd ≤ entry B 0 j0 := by
    have hj0len : j0 < B.length := hnr1.1
    have hmem : B.getD j0 (0, 0) ∈ B := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj0len]
      simpa using List.getElem_mem hj0len
    rw [entry, if_pos rfl]; exact hb.2.1 _ hmem
  have hd0 : entry B 0 j0 = bd := by omega
  -- したがって `j0` は `q` の位置
  have hjq : j0 = G0.length := by
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, j0 = G0.length + 1 + i := ⟨j0 - G0.length - 1, by omega⟩
    have hiP : i < pre.length := by omega
    have hent : entry B 0 j0 = (pre.getD i (0, 0)).1 := by
      rw [hB0, hi, show G0.length + 1 + i = G0.length + (i + 1) by omega,
        entry_append_right, entry_cons_succ, entry, if_pos rfl, getD_append_left hiP]
    have hmemP : pre.getD i (0, 0) ∈ pre := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiP]
      simpa using List.getElem_mem hiP
    have hdp := hpd _ hmemP
    omega
  have hent1q : entry B 1 j0 = q.2 := by
    rw [hjq, hB0, show G0.length = G0.length + 0 by omega, entry_append_right, entry_zero1]
    simp
  have hlevx : q.2 < entry B 1 x := by
    have := hnr1.2.2.2.1
    omega
  -- 鎖の最初の一歩 `y` は深さ `bd + 1`
  have hjx : j0 < x := hnr1.2.2.1
  obtain ⟨y, hy1, hy2⟩ : ∃ y, nextrel0 B j0 y ∧ Relation.ReflTransGen (nextrel0 B) y x := by
    rcases Relation.ReflTransGen.cases_head hnr1.2.2.2.2.1.2.2 with h | ⟨y, hy1, hy2⟩
    · exact absurd h (by omega)
    · exact ⟨y, hy1, hy2⟩
  have hentp : entry B 0 (G0.length + 1) = bd + 1 := by
    rw [hB0, show G0.length + 1 = G0.length + (0 + 1) by omega, entry_append_right,
      entry_cons_succ, entry_zero0, headI_append_left hprene, hpreh]
    omega
  have hylt : y ≤ x := nextrel0_rtrancl_index_le hy2
  have hydep : entry B 0 y = bd + 1 := by
    have h1 : entry B 0 j0 < entry B 0 y := hy1.2.2.2.1
    have h2 : j0 < y := hy1.2.2.1
    rcases Nat.lt_or_ge (G0.length + 1) y with hcase | hcase
    · have hx2 := hy1.2.2.2.2 (G0.length + 1) ⟨by omega, hcase⟩
      omega
    · have hye : y = G0.length + 1 := by omega
      rw [hye]; exact hentp
  -- `y` は `rest2` の中
  have hyge : G2.length ≤ y := by
    by_contra hyl
    have hkey : entry B 0 y < bd + 1 := by
      rw [← hheadR]
      exact le0_interval_gt hy2 G2.length ⟨by omega, by omega⟩
    omega
  have hle0y : le0 B y x := ⟨by omega, hxlt, hy2⟩
  have hmin := hnr1.2.2.2.2.2 y ⟨by omega, hle0y⟩
  -- `descOK` で `y` の段は `rest2` の頭以下
  have hThd : (U ++ q :: (pre ++ rest2)) = []
      ∨ ¬ (p.1 < ((U ++ q :: (pre ++ rest2)).headI).1) := by
    right
    by_cases hUe : U = []
    · rw [hUe]; simp only [List.nil_append, List.headI]; omega
    · rw [headI_append_left hUe]
      rcases hU.head_eq with h | h
      · exact absurd h hUe
      · rw [h]; omega
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := (U ++ q :: (pre ++ rest2))) (dd := p.1)
    hAdeep hThd
  have hdT : descOK (U ++ q :: (pre ++ rest2)) := by
    have hxx := (descOK_cons.1 (by rw [← hBdef]; exact hd)).2.2
    rw [e2] at hxx; exact hxx
  have hqL : (q :: (pre ++ rest2)) = [] ∨ ¬ (p.1 < ((q :: (pre ++ rest2)).headI).1) := by
    right; simp only [List.headI]; omega
  have hdQ : descOK (q :: (pre ++ rest2)) :=
    descOK_units p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU) hdT
  have hTdeep : ∀ z ∈ (pre ++ rest2), q.1 < z.1 := by
    intro z hz
    rw [hq1]
    rcases List.mem_append.1 hz with h | h
    · exact hpd z h
    · exact hrd z h
  obtain ⟨f1, f2⟩ := split_append (X := (pre ++ rest2)) (Y := ([] : PairSeq)) (dd := q.1)
    hTdeep (Or.inl rfl)
  simp only [List.append_nil] at f1
  have hdPR : descOK (pre ++ rest2) := by
    have hxx := (descOK_cons.1 hdQ).2.1
    rw [f1] at hxx; exact hxx
  have hrestL : rest2 = [] ∨ ¬ (p.1 + 1 < (rest2.headI).1) := Or.inr (by rw [hrh1]; omega)
  have hpreall : ∀ c ∈ pre, p.1 + 1 ≤ c.1 := fun c hcc => by have := hpd c hcc; omega
  have hpreh' : pre = [] ∨ (pre.headI).1 ≤ p.1 + 1 := Or.inr (by rw [hpreh])
  have hdR : descOK rest2 :=
    descOK_units (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hdPR
  have hbR : blockok (bd + 1) rest2 := by
    refine ⟨fun _ => by rw [hrh1]; omega, fun cc hcc => by have := hrd cc hcc; omega, ?_⟩
    exact (steps1_append.1 (by rw [← hB2]; exact hb.2.2)).2.1
  have hyR : y - G2.length < rest2.length := by omega
  have hsplitR : ∀ i : ℕ, entry B i (G2.length + (y - G2.length))
      = entry rest2 i (y - G2.length) := by
    intro i; rw [hB2]; exact entry_append_right G2 rest2 i (y - G2.length)
  have hyeq : G2.length + (y - G2.length) = y := by omega
  have hentR0 : entry rest2 0 (y - G2.length) = bd + 1 := by
    rw [← hsplitR 0, hyeq]; exact hydep
  have hentR1 : entry rest2 1 (y - G2.length) = entry B 1 y := by
    rw [← hsplitR 1, hyeq]
  have hkey := descOK_level_le_head rest2.length (bd + 1) rest2 (Nat.le_refl _) hbR hdR
    (y - G2.length) hyR hentR0
  rw [hentR1] at hkey
  omega

/-- **縮約が発火する段（段 > 0・残余なし）**。段 0 と同じく `Bq ≠ []` なら `q` の兄弟へ、
`Bq = []` なら `rest2` へ降りる。 -/
theorem reindexD_pos_fire2 (N : ℕ)
    (ih : ∀ (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → 2 ≤ B.length →
      0 < entry B 1 (B.length - 1) →
      argPatOK B → argCtrOK B → adjLev B →
      hpOK B d plev first force → fOK B d plev force →
      dpOK bd d plev first → hcOK B plev first →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force)
    {p q : ℕ × ℕ} {A T U pre rest2 Bq : PairSeq} {bd d plev : ℕ} {first force : Bool}
    (hlenN : (p :: (A ++ T)).length ≤ N + 1)
    (hb : blockok bd (p :: (A ++ T))) (hc : colOK (p :: (A ++ T)))
    (hd : descOK (p :: (A ++ T))) (hbd : bd ≤ d)
    (hp1 : p.1 = bd)
    (hlev : 0 < entry (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1))
    (hAP : argPatOK (p :: (A ++ T))) (hAC : argCtrOK (p :: (A ++ T)))
    (hLB : adjLev (p :: (A ++ T)))
    (hAdeep : ∀ x ∈ A, p.1 < x.1)
    (hlad : ladOf p.2 d plev first force = true)
    (hpar : hasParent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1))
    (hU : Units p U) (hTeq : T = U ++ q :: ((pre ++ rest2) ++ Bq))
    (hq2 : q.2 + 1 = p.2) (hq1 : q.1 = p.1) (hpre : pre = contrPre p U A)
    (hpd : ∀ x ∈ pre, p.1 < x.1) (hrd : ∀ x ∈ rest2, p.1 < x.1)
    (hBqh : Bq = [] ∨ ¬ (p.1 < (Bq.headI).1))
    (hrne : rest2 ≠ []) (hrh1 : (rest2.headI).1 = p.1 + 1) (hrh2 : (rest2.headI).2 < p.2) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ T)) d plev first force)⟦m⟧
        = convC ((p :: (A ++ T))⟦n'⟧) d plev first force := by
  intro n hn
  have hnr1 : nextrel1 (p :: (A ++ T))
      (parent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1))
      ((p :: (A ++ T)).length - 1) := by
    have h := parent_nextR hpar
    unfold nextR at h; rw [if_neg (by simp)] at h; exact h
  have hjlt : parent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1)
      < (p :: (A ++ T)).length - 1 := hnr1.2.2.1
  have hTdeep : ∀ x ∈ (pre ++ rest2), p.1 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hpd x h
    · exact hrd x h
  have hpreh : (pre.headI).1 = p.1 + 1 := by rw [hpre]; simp [contrPre, shift1]
  have hThd : T = [] ∨ ¬ (p.1 < (T.headI).1) := by
    right
    rw [hTeq]
    by_cases hUe : U = []
    · rw [hUe]; simp only [List.nil_append, List.headI]; omega
    · rw [headI_append_left hUe]
      rcases hU.head_eq with h | h
      · exact absurd h hUe
      · rw [h]; omega
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := p.1) hAdeep hThd
  have hdT : descOK T := by
    have hx := (descOK_cons.1 hd).2.2
    rw [e2] at hx; exact hx
  have hAPt : argPatOK T := by
    have hx := (argPatOK_cons.1 hAP).2.2
    rw [e2] at hx; exact hx
  have hACt : argCtrOK T := by
    have hx := (argCtrOK_cons.1 hAC).2.2
    rw [e2] at hx; exact hx
  have hqL : (q :: ((pre ++ rest2) ++ Bq)) = []
      ∨ ¬ (p.1 < ((q :: ((pre ++ rest2) ++ Bq)).headI).1) := by
    right; simp only [List.headI]; omega
  have hdQ : descOK (q :: ((pre ++ rest2) ++ Bq)) :=
    descOK_units p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hdT)
  have hAPq : argPatOK (q :: ((pre ++ rest2) ++ Bq)) :=
    argPatOK_drop p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hAPt)
  have hACq : argCtrOK (q :: ((pre ++ rest2) ++ Bq)) :=
    argCtrOK_drop p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hACt)
  obtain ⟨f1, f2⟩ := split_append (X := (pre ++ rest2)) (Y := Bq) (dd := q.1)
    (by rw [hq1]; exact hTdeep) (by rw [hq1]; exact hBqh)
  have hdBq : descOK Bq := by
    have hx := (descOK_cons.1 hdQ).2.2
    rw [f2] at hx; exact hx
  have hAPBq : argPatOK Bq := by
    have hx := (argPatOK_cons.1 hAPq).2.2
    rw [f2] at hx; exact hx
  have hACBq : argCtrOK Bq := by
    have hx := (argCtrOK_cons.1 hACq).2.2
    rw [f2] at hx; exact hx
  have hdPR : descOK (pre ++ rest2) := by
    have hx := (descOK_cons.1 hdQ).2.1
    rw [f1] at hx; exact hx
  have hAPPR : argPatOK (pre ++ rest2) := by
    have hx := (argPatOK_cons.1 hAPq).2.1
    rw [f1] at hx; exact hx
  have hACPR : argCtrOK (pre ++ rest2) := by
    have hx := (argCtrOK_cons.1 hACq).2.1
    rw [f1] at hx; exact hx
  have hrestL : rest2 = [] ∨ ¬ (p.1 + 1 < (rest2.headI).1) := Or.inr (by rw [hrh1]; omega)
  have hpreall : ∀ c ∈ pre, p.1 + 1 ≤ c.1 := fun c hcc => by have := hpd c hcc; omega
  have hpreh' : pre = [] ∨ (pre.headI).1 ≤ p.1 + 1 := Or.inr (by rw [hpreh])
  have hdR : descOK rest2 :=
    descOK_units (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hdPR
  have hAPR : argPatOK rest2 :=
    argPatOK_drop (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hAPPR
  have hACR : argCtrOK rest2 :=
    argCtrOK_drop (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hACPR
  have hmemBq : ∀ c ∈ Bq, c ∈ (p :: (A ++ T)) := by
    intro c hcc
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    rw [hTeq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hcc))
  have hmemR : ∀ c ∈ rest2, c ∈ (p :: (A ++ T)) := by
    intro c hcc
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    rw [hTeq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_right _ hcc)))
  have hcBq : colOK Bq := fun cc hcc => hc cc (hmemBq cc hcc)
  have hcR : colOK rest2 := fun cc hcc => hc cc (hmemR cc hcc)
  by_cases hBqe : Bq = []
  · -- `Bq = []`: `rest2` へ降りるか、残余
    obtain ⟨G2, hG2⟩ : ∃ G2 : PairSeq, G2 = p :: (A ++ (U ++ q :: pre)) := ⟨_, rfl⟩
    have hBeq2 : (p :: (A ++ T)) = G2 ++ rest2 := by
      rw [hG2, hTeq, hBqe]; simp [List.append_assoc]
    have hBeq3 : (p :: (A ++ T)) = p :: (A ++ (U ++ q :: (pre ++ rest2))) := by
      rw [hTeq, hBqe]; simp [List.append_assoc]
    have hG2len : 1 ≤ G2.length := by rw [hG2]; simp
    have hR1 : 1 ≤ rest2.length := List.length_pos_of_ne_nil hrne
    have hlenB2 : (p :: (A ++ T)).length = G2.length + rest2.length := by
      rw [hBeq2]; simp
    have hlast : (p :: (A ++ T)).getLastD (0, 0) = rest2.getLastD (0, 0) := by
      rw [hBeq2]; exact getLastD_append_right hrne _
    have hlevR : 0 < entry rest2 1 (rest2.length - 1) := by
      rw [entry_last, ← hlast, ← entry_last]; exact hlev
    have hzR : ¬ (entry rest2 0 (rest2.length - 1) = 0 ∧ entry rest2 1 (rest2.length - 1) = 0) := by
      rintro ⟨-, h1⟩
      omega
    have hbR : blockok (p.1 + 1) rest2 := by
      refine ⟨fun _ => hrh1, fun cc hcc => by have := hrd cc hcc; omega, ?_⟩
      exact (steps1_append.1 (by rw [← hBeq2]; exact hb.2.2)).2.1
    have hLR : adjLev rest2 :=
      adjLev_infix ⟨G2, [], by rw [List.append_nil]; exact hBeq2.symm⟩ hLB
    by_cases hge2 : G2.length ≤ parent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1)
    · have hiR : idx1 rest2 (rest2.length - 1) = 1 := by rw [idx1, if_pos hlevR]
      have hR2 : 2 ≤ rest2.length := by omega
      have hidx : (p :: (A ++ T)).length - 1 = G2.length + (rest2.length - 1) := by omega
      have hpB : hasParent (G2 ++ rest2) (idx1 rest2 (rest2.length - 1))
          (G2.length + (rest2.length - 1)) := by
        rw [hiR, ← hidx, ← hBeq2]; exact hpar
      have hgeB : G2.length ≤ parent (G2 ++ rest2) (idx1 rest2 (rest2.length - 1))
          (G2.length + (rest2.length - 1)) := by
        rw [hiR, ← hidx, ← hBeq2]; exact hge2
      rw [hG2] at hpB hgeB
      have hIH := ih rest2 (by omega) (p.1 + 1) (d + 1) p.2 false false hbR hcR hdR
        (by omega) hR2 hlevR hAPR hACR hLR hpOK_false fOK_false dpOK_false hcOK_false
      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_rest_contr (Arg := A) (T := rest2)
        hAdeep hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 hlad hbR hcR hdR (by omega) hzR
        hpB hgeB hIH n hn
      refine ⟨m, n', k1, k2, ?_⟩
      rw [← hG2, ← hBeq2] at k3
      exact k3
    · rw [hBeq3]
      refine rdPosStop2 p q A U pre rest2 bd d plev first force ?_ ?_ ?_ hbd hp1 hAdeep hU
        hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 ?_ ?_ ?_ ?_ hlad ?_ ?_ n hn
      · rw [← hBeq3]; exact hb
      · rw [← hBeq3]; exact hc
      · rw [← hBeq3]; exact hd
      · rw [← hBeq3]; exact hlev
      · rw [← hBeq3]; exact hAP
      · rw [← hBeq3]; exact hAC
      · rw [← hBeq3]; exact hLB
      · rw [← hBeq3]; exact hpar
      · rw [← hBeq3, ← hG2]; exact hge2
  · -- `Bq ≠ []`: `q` の兄弟へ降りる
    have hBqh' : ¬ (p.1 < (Bq.headI).1) := by
      rcases hBqh with h | h
      · exact absurd h hBqe
      · exact h
    obtain ⟨G1, hG1⟩ : ∃ G1 : PairSeq, G1 = p :: (A ++ (U ++ q :: (pre ++ rest2))) := ⟨_, rfl⟩
    have hBeq1 : (p :: (A ++ T)) = G1 ++ Bq := by
      rw [hG1, hTeq]; simp [List.append_assoc]
    have hG1len : 1 ≤ G1.length := by rw [hG1]; simp
    have hBq1 : 1 ≤ Bq.length := List.length_pos_of_ne_nil hBqe
    have hlenB1 : (p :: (A ++ T)).length = G1.length + Bq.length := by
      rw [hBeq1]; simp
    have hlast : (p :: (A ++ T)).getLastD (0, 0) = Bq.getLastD (0, 0) := by
      rw [hBeq1]; exact getLastD_append_right hBqe _
    have hlevBq : 0 < entry Bq 1 (Bq.length - 1) := by
      rw [entry_last, ← hlast, ← entry_last]; exact hlev
    have hzBq : ¬ (entry Bq 0 (Bq.length - 1) = 0 ∧ entry Bq 1 (Bq.length - 1) = 0) := by
      rintro ⟨-, h1⟩
      omega
    have hbBq : blockok bd Bq := by
      refine ⟨?_, fun cc hcc => hb.2.1 cc (hmemBq cc hcc), ?_⟩
      · intro hne
        have h1 : bd ≤ (Bq.headI).1 := hb.2.1 _ (hmemBq _ (headI_mem hne))
        omega
      · exact (steps1_append.1 (by rw [← hBeq1]; exact hb.2.2)).2.1
    have hLBq : adjLev Bq :=
      adjLev_infix ⟨G1, [], by rw [List.append_nil]; exact hBeq1.symm⟩ hLB
    have hlowG1 : ∀ c ∈ G1, bd ≤ c.1 := by
      intro c hcm
      exact hb.2.1 c (by rw [hBeq1]; exact List.mem_append_left _ hcm)
    have hidx : (p :: (A ++ T)).length - 1 = G1.length + (Bq.length - 1) := by omega
    have hle0 : le0 (G1 ++ Bq) (parent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1))
        (G1.length + (Bq.length - 1)) := by
      rw [← hidx, ← hBeq1]; exact hnr1.2.2.2.2.1
    have hgeG1 : G1.length ≤ parent (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) :=
      le0_ge_of_append hBqe hlowG1 (hbBq.1 hBqe) hle0 (by omega)
    have hBq2 : 2 ≤ Bq.length := by omega
    have hiBq : idx1 Bq (Bq.length - 1) = 1 := by rw [idx1, if_pos hlevBq]
    have hpB : hasParent (G1 ++ Bq) (idx1 Bq (Bq.length - 1))
        (G1.length + (Bq.length - 1)) := by
      rw [hiBq, ← hidx, ← hBeq1]; exact hpar
    have hgeB : G1.length ≤ parent (G1 ++ Bq) (idx1 Bq (Bq.length - 1))
        (G1.length + (Bq.length - 1)) := by
      rw [hiBq, ← hidx, ← hBeq1]; exact hgeG1
    rw [hG1] at hpB hgeB
    have hIH := ih Bq (by omega) bd d p.2 false false hbBq hcBq hdBq hbd hBq2 hlevBq hAPBq
      hACBq hLBq hpOK_false fOK_false dpOK_false hcOK_false
    obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_contr (Arg := A) (T := Bq)
      hAdeep hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 hBqh' hlad (by rw [hp1]; exact hbBq)
      hcBq hdBq (by omega) hzBq hpB hgeB hIH n hn
    refine ⟨m, n', k1, k2, ?_⟩
    rw [← hG1, ← hBeq1] at k3
    exact k3


/-- **段 > 0 の組み立て（縮約つき・Stop の残余なし）**。残りは
`CtrPres2` / `RDnopar` / `RDnode` の 3 つ。 -/
theorem reindexD_pos_block4 (Hp : CtrPres2) (Hn : RDnopar) (Hd : RDnode) :
    ∀ (N : ℕ) (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → 2 ≤ B.length →
      0 < entry B 1 (B.length - 1) →
      argPatOK B → argCtrOK B → adjLev B →
      hpOK B d plev first force → fOK B d plev force →
      dpOK bd d plev first → hcOK B plev first →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force := by
  intro N
  induction N with
  | zero =>
    intro B hB bd d plev first force _ _ _ _ h2 _ _ _ _ _ _ _ _ n hn
    exact absurd hB (by omega)
  | succ N ih =>
    intro B hB bd d plev first force hb hc hd hbd h2 hlev hAP hAC hLB hHP hFC hDP hHC n hn
    cases B with
    | nil => exact absurd h2 (by simp)
    | cons p r =>
      have hp1 : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp1]⟩
      obtain ⟨A, T, hAd, hTd⟩ :
          ∃ A T, A = (r.takeWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) ∧
                 T = (r.dropWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) := ⟨_, _, rfl, rfl⟩
      have hrAT : r = A ++ T := by
        rw [hAd, hTd]; exact (List.takeWhile_append_dropWhile).symm
      subst hrAT
      have hAdeep : ∀ x ∈ A, ((bd, y) : ℕ × ℕ).1 < x.1 := by
        intro x hx
        rw [hAd] at hx
        simpa using List.mem_takeWhile_imp hx
      have hThd : T = [] ∨ ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
        rw [hTd]; exact dropWhile_head_not _ _
      obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := ((bd, y) : ℕ × ℕ).1)
        hAdeep hThd
      -- 新しい不変量を割る
      obtain ⟨hAPh, hAPa, hAPt⟩ := argPatOK_cons.1 hAP
      rw [e1] at hAPh hAPa
      rw [e2] at hAPt
      obtain ⟨hACh, hACa, hACt⟩ := argCtrOK_cons.1 hAC
      rw [e1] at hACh hACa
      rw [e2] at hACt
      have hLA : adjLev A := by
        have hx := adjLev_infix (takeWhile_infix_cons ((bd, y) : ℕ × ℕ) (A ++ T)) hLB
        rw [e1] at hx; exact hx
      have hLT : adjLev T := by
        have hx := adjLev_infix (dropWhile_infix_cons ((bd, y) : ℕ × ℕ) (A ++ T)) hLB
        rw [e2] at hx; exact hx
      have hycol : ((bd, y) : ℕ × ℕ).2 ≤ ((bd, y) : ℕ × ℕ).1 := hc _ (by simp)
      have hfA : fOK A (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
          ((bd, y) : ℕ × ℕ).2 (first && (((bd, y) : ℕ × ℕ).2 == plev)) := by
        intro hft
        have hf1 : first = true := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.1
        have hpl : ((bd, y) : ℕ × ℕ).2 = plev := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.2
        rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
        · left
          intro a s hs
          have hkey := hh ((bd, y) : ℕ × ℕ) (A ++ T) rfl hpl (by rw [e1, hs]; simp)
          rw [e1, hs] at hkey
          simpa using hkey
        · right
          subst hd0; subst hpl0; subst hfc0
          have hy0 : y = 0 := by simpa using hpl
          subst hy0
          simp [ddOf, ladOf]
      have hbA : blockok (bd + 1) A := by rw [← e1]; exact blockok_arg hb
      have hbT : blockok bd T := by rw [← e2]; exact blockok_tail hb
      have hcA : colOK A := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_left A T))) hc
      have hcT : colOK T := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_right A T))) hc
      obtain ⟨hdh, hdA, hdT⟩ := descOK_cons.1 hd
      rw [e1] at hdA
      rw [e2] at hdh hdT
      have hlAT : A.length + T.length ≤ N := by
        simp only [List.length_cons, List.length_append] at hB
        omega
      have hlen : ((bd, y) :: (A ++ T)).length = A.length + T.length + 1 := by simp
      have hi1 : idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1) = 1 := by
        rw [idx1, if_pos hlev]
      by_cases hpar : hasParent ((bd, y) :: (A ++ T)) 1
          (((bd, y) :: (A ++ T)).length - 1)
      · have hnr1 : nextrel1 ((bd, y) :: (A ++ T))
            (parent ((bd, y) :: (A ++ T)) 1 (((bd, y) :: (A ++ T)).length - 1))
            (((bd, y) :: (A ++ T)).length - 1) := by
          have h := parent_nextR hpar
          unfold nextR at h; rw [if_neg (by omega)] at h; exact h
        by_cases hTe : T = []
        · -- 兄弟が空: ブロックは p :: A
          subst hTe
          have hAne : A ≠ [] := by
            intro he
            rw [he] at h2
            simp at h2
          have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
          have hlastA : ((bd, y) :: (A ++ [])).getLastD (0, 0) = A.getLastD (0, 0) := by
            rw [List.append_nil]; exact getLastD_cons_ne _ hAne _
          have hlevA : 0 < entry A 1 (A.length - 1) := by
            rw [entry_last, ← hlastA, ← entry_last]; exact hlev
          have hiA : idx1 A (A.length - 1) = 1 := by rw [idx1, if_pos hlevA]
          have hzA : ¬ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0) := by
            rintro ⟨-, h1⟩
            omega
          have hidx : ((bd, y) :: (A ++ [])).length - 1
              = ([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1) := by
            simp only [List.length_cons, List.length_nil, List.append_nil]
            omega
          have hBeq : ((bd, y) :: (A ++ [])) = [((bd, y) : ℕ × ℕ)] ++ A := by simp
          by_cases hj00 : parent ((bd, y) :: (A ++ []))
              1 (((bd, y) :: (A ++ [])).length - 1) = 0
          · -- 場合 (d): 親が節点（ずれたコピーの補題が要る）
            exact Hd ((bd, y) : ℕ × ℕ) A [] bd d plev first force hb hc hd hbd rfl h2
              hAdeep (Or.inl rfl) hlev hAP hAC hLB hHP hFC hDP hHC ⟨rfl, hj00⟩ n hn
          · -- 場合 (c): 引数ブロックへ降りる
            have hlenA : ((bd, y) :: (A ++ [])).length - 1 = A.length := by simp
            have hA2 : 2 ≤ A.length := by
              have hj0lt := hnr1.2.2.1
              have hj0ne : parent ((bd, y) :: (A ++ [])) 1
                  (((bd, y) :: (A ++ [])).length - 1) ≠ 0 := hj00
              omega
            have hpB : hasParent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
              rw [hiA, ← hidx, ← hBeq]; exact hpar
            have hgeB : ([((bd, y) : ℕ × ℕ)] : PairSeq).length
                ≤ parent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                    (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
              rw [hiA, ← hidx, ← hBeq]
              show 1 ≤ parent ((bd, y) :: (A ++ [])) 1 (((bd, y) :: (A ++ [])).length - 1)
              omega
            by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
            · have hIH := ih A (by omega) (bd + 1) (d + 2) ((bd, y) : ℕ × ℕ).2 true false
                hbA hcA hdA (by omega) hA2 hlevA hAPa hACa hLA
                (hpOK_of_headPatOK hAPh) fOK_false
                (fun _ he => absurd he (by omega)) (fun _ => hACh)
              obtain ⟨m, n', k1, k2, k3⟩ := reindexD_arg_lad (p := ((bd, y) : ℕ × ℕ))
                hAdeep hlad hbA hcA hdA (by omega) hzA hpB hgeB hIH n hn
              exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
            · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                | false => rfl
                | true => exact absurd hx hlad
              have hIH := ih A (by omega) (bd + 1)
                (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
                ((bd, y) : ℕ × ℕ).2 true (first && (((bd, y) : ℕ × ℕ).2 == plev))
                hbA hcA hdA
                (by have := le_ddOf ((bd, y) : ℕ × ℕ).2 d plev first force; omega)
                hA2 hlevA hAPa hACa hLA (hpOK_of_headPatOK hAPh) hfA
                (dpOK_arg (p := ((bd, y) : ℕ × ℕ)) rfl hbd hycol) (fun _ => hACh)
              obtain ⟨m, n', k1, k2, k3⟩ := reindexD_arg_nolad (p := ((bd, y) : ℕ × ℕ))
                hAdeep hnl hbA hcA hdA (by omega) hzA hpB hgeB hIH n hn
              exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
        · -- 兄弟が空でない: 床の補題で親は兄弟の中
          have hTne : T ≠ [] := hTe
          have hT1 : 1 ≤ T.length := List.length_pos_of_ne_nil hTne
          have hTh : ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
            rcases hThd with h | h
            · exact absurd h hTne
            · exact h
          have hBeq : ((bd, y) :: (A ++ T)) = (((bd, y) : ℕ × ℕ) :: A) ++ T := by simp
          have hidx : ((bd, y) :: (A ++ T)).length - 1
              = (((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1) := by
            simp only [List.length_cons, List.length_append]
            omega
          have hlastT : ((bd, y) :: (A ++ T)).getLastD (0, 0) = T.getLastD (0, 0) := by
            rw [hBeq]; exact getLastD_append_right hTne _
          have hlevT : 0 < entry T 1 (T.length - 1) := by
            rw [entry_last, ← hlastT, ← entry_last]; exact hlev
          have hiT : idx1 T (T.length - 1) = 1 := by rw [idx1, if_pos hlevT]
          have hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0) := by
            rintro ⟨-, h1⟩
            omega
          -- 床の補題
          have hlowG : ∀ c ∈ (((bd, y) : ℕ × ℕ) :: A), bd ≤ c.1 := by
            intro c hcm
            refine hb.2.1 c ?_
            rw [hBeq]
            exact List.mem_append_left _ hcm
          have hhead : (T.headI).1 = bd := hbT.1 hTne
          have hle0 : le0 ((((bd, y) : ℕ × ℕ) :: A) ++ T)
              (parent ((bd, y) :: (A ++ T)) 1 (((bd, y) :: (A ++ T)).length - 1))
              (((bd, y) :: (A ++ T)).length - 1) := by
            rw [← hBeq]; exact hnr1.2.2.2.2.1
          have hgeT : (((bd, y) : ℕ × ℕ) :: A).length
              ≤ parent ((bd, y) :: (A ++ T)) 1 (((bd, y) :: (A ++ T)).length - 1) :=
            le0_ge_of_append hTne hlowG hhead hle0 (by rw [hidx]; omega)
          have hj0lt := hnr1.2.2.1
          have hT2 : 2 ≤ T.length := by
            simp only [List.length_cons, List.length_append] at hj0lt hgeT
            omega
          have hpB : hasParent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
              ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
            rw [hiT, ← hidx, ← hBeq]; exact hpar
          have hgeB : (((bd, y) : ℕ × ℕ) :: A).length
              ≤ parent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                  ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
            rw [hiT, ← hidx, ← hBeq]; exact hgeT
          have hIH := ih T (by omega) bd d ((bd, y) : ℕ × ℕ).2 false false
            hbT hcT hdT hbd hT2 hlevT hAPt hACt hLT hpOK_false fOK_false
            dpOK_false hcOK_false
          by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
          · have hlad2 : first = true ∧ ((bd, y) : ℕ × ℕ).2 = plev + 1 := by
              unfold ladOf at hlad
              simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
                decide_eq_true_eq] at hlad
              exact ⟨hlad.1.1, hlad.1.2⟩
            have hcth : contrLen' ((bd, y) : ℕ × ℕ) T (unitsLen ((bd, y) : ℕ × ℕ) T) A
                = contrLen ((bd, y) : ℕ × ℕ) T (unitsLen ((bd, y) : ℕ × ℕ) T) A := by
              have hx := hHC hlad2.1 ((bd, y) : ℕ × ℕ) (A ++ T) rfl hlad2.2
              rw [e1, e2] at hx
              exact hx
            by_cases hnc : contrLen ((bd, y) : ℕ × ℕ) T
                (unitsLen ((bd, y) : ℕ × ℕ) T) A = none
            · obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_lad2 (p := ((bd, y) : ℕ × ℕ))
                hAdeep hTh hlad hnc
                (fun k hk => Hp ((bd, y) : ℕ × ℕ) A T bd hb hc hd rfl hAdeep hThd hcth
                  hnc k hk)
                hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
              rw [← hBeq] at k3
              exact ⟨m, n', k1, k2, k3⟩
            · obtain ⟨rest2, Bq, hcc⟩ : ∃ rest2 Bq, contrLen ((bd, y) : ℕ × ℕ) T
                  (unitsLen ((bd, y) : ℕ × ℕ) T) A = some (rest2, Bq) := by
                rcases hx : contrLen ((bd, y) : ℕ × ℕ) T
                    (unitsLen ((bd, y) : ℕ × ℕ) T) A with _ | ⟨r2, bq⟩
                · exact absurd hx hnc
                · exact ⟨r2, bq, rfl⟩
              obtain ⟨qq, U, pre, hU, hTeq, hq2, hq1, hpre, hpd, hrd, hBqh,
                hrne, hrh1, hrh2⟩ := contrLen_shape hcc
              exact reindexD_pos_fire2 N ih hB hb hc hd hbd rfl hlev hAP hAC hLB
                hAdeep hlad hpar hU hTeq hq2 hq1 hpre hpd hrd hBqh hrne hrh1 hrh2 n hn
          · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
              cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
              | false => rfl
              | true => exact absurd hx hlad
            obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_nolad (p := ((bd, y) : ℕ × ℕ))
              hAdeep hTh hnl hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
            rw [← hBeq] at k3
            exact ⟨m, n', k1, k2, k3⟩
      · -- 場合 (b): 親がない（弱めた contrOK が要る）
        exact Hn ((bd, y) : ℕ × ℕ) A T bd d plev first force hb hc hd hbd rfl h2
          hAdeep hThd hlev hAP hAC hLB hHP hFC hDP hHC hpar n hn

/-- 段が正の場合の入口（残余 3 つ）。 -/
theorem reindexD_pos_of4 (Hc : CtrRes) (Hp : CtrPres2) (Hn : RDnopar) (Hd : RDnode) :
    ReindexD_pos := by
  intro A hA hL hlev n hn
  have h := reindexD_pos_block4 Hp Hn Hd A.length A (Nat.le_refl _) 0 0 0 true false
    (blockok_ST_PS hA) (colOK_ST_PS hA) (descOK_ST_PS hA) (Nat.le_refl 0)
    (by omega) hlev (argPatOK_ST_PS hA) (Hc hA) (adjLev_ST_PS hA)
    (fun _ => Or.inr ⟨rfl, rfl, rfl⟩) fOK_false (fun _ _ => Or.inl rfl)
    (fun _ => ctrHeadOK_root (blockok_ST_PS hA) (colOK_ST_PS hA)) n hn
  obtain ⟨m, n', h1, h2, h3⟩ := h
  exact ⟨m, n', h1, h2, by rw [conC, conC]; exact h3⟩

/-- **到達点**: `ReindexD` は 5 つの残余
`CtrRes` / `CtrPres2` / `RDzeroStop2` / `RDnopar` / `RDnode` だけに絞られた。
段 > 0 側の「縮約の内側に親がある」場合は `rdPosStop2` で**消えた**。 -/
theorem reindexD_holds_of_res6 (Hc : CtrRes) (Hp : CtrPres2) (H0 : RDzeroStop2)
    (Hn : RDnopar) (Hd : RDnode) : ReindexD := by
  intro A hA hL n hn
  by_cases hz : entry A 1 (A.length - 1) = 0
  · exact reindexD_zero4 Hc Hp H0 hA hz n hn
  · exact reindexD_pos_of4 Hc Hp Hn Hd hA hL (by omega) n hn

/-- 同じ形で主定理まで。 -/
theorem ST_D_conC_holds_of_res6 (Hc : CtrRes) (Hp : CtrPres2) (H0 : RDzeroStop2)
    (Hn : RDnopar) (Hd : RDnode) {M : PairSeq} (hM : ST_PS M) : ST_D (conC M) :=
  ST_D_conC (reindexD_holds_of_res6 Hc Hp H0 Hn Hd) hM

/-- **段 0 の Stop（コピー regime）の形**。縮約が発火して `Bq = []`、
しかも末尾列の親が縮約の内側にあるなら、親はかならず `q` の位置で、
展開は `q` から末尾列の 1 つ手前までのコピーの並びになる。 -/
theorem zeroStop_shape {p q : ℕ × ℕ} {A U pre rest2 : PairSeq} {bd : ℕ}
    (hb : blockok bd (p :: (A ++ (U ++ q :: (pre ++ rest2)))))
    (hp1 : p.1 = bd) (hq1 : q.1 = p.1)
    (hpd : ∀ x ∈ pre, p.1 < x.1) (hrd : ∀ x ∈ rest2, p.1 < x.1)
    (hrne : rest2 ≠ []) (hrh1 : (rest2.headI).1 = p.1 + 1)
    (hlev : entry (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 1
      ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1) = 0)
    (hpar : hasParent (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 0
      ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1))
    (hge : ¬ ((p :: (A ++ (U ++ q :: pre))).length
        ≤ parent (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 0
            ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1))) :
    parent (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 0
          ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1) = (p :: (A ++ U)).length
      ∧ ∀ n : ℕ, (p :: (A ++ (U ++ q :: (pre ++ rest2))))⟦n⟧
          = (p :: (A ++ U))
            ++ (List.replicate n (q :: (pre ++ rest2.dropLast))).flatten := by
  obtain ⟨r0, lp, rfl⟩ : ∃ r0 lp, rest2 = r0 ++ [lp] :=
    ⟨rest2.dropLast, rest2.getLast hrne, (List.dropLast_append_getLast hrne).symm⟩
  simp only [List.dropLast_concat]
  obtain ⟨G0, hG0⟩ : ∃ G0, G0 = p :: (A ++ U) := ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2, G2 = p :: (A ++ (U ++ q :: pre)) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = p :: (A ++ (U ++ q :: (pre ++ (r0 ++ [lp])))) := ⟨_, rfl⟩
  rw [← hBdef] at hb hlev hpar hge
  rw [← hG2] at hge
  rw [← hBdef, ← hG0]
  have hB0 : B = G0 ++ (q :: (pre ++ (r0 ++ [lp]))) := by
    rw [hBdef, hG0]; simp [List.append_assoc]
  have hB2 : B = G2 ++ (r0 ++ [lp]) := by rw [hBdef, hG2]; simp [List.append_assoc]
  have hBsnoc : B = (G0 ++ (q :: (pre ++ r0))) ++ [lp] := by
    rw [hBdef, hG0]; simp [List.append_assoc]
  have hlen02 : G2.length = G0.length + 1 + pre.length := by
    rw [hG0, hG2]; simp only [List.length_cons, List.length_append]; omega
  have hBlen : B.length = G2.length + (r0.length + 1) := by rw [hB2]; simp
  have hG0len : 1 ≤ G0.length := by rw [hG0]; simp
  have hL2 : 1 < B.length := by omega
  obtain ⟨x, hx⟩ : ∃ x, x = B.length - 1 := ⟨_, rfl⟩
  rw [← hx] at hpar hge hlev
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 = parent B 0 x := ⟨_, rfl⟩
  rw [← hj0] at hge
  rw [← hx, ← hj0]
  have hnr0 : nextrel0 B j0 x := by
    rw [hj0]
    have h := parent_nextR hpar
    unfold nextR at h; rw [if_pos rfl] at h; exact h
  have hxlt : x < B.length := hnr0.2.1
  have hj0lt : j0 < G2.length := by omega
  have hlowG0 : ∀ c ∈ G0, bd ≤ c.1 := by
    intro c hcm; exact hb.2.1 c (by rw [hB0]; exact List.mem_append_left _ hcm)
  have hle0B : le0 (G0 ++ (q :: (pre ++ (r0 ++ [lp])))) j0 x := by
    rw [← hB0]
    exact ⟨hnr0.1, hnr0.2.1, Relation.ReflTransGen.single hnr0⟩
  have hgeq : G0.length ≤ j0 :=
    le0_ge_of_append (by simp) hlowG0 (by simp only [List.headI]; omega) hle0B (by omega)
  have hheadR : entry B 0 G2.length = bd + 1 := by
    rw [hB2, show G2.length = G2.length + 0 by omega, entry_append_right, entry_zero0]
    omega
  have hlt1 : entry B 0 j0 < bd + 1 := by
    rw [← hheadR]
    exact le0_interval_gt (Relation.ReflTransGen.single hnr0) G2.length ⟨hj0lt, by omega⟩
  have hge1 : bd ≤ entry B 0 j0 := by
    have hj0len : j0 < B.length := hnr0.1
    have hmem : B.getD j0 (0, 0) ∈ B := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj0len]
      simpa using List.getElem_mem hj0len
    rw [entry, if_pos rfl]; exact hb.2.1 _ hmem
  have hd0 : entry B 0 j0 = bd := by omega
  have hjq : j0 = G0.length := by
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, j0 = G0.length + 1 + i := ⟨j0 - G0.length - 1, by omega⟩
    have hiP : i < pre.length := by omega
    have hent : entry B 0 j0 = (pre.getD i (0, 0)).1 := by
      rw [hB0, hi, show G0.length + 1 + i = G0.length + (i + 1) by omega,
        entry_append_right, entry_cons_succ, entry, if_pos rfl, getD_append_left hiP]
    have hmemP : pre.getD i (0, 0) ∈ pre := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiP]
      simpa using List.getElem_mem hiP
    have hdp := hpd _ hmemP
    omega
  refine ⟨hjq, ?_⟩
  intro n
  have hnr0' : nextrel0 B (G0.length) (B.length - 1) := by rw [← hjq, ← hx]; exact hnr0
  have hrep := oper_repeat_at (M := B) G0.length n hL2 (by rw [← hx]; exact hlev) hnr0'
  have htake : B.take G0.length = G0 := by rw [hB0]; simp
  have hdl : B.dropLast.drop G0.length = q :: (pre ++ r0) := by
    rw [hBsnoc, List.dropLast_concat]
    simp
  rw [htake, hdl] at hrep
  exact hrep

/-! ## 4.19 `convC` の平行移動不変性

`shift1`（行 0 に +1）はブロックの相対構造を変えないので、`convC` の像も変わらない。
`RDzeroStop2`（コピー regime）と `RDnode`（ずれたコピー）の両方で使う。 -/

/-- `first = false` なら `plev` と `force` は像に効かない。 -/
theorem convC_first_false (M : PairSeq) (d plev plev' : ℕ) (force force' : Bool) :
    convC M d plev false force = convC M d plev' false force' := by
  cases M with
  | nil => simp
  | cons p r =>
    have hl : ∀ (pl : ℕ) (fo : Bool), ladOf p.2 d pl false fo = false := by
      intro pl fo; simp [ladOf]
    have hdd : ∀ (pl : ℕ) (fo : Bool),
        ddOf p.2 d pl false fo = (if 0 < p.2 ∧ d ≤ p.2 then p.2 + 1 else d) := by
      intro pl fo
      unfold ddOf
      rw [if_neg (by rw [hl pl fo]; simp)]
    rw [convC_cons_nolad p r d plev false force (hl plev force),
      convC_cons_nolad p r d plev' false force' (hl plev' force'), hdd plev force,
      hdd plev' force']
    simp

theorem shift1_append (X Y : PairSeq) : shift1 (X ++ Y) = shift1 X ++ shift1 Y := by
  simp [shift1]

theorem shift1_take (k : ℕ) (X : PairSeq) : (shift1 X).take k = shift1 (X.take k) := by
  simp [shift1]

theorem shift1_drop (k : ℕ) (X : PairSeq) : (shift1 X).drop k = shift1 (X.drop k) := by
  simp [shift1]

@[simp] theorem shift1_eq_nil_iff (X : PairSeq) : shift1 X = [] ↔ X = [] := by
  cases X with
  | nil => simp
  | cons c l => simp

theorem shift1_headI (X : PairSeq) (h : X ≠ []) :
    (shift1 X).headI = ((X.headI).1 + 1, (X.headI).2) := by
  cases X with
  | nil => exact absurd rfl h
  | cons c l => rfl

theorem shift1_inj : ∀ {X Y : PairSeq}, shift1 X = shift1 Y → X = Y := by
  intro X
  induction X with
  | nil =>
    intro Y h
    rw [eq_comm, ← shift1_eq_nil_iff, ← h]; rfl
  | cons c l ih =>
    intro Y h
    cases Y with
    | nil => simp at h
    | cons e m =>
      rw [shift1_cons, shift1_cons] at h
      simp only [List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have hce : c = e := Prod.ext (by omega) h2
      rw [hce, ih h3]

@[simp] theorem shift1_inj_iff (X Y : PairSeq) : shift1 X = shift1 Y ↔ X = Y :=
  ⟨shift1_inj, fun h => by rw [h]⟩

theorem unitsLen_shift1 : ∀ (n : ℕ) (p : ℕ × ℕ) (B : PairSeq), B.length ≤ n →
    unitsLen ((p.1 + 1, p.2) : ℕ × ℕ) (shift1 B) = unitsLen p B := by
  intro n
  induction n with
  | zero =>
    intro p B hB
    have : B = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [unitsLen]
  | succ n ih =>
    intro p B hB
    match B with
    | [] => simp [unitsLen]
    | c :: r =>
      by_cases h : c = p
      · rw [h]
        have hlen : (r.dropWhile fun x => p.1 < x.1).length ≤ n := by
          have := List.length_dropWhile_le (fun x : ℕ × ℕ => p.1 < x.1) r
          simp only [List.length_cons] at hB; omega
        rw [shift1_cons, unitsLen_cons_pos, unitsLen_cons_pos]
        simp only []
        rw [shift1_takeWhile p.1 r, shift1_dropWhile p.1 r, shift1_length, ih p _ hlen]
      · rw [shift1_cons, unitsLen_cons_neg (by
          intro hc
          simp only [Prod.mk.injEq] at hc
          exact h (Prod.ext (by omega) hc.2)), unitsLen_cons_neg h]

theorem contrPre_shift1 (p : ℕ × ℕ) (U A : PairSeq) :
    contrPre ((p.1 + 1, p.2) : ℕ × ℕ) (shift1 U) (shift1 A)
      = shift1 (contrPre p U A) := by
  simp [contrPre, shift1_append]

/-- 縮約の判定は平行移動で保たれる。 -/
theorem contrLen_shift1 (p : ℕ × ℕ) (B A : PairSeq) (k : ℕ) :
    contrLen ((p.1 + 1, p.2) : ℕ × ℕ) (shift1 B) k (shift1 A)
      = (contrLen p B k A).map (fun x => (shift1 x.1, shift1 x.2)) := by
  rcases hd : B.drop k with _ | ⟨q, r2⟩
  · rw [contrLen, contrLen, shift1_drop, hd]
    simp
  · have hds : (shift1 B).drop k = ((q.1 + 1, q.2) : ℕ × ℕ) :: shift1 r2 := by
      rw [shift1_drop, hd, shift1_cons]
    rw [contrLen, contrLen, hd, hds]
    simp only []
    rw [shift1_takeWhile q.1 r2, shift1_dropWhile q.1 r2, shift1_take k B,
      contrPre_shift1 p (B.take k) A, shift1_length (contrPre p (B.take k) A),
      shift1_drop (contrPre p (B.take k) A).length (r2.takeWhile fun x => q.1 < x.1)]
    by_cases hne : ((r2.takeWhile fun x => q.1 < x.1).drop
        (contrPre p (B.take k) A).length) = []
    · rw [hne]
      simp
    · rw [shift1_headI _ hne, shift1_take (contrPre p (B.take k) A).length]
      simp only [ne_eq, shift1_eq_nil_iff, shift1_inj_iff]
      split_ifs with h1 h2 h2
      · simp
      · exact absurd ⟨h1.1, by omega, h1.2.2.1, h1.2.2.2.1, by omega, h1.2.2.2.2.2⟩ h2
      · exact absurd ⟨h2.1, by omega, h2.2.2.1, h2.2.2.2.1, by omega, h2.2.2.2.2.2⟩ h1
      · rfl

/-- **`convC` は平行移動で変わらない**。 -/
theorem convC_shift1 : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n →
    ∀ (d plev : ℕ) (first force : Bool),
    convC (shift1 M) d plev first force = convC M d plev first force := by
  intro n
  induction n with
  | zero =>
    intro M hM d plev first force
    have : M = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp
  | succ n ih =>
    intro M hM d plev first force
    match M with
    | [] => simp
    | p :: r =>
      have hlenr : r.length ≤ n := by simp only [List.length_cons] at hM; omega
      have hTk : (r.takeWhile fun q => p.1 < q.1).length ≤ n :=
        le_trans (List.takeWhile_sublist _).length_le hlenr
      have hDr : (r.dropWhile fun q => p.1 < q.1).length ≤ n :=
        le_trans (List.length_dropWhile_le _ r) hlenr
      by_cases hl : ladOf p.2 d plev first force = true
      · rcases hcc : contrLen p (r.dropWhile fun q => p.1 < q.1)
            (unitsLen p (r.dropWhile fun q => p.1 < q.1))
            (r.takeWhile fun q => p.1 < q.1) with _ | ⟨rest2, Bq⟩
        · have hccs : contrLen ((p.1 + 1, p.2) : ℕ × ℕ)
              ((shift1 r).dropWhile fun q => ((p.1 + 1, p.2) : ℕ × ℕ).1 < q.1)
              (unitsLen ((p.1 + 1, p.2) : ℕ × ℕ)
                ((shift1 r).dropWhile fun q => ((p.1 + 1, p.2) : ℕ × ℕ).1 < q.1))
              ((shift1 r).takeWhile fun q => ((p.1 + 1, p.2) : ℕ × ℕ).1 < q.1) = none := by
            simp only []
            rw [shift1_dropWhile p.1 r, shift1_takeWhile p.1 r,
              unitsLen_shift1 (r.dropWhile fun q => p.1 < q.1).length p _ (Nat.le_refl _),
              contrLen_shift1, hcc]
            simp
          rw [shift1_cons,
            convC_cons_lad_none ((p.1 + 1, p.2) : ℕ × ℕ) (shift1 r) d plev first force
              (by exact hl) hccs,
            convC_cons_lad_none p r d plev first force hl hcc]
          simp only []
          rw [shift1_takeWhile p.1 r, shift1_dropWhile p.1 r, ih _ hTk, ih _ hDr]
        · have hlt := contrLen_lt hcc
          have hR2 : rest2.length ≤ n := by omega
          have hBq : Bq.length ≤ n := by omega
          have hTu : ((r.dropWhile fun q => p.1 < q.1).take
              (unitsLen p (r.dropWhile fun q => p.1 < q.1))).length ≤ n :=
            le_trans (List.take_sublist _ _).length_le hDr
          have hccs : contrLen ((p.1 + 1, p.2) : ℕ × ℕ)
              ((shift1 r).dropWhile fun q => ((p.1 + 1, p.2) : ℕ × ℕ).1 < q.1)
              (unitsLen ((p.1 + 1, p.2) : ℕ × ℕ)
                ((shift1 r).dropWhile fun q => ((p.1 + 1, p.2) : ℕ × ℕ).1 < q.1))
              ((shift1 r).takeWhile fun q => ((p.1 + 1, p.2) : ℕ × ℕ).1 < q.1)
              = some (shift1 rest2, shift1 Bq) := by
            simp only []
            rw [shift1_dropWhile p.1 r, shift1_takeWhile p.1 r,
              unitsLen_shift1 (r.dropWhile fun q => p.1 < q.1).length p _ (Nat.le_refl _),
              contrLen_shift1, hcc]
            simp
          rw [shift1_cons,
            convC_cons_lad_some ((p.1 + 1, p.2) : ℕ × ℕ) (shift1 r) d plev first force
              (by exact hl) hccs,
            convC_cons_lad_some p r d plev first force hl hcc]
          simp only []
          rw [shift1_takeWhile p.1 r, shift1_dropWhile p.1 r,
            unitsLen_shift1 (r.dropWhile fun q => p.1 < q.1).length p _ (Nat.le_refl _),
            shift1_take, ih _ hTk, ih _ hTu, ih _ hR2, ih _ hBq]
      · have hnl : ladOf p.2 d plev first force = false := by
          cases hx : ladOf p.2 d plev first force with
          | false => rfl
          | true => exact absurd hx hl
        rw [shift1_cons,
          convC_cons_nolad ((p.1 + 1, p.2) : ℕ × ℕ) (shift1 r) d plev first force (by exact hnl),
          convC_cons_nolad p r d plev first force hnl]
        simp only []
        rw [shift1_takeWhile p.1 r, shift1_dropWhile p.1 r, ih _ hTk, ih _ hDr]

/-- **ユニット列のうしろで像は切れる**（`first = false` の並び）。 -/
theorem convC_units_append {t : ℕ × ℕ} : ∀ {V : PairSeq}, Units t V →
    ∀ (L : PairSeq), (L = [] ∨ ¬ (t.1 < (L.headI).1)) →
    ∀ (D plev plev' : ℕ),
      convC (V ++ L) D plev false false
        = convC V D plev false false ++ convC L D plev' false false := by
  intro V hV
  induction hV with
  | nil =>
    intro L hL D plev plev'
    simp only [List.nil_append, convC_nil]
    exact convC_first_false L D plev plev' false false
  | @cons A U' hA hU ih =>
    intro L hL D plev plev'
    have hhd : U' ≠ [] → U'.headI = t := by
      intro hne
      rcases hU.head_eq with h | h
      · exact absurd h hne
      · exact h
    have hUL : (U' ++ L) = [] ∨ ¬ (t.1 < ((U' ++ L).headI).1) := by
      by_cases hne : U' = []
      · rw [hne]; simpa using hL
      · right
        rw [headI_append_left hne, hhd hne]; omega
    have hUe : U' = [] ∨ ¬ (t.1 < (U'.headI).1) := by
      by_cases hne : U' = []
      · exact Or.inl hne
      · right; rw [hhd hne]; omega
    obtain ⟨e1, e2⟩ := split_append (X := A) (Y := (U' ++ L)) (dd := t.1) hA hUL
    obtain ⟨f1, f2⟩ := split_append (X := A) (Y := U') (dd := t.1) hA hUe
    have hnl : ladOf t.2 D plev false false = false := by simp [ladOf]
    have hshape : (t :: (A ++ U')) ++ L = t :: (A ++ (U' ++ L)) := by
      simp [List.append_assoc]
    rw [hshape, convC_cons_nolad t (A ++ (U' ++ L)) D plev false false hnl,
      convC_cons_nolad t (A ++ U') D plev false false hnl, e1, e2, f1, f2,
      ih L hL D t.2 plev']
    simp [List.append_assoc]

/-- ユニット列を平行移動してもユニット列。 -/
theorem Units_shift1 {p : ℕ × ℕ} : ∀ {U : PairSeq}, Units p U →
    Units ((p.1 + 1, p.2) : ℕ × ℕ) (shift1 U) := by
  intro U hU
  induction hU with
  | nil => simpa using Units.nil
  | @cons A U' hA hU' ih =>
    rw [shift1_cons, shift1_append]
    refine Units.cons ?_ ih
    intro c hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    have := hA e he
    simp only []
    omega

/-- **縮約の前置きの像**。`pre = contrPre p U A` の像は
「梯子の本体 + `A` の像 + `U` の像」になる。 -/
theorem convC_contrPre {p : ℕ × ℕ} {A U r0 : PairSeq} {d : ℕ}
    (hA : ∀ c ∈ A, p.1 < c.1) (hU : Units p U) (hp2 : 1 ≤ p.2) (hdp : p.2 ≤ d)
    (hr0 : r0 = [] ∨ ¬ ((p.1 + 1) < (r0.headI).1)) :
    convC (contrPre p U A ++ r0) (d + 1) (p.2 - 1) true false
      = (d + 1, p.2) :: (convC A (d + 2) p.2 true false
          ++ convC U (d + 1) p.2 false false ++ convC r0 (d + 1) p.2 false false) := by
  have hshape : contrPre p U A ++ r0
      = ((p.1 + 1, p.2) : ℕ × ℕ) :: (shift1 A ++ (shift1 U ++ r0)) := by
    unfold contrPre
    simp [List.append_assoc]
  have hUs : Units ((p.1 + 1, p.2) : ℕ × ℕ) (shift1 U) := Units_shift1 hU
  have hAs : ∀ c ∈ shift1 A, ((p.1 + 1, p.2) : ℕ × ℕ).1 < c.1 := by
    intro c hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    have := hA e he
    simp only []
    omega
  have hUr : (shift1 U ++ r0) = [] ∨ ¬ (((p.1 + 1, p.2) : ℕ × ℕ).1 < ((shift1 U ++ r0).headI).1) := by
    by_cases hne : U = []
    · rw [hne]
      simp only [shift1_nil, List.nil_append]
      simpa using hr0
    · right
      have hsne : shift1 U ≠ [] := by rw [ne_eq, shift1_eq_nil_iff]; exact hne
      rw [headI_append_left hsne, shift1_headI U hne]
      have he : U.headI = p := by
        rcases hU.head_eq with h | h
        · exact absurd h hne
        · exact h
      rw [he]
      simp only []
      omega
  have hnl : ladOf (((p.1 + 1, p.2) : ℕ × ℕ)).2 (d + 1) (p.2 - 1) true false = false := by
    have hnd : ¬ (d + 1 ≤ p.2) := by omega
    simp [ladOf, hnd]
  have hdd : ddOf (((p.1 + 1, p.2) : ℕ × ℕ)).2 (d + 1) (p.2 - 1) true false = d + 1 := by
    unfold ddOf
    rw [if_neg (by rw [hnl]; simp), if_neg (by simp only []; omega)]
  obtain ⟨e1, e2⟩ := split_append (X := shift1 A) (Y := (shift1 U ++ r0))
    (dd := ((p.1 + 1, p.2) : ℕ × ℕ).1) hAs hUr
  rw [hshape, convC_cons_nolad _ _ (d + 1) (p.2 - 1) true false hnl, hdd, e1, e2]
  have hfr : (true && ((((p.1 + 1, p.2) : ℕ × ℕ)).2 == p.2 - 1)) = false := by
    simp only [Bool.true_and, beq_eq_false_iff_ne, ne_eq]
    omega
  rw [hfr, convC_units_append hUs r0 hr0 (d + 1) p.2 p.2,
    convC_shift1 A.length A (Nat.le_refl _), convC_shift1 U.length U (Nat.le_refl _)]
  simp [List.append_assoc]

/-- **コピーの並びの像**（コピー regime の核心）。 -/
theorem convC_run_contr {p q : ℕ × ℕ} {A U r0 : PairSeq} {d : ℕ}
    (hA : ∀ c ∈ A, p.1 < c.1) (hU : Units p U)
    (hq1 : q.1 = p.1) (hq2 : q.2 + 1 = p.2) (hdp : p.2 ≤ d)
    (hr0 : r0 = [] ∨ (r0.headI).1 = p.1 + 1)
    (hr0d : ∀ c ∈ r0, p.1 < c.1) :
    ∀ (k plev₀ : ℕ),
      convC ((List.replicate k (q :: (contrPre p U A ++ r0))).flatten) d plev₀ false false
        = (List.replicate k (((d, q.2) : ℕ × ℕ) :: ((d + 1, p.2) : ℕ × ℕ) ::
            (convC A (d + 2) p.2 true false ++ convC U (d + 1) p.2 false false
              ++ convC r0 (d + 1) p.2 false false))).flatten := by
  have hr0h : r0 = [] ∨ ¬ ((p.1 + 1) < (r0.headI).1) := by
    rcases hr0 with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hpre : ∀ c ∈ (contrPre p U A ++ r0), q.1 < c.1 := by
    intro c hc
    rw [hq1]
    rcases List.mem_append.1 hc with h | h
    · unfold contrPre at h
      rcases List.mem_append.1 h with h1 | h1
      · rcases List.mem_cons.1 h1 with rfl | h2
        · simp only []; omega
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h2
          have := hA e he
          simp only []; omega
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h1
        have := hU.ge e he
        simp only []; omega
    · exact hr0d c h
  intro k
  induction k with
  | zero => intro plev₀; simp
  | succ k ih =>
    intro plev₀
    have hflat : (List.replicate (k + 1) (q :: (contrPre p U A ++ r0))).flatten
        = q :: ((contrPre p U A ++ r0) ++ (List.replicate k
            (q :: (contrPre p U A ++ r0))).flatten) := by
      rw [List.replicate_succ, List.flatten_cons, List.cons_append]
    have hrest : (List.replicate k (q :: (contrPre p U A ++ r0))).flatten = []
        ∨ ¬ (q.1 < (((List.replicate k (q :: (contrPre p U A ++ r0))).flatten).headI).1) := by
      cases k with
      | zero => exact Or.inl rfl
      | succ k' =>
        right
        rw [List.replicate_succ, List.flatten_cons, List.cons_append]
        simp
    obtain ⟨e1, e2⟩ := split_append (X := (contrPre p U A ++ r0)) (dd := q.1) hpre hrest
    have hnl : ladOf q.2 d plev₀ false false = false := by simp [ladOf]
    have hdd : ddOf q.2 d plev₀ false false = d := by
      unfold ddOf
      rw [if_neg (by rw [hnl]; simp), if_neg (by omega)]
    rw [hflat, convC_cons_nolad q _ d plev₀ false false hnl, hdd, e1, e2]
    simp only [Bool.false_and]
    rw [ih q.2]
    have hq2' : q.2 = p.2 - 1 := by omega
    rw [hq2', convC_contrPre hA hU (by omega) hdp hr0h, List.replicate_succ, List.flatten_cons]
    simp [List.append_assoc]

/-- 縮約の前置きのあとに何も残らなければ縮約は発火しない。 -/
theorem contrLen_of_shape_nil {p q : ℕ × ℕ} {Arg U pre L : PairSeq}
    (hU : Units p U) (hpre : pre = contrPre p U Arg)
    (hpd : ∀ x ∈ pre, p.1 < x.1)
    (hq1 : q.1 = p.1) (hq2 : q.2 + 1 = p.2)
    (hL : L = [] ∨ ¬ (p.1 < (L.headI).1)) :
    contrLen p (U ++ q :: (pre ++ L)) (unitsLen p (U ++ q :: (pre ++ L))) Arg = none := by
  have hk : unitsLen p (U ++ q :: (pre ++ L)) = U.length :=
    unitsLen_append_units hU (Or.inr ⟨by simp only [List.headI]; omega,
      by simp only [List.headI]; intro h; rw [h] at hq2; omega⟩)
  have hdrop : (U ++ q :: (pre ++ L)).drop U.length = q :: (pre ++ L) := by simp
  have htake : (U ++ q :: (pre ++ L)).take U.length = U := by simp
  have hall : ∀ x ∈ pre, q.1 < x.1 := by
    intro x hx; rw [hq1]; exact hpd x hx
  have hLh : L = [] ∨ ¬ (q.1 < (L.headI).1) := by rw [hq1]; exact hL
  obtain ⟨e1, e2⟩ := split_append (dd := q.1) hall hLh
  rw [contrLen, hk, hdrop]
  simp only [htake, e1, e2, ← hpre]
  rw [if_neg (by rintro ⟨-, -, -, h4, -, -⟩; exact h4 (by simp))]

/-- ユニット列の像は深さパラメタを 1 増やしても変わらない（`d = p.2` のとき）。 -/
theorem convC_units_depth {p : ℕ × ℕ} (hp2 : 0 < p.2) : ∀ {U : PairSeq}, Units p U →
    ∀ d : ℕ, d = p.2 →
      convC U d p.2 false false = convC U (d + 1) p.2 false false := by
  intro U hU
  induction hU with
  | nil => intro d _; simp
  | @cons A U' hA hU' ih =>
    intro d hd
    have hUe : U' = [] ∨ ¬ (p.1 < (U'.headI).1) := by
      by_cases hne : U' = []
      · exact Or.inl hne
      · right
        have he : U'.headI = p := by
          rcases hU'.head_eq with h | h
          · exact absurd h hne
          · exact h
        rw [he]; omega
    obtain ⟨e1, e2⟩ := split_append (X := A) (Y := U') (dd := p.1) hA hUe
    have hnl : ∀ D : ℕ, ladOf p.2 D p.2 false false = false := by intro D; simp [ladOf]
    have hdd1 : ddOf p.2 d p.2 false false = d + 1 := by
      unfold ddOf
      rw [if_neg (by rw [hnl d]; simp), if_pos ⟨hp2, by omega⟩]
      omega
    have hdd2 : ddOf p.2 (d + 1) p.2 false false = d + 1 := by
      unfold ddOf
      rw [if_neg (by rw [hnl (d + 1)]; simp), if_neg (by omega)]
    rw [convC_cons_nolad p (A ++ U') d p.2 false false (hnl d),
      convC_cons_nolad p (A ++ U') (d + 1) p.2 false false (hnl (d + 1)),
      hdd1, hdd2, e1, e2, ih d hd]

/-- **段 0 の Stop（コピー regime）は本当に成り立つ**。
BMS 側は `q` から末尾列の 1 つ手前までのコピーの並び、DBMS 側は像の `dropLast` の
コピーの並びで、`m = n`（`rest2` が 2 列以上）または `m = n + 1`（`rest2` が 1 列）
で合う。 -/
theorem rdZeroStop {p q : ℕ × ℕ} {A U pre rest2 : PairSeq} {bd d plev : ℕ}
    {first force : Bool}
    (hb : blockok bd (p :: (A ++ (U ++ q :: (pre ++ rest2)))))
    (hc : colOK (p :: (A ++ (U ++ q :: (pre ++ rest2)))))
    (hbd : bd ≤ d) (hdle : d ≤ p.2) (hp1 : p.1 = bd)
    (hAdeep : ∀ x ∈ A, p.1 < x.1)
    (hU : Units p U) (hq2 : q.2 + 1 = p.2) (hq1 : q.1 = p.1) (hpre : pre = contrPre p U A)
    (hpd : ∀ x ∈ pre, p.1 < x.1) (hrd : ∀ x ∈ rest2, p.1 < x.1)
    (hrne : rest2 ≠ []) (hrh1 : (rest2.headI).1 = p.1 + 1) (hrh2 : (rest2.headI).2 < p.2)
    (hlev : entry (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 1
      ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1) = 0)
    (hlad : ladOf p.2 d plev first force = true)
    (hge : ¬ ((p :: (A ++ (U ++ q :: pre))).length
        ≤ parent (p :: (A ++ (U ++ q :: (pre ++ rest2)))) 0
            ((p :: (A ++ (U ++ q :: (pre ++ rest2)))).length - 1))) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ (U ++ q :: (pre ++ rest2)))) d plev first force)⟦m⟧
        = convC ((p :: (A ++ (U ++ q :: (pre ++ rest2))))⟦n'⟧) d plev first force := by
  intro n hn
  subst hpre
  have hpp : p.2 ≤ p.1 := hc p (by simp)
  have hdeq : d = p.2 := by omega
  have hp2 : 0 < p.2 := by omega
  have hplev : q.2 = plev := by
    unfold ladOf at hlad
    simp only [Bool.and_eq_true, beq_iff_eq] at hlad
    omega
  obtain ⟨r0, lp, hrs⟩ : ∃ r0 lp, rest2 = r0 ++ [lp] :=
    ⟨rest2.dropLast, rest2.getLast hrne, (List.dropLast_append_getLast hrne).symm⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = p :: (A ++ (U ++ q :: (contrPre p U A ++ rest2))) := ⟨_, rfl⟩
  obtain ⟨G0, hG0⟩ : ∃ G0, G0 = p :: (A ++ U) := ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2, G2 = p :: (A ++ (U ++ q :: contrPre p U A)) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = q :: (contrPre p U A ++ r0) := ⟨_, rfl⟩
  obtain ⟨C0, hC0⟩ : ∃ C0, C0 = ((d, plev) : ℕ × ℕ) :: ((d + 1, p.2) : ℕ × ℕ) ::
      (convC A (d + 2) p.2 true false ++ convC U (d + 1) p.2 false false) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = C0 ++ convC r0 (d + 1) p.2 false false := ⟨_, rfl⟩
  rw [← hBdef] at hb hc hlev hge ⊢
  rw [← hG2] at hge
  have hB0 : B = G0 ++ (q :: (contrPre p U A ++ rest2)) := by
    rw [hBdef, hG0]; simp [List.append_assoc]
  have hB2 : B = G2 ++ rest2 := by rw [hBdef, hG2]; simp [List.append_assoc]
  have hBsnoc : B = (G2 ++ r0) ++ [lp] := by rw [hB2, hrs]; simp [List.append_assoc]
  have hR1 : 1 ≤ rest2.length := List.length_pos_of_ne_nil hrne
  have hG0len : 1 ≤ G0.length := by rw [hG0]; simp
  have hlen02 : G2.length = G0.length + 1 + (contrPre p U A).length := by
    rw [hG0, hG2]; simp only [List.length_cons, List.length_append]; omega
  have hBlen : B.length = G2.length + rest2.length := by rw [hB2]; simp
  have hL2 : 1 < B.length := by omega
  have hlastB : B.getLastD (0, 0) = lp := by rw [hBsnoc]; exact getLastD_snoc _ _ _
  have hlastR : rest2.getLastD (0, 0) = lp := by rw [hrs]; exact getLastD_snoc _ _ _
  have hlpmem : lp ∈ rest2 := by rw [hrs]; simp
  have hlplev : lp.2 = 0 := by rw [← hlastB, ← entry_last]; exact hlev
  have hentq : entry B 0 G0.length = bd := by
    rw [hB0, show G0.length = G0.length + 0 by omega, entry_append_right, entry_zero0]
    simp only [List.headI]; omega
  have hentlast : entry B 0 (B.length - 1) = lp.1 := by rw [entry_last0, hlastB]
  have hlpge : bd + 1 ≤ lp.1 := by have := hrd lp hlpmem; omega
  have hpar : hasParent B 0 (B.length - 1) :=
    hasParent0_of_exists (by omega) ⟨G0.length, by omega, by rw [hentq, hentlast]; omega⟩
  obtain ⟨hparv, hoper⟩ := zeroStop_shape (bd := bd) (by rw [← hBdef]; exact hb)
    hp1 hq1 hpd hrd hrne hrh1 (by rw [← hBdef]; exact hlev)
    (by rw [← hBdef]; exact hpar) (by rw [← hBdef, ← hG2]; exact hge)
  rw [← hBdef, ← hG0] at hparv hoper
  have hnr0 : nextrel0 B G0.length (B.length - 1) := by
    have h := parent_nextR hpar
    unfold nextR at h
    rw [if_pos rfl, hparv] at h
    exact h
  have hentG2 : entry B 0 G2.length = bd + 1 := by
    rw [hB2, show G2.length = G2.length + 0 by omega, entry_append_right, entry_zero0]
    omega
  have hlpd : lp.1 = bd + 1 := by
    rcases Nat.lt_or_ge G2.length (B.length - 1) with hcase | hcase
    · have hx := hnr0.2.2.2.2 G2.length ⟨by omega, hcase⟩
      rw [hentlast, hentG2] at hx
      omega
    · have heq : G2.length = B.length - 1 := by omega
      rw [heq, hentlast] at hentG2
      omega
  have hr0d : ∀ x ∈ r0, p.1 < x.1 := fun x hx =>
    hrd x (by rw [hrs]; exact List.mem_append_left _ hx)
  have hr0h : r0 = [] ∨ (r0.headI).1 = p.1 + 1 := by
    by_cases hr : r0 = []
    · exact Or.inl hr
    · right; rw [← hrh1, hrs, headI_append_left hr]
  have hrmin : ∀ c ∈ rest2, (rest2.getLastD (0, 0)).1 ≤ c.1 := by
    intro c hcm
    rw [hlastR, hlpd]
    have := hrd c hcm; omega
  have hCB : convC B d plev first force = C0 ++ convC rest2 (d + 1) p.2 false false := by
    have h := convC_factor_contr (p := p) (q := q) (Arg := A) (U := U)
      (pre := contrPre p U A) (rest2 := rest2) (L := ([] : PairSeq)) (d := d) (plev := plev)
      (first := first) (force := force)
      hAdeep hU hq2 hq1 rfl hpd hrd hrne hrh1 hrh2 (Or.inl rfl) hlad
    simp only [List.append_nil, convC_nil] at h
    rw [hBdef, h, hC0]
    simp [List.append_assoc]
  have hCrestne : convC rest2 (d + 1) p.2 false false ≠ [] := by
    rw [ne_eq, convC_eq_nil_iff]; exact hrne
  have hdropR : (convC rest2 (d + 1) p.2 false false).dropLast
      = convC r0 (d + 1) p.2 false false := by
    rcases Nat.lt_or_ge 1 rest2.length with hcase | hcase
    · have hiR : idx1 rest2 (rest2.length - 1) = 0 := by
        rw [idx1, if_neg (by rw [entry_last, hlastR, hlplev]; omega)]
      have hnp : ¬ hasParent rest2 (idx1 rest2 (rest2.length - 1)) (rest2.length - 1) := by
        rw [hiR]
        rintro ⟨j, hj, -⟩
        unfold nextR at hj
        rw [if_pos rfl] at hj
        have h1 : entry rest2 0 j < entry rest2 0 (rest2.length - 1) := hj.2.2.2.1
        have hjl : j < rest2.length := hj.1
        have hmem : rest2.getD j (0, 0) ∈ rest2 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
          simpa using List.getElem_mem hjl
        have h2 := hrd _ hmem
        rw [entry, if_pos rfl] at h1
        rw [entry_last0, hlastR, hlpd] at h1
        omega
      have h := convC_dropLast_noParent_aux rest2.length rest2 (Nat.le_refl _) hcase
        (d + 1) p.2 false false
        (contrOK_of_last_zero (by rw [entry_last, hlastR, hlplev])) hnp
      rw [← h, hrs]
      simp
    · have hr0e : r0 = [] := by
        have hlen1 : rest2.length = 1 := by omega
        rw [hrs] at hlen1
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen1
        exact List.eq_nil_of_length_eq_zero (by omega)
      rw [hrs, hr0e]
      simp only [List.nil_append, convC_nil]
      have hnl : ladOf lp.2 (d + 1) p.2 false false = false := by simp [ladOf]
      rw [convC_cons_nolad lp [] (d + 1) p.2 false false hnl]
      simp
  have hDdrop : (convC B d plev first force).dropLast = D := by
    rw [hCB, hD, List.dropLast_append_of_ne_nil hCrestne, hdropR]
  have hCBlen : 2 ≤ (convC B d plev first force).length := convC_length_ge_two hL2 _ _ _ _
  have hCBlast : ((convC B d plev first force).getLastD (0, 0)).1 = d + 1 := by
    rw [hCB, getLastD_append_right hCrestne]
    exact convC_getLast_min rest2.length rest2 (Nat.le_refl _) hrne hrmin
      (by rw [hlastR, hlplev]) (d + 1) p.2 false false
  have hCBlev : entry (convC B d plev first force) 1
      ((convC B d plev first force).length - 1) = 0 := by
    rw [entry_last, convC_getLast_level B.length B (Nat.le_refl _) d plev first force,
      hlastB, hlplev]
  have hCBhead : entry (convC B d plev first force) 0 0 = d := by
    rw [entry_zero0, hCB, hC0]
    simp
  have hCBmid : ∀ j, 0 < j → j < (convC B d plev first force).length →
      d + 1 ≤ entry (convC B d plev first force) 0 j := by
    intro j hj0 hjl
    obtain ⟨R, hR⟩ : ∃ R, R = ((d + 1, p.2) : ℕ × ℕ) ::
        ((convC A (d + 2) p.2 true false ++ convC U (d + 1) p.2 false false)
          ++ convC rest2 (d + 1) p.2 false false) := ⟨_, rfl⟩
    have hCBR : convC B d plev first force = ((d, plev) : ℕ × ℕ) :: R := by
      rw [hCB, hC0, hR]; simp [List.append_assoc]
    have hRge : ∀ c ∈ R, d + 1 ≤ c.1 := by
      intro c hcm
      rw [hR] at hcm
      rcases List.mem_cons.1 hcm with rfl | hcm2
      · simp
      rcases List.mem_append.1 hcm2 with hcm3 | hcm3
      · rcases List.mem_append.1 hcm3 with hcm4 | hcm4
        · have := convC_ge' A (d + 2) p.2 true false c hcm4; omega
        · exact convC_ge' U (d + 1) p.2 false false c hcm4
      · exact convC_ge' rest2 (d + 1) p.2 false false c hcm3
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj'l : j' < R.length := by
      rw [hCBR] at hjl; simp only [List.length_cons] at hjl; omega
    have hmem : R.getD j' (0, 0) ∈ R := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'l]
      simpa using List.getElem_mem hj'l
    rw [hCBR, entry_cons_succ, entry, if_pos rfl]
    exact hRge _ hmem
  have hCBnr : nextrel0 (convC B d plev first force) 0
      ((convC B d plev first force).length - 1) := by
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [hCBhead, entry_last0, hCBlast]; omega
    · rintro j ⟨hj0, hjl⟩
      rw [entry_last0, hCBlast]
      exact hCBmid j hj0 (by omega)
  have hDBMS : ∀ m : ℕ, (convC B d plev first force)⟦m⟧ = (List.replicate m D).flatten := by
    intro m
    have h := oper_repeat_at (M := convC B d plev first force) 0 m (by omega) hCBlev hCBnr
    rw [h]
    simp only [List.take_zero, List.nil_append, List.drop_zero, hDdrop]
  have hVhead : ∀ k : ℕ, (List.replicate k V).flatten = []
      ∨ ¬ (p.1 < (((List.replicate k V).flatten).headI).1) := by
    intro k
    cases k with
    | zero => exact Or.inl rfl
    | succ k' =>
      right
      rw [List.replicate_succ, List.flatten_cons, hV, List.cons_append]
      simp only [List.headI]
      omega
  have hVhead1 : ∀ k : ℕ, ¬ (p.1 < (((List.replicate (k + 1) V).flatten).headI).1) := by
    intro k
    rw [List.replicate_succ, List.flatten_cons, hV, List.cons_append]
    simp only [List.headI]
    omega
  have hrdl : rest2.dropLast = r0 := by rw [hrs]; simp
  obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
  have hflat : (List.replicate (k' + 1) V).flatten = V ++ (List.replicate k' V).flatten := by
    rw [List.replicate_succ, List.flatten_cons]
  have hoperV : B⟦k' + 1⟧ = G0 ++ (List.replicate (k' + 1) V).flatten := by
    rw [hoper (k' + 1), hrdl, hV]
  have hrun : ∀ k : ℕ, convC ((List.replicate k V).flatten) d p.2 false false
      = (List.replicate k (((d, q.2) : ℕ × ℕ) :: ((d + 1, p.2) : ℕ × ℕ) ::
          (convC A (d + 2) p.2 true false ++ convC U (d + 1) p.2 false false
            ++ convC r0 (d + 1) p.2 false false))).flatten := by
    intro k
    rw [hV]
    exact convC_run_contr hAdeep hU hq1 hq2 (by omega) hr0h hr0d k p.2
  have hDrun : (((d, q.2) : ℕ × ℕ) :: ((d + 1, p.2) : ℕ × ℕ) ::
      (convC A (d + 2) p.2 true false ++ convC U (d + 1) p.2 false false
        ++ convC r0 (d + 1) p.2 false false)) = D := by
    rw [hD, hC0, hplev]; simp [List.append_assoc]
  rw [hDrun] at hrun
  by_cases hr0e : r0 = []
  · refine ⟨k' + 2, k' + 1, by omega, Nat.le_refl _, ?_⟩
    have hTh : (U ++ (List.replicate (k' + 1) V).flatten) = []
        ∨ ¬ (p.1 < ((U ++ (List.replicate (k' + 1) V).flatten).headI).1) := by
      right
      by_cases hUe : U = []
      · rw [hUe]
        simp only [List.nil_append]
        exact hVhead1 k'
      · rw [headI_append_left hUe]
        have he : U.headI = p := by
          rcases hU.head_eq with h | h
          · exact absurd h hUe
          · exact h
        rw [he]; omega
    have hVW : V ++ (List.replicate k' V).flatten
        = q :: (contrPre p U A ++ (List.replicate k' V).flatten) := by
      rw [hV, hr0e]; simp
    have hnone : contrLen p (U ++ (List.replicate (k' + 1) V).flatten)
        (unitsLen p (U ++ (List.replicate (k' + 1) V).flatten)) A = none := by
      rw [hflat, hVW]
      exact contrLen_of_shape_nil hU rfl hpd hq1 hq2 (hVhead k')
    obtain ⟨e1, e2⟩ := split_append (X := A) (Y := (U ++ (List.replicate (k' + 1) V).flatten))
      (dd := p.1) hAdeep hTh
    have hkey : convC (B⟦k' + 1⟧) d plev first force
        = (List.replicate (k' + 2) D).flatten := by
      rw [hoperV, hG0]
      have hsh : (p :: (A ++ U)) ++ (List.replicate (k' + 1) V).flatten
          = p :: (A ++ (U ++ (List.replicate (k' + 1) V).flatten)) := by
        simp [List.append_assoc]
      rw [hsh, convC_cons_lad_none p _ d plev first force hlad (by rw [e1, e2]; exact hnone),
        e1, e2, convC_units_append hU _ (hVhead (k' + 1)) d p.2 p.2,
        convC_units_depth hp2 hU d hdeq, hrun (k' + 1), hD, hC0, hr0e]
      simp [List.replicate_succ, List.append_assoc]
    rw [hDBMS (k' + 2), hkey]
  · refine ⟨k' + 1, k' + 1, by omega, Nat.le_refl _, ?_⟩
    have hr0h1 : (r0.headI).1 = p.1 + 1 := by
      rcases hr0h with h | h
      · exact absurd h hr0e
      · exact h
    have hr0h2 : (r0.headI).2 < p.2 := by
      have he : rest2.headI = r0.headI := by rw [hrs, headI_append_left hr0e]
      rw [← he]; exact hrh2
    have hkey : convC (B⟦k' + 1⟧) d plev first force
        = (List.replicate (k' + 1) D).flatten := by
      rw [hoperV, hG0, hflat]
      have hsh : (p :: (A ++ U)) ++ (V ++ (List.replicate k' V).flatten)
          = p :: (A ++ (U ++ q :: ((contrPre p U A ++ r0)
              ++ (List.replicate k' V).flatten))) := by
        rw [hV]; simp [List.append_assoc]
      rw [hsh, convC_factor_contr hAdeep hU hq2 hq1 rfl hpd hr0d hr0e hr0h1 hr0h2
        (hVhead k') hlad, hrun k', hD, hC0]
      rw [List.replicate_succ, List.flatten_cons]
      simp [List.append_assoc]
    rw [hDBMS (k' + 1), hkey]


/-- **縮約が発火する段（段 0・残余なし）**。 -/
theorem reindexD_zero_fire3 (N : ℕ)
    (ih : ∀ (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → (bd = 0 → d = 0) →
      entry B 1 (B.length - 1) = 0 →
      argPatOK B → hpOK B d plev first force → fOK B d plev force →
      argCtrOK B → hcOK B plev first →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force)
    {p q : ℕ × ℕ} {A T U pre rest2 Bq : PairSeq} {bd d plev : ℕ} {first force : Bool}
    (hlenN : (p :: (A ++ T)).length ≤ N + 1)
    (hb : blockok bd (p :: (A ++ T))) (hc : colOK (p :: (A ++ T)))
    (hd : descOK (p :: (A ++ T))) (hbd : bd ≤ d) (hz0 : bd = 0 → d = 0)
    (hp1 : p.1 = bd)
    (hlev : entry (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) = 0)
    (hAP : argPatOK (p :: (A ++ T))) (hAC : argCtrOK (p :: (A ++ T)))
    (hFC : fOK (p :: (A ++ T)) d plev force)
    (hAdeep : ∀ x ∈ A, p.1 < x.1)
    (hlad : ladOf p.2 d plev first force = true)
    (hpar : hasParent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1))
    (hU : Units p U) (hTeq : T = U ++ q :: ((pre ++ rest2) ++ Bq))
    (hq2 : q.2 + 1 = p.2) (hq1 : q.1 = p.1) (hpre : pre = contrPre p U A)
    (hpd : ∀ x ∈ pre, p.1 < x.1) (hrd : ∀ x ∈ rest2, p.1 < x.1)
    (hBqh : Bq = [] ∨ ¬ (p.1 < (Bq.headI).1))
    (hrne : rest2 ≠ []) (hrh1 : (rest2.headI).1 = p.1 + 1) (hrh2 : (rest2.headI).2 < p.2) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
      (convC (p :: (A ++ T)) d plev first force)⟦m⟧
        = convC ((p :: (A ++ T))⟦n'⟧) d plev first force := by
  intro n hn
  -- 共通の下ごしらえ
  have hnrp : nextrel0 (p :: (A ++ T))
      (parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1))
      ((p :: (A ++ T)).length - 1) := by
    have h := parent_nextR hpar
    unfold nextR at h; rw [if_pos rfl] at h; exact h
  have hj0ge : bd ≤ entry (p :: (A ++ T)) 0
      (parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1)) := by
    have hj := hnrp.1
    have hmem : (p :: (A ++ T)).getD
        (parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1)) (0, 0) ∈ (p :: (A ++ T)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      simpa using List.getElem_mem hj
    rw [entry, if_pos rfl]
    exact hb.2.1 _ hmem
  have hlpgt : bd < ((p :: (A ++ T)).getLastD (0, 0)).1 := by
    have h1 := hnrp.2.2.2.1
    rw [entry_last0] at h1
    omega
  have hlplev : ((p :: (A ++ T)).getLastD (0, 0)).2 = 0 := by
    rw [← entry_last]; exact hlev
  have hTdeep : ∀ x ∈ (pre ++ rest2), p.1 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hpd x h
    · exact hrd x h
  have hpreh : (pre.headI).1 = p.1 + 1 := by rw [hpre]; simp [contrPre, shift1]
  have hThd : T = [] ∨ ¬ (p.1 < (T.headI).1) := by
    right
    rw [hTeq]
    by_cases hUe : U = []
    · rw [hUe]; simp only [List.nil_append, List.headI]; omega
    · rw [headI_append_left hUe]
      rcases hU.head_eq with h | h
      · exact absurd h hUe
      · rw [h]; omega
  obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := p.1) hAdeep hThd
  have hdT : descOK T := by
    have hx := (descOK_cons.1 hd).2.2
    rw [e2] at hx; exact hx
  have hAPt : argPatOK T := by
    have hx := (argPatOK_cons.1 hAP).2.2
    rw [e2] at hx; exact hx
  have hqL : (q :: ((pre ++ rest2) ++ Bq)) = []
      ∨ ¬ (p.1 < ((q :: ((pre ++ rest2) ++ Bq)).headI).1) := by
    right; simp only [List.headI]; omega
  have hdQ : descOK (q :: ((pre ++ rest2) ++ Bq)) :=
    descOK_units p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hdT)
  have hAPq : argPatOK (q :: ((pre ++ rest2) ++ Bq)) :=
    argPatOK_drop p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hAPt)
  obtain ⟨f1, f2⟩ := split_append (X := (pre ++ rest2)) (Y := Bq) (dd := q.1)
    (by rw [hq1]; exact hTdeep) (by rw [hq1]; exact hBqh)
  have hdBq : descOK Bq := by
    have hx := (descOK_cons.1 hdQ).2.2
    rw [f2] at hx; exact hx
  have hAPBq : argPatOK Bq := by
    have hx := (argPatOK_cons.1 hAPq).2.2
    rw [f2] at hx; exact hx
  have hdPR : descOK (pre ++ rest2) := by
    have hx := (descOK_cons.1 hdQ).2.1
    rw [f1] at hx; exact hx
  have hAPPR : argPatOK (pre ++ rest2) := by
    have hx := (argPatOK_cons.1 hAPq).2.1
    rw [f1] at hx; exact hx
  have hrestL : rest2 = [] ∨ ¬ (p.1 + 1 < (rest2.headI).1) := Or.inr (by rw [hrh1]; omega)
  have hpreall : ∀ c ∈ pre, p.1 + 1 ≤ c.1 := fun c hcc => by have := hpd c hcc; omega
  have hpreh' : pre = [] ∨ (pre.headI).1 ≤ p.1 + 1 := Or.inr (by rw [hpreh])
  have hdR : descOK rest2 :=
    descOK_units (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hdPR
  have hAPR : argPatOK rest2 :=
    argPatOK_drop (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hAPPR
  have hACt : argCtrOK T := by
    have hx := (argCtrOK_cons.1 hAC).2.2
    rw [e2] at hx; exact hx
  have hACq : argCtrOK (q :: ((pre ++ rest2) ++ Bq)) :=
    argCtrOK_drop p.1 _ hqL U.length U (Nat.le_refl _) (Units.ge hU) (Units.head_le hU)
      (by rw [← hTeq]; exact hACt)
  have hACBq : argCtrOK Bq := by
    have hx := (argCtrOK_cons.1 hACq).2.2
    rw [f2] at hx; exact hx
  have hACPR : argCtrOK (pre ++ rest2) := by
    have hx := (argCtrOK_cons.1 hACq).2.1
    rw [f1] at hx; exact hx
  have hACR : argCtrOK rest2 :=
    argCtrOK_drop (p.1 + 1) rest2 hrestL pre.length pre (Nat.le_refl _) hpreall hpreh' hACPR
  have hmemBq : ∀ c ∈ Bq, c ∈ (p :: (A ++ T)) := by
    intro c hcc
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    rw [hTeq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hcc))
  have hmemR : ∀ c ∈ rest2, c ∈ (p :: (A ++ T)) := by
    intro c hcc
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    rw [hTeq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_right _ hcc)))
  have hcBq : colOK Bq := fun cc hcc => hc cc (hmemBq cc hcc)
  have hcR : colOK rest2 := fun cc hcc => hc cc (hmemR cc hcc)
  by_cases hBqe : Bq = []
  · -- `Bq = []`: `rest2` へ降りるか、残余
    obtain ⟨G2, hG2⟩ : ∃ G2 : PairSeq, G2 = p :: (A ++ (U ++ q :: pre)) := ⟨_, rfl⟩
    have hBeq2 : (p :: (A ++ T)) = G2 ++ rest2 := by
      rw [hG2, hTeq, hBqe]; simp [List.append_assoc]
    have hBeq3 : (p :: (A ++ T)) = p :: (A ++ (U ++ q :: (pre ++ rest2))) := by
      rw [hTeq, hBqe]; simp [List.append_assoc]
    have hG2len : 1 ≤ G2.length := by rw [hG2]; simp
    have hlenB2 : (p :: (A ++ T)).length = G2.length + rest2.length := by
      rw [hBeq2]; simp
    have hlast : (p :: (A ++ T)).getLastD (0, 0) = rest2.getLastD (0, 0) := by
      rw [hBeq2]; exact getLastD_append_right hrne _
    have hlevR : entry rest2 1 (rest2.length - 1) = 0 := by
      rw [entry_last, ← hlast]; exact hlplev
    have hzR : ¬ (entry rest2 0 (rest2.length - 1) = 0 ∧ entry rest2 1 (rest2.length - 1) = 0) := by
      rintro ⟨h1, -⟩
      rw [entry_last0, ← hlast] at h1
      omega
    have hbR : blockok (p.1 + 1) rest2 := by
      refine ⟨fun _ => hrh1, fun cc hcc => by have := hrd cc hcc; omega, ?_⟩
      exact (steps1_append.1 (by rw [← hBeq2]; exact hb.2.2)).2.1
    by_cases hge2 : G2.length ≤ parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1)
    · have hiR : idx1 rest2 (rest2.length - 1) = 0 := by
        rw [idx1, if_neg (by rw [hlevR]; omega)]
      have hR1 : 1 ≤ rest2.length := List.length_pos_of_ne_nil hrne
      have hidx : (p :: (A ++ T)).length - 1 = G2.length + (rest2.length - 1) := by omega
      have hpB : hasParent (G2 ++ rest2) (idx1 rest2 (rest2.length - 1))
          (G2.length + (rest2.length - 1)) := by
        rw [hiR, ← hidx, ← hBeq2]; exact hpar
      have hgeB : G2.length ≤ parent (G2 ++ rest2) (idx1 rest2 (rest2.length - 1))
          (G2.length + (rest2.length - 1)) := by
        rw [hiR, ← hidx, ← hBeq2]; exact hge2
      rw [hG2] at hpB hgeB
      have hIH := ih rest2 (by omega) (p.1 + 1) (d + 1) p.2 false false hbR hcR hdR
        (by omega) (by omega) hlevR hAPR hpOK_false fOK_false hACR hcOK_false
      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_rest_contr (Arg := A) (T := rest2)
        hAdeep hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 hlad hbR hcR hdR (by omega) hzR
        hpB hgeB hIH n hn
      refine ⟨m, n', k1, k2, ?_⟩
      rw [← hG2, ← hBeq2] at k3
      exact k3
    · rw [hBeq3]
      have hdle : d ≤ p.2 := by
        unfold ladOf at hlad
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hlad
        rcases hlad.2 with hx | hx
        · exact hx
        · rcases hFC hx with h1 | h2
          · exact absurd hlad.1.2 (h1 p (A ++ T) rfl)
          · omega
      exact rdZeroStop (bd := bd) (by rw [← hBeq3]; exact hb) (by rw [← hBeq3]; exact hc)
        hbd hdle hp1 hAdeep hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2
        (by rw [← hBeq3]; exact hlev) hlad (by rw [← hBeq3, ← hG2]; exact hge2) n hn
  · -- `Bq ≠ []`: `q` の兄弟へ降りる
    have hBqh' : ¬ (p.1 < (Bq.headI).1) := by
      rcases hBqh with h | h
      · exact absurd h hBqe
      · exact h
    obtain ⟨G1, hG1⟩ : ∃ G1 : PairSeq, G1 = p :: (A ++ (U ++ q :: (pre ++ rest2))) := ⟨_, rfl⟩
    have hBeq1 : (p :: (A ++ T)) = G1 ++ Bq := by
      rw [hG1, hTeq]; simp [List.append_assoc]
    have hG1len : 1 ≤ G1.length := by rw [hG1]; simp
    have hBq1 : 1 ≤ Bq.length := List.length_pos_of_ne_nil hBqe
    have hlenB1 : (p :: (A ++ T)).length = G1.length + Bq.length := by
      rw [hBeq1]; simp
    have hlast : (p :: (A ++ T)).getLastD (0, 0) = Bq.getLastD (0, 0) := by
      rw [hBeq1]; exact getLastD_append_right hBqe _
    have hlevBq : entry Bq 1 (Bq.length - 1) = 0 := by
      rw [entry_last, ← hlast]; exact hlplev
    have hzBq : ¬ (entry Bq 0 (Bq.length - 1) = 0 ∧ entry Bq 1 (Bq.length - 1) = 0) := by
      rintro ⟨h1, -⟩
      rw [entry_last0, ← hlast] at h1
      omega
    have hbBq : blockok bd Bq := by
      refine ⟨?_, fun cc hcc => hb.2.1 cc (hmemBq cc hcc), ?_⟩
      · intro hne
        have h1 : bd ≤ (Bq.headI).1 := hb.2.1 _ (hmemBq _ (headI_mem hne))
        omega
      · exact (steps1_append.1 (by rw [← hBeq1]; exact hb.2.2)).2.1
    have hgeG1 : G1.length ≤ parent (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1) := by
      by_contra hlt
      have hhead : entry (p :: (A ++ T)) 0 G1.length = (Bq.headI).1 := by
        rw [hBeq1, show G1.length = G1.length + 0 by omega, entry_append_right, entry_zero0]
      have hthead : (Bq.headI).1 ≤ bd := by omega
      rcases Nat.lt_or_ge G1.length ((p :: (A ++ T)).length - 1) with hcase | hcase
      · have hx := hnrp.2.2.2.2 G1.length ⟨by omega, hcase⟩
        rw [entry_last0, hhead] at hx
        omega
      · have heq : G1.length = (p :: (A ++ T)).length - 1 := by omega
        rw [heq, entry_last0] at hhead
        omega
    have hiBq : idx1 Bq (Bq.length - 1) = 0 := by
      rw [idx1, if_neg (by rw [hlevBq]; omega)]
    have hidx : (p :: (A ++ T)).length - 1 = G1.length + (Bq.length - 1) := by omega
    have hpB : hasParent (G1 ++ Bq) (idx1 Bq (Bq.length - 1))
        (G1.length + (Bq.length - 1)) := by
      rw [hiBq, ← hidx, ← hBeq1]; exact hpar
    have hgeB : G1.length ≤ parent (G1 ++ Bq) (idx1 Bq (Bq.length - 1))
        (G1.length + (Bq.length - 1)) := by
      rw [hiBq, ← hidx, ← hBeq1]; exact hgeG1
    rw [hG1] at hpB hgeB
    have hIH := ih Bq (by omega) bd d p.2 false false hbBq hcBq hdBq hbd hz0 hlevBq hAPBq
      hpOK_false fOK_false hACBq hcOK_false
    obtain ⟨m, n', k1, k2, k3⟩ := reindexD_sib_contr (Arg := A) (T := Bq)
      hAdeep hU hq2 hq1 hpre hpd hrd hrne hrh1 hrh2 hBqh' hlad (by rw [hp1]; exact hbBq)
      hcBq hdBq (by omega) hzBq
      hpB hgeB hIH n hn
    refine ⟨m, n', k1, k2, ?_⟩
    rw [← hG1, ← hBeq1] at k3
    exact k3


/-- **段 0 の組み立て（残余は `CtrPres2` だけ）**。 -/
theorem reindexD_zero_block5 (Hp : CtrPres2) :
    ∀ (N : ℕ) (B : PairSeq), B.length ≤ N → ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd B → colOK B → descOK B → bd ≤ d → (bd = 0 → d = 0) →
      entry B 1 (B.length - 1) = 0 →
      argPatOK B → hpOK B d plev first force → fOK B d plev force →
      argCtrOK B → hcOK B plev first →
      ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧
        (convC B d plev first force)⟦m⟧ = convC (B⟦n'⟧) d plev first force := by
  intro N
  induction N with
  | zero =>
    intro B hB bd d plev first force _ _ _ _ _ _ _ _ _ _ _ n hn
    have hBe : B = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hBe
    exact ⟨1, n, Nat.le_refl 1, Nat.le_refl n, by
      rw [convC_nil, oper_eq_self_short n (by simp), convC_nil,
        oper_eq_self_short 1 (by simp)]⟩
  | succ N ih =>
    intro B hB bd d plev first force hb hc hd hbd hz0 hlev hAP hHP hFC hAC hHC n hn
    cases B with
    | nil =>
      exact ⟨1, n, Nat.le_refl 1, Nat.le_refl n, by
        rw [convC_nil, oper_eq_self_short n (by simp), convC_nil,
          oper_eq_self_short 1 (by simp)]⟩
    | cons p r =>
      have hp1 : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp1]⟩
      -- 引数ブロックと兄弟ブロックに割る
      obtain ⟨A, T, hAd, hTd⟩ :
          ∃ A T, A = (r.takeWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) ∧
                 T = (r.dropWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) := ⟨_, _, rfl, rfl⟩
      have hrAT : r = A ++ T := by
        rw [hAd, hTd]; exact (List.takeWhile_append_dropWhile).symm
      subst hrAT
      have hAdeep : ∀ x ∈ A, ((bd, y) : ℕ × ℕ).1 < x.1 := by
        intro x hx
        rw [hAd] at hx
        simpa using List.mem_takeWhile_imp hx
      have hThd : T = [] ∨ ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
        rw [hTd]; exact dropWhile_head_not _ _
      obtain ⟨e1, e2⟩ := split_append (X := A) (Y := T) (dd := ((bd, y) : ℕ × ℕ).1)
        hAdeep hThd
      -- 新しい不変量を割る
      obtain ⟨hAPh, hAPa, hAPt⟩ := argPatOK_cons.1 hAP
      rw [e1] at hAPh hAPa
      rw [e2] at hAPt
      obtain ⟨hACh, hACa, hACt⟩ := argCtrOK_cons.1 hAC
      rw [e1] at hACh hACa
      rw [e2] at hACt
      have hfA : fOK A (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
          ((bd, y) : ℕ × ℕ).2 (first && (((bd, y) : ℕ × ℕ).2 == plev)) := by
        intro hft
        have hf1 : first = true := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.1
        have hpl : ((bd, y) : ℕ × ℕ).2 = plev := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.2
        rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
        · left
          intro a s hs
          have hkey := hh ((bd, y) : ℕ × ℕ) (A ++ T) rfl hpl (by rw [e1, hs]; simp)
          rw [e1, hs] at hkey
          simpa using hkey
        · right
          subst hd0; subst hpl0; subst hfc0
          have hy0 : y = 0 := by simpa using hpl
          subst hy0
          simp [ddOf, ladOf]
      -- 不変量を割る
      have hbA : blockok (bd + 1) A := by rw [← e1]; exact blockok_arg hb
      have hbT : blockok bd T := by rw [← e2]; exact blockok_tail hb
      have hcA : colOK A := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_left A T))) hc
      have hcT : colOK T := colOK_sublist
        (List.Sublist.cons _ ((List.sublist_append_right A T))) hc
      obtain ⟨hdh, hdA, hdT⟩ := descOK_cons.1 hd
      rw [e1] at hdA
      rw [e2] at hdh hdT
      have hlAT : A.length + T.length ≤ N := by
        simp only [List.length_cons, List.length_append] at hB
        omega
      -- 末尾列
      have hBne : ((bd, y) :: (A ++ T)) ≠ [] := by simp
      have hlplev : (((bd, y) :: (A ++ T)).getLastD (0, 0)).2 = 0 := by
        rw [← entry_last]; exact hlev
      by_cases hrne : A ++ T = []
      · -- 1 列のブロック
        obtain ⟨hAe, hTe⟩ := List.append_eq_nil_iff.1 hrne
        subst hAe; subst hTe
        have hy : y = 0 := by
          have h := hlplev
          simp only [List.append_nil, List.getLastD] at h
          simpa using h
        subst hy
        refine ⟨1, n, Nat.le_refl 1, Nat.le_refl n, ?_⟩
        have hnl : ladOf ((bd, 0) : ℕ × ℕ).2 d plev first force = false := by simp [ladOf]
        rw [List.append_nil, oper_eq_self_short n (by simp),
          convC_cons_nolad ((bd, 0) : ℕ × ℕ) [] d plev first force hnl]
        simp only [List.takeWhile_nil, List.dropWhile_nil, convC_nil, List.append_nil]
        exact oper_eq_self_short 1 (by simp)
      · have hL2 : 1 < ((bd, y) :: (A ++ T)).length := by
          simp only [List.length_cons]
          have := List.length_pos_of_ne_nil hrne
          omega
        have hlpmem : ((bd, y) :: (A ++ T)).getLastD (0, 0) ∈ ((bd, y) :: (A ++ T)) :=
          getLastD_mem hBne _
        by_cases hlp0 : (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 = 0
        · -- 場合 (a): 末尾列 = (0,0)
          have hbd0 : bd = 0 := by
            have := hb.2.1 _ hlpmem
            omega
          have hd0 : d = 0 := hz0 hbd0
          subst hd0
          have hlpeq : ((bd, y) :: (A ++ T)).getLastD (0, 0) = ((0, 0) : ℕ × ℕ) :=
            Prod.ext hlp0 hlplev
          have hg : ((bd, y) :: (A ++ T)).getLast hBne = ((0, 0) : ℕ × ℕ) := by
            rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast (h := hBne)] at hlpeq
            simpa using hlpeq
          have hsplit : ((bd, y) :: (A ++ T)).dropLast ++ [((0, 0) : ℕ × ℕ)]
              = ((bd, y) :: (A ++ T)) := by
            rw [← hg]; exact List.dropLast_append_getLast hBne
          have hdne : ((bd, y) :: (A ++ T)).dropLast ≠ [] := by
            intro he
            have hl : ((bd, y) :: (A ++ T)).dropLast.length
                = ((bd, y) :: (A ++ T)).length - 1 := List.length_dropLast
            rw [he] at hl
            simp only [List.length_nil] at hl
            omega
          have hcdl : colOK (((bd, y) :: (A ++ T)).dropLast) :=
            colOK_sublist (List.dropLast_sublist _) hc
          obtain ⟨m, n', h1, h2, h3⟩ := reindexD_succ_gen plev first force hdne hcdl n hn
          rw [hsplit] at h3
          exact ⟨m, n', h1, h2, h3⟩
        · -- 末尾列の深さは正
          have hlpos : 0 < (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 := by omega
          have hz : ¬ (entry ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1) = 0 ∧
                       entry ((bd, y) :: (A ++ T)) 1
                         (((bd, y) :: (A ++ T)).length - 1) = 0) := by
            rintro ⟨h1, -⟩
            rw [entry_last0] at h1
            omega
          have hi1 : idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1) = 0 := by
            rw [idx1, if_neg (by rw [hlev]; omega)]
          by_cases hpar : hasParent ((bd, y) :: (A ++ T))
              (idx1 ((bd, y) :: (A ++ T)) (((bd, y) :: (A ++ T)).length - 1))
              (((bd, y) :: (A ++ T)).length - 1)
          · -- 親がある
            rw [hi1] at hpar
            have hnrp : nextrel0 ((bd, y) :: (A ++ T))
                (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1))
                (((bd, y) :: (A ++ T)).length - 1) := by
              have h := parent_nextR hpar
              unfold nextR at h; rw [if_pos rfl] at h; exact h
            have hj0ge : bd ≤ entry ((bd, y) :: (A ++ T)) 0
                (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1)) := by
              have hj := hnrp.1
              have hmem : ((bd, y) :: (A ++ T)).getD
                  (parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1)) (0, 0)
                  ∈ ((bd, y) :: (A ++ T)) := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
                simpa using List.getElem_mem hj
              rw [entry, if_pos rfl]
              exact hb.2.1 _ hmem
            have hlpgt : bd < (((bd, y) :: (A ++ T)).getLastD (0, 0)).1 := by
              have h1 := hnrp.2.2.2.1
              rw [entry_last0] at h1
              omega
            by_cases hTe : T = []
            · -- 兄弟が空: ブロックは p :: A
              subst hTe
              have hAne : A ≠ [] := by
                intro he; rw [he] at hrne; simp at hrne
              have hA1 : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
              have hAlen : ((bd, y) :: (A ++ [])).length = A.length + 1 := by simp
              have hlastA : ((bd, y) :: (A ++ [])).getLastD (0, 0) = A.getLastD (0, 0) := by
                rw [List.append_nil]; exact getLastD_cons_ne _ hAne _
              have hlevA : entry A 1 (A.length - 1) = 0 := by
                rw [entry_last, ← hlastA]; exact hlplev
              have hiA : idx1 A (A.length - 1) = 0 := by
                rw [idx1, if_neg (by rw [hlevA]; omega)]
              have hzA : ¬ (entry A 0 (A.length - 1) = 0 ∧ entry A 1 (A.length - 1) = 0) := by
                rintro ⟨h1, -⟩
                rw [entry_last0, ← hlastA] at h1
                omega
              have hidx : ((bd, y) :: (A ++ [])).length - 1
                  = ([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1) := by
                simp only [List.length_cons, List.length_nil, List.append_nil]
                omega
              have hBeq : ((bd, y) :: (A ++ [])) = [((bd, y) : ℕ × ℕ)] ++ A := by simp
              by_cases hj00 : parent ((bd, y) :: (A ++ []))
                  0 (((bd, y) :: (A ++ [])).length - 1) = 0
              · -- 場合 (d): 親が節点
                have hnr0 : nextrel0 ((bd, y) :: (A ++ [])) 0
                    (((bd, y) :: (A ++ [])).length - 1) := by
                  rw [← hj00]; exact hnrp
                have hBA : ((bd, y) :: (A ++ [])) = (((bd, y) : ℕ × ℕ) :: A) := by simp
                have hmin : ∀ c ∈ A, (A.getLastD (0, 0)).1 ≤ c.1 := by
                  intro c hcm
                  obtain ⟨i, hi, hei⟩ := entry_of_mem hcm
                  rw [hBA] at hnr0
                  have key : entry (((bd, y) : ℕ × ℕ) :: A) 0
                      ((((bd, y) : ℕ × ℕ) :: A).length - 1)
                      ≤ entry (((bd, y) : ℕ × ℕ) :: A) 0 (i + 1) := by
                    rcases Nat.lt_or_ge (i + 1) ((((bd, y) : ℕ × ℕ) :: A).length - 1)
                      with hlt | hge
                    · exact hnr0.2.2.2.2 (i + 1) ⟨by omega, hlt⟩
                    · have hie : i + 1 = (((bd, y) : ℕ × ℕ) :: A).length - 1 := by
                        simp only [List.length_cons] at hge ⊢
                        omega
                      rw [hie]
                  have h1 : entry (((bd, y) : ℕ × ℕ) :: A) 0 (i + 1) = entry A 0 i :=
                    entry_cons_succ _ _ _ _
                  have h2 : entry (((bd, y) : ℕ × ℕ) :: A) 0 ((A.length - 1) + 1)
                      = entry A 0 (A.length - 1) := entry_cons_succ _ _ _ _
                  have h3 : (((bd, y) : ℕ × ℕ) :: A).length - 1 = (A.length - 1) + 1 := by
                    simp only [List.length_cons]
                    omega
                  rw [h3, h2, h1] at key
                  rw [← hei, ← entry_last0]
                  exact key
                have hlevA' : (A.getLastD (0, 0)).2 = 0 := by rw [← hlastA]; exact hlplev
                by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
                · -- 梯子つき: `fOK` が `force` を潰し、`d = p.2` が出る
                  have hlad2 : first = true ∧ ((bd, y) : ℕ × ℕ).2 = plev + 1
                      ∧ (d ≤ ((bd, y) : ℕ × ℕ).2 ∨ force = true) := by
                    unfold ladOf at hlad
                    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
                      decide_eq_true_eq] at hlad
                    exact ⟨hlad.1.1, hlad.1.2, hlad.2⟩
                  have hdy : d ≤ ((bd, y) : ℕ × ℕ).2 := by
                    rcases hlad2.2.2 with hh | hh
                    · exact hh
                    · rcases hFC hh with h1 | h2
                      · exact absurd hlad2.2.1 (h1 ((bd, y) : ℕ × ℕ) (A ++ []) rfl)
                      · have hpp := hlad2.2.1
                        simp only [] at hpp ⊢
                        omega
                  have hyd : ((bd, y) : ℕ × ℕ).2 ≤ ((bd, y) : ℕ × ℕ).1 :=
                    hc _ (by simp)
                  have hdp : d = ((bd, y) : ℕ × ℕ).2 := by
                    simp only [] at hdy hyd ⊢
                    omega
                  obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_lad_shape hAne hAdeep hmin
                    hlevA' d plev first force hlad hdp n hn
                  exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
                · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                    cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                    | false => rfl
                    | true => exact absurd hx hlad
                  by_cases hfr : (first && (((bd, y) : ℕ × ℕ).2 == plev)) = true
                  · -- `hpOK` で潰す枝
                    have hf1 : first = true := by
                      simp only [Bool.and_eq_true, beq_iff_eq] at hfr; exact hfr.1
                    have hpl : ((bd, y) : ℕ × ℕ).2 = plev := by
                      simp only [Bool.and_eq_true, beq_iff_eq] at hfr; exact hfr.2
                    rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
                    · have hkey := hh ((bd, y) : ℕ × ℕ) (A ++ []) rfl hpl
                        (by rw [e1]; exact hAne)
                      rw [e1] at hkey
                      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_gen2_shape hAne hAdeep
                        hmin hlevA' d plev first force hnl hkey n hn
                      exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
                    · -- 根: `conC` そのものなので `reindexD_node0` が効く
                      subst hd0; subst hpl0; subst hfc0; subst hf1
                      have hbd0 : bd = 0 := by omega
                      have hy0 : y = 0 := by
                        have hyc := hc ((bd, y) : ℕ × ℕ) (by simp)
                        simp only [] at hyc
                        omega
                      have hhd0 : ((bd, y) :: (A ++ [])).headI = ((0, 0) : ℕ × ℕ) := by
                        show ((bd, y) : ℕ × ℕ) = ((0, 0) : ℕ × ℕ)
                        rw [hbd0, hy0]
                      obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_shape n hn hL2
                        (contrOK_of_last_zero hlev) hhd0 hlev hnr0
                      simp only [conC] at k3
                      exact ⟨m, n', k1, k2, k3⟩
                  · have hfr' : (first && (((bd, y) : ℕ × ℕ).2 == plev)) = false := by
                      cases hx : (first && (((bd, y) : ℕ × ℕ).2 == plev)) with
                      | false => rfl
                      | true => exact absurd hx hfr
                    obtain ⟨m, n', k1, k2, k3⟩ := reindexD_node0_gen_shape hAne hAdeep hmin
                      hlevA' d plev first force hnl hfr' n hn
                    exact ⟨m, n', k1, k2, by rw [List.append_nil]; exact k3⟩
              · -- 場合 (c): 引数ブロックへ降りる
                have hge1 : 1 ≤ parent ((bd, y) :: (A ++ [])) 0
                    (((bd, y) :: (A ++ [])).length - 1) := by omega
                have hpB : hasParent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                    (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
                  rw [hiA, ← hidx, ← hBeq]; exact hpar
                have hgeB : ([((bd, y) : ℕ × ℕ)] : PairSeq).length
                    ≤ parent ([((bd, y) : ℕ × ℕ)] ++ A) (idx1 A (A.length - 1))
                        (([((bd, y) : ℕ × ℕ)] : PairSeq).length + (A.length - 1)) := by
                  rw [hiA, ← hidx, ← hBeq]
                  simpa using hge1
                by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
                · have hIH := ih A (by omega) (bd + 1) (d + 2) ((bd, y) : ℕ × ℕ).2 true false
                    hbA hcA hdA (by omega) (by omega) hlevA hAPa
                    (hpOK_of_headPatOK hAPh) fOK_false hACa (fun _ => hACh)
                  have hres := reindexD_arg_lad (p := ((bd, y) : ℕ × ℕ)) hAdeep hlad hbA hcA hdA
                    (by omega) hzA hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
                · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                    cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                    | false => rfl
                    | true => exact absurd hx hlad
                  have hIH := ih A (by omega) (bd + 1)
                    (ddOf ((bd, y) : ℕ × ℕ).2 d plev first force + 1)
                    ((bd, y) : ℕ × ℕ).2 true (first && (((bd, y) : ℕ × ℕ).2 == plev))
                    hbA hcA hdA
                    (by have := le_ddOf ((bd, y) : ℕ × ℕ).2 d plev first force; omega)
                    (by omega) hlevA hAPa (hpOK_of_headPatOK hAPh) hfA hACa (fun _ => hACh)
                  have hres := reindexD_arg_nolad (p := ((bd, y) : ℕ × ℕ)) hAdeep hnl hbA hcA hdA
                    (by omega) hzA hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  exact ⟨m, n', k1, k2, by rw [← hBeq] at k3; exact k3⟩
            · -- 兄弟が空でない: 親は兄弟の中にある
              have hTne : T ≠ [] := hTe
              have hT1 : 1 ≤ T.length := List.length_pos_of_ne_nil hTne
              have hTh : ¬ (((bd, y) : ℕ × ℕ).1 < (T.headI).1) := by
                rcases hThd with h | h
                · exact absurd h hTne
                · exact h
              have hBeq : ((bd, y) :: (A ++ T))
                  = (((bd, y) : ℕ × ℕ) :: A) ++ T := by simp
              have hidx : ((bd, y) :: (A ++ T)).length - 1
                  = (((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1) := by
                simp only [List.length_cons, List.length_append]
                omega
              have hlastT : ((bd, y) :: (A ++ T)).getLastD (0, 0) = T.getLastD (0, 0) := by
                rw [hBeq]; exact getLastD_append_right hTne _
              have hlevT : entry T 1 (T.length - 1) = 0 := by
                rw [entry_last, ← hlastT]; exact hlplev
              have hiT : idx1 T (T.length - 1) = 0 := by
                rw [idx1, if_neg (by rw [hlevT]; omega)]
              have hzT : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0) := by
                rintro ⟨h1, -⟩
                rw [entry_last0, ← hlastT] at h1
                omega
              -- 親は `p :: A` より後ろ
              have hgeT : (((bd, y) : ℕ × ℕ) :: A).length
                  ≤ parent ((bd, y) :: (A ++ T)) 0 (((bd, y) :: (A ++ T)).length - 1) := by
                by_contra hlt
                have hlt' : parent ((bd, y) :: (A ++ T)) 0
                    (((bd, y) :: (A ++ T)).length - 1)
                    < (((bd, y) : ℕ × ℕ) :: A).length := by omega
                have hhead : entry ((bd, y) :: (A ++ T)) 0
                    ((((bd, y) : ℕ × ℕ) :: A).length) = (T.headI).1 := by
                  rw [hBeq,
                    show (((bd, y) : ℕ × ℕ) :: A).length
                      = (((bd, y) : ℕ × ℕ) :: A).length + 0 by omega,
                    entry_append_right, entry_zero0]
                have hthead : (T.headI).1 ≤ bd := by omega
                rcases Nat.lt_or_ge ((((bd, y) : ℕ × ℕ) :: A).length)
                    (((bd, y) :: (A ++ T)).length - 1) with hcase | hcase
                · have := hnrp.2.2.2.2 ((((bd, y) : ℕ × ℕ) :: A).length) ⟨by omega, hcase⟩
                  rw [entry_last0, hhead] at this
                  omega
                · have heq : (((bd, y) : ℕ × ℕ) :: A).length
                      = ((bd, y) :: (A ++ T)).length - 1 := by
                    simp only [List.length_cons, List.length_append] at hcase ⊢
                    omega
                  rw [heq, entry_last0] at hhead
                  omega
              have hpB : hasParent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                  ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
                rw [hiT, ← hidx, ← hBeq]; exact hpar
              have hgeB : (((bd, y) : ℕ × ℕ) :: A).length
                  ≤ parent ((((bd, y) : ℕ × ℕ) :: A) ++ T) (idx1 T (T.length - 1))
                      ((((bd, y) : ℕ × ℕ) :: A).length + (T.length - 1)) := by
                rw [hiT, ← hidx, ← hBeq]; exact hgeT
              have hIH := ih T (by omega) bd d ((bd, y) : ℕ × ℕ).2 false false
                hbT hcT hdT hbd hz0 hlevT hAPt hpOK_false fOK_false hACt hcOK_false
              by_cases hlad : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = true
              · have hlad2 : first = true ∧ ((bd, y) : ℕ × ℕ).2 = plev + 1
                    ∧ (d ≤ ((bd, y) : ℕ × ℕ).2 ∨ force = true) := by
                  unfold ladOf at hlad
                  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
                    decide_eq_true_eq] at hlad
                  exact ⟨hlad.1.1, hlad.1.2, hlad.2⟩
                have hcth : contrLen' ((bd, y) : ℕ × ℕ) T (unitsLen ((bd, y) : ℕ × ℕ) T) A
                    = contrLen ((bd, y) : ℕ × ℕ) T (unitsLen ((bd, y) : ℕ × ℕ) T) A := by
                  have hx := hHC hlad2.1 ((bd, y) : ℕ × ℕ) (A ++ T) rfl hlad2.2.1
                  rw [e1, e2] at hx
                  exact hx
                by_cases hnc : contrLen ((bd, y) : ℕ × ℕ) T
                    (unitsLen ((bd, y) : ℕ × ℕ) T) A = none
                · have hres := reindexD_sib_lad2 (p := ((bd, y) : ℕ × ℕ)) hAdeep hTh hlad hnc
                    (fun k hk => Hp ((bd, y) : ℕ × ℕ) A T bd hb hc hd rfl hAdeep hThd hcth
                      hnc k hk)
                    hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
                  obtain ⟨m, n', k1, k2, k3⟩ := hres
                  rw [← hBeq] at k3
                  exact ⟨m, n', k1, k2, k3⟩
                · obtain ⟨rest2, Bq, hcc⟩ : ∃ rest2 Bq, contrLen ((bd, y) : ℕ × ℕ) T
                      (unitsLen ((bd, y) : ℕ × ℕ) T) A = some (rest2, Bq) := by
                    rcases hx : contrLen ((bd, y) : ℕ × ℕ) T
                        (unitsLen ((bd, y) : ℕ × ℕ) T) A with _ | ⟨r2, bq⟩
                    · exact absurd hx hnc
                    · exact ⟨r2, bq, rfl⟩
                  obtain ⟨qq, U, pre, hU, hTeq, hq2, hq1, hpre, hpd, hrd, hBqh,
                    hrne, hrh1, hrh2⟩ := contrLen_shape hcc
                  exact reindexD_zero_fire3 N ih hB hb hc hd hbd hz0 rfl hlev hAP hAC hFC
                    hAdeep hlad hpar hU hTeq hq2 hq1 hpre hpd hrd hBqh hrne hrh1 hrh2 n hn
              · have hnl : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force = false := by
                  cases hx : ladOf ((bd, y) : ℕ × ℕ).2 d plev first force with
                  | false => rfl
                  | true => exact absurd hx hlad
                have hres := reindexD_sib_nolad (p := ((bd, y) : ℕ × ℕ)) hAdeep hTh hnl
                  hbT hcT hdT (by omega) hzT hpB hgeB hIH n hn
                obtain ⟨m, n', k1, k2, k3⟩ := hres
                rw [← hBeq] at k3
                exact ⟨m, n', k1, k2, k3⟩
          · -- 場合 (b): 親がない
            exact reindexD_noParent_zero d plev first force hL2 hlev hz hpar n hn

/-- **段 0 の入口（残余は `CtrRes` と `CtrPres2` だけ）**。 -/
theorem reindexD_zero5 (Hc : CtrRes) (Hp : CtrPres2)
    {M : PairSeq} (hM : ST_PS M) (hlev : entry M 1 (M.length - 1) = 0) :
    ∀ n : ℕ, 1 ≤ n → ∃ m n' : ℕ, 1 ≤ m ∧ n ≤ n' ∧ (conC M)⟦m⟧ = conC (M⟦n'⟧) := by
  intro n hn
  have h := reindexD_zero_block5 Hp M.length M (Nat.le_refl _) 0 0 0 true false
    (blockok_ST_PS hM) (colOK_ST_PS hM) (descOK_ST_PS hM) (Nat.le_refl 0)
    (fun _ => rfl) hlev (argPatOK_ST_PS hM)
    (fun _ => Or.inr ⟨rfl, rfl, rfl⟩) fOK_false (Hc hM)
    (fun _ => ctrHeadOK_root (blockok_ST_PS hM) (colOK_ST_PS hM)) n hn
  obtain ⟨m, n', h1, h2, h3⟩ := h
  exact ⟨m, n', h1, h2, by rw [conC, conC]; exact h3⟩

/-- **到達点**: `ReindexD` の残余は
`CtrRes` / `CtrPres2` / `RDnopar` / `RDnode` の 4 つだけになった。
梯子つきの縮約（旧 `RDzeroRes2` / `RDlad2`）は完全に消えた。 -/
theorem reindexD_holds_of_res7 (Hc : CtrRes) (Hp : CtrPres2)
    (Hn : RDnopar) (Hd : RDnode) : ReindexD := by
  intro A hA hL n hn
  by_cases hz : entry A 1 (A.length - 1) = 0
  · exact reindexD_zero5 Hc Hp hA hz n hn
  · exact reindexD_pos_of4 Hc Hp Hn Hd hA hL (by omega) n hn

/-- 同じ形で主定理まで。 -/
theorem ST_D_conC_holds_of_res7 (Hc : CtrRes) (Hp : CtrPres2)
    (Hn : RDnopar) (Hd : RDnode) {M : PairSeq} (hM : ST_PS M) : ST_D (conC M) :=
  ST_D_conC (reindexD_holds_of_res7 Hc Hp Hn Hd) hM


/-! ## 4.20 `CtrRes` を `ArgDomCore` から証明する

`ctrHeadOK` の中身は「縮約の前置きが揃えば、その次の列の段は必ず下がる」。
節点 `c = (u, w)` の引数ブロックの頭を `p` とすると `p = (u+1, w+1)` で、
縮約の前置きが揃うとは「兄弟 `q = (u+1, w)` の引数が
`contrPre p U A = shiftr0 1 (p :: (A ++ U))` で始まる」ということである。

ここで `c` と `q` は**行 1 の値が同じ** `w` で、深さが `u` と `u+1`（`e = 1`）。
その間の列（`p :: (A ++ U)`）はすべて深さ `≥ u+1` なので `SpineOK` は空虚に成り立つ。
したがって `ArgDomCore` がそのまま使えて

    sle Aq (shiftr0 1 ((p :: (A ++ U)) ++ q :: (Aq ++ Bq)))

を得る。右辺の頭 `shiftr0 1 (p :: (A ++ U))` はちょうど `contrPre p U A`
（`contrPre_eq_shiftr0`）なので、共通の前置きを `seqlex_append_cancel` で消すと

    sle rest2 ((u+2, w) :: ...)

が残る。`rest2` の頭の深さは `p.1 + 1 = u+2` なので列辞書式順序から段は `w` 以下。
`p.2 = w + 1` だから `(rest2.headI).2 < p.2`、すなわち `ctrHeadOK` である。 -/

/-- `contrLen'` が返す形を読み解く（`contrLen_spec` の段の条件なし版）。 -/
theorem contrLen'_spec {p : ℕ × ℕ} {B A rest2 Bq : PairSeq} {k : ℕ}
    (h : contrLen' p B k A = some (rest2, Bq)) :
    ∃ q r2, B.drop k = q :: r2 ∧ q.2 + 1 = p.2 ∧ q.1 = p.1 ∧
      (r2.takeWhile fun x => q.1 < x.1) = contrPre p (B.take k) A ++ rest2 ∧
      (r2.dropWhile fun x => q.1 < x.1) = Bq ∧
      rest2 ≠ [] ∧ (rest2.headI).1 = p.1 + 1 := by
  unfold contrLen' at h
  rcases hd : B.drop k with _ | ⟨q, r2⟩ <;> rw [hd] at h
  · simp at h
  · refine ⟨q, r2, rfl, ?_⟩
    simp only [] at h
    split at h
    · rename_i hcond
      obtain ⟨c1, c2, c3, c4, c5⟩ := hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      refine ⟨c1, c2, ?_, rfl, c4, c5⟩
      conv_lhs => rw [← List.take_append_drop (contrPre p (B.take k) A).length
        (r2.takeWhile fun x => q.1 < x.1)]
      rw [c3]
    · simp at h

/-- 段が下がることさえ言えれば `contrLen'` と `contrLen` は一致する。 -/
theorem contrLen_eq_of_head_lt (p : ℕ × ℕ) (B A : PairSeq) (k : ℕ)
    (h : ∀ rest2 Bq : PairSeq, contrLen' p B k A = some (rest2, Bq) → (rest2.headI).2 < p.2) :
    contrLen' p B k A = contrLen p B k A := by
  unfold contrLen' at h ⊢
  unfold contrLen
  rcases hd : B.drop k with _ | ⟨q, r2⟩
  · rfl
  · rw [hd] at h
    simp only [] at h ⊢
    by_cases hc : q.2 + 1 = p.2 ∧ q.1 = p.1 ∧
        (r2.takeWhile fun x => q.1 < x.1).take (contrPre p (B.take k) A).length
          = contrPre p (B.take k) A ∧
        (r2.takeWhile fun x => q.1 < x.1).drop (contrPre p (B.take k) A).length ≠ [] ∧
        (((r2.takeWhile fun x => q.1 < x.1).drop
            (contrPre p (B.take k) A).length).headI).1 = p.1 + 1
    · have hlt := h _ _ (by rw [if_pos hc])
      rw [if_pos hc, if_pos ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, hlt⟩]
    · rw [if_neg hc, if_neg (by
        intro hcc
        exact hc ⟨hcc.1, hcc.2.1, hcc.2.2.1, hcc.2.2.2.1, hcc.2.2.2.2.1⟩)]

/-- **`ArgDomCore` の一発適用**（分解済みの形）。`c` と `q` は行 1 が同じ `c.2`、
深さが `c.1` と `c.1 + 1` なので、`e = 1` の `ArgDomCore` が使える。 -/
theorem ctrHead_lt_core {M X A U Bq Z : PairSeq} {c p q : ℕ × ℕ} {rest2 : PairSeq}
    (hM : ST_PS M)
    (hMform : M = (X ++ c :: ((p :: (A ++ U))
        ++ q :: ((contrPre p U A ++ rest2) ++ Bq))) ++ Z)
    (hArgd : ∀ x ∈ ((p :: (A ++ U)) ++ q :: ((contrPre p U A ++ rest2) ++ Bq)), c.1 < x.1)
    (hp1 : p.1 = c.1 + 1) (hq1 : q.1 = p.1) (hq2 : q.2 = c.2)
    (hAqd : ∀ x ∈ (contrPre p U A ++ rest2), q.1 < x.1)
    (hBqh : Bq = [] ∨ ¬ (q.1 < (Bq.headI).1))
    (hZh : Z = [] ∨ ¬ (c.1 < (Z.headI).1))
    (hrne : rest2 ≠ []) (hrh1 : (rest2.headI).1 = p.1 + 1) :
    (rest2.headI).2 ≤ c.2 := by
  have hqeq : q = ((c.1 + 1, c.2) : ℕ × ℕ) := by
    have h1 : q.1 = c.1 + 1 := by omega
    exact Prod.ext h1 hq2
  have hST : ST_PS ((X ++ (c.1, c.2) :: ((p :: (A ++ U))
      ++ (c.1 + 1, c.2) :: ((contrPre p U A ++ rest2) ++ Bq))) ++ Z) := by
    rw [show ((c.1, c.2) : ℕ × ℕ) = c from rfl, ← hqeq, ← hMform]; exact hM
  have hA1d : ∀ x ∈ (p :: (A ++ U)), c.1 < x.1 := by
    intro x hx; exact hArgd x (List.mem_append_left _ hx)
  have hBd : ∀ x ∈ (contrPre p U A ++ rest2), c.1 + 1 < x.1 := by
    intro x hx
    have := hAqd x hx
    omega
  have hA2d : ∀ x ∈ Bq, c.1 < x.1 := by
    intro x hx
    exact hArgd x (List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_append_right _ hx)))
  have hA2h : Bq = [] ∨ (Bq.headI).1 ≤ c.1 + 1 := by
    rcases hBqh with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hZh' : Z = [] ∨ (Z.headI).1 ≤ c.1 := by
    rcases hZh with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hspine : SpineOK (p :: (A ++ U)) (c.1 + 1) c.2 := by
    intro V W x hA1 hxlt _
    exfalso
    have hx : x ∈ (p :: (A ++ U)) := by rw [hA1]; exact List.mem_append_right _ (by simp)
    have := hA1d x hx
    omega
  have hsle := argDomCore_holds (X := X) (A1 := p :: (A ++ U))
    (B := contrPre p U A ++ rest2) (A2 := Bq) (Z := Z) (u := c.1) (w := c.2) (e := 1)
    hST Nat.one_pos hA1d hBd hA2d hA2h hZh' hspine
  have hRHS : shiftr0 1 ((p :: (A ++ U)) ++ (c.1 + 1, c.2) :: ((contrPre p U A ++ rest2) ++ Bq))
      = contrPre p U A
        ++ ((c.1 + 1 + 1, c.2) :: shiftr0 1 ((contrPre p U A ++ rest2) ++ Bq)) := by
    rw [shiftr0_append 1 (p :: (A ++ U)) ((c.1 + 1, c.2) :: ((contrPre p U A ++ rest2) ++ Bq)),
      ← contrPre_eq_shiftr0 p U A,
      shiftr0_cons 1 ((c.1 + 1, c.2) : ℕ × ℕ) ((contrPre p U A ++ rest2) ++ Bq)]
  rw [hRHS] at hsle
  rcases rest2 with _ | ⟨z, rs⟩
  · exact absurd rfl hrne
  · have hz1 : z.1 = c.1 + 1 + 1 := by
      simp only [List.headI_cons] at hrh1; omega
    rcases hsle with heq2 | hlex
    · have hcut : z :: rs
          = (c.1 + 1 + 1, c.2) :: shiftr0 1 ((contrPre p U A ++ z :: rs) ++ Bq) :=
        List.append_cancel_left heq2
      rw [hcut]; simp
    · rw [seqlex_append_cancel] at hlex
      rcases hlex with hpl | ⟨hzz, -⟩
      · rcases hpl with hlt | ⟨-, hlt⟩
        · exfalso
          have hlt' : z.1 < c.1 + 1 + 1 := hlt
          omega
        · have hlt' : z.2 < c.2 := hlt
          simp only [List.headI_cons]
          omega
      · rw [hzz]; simp

/-- 節点 `c` の引数ブロックについて `ctrHeadOK` が成り立つ。 -/
theorem ctrHeadOK_arg_of_ST {M X r : PairSeq} {c : ℕ × ℕ}
    (hM : ST_PS M) (heq : M = X ++ c :: r) :
    ctrHeadOK (r.takeWhile fun x => c.1 < x.1) c.2 := by
  intro p r' harg hp2
  refine contrLen_eq_of_head_lt p _ _ _ ?_
  intro rest2 Bq hcl
  obtain ⟨q, r2, hdq, hq2, hq1, hAq, hBq, hrne, hrh1⟩ := contrLen'_spec hcl
  have hArgd : ∀ x ∈ (r.takeWhile fun x => c.1 < x.1), c.1 < x.1 := by
    intro x hx
    simpa using List.mem_takeWhile_imp (p := fun z : ℕ × ℕ => decide (c.1 < z.1)) hx
  have hrsplit : (r.takeWhile fun x => c.1 < x.1) ++ (r.dropWhile fun x => c.1 < x.1) = r :=
    List.takeWhile_append_dropWhile
  have hZh : (r.dropWhile fun x => c.1 < x.1) = []
      ∨ ¬ (c.1 < ((r.dropWhile fun x => c.1 < x.1).headI).1) := dropWhile_head_neg r
  have hr'split : (r'.takeWhile fun x => p.1 < x.1) ++ (r'.dropWhile fun x => p.1 < x.1) = r' :=
    List.takeWhile_append_dropWhile
  set Arg := r.takeWhile (fun x => c.1 < x.1) with hArgdef
  set Z := r.dropWhile (fun x => c.1 < x.1) with hZdef
  set A := r'.takeWhile (fun x => p.1 < x.1) with hAdef
  set T := r'.dropWhile (fun x => p.1 < x.1) with hTdef
  set k := unitsLen p T with hkdef
  set U := T.take k with hUdef
  have hTsplit : U ++ q :: r2 = T := by
    rw [hUdef, ← hdq, List.take_append_drop]
  have hr2split : ((contrPre p U A ++ rest2) ++ Bq) = r2 := by
    rw [← hAq, ← hBq]; exact List.takeWhile_append_dropWhile
  have hArgeq : Arg = (p :: (A ++ U)) ++ q :: ((contrPre p U A ++ rest2) ++ Bq) := by
    rw [harg, hr2split, ← hr'split, ← hTsplit]
    simp [List.append_assoc]
  have hMform : M = ((X ++ c :: ((p :: (A ++ U))
      ++ q :: ((contrPre p U A ++ rest2) ++ Bq))) ++ Z) := by
    rw [← hArgeq, heq, ← hrsplit]
    simp [List.append_assoc]
  have hrp : r = p :: (r' ++ Z) := by rw [← hrsplit, harg]; simp
  have hcp : c.1 < p.1 := hArgd p (by rw [harg]; simp)
  have hp1 : p.1 = c.1 + 1 := by
    have hsteps : steps1 M := (blockok_ST_PS hM).2.2
    rw [heq, hrp] at hsteps
    have h2 := (steps1_append.1 hsteps).2.1
    have h3 := (steps1_cons_cons.1 h2).1
    omega
  have hArgd' : ∀ x ∈ ((p :: (A ++ U)) ++ q :: ((contrPre p U A ++ rest2) ++ Bq)),
      c.1 < x.1 := by
    rw [← hArgeq]; exact hArgd
  have hAqd : ∀ x ∈ (contrPre p U A ++ rest2), q.1 < x.1 := by
    intro x hx
    rw [← hAq] at hx
    simpa using List.mem_takeWhile_imp (p := fun z : ℕ × ℕ => decide (q.1 < z.1)) hx
  have hBqh : Bq = [] ∨ ¬ (q.1 < (Bq.headI).1) := by
    rw [← hBq]; exact dropWhile_head_neg r2
  have hkey := ctrHead_lt_core hM hMform hArgd' hp1 hq1 (by omega) hAqd hBqh hZh hrne hrh1
  omega

/-- 全部の節点で `ctrHeadOK` が成り立てば `argCtrOK`。 -/
theorem argCtrOK_of_nodes : ∀ (N : ℕ) (M : PairSeq), M.length ≤ N →
    (∀ (X r : PairSeq) (c : ℕ × ℕ), M = X ++ c :: r →
      ctrHeadOK (r.takeWhile fun x => c.1 < x.1) c.2) → argCtrOK M := by
  intro N
  induction N with
  | zero =>
    intro M hMl _
    have : M = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; exact argCtrOK_nil
  | succ N ih =>
    intro M hMl hN
    match M with
    | [] => exact argCtrOK_nil
    | p :: r =>
      have hlenT : (r.takeWhile fun q => p.1 < q.1).length ≤ N := by
        have := (List.takeWhile_sublist (p := fun q : ℕ × ℕ => decide (p.1 < q.1))
          (l := r)).length_le
        simp only [List.length_cons] at hMl; omega
      have hlenD : (r.dropWhile fun q => p.1 < q.1).length ≤ N := by
        have := List.length_dropWhile_le (fun q : ℕ × ℕ => decide (p.1 < q.1)) r
        simp only [List.length_cons] at hMl; omega
      have hsplit : (r.takeWhile fun q => p.1 < q.1) ++ (r.dropWhile fun q => p.1 < q.1) = r :=
        List.takeWhile_append_dropWhile
      rw [argCtrOK_cons]
      refine ⟨hN [] r p rfl, ?_, ?_⟩
      · refine ih _ hlenT ?_
        intro X r'' c hEq
        have hcmem : c ∈ (r.takeWhile fun q => p.1 < q.1) := by rw [hEq]; simp
        have hcd : p.1 < c.1 := by
          simpa using List.mem_takeWhile_imp (p := fun z : ℕ × ℕ => decide (p.1 < z.1)) hcmem
        have hDh : (r.dropWhile fun q => p.1 < q.1) = []
            ∨ ¬ (c.1 < ((r.dropWhile fun q => p.1 < q.1).headI).1) := by
          rcases dropWhile_head_neg (a := p.1) r with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
        have hM2 : (p :: r) = (p :: X) ++ c :: (r'' ++ (r.dropWhile fun q => p.1 < q.1)) := by
          conv_lhs => rw [← hsplit, hEq]
          simp [List.append_assoc]
        have hkey := hN (p :: X) (r'' ++ (r.dropWhile fun q => p.1 < q.1)) c hM2
        rw [(split_append_gen hDh r'').1] at hkey
        exact hkey
      · refine ih _ hlenD ?_
        intro X r'' c hEq
        refine hN (p :: ((r.takeWhile fun q => p.1 < q.1) ++ X)) r'' c ?_
        conv_lhs => rw [← hsplit, hEq]
        simp [List.append_assoc]

/-- **`CtrRes` は定理**（`ArgDomCore` から）。残余が 1 つ減る。 -/
theorem ctrRes_holds : CtrRes := by
  intro M hM
  exact argCtrOK_of_nodes M.length M (Nat.le_refl _)
    (fun X r c heq => ctrHeadOK_arg_of_ST hM heq)

/-- **到達点**: `ReindexD` の残余は `CtrPres2` / `RDnopar` / `RDnode` の 3 つ。 -/
theorem reindexD_holds_of_res8 (Hp : CtrPres2) (Hn : RDnopar) (Hd : RDnode) : ReindexD :=
  reindexD_holds_of_res7 ctrRes_holds Hp Hn Hd

/-- 同じ形で主定理まで。 -/
theorem ST_D_conC_holds_of_res8 (Hp : CtrPres2) (Hn : RDnopar) (Hd : RDnode)
    {M : PairSeq} (hM : ST_PS M) : ST_D (conC M) :=
  ST_D_conC_holds_of_res7 ctrRes_holds Hp Hn Hd hM

/-! ## 4.21 `RDnopar`: `contrOK` を不変量に置き換える

`convC_dropLast_noParent_aux` が要求する `contrOK` は**本当に偽になりうる**
（`B = (2,2)(2,1)(3,2)(3,1)` は `contrOK` を満たさないが `RDnopar` の入力になる）。
壊れる形は「梯子が立つ段で縮約が `some ([x], [])` に発火し `x.2 > 0`」だけで、
`x.2 < p.2` だから `p.2 ≥ 2` が要る。ところが不変量から

    梯子が立つ ⟹ p.2 ≤ 1        （`lad_lev_le_one`）

が出る。実際、梯子は `d ≤ p.2 ∨ force` を要求し、`force` の場合は `fOK` が
`d ≤ plev + 1 = p.2` を与える。`p.2 ≤ p.1 = bd ≤ d` と合わせて
`d = p.2 = bd = p.1`、そこで `dpOK` が `plev = 0`（すなわち `p.2 = 1`）を強いる。

そこで `contrOK` を `blockok` / `colOK` / `bd ≤ d` / `argPatOK` / `dpOK` /
`hpOK` / `fOK` に置き換えた `convC_dropLast_noParent_aux2` を作る。 -/

/-- **梯子が立つなら頭の段は 1 以下**（不変量から）。 -/
theorem lad_lev_le_one {p : ℕ × ℕ} {r : PairSeq} {bd d plev : ℕ} {first force : Bool}
    (hp1 : p.1 = bd) (hcol : p.2 ≤ p.1) (hbd : bd ≤ d)
    (hdp : dpOK bd d plev first) (hf : fOK (p :: r) d plev force)
    (hlad : ladOf p.2 d plev first force = true) : p.2 ≤ 1 := by
  unfold ladOf at hlad
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hlad
  obtain ⟨⟨hf1, hpl⟩, hor⟩ := hlad
  have hdle : d ≤ p.2 := by
    rcases hor with hh | hh
    · exact hh
    · rcases hf hh with h1 | h2
      · exact absurd hpl (h1 p r rfl)
      · omega
  have hdbd : d = bd := by omega
  rcases hdp hf1 hdbd with h | h <;> omega

/-- 引数ブロックの `blockok`（頭を `(bd, y)` に分解しない版）。 -/
theorem blockok_arg' {p : ℕ × ℕ} {A B : PairSeq} {bd : ℕ}
    (hb : blockok bd (p :: (A ++ B))) (hp1 : p.1 = bd) (hAd : ∀ x ∈ A, p.1 < x.1) :
    blockok (bd + 1) A := by
  refine ⟨?_, fun x hx => by have := hAd x hx; omega, ?_⟩
  · intro hne
    obtain ⟨a, as, ha⟩ : ∃ a as, A = a :: as := by
      cases A with
      | nil => exact absurd rfl hne
      | cons a as => exact ⟨a, as, rfl⟩
    have h1 : p.1 < a.1 := hAd a (by rw [ha]; simp)
    have h2 : a.1 ≤ p.1 + 1 := by
      have hs := hb.2.2
      rw [ha] at hs
      simp only [List.cons_append, steps1_cons_cons] at hs
      exact hs.1
    rw [ha]; simp only [List.headI]; omega
  · exact (steps1_append.1 (steps1_tail hb.2.2)).1

/-- 兄弟ブロックの `blockok`。 -/
theorem blockok_sib' {p : ℕ × ℕ} {A B : PairSeq} {bd : ℕ}
    (hb : blockok bd (p :: (A ++ B))) (hp1 : p.1 = bd)
    (hBh : B = [] ∨ ¬ (p.1 < (B.headI).1)) : blockok bd B := by
  refine ⟨?_, ?_, ?_⟩
  · intro hne
    have h1 : bd ≤ (B.headI).1 := hb.2.1 _ (List.mem_cons_of_mem _
      (List.mem_append_right _ (headI_mem hne)))
    have h2 : ¬ (p.1 < (B.headI).1) := hBh.resolve_left hne
    omega
  · intro x hx
    exact hb.2.1 x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
  · exact (steps1_append.1 (steps1_tail hb.2.2)).2.1

theorem steps1_suffix {L M : PairSeq} (h : L <:+ M) (hs : steps1 M) : steps1 L := by
  obtain ⟨t, ht⟩ := h
  rw [← ht] at hs
  exact (steps1_append.1 hs).2.1

theorem colOK_of_suffix {L M : PairSeq} (h : L <:+ M) (hc : colOK M) : colOK L :=
  fun x hx => hc x (h.subset hx)

/-- **場合 (b) の `dropLast`（不変量つき）**。`contrOK` は要らない。 -/
theorem convC_dropLast_noParent_aux2 : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n → 1 < M.length →
    ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd M → colOK M → bd ≤ d → argPatOK M →
      dpOK bd d plev first → hpOK M d plev first force → fOK M d plev force →
      ¬ hasParent M (idx1 M (M.length - 1)) (M.length - 1) →
      convC (M.dropLast) d plev first force = (convC M d plev first force).dropLast := by
  intro n
  induction n with
  | zero =>
    intro M hM h1 _ _ _ _ _ _ _ _ _ _ _ _ _
    omega
  | succ n ih =>
    intro M hM h1 bd d plev first force hb hcol hbd hAP hdp hHP hFC hnp
    match M with
    | [] => simp at h1
    | p :: r =>
      obtain ⟨A, B, rfl, hAd, hBh⟩ := split_takeWhile p r
      obtain ⟨e1, e2⟩ := split_append (X := A) (Y := B) (dd := p.1) hAd hBh
      have hp1 : p.1 = bd := by have := hb.1 (by simp); simpa using this
      have hcolp : p.2 ≤ p.1 := hcol p (by simp)
      obtain ⟨hHA, hAPA, hAPB⟩ := argPatOK_cons.1 hAP
      rw [e1] at hHA hAPA
      rw [e2] at hAPB
      by_cases hBe : B = []
      · -- 兄弟が空: 引数ブロック `A` に降りる
        subst hBe
        simp only [List.append_nil] at hb hcol hAP hHP hFC hnp ⊢
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
          have hnpA : ¬ hasParent A (idx1 A (A.length - 1)) (A.length - 1) :=
            noParent_suffix hAne ⟨[p], rfl⟩ hnp
          have hbA : blockok (bd + 1) A :=
            blockok_arg' (B := []) (by simpa using hb) hp1 hAd
          have hcolA : colOK A := fun x hx => hcol x (List.mem_cons_of_mem _ hx)
          have hHPA : ∀ (dd : ℕ) (fc : Bool), hpOK A dd p.2 true fc :=
            fun dd fc => hpOK_of_headPatOK (by simpa using hHA)
          have hdpA1 : dpOK (bd + 1) (d + 2) p.2 true := by intro _ he; omega
          have hdpA2 : dpOK (bd + 1) (ddOf p.2 d plev first force + 1) p.2 true :=
            dpOK_arg hp1 hbd hcolp
          have hbdA1 : bd + 1 ≤ d + 2 := by omega
          have hbdA2 : bd + 1 ≤ ddOf p.2 d plev first force + 1 := by
            have := le_ddOf p.2 d plev first force; omega
          have hAte : (A.takeWhile fun x => p.1 < x.1) = A := by simpa using e1
          have hfA : fOK A (ddOf p.2 d plev first force + 1) p.2
              (first && (p.2 == plev)) := by
            intro hft
            have hf1 : first = true := by
              simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.1
            have hpl : p.2 = plev := by
              simp only [Bool.and_eq_true, beq_iff_eq] at hft; exact hft.2
            rcases hHP hf1 with hh | ⟨hd0, hpl0, hfc0⟩
            · left
              intro a s hs
              have hkey := hh p A rfl hpl (by rw [hAte, hs]; simp)
              rw [hAte, hs] at hkey
              simpa using hkey
            · right
              subst hd0; subst hpl0; subst hfc0
              have hy0 : p.2 = 0 := hpl
              have hz : ddOf p.2 0 0 first false = 0 := by
                unfold ddOf ladOf; simp [hy0]
              omega
          rw [dropLast_cons_ne hAne]
          exact convC_dropLast_arg' p A d plev first force hAd hAne
            (ih A hAlen hA2 (bd + 1) (d + 2) p.2 true false hbA hcolA hbdA1 hAPA
              hdpA1 (hHPA _ _) fOK_false hnpA)
            (ih A hAlen hA2 (bd + 1) (ddOf p.2 d plev first force + 1) p.2 true
              (first && (p.2 == plev)) hbA hcolA hbdA2 hAPA hdpA2 (hHPA _ _) hfA hnpA)
      · -- 兄弟が空でない: 末尾列は `B` の中
        have hBhne : ¬ (p.1 < (B.headI).1) := hBh.resolve_left hBe
        have hABne : A ++ B ≠ [] := by
          intro he; exact hBe (List.append_eq_nil_iff.1 he).2
        have hbB : blockok bd B := blockok_sib' hb hp1 hBh
        have hcolB : colOK B :=
          fun x hx => hcol x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
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
          have hnpB : ¬ hasParent B (idx1 B (B.length - 1)) (B.length - 1) :=
            noParent_suffix hBe ⟨p :: A, rfl⟩ hnp
          have ihB := ih B hBlen hB2 bd d p.2 false false hbB hcolB hbd hAPB
            dpOK_false hpOK_false fOK_false hnpB
          by_cases hl : ladOf p.2 d plev first force = true
          · have hple : p.2 ≤ 1 := lad_lev_le_one hp1 hcolp hbd hdp hFC hl
            rcases hcc : contrLen p B (unitsLen p B) A with _ | ⟨rest2, Bq⟩
            · exact convC_dropLast_lad_none p A B d plev first force hAd hBe hBdne hBhne hl
                hcc (contrLen_dropLast_none p A B hcc) ihB
            · obtain ⟨q, r2, hdq, hq2, hq1, hAq2, hBq2, hr2ne, hr2d, hr2l⟩ := contrLen_spec hcc
              have hr2suf : r2 <:+ B := ⟨B.take (unitsLen p B) ++ [q], by
                rw [List.append_assoc, List.singleton_append, ← hdq, List.take_append_drop]⟩
              have hBsuf : B <:+ (p :: (A ++ B)) := ⟨p :: A, rfl⟩
              -- `B = U ++ q :: r2` と、そこから来る不変量
              have hBform2 : (B.take (unitsLen p B)) ++ (q :: r2) = B := by
                conv_rhs => rw [← List.take_append_drop (unitsLen p B) B]
                rw [hdq]
              have hUge : ∀ c ∈ (B.take (unitsLen p B)), p.1 ≤ c.1 := by
                intro c hc
                have := hbB.2.1 c ((List.take_sublist _ _).subset hc)
                omega
              have hUhead : (B.take (unitsLen p B)) = []
                  ∨ ((B.take (unitsLen p B)).headI).1 ≤ p.1 := by
                by_cases hUe : (B.take (unitsLen p B)) = []
                · exact Or.inl hUe
                · right
                  have hh : (B.headI).1 = ((B.take (unitsLen p B)).headI).1 := by
                    conv_lhs => rw [← List.take_append_drop (unitsLen p B) B]
                    rw [headI_append_left hUe]
                  have hB0 := hbB.1 hBe
                  omega
              have hqL : (q :: r2) = [] ∨ ¬ (p.1 < ((q :: r2).headI).1) := by
                right; simp only [List.headI]; omega
              have hAPq : argPatOK (q :: r2) :=
                argPatOK_drop p.1 (q :: r2) hqL (B.take (unitsLen p B)).length
                  (B.take (unitsLen p B)) (Nat.le_refl _) hUge hUhead
                  (by rw [hBform2]; exact hAPB)
              obtain ⟨-, hAPAq, hAPBq⟩ := argPatOK_cons.1 hAPq
              rw [hAq2] at hAPAq
              rw [hBq2] at hAPBq
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
                · -- 壊れる形。不変量から `p.2 ≤ 1`、よって段は 0、行 0 の親が立って矛盾
                  exfalso
                  obtain ⟨x, hrest⟩ := List.length_eq_one_iff.1 hR1
                  have hx0 : x.2 = 0 := by
                    rw [hrest] at hr2l; simp only [List.headI_cons] at hr2l; omega
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
                  have hrd : ∀ c ∈ rest2, p.1 < c.1 := by
                    intro c hc
                    have hcm : c ∈ (r2.takeWhile fun x => q.1 < x.1) := by
                      rw [hAq2]; exact List.mem_append_right _ hc
                    have := List.mem_takeWhile_imp
                      (p := fun z : ℕ × ℕ => decide (q.1 < z.1)) hcm
                    simp only [decide_eq_true_eq] at this
                    omega
                  have hbR : blockok (p.1 + 1) rest2 := by
                    refine ⟨fun _ => hr2d, fun c hc => by have := hrd c hc; omega, ?_⟩
                    exact steps1_suffix hRsuf hb.2.2
                  have hcolR : colOK rest2 :=
                    colOK_of_suffix hRsuf hcol
                  have hpreall : ∀ c ∈ contrPre p (B.take (unitsLen p B)) A, p.1 + 1 ≤ c.1 := by
                    intro c hc
                    rw [contrPre] at hc
                    rcases List.mem_append.1 hc with hc1 | hc1
                    · rcases List.mem_cons.1 hc1 with hc2 | hc2
                      · rw [hc2]
                      · obtain ⟨y, hy, hyc⟩ := List.mem_map.1 hc2
                        have := hAd y hy
                        rw [← hyc]; simp only []; omega
                    · obtain ⟨y, hy, hyc⟩ := List.mem_map.1 hc1
                      have := hUge y hy
                      rw [← hyc]; simp only []; omega
                  have hpreh : (contrPre p (B.take (unitsLen p B)) A) = []
                      ∨ ((contrPre p (B.take (unitsLen p B)) A).headI).1 ≤ p.1 + 1 := by
                    right; simp [contrPre]
                  have hrestL : rest2 = [] ∨ ¬ (p.1 + 1 < (rest2.headI).1) :=
                    Or.inr (by rw [hr2d]; omega)
                  have hAPR : argPatOK rest2 :=
                    argPatOK_drop (p.1 + 1) rest2 hrestL
                      (contrPre p (B.take (unitsLen p B)) A).length
                      (contrPre p (B.take (unitsLen p B)) A) (Nat.le_refl _) hpreall hpreh
                      hAPAq
                  exact convC_dropLast_contr2 p A B d plev first force hAd hBh hl hcc hRd
                    (ih rest2 hRlen (by omega) (p.1 + 1) (d + 1) p.2 false false
                      hbR hcolR (by omega) hAPR dpOK_false hpOK_false fOK_false
                      (noParent_suffix hr2ne hRsuf hnp))
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
                    have hQh : ¬ (q.1 < (Bq.headI).1) := by
                      rcases dropWhile_head_neg (a := q.1) r2 with hh | hh
                      · exact absurd (by rw [← hBq2]; exact hh) hBqe
                      · rw [hBq2] at hh; exact hh
                    have hbQ : blockok bd Bq := by
                      refine ⟨?_, ?_, ?_⟩
                      · intro hne
                        have h1 : bd ≤ (Bq.headI).1 :=
                          hb.2.1 _ (hQsuf.subset (headI_mem hne))
                        have h2 : ¬ (q.1 < (Bq.headI).1) := hQh
                        omega
                      · intro c hc
                        exact hb.2.1 c (hQsuf.subset hc)
                      · exact steps1_suffix hQsuf hb.2.2
                    exact ih Bq hQlen (by omega) bd d p.2 false false hbQ
                      (colOK_of_suffix hQsuf hcol) hbd hAPBq dpOK_false hpOK_false fOK_false
                      (noParent_suffix hBqe hQsuf hnp)
                exact convC_dropLast_contr p A B d plev first force hAd hBh hl hcc hBqe ihQ
          · exact convC_dropLast_tail p A B d plev first force hAd hBe hBdne hBhne
              (by simpa using hl) ihB

/-- **`RDnopar` は定理**。`contrOK` を不変量に置き換えた `dropLast` 補題から出る。 -/
theorem rdNopar : RDnopar := by
  intro p A T bd d plev first force hb hc _hd2 hbd _hp1 hlen2 _hAd _hTh hlev hAP _hAC _hadj
    hHP hFC hdp _hhc hnopar n _hn
  have hL : 1 < (p :: (A ++ T)).length := by omega
  have hidx : idx1 (p :: (A ++ T)) ((p :: (A ++ T)).length - 1) = 1 := by
    unfold idx1; rw [if_pos hlev]
  have hnp : ¬ hasParent (p :: (A ++ T)) (idx1 (p :: (A ++ T)) ((p :: (A ++ T)).length - 1))
      ((p :: (A ++ T)).length - 1) := by rw [hidx]; exact hnopar
  have hz : ¬ (entry (p :: (A ++ T)) 0 ((p :: (A ++ T)).length - 1) = 0
      ∧ entry (p :: (A ++ T)) 1 ((p :: (A ++ T)).length - 1) = 0) := by
    rintro ⟨-, h2⟩; omega
  refine ⟨1, n, Nat.le_refl 1, Nat.le_refl n, ?_⟩
  rw [oper_one (convC_length_ge_two hL d plev first force),
    oper_eq_pred_of_noParent n (by omega) hz hnp, Pred, if_neg (by omega)]
  exact (convC_dropLast_noParent_aux2 (p :: (A ++ T)).length (p :: (A ++ T))
    (Nat.le_refl _) hL bd d plev first force hb hc hbd hAP hdp hHP hFC hnp).symm

/-- **到達点**: `ReindexD` の残余は `CtrPres2` / `RDnode` の 2 つ。 -/
theorem reindexD_holds_of_res9 (Hp : CtrPres2) (Hd : RDnode) : ReindexD :=
  reindexD_holds_of_res8 Hp rdNopar Hd

/-- 同じ形で主定理まで。 -/
theorem ST_D_conC_holds_of_res9 (Hp : CtrPres2) (Hd : RDnode)
    {M : PairSeq} (hM : ST_PS M) : ST_D (conC M) :=
  ST_D_conC_holds_of_res8 Hp rdNopar Hd hM

/-- **梯子が立つときの数値**（`dpOK` を使わない版）。`fOK` だけで
`d = p.2 = p.1 = bd` かつ `p.2 = plev + 1` が出る（頭は対角の上）。
`dpOK` も足すと `lad_lev_le_one` で `p.2 = 1`、すなわち
**梯子は `p = (1,1)`・`bd = d = 1`・`plev = 0` でしか立たない**。
（実測: ブロック ≤5 列・`bd ≤ 3`・`plev ≤ 4` の全不変量つきの呼び出しで
梯子が立つ組は `(p,bd,d,plev,first) = ((1,1),1,1,0,true)` の 1 通りだけ。） -/
theorem lad_diag {p : ℕ × ℕ} {r : PairSeq} {bd d plev : ℕ} {first force : Bool}
    (hp1 : p.1 = bd) (hcol : p.2 ≤ p.1) (hbd : bd ≤ d)
    (hf : fOK (p :: r) d plev force)
    (hlad : ladOf p.2 d plev first force = true) :
    first = true ∧ d = p.2 ∧ p.2 = p.1 ∧ p.1 = bd ∧ p.2 = plev + 1 := by
  unfold ladOf at hlad
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hlad
  obtain ⟨⟨hf1, hpl⟩, hor⟩ := hlad
  have hdle : d ≤ p.2 := by
    rcases hor with hh | hh
    · exact hh
    · rcases hf hh with h1 | h2
      · exact absurd hpl (h1 p r rfl)
      · omega
  exact ⟨hf1, by omega, by omega, hp1, hpl⟩

/-! ## 4.22 ずれたコピーの道具（`RDnode` 用の下ごしらえ）

`RDnode`（段 > 0・末尾列の親が節点）では

    B⟦n⟧ = W ++ shiftr0 d0 W ++ shiftr0 (2 d0) W ++ …       (W = B.dropLast)

という**ずれたコピーの階段**になる（段 0 の `reindexD_node0_gen2` は `d0 = 0` で
素直な繰り返しだった）。`convC` は深さの平行移動で変わらない（`convC_shift1`）ので、
コピーの像は「ずれ」に依らず `(d, plev, first, force)` だけで決まる。 -/

theorem shiftr0_succ (e : ℕ) (M : PairSeq) : shiftr0 (e + 1) M = shift1 (shiftr0 e M) := by
  unfold shiftr0 shift1
  rw [List.map_map]
  rfl

/-- **`convC` は深さの平行移動 `shiftr0` で変わらない**。 -/
theorem convC_shiftr0 (e : ℕ) (M : PairSeq) (d plev : ℕ) (first force : Bool) :
    convC (shiftr0 e M) d plev first force = convC M d plev first force := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [shiftr0_succ,
      convC_shift1 (shiftr0 e M).length (shiftr0 e M) (Nat.le_refl _) d plev first force, ih]

/-! ## 4.23 `RDnode` の BMS 側の形（ずれたコピーの階段）

末尾列の行 1 の親がブロックの頭（index 0）のとき、展開は

    M⟦n⟧ = copies d0 M.dropLast n
         = M.dropLast ++ shiftr0 d0 M.dropLast ++ shiftr0 (2 d0) M.dropLast ++ …

という**ずれたコピーの階段**になる（`copies` は `Pair/Cnf.lean`、
`copies_succ_front` が「1 段剥がす」補題）。段 0 の `oper_repeat_root` は
`d0 = 0` の素直な繰り返しで、その一般化にあたる。 -/

/-- 添字の並びの像を深さだけずらしたもの。 -/
theorem range'_map_entry_shift (M : PairSeq) {j0 j1 : ℕ} (h0 : j0 ≤ j1) (h1 : j1 ≤ M.length)
    (c : ℕ) :
    (List.range' j0 (j1 - j0)).map (fun j => ((entry M 0 j + c : ℕ), (entry M 1 j : ℕ)))
      = shiftr0 c ((M.take j1).drop j0) := by
  rw [← range'_map_entry M h0 h1]
  unfold shiftr0
  rw [List.map_map]
  rfl

/-- **末尾列の行 1 の親が頭なら、展開はずれたコピーの階段**。 -/
theorem oper_tower {M : PairSeq} (n : ℕ) (hL : 1 < M.length)
    (hlev : 0 < entry M 1 (M.length - 1))
    (hp : hasParent M 1 (M.length - 1))
    (hj0 : parent M 1 (M.length - 1) = 0) :
    M⟦n⟧ = copies (entry M 0 (M.length - 1) - entry M 0 0) M.dropLast n := by
  have hi1 : idx1 M (M.length - 1) = 1 := by rw [idx1, if_pos hlev]
  have hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0) := by
    rintro ⟨-, h1⟩; omega
  have hp' : hasParent M (idx1 M (M.length - 1)) (M.length - 1) := by rw [hi1]; exact hp
  rw [oper_bad_unfold n (by omega) hz hp', hi1, hj0]
  simp only [List.take_zero, List.nil_append, Nat.sub_zero,
    Nat.zero_lt_one, if_true]
  unfold copies
  refine List.flatMap_congr ?_
  intro k _
  have hz0 : (M.length - 1) = (M.length - 1) - 0 := by omega
  rw [hz0, range'_map_entry_shift M (Nat.zero_le _) (by omega), List.drop_zero,
    List.dropLast_eq_take]

/-- `RDnode` の配置での BMS 側の形。 -/
theorem rdNode_bms_shape {p : ℕ × ℕ} {A : PairSeq} (hAne : A ≠ [])
    (hlev : 0 < entry (p :: A) 1 ((p :: A).length - 1))
    (hp : hasParent (p :: A) 1 ((p :: A).length - 1))
    (hj0 : parent (p :: A) 1 ((p :: A).length - 1) = 0) (n : ℕ) :
    (p :: A)⟦n⟧ = copies ((A.getLastD (0, 0)).1 - p.1) (p :: A.dropLast) n := by
  have hL : 1 < (p :: A).length := by
    have : 1 ≤ A.length := List.length_pos_of_ne_nil hAne
    simp only [List.length_cons]; omega
  have hlast : entry (p :: A) 0 ((p :: A).length - 1) = (A.getLastD (0, 0)).1 := by
    rw [entry_last0, getLastD_cons_ne p hAne]
  have hhead : entry (p :: A) 0 0 = p.1 := by rw [entry_zero0]; simp
  have hdl : (p :: A).dropLast = p :: A.dropLast := dropLast_cons_ne hAne
  rw [oper_tower n hL hlev hp hj0, hlast, hhead, hdl]

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
#print axioms DBMS.oper_headI
#print axioms DBMS.hasParent1_of_exists
#print axioms DBMS.idx1_convC
#print axioms DBMS.convC_factor_sib
#print axioms DBMS.convC_factor_arg
#print axioms DBMS.oper_append_convC_auto
#print axioms DBMS.oper_append_convC1_auto
#print axioms DBMS.reindexD_descend
#print axioms DBMS.reindexD_sib_step
#print axioms DBMS.convC_exists_shallow_gen
#print axioms DBMS.oper_append_convC_gen
#print axioms DBMS.oper_depth_gt
#print axioms DBMS.reindexD_arg_step
#print axioms DBMS.reindexD_step_gen
#print axioms DBMS.contrLen_nil
#print axioms DBMS.convC_factor_arg_lad
#print axioms DBMS.convC_factor_sib_lad
#print axioms DBMS.reindexD_arg_nolad
#print axioms DBMS.reindexD_arg_lad
#print axioms DBMS.reindexD_sib_nolad
#print axioms DBMS.reindexD_sib_lad
#print axioms DBMS.reindexD_succ_gen
#print axioms DBMS.reindexD_noParent_gen
#print axioms DBMS.reindexD_noParent_zero
#print axioms DBMS.convC_run_first
#print axioms DBMS.reindexD_node0_gen
#print axioms DBMS.reindexD_node0_gen_shape
#print axioms DBMS.oper_repeat_at
#print axioms DBMS.unitsLen_replicate
#print axioms DBMS.contrLen_of_drop_nil
#print axioms DBMS.convC_dropLast_min
#print axioms DBMS.convC_run_lad
#print axioms DBMS.reindexD_node0_lad
#print axioms DBMS.reindexD_node0_lad_shape
#print axioms DBMS.dropWhile_head_not
#print axioms DBMS.reindexD_zero_block
#print axioms DBMS.reindexD_zero
#print axioms DBMS.reindexD_holds_of_zero
#print axioms DBMS.ST_D_conC_holds_of_zero
#print axioms DBMS.reindexD_pos_block
#print axioms DBMS.reindexD_pos_of
#print axioms DBMS.reindexD_holds_of_res
#print axioms DBMS.ST_D_conC_holds_of_res
#print axioms DBMS.noAdj3_of_agree
#print axioms DBMS.noAdj3_take
#print axioms DBMS.noAdj3_diagSeq
#print axioms DBMS.entry1_last_le_of_lt
#print axioms DBMS.noAdj3_ST_PS
#print axioms DBMS.noAdj3_infix
#print axioms DBMS.argPatOK_of_noAdj3
#print axioms DBMS.argPatOK_ST_PS
#print axioms DBMS.convC_force_head
#print axioms DBMS.convC_arg_force_eq
#print axioms DBMS.ladOf_false_of_ne
#print axioms DBMS.convC_force_ne
#print axioms DBMS.convC_force_arg_ne
#print axioms DBMS.drop_append_len
#print axioms DBMS.getLastD_snoc
#print axioms DBMS.split_takeWhile
#print axioms DBMS.getLastD_cons_ne
#print axioms DBMS.argPatOK_nil
#print axioms DBMS.argPatOK_cons
#print axioms DBMS.takeWhile_infix_cons
#print axioms DBMS.dropWhile_infix_cons
#print axioms DBMS.adjLev_of_r1ok
#print axioms DBMS.adjLev_ST_PS
#print axioms DBMS.adjLev_infix
#print axioms DBMS.dpOK_false
#print axioms DBMS.dpOK_arg
#print axioms DBMS.argCtrOK_nil
#print axioms DBMS.argCtrOK_cons
#print axioms DBMS.hcOK_false
#print axioms DBMS.ctrHeadOK_root
#print axioms DBMS.reindexD_pos_block2
#print axioms DBMS.reindexD_pos_of2
#print axioms DBMS.reindexD_holds_of_res2
#print axioms DBMS.ST_D_conC_holds_of_res2
#print axioms DBMS.contrPre_eq_shiftr0
#print axioms DBMS.contrLen_of_shape
#print axioms DBMS.convC_factor_contr
#print axioms DBMS.reindexD_sib_contr
#print axioms DBMS.reindexD_rest_contr
#print axioms DBMS.reindexD_sib_lad2
#print axioms DBMS.argPatOK_drop
#print axioms DBMS.Units.head_le
#print axioms DBMS.contrLen_shape
#print axioms DBMS.headI_mem
#print axioms DBMS.reindexD_zero_fire
#print axioms DBMS.reindexD_zero_block3
#print axioms DBMS.reindexD_zero3
#print axioms DBMS.reindexD_holds_of_res3
#print axioms DBMS.ST_D_conC_holds_of_res3
#print axioms DBMS.argCtrOK_drop
#print axioms DBMS.reindexD_zero_fire2
#print axioms DBMS.reindexD_zero_block4
#print axioms DBMS.reindexD_zero4
#print axioms DBMS.reindexD_holds_of_res4
#print axioms DBMS.ST_D_conC_holds_of_res4
#print axioms DBMS.reindexD_pos_fire
#print axioms DBMS.reindexD_pos_block3
#print axioms DBMS.reindexD_pos_of3
#print axioms DBMS.reindexD_holds_of_res5
#print axioms DBMS.ST_D_conC_holds_of_res5
#print axioms DBMS.entry_zero1
#print axioms DBMS.descOK_level_le_head
#print axioms DBMS.rdPosStop2
#print axioms DBMS.reindexD_pos_fire2
#print axioms DBMS.reindexD_pos_block4
#print axioms DBMS.reindexD_pos_of4
#print axioms DBMS.reindexD_holds_of_res6
#print axioms DBMS.ST_D_conC_holds_of_res6
#print axioms DBMS.zeroStop_shape
#print axioms DBMS.convC_first_false
#print axioms DBMS.shift1_inj
#print axioms DBMS.unitsLen_shift1
#print axioms DBMS.contrPre_shift1
#print axioms DBMS.contrLen_shift1
#print axioms DBMS.convC_shift1
#print axioms DBMS.convC_units_append
#print axioms DBMS.convC_run_contr
#print axioms DBMS.contrLen_of_shape_nil
#print axioms DBMS.convC_units_depth
#print axioms DBMS.zeroStop_shape
#print axioms DBMS.rdZeroStop
#print axioms DBMS.reindexD_zero_fire3
#print axioms DBMS.reindexD_zero_block5
#print axioms DBMS.reindexD_zero5
#print axioms DBMS.reindexD_holds_of_res7
#print axioms DBMS.ST_D_conC_holds_of_res7
#print axioms DBMS.contrLen'_spec
#print axioms DBMS.contrLen_eq_of_head_lt
#print axioms DBMS.ctrHead_lt_core
#print axioms DBMS.ctrHeadOK_arg_of_ST
#print axioms DBMS.argCtrOK_of_nodes
#print axioms DBMS.ctrRes_holds
#print axioms DBMS.reindexD_holds_of_res8
#print axioms DBMS.ST_D_conC_holds_of_res8
#print axioms DBMS.lad_lev_le_one
#print axioms DBMS.blockok_arg'
#print axioms DBMS.blockok_sib'
#print axioms DBMS.convC_dropLast_noParent_aux2
#print axioms DBMS.rdNopar
#print axioms DBMS.reindexD_holds_of_res9
#print axioms DBMS.ST_D_conC_holds_of_res9
#print axioms DBMS.lad_diag
#print axioms DBMS.shiftr0_succ
#print axioms DBMS.convC_shiftr0
#print axioms DBMS.range'_map_entry_shift
#print axioms DBMS.oper_tower
#print axioms DBMS.rdNode_bms_shape
