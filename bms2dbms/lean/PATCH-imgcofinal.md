# `ImgClosedT3` を `ImgCofinalT3` に弱める（2026-08-28）

## なぜ弱められるか

`ReindexT1_of_block`（`Dbms3.lean:1171`）が `ImgClosedT3`（すべての `m`）から
実際に使うのは **`m := n + 1` ただ 1 つ**である。だから

    ImgClosedT3 : すべての m>=1 で (conv3 A)⟦m⟧ に標準形の逆像がある

は要らず、

    ImgCofinalT3 : いくらでも大きい m で (conv3 A)⟦m⟧ に標準形の逆像がある

で足りる。差を埋めるのは「展開指数についての単調性」

    j <= k  ->  M⟦j⟧ = M⟦k⟧  or  seqlex (M⟦j⟧) (M⟦k⟧)

で、これは `oper` の定義（`Trio.lean:98`）が
`M.take j0 ++ (List.range n).flatMap g` という形をしていること、つまり
`List.range (n+1) = List.range n ++ [n]` だけから出る（`M⟦n+1⟧` は `M⟦n⟧` の
**接尾に足しただけ**）。**`lean/Cofidx.lean` に証明済み（sorry 0, exit 0）**。

## Dbms3.lean に足すもの（`§11.3` の直前）

```lean
/-- **像は展開で共終に閉じている**（`ImgClosedT3` の弱め）。 -/
def ImgCofinalT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → ∀ m0 : ℕ,
    ∃ m : ℕ, m0 ≤ m ∧ ∃ B : TrioSeq, ST_TS B ∧ (conv3 A)⟦m⟧ = conv3 B

theorem ImgCofinalT3_of_ImgClosedT3 {conv3 : TrioSeq → TrioSeq}
    (h : ImgClosedT3 conv3) : ImgCofinalT3 conv3 := by
  intro A hA hlen m0
  obtain ⟨B, hB, heq⟩ := h hA hlen (max m0 1) (le_max_right _ _)
  exact ⟨max m0 1, le_max_left _ _, B, hB, heq⟩

/-- **`ReindexT1` は `ImgCofinalT3` から出る**（`ImgClosedT3` は要らない）。 -/
theorem ReindexT1_of_cofinal {conv3 : TrioSeq → TrioSeq}
    (hI : ImgCofinalT3 conv3) (hO : OrderT3 conv3) (hU : SandwichUT3 conv3)
    (hb : ImgBlockT3 conv3) (hlen2 : ImgLenT3 conv3) :
    ReindexT1 conv3 := by
  intro A hA hlen n hn
  obtain ⟨m, hm0, B, hB, heq⟩ := hI hA hlen (n + 1)
  refine ⟨m, B, by omega, hB, ?_, ?_, heq⟩
  · have h1 := hU hA hlen n hn
    have h2 : sle3 ((conv3 A)⟦n + 1⟧) ((conv3 A)⟦m⟧) := oper_mono_idx hm0
    have h3 : sle3 (conv3 (A⟦n⟧)) (conv3 B) := by
      rw [heq]
      rcases h1 with e1 | s1
      · rcases h2 with e2 | s2
        · exact Or.inl (e1.trans e2)
        · exact Or.inr (e1 ▸ s2)
      · rcases h2 with e2 | s2
        · exact Or.inr (e2 ▸ s1)
        · exact Or.inr (seqlex_trans s1 s2)
    exact ole_of_sle3 hO (ST_TS.oper hA hn) hB h3
  · refine (hO hB hA).2 ?_
    rw [← heq]
    exact seqlex_oper (hb hA) (hlen2 hA hlen) (by omega)
```

`ST_D3_conv3_of_parts` の `hI : ImgClosedT3 conv3` を `ImgCofinalT3 conv3` に
差し替え、本体の `ReindexT1_of_block` を `ReindexT1_of_cofinal` にする。
`import Cofidx` を足すこと（`Cofidx` は `Seqlex` だけに依存する）。
`seqlex_trans` は `Cofinality.lean:25`。

## 測る側（Python）に何が変わるか

`imgfast.py` の採点は「すべての m<=3」で破れを数えている。これからは

    **A ごとに、逆像を持つ m の集合が非有界か**

を測ればよい。実務上は「m = 1..M で逆像を持つ m が M/2 個以上ある」
「周期的に当たる」等で十分な証拠になる。`(conv3 A)⟦m⟧` は m について
**接頭辞の増加列**なので、当たる m が周期的になるのは自然である。
