# 補題索引 — 書く前に grep する

生成: `cd lean && python3 ../tools/dbms/mkindex.py`（team-lead、2026-08-31）
2922 件 / 48 ファイル。形式: `file:line <TAB> kind name <TAB> 完全な型`

## 使い方

    grep -i "nextR_src\|src_ge" LEMMA-INDEX.tsv     # 概念語で探す
    grep "theorem snoc_" LEMMA-INDEX.tsv            # 接頭辞で探す
    grep "le1 (Lift1" LEMMA-INDEX.tsv               # 型の断片で探す

**新しい補題を書く前に、必ず 1 回 grep すること。**
L3 はこのセッションで 9 回、既存の補題を書き直した。
うち §86/§87 は `Wset.nextR_src_ge`（3 行を一度に扱い、錨も不要）の特殊化だった。
