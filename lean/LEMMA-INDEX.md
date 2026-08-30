# 補題索引 — 書く前に grep する

生成: `cd lean && python3 ../tools/dbms/mkindex.py`（team-lead、2026-08-30 再生成）
3715 件 / 48 ファイル。形式: `file:line <TAB> kind name <TAB> 完全な型`

## 使い方

    grep -i "nextR_src\|src_ge" LEMMA-INDEX.tsv     # 概念語で探す
    grep "theorem snoc_" LEMMA-INDEX.tsv            # 接頭辞で探す
    grep "le1 (Lift1" LEMMA-INDEX.tsv               # 型の断片で探す

**新しい補題を書く前に、必ず 1 回 grep すること。**
L3 はこのセッションで 9 回、既存の補題を書き直した。
うち §86/§87 は `Wset.nextR_src_ge`（3 行を一度に扱い、錨も不要）の特殊化だった。

## ★ docstring 列（2026-09-01 追加）

**型だけでは「なぜその形か」が読めない。** L3 と team-lead の「使い所を数える」5 回のうち
**2 回、決め手が docstring にあった**（`nextR_src_ge` / `oper_snoc_flat_root` / `W_flatMap_copies`）。

    grep "PrefixCopies" LEMMA-INDEX.tsv | cut -f4    # docstring だけ見る
    awk -F'\t' '$4 ~ /核のまま/' LEMMA-INDEX.tsv     # 「核」と書いてあるものを全部

**⚠ 索引に無いことは「未着手」と「書けない」を区別しない**（教訓 63）。
**名前を見つけたら必ずファイルを開くこと。**
