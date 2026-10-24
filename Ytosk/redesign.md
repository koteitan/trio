# 接ぎ木の悪い形 Bad2 への対応（2026-10-24）

接ぎ木の標準形（tmp/ytosk-handoff/sets/graftA.pkl・graftB.pkl、作り方 tmp/claude/gen_graft.py）で、最上位の残り HFrameV2・HDropV2W と不変条件 Inv3V2 の欄 TPLoW・AbsDW が偽だった。破れはすべて構造の形 `Bad2`（x − 1 に上がり先がある ∧ x − 1 の親が bump 子）の中にある。

## 済んだこと（main に取り込み済み）
- `Bad2` で分けた: 偽の欄・残りは ¬Bad2 の前提つき、Bad2 の行列の段は新しい残り `TakeBadV2`・`BadOutV2`・`Drop0BadV2`（V3MainV2）。全体ビルド緑、公理は標準の 3 つ。詳しくは desc.md「最上位を接ぎ木の悪い形 Bad2 で分けた」。

## 残り
1. 新しい残りの中身を示す: Bad2 の行列の展開で、弱い変化（x − 1 が上がり先を失い、その親が bump 子なので bump の項を通って祖先が弱く変わる）を扱う落とす補題と t0・t1・t2 のエンジンの場合。参考: ブランチ drop-redesign（CntX を広げる案。PV は「数える子は x だけ ∧ UpgBad(x − 1)」の CntX で graftB 全数・ext2・std_b・ext1 で例外 0、UpgAbsXW0 の NBPar を外す、BumpWeakShapeSrc を「i の子は jl と x だけ」に、BumpAbsC を弱い道との選言に）。
2. 未測定の Inv3V2 の欄（FC3・TP1C・TP1WC の Lean の形）と HLeafV2 を接ぎ木で測る。
3. 新しい残りを立てるときは、必ず接ぎ木の集合（graftA・graftB と Bad2 側 graftBb2）でも測る。
