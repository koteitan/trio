# WfSrcA: T2AbsNSrcW の (a)（2026-10-31）

## Lean（Ytosk/lean/Ytosk/WfSrcA.lean）
- `not_dropFail_of_case_a (hS : SrcAShape)`: (a) の枠で DropFail なし。
  c = x−1 は not_dropFail_of_lost_grandchild、e1 c > e1 m・前の写しは failed_drop_* で除外、
  e1 c = e1 m ∧ e0 m < e0(c+1) は nonlost_return_value + not_dropFail_of_parent_le_child。
- 残り `SrcAShape`: (i)(ii) の形は起きない（e1 c = e1 m ∧ e0 m < e0(c+1)）。
- `T2AbsNSrcWBC`: T2AbsNSrcW を P0 x = P1 x = x−1 に制限したもの（(b)(c)）。
- 橋 `t2AbsNSrcW_of : SrcAShape → T2AbsNSrcWBC → WfT2Src.T2AbsNSrcW`。公理は標準 3 つ。

## 測定（probe_resid.py、resid*.json）
- V1 = Bad2 (a) の枠そのもの: 例外 0（b2grow1 1824、b2grow2 3797、wide 3493、接ぎ木 400 の 528 など）。
- V2 = 枠の構造だけ（Bad2 の値の条件なし）: 偽（cbadext 13、graftB 47）。
  例 (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)(7,2,1)(8,1,0)(4,2,0)(5,3,1)(6,3,1)(7,3,0)(5,3,1)(6,3,1)(7,1,0)(8,2,1)(9,2,1)(10,1,0)(5,3,1)
  m=18, i=22, j=23, c=24=(7,1,0)（e1 c < e1 m、c は x−1 の祖先）。UpgAbsX 真なので Bad2 でない。i=22 の窓は空（W = v(m)）。
- V0 = 枠なし: 偽（std_a 13 など）。
- よって SrcAShape は Bad2 の値の条件に依存する。

## 構造の観察
- (ii)-祖先型（c が x−1 の祖先、e1 c < e1 m）: 前の写し (e1 = e1 m の兄) を消すと、ArgDomCore(a, c)
  （a = m の行 1 の鎖で行 e1 c の列）で x−1 の列が非標準になる例がある（core_bad で確認）。
- (i)-次列型（c が葉、upg c = c+1 が P1 m の子）: c+1 の部分木は兄 m_q の部分木で上から抑えられる（bms -s）。

## 追記: 狭めた残り SrcARem2（9da32280）
- `SrcARem`: 残りの形 ⇒ ¬DropFail（SrcAShape より弱い。srcARem_of_shape）。
- `caseB_next`（証明済み）: c が x−1 の祖先でないとき、ICC で c の部分木の次の列 c′ に upg(c′−1)=c′、
  q = P0 c′ = P1(c′−1) は m の真の祖先（q = m なら e1 c > e1 m で矛盾、q は c 以下・j・i でない）。
- `SrcARem2`: (A) c は x−1 の祖先で e1 c < e1 m、または (B) 上の c′・q（q は m の真の祖先）⇒ ¬DropFail。
  橋 `t2AbsNSrcW_of_rem2 : SrcARem2 → T2AbsNSrcWBC → WfT2Src.T2AbsNSrcW`。
- 測定（resid4/resid5、V0 = 枠も Bad2 も外した一般化）: 残りの形の出現はすべて (A)、(B) は 0 件。
  (A) で DropFail 0 件。証明書は v(m) < τ.o c（大半）か窓の head < ω²（Window で閉じる）。
  graftB 1099、graftBb2St 106、d3s 345、cbadext 625、std_a 13 など。
- (A) の構造的な理由の候補: ArgDomCore(a, c)（a は m の行 1 の鎖で行 e1 c の列）。c の部分木は a の部分木の
  ずらしで上から抑えられる。(B) の候補: c′ の部分木は兄 m_q の部分木で抑えられる。
