#!/usr/bin/env python3
"""課題 L11 (DBMS): `Conv3.BlkInv` の**縮約の枝**の証明債務を、書く前に測る。

`Dbms3.lean` §11.5 の doc は残りを 2 つの穴と書いている:

  * `contr_rd_ok`  … 残余の開始深さ `rd` が `d ≤ rd ≤ |rU.2.ST|` に収まる
  * `convResid_blk` … `convResid` の不変量。「残余は森なので開始深さが下がる。
                      だから `BlkOK` の第 2 項はそのままでは偽」と書いてある

これを**実際の呼び出し点で**測る。`Dbms3.lean` の本文をそのまま貼った使い捨ての
Lean file を作り、縮約の枝に計測を埋め込む。埋め込み先は `St.nc`（縮約の発火
回数）で、**`nc` は像に一切効かない**（`grep '\\.nc'` で読むところが無い）ので
安全である。10 個の条件を 100 進の桁に詰めて、`#eval` で合計を出す。

    python3 l11_blkmeas.py gen  <out.lean> <matrices.txt> [...]
    leanman check -C /home/koteitan/proofs/dbms/lean <out.lean>

行列の file は `l1_sets.py` が作る形（1 行 1 行列、`x,y,z x,y,z ...`）。

## 測る 10 本（`nc` の 100 進の桁 1..10）と陽性対照（桁 11）

    1  d ≤ rd                                   contr_rd_ok の下半分
    2  rd ≤ |rU.2.ST|                           contr_rd_ok の上半分
    3  steps1 rR.1                              convResid_blk 節 1
    4  rd ≤ |rR.2.ST|                           convResid_blk 節 2（偽と疑われていた）
    5  rR.1 = [] → |rR.2.ST| = |rU.2.ST|        convResid_blk 節 3
    6  rR.1 ≠ [] → head.1 ≤ |rU.2.ST|           convResid_blk 節 4
    7  rR.1 ≠ [] → last.1 + 1 = |rR.2.ST|       convResid_blk 節 5
    8  d ≤ |rR.2.ST|                            rB の帰納法の仮定の入口
    9  dmap が狭義単調                          BlkOK に足す候補の不変量
    10 dmap の全要素 < |ST|                     同上
    11 rd + 1 ≤ d                               **陽性対照**（発火数と一致すべき）

## 結果（2026-08-28）

    <=6 列 全数 8387 個   … 発火 44、**違反 0（10 本とも）**、陽性対照 44/44
    7 列 縮約発火 294 個  … 発火 294、**違反 0（10 本とも）**、陽性対照 294/294

合計 338 発火 = `SESSION-2026-08-28.md` の「発火は 338/77282」と一致（＝
既知の発火を全部踏んでいる）。

⟹ **`convResid_blk` は呼び出し点では `BlkOK` そのままで真**であり、doc の
「第 2 項はそのままでは偽」は**実際に現れる `rd` については観測されない**
（`rd` の上界を落とした `ResidBlk` が偽であることとは別の話）。
⟹ 候補の `dmap` 不変量（狭義単調・`< |ST|`）も**真**。
"""
import re
import sys

SRC = '/home/koteitan/proofs/dbms/lean/Dbms3.lean'

OLD = """        let rR := convResid rest2 rd Lr (v, s2) (e1, e2) rU.2
                    (match Bq with | b :: _ => some b | [] => nx) (oq + 1 + kp)
        let rB := conv3 Bq d L FA (v, s2) (e1, e2) false false rR.2 nx (oq + 1 + Aq.length)
        (cols ++ rA.1 ++ rU.1 ++ rR.1 ++ rB.1,
          { rB.2 with nc := rB.2.nc + 1 })"""

NEW = """        let rR := convResid rest2 rd Lr (v, s2) (e1, e2) rU.2
                    (match Bq with | b :: _ => some b | [] => nx) (oq + 1 + kp)
        let rB := conv3 Bq d L FA (v, s2) (e1, e2) false false rR.2 nx (oq + 1 + Aq.length)
        let w1 := if d ≤ rd then 0 else 100
        let w2 := if rd ≤ rU.2.ST.length then 0 else 100^2
        let w3 := if steps1B rR.1 then 0 else 100^3
        let w4 := if rd ≤ rR.2.ST.length then 0 else 100^4
        let w5 := if rR.1.isEmpty then
                    (if rR.2.ST.length = rU.2.ST.length then 0 else 100^5) else 0
        let w6 := if rR.1.isEmpty then 0 else
                    (if (rR.1.headI).1 ≤ rU.2.ST.length then 0 else 100^6)
        let w7 := if rR.1.isEmpty then 0 else
                    (if (rR.1.getLastD (0,0,0)).1 + 1 = rR.2.ST.length then 0 else 100^7)
        let w8 := if d ≤ rR.2.ST.length then 0 else 100^8
        let w9 := if dmapMono rU.2.dmap then 0 else 100^9
        let w10 := if dmapLt rU.2.dmap rU.2.ST.length then 0 else 100^10
        let wc := if rd + 1 ≤ d then 0 else 100^11
        (cols ++ rA.1 ++ rU.1 ++ rR.1 ++ rB.1,
          { rB.2 with nc := rB.2.nc + 1 + w1 + w2 + w3 + w4 + w5 + w6 + w7 + w8 + w9
                        + w10 + wc })"""

HELPER = """/-- 計測用: `steps1` の Bool 版。 -/
def steps1B : TrioSeq → Bool
  | [] => true
  | [_] => true
  | a :: b :: r => (decide (b.1 ≤ a.1 + 1)) && steps1B (b :: r)

/-- 計測用: `dmap` が狭義単調か。 -/
def dmapMono : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: r => decide (a < b) && dmapMono (b :: r)

/-- 計測用: `dmap` の全要素が `n` 未満か。 -/
def dmapLt (dm : List ℕ) (n : ℕ) : Bool := dm.all (fun k => decide (k < n))

"""

TAIL = """
namespace TRIO
namespace L11Meas

/-- `nc` に 100 進で詰めた計測値をほどく。 -/
def digits (n : ℕ) : List ℕ :=
  (List.range 12).map (fun k => (n / 100 ^ k) % 100)

def runNc (M : TrioSeq) : ℕ :=
  (Conv3.conv3 M 0 [] [] (0, 0) (0, 0) true false ⟨[], 2, [], M, 0, []⟩ none 0).2.nc

def tally (ms : List TrioSeq) : List ℕ :=
  ms.foldl (fun acc M => List.zipWith (· + ·) acc (digits (runNc M)))
    (List.replicate 12 0)

"""

CH = 500


def enc(line):
    return '[' + ', '.join('(%s)' % c for c in line.split()) + ']'


def block(path, tag):
    mats = [l.strip() for l in open(path) if l.strip()]
    chunks = [mats[i:i + CH] for i in range(0, len(mats), CH)]
    out, names = [], []
    for i, ch in enumerate(chunks):
        body = ',\n '.join(enc(m) for m in ch)
        out.append("set_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\n"
                   "def %s_c%d : List TrioSeq := [\n %s]\n" % (tag, i, body))
        names.append("%s_c%d" % (tag, i))
    out.append("set_option maxRecDepth 100000 in\ndef %s : List TrioSeq := %s\n"
               % (tag, " ++ ".join(names)))
    out.append("#eval tally %s\n" % tag)
    return "".join(out)


def main(out, paths):
    src = open(SRC).read()
    assert OLD in src, '縮約の枝が見つからない（Dbms3.lean が変わった？）'
    src = src.replace(OLD, NEW, 1)
    i = src.index("\nmutual\n")
    src = src[:i + 1] + HELPER + src[i + 1:]
    body = TAIL
    for k, p in enumerate(paths):
        body += block(p, 'ms%d' % k)
    body += "end L11Meas\nend TRIO\n"
    open(out, 'w').write(src + body)
    print('wrote', out, len(src.splitlines()) + len(body.splitlines()), 'lines')


if __name__ == '__main__':
    if len(sys.argv) < 4 or sys.argv[1] != 'gen':
        print(__doc__)
        sys.exit(1)
    main(sys.argv[2], sys.argv[3:])
