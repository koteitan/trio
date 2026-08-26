"""`conC (A.dropLast)` が `conC A` の接頭辞かを全数検査する。

`oper_one`（`M⟦1⟧ = M.dropLast`、`lean/DbmsStd.lean` で証明済み）より

    g(1) = 1  ⟺  conC (A.dropLast) = (conC A).dropLast

なので、この可換性は REINDEX の n=1 の場合そのもの。場合 (b)（親がない）と
場合 (d)（親がこの段、コピーが素直な繰り返し）は、どちらもこれに帰着する。

実測（BMS 標準形、`python3 droplast.py 9`）:

```
(接頭辞か, 長さの差): {(True,1): 289379, (True,2): 5585, (False,*): 49}
```

* 差 1 … 可換（求める場合）
* 差 2 … 末尾列が梯子を敷く（影の分だけ像が 2 列長い）
* 接頭辞でない … 末尾列を落とすと**縮約が消える**ので像がかえって長くなる
  （contr regime の 49 個ちょうど）

使い方: python3 droplast.py [列数上限]
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import show
from rows2 import gen, convC


def main(lim=8):
    Ms = gen('BMS', lim)
    c = collections.Counter()
    ex = []
    for i, M in enumerate(Ms):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._flat_memo.clear()
        if len(M) <= 1:
            continue
        W = tuple(convC(list(M)))
        V = tuple(convC(list(M[:-1])))
        pref = (W[:len(V)] == V)
        c[(pref, len(W) - len(V))] += 1
        if not pref and len(ex) < 5:
            ex.append((M, W, V))
    print("lim=%d  (接頭辞か, 長さの差): %s"
          % (lim, dict(sorted(c.items(), key=lambda x: str(x)))))
    for M, W, V in ex:
        print("   %s -> conC=%s  conC(dropLast)=%s" % (show(M), show(W), show(V)))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 8)
