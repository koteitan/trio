"""順序検算: シートの BMS 列と DBMS 列が順序同型かを全ペアで確かめる。

f が順序同型なら、任意の 2 行 i,j について
    sign(cmp(bms_i, bms_j)) == sign(cmp(dbms_i, dbms_j))
が成り立たねばならない。cmpmat は同一システム内の標準形どうしなら正しい順序を与える
ので、A 列どうし・E 列どうしの比較はそれぞれ健全。

  python3 tools/dbms/order_check.py [rows]      # rows=2 or 3
  python3 tools/dbms/order_check.py 2 --cand    # 自作規則の出力で置き換えて検算
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import flat, show
from check_sheet import load


def cmpf(a, b):
    for x, y in zip(a, b):
        if x != y:
            return 1 if x > y else -1
    return 0 if len(a) == len(b) else (1 if len(a) > len(b) else -1)


def check(pairs):
    """pairs = [(label, bms_mat, dbms_mat)] の全ペア検算。違反リストを返す。"""
    fb = [flat(p[1]) for p in pairs]
    fd = [flat(p[2]) for p in pairs]
    out = []
    for i in range(len(pairs)):
        for j in range(i + 1, len(pairs)):
            a, b = cmpf(fb[i], fb[j]), cmpf(fd[i], fd[j])
            if (a > 0) != (b > 0) or (a == 0) != (b == 0):
                out.append((pairs[i][0], pairs[j][0], a, b))
    return out


def main():
    want = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    use_cand = '--cand' in sys.argv
    d = [x for x in load() if x[3] == want]
    if use_cand:
        import rule as R
        pairs = [(r['row'], mb, R.R8(mb, Y)) for r, mb, md, Y in d]
    else:
        pairs = [(r['row'], mb, md) for r, mb, md, Y in d]
    v = check(pairs)
    n = len(pairs)
    print('rows=%d  pairs=%d  violations=%d' % (n, n * (n - 1) // 2, len(v)))
    for x in v[:20]:
        print('  row%s vs row%s : bms %+d / dbms %+d' % x)


if __name__ == '__main__':
    main()
