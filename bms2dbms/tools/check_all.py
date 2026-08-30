"""シートとの一致と、シート外での必要条件をまとめて測る。"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_sheet import load
from core import isstd
from order_check import check
import rule as R
import verify_gen as VG


def sheet():
    tot = okall = 0; res = []; ns = 0; viol = 0
    for Y in (1, 2, 3):
        d = [x for x in load() if x[3] == Y]
        outs = [(r['row'], mb, R.convert(mb, Y)) for r, mb, md, _ in d]
        ok = [(rw, mb, g) for (rw, mb, g), (r, m2, md, _) in zip(outs, d) if g == md]
        ns += sum(1 for _, _, g in outs if not isstd(g, 'DBMS'))
        viol += len(check(ok))
        tot += len(d); okall += len(ok); res.append('Y%d %d/%d' % (Y, len(ok), len(d)))
    print('シート  %s 合計 %d/%d  非標準 %d 順序違反 %d' % (' '.join(res), okall, tot, ns, viol))
    return okall, tot


if __name__ == '__main__':
    sheet()
    VG.main()
