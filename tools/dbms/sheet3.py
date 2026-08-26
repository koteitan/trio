"""BM4-Analysis シートの BMS 列 / DBMS 列で 3 行の変換器を採点する。

シートは正解表である（`~/proofs/papers/BM4-Analysis-2021.4.27.xlsx` を
`psiI.json` に落としたもの）。既知の誤記は `check_sheet.py` の表で直す。

    python3 sheet3.py [不一致を何件出すか]
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_sheet as CS
from core import parse, show, rows, isstd, expand
from rows3 import b2d3

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'psiI.json')


def fix(r):
    if r['row'] in CS.SHEET_ERRORS:
        r = dict(r, dbms=CS.SHEET_ERRORS[r['row']])
    if r['row'] in CS.BMS_ERRORS:
        r = dict(r, bms=CS.BMS_ERRORS[r['row']])
    elif r['row'] in CS.BMS_ERRORS2:
        r = dict(r, bms=CS.BMS_ERRORS2[r['row']])
    return r


def load(zcap=1):
    """3 行で z<=zcap の (シート行番号, BMS, DBMS) を BMS の列数順に。"""
    out = []
    for r in json.load(open(DATA)):
        if not (r.get('bms') and r.get('dbms')):
            continue
        r = fix(r)
        try:
            if rows(parse(r['bms'])) != 3:
                continue
            b, d = parse(r['bms'], 3), parse(r['dbms'], 3)
        except Exception:
            continue
        if any(c[2] > zcap for c in b):
            continue
        if not isstd(b, 'BMS'):
            continue
        out.append((r['row'], b, d))
    out.sort(key=lambda t: (len(t[1]), t[0]))
    return out


def score(f=b2d3, show_n=10, zcap=1):
    T = load(zcap)
    ok, ex = 0, []
    for row, b, d in T:
        n = tuple(f(b))
        if n == d:
            ok += 1
        elif len(ex) < show_n:
            ex.append((row, b, d, n))
    print('シート 3 行 z<=%d: %d 件   一致 %d   不一致 %d'
          % (zcap, len(T), ok, len(T) - ok))
    for row, b, d, n in ex:
        print('  行%-5d %s' % (row, show(b)))
        print('        正 %s' % show(d))
        print('        誤 %s' % show(n))
    return ok, len(T)


if __name__ == '__main__':
    score(show_n=int(sys.argv[1]) if len(sys.argv) > 1 else 6)
