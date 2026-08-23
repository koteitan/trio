"""BM4-Analysis xlsx の BMS 列 / DBMS 列で変換器を採点する。

  python3 tools/dbms/check_sheet.py [rule|exact] [rows]
"""
import sys, os, json, time, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, rows, isstd, cmpmat
import rule as RULE
import convert as CONV

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'psiI.json')

# シート E 列(DBMS) の誤り。BMS 列と OCF ラベルは正しく、DBMS 列だけが別の順序数を指す。
#   128 phi(3,z0)        E 列 = ...(4,1)(4,1)    -> 引数を戻すと e1  なので psi(W^3*e1)
#   129 phi(3,phi(3,0))  E 列 = ...(4,1)(4,1)(4,1) -> 同じく e2 なので psi(W^3*e2)
# 正しくは ...(4,1)(5,1) / ...(4,1)(5,1)(5,1)（行 113/117/121/127 の綴り方と同じ）。
SHEET_ERRORS = {128: '(0)(1)(2,1)(3,1)(3,1)(3)(4,1)(5,1)',
                129: '(0)(1)(2,1)(3,1)(3,1)(3)(4,1)(5,1)(5,1)'}

# シート A 列(BMS) の誤り。末尾列の行 2 の印 1 が 0 になっている。
# 判定: 直すと (a) BMS 標準形のまま (b) シートの他行と重複しない
#       (c) 全 1357 行との順序が E 列と一致する (d) 変換器の出力が E 列に一致する
# の 4 つを全部みたす（`scratchpad/typo.py` の探索）。
BMS_ERRORS = {
 346:  '(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(2,0,0)',
 563:  '(0,0,0)(1,1,1)(2,1,0)(2,1,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,2,0)(3,2,0)(2,2,1)',
 713:  '(0,0,0)(1,1,1)(2,1,0)(3,1,0)(2,1,0)(3,1,0)(1,1,0)(2,2,1)(3,2,0)(4,2,0)(3,2,0)(4,1,0)(3,1,0)',
 764:  '(0,0,0)(1,1,1)(2,1,0)(3,1,0)(4,1,0)(1,1,0)(2,2,1)(3,2,0)(4,2,0)(5,1,0)(4,1,0)',
 951:  '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,3,0)(5,3,0)(3,2,0)',
 999:  '(0,0,0)(1,1,1)(2,1,0)(3,2,1)(1,1,0)(2,2,1)(3,2,0)(4,3,1)(1,1,0)(2,2,1)(3,2,0)(4,3,1)',
 1003: '(0,0,0)(1,1,1)(2,1,0)(3,2,1)(1,1,0)(2,2,1)(3,2,0)(4,3,1)(2,2,0)(3,3,1)(4,3,0)(5,4,1)',
 1004: '(0,0,0)(1,1,1)(2,1,0)(3,2,1)(1,1,0)(2,2,1)(3,2,0)(4,3,1)(2,2,0)(3,3,1)(4,3,0)(5,4,1)(3,3,0)',
 1027: '(0,0,0)(1,1,1)(2,1,0)(3,2,1)(2,1,0)(3,2,1)(2,1,0)(3,2,1)',
 1185: '(0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(5,1,0)(1,1,0)(2,2,1)(3,2,0)(4,3,1)(5,3,0)(6,1,0)(6,1,0)',
 1197: '(0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(5,2,0)(3,2,0)(4,3,1)(5,3,0)(6,3,0)(4,3,0)(5,4,1)(6,4,0)(6,4,0)',
 1287: '(0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(5,3,1)(5,3,1)',
 1406: '(0,0,0)(1,1,1)(2,1,1)(2,1,0)(1,1,0)(2,2,1)(3,2,1)(3,1,0)(2,2,1)(3,2,0)(4,3,1)(5,3,1)(5,1,0)(4,3,0)(5,4,1)(6,4,1)(5,4,0)',
}


def load():
    out = []
    for r in json.load(open(DATA)):
        if not (r['bms'] and r['dbms']):
            continue
        if not os.environ.get('RAWSHEET'):
            if r['row'] in SHEET_ERRORS:
                r = dict(r, dbms=SHEET_ERRORS[r['row']])
            if r['row'] in BMS_ERRORS:
                r = dict(r, bms=BMS_ERRORS[r['row']])
        try:
            Y = max(rows(parse(r['bms'])), rows(parse(r['dbms'])))
            mb, md = parse(r['bms'], Y), parse(r['dbms'], Y)
        except Exception:
            continue
        if not (isstd(mb, 'BMS') and isstd(md, 'DBMS')):
            continue          # シートの誤記・非標準形は除外
        out.append((r, mb, md, Y))
    return out


class TO(Exception):
    pass


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'rule'
    want = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    data = load()
    if want:
        data = [d for d in data if d[3] == want]
    signal.signal(signal.SIGALRM, lambda *a: (_ for _ in ()).throw(TO()))
    good = bad = err = 0
    fails = []
    t0 = time.time()
    for r, mb, md, Y in data:
        try:
            if mode == 'rule':
                got = RULE.R1(mb, Y)
            elif mode == 'rule2':
                got = RULE.R2(mb, Y)
            else:
                CONV.stats['limit'] = 0
                signal.alarm(int(os.environ.get('TMO','5')))
                got = CONV.convert(mb, Y)
                signal.alarm(0)
        except Exception as e:
            signal.alarm(0)
            err += 1
            continue
        if os.environ.get('V'):
            print('%s %s' % ('ok' if got == md else 'NG', r['row']), flush=True)
        if got == md:
            good += 1
        else:
            bad += 1
            if len(fails) < 20:
                fails.append((r['row'], show(mb, 1), show(md, 1), show(got, 1)))
    print('---')
    print('mode=%s rows=%s  total=%d  ok=%d  ng=%d  err/timeout=%d  (%.1fs)'
          % (mode, want or 'all', len(data), good, bad, err, time.time() - t0))
    for f in fails:
        print('  row%-5s %s\n         true %s\n         got  %s' % f)


if __name__ == '__main__':
    main()
