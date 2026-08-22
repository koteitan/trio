"""BM4-Analysis xlsx の BMS 列 / DBMS 列で変換器を採点する。

  python3 tools/dbms/check_sheet.py [rule|exact] [rows]
"""
import sys, os, json, time, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, rows, isstd, cmpmat
import rule as RULE
import convert as CONV

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'psiI.json')


def load():
    out = []
    for r in json.load(open(DATA)):
        if not (r['bms'] and r['dbms']):
            continue
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
