"""Python の isstd / cmpmat を yaBMS の C 実装 (c/bms) と突き合わせる。

core.py の判定は yaBMS の移植なので、検証の土台そのものを確かめておく。
使い方: python3 crosscheck.py [標本数]
"""
import sys, os, subprocess, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import isstd, cmpmat, rows
from check_sheet import load
import rule as R
import verify_gen as VG

BMS = os.path.expanduser('~/code/yaBMS/c/bms')


def ser(m, Y=None):
    """全行そろえた文字列に。C 実装は行数不一致で落ちる。"""
    if Y is None:
        Y = max((len(c) for c in m), default=1)
        Y = max(Y, rows(m))
    return ''.join('(' + ','.join(str(c[y] if y < len(c) else 0)
                                  for y in range(Y)) + ')' for c in m)


def c_isstd(m, ver, Y=None):
    v = 'DBMS' if ver == 'DBMS' else '4'
    out = subprocess.run([BMS, '-s', '-v', v, ser(m, Y)],
                         capture_output=True, text=True, timeout=60)
    t = out.stdout.strip()
    if t not in ('0', '1'):
        return None
    return t == '1'


def c_cmp(a, b, Y=None):
    out = subprocess.run([BMS, '-c', ser(a, Y), ser(b, Y)],
                         capture_output=True, text=True, timeout=60)
    t = out.stdout.strip()
    return int(t) if t in ('-1', '0', '1') else None


def main(n=400):
    if not os.path.exists(BMS):
        print('c/bms が無い。~/code/yaBMS/c で make してから。'); return
    random.seed(7)
    cases = []          # (行列, ver, ラベル)
    for r, mb, md, Y in load():
        if mb:
            cases.append((mb, 'BMS', 'シート BMS 行%s' % r['row']))
            cases.append((md, 'DBMS', 'シート DBMS 行%s' % r['row']))
    outs = []
    for m in VG.gen(VG.seeds()):
        if m:
            outs.append(m)
    random.shuffle(outs)
    for m in outs[:n]:
        cases.append((m, 'BMS', '生成 BMS'))
        cases.append((R.convert(m, 3), 'DBMS', '生成の変換結果'))
    random.shuffle(cases)
    cases = cases[:2 * n]
    ng = 0
    for m, ver, lab in cases:
        try:
            c = c_isstd(m, ver)
        except Exception as e:
            print('  C 呼び出し失敗 %s: %r' % (lab, e)); ng += 1; continue
        p = isstd(m, ver)
        if c is None:
            print('  C の出力が読めない %s' % lab); ng += 1; continue
        if c != p:
            ng += 1
            if ng <= 5:
                print('  不一致 %-22s ver=%-4s C=%s Python=%s' % (lab, ver, c, p))
                print('     %s' % ser(m))
    print('isstd 突き合わせ %d 件、不一致 %d 件' % (len(cases), ng))

    # 比較関数も見る
    # 行数が同じものどうしだけ比べる（cmpmat は同じ行数の標準形どうしで使う）
    pool = [m for m, ver, lab in cases if ver == 'DBMS' and rows(m) == 3][:60]
    ng2 = 0; tot2 = 0
    for i in range(len(pool)):
        for j in range(i + 1, min(i + 6, len(pool))):
            Y = 3
            cc = c_cmp(pool[i], pool[j], Y)
            pp = cmpmat(pool[i], pool[j])
            tot2 += 1
            if cc is None or cc != pp:
                ng2 += 1
                if ng2 <= 3:
                    print('  cmp 不一致 C=%s Python=%s' % (cc, pp))
    print('cmpmat 突き合わせ %d 件、不一致 %d 件' % (tot2, ng2))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 400)
