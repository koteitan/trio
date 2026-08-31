"""シートの BMS 列の補正の証拠能力を測る。

結論（2026-08-23）:
- (a)(b)(c) の客観条件だけでは、どの行も候補が 12〜43 個あり**一意に決まらない**。
  どれを選ぶかは変換器が決めている。
- ただし反証テスト（下の falsification）で、補正の要らない正しい行 40 個には
  「条件を満たし、かつ変換器も一致する別の 1 手編集」が**1 個も無かった**。
  つまりそういう編集が見つかること自体が稀な出来事で、補正した 25 行で
  見つかったのは偶然ではない。
- さらに 2 行（1287, 1433）は隣の行と BMS が同一で、生シートのままだと
  DBMS 列との順序が破れる。ここだけは変換器と無関係な硬い証拠がある。



補正候補のうち
  (a) BMS 標準形
  (b) 他行と重複しない
  (c) その行を置き換えても、シートの DBMS 列との順序が全 1356 行で保たれる
の 3 条件だけを満たすものを数える。1 通りしかなければ補正は**強制**で、
変換器に依存しない。複数あるなら、どれを選ぶかは変換器頼み（＝循環）。
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import isstd, flat, show, parse
from order_check import cmpf
os.environ['RAWSHEET'] = '1'      # もとの（未補正の）シートを読む
import check_sheet as CS
from typo_search import edits1


def evidence(row, twostep=False):
    d = [x for x in CS.load() if x[3] == 3]
    tgt = [x for x in d if x[0]['row'] == row]
    if not tgt:
        return None
    r, mb, md, _ = tgt[0]
    others = [(x[0]['row'], x[1], x[2]) for x in d if x[0]['row'] != row]
    seen = {b for _, b, _ in others}
    fo = [(flat(b), flat(dd)) for _, b, dd in others]
    fd = flat(md)

    def ok(cand):
        if cand in seen or not isstd(cand, 'BMS'):
            return False
        fc = flat(cand)
        for fb, fdd in fo:
            a, b = cmpf(fc, fb), cmpf(fd, fdd)
            if (a > 0) != (b > 0) or (a == 0) != (b == 0):
                return False
        return True

    cands = []
    for c in edits1(mb):
        if c != mb and ok(c):
            cands.append(c)
    return mb, cands


if __name__ == '__main__':
    rows = [int(a) for a in sys.argv[1:]] or sorted(
        set(CS.BMS_ERRORS) | set(CS.BMS_ERRORS2))
    print('（生シートを読み、補正候補を数える）')
    uniq = 0
    for rw in rows:
        e = evidence(rw)
        if e is None:
            print('row %-5s 見つからず' % rw); continue
        mb, cands = e
        fix = CS.BMS_ERRORS.get(rw) or CS.BMS_ERRORS2.get(rw)
        fixm = parse(fix, 3) if fix else None
        hit = fixm in cands if fixm else False
        if len(cands) == 1:
            uniq += 1
        print('row %-5s 条件を満たす 1 手の候補 %2d 個  採用したものが含まれる: %s'
              % (rw, len(cands), hit))
    print()
    print('候補が 1 通りに決まった行: %d / %d' % (uniq, len(rows)))


def falsification(sample=40, seed=3):
    """反証テスト: 補正が要らない（生シートで変換器が一致する）行について、
    1 手の編集で「条件 (a)(b)(c) を満たし、かつ変換器がシートの DBMS に一致する」
    ものが他にどれだけあるかを数える。

    ほとんど 0 なら、補正した行で見つかった編集は偶然ではない＝証拠になる。
    よく見つかるなら、補正は変換器頼みの循環にすぎない。
    """
    import random
    import rule as R
    d = [x for x in CS.load() if x[3] == 3]
    good = [(r, mb, md) for r, mb, md, _ in d if R.convert(mb, 3) == md]
    random.seed(seed)
    pick = random.sample(good, min(sample, len(good)))
    others_all = [(x[0]['row'], x[1], x[2]) for x in d]
    tot = 0; hit = 0; hits = []
    for r, mb, md in pick:
        others = [o for o in others_all if o[0] != r['row']]
        seen = {b for _, b, _ in others}
        fo = [(flat(b), flat(dd)) for _, b, dd in others]
        fd = flat(md)
        n = 0
        for c in edits1(mb):
            if c == mb or c in seen or not isstd(c, 'BMS'):
                continue
            fc = flat(c)
            bad = False
            for fb, fdd in fo:
                a, b = cmpf(fc, fb), cmpf(fd, fdd)
                if (a > 0) != (b > 0) or (a == 0) != (b == 0):
                    bad = True; break
            if bad:
                continue
            try:
                if R.convert(c, 3) == md:
                    n += 1
            except Exception:
                pass
        tot += 1
        if n:
            hit += 1; hits.append((r['row'], n))
    print('反証テスト: 正しい行 %d 個中、変換器も一致する別の 1 手編集が'
          '見つかった行 %d 個' % (tot, hit))
    for rw, n in hits[:10]:
        print('   row %-5s %d 個' % (rw, n))
