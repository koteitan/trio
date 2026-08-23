"""後始末（深さの振り直し）が出した答えを教師データにして、欠けている規則を探す。

結論（2026-08-24）: **見つからなかった**。

正例（後始末が「ここを深くすべき」と出した地点）376 に対し、負例を
「規則が正しく効いている行列 6000 個」から 9139 地点取り直して探索したところ、
3 つまでの特徴の連言では純度 0.957 が上限で、しかもその条件は `op_a=5`
（開き列の行 0 がちょうど 5）という具体的な数値に依存している＝丸暗記。

負例を「後始末が働いた行列」だけから取ると純度 1.0 の条件が出るが、
それを規則に入れると生成 40032 個で規則だけの非標準形が 316 -> 1589 に悪化する。
**負例の母集団を間違えると、完璧に見える偽の規則が出る**という教訓。

同じ失敗を 3 回した:
  1. regime_probe.py — 負例をシートだけから取った
  2. nest=1 案 — 負例を後始末が働いた行列だけから取った
  3. 上の 0.957 — 数値の丸暗記
欠けている構造は、いまの局所的な特徴（前後の列・状態・regime の入れ子）では
書けない。階段そのものの定式化を変える必要がある。


規則の出力が標準形にならず、後始末が深さを反転して直した地点を「本当は反転すべき」、
同じ行列の他の分岐列を「反転すべきでない」として集め、両者を分ける条件を探す。
"""
import sys, os, itertools, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import isstd, show, cmpmat, pim
import rule as R
import verify_gen as VG


def feats(m, x, ds):
    c = m[x]
    nxt = m[x + 1] if x + 1 < len(m) else None
    pv = m[x - 1] if x > 0 else None
    P = pim(m)
    b = max([q for q in range(x) if R.is_anchor1(m[q])], default=0)
    op = [q for q in range(b, x)
          if len(m[q]) > 2 and m[q][2] >= 1 and m[q][1] <= m[q][2]]
    op = op[-1] if op else None
    prevd = None
    for q in range(x - 1, -1, -1):
        if R.is_anchor1(m[q]):
            prevd = 0; break
        if R.is_branching(m[q]):
            prevd = ds[q]; break
    return {
        'depth': ds[x],
        'prev': prevd,
        'nxt_rel': ('なし' if nxt is None else
                    '+1' if nxt[0] == c[0] + 1 else
                    '同' if nxt[0] == c[0] else
                    '戻り' if nxt[0] < c[0] else '飛び'),
        'nxt_lv': -1 if nxt is None else nxt[1] + (10 if len(nxt) > 2 and nxt[2] else 0),
        'pv_rel': ('なし' if pv is None else
                   '+1' if pv[0] == c[0] + 1 else
                   '同' if pv[0] == c[0] else
                   '戻り' if pv[0] < c[0] else '飛び'),
        'pv_lv': -1 if pv is None else pv[1] + (10 if len(pv) > 2 and pv[2] else 0),
        'hi': R.hi_block(m, x),
        'spent': R.spent_level(m, x, c[1] + 1),
        'rep': R.is_repeat(m, x),
        'closes': R.closes_unit(nxt),
        'op_gap': (x - op) if op is not None else -1,
        'op_after_w': (op is not None and op > 0 and len(m[op - 1]) > 1
                       and m[op - 1][1] == 0 and m[op - 1][0] >= 1),
        'p1_is_op': op is not None and P[x][1] == op,
        'c_lv': c[1],
    }


def collect(maxcols=36):
    pos, neg = [], []
    n_fire = n_fix = 0
    for m in VG.gen(VG.seeds()):
        if not m or len(m) > maxcols:
            continue
        ds = R.depths(m)
        Z = R.dedup(R._stair(m, 3, lambda x, c: ds[x]))
        if isstd(Z, 'DBMS'):
            continue
        n_fire += 1
        W = R.convert(m, 3)
        if not isstd(W, 'DBMS'):
            continue          # 後始末でも直らなかった
        n_fix += 1
        # どの反転で W になったかを求める
        br = [x for x, c in enumerate(m) if R.is_branching(c)]
        flips = None
        for k in (1, 2, 3):
            for f in itertools.combinations(br, k):
                e = list(ds)
                for i in f:
                    e[i] ^= 1
                try:
                    V = R.dedup(R._stair(m, 3, lambda x, c, e=e: e[x]))
                except Exception:
                    continue
                if V == W:
                    flips = set(f); break
            if flips is not None:
                break
        if flips is None:
            continue
        for x in br:
            f = feats(m, x, ds)
            f['m'] = [list(c) for c in m]
            f['x'] = x
            (pos if x in flips else neg).append(f)
    print('後始末が働いた行列 %d、直った %d' % (n_fire, n_fix))
    return pos, neg


DUMP = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'flip_data.json')


def load_or_collect():
    if os.path.exists(DUMP):
        d = json.load(open(DUMP))
        return d['pos'], d['neg']
    pos, neg = collect()
    json.dump({'pos': pos, 'neg': neg}, open(DUMP, 'w'))
    return pos, neg


if __name__ == '__main__':
    pos, neg = load_or_collect()
    print('反転すべき地点 %d、そのままでよい地点 %d' % (len(pos), len(neg)))
    if not pos:
        sys.exit()
    keys = [k for k in pos[0] if k not in ('depth', 'm', 'x')]
    atoms = []
    for k in keys:
        for v in sorted({d[k] for d in pos} | {d[k] for d in neg}, key=str):
            atoms.append((k, v))
    best = []
    for L in (1, 2, 3):
        for cond in itertools.combinations(atoms, L):
            if len({k for k, v in cond}) != L:
                continue
            np_ = sum(1 for d in pos if all(d[k] == v for k, v in cond))
            nn = sum(1 for d in neg if all(d[k] == v for k, v in cond))
            if nn == 0 and np_ > 0:
                best.append((np_, cond))
        if best:
            break
    best.sort(reverse=True)
    print('そのままでよい地点を巻き込まずに反転地点を覆う条件（上位）:')
    for n, cond in best[:10]:
        print('  %-58s %d/%d' % (' かつ '.join('%s=%s' % kv for kv in cond), n, len(pos)))
    if not best:
        print('  （完全に分離する条件は無し）')
        print('  純度の高い条件（正例をよく覆い、負例の混入が少ない順）:')
        scored = []
        for L in (1, 2, 3, 4):
            for cond in itertools.combinations(atoms, L):
                if len({k for k, v in cond}) != L:
                    continue
                np_ = sum(1 for d in pos if all(d[k] == v for k, v in cond))
                if np_ < 20:
                    continue
                nn = sum(1 for d in neg if all(d[k] == v for k, v in cond))
                scored.append((np_ / (np_ + nn), np_, nn, cond))
        scored.sort(reverse=True)
        for pu, np_, nn, cond in scored[:12]:
            print('    純度 %.3f  正 %4d / 負 %4d   %s'
                  % (pu, np_, nn, ' かつ '.join('%s=%s' % kv for kv in cond)))
        c = collections.Counter()
        for d in pos:
            c[(d['depth'], d['nxt_rel'], d['pv_lv'], d['hi'])] += 1
        print('  反転地点の文脈（多い順）:')
        for k, v in c.most_common(10):
            print('    深さ%s 次=%s 前段=%s hi=%s : %d' % (k[0], k[1], k[2], k[3], v))


NEGDUMP = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'flip_neg.json')


def collect_negatives(limit=6000, maxcols=40):
    """規則が正しく効いている行列（生出力が標準形）の分岐列を負例にする。

    flip_data.json の負例は「後始末が働いた行列」からしか取れておらず偏っている。
    本当の負例はこちら。
    """
    out = []
    n = 0
    for m in VG.gen(VG.seeds()):
        if not m or len(m) > maxcols:
            continue
        ds = R.depths(m)
        try:
            Z = R.dedup(R._stair(m, 3, lambda x, c: ds[x]))
        except Exception:
            continue
        if not isstd(Z, 'DBMS'):
            continue
        n += 1
        if n > limit:
            break
        for x, c in enumerate(m):
            if not R.is_branching(c):
                continue
            f = feats(m, x, ds)
            f['m'] = [list(c2) for c2 in m]
            f['x'] = x
            out.append(f)
    json.dump(out, open(NEGDUMP, 'w'))
    print('正しく効いている行列 %d 個から負例 %d 地点' % (min(n, limit), len(out)))
    return out
