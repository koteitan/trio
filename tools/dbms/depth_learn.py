"""深さ 1 ビットの規則を、正解ラベルから決定リストとして学習する。

各段階で「残りのデータを純粋に（例外なく）切り取れる条件」のうち、
いちばん多くを覆うものを選ぶ。条件は 1〜3 個の特徴の連言。
出てきたリストが、いまの手書き規則より短くなるかを見る。
"""
import sys, os, json, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'depth_data.json')
KEYS = ['nxt_rel', 'nxt_lv', 'nxt_anchor1', 'nxt_full', 'nxt_base',
        'pv_rel', 'pv_lv', 'pv2_rel', 'pv2_lv', 'prev', 'hi', 'spent',
        'rep', 'p1_root', 'first_br']


def atoms(D):
    """使える単項条件（特徴 == 値）を集める。"""
    out = []
    for k in KEYS:
        for v in sorted({d[k] for d in D}, key=str):
            out.append((k, v))
    return out


def match(d, cond):
    return all(d[k] == v for k, v in cond)


def learn(D, maxlen=3, minpure=1):
    rules = []
    rest = list(D)
    A = atoms(D)
    while rest:
        best = None
        for L in range(1, maxlen + 1):
            for cond in itertools.combinations(A, L):
                if len({k for k, v in cond}) != L:
                    continue
                sel = [d for d in rest if match(d, cond)]
                if len(sel) < minpure:
                    continue
                lab = {d['depth'] for d in sel}
                if len(lab) != 1:
                    continue
                if best is None or len(sel) > best[0]:
                    best = (len(sel), cond, lab.pop())
            if best is not None and best[0] > 0:
                break          # 短い条件を優先
        if best is None:
            break
        n, cond, lab = best
        rules.append((cond, lab, n))
        rest = [d for d in rest if not match(d, cond)]
    return rules, rest


if __name__ == '__main__':
    D = [d for d in json.load(open(DATA)) if d['forced']]
    print('強制ラベル %d 件' % len(D))
    rules, rest = learn(D)
    print('学習した決定リスト %d 本、覆えなかった %d 件' % (len(rules), len(rest)))
    for cond, lab, n in rules:
        print('  %-58s -> %s  (%d 件)'
              % (' かつ '.join('%s=%s' % (k, v) for k, v in cond),
                 '深' if lab else '浅', n))
    if rest:
        c = collections.Counter((d['row'], d['depth']) for d in rest)
        print('  残り:', list(c)[:10])
