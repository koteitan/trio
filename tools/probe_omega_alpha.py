"""Observing the general term of psi_0(Omega_alpha).

Extract from the "To psi(I)" sheet of BM4-Analysis every pure psi(W_alpha) row (an
Omega_alpha collapse not mixed with sums, products or powers) and measure:

1. Orbit closure: if M is pure and its branch is T2/T0 (alpha a limit), then M[n] is pure
   as well. If the branch is T1 (alpha a successor, the (d-2) tower), M[n] leaves the pure
   family and dives into a power tower psi(W_w^...) - as the dom correspondence predicts.
2. Dump the pure rows to tmp/pure-rows.tsv for inspection. The table the builder and the
   probes actually read is tools/omega_alpha_rows.tsv, which normalize_sheet.py writes from
   the format-normalized labels; this script must not overwrite it.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(__file__))
from trio import expand
from probe_dom import classify

XLSX = os.path.expanduser('~/proofs/papers/BM4-Analysis-2021.4.27.xlsx')

def pure_sub(label):
    """Return the alpha string when the label is a bare psi(W_alpha); None otherwise."""
    if not (isinstance(label, str) and label.startswith('psi(W') and label.endswith(')')):
        return None
    body = label[4:-1]
    if body == 'W':
        return '1'
    if not body.startswith('W_'):
        # psi(W2) and friends have no W_, so they are Omega*2 shapes; W alone is above.
        return None
    sub = body[2:]
    depth = 0
    for ch in sub:
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth = max(0, depth - 1)
        elif ch in '+*^' and depth == 0:
            return None
    return sub

def mat(s):
    cols = [tuple(int(v) for v in c.split(',')) for c in re.findall(r'\(([^)]*)\)', s)]
    return [c + (0,) * (3 - len(c)) for c in cols]

def main():
    import openpyxl
    wb = openpyxl.load_workbook(XLSX, read_only=True)
    ws = wb['To psi(I)']
    rows = [(i + 1, r[0], r[1]) for i, r in enumerate(ws.iter_rows(values_only=True))
            if r and isinstance(r[0], str) and r[0].startswith('(')
            and isinstance(r[1], str)]
    label = {m: lab for _, m, lab in rows}
    pure = [(n, m, lab, pure_sub(lab)) for n, m, lab in rows if pure_sub(lab)]
    print('To psi(I): %d rows, pure psi(W_alpha): %d rows' % (len(rows), len(pure)))

    out = os.path.join(os.path.dirname(__file__), '..', 'tmp', 'pure-rows.tsv')
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, 'w') as f:
        f.write('row\talpha\tbranch\tmatrix\n')
        for n, m, lab, a in pure:
            b = classify(mat(m))[0]
            f.write('%d\t%s\t%s\t%s\n' % (n, a, b, m))

    from collections import Counter
    stat = Counter()
    bad = []
    for n, m, lab, a in pure:
        M = mat(m)
        b = classify(M)[0]
        for k in (2, 3):
            E = expand(M, k)
            key = ''.join('(%d,%d,%d)' % c for c in E)
            lab2 = label.get(key)
            kind = ('absent' if lab2 is None
                    else 'pure' if pure_sub(lab2) else 'impure')
            stat[(b, kind)] += 1
            # compare against the dom correspondence's prediction
            if b in ('T2', 'T0') and kind == 'impure':
                bad.append((n, a, b, k, lab2))
            if b == 'T1' and kind == 'pure':
                bad.append((n, a, b, k, lab2))
    print('\nbranch x destination (n = 2 and 3 together):')
    for key in sorted(stat):
        print('  %-4s -> %-7s %5d' % (key[0], key[1], stat[key]))
    print('\nprediction violated (T2/T0 -> impure, T1 -> pure): %d' % len(bad))
    for v in bad[:10]:
        print('   ', v)
    branches = Counter(classify(mat(m))[0] for _, m, _, _ in pure)
    print('\nbranch distribution over the pure rows:', dict(branches))
    print('\nall done')

if __name__ == '__main__':
    main()
