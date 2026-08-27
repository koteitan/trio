"""実験旗の組み合わせを rows3.check + sheet3 で採点する。
    COMBOS='[["a","b"],[]]' python3 score.py [lim] [imgc]
"""
import sys, os, json, time, io, contextlib, re
sys.path.insert(0, '/tmp/claude-1000/-home-koteitan-proofs-dbms/ebd5ffaf-97c2-45bc-92a0-5391fe3b1a6d/scratchpad')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3t, sheet3

FLAGS = list(rows3t.VX.keys())
LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 5
IMGC = int(sys.argv[2]) if len(sys.argv) > 2 else 3


def setflags(on):
    for k in FLAGS:
        rows3t.VX[k] = (k in on)


A = sorted(rows3.gen3('BMS', LIM, zcap=1), key=rows3.key)
print('lim=%d imgc=%d  %d 個' % (LIM, IMGC, len(A)), flush=True)

COMBOS = json.loads(os.environ.get('COMBOS', '[[]]'))
for c in COMBOS:
    t = time.time()
    setflags(set(c))
    f = rows3t.b2d3
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        sh = sheet3.score(f=f, show_n=0)
        rows3.check(f, A, verbose=0, imgc=IMGC)
    txt = buf.getvalue()
    g = lambda pat: (re.search(pat, txt).group(1) if re.search(pat, txt) else '?')
    print('=== %s   (%.0fs)' % (','.join(sorted(c)) or '(none)', time.time() - t))
    print('    sheet=%d/%d  非標準=%s  順序=%s  衝突=%s  z0=%s  d2b3=%s  C1=%s C2=%s  Img破れ=%s'
          % (sh[0], sh[1],
             g(r'像が DBMS 非標準 : (\d+)'),
             g(r'順序保存の違反 : (\d+)'),
             g(r'衝突 (\d+) 組'),
             g(r'z=0 で 2 行版と食い違い : (\d+)'),
             g(r'!= M : (\d+)'),
             g(r'共終性 C1 の破れ : (\d+)'),
             g(r'C2 の破れ : (\d+)'),
             g(r'破れた A (\d+) 個')), flush=True)
