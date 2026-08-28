"""接頭辞を固定した全数展開で「木が 3 本以上」の残余を狩る（課題 R2 (3)）。"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r2
from r1ext import gen_ext

if __name__ == '__main__':
    pref = tuple(eval(sys.argv[1])); lim = int(sys.argv[2])
    t = time.time(); P = gen_ext(pref, lim)
    print('prefix', pref, 'lim', lim, ':', len(P), '%.1fs' % (time.time() - t),
          flush=True)
    r2.run(P, 'ext %s lim %d' % (str(pref), lim))
    # 木が 3 本以上のものだけ表にする
    big = [f for f in r2.FOREST if len(f['trees']) >= 3]
    print('木が 3 本以上:', len(big))
    for f in big[:10]:
        print('   ', ''.join(str(c).replace(' ', '') for c in f['M']),
              'd=', f['d'], 'rest=', f['rest'],
              [(t['m0'], t['rd'], t['omin']) for t in f['trees']])
