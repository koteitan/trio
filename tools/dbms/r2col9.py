"""9 列の標準形の**全数**を流しながら測る（貯めない）。

`r2_e8.pkl`（8 列の標準形 全数）を読み、各行列に 9 列目を足して
`isstd` を通ったものだけ `conv3` にかける。分割は `shard/nshard`。
"""
import sys, os, time, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r2, rows3, core, gc
from core import isstd

if __name__ == '__main__':
    shard = int(sys.argv[1]); nsh = int(sys.argv[2])
    zcap = 1
    # メモリ節約: 8 列全数を 1 行列 24 バイトの生バイト列で持つ
    # （pickle の list of tuples は 3.4GB、bin は 17MB）
    with open('/home/koteitan/proofs/dbms/tools/dbms/r2_e8.bin', 'rb') as f:
        BIN = f.read()
    NE8 = len(BIN) // 24

    def get8(j):
        o = j * 24
        return tuple((BIN[o + 3 * k], BIN[o + 3 * k + 1], BIN[o + 3 * k + 2])
                     for k in range(8))
    E8 = range(NE8)
    t = time.time(); n9 = 0; ncand = 0; nproc = 0
    for i in E8:
        if i % nsh != shard:
            continue
        S = get8(i)
        # メモが青天井に伸びる（9 列は 1 個ずつしか問い合わせないので効かない）。
        # 注意: `i % N` だと N が 4 の倍数のとき shard 0 しか掃除しない。
        nproc += 1
        if nproc % 500 == 0:
            core._isstd_memo.clear(); core._exp_memo.clear()
            core._flat_memo.clear(); gc.collect()
        amax = S[-1][0] + 1
        for a in range(amax + 1):
            for b in range(a + 1):
                for c in range(min(b, zcap) + 1):
                    T = S + ((a, b, c),)
                    ncand += 1
                    if isstd(T, 'BMS'):
                        n9 += 1
                        r2.run1(T)
    print('== 9 列 shard %d/%d  候補 %d  標準形 %d  %.1fs'
          % (shard, nsh, ncand, n9, time.time() - t))
    for k in sorted(r2.C):
        print('   %-20s %d' % (k, r2.C[k]))
    with open('/home/koteitan/proofs/dbms/tools/dbms/r2_9_%d.pkl' % shard,
              'wb') as f:
        pickle.dump({'c': dict(r2.C), 'forest': r2.FOREST, 'n': n9}, f)
