import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3
MODE = sys.argv[1]; lim = int(sys.argv[2])
if MODE == 'noaw':
    rows3.V17['awflip'] = False
elif MODE == 'noh1':
    rows3.V14['h1'] = False
elif MODE == 'awmono':
    # 群 A の犯人 `is_w_col(Mo[-1])` を消した版（第 1 選言を落とす）
    _p = rows3.par0; _w = rows3.is_w_col
    def aw2(Mo, off):
        a01 = _p(Mo, off)
        if a01 >= 0 and off - a01 > 3:
            return False
        p0 = Mo[off][0]
        for t in range(off - 1, -1, -1):
            if Mo[t][0] < p0:
                return False
            if Mo[t][0] == p0:
                return Mo[t][0] == Mo[t][1] and Mo[t][0] >= 1
        return False
    rows3.aw_flip = aw2
print('== 版 =', MODE)
rows3.main(lim=lim, imgc=3)
