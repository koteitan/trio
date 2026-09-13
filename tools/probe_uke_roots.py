"""追記531 の UKE の確認: 鎖を明示した塔の最内の中身に底を置いたときの根と展開。

塔（段 o = 1）: (0,0,0) N=(1,1,0) ℓ=(2,2,1) F(o+1)=(3,2,0) ℓ↑=(4,3,1) F(o+2)=(5,3,0) ℓ↑↑=(6,4,1)
最内の中身の底の段 = o（印なし）/ o+1（印 1）/ o+2（印 2）/ o+3（F の段）。
展開 [2] の写しの先頭の列が、根の写し（印 k の底なら F(o+k−1)、F の段なら最内の F）になることを見る。
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

BASE = [(0, 0, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 0), (6, 4, 1)]
CASES = [
    ('印なし（段 o = 1）', (7, 1, 0), (0, 0, 0)),
    ('印 1（段 2）', (7, 2, 0), (1, 1, 0)),
    ('印 2（段 3）', (7, 3, 0), (3, 2, 0)),
    ('F の段（段 4）', (7, 4, 0), (5, 3, 0)),
]

ok = True
for name, last, root in CASES:
    S = [list(c) for c in BASE] + [list(last)]
    E = [tuple(c) for c in trio.expand(S, 2)]
    copy = E[len(BASE):]
    # 写しの先頭は根の写し（行 0 だけずれ、行 1・行 2 は同じ）
    head = copy[0]
    good = head[1:] == root[1:]
    # 写しの中の行 1 は元の対応する列と同じ（Δ₁ = 0）
    ridx = BASE.index(root)
    seg = BASE[ridx:]
    same_row1 = [c[1] for c in copy] == [c[1] for c in seg]
    ok = ok and good and same_row1
    print(name, '写し =', copy, '根の写し', 'OK' if good else 'NG', '行1不変', 'OK' if same_row1 else 'NG')
print('ALL OK' if ok else 'FAIL')
