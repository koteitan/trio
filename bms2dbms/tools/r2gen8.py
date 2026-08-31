"""gen3(8) の 8 列だけを pickle して、9 列の全数を分割して回せるようにする。"""
import sys, os, time, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rows3 import gen3

if __name__ == '__main__':
    t = time.time()
    G = gen3('BMS', 8, zcap=1)
    E8 = [tuple(M) for M in G if len(M) == 8]
    print('gen3<=8', len(G), ' 8 列', len(E8), '%.1fs' % (time.time() - t))
    with open('/home/koteitan/proofs/dbms/bms2dbms/tools/r2_e8.pkl', 'wb') as f:
        pickle.dump(E8, f, protocol=4)
    print('saved')
