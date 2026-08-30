# -*- coding: utf-8 -*-
import sys, pickle
from collections import Counter, defaultdict
sys.path.insert(0, '/tmp/h1work'); sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')

def load(*names):
    R = []
    for n in names:
        R += pickle.load(open('/tmp/h1work/%s' % n, 'rb'))
    return R

def cw2(r):
    """_cw2 が新しく発火する柱か（closes_unit ではまだ閉じない (k,0,0)）。"""
    nx = r['dec']['nxt']
    return (nx is not None and nx[1] == 0 and nx[2] == 0
            and 2 <= nx[0] < r['feat']['p0'])

if __name__ == '__main__':
    S = load('S.pkl')
    T = load('T6.pkl', 'T5.pkl')
    for nm, R in (('シート', S), ('目標', T)):
        sub = [r for r in R if cw2(r)]
        print('%s: 決定 %d 本 / _cw2 発火 %d 本  深い %d 浅い %d'
              % (nm, len(R), len(sub),
                 sum(1 for r in sub if not r['shallow']),
                 sum(1 for r in sub if r['shallow'])))
