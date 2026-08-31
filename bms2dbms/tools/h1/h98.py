# -*- coding: utf-8 -*-
"""**(w3) 箱を広げて `p_rel >= 2` を出しにいく。**"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
from h96 import run

if __name__ == '__main__':
    print('## (w3) `p_rel >= 2`: 箱を広げる')
    print()
    run((2, 3, 4), 4, 4, tag='(B) 行0∈[1,3]・行1<4、')
    run((2, 3), 5, 5, tag='(C) 行0∈[1,4]・行1<5、')
