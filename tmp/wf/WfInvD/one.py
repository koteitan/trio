import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import probe_newpv3 as P
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',sys.argv[1])]
c,e=P.go(M);print(dict(c));print(e)
