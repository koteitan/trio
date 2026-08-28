import sys, os, importlib
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import cofinal
mod = importlib.import_module(sys.argv[1])
cofinal.score(int(sys.argv[2]), 16, f=mod.b2d3)
