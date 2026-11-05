"""HardArg (V3DropStrong.lean) on all 86 input sets, via tools/probe_dropres.measure (exact Lean form, below SRO)."""
import sys, json, collections
from multiprocessing import Pool
sys.path.insert(0, '/home/koteitan/proofs/trio/tools'); sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfDrE')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfInvD')
import probe_dropres as D
from pv2 import load
if __name__ == '__main__':
    sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
    tot = collections.Counter(); exs = {}
    with Pool(4) as pool:
        for f in sets:
            for c, e in pool.imap_unordered(D.measure, load(f), chunksize=50):
                tot.update({k: v for k, v in c.items() if k.startswith('HardArg')})
                for k, v in e.items():
                    if k.startswith('HardArg'): exs.setdefault(k, v)
            print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', json.dumps(exs, default=str)[:3000])
