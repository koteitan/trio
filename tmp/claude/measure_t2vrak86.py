"""T2VRAK KAG (exact current form, tools/probe_t2vrak.measure: u in {v_P(i)} ∪ PathLvAll, u <= V) on all 86 sets."""
import sys, json, collections
from multiprocessing import Pool
for p in ['/home/koteitan/proofs/trio/tools', '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
import probe_t2vrak as K
from pv2 import load
if __name__ == '__main__':
    sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
    tot = collections.Counter(); exs = {}
    with Pool(4) as pool:
        for f in sets:
            for c, e in pool.imap_unordered(K.measure, load(f), chunksize=100):
                tot.update(c)
                for k, v in e.items(): exs.setdefault(k, v)
            print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', json.dumps(exs, default=str)[:4000])
