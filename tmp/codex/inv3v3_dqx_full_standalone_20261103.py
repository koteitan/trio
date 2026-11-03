"""Standalone full DQX audit, without chaining into the drop audit."""
from pathlib import Path
import sys, json, collections, time
from multiprocessing import Pool
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tmp/codex"))
import inv3v3_dqx_audit_20261101 as D
A = D.A

if __name__ == "__main__":
    out = ROOT / "tmp/codex/inv3v3_dqx_full_20261103.jsonl"
    files = json.loads((ROOT / "tmp/codex/inv3v3_inputs_sets_20261101.json").read_text())
    done = set()
    if out.exists():
        for line in out.read_text().splitlines():
            if line.strip():
                row = json.loads(line); done.add((row["set"], row["shard"]))
    for f in files:
        mats = A.load(f)
        for sh in range(0, len(mats), 10000):
            if (f, sh) in done:
                continue
            started = time.time(); cnt = collections.Counter(); ex = {}
            part = mats[sh:sh + 10000]
            with Pool(4, maxtasksperchild=100) as pool:
                batches = [part[j:j + 20] for j in range(0, len(part), 20)]
                for c, e in pool.imap_unordered(D.work, batches):
                    cnt.update(c)
                    for k, v in e.items():
                        if k not in ex or (len(v["matrix"]), v["matrix"]) < (len(ex[k]["matrix"]), ex[k]["matrix"]):
                            ex[k] = v
            row = {"set": f, "shard": sh, "total": len(mats), "n": len(part),
                   "seconds": round(time.time() - started, 2), "counts": dict(cnt), "examples": ex,
                   "n_values": [2, 3], "eta_cap": 128}
            with out.open("a") as fp:
                fp.write(json.dumps(row) + "\n")
            print(json.dumps({k: v for k, v in row.items() if k != "examples"}), flush=True)
            if cnt.get("exception.fail"):
                print("EXCEPTION", json.dumps(ex), flush=True)
