"""Serial stage runner: resume frame/QN/QR, then exact U inputs, then DQX."""
from pathlib import Path
import json, os, subprocess, sys, time
ROOT = Path(__file__).resolve().parents[2]
SETS = json.loads((ROOT / "tmp/codex/inv3v3_inputs_sets_20261101.json").read_text())
PY = sys.executable

def run(label, cmd, env_updates=None):
    env = os.environ.copy()
    env.pop("V3_AUDIT_STAGE", None)
    env.pop("V3_DQX_STAGE", None)
    if env_updates:
        env.update(env_updates)
    print(json.dumps({"stage": label, "event": "start", "command": cmd, "time": time.time()}), flush=True)
    result = subprocess.run(cmd, cwd=ROOT, env=env)
    print(json.dumps({"stage": label, "event": "end", "exit": result.returncode, "time": time.time()}), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)

run("frame_qn_qr", [PY, str(ROOT / "tmp/codex/inv3v3_frame_qn_audit_20261101.py"),
    str(ROOT / "tmp/codex/inv3v3_frame_qn_full_20261101.jsonl"), "4", *SETS],
    {"V3_AUDIT_KEEP_GOING": "1"})
run("exact_upg_inputs", [PY, str(ROOT / "tmp/codex/inv3v3_upg_inputs_audit_20261103.py"),
    str(ROOT / "tmp/codex/inv3v3_upg_inputs_full_20261103.jsonl"), "4", *SETS])
run("dqx", [PY, str(ROOT / "tmp/codex/inv3v3_dqx_full_standalone_20261103.py")])
