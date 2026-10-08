"""Run PR 7's own global producer pipeline at ground size H (even, 8..28) in
work_h{H}/, keeping its intermediate files: local.bin (their local producer),
dag.bin (their merged, pre-resynthesis global DAG), demands.txt and
templates.bin (their star templates). Prints their own JSON summaries.
This is the NON-independent part; verify_dag.cpp then checks the files.
Usage: python3 run_theirs.py H
"""
import sys, os, json, subprocess, time
HERE = os.path.dirname(os.path.abspath(__file__))
PR7 = os.path.join(HERE, '..', 'pr7', 'scripts')
sys.path.insert(0, PR7)
from pathlib import Path
import prime_field_circuit as P

h = int(sys.argv[1])
work = Path(HERE) / f'work_h{h}'
work.mkdir(exist_ok=True)
t0 = time.time()
local = work / 'local.bin'
res = P.export_local(local, n=h - 2)
print('their local producer:', json.dumps(res, sort_keys=True), f'({time.time()-t0:.0f}s)', flush=True)
binary = work / 'check'
if not binary.exists():
    subprocess.run(['c++', '-std=c++17', '-O2', os.path.join(PR7, 'prime_field_supports.cpp'), '-o', str(binary)], check=True)
dag = work / 'dag.bin'
demands = work / 'demands.txt'
first = subprocess.run([str(binary), str(local), str(dag), str(demands)], check=True, capture_output=True, text=True)
print('their global pass 1:', first.stdout.strip(), flush=True)
templates = work / 'templates.bin'
rep = P.export_templates(demands, templates, h=h)
print('their templates:', json.dumps(rep, sort_keys=True), flush=True)
second = subprocess.run([str(binary), str(local), '-', str(demands), str(templates)], check=True, capture_output=True, text=True)
print('their global pass 2:', second.stdout.strip().replace('\n', ' | '), flush=True)
print(f'total {time.time()-t0:.0f}s')
