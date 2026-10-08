#!/usr/bin/env bash
# re-run the quick steps of run_all.sh to populate logs/ (same commands)
cd "$(dirname "$0")"
L=$(pwd)/logs
(cd pr7b && nice python3 net.py 8 mine --three > $L/pr7b_mine_h8.log 2>&1
 for h in 10 12; do nice python3 run_theirs.py $h > $L/pr7b_theirs_h$h.log 2>&1; ./verify_dag $h work_h$h/dag.bin work_h$h/templates.bin work_h$h/final.bin > $L/pr7b_verify_h$h.log 2>&1; done
 nice python3 controls.py 8 > $L/pr7b_controls.log 2>&1
 nice python3 net.py 10 final work_h10/final.bin > $L/pr7b_final_h10.log 2>&1
 nice python3 net.py 10 mine > $L/pr7b_mine_h10.log 2>&1)
(cd pr7c && for h in 8 10 12; do nice python3 adapter.py $h --frames --scalar $( [ $h -le 10 ] && echo --three ) > $L/pr7c_h$h.log 2>&1; done
 nice python3 controls.py 10 > $L/pr7c_controls.log 2>&1)
(cd pr8geo && for n in 6 7 8; do nice python3 build.py $n --frames --scalar --three > $L/pr8_n$n.log 2>&1; done
 nice python3 controls.py 7 > $L/pr8_controls.log 2>&1)
(cd lib && nice python3 step_tensor_phase.py pr8 6 1.0 > $L/pr8_tensor_phase_n6.log 2>&1)
nice python3 arith.py > $L/arith.log 2>&1
echo done > $L/quick_chain.done
