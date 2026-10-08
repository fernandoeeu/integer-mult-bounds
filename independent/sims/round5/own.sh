#!/bin/sh
# Non-independent signal: each PR's own checks in scratch checkouts (git archive of pinned heads).
cd "$(dirname "$0")"; L=$(pwd)/logs; st=0
export PYTHONDONTWRITEBYTECODE=1
( cd pr14 && timeout 1200 nice python3 research/source-frame-corners/witness.py ) > $L/own_pr14_witness.log 2>&1 || st=1
( cd pr15 && timeout 1200 nice python3 -m unittest tests.test_source_frame_stream_network tests.test_complex_all_residuals ) > $L/own_pr15_tests.log 2>&1 || st=1
( cd pr16 && timeout 1200 nice python3 -m unittest tests.test_nested_source_integration ) > $L/own_pr16_tests.log 2>&1 || st=1
( cd pr16 && timeout 1200 nice python3 research/nested-source/verify.py ) > $L/own_pr16_verify.log 2>&1 || st=1
for f in own_pr14_witness own_pr15_tests own_pr16_tests own_pr16_verify; do echo "== $f"; tail -n 4 $L/$f.log; done
echo "own status $st"; exit $st
