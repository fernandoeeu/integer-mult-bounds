import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import controls
print('negative controls (each must show a rejection or a changed count):')
controls.run_all()
