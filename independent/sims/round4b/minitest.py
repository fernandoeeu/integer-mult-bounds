import sys, importlib.util, inspect, traceback, os
path = sys.argv[1]; sys.path[:0] = [os.path.dirname(path), os.path.join(os.path.dirname(path), '..', 'scripts')]
spec = importlib.util.spec_from_file_location('t', path); mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
p = f = 0
for n, fn in sorted(vars(mod).items()):
    if n.startswith('test') and callable(fn) and not inspect.signature(fn).parameters:
        try: fn(); p += 1
        except Exception: f += 1; print('FAIL', n); traceback.print_exc()
print(f'{p} passed, {f} failed')
