"""F-level frame/residual check of one invocation per stage, any h."""
import time
from network import Labels, check_invocation, data_terminals, EdgeChecker
from f2 import Space


def run(C, R, recipe, node_label, stages=(1, 2, 3), verbose=True):
    labels = Labels(C, lambda key: node_label(C, key, Space))
    out = {}
    ec = EdgeChecker(labels)
    for j in stages:
        t = time.time()
        inv = recipe(C, R, reverse=(j == 2))
        src, snk = data_terminals(inv)
        rep = check_invocation(inv, labels, j, src, snk, ec=ec)
        loss = sum(d[2] for d in rep['dec'])
        kinds = {}
        for w, i, l, a, b in rep['dec']:
            kinds[(a, b, l)] = kinds.get((a, b, l), 0) + 1
        out[j] = dict(fails=rep['fails'], tot_abs=rep['tot_abs'], tot_signed=rep['tot_signed'],
                      loss=loss, n_dec=len(rep['dec']), n_edges=rep['n_edges'],
                      n_residuals=rep['n_residuals'], dec_kinds=kinds, nw=inv.nw)
        if verbose:
            print(f"  stage {j}: wires {inv.nw} edges {rep['n_edges']} distinct residuals {rep['n_residuals']} "
                  f"failures {len(rep['fails'])} decreasing edges {len(rep['dec'])} loss {loss} "
                  f"sum|d| {rep['tot_abs']} ({time.time()-t:.1f}s)")
            for f in rep['fails'][:5]:
                print('    FAIL', f)
    return out
