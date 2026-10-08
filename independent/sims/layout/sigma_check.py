"""Side check for the recursive-cost unrolling: b = s/W < m^sigma, i.e.
log_m(s/W) < sigma, for the h=25 complex constants (from the certificate) and
sigma = 1 - 418/10^12, evaluated with 80-digit decimal arithmetic."""
from decimal import Decimal as Dm, getcontext
getcontext().prec = 80
m, W, s = 15625, 58645352620000, 916333630984500000
sigma = 1 - Dm(418) / Dm(10) ** 12
lhs = (Dm(s) / Dm(W)).ln() / Dm(m).ln()
gap = sigma - lhs
print("log_m(s/W) =", +lhs)
print("sigma      =", +sigma)
print("gap        =", f"{gap:.6e}", "->", "holds" if gap > Dm(10) ** -60 else "FAILS")
