"""Negative controls: deliberately broken variants of the construction must be
rejected by the same checker, showing that the checks have teeth."""
from fractions import Fraction as F
import layout_sim as L
from layout_sim import Params, run_layout, LayoutFailure


def base():
    # m=2, W=3, d=64, K=32, G=1: q0 = 2*7 = 14, qF = 4, qB = 2, Q0 = 20 < D = 64,
    # k0 = 6, largest piece 32 so 5 = k0 - 1 nested splits occur
    return Params(m=2, W=3, d=64, D=64, K=32, G=1, beta=F(1, 1000))


def expect_fail(name, fn):
    try:
        fn()
        print(f"[NOT CAUGHT] {name}")
        return False
    except LayoutFailure as e:
        print(f"[caught] {name}: {e}")
        return True


ok = True
# control: the unmutated construction passes
st = run_layout(base(), mode="full")
print(f"[control passes] nodes={st.nodes} compact={st.compact_nodes} max_depth={st.max_depth}")

# 1. pad only to a multiple of W^(k0-2).  (W^(k0-1) would NOT be caught, and
# rightly so: splits per piece are at most floor(log_m(D-Q0)) <= k0-1 because
# D - Q0 < d <= m^k0, so the stated W^k0 has one factor W of slack.)
orig_pad = L.pad_rows
def pad_short(pr, stats):
    pr.k0 -= 2
    r = orig_pad(pr, stats)
    pr.k0 += 2
    return r
L.pad_rows = pad_short
ok &= expect_fail("padding to W^(k0-2) only", lambda: run_layout(base(), mode="full"))
L.pad_rows = orig_pad

# 2. front reservation of only ceil(H/K) chunks
orig_derive = Params.derive
def derive_short(self):
    orig_derive(self)
    self.qF = L.cdiv(self.H, self.K)
    self.Q0 = self.q0 + self.qF + self.qB
    return self
Params.derive = derive_short
ok &= expect_fail("front reservation ceil(H/K)", lambda: run_layout(base(), mode="full"))
Params.derive = orig_derive

# 3. back field carved from the front block (does not follow the slots)
orig_fb = L.front_back_fields
def fb_wrong(pr, n):
    fs, mid, back = orig_fb(pr, n)
    fs = [L.Field("b" if x.kind == "t" else x.kind, x.start, x.length) for x in fs]
    back = [L.Field("t" if x.kind == "b" else x.kind, x.start, x.length) for x in back]
    return fs, mid, back
L.front_back_fields = fb_wrong
ok &= expect_fail("t/b swapped (temporary b before slots)", lambda: run_layout(base(), mode="full"))
L.front_back_fields = orig_fb

# 4. stopping rule e <= d^beta replaced by e <= 0 (never stop) -> splits e=1
orig_lt = L.lt_power
L.lt_power = lambda e, d, beta: False
ok &= expect_fail("never stop", lambda: run_layout(base(), mode="full"))
L.lt_power = orig_lt

# 5. q0 too small: only ceil(log2 W) chunks with K=1 (row range < W^k0)
def derive_q0(self):
    orig_derive(self)
    self.q0 = 1
    self.Q0 = self.q0 + self.qF + self.qB
    return self
Params.derive = derive_q0
ok &= expect_fail("row index of one 1-bit chunk", lambda: run_layout(
    Params(m=2, W=3, d=64, D=64, K=1, G=0, beta=F(1, 1000)), mode="full"))
Params.derive = orig_derive

print("negative controls:", "all caught" if ok else "SOME NOT CAUGHT")
