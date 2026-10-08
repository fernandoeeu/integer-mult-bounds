// Independent verifier for PR 7's F3 five-subset producer (written from
// notes/prime-field28-construction.tex, not from prime_field_supports.cpp).
//
// Input: their merged global DAG (dag.bin: v, size, nr, args[size][2],
// roots[nr], active[size]) and their star templates (templates.bin).
// Every check below recomputes supports exactly as bitsets; nothing is hashed.
//
// Checks
//  T  topological order, every operand nonzero and earlier
//  P  every active addition has a common pair (core = intersection of its
//     five-sets has >= 2 points)
//  D  every active addition joins disjoint supports (exact bitsets)
//  O  roots: for every pair C exactly one root equal to A_C (all five-sets
//     containing C) and, for every 3-set E outside C, exactly one root equal to
//     D_{C,E} (five-sets meeting C u E exactly in C); nothing else
//  S  star resynthesis: for every 4-set B, the set of sums over B-stars that
//     are needed outside the star (by an active addition with smaller core or
//     by a root) is recomputed here; the matching template must compute every
//     one of them with disjoint additions from the leaves; gates are counted
//  N  final counts c = (active additions outside stars) + (template gates),
//     q = roots, R = c + q
// Optional: write the assembled final DAG (small h) for the Python checker.
//
// Usage: verify_dag H dag.bin templates.bin [final.bin]
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <unordered_map>
#include <vector>
#include <algorithm>
using u32 = uint32_t; using u64 = uint64_t;

static u64 binom(int n, int k) { if (k < 0 || k > n) return 0; u64 r = 1; for (int j = 1; j <= k; j++) r = r * (n + 1 - j) / j; return r; }
static int H;
static long long FAILS = 0;
#define FAIL(...) do { if (FAILS < 20) { fprintf(stdout, "FAIL: "); fprintf(stdout, __VA_ARGS__); fprintf(stdout, "\n"); } FAILS++; } while (0)

u32 rd(std::ifstream &f) { u32 x; f.read((char *)&x, 4); if (!f) { std::cerr << "short read\n"; exit(2); } return x; }

// local index of a five-set relative to its core K: points of [H]\K in
// increasing order get positions 0..; |K|=2 -> colex rank of the triple,
// |K|=3 -> colex rank of the pair
struct Frame {
  u32 K; int k; int pos[32]; int pts[32]; int n;
  std::vector<u32> unrank;  // local index -> five mask
  void init(u32 K_) {
    K = K_; k = __builtin_popcount(K); n = 0;
    for (int p = 0; p < H; p++) { pos[p] = -1; if (!(K >> p & 1)) { pos[p] = n; pts[n++] = p; } }
    unrank.clear();
    if (k == 2) { unrank.resize(binom(n, 3)); for (int c = 2; c < n; c++) for (int b = 1; b < c; b++) for (int a = 0; a < b; a++) unrank[binom(a, 1) + binom(b, 2) + binom(c, 3)] = K | 1u << pts[a] | 1u << pts[b] | 1u << pts[c]; }
    if (k == 3) { unrank.resize(binom(n, 2)); for (int b = 1; b < n; b++) for (int a = 0; a < b; a++) unrank[binom(a, 1) + binom(b, 2)] = K | 1u << pts[a] | 1u << pts[b]; }
  }
  u32 index(u32 five) const {  // five must contain K
    u32 r = five & ~K; int q[3]; int t = 0;
    while (r) { int p = __builtin_ctz(r); r &= r - 1; q[t++] = pos[p]; }
    std::sort(q, q + t);
    if (k == 2) return binom(q[0], 1) + binom(q[1], 2) + binom(q[2], 3);
    return binom(q[0], 1) + binom(q[1], 2);
  }
  size_t words() const { return (unrank.size() + 63) / 64; }
};

int main(int argc, char **argv) {
  if (argc < 4) { std::cerr << "usage\n"; return 2; }
  H = atoi(argv[1]);
  std::ifstream f(argv[2], std::ios::binary);
  u32 v = rd(f), size = rd(f), nr = rd(f);
  std::vector<u32> A(size), B(size);
  for (u32 i = 0; i < size; i++) { A[i] = rd(f); B[i] = rd(f); }
  std::vector<u32> roots(nr); for (auto &x : roots) x = rd(f);
  std::vector<uint8_t> active(size); f.read((char *)active.data(), size);
  if (v != binom(H, 5)) { FAIL("v=%u", v); }
  // input ids 1..v: colex order of five-sets (rank = sum C(b_j, j) + 1)
  std::vector<u32> five(v + 1, 0);
  {
    std::vector<u32> all;
    for (u32 m = 0; m < (1u << H); m++) if (__builtin_popcount(m) == 5) all.push_back(m);
    // colex order = increasing numeric order of masks
    for (u32 i = 0; i < v; i++) five[i + 1] = all[i];
  }
  // pass 1: cores, topology
  std::vector<u32> core(size, 0);
  for (u32 i = 1; i <= v; i++) { core[i] = five[i]; if (A[i] || B[i]) FAIL("input %u has args", i); }
  u64 nadd = 0, nact = 0;
  for (u32 x = v + 1; x < size; x++) {
    if (!A[x] || !B[x] || A[x] >= x || B[x] >= x) { FAIL("topology at %u", x); continue; }
    core[x] = core[A[x]] & core[B[x]];
    nadd++;
    if (active[x]) {
      nact++;
      if (!active[A[x]] || !active[B[x]]) FAIL("active node %u has inactive operand", x);
      if (__builtin_popcount(core[x]) < 2) FAIL("node %u without common pair", x);
    }
  }
  // roots grouped by core
  std::map<u32, std::vector<u32>> rootsByCore;
  for (u32 r : roots) { if (!active[r]) FAIL("inactive root"); rootsByCore[core[r]].push_back(r); }
  for (auto &kv : rootsByCore) if (__builtin_popcount(kv.first) != 2) FAIL("root with core size %d", __builtin_popcount(kv.first));
  if (rootsByCore.size() != binom(H, 2)) FAIL("roots cover %zu pairs", rootsByCore.size());
  // pass 2: supports
  std::unordered_map<u32, Frame> frames3;  // per 3-core
  std::vector<u64> pool3; std::vector<u32> off3(size, UINT32_MAX);
  std::vector<u32> fifth(size, 0);  // 4-core nodes: mask of fifth points
  Frame cur2; cur2.K = 0; std::unordered_map<u32, std::vector<u64>> sup2;
  std::set<std::pair<u32, u32>> seenD; u64 seenA = 0, rootsChecked = 0;
  std::set<u32> finished;
  auto members = [&](u32 a, std::vector<u32> &out) {  // five masks of support(a)
    u32 ca = core[a]; int k = __builtin_popcount(ca);
    if (a <= v) { out.push_back(five[a]); return; }
    if (k == 4) { u32 m = fifth[a]; while (m) { int p = __builtin_ctz(m); m &= m - 1; out.push_back(ca | 1u << p); } return; }
    if (k == 3) { Frame &F = frames3[ca]; const u64 *w = &pool3[off3[a]]; for (size_t j = 0; j < F.words(); j++) { u64 b = w[j]; while (b) { int t = __builtin_ctzll(b); b &= b - 1; out.push_back(F.unrank[j * 64 + t]); } } return; }
    if (k == 2) { auto &w = sup2.at(a); for (size_t j = 0; j < w.size(); j++) { u64 b = w[j]; while (b) { int t = __builtin_ctzll(b); b &= b - 1; out.push_back(cur2.unrank[j * 64 + t]); } } return; }
    FAIL("members of core size %d", k);
  };
  auto finish2 = [&]() {
    if (!cur2.K) return;
    if (finished.count(cur2.K)) FAIL("context %x resumed", cur2.K);
    finished.insert(cur2.K);
    size_t W = cur2.words(), nt = cur2.unrank.size();
    for (u32 r : rootsByCore[cur2.K]) {
      rootsChecked++;
      auto it = sup2.find(r); if (it == sup2.end()) { FAIL("root support missing"); continue; }
      auto &w = it->second; u64 cnt = 0; u32 cover = 0;
      for (size_t j = 0; j < W; j++) { u64 b = w[j]; cnt += __builtin_popcountll(b); while (b) { int t = __builtin_ctzll(b); b &= b - 1; cover |= cur2.unrank[j * 64 + t]; } }
      if (cnt == nt) { seenA++; continue; }  // A_C
      u32 E = ((1u << H) - 1) & ~cover;
      if (__builtin_popcount(E) != 3) { FAIL("root of context %x is neither A_C nor D_{C,E}", cur2.K); continue; }
      // exact: every triple of [H]\(C u E) present, nothing else
      u64 want = 0; bool ok = true;
      for (size_t i = 0; i < nt; i++) { bool in = !(cur2.unrank[i] & E); bool has = w[i / 64] >> (i % 64) & 1; if (in != has) ok = false; want += in; }
      if (!ok || want != cnt) FAIL("root D_{C,E} support inexact");
      if (!seenD.insert({cur2.K, E}).second) FAIL("duplicate D root");
    }
    sup2.clear();
  };
  std::vector<u32> tmp;
  for (u32 x = v + 1; x < size; x++) {
    if (!active[x]) continue;
    u32 K = core[x]; int k = __builtin_popcount(K);
    u32 a = A[x], b = B[x];
    if (k == 4) {
      u32 fa = a <= v ? five[a] & ~K : (core[a] == K ? fifth[a] : 0xffffffff);
      u32 fb = b <= v ? five[b] & ~K : (core[b] == K ? fifth[b] : 0xffffffff);
      if (fa == 0xffffffff || fb == 0xffffffff) { FAIL("4-core operand with other core"); continue; }
      if (fa & fb) FAIL("overlap in 4-star node %u", x);
      fifth[x] = fa | fb; continue;
    }
    if (k == 3) {
      Frame &F = frames3[K]; if (F.unrank.empty()) F.init(K);
      size_t W = F.words(); u32 o = pool3.size(); pool3.resize(o + W, 0); off3[x] = o;
      for (u32 c : {a, b}) {
        tmp.clear(); members(c, tmp);
        for (u32 s : tmp) { if ((s & K) != K) { FAIL("member outside core"); continue; } u32 i = F.index(s); u64 &w = pool3[o + i / 64]; if (w >> (i % 64) & 1) FAIL("overlap in 3-core node %u", x); w |= 1ull << (i % 64); }
      }
      continue;
    }
    if (k == 2) {
      if (K != cur2.K) { finish2(); cur2.init(K); }
      std::vector<u64> w(cur2.words(), 0);
      for (u32 c : {a, b}) {
        if (core[c] == K) { auto &wc = sup2.at(c); for (size_t j = 0; j < w.size(); j++) { if (w[j] & wc[j]) FAIL("overlap in 2-core node %u", x); w[j] |= wc[j]; } continue; }
        tmp.clear(); members(c, tmp);
        for (u32 s : tmp) { u32 i = cur2.index(s); if (w[i / 64] >> (i % 64) & 1) FAIL("overlap in 2-core node %u", x); w[i / 64] |= 1ull << (i % 64); }
      }
      sup2[x] = std::move(w); continue;
    }
    FAIL("core size %d", k);
  }
  finish2();
  if (seenA != binom(H, 2)) FAIL("A roots %llu", (unsigned long long)seenA);
  if (seenD.size() != binom(H, 2) * binom(H - 2, 3)) FAIL("D roots %zu", seenD.size());
  if (rootsChecked != nr) FAIL("roots checked %llu of %u", (unsigned long long)rootsChecked, nr);
  // star demand, recomputed here
  std::map<u32, std::set<u32>> demand; std::map<u32, u64> starNodes; u64 nonstar = 0;
  for (u32 x = v + 1; x < size; x++) {
    if (!active[x]) continue;
    int k = __builtin_popcount(core[x]);
    if (k == 4) { starNodes[core[x]]++; continue; }
    nonstar++;
    for (u32 c : {A[x], B[x]}) if (c > v && __builtin_popcount(core[c]) == 4) demand[core[c]].insert(fifth[c]);
  }
  for (u32 r : roots) if (__builtin_popcount(core[r]) == 4) demand[core[r]].insert(fifth[r]);
  // templates
  std::ifstream tf(argv[3], std::ios::binary);
  if ((int)rd(tf) != H) FAIL("template h");
  u32 nt = rd(tf); int L = H - 4;
  std::map<std::vector<u32>, std::pair<u32, std::vector<std::pair<u32, u32>>>> templ;
  u64 unusedGates = 0;
  for (u32 t = 0; t < nt; t++) {
    u32 nout = rd(tf), ng = rd(tf); std::vector<u32> tg(nout); for (auto &x : tg) x = rd(tf);
    std::vector<std::pair<u32, u32>> gates(ng); for (auto &g : gates) { g.first = rd(tf); g.second = rd(tf); }
    std::set<u32> have; for (int i = 0; i < L; i++) have.insert(1u << i);
    std::map<u32, int> uses;
    for (auto &g : gates) {
      if (!g.first || !g.second || (g.first & g.second)) FAIL("template gate not disjoint");
      if (!have.count(g.first) || !have.count(g.second)) FAIL("template operand not yet computed");
      if (!have.insert(g.first | g.second).second) FAIL("template recomputes a sum");
      uses[g.first]++; uses[g.second]++;
    }
    for (u32 x : tg) { if (!have.count(x)) FAIL("template misses a target"); uses[x]++; }
    for (auto &g : gates) if (!uses[g.first | g.second]) unusedGates++;
    std::vector<u32> key = tg; std::sort(key.begin(), key.end());
    templ[key] = {ng, gates};
  }
  u64 oldStar = 0, newStar = 0, starsUsed = 0;
  for (auto &kv : starNodes) oldStar += kv.second;
  std::map<u32, std::vector<u32>> starOrder;
  for (auto &kv : demand) {
    u32 Bk = kv.first; std::vector<u32> order;
    for (int x = 0; x < H; x++) if (!(Bk >> x & 1) && !(Bk >> (x ^ 1) & 1)) order.push_back(x);   // intact global pairs first
    for (int x = 0; x < H; x++) if (!(Bk >> x & 1) && (Bk >> (x ^ 1) & 1)) order.push_back(x);    // then partners of removed points
    if ((int)order.size() != L) FAIL("order size");
    std::vector<u32> key;
    for (u32 m : kv.second) { u32 z = 0; for (int j = 0; j < L; j++) if (m >> order[j] & 1) z |= 1u << j; if (__builtin_popcount(z) != __builtin_popcount(m)) FAIL("demand outside order"); key.push_back(z); }
    std::sort(key.begin(), key.end());
    auto it = templ.find(key);
    if (it == templ.end()) { FAIL("no template for star %x", Bk); continue; }
    newStar += it->second.first; starsUsed++; starOrder[Bk] = order;
  }
  // stars that have active nodes but no outside demand would be dropped entirely
  u64 starsWithoutDemand = 0; for (auto &kv : starNodes) if (!demand.count(kv.first)) starsWithoutDemand++;
  u64 c = nonstar + newStar;
  printf("{\"h\":%d,\"v\":%u,\"additions_total\":%llu,\"active_additions\":%llu,\"nonstar_active\":%llu,"
         "\"star_keys_with_nodes\":%zu,\"star_keys_demanded\":%zu,\"stars_without_outside_demand\":%llu,"
         "\"old_star_additions\":%llu,\"template_gates\":%llu,\"unused_template_gates\":%llu,\"templates\":%u,"
         "\"c\":%llu,\"q\":%u,\"R\":%llu,\"A_roots\":%llu,\"D_roots\":%zu,\"fails\":%lld}\n",
         H, v, (unsigned long long)nadd, (unsigned long long)nact, (unsigned long long)nonstar,
         starNodes.size(), demand.size(), (unsigned long long)starsWithoutDemand,
         (unsigned long long)oldStar, (unsigned long long)newStar, (unsigned long long)unusedGates, nt,
         (unsigned long long)c, nr, (unsigned long long)(c + nr), (unsigned long long)seenA, seenD.size(), FAILS);
  // optional: assembled final DAG for small h
  if (argc >= 5) {
    // ids: inputs 0..v-1 (colex), then additions; outputs (node, C mask, S mask or 0 for A_C)
    std::vector<u32> nid(size, UINT32_MAX); for (u32 i = 1; i <= v; i++) nid[i] = i - 1;
    std::map<u32, u32> idx5; for (u32 i = 1; i <= v; i++) idx5[five[i]] = i - 1;
    std::vector<std::pair<u32, u32>> adds; u32 next = v;
    std::map<std::pair<u32, u32>, u32> starNode;  // (B, fifth mask) -> new id
    for (auto &kv : demand) {
      u32 Bk = kv.first; auto &order = starOrder[Bk];
      std::vector<u32> key; for (u32 m : kv.second) { u32 z = 0; for (int j = 0; j < L; j++) if (m >> order[j] & 1) z |= 1u << j; key.push_back(z); }
      std::sort(key.begin(), key.end()); auto &gates = templ[key].second;
      std::map<u32, u32> loc; for (int j = 0; j < L; j++) loc[1u << j] = idx5[Bk | 1u << order[j]];
      for (auto &g : gates) { adds.push_back({loc[g.first], loc[g.second]}); loc[g.first | g.second] = next++; }
      for (auto &z : loc) { u32 m = 0; for (int j = 0; j < L; j++) if (z.first >> j & 1) m |= 1u << order[j]; starNode[{Bk, m}] = z.second; }
    }
    auto map_operand = [&](u32 c) -> u32 {
      if (c <= v) return nid[c];
      if (__builtin_popcount(core[c]) == 4) return starNode.at({core[c], fifth[c]});
      return nid[c];
    };
    for (u32 x = v + 1; x < size; x++) {
      if (!active[x] || __builtin_popcount(core[x]) == 4) continue;
      adds.push_back({map_operand(A[x]), map_operand(B[x])}); nid[x] = next++;
    }
    // star template nodes come first, so topological order holds: star
    // nodes only use inputs and earlier star nodes
    std::ofstream o(argv[4], std::ios::binary);
    auto w = [&](u32 x) { o.write((char *)&x, 4); };
    w(v); w(adds.size()); for (auto &p : adds) { w(p.first); w(p.second); }
    w(nr);
    for (u32 r : roots) { w(map_operand(r)); w(core[r]); }
  }
  return FAILS ? 1 : 0;
}
