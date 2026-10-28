// Offline endpoint edge collapses. Preserve link conditions and face
// orientation; constrain each collapse against incident planes. This is a mesh
// approximation, not a mathematical topology certificate or a global
// Hausdorff-error bound.
#include <algorithm>
#include <array>
#include <cmath>
#include <fstream>
#include <iostream>
#include <unordered_set>
#include <vector>
using namespace std;
using V = array<double, 3>;
using T = array<unsigned, 3>;
V sub(V a, V b) { return {a[0] - b[0], a[1] - b[1], a[2] - b[2]}; }
V cross(V a, V b) {
  return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2],
          a[0] * b[1] - a[1] * b[0]};
}
double dot(V a, V b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
// Distances are in normalized display coordinates; angle tests use squared cosines.
constexpr int COLLAPSE_PASSES = 8;
constexpr double MAX_EDGE_LENGTH_SQUARED = 0.0025;
constexpr double MIN_FACE_NORMAL_SQUARED = 1e-28;
constexpr double MIN_NORMAL_COSINE_SQUARED = 0.95;
bool preservesFaceOrientation(V before, V after) {
  const double alignment = dot(before, after);
  return alignment > 0 && alignment * alignment >=
      MIN_NORMAL_COSINE_SQUARED * dot(before, before) * dot(after, after);
}
int main(int argc, char **argv) {
  if (argc != 4 && argc != 5) {
    cerr << "usage: simplify INPUT_POSITIONS_NORMALS INPUT_INDICES OUTPUT_INDICES "
            "[TOLERANCE]\n";
    return 2;
  }
  double tolerance = argc == 5 ? stod(argv[4]) : 0.00018;
  if (!isfinite(tolerance) || tolerance <= 0 || tolerance > 0.01) {
    cerr << "Invalid tolerance\n";
    return 2;
  }
  ifstream pf(argv[1], ios::binary | ios::ate),
      tf(argv[2], ios::binary | ios::ate);
  if (!pf || !tf) {
    cerr << "Cannot open input\n";
    return 2;
  }
  size_t nv = pf.tellg() / 24, nt = tf.tellg() / 12;
  pf.seekg(0);
  tf.seekg(0);
  vector<V> p(nv), normals(nv);
  for (size_t i = 0; i < nv; i++) {
    float q[6];
    pf.read((char *)q, 24);
    p[i] = {q[0], q[1], q[2]};
    normals[i] = {q[3], q[4], q[5]};
  }
  vector<T> f(nt);
  tf.read((char *)f.data(), nt * 12);
  vector<unordered_set<unsigned>> star(nv);
  vector<bool> alive(nt, true);
  for (unsigned i = 0; i < nt; i++)
    for (auto v : f[i])
      star[v].insert(i);
  size_t count = nt;
  for (int pass = 0; pass < COLLAPSE_PASSES; pass++) {
    size_t before = count;
    for (unsigned b = 0; b < nv; b++) {
      if (star[b].empty())
        continue;
      unordered_set<unsigned> nb;
      for (auto t : star[b])
        for (auto v : f[t])
          if (v != b)
            nb.insert(v);
      vector<pair<double, unsigned>> candidates;
      for (auto a : nb)
        candidates.push_back({dot(sub(p[a], p[b]), sub(p[a], p[b])), a});
      sort(candidates.begin(), candidates.end());
      for (auto [len, a] : candidates) {
        if (len > MAX_EDGE_LENGTH_SQUARED)
          continue;
        unordered_set<unsigned> na, opp;
        vector<unsigned> shared;
        for (auto t : star[a])
          for (auto v : f[t])
            if (v != a)
              na.insert(v);
        for (auto t : star[b])
          if (star[a].count(t)) {
            shared.push_back(t);
            for (auto v : f[t])
              if (v != a && v != b)
                opp.insert(v);
          }
        if (shared.size() != 2 || opp.size() != 2)
          continue;
        unsigned common = 0;
        bool good = true;
        for (auto v : nb)
          if (na.count(v)) {
            common++;
            if (!opp.count(v))
              good = false;
          }
        if (!good || common != 2)
          continue;
        // Bound distance to every old incident plane; preserve face
        // orientation.
        for (auto t : star[b]) {
          auto old = f[t];
          V n = cross(sub(p[old[1]], p[old[0]]), sub(p[old[2]], p[old[0]]));
          double nn = dot(n, n);
          if (nn < MIN_FACE_NORMAL_SQUARED) {
            good = false;
            break;
          }
          double d = dot(n, sub(p[a], p[b]));
          if (d * d > tolerance * tolerance * nn) {
            good = false;
            break;
          }
          if (star[a].count(t))
            continue;
          auto q = old;
          for (auto &v : q)
            if (v == b)
              v = a;
          V n2 = cross(sub(p[q[1]], p[q[0]]), sub(p[q[2]], p[q[0]]));
          V smooth{};
          for (auto v : q)
            for (int j = 0; j < 3; j++) smooth[j] += normals[v][j];
          if (!preservesFaceOrientation(n, n2) || dot(n2, smooth) <= 0) {
            good = false;
            break;
          }
        }
        if (!good)
          continue;
        vector<unsigned> incident(star[b].begin(), star[b].end());
        for (auto t : incident) {
          if (star[a].count(t)) {
            alive[t] = false;
            for (auto v : f[t])
              star[v].erase(t);
            count--;
          } else {
            for (auto &v : f[t])
              if (v == b)
                v = a;
            star[a].insert(t);
          }
        }
        star[b].clear();
        break;
      }
    }
    cerr << "pass " << pass << " triangles " << count << endl;
    if (before == count)
      break;
  }
  ofstream out(argv[3], ios::binary);
  for (size_t i = 0; i < nt; i++)
    if (alive[i])
      out.write((char *)f[i].data(), 12);
}
