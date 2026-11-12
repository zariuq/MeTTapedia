// Incremental evaluation of an already compiled arithmetic DAG.
// No Boolean compilation or representation-specific transformation occurs here.
#include <algorithm>
#include <cstdint>
#include <functional>
#include <stdexcept>
#include <vector>

struct Circuit {
  std::uint32_t n, lanes;
  std::vector<std::uint32_t> op, offsets, children;
  std::vector<std::vector<std::uint32_t>> parents;
  std::vector<double> values;
  std::vector<std::uint64_t> queued;
  std::vector<std::uint32_t> heap;
  std::uint64_t epoch = 0, visits = 0, arithmetic = 0;

  Circuit(std::uint32_t nodes, std::uint32_t width, const std::uint32_t* operations,
          const std::uint32_t* starts, const std::uint32_t* edges)
      : n(nodes), lanes(width), op(operations, operations + nodes),
        offsets(starts, starts + nodes + 1), children(edges, edges + starts[nodes]),
        parents(nodes), values(static_cast<std::size_t>(nodes) * width), queued(nodes, 0) {
    if (!lanes || offsets[0] != 0) throw std::invalid_argument("invalid graph shape");
    for (std::uint32_t i = 0; i < n; ++i) {
      if (op[i] > 4 || offsets[i] > offsets[i + 1]) throw std::invalid_argument("invalid operation");
      for (std::uint32_t k = offsets[i]; k < offsets[i + 1]; ++k) {
        if (children[k] >= i) throw std::invalid_argument("graph is not topological");
        parents[children[k]].push_back(i);
      }
    }
  }

  bool compute(std::uint32_t i) {
    bool changed = false;
    for (std::uint32_t lane = 0; lane < lanes; ++lane) {
      double result = op[i] == 2 || op[i] == 4 ? 1.0 : 0.0;
      if (op[i] == 0) result = values[static_cast<std::size_t>(i) * lanes + lane];
      for (std::uint32_t k = offsets[i]; k < offsets[i + 1]; ++k) {
        double value = values[static_cast<std::size_t>(children[k]) * lanes + lane];
        if (op[i] == 3) result += value;
        else if (op[i] == 4) result *= value;
        ++arithmetic;
      }
      auto& previous = values[static_cast<std::size_t>(i) * lanes + lane];
      changed |= previous != result;
      previous = result;
    }
    ++visits;
    return changed;
  }

  void enqueue(std::uint32_t node) {
    if (queued[node] == epoch) return;
    queued[node] = epoch;
    heap.push_back(node);
    std::push_heap(heap.begin(), heap.end(), std::greater<std::uint32_t>());
  }

  void initialize(const double* input) {
    std::copy(input, input + values.size(), values.begin());
    for (std::uint32_t i = 0; i < n; ++i) compute(i);
  }

  bool update(std::uint32_t count, const std::uint32_t* indices, const double* input) {
    for (std::uint32_t j = 0; j < count; ++j)
      if (indices[j] >= n || op[indices[j]] != 0) return false;
    if (++epoch == 0) { std::fill(queued.begin(), queued.end(), 0); ++epoch; }
    heap.clear();
    for (std::uint32_t j = 0; j < count; ++j) {
      const auto i = indices[j];
      bool changed = false;
      for (std::uint32_t lane = 0; lane < lanes; ++lane) {
        auto& previous = values[static_cast<std::size_t>(i) * lanes + lane];
        double value = input[static_cast<std::size_t>(j) * lanes + lane];
        changed |= previous != value;
        previous = value;
      }
      if (changed) for (auto parent : parents[i]) enqueue(parent);
    }
    while (!heap.empty()) {
      std::pop_heap(heap.begin(), heap.end(), std::greater<std::uint32_t>());
      auto node = heap.back();
      heap.pop_back();
      if (compute(node)) for (auto parent : parents[node]) enqueue(parent);
    }
    return true;
  }
};

extern "C" {
void* closure_dag_create(std::uint32_t n, std::uint32_t lanes, const std::uint32_t* op,
                         const std::uint32_t* offsets, const std::uint32_t* edges) {
  try { return new Circuit(n, lanes, op, offsets, edges); } catch (...) { return nullptr; }
}
void closure_dag_destroy(void* pointer) { delete static_cast<Circuit*>(pointer); }
void closure_dag_initialize(void* pointer, const double* input) {
  static_cast<Circuit*>(pointer)->initialize(input);
}
int closure_dag_update(void* pointer, std::uint32_t count, const std::uint32_t* indices, const double* input) {
  return static_cast<Circuit*>(pointer)->update(count, indices, input);
}
double* closure_dag_values(void* pointer) { return static_cast<Circuit*>(pointer)->values.data(); }
void closure_dag_stats(void* pointer, std::uint64_t* result) {
  auto* c = static_cast<Circuit*>(pointer);
  result[0] = c->visits; result[1] = c->arithmetic;
}
void closure_dag_reset_stats(void* pointer) {
  auto* c = static_cast<Circuit*>(pointer); c->visits = c->arithmetic = 0;
}
}
