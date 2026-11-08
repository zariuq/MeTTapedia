import Mettapedia.Machines.ReadOnlyQueryDemand

/-! # Sequential composition of partially available query observations -/

set_option autoImplicit false

namespace Mettapedia.Machines.ReadOnlyQueryPartialComposition

open ReadOnlyQuery ReadOnlyQueryDemand

variable {Key Reply Answer Other : Type}

theorem run_demand_bind (available : Key → Option Reply) (program : Program Key Reply Answer)
    (next : Answer → Program Key Reply Other) :
    run available (demand (bind program next)) =
      let first := run available (demand program)
      match first.answer with
      | none => ⟨none, first.reads⟩
      | some answer =>
          let second := run available (demand (next answer))
          ⟨second.answer, first.reads ++ second.reads⟩ := by
  induction program with
  | pure answer => simp [ReadOnlyQuery.bind, demand, run]
  | read key more ih =>
      cases found : available key with
      | none => simp [ReadOnlyQuery.bind, demand, run, found]
      | some reply =>
          simp only [ReadOnlyQuery.bind, demand, run, found]
          rw [ih reply]
          cases selected : (run available (demand (more reply))).answer <;>
            simp [selected]

theorem run_demand_map (available : Key → Option Reply) (program : Program Key Reply Answer)
    (convert : Answer → Other) :
    run available (demand (map convert program)) =
      let result := run available (demand program)
      ⟨result.answer.map convert, result.reads⟩ := by
  rw [ReadOnlyQuery.map, run_demand_bind]
  cases selected : (run available (demand program)).answer <;> simp [selected, demand, run]

/-- Continuations need agree only at a result actually returned by the
first partial query. No coverage or termination of an unused branch is owed. -/
theorem run_demand_bind_congr (available : Key → Option Reply)
    (first second : Program Key Reply Answer)
    (left right : Answer → Program Key Reply Other)
    (before : run available (demand first) = run available (demand second))
    (after : ∀ answer, (run available (demand first)).answer = some answer →
      run available (demand (left answer)) = run available (demand (right answer))) :
    run available (demand (bind first left)) = run available (demand (bind second right)) := by
  rw [run_demand_bind, run_demand_bind, ← before]
  dsimp only
  cases selected : (run available (demand first)).answer with
  | none => rfl
  | some answer =>
      dsimp only
      rw [after answer selected]

end Mettapedia.Machines.ReadOnlyQueryPartialComposition
