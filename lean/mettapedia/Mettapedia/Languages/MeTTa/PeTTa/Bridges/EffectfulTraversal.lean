import Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource

/-! Ordered traversal composition retains the accumulated answer prefix and
executes every leaf against its current state. No commutation is assumed. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

theorem traverse_prefix (body : Body) (captured : List Subst) (before : Effects.State)
    (earlier collected : List Atom) :
    traverse body captured (before, earlier ++ collected) =
      (traverse body captured (before, collected)).map (fun receipt => (receipt.1, earlier ++ receipt.2)) := by
  induction captured generalizing before collected with
  | nil => rfl
  | cons bindings rest ih =>
      simp only [EffectfulQuerySource.traverse, List.append_assoc, ih, Option.map_bind, Function.comp_def]

theorem traverse_accumulate (body : Body) (captured : List Subst) (before : Effects.State)
    (earlier : List Atom) :
    traverse body captured (before, earlier) =
      (traverse body captured (before, [])).map (fun receipt => (receipt.1, earlier ++ receipt.2)) := by
  simpa only [List.append_nil] using traverse_prefix body captured before earlier []

theorem traverse_nested (body : Body) (inside : Subst → List Subst) (outer : List Subst)
    (before : Effects.State) (collected : List Atom) :
    traverse (fun bindings state => traverse body (inside bindings) (state, [])) outer (before, collected) =
      traverse body (outer.flatMap inside) (before, collected) := by
  induction outer generalizing before collected with
  | nil => rfl
  | cons bindings rest ih =>
      simp only [EffectfulQuerySource.traverse, List.flatMap_cons, traverse_append, ih]
      rw [traverse_accumulate body (inside bindings) before collected]
      simp only [Option.bind_map, Function.comp_def]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource
