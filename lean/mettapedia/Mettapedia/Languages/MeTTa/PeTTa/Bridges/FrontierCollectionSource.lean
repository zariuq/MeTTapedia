import Mettapedia.Languages.MeTTa.PeTTa.StreamSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource

/-!
# Source frontier collection after ordered effectful visits

The captured frontier is unpacked as values. Each value gets a fresh lexical
binding; the body visits run in order against the current state. Only their
completed answer packet is deduplicated. Refusal of a private worker is not
an empty frontier and grants no rollback permission after native publication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierCollectionSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics EffectfulQuerySource

def visits (frontier itemName : String) (body : Atom) : Atom :=
  .expression [.symbol "let", .var itemName, .expression [.symbol "superpose", .var frontier], body]

def source (frontier itemName : String) (body : Atom) : Atom :=
  .expression [.symbol "collapse", StreamSource.unique (visits frontier itemName body)]

def environments (caller : Subst) (itemName : String) (values : List Atom) : List Subst :=
  values.map (fun value => (itemName, value) :: caller)

def run (worker : Body) (frontier itemName : String) (caller : Subst) (before : Effects.State) : Option (Effects.State × List Atom) := do
  match Subst.lookup caller frontier with
  | some (.expression values) =>
      if Subst.lookup caller itemName = none then do
        let result ← traverse worker (environments caller itemName values) (before, [])
        some (result.1, result.2.eraseDups)
      else none
  | _ => none

private theorem trans {system : Mettapedia.GSLT.GSLT} {a b c : system.Term}
    (first : system.MultiStep a b) (second : system.MultiStep b c) : system.MultiStep a c := by
  induction first with
  | refl _ => exact second
  | step step _ ih => exact .step step (ih second)

theorem visits_returns (program : Program) (expression : Atom) (worker : Body)
    (law : ∀ bindings before after answers, worker bindings before = some (after, answers) →
      Returns program bindings before expression after answers)
    (frontier itemName : String) (caller : Subst) (values : List Atom)
    (captured : Subst.lookup caller frontier = some (.expression values))
    (fresh : Subst.lookup caller itemName = none)
    (before after : Effects.State) (answers : List Atom)
    (completed : traverse worker (environments caller itemName values) (before, []) = some (after, answers)) :
    Returns program caller before (visits frontier itemName expression) after answers := by
  have produced := StreamSource.dynamic_superpose_returns program caller before frontier values captured
  refine .step (.let_enter rfl) (trans (path_with_caller_frames program [.bind caller (.var itemName) expression] produced) ?_)
  refine .step (.binding_return rfl rfl) ?_
  have visited := sequence_returns program expression worker (environments caller itemName values)
    (fun bindings _ before after answers done => law bindings before after answers done) before after [] answers completed
  simpa [environments, matchBinding, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, fresh,
    List.filterMap_eq_map, List.map_map, Function.comp_def, withFrames, finished] using visited

theorem source_returns (program : Program) (expression : Atom) (worker : Body)
    (law : ∀ bindings before after answers, worker bindings before = some (after, answers) →
      Returns program bindings before expression after answers)
    (frontier itemName : String) (caller : Subst) (before after : Effects.State) (next : List Atom)
    (completed : run worker frontier itemName caller before = some (after, next)) :
    PureReturns program caller before (source frontier itemName expression) after (.expression next) := by
  unfold run at completed
  split at completed
  next values captured =>
    split at completed
    next fresh =>
      obtain ⟨result, visited, same⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact collapse_returns program caller before result.1 _ _
        (StreamSource.unique_returns program caller before result.1 _ result.2
          (visits_returns program expression worker law frontier itemName caller values captured fresh before result.1 result.2 visited))
    next => cases completed
  next => cases completed

theorem exact_raw_observation (worker : Body) (frontier itemName : String) (caller : Subst)
    (before after : Effects.State) (next : List Atom)
    (completed : run worker frontier itemName caller before = some (after, next)) :
    ∃ values answers, Subst.lookup caller frontier = some (.expression values) ∧
      Subst.lookup caller itemName = none ∧
      traverse worker (environments caller itemName values) (before, []) = some (after, answers) ∧ next = answers.eraseDups := by
  unfold run at completed
  split at completed
  next values captured =>
    split at completed
    next fresh =>
      obtain ⟨result, visited, same⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨values, result.2, captured, fresh, visited, rfl⟩
    next => cases completed
  next => cases completed

theorem next_membership (worker : Body) (frontier itemName : String) (caller : Subst)
    (before after : Effects.State) (next : List Atom)
    (completed : run worker frontier itemName caller before = some (after, next)) :
    ∃ values answers, traverse worker (environments caller itemName values) (before, []) = some (after, answers) ∧
      ∀ value, value ∈ next ↔ value ∈ answers := by
  obtain ⟨values, answers, _, _, visited, rfl⟩ := exact_raw_observation worker frontier itemName caller before after next completed
  exact ⟨values, answers, visited, fun _ => by simp⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierCollectionSource
