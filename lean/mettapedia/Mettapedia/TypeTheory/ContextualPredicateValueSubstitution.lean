import Mettapedia.TypeTheory.ContextualPredicateCapabilities
import Mettapedia.TypeTheory.ContextualModelTelescopes

/-!
# Complete proposition and refinement values under substitution

The readouts retain both the type presentation and the supplied dependent
section. Refinement guards are transported through the actual self-extension
square. Introduction and forgetting use only their local chosen-operation
laws; no syntax evaluator or complete-judgment compatibility is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateValueSubstitution

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualModelTelescopes
open ContextualTypeOperations ContextualProductComparison

universe c s t m p
variable {C : Cwf.{c, s, t, m}}
variable {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
variable {source target : C.Ctx}

namespace PropositionOperations

variable (operations : ContextualPredicateCapabilities.PropositionOperations doctrine)

def substitute (substitution : C.Sub source target) (term : C.Tm target (operations.omega target)) :
    C.Tm source (operations.omega source) :=
  cast (congrArg (C.Tm source) (operations.omega_substitution substitution)) (C.tmSub term substitution)

theorem substitute_heq (substitution : C.Sub source target) (term : C.Tm target (operations.omega target)) :
    HEq (substitute operations substitution term) (C.tmSub term substitution) := cast_heq _ _

theorem value_substitute (substitution : C.Sub source target) (term : C.Tm target (operations.omega target)) :
    Value.substitute (⟨operations.omega target, term⟩ : Value C target) substitution =
      ⟨operations.omega source, substitute operations substitution term⟩ :=
  Sigma.ext (operations.omega_substitution substitution) (substitute_heq operations substitution term).symm

theorem quote_value_substitute (substitution : C.Sub source target) (predicate : doctrine.Predicate target) :
    Value.substitute (⟨operations.omega target, operations.quote predicate⟩ : Value C target) substitution =
      ⟨operations.omega source, operations.quote (doctrine.reindex substitution predicate)⟩ :=
  Sigma.ext (operations.omega_substitution substitution) (operations.quote_substitution substitution predicate)

theorem holds_substitute (substitution : C.Sub source target) (term : C.Tm target (operations.omega target)) :
    operations.holds (substitute operations substitution term) =
      doctrine.reindex substitution (operations.holds term) :=
  operations.holds_substitution substitution term _ (substitute_heq operations substitution term).symm

end PropositionOperations

namespace RefinementOperations

variable (operations : ContextualPredicateCapabilities.RefinementOperations doctrine)

/-- The actual self-extension square earns the substituted guard. -/
theorem substituted_guard (substitution : C.Sub source target) (type : C.Ty target)
    (predicate : doctrine.Predicate (C.ext target type)) (term : C.Tm target type)
    (guard : doctrine.reindex (selfExtend C term) predicate = ⊤) :
    doctrine.reindex (selfExtend C (C.tmSub term substitution))
      (doctrine.reindex (TypeOver.extensionSubstitution substitution type) predicate) = ⊤ := by
  rw [← doctrine.reindex_comp, selfExtend_substitution substitution term, doctrine.reindex_comp, guard]
  exact map_top (doctrine.reindex substitution)

def substitute (substitution : C.Sub source target) (type : C.Ty target)
    (predicate : doctrine.Predicate (C.ext target type)) (term : C.Tm target (operations.refined type predicate)) :
    C.Tm source (operations.refined (C.tySub type substitution)
      (doctrine.reindex (TypeOver.extensionSubstitution substitution type) predicate)) :=
  cast (congrArg (C.Tm source) (operations.formation_substitution substitution type predicate))
    (C.tmSub term substitution)

theorem substitute_heq (substitution : C.Sub source target) (type : C.Ty target)
    (predicate : doctrine.Predicate (C.ext target type)) (term : C.Tm target (operations.refined type predicate)) :
    HEq (substitute operations substitution type predicate term) (C.tmSub term substitution) := cast_heq _ _

theorem value_substitute (substitution : C.Sub source target) (type : C.Ty target)
    (predicate : doctrine.Predicate (C.ext target type)) (term : C.Tm target (operations.refined type predicate)) :
    Value.substitute (⟨operations.refined type predicate, term⟩ : Value C target) substitution =
      ⟨operations.refined (C.tySub type substitution)
        (doctrine.reindex (TypeOver.extensionSubstitution substitution type) predicate),
          substitute operations substitution type predicate term⟩ :=
  Sigma.ext (operations.formation_substitution substitution type predicate)
    (substitute_heq operations substitution type predicate term).symm

theorem introduction_value_substitute (substitution : C.Sub source target) (type : C.Ty target)
    (predicate : doctrine.Predicate (C.ext target type)) (term : C.Tm target type)
    (guard : doctrine.reindex (selfExtend C term) predicate = ⊤) :
    Value.substitute (⟨operations.refined type predicate, operations.intro type predicate term guard⟩ :
      Value C target) substitution =
      ⟨operations.refined (C.tySub type substitution)
          (doctrine.reindex (TypeOver.extensionSubstitution substitution type) predicate),
        operations.intro (C.tySub type substitution)
          (doctrine.reindex (TypeOver.extensionSubstitution substitution type) predicate)
            (C.tmSub term substitution) (substituted_guard substitution type predicate term guard)⟩ :=
  Sigma.ext (operations.formation_substitution substitution type predicate)
    (operations.intro_substitution substitution type predicate term guard _)

theorem forgetting_value_substitute (substitution : C.Sub source target) (type : C.Ty target)
    (predicate : doctrine.Predicate (C.ext target type)) (term : C.Tm target (operations.refined type predicate)) :
    Value.substitute (⟨type, operations.forget type predicate term⟩ : Value C target) substitution =
      ⟨C.tySub type substitution,
        operations.forget (C.tySub type substitution)
          (doctrine.reindex (TypeOver.extensionSubstitution substitution type) predicate)
            (substitute operations substitution type predicate term)⟩ :=
  Sigma.ext rfl (operations.forget_substitution substitution type predicate term _
    (substitute_heq operations substitution type predicate term).symm)

theorem forget_injective {context : C.Ctx} (type : C.Ty context)
    (predicate : doctrine.Predicate (C.ext context type)) :
    Function.Injective (operations.forget type predicate) := by
  intro first second same
  calc
    first = operations.intro type predicate (operations.forget type predicate first)
        (operations.forget_guard type predicate first) := (operations.eta type predicate first).symm
    _ = operations.intro type predicate (operations.forget type predicate second)
        (operations.forget_guard type predicate second) := by
      have guardedSame : (⟨operations.forget type predicate first,
          operations.forget_guard type predicate first⟩ :
          {value : C.Tm context type // doctrine.reindex (selfExtend C value) predicate = ⊤}) =
        ⟨operations.forget type predicate second, operations.forget_guard type predicate second⟩ :=
        Subtype.ext same
      exact congrArg (fun guarded : {value : C.Tm context type //
        doctrine.reindex (selfExtend C value) predicate = ⊤} =>
          operations.intro type predicate guarded.val guarded.property) guardedSame
    _ = second := operations.eta type predicate second

end RefinementOperations

end Mettapedia.TypeTheory.ContextualPredicateValueSubstitution
