import Mathlib.CategoryTheory.Discrete.Basic
import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# Semantic invariants of graph-structured lambda theories

A GSLT supplies operational syntax: terms, equations, and directed rewrites.
It does not by itself say what a term denotes in an independently chosen
mathematical domain.  A `SemanticInvariant` supplies such a denotation when
both equations and rewrites preserve it.

This is the common structure behind representation-changing machines.  An
edge-list-to-matrix rewrite may change layout while retaining one finite
graph; a query machine may change control state while retaining one observed
answer.  The invariant is deliberately optional: evaluators whose rewrites
change the selected semantic value simply do not inhabit this interface for
that value.

Every invariant:

* gives a total instance of the existing partial `GSLT.Elaboration` boundary;
* is conserved by finite proof-relevant rewrite paths and `MultiStep` proofs;
* decomposes the GSLT into closed semantic fibres; and
* induces a functor from the free execution-path category to the discrete
  category of semantic values.

The last point makes the semantic organization precise.  GSLT paths live over
one semantic value whenever the chosen observation is invariant; operational
history is retained in the source category rather than collapsed into the
discrete target.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

open CategoryTheory
open Mettapedia.GSLT.IndexedOperational

universe uTerm uSemantic uSemantic'

/-- An independently selected semantic observation conserved by both static
equations and directed computation. -/
structure SemanticInvariant (system : GSLT.{uTerm})
    (Semantic : Type uSemantic) where
  denote : system.Term → Semantic
  equation : ∀ {left right}, system.Equiv left right →
    denote left = denote right
  rewrite : ∀ {source target}, system.Step source target →
    denote source = denote target

namespace SemanticInvariant

variable {system : GSLT.{uTerm}} {Semantic : Type uSemantic}
  {Semantic' : Type uSemantic'}

/-- A total invariant is a non-failing elaboration.  This bridge reuses the
existing GSLT elaboration interface rather than introducing a second notion
of interpretation. -/
def toElaboration (invariant : SemanticInvariant system Semantic) :
    GSLT.Elaboration system Semantic where
  elaborate := fun term => some (invariant.denote term)
  equation := fun equivalent => congrArg some (invariant.equation equivalent)
  rewrite := fun step => congrArg some (invariant.rewrite step)

/-- Postcomposition changes the semantic vocabulary without changing which
operational distinctions are conserved. -/
def map (invariant : SemanticInvariant system Semantic)
    (translate : Semantic → Semantic') :
    SemanticInvariant system Semantic' where
  denote := translate ∘ invariant.denote
  equation := fun equivalent => congrArg translate (invariant.equation equivalent)
  rewrite := fun step => congrArg translate (invariant.rewrite step)

@[simp] theorem map_denote (invariant : SemanticInvariant system Semantic)
    (translate : Semantic → Semantic') (term : system.Term) :
    (invariant.map translate).denote term = translate (invariant.denote term) :=
  rfl

/-- Every finite, proof-relevant execution path stays at one selected
semantic value.  `ExecutionPath` is the universe-polymorphic free path
object used by the categorical operational layer. -/
theorem executionPath_eq (invariant : SemanticInvariant system Semantic)
    {source target : ExecutionObject system}
    (path : ExecutionPath system source target) :
    invariant.denote source = invariant.denote target :=
  Mettapedia.GSLT.Ultrainfinite.Route.observe_eq_of_route invariant.denote
    (fun step => invariant.rewrite step.down) path

/-- Compatibility with the original universe-zero `GSLT.RewritePath` API.
New generic developments should use `executionPath_eq`. -/
theorem rewritePath_eq {smallSystem : GSLT}
    (invariant : SemanticInvariant smallSystem Semantic) :
    {source target : smallSystem.Term} →
      smallSystem.RewritePath source target →
        invariant.denote source = invariant.denote target
  | _, _, .nil _ => rfl
  | _, _, .cons step rest =>
      (invariant.rewrite step).trans (invariant.rewritePath_eq rest)

/-- The proposition-valued reflexive-transitive closure conserves the same
semantic value. -/
theorem multiStep_eq (invariant : SemanticInvariant system Semantic) :
    {source target : system.Term} →
      system.MultiStep source target →
        invariant.denote source = invariant.denote target
  | _, _, .refl _ => rfl
  | _, _, .step step rest =>
      (invariant.rewrite step).trans (invariant.multiStep_eq rest)

/-! ## Closed semantic fibres -/

/-- Terms denoting one fixed semantic value. -/
abbrev FibreTerm (invariant : SemanticInvariant system Semantic)
    (meaning : Semantic) :=
  { term : system.Term // invariant.denote term = meaning }

/-- A semantic fibre is itself a GSLT.  Equations and rewrites are inherited,
and invariant preservation proves that generated targets remain in the same
fibre. -/
def fibre (invariant : SemanticInvariant system Semantic)
    (meaning : Semantic) : GSLT where
  Term := invariant.FibreTerm meaning
  equations :=
    { r := fun left right => system.Equiv left.1 right.1
      iseqv :=
        { refl := fun term => system.equations.iseqv.refl term.1
          symm := fun equivalent => system.equations.iseqv.symm equivalent
          trans := fun first second =>
            system.equations.iseqv.trans first second } }
  rewrites := fun source target => system.Step source.1 target.1
  rewrites_resp_left := by
    intro source source' target equivalent step
    obtain ⟨rawTarget, nextStep, targetEquivalent⟩ :=
      system.rewrites_resp_left equivalent step
    have rawTargetMeaning : invariant.denote rawTarget = meaning :=
      (invariant.rewrite nextStep).symm.trans source'.2
    exact
      ⟨⟨rawTarget, rawTargetMeaning⟩, nextStep, targetEquivalent⟩
  rewrites_resp_right := by
    intro source target target' step equivalent
    exact system.rewrites_resp_right step equivalent

/-- Forget one fibre term back to the ambient GSLT term. -/
def forgetFibreTerm (invariant : SemanticInvariant system Semantic)
    (meaning : Semantic) : (invariant.fibre meaning).Term → system.Term :=
  Subtype.val

/-- Forget a fibre execution path without losing its ordered step
occurrences. -/
def forgetFibrePath (invariant : SemanticInvariant system Semantic)
    (meaning : Semantic) :
    {source target : (invariant.fibre meaning).Term} →
      ExecutionPath (invariant.fibre meaning) source target →
        ExecutionPath system source.1 target.1
  | _, _, .refl term => .refl term.1
  | _, _, .cons step rest =>
      .cons ⟨step.down⟩ (invariant.forgetFibrePath meaning rest)

/-- Every ambient path whose source lies in a selected fibre ends in that
same fibre. -/
theorem target_in_fibre (invariant : SemanticInvariant system Semantic)
    {source target : system.Term} (meaning : Semantic)
    (sourceInFibre : invariant.denote source = meaning)
    (path : ExecutionPath system source target) :
    invariant.denote target = meaning :=
  (invariant.executionPath_eq path).symm.trans sourceInFibre

/-! ## Categorical form -/

/-- A semantic invariant sends the free execution-path category to the
discrete category of meanings.  All nontrivial operational history is mapped
to the unique equality arrow licensed by conservation. -/
def pathToDiscrete (invariant : SemanticInvariant system Semantic) :
    CategoryTheory.Functor (ExecutionObject system)
      (CategoryTheory.Discrete Semantic) where
  obj term := CategoryTheory.Discrete.mk (invariant.denote term)
  map path := CategoryTheory.Discrete.eqToHom'
    (invariant.executionPath_eq path)
  map_id _ := by rfl
  map_comp _ _ := by apply Subsingleton.elim

@[simp] theorem pathToDiscrete_obj
    (invariant : SemanticInvariant system Semantic)
    (term : ExecutionObject system) :
    (invariant.pathToDiscrete.obj term).as = invariant.denote term :=
  rfl

/-- Two endpoints connected by an execution path have literally equal
images in the discrete semantic category. -/
theorem pathToDiscrete_obj_eq
    (invariant : SemanticInvariant system Semantic)
    {source target : ExecutionObject system} (path : source ⟶ target) :
    invariant.pathToDiscrete.obj source =
      invariant.pathToDiscrete.obj target :=
  congrArg CategoryTheory.Discrete.mk (invariant.executionPath_eq path)

end SemanticInvariant

#print axioms SemanticInvariant.toElaboration
#print axioms SemanticInvariant.executionPath_eq
#print axioms SemanticInvariant.rewritePath_eq
#print axioms SemanticInvariant.multiStep_eq
#print axioms SemanticInvariant.fibre
#print axioms SemanticInvariant.forgetFibrePath
#print axioms SemanticInvariant.pathToDiscrete

end Mettapedia.GSLT
