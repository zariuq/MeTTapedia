import Mettapedia.Logic.HOL.OrderedPositionConversion
import Mettapedia.Logic.HOL.ConstructorPositionReadback
import Mettapedia.Logic.HOL.OrderedConstructorChildExistence

/-!
# Original child guards from converted position plans

The original field guard and a canonical lookup rebuild the source child
guard at the same slot and index. Count/label equations are actual retained
proofs, and no arithmetic law or uniqueness assumption is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
open FiniteConstructorEncoding CurriedPredicates OrderedPositionPrograms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (constructors : ConstructorPrograms Const Γ)
    (zero : ClosedTerm Const constructors.number) (successor : ClosedTerm Const (constructors.number ⇒ constructors.number))
    (plans : (occurrence : Fin constructors.fields.length) →
      FieldPlan Const Γ (constructors.fields.get occurrence) constructors.number constructors.index)
    {Δ : List (Formula Const Γ)}

def childFromCanonical (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number) (target : Term Const Γ constructors.index)
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const Δ (compileAt zero successor canonical Subst.id slot target)) :
    ProofSyntax Const Δ ((ofSegments constructors zero successor plans).childGuard
      (encode constructors.fields occurrence arguments) slot target) :=
  (ofSegments constructors zero successor plans).childFromOriginal occurrence arguments slot target allowed
    (.impE (.eqPropER (fieldGraph_beta zero successor _ (plans occurrence) slot target arguments))
      (.impE (.eqPropER (compileAt_planEquation zero successor equations slot target)) related))

theorem childFromCanonical_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number) (target : Term Const Γ constructors.index)
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const Δ (compileAt zero successor canonical Subst.id slot target))
    (equationsFree : equations.Free) (allowedFree : allowed.FunctionExtensionalityFree) (relatedFree : related.FunctionExtensionalityFree) :
    (childFromCanonical constructors zero successor plans occurrence arguments canonical equations slot target allowed related).FunctionExtensionalityFree :=
  (ofSegments constructors zero successor plans).childFromOriginal_free _ _ _ _ allowed _ allowedFree
    ⟨fieldGraph_beta_free _ _ _ _ _ _ _,⟨compileAt_planEquation_free _ _ equations slot target equationsFree,relatedFree⟩⟩

#print axioms childFromCanonical_free

def certifiedChildFromCanonical (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number) (target : Term Const Γ constructors.index)
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const Δ (compileAt zero successor canonical Subst.id slot target))
    (equationsFree : equations.Free) (allowedFree : allowed.FunctionExtensionalityFree) (relatedFree : related.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const Δ ((ofSegments constructors zero successor plans).childGuard
      (encode constructors.fields occurrence arguments) slot target) // proof.FunctionExtensionalityFree } :=
  ⟨childFromCanonical constructors zero successor plans occurrence arguments canonical equations slot target allowed related,
    childFromCanonical_free constructors zero successor plans occurrence arguments canonical equations slot target allowed related
      equationsFree allowedFree relatedFree⟩
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
