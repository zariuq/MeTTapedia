import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementJudgmentInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementConstructorInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSubstitutionEvaluation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementRenamingReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPairContextInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSoundnessFormation

/-!
# Native refinement formation and introduction readouts

Each rule constructs actual interpreted scopes, varying native types or full
supplied sections from its interpreted local premises. Proposition assumptions
select their satisfying context. These local theorems contain no whole-model
soundness or evaluator compatibility field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory NativeLocalTypeFormers PresheafNativePropositionReadout
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualSumComprehension

universe u v
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C] {D : Signature S}

namespace ModelData

variable (model : ModelData S C) {n k : Nat}

theorem contextNil_sound : Interprets model (.context (.nil : ContextExpr S 0)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.contextNil_sound model.toAbstract)

theorem contextExtend_sound (context : ContextExpr S n) (type : TypeExpr S n)
    (contextInterpreted : Interprets model (.context context))
    (typeInterpreted : Interprets model (.type context type)) :
    Interprets model (.context (.snoc context type)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.contextExtend_sound model.toAbstract context type contextInterpreted.toAbstract
      typeInterpreted.toAbstract)

theorem contextAssume_sound (context : ContextExpr S n) (predicate : PropExpr S n)
    (contextInterpreted : Interprets model (.context context))
    (predicateInterpreted : Interprets model (.predicate context predicate)) :
    Interprets model (.context (.assume context predicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.contextAssume_sound model.toAbstract context predicate
      contextInterpreted.toAbstract predicateInterpreted.toAbstract)

theorem propositionType_sound (context : ContextExpr S n)
    (contextInterpreted : Interprets model (.context context)) :
    Interprets model (.type context .propositions) :=
  model.interprets_of_abstract
    (Abstract.ModelData.propositionType_sound model.toAbstract context contextInterpreted.toAbstract)

theorem variable_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (index : Fin n)
    (contextInterpreted : Interprets model (.context context)) :
    Interprets model (.term context (.var index) (context.lookup index)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.variable_sound model.toAbstract (model.stable_toAbstract stable) context index
      contextInterpreted.toAbstract)

theorem family_sound (realization : SignatureRealization model D)
    (context : ContextExpr S n) (symbol : S.TypeSymbol)
    (arguments : Substitution S (S.typeArity symbol) n)
    (contextInterpreted : Interprets model (.context context))
    (argumentsInterpreted : Interprets model (.substitution context (D.typeParameters symbol) arguments)) :
    Interprets model (.type context (.family symbol arguments)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.family_sound model.toAbstract realization.toAbstract context symbol arguments
      contextInterpreted.toAbstract argumentsInterpreted.toAbstract)

theorem primitive_sound (stable : StrictPiSubstitution model.products)
    (realization : SignatureRealization model D)
    (context : ContextExpr S n) (symbol : S.TermSymbol)
    (arguments : Substitution S (S.termArity symbol) n)
    (argumentsInterpreted : Interprets model
      (.substitution context (D.termParameters symbol) arguments)) :
    Interprets model (.term context (.primitive symbol arguments)
      ((D.termResult symbol).substitute arguments)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.primitive_sound model.toAbstract (model.stable_toAbstract stable)
      realization.toAbstract context symbol arguments argumentsInterpreted.toAbstract)

theorem piFormation_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (body : TypeExpr S (n + 1)) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body)) :
    Interprets model (.type context (.pi domain body)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.piFormation_sound model.toAbstract context domain body
      domainInterpreted.toAbstract bodyInterpreted.toAbstract)

theorem sigmaFormation_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (body : TypeExpr S (n + 1)) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body)) :
    Interprets model (.type context (.sigma domain body)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.sigmaFormation_sound model.toAbstract context domain body
      domainInterpreted.toAbstract bodyInterpreted.toAbstract)

theorem lambda_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (body : TypeExpr S (n + 1)) (term : TermExpr S (n + 1))
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (termInterpreted : Interprets model (.term (.snoc context domain) term body)) :
    Interprets model (.term context (.lam domain body term) (.pi domain body)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.lambda_sound model.toAbstract context domain body term
      domainInterpreted.toAbstract bodyInterpreted.toAbstract termInterpreted.toAbstract)

theorem application_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (function argument : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (functionInterpreted : Interprets model (.term context function (.pi domain body)))
    (argumentInterpreted : Interprets model (.term context argument domain)) :
    Interprets model (.term context (.app domain body function argument)
      (body.substitute (instantiate argument))) :=
  model.interprets_of_abstract
    (Abstract.ModelData.application_sound model.toAbstract (model.stable_toAbstract stable) context domain
      body function argument domainInterpreted.toAbstract bodyInterpreted.toAbstract
      functionInterpreted.toAbstract argumentInterpreted.toAbstract)

theorem pairIntroduction_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (first second : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (firstInterpreted : Interprets model (.term context first domain))
    (secondInterpreted : Interprets model (.term context second (body.substitute (instantiate first)))) :
    Interprets model (.term context (.pair domain body first second) (.sigma domain body)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.pairIntroduction_sound model.toAbstract (model.stable_toAbstract stable) context
      domain body first second domainInterpreted.toAbstract bodyInterpreted.toAbstract
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem firstProjection_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (body : TypeExpr S (n + 1)) (pair : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (pairInterpreted : Interprets model (.term context pair (.sigma domain body))) :
    Interprets model (.term context (.fst domain body pair) domain) :=
  model.interprets_of_abstract
    (Abstract.ModelData.firstProjection_sound model.toAbstract context domain body pair
      domainInterpreted.toAbstract bodyInterpreted.toAbstract pairInterpreted.toAbstract)

theorem secondProjection_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (pair : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (pairInterpreted : Interprets model (.term context pair (.sigma domain body))) :
    Interprets model (.term context (.snd domain body pair)
      (body.substitute (instantiate (.fst domain body pair)))) :=
  model.interprets_of_abstract
    (Abstract.ModelData.secondProjection_sound model.toAbstract (model.stable_toAbstract stable) context
      domain body pair domainInterpreted.toAbstract bodyInterpreted.toAbstract pairInterpreted.toAbstract)

theorem sigmaElimination_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body motive : TypeExpr S (n + 1))
    (branch : TermExpr S (n + 2)) (pair : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (motiveInterpreted : Interprets model (.type (.snoc context (.sigma domain body)) motive))
    (branchInterpreted : Interprets model (.term (.snoc (.snoc context domain) body) branch
      (motive.substitute (packSubstitution domain body))))
    (pairInterpreted : Interprets model (.term context pair (.sigma domain body))) :
    Interprets model (.term context (.sigmaElim domain body motive branch pair)
      (motive.substitute (instantiate pair))) :=
  model.interprets_of_abstract
    (Abstract.ModelData.sigmaElimination_sound model.toAbstract (model.stable_toAbstract stable) context
      domain body motive branch pair domainInterpreted.toAbstract bodyInterpreted.toAbstract
      motiveInterpreted.toAbstract branchInterpreted.toAbstract pairInterpreted.toAbstract)

theorem comprehensionFormation_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1))
    (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate)) :
    Interprets model (.type context (.comprehension domain predicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.comprehensionFormation_sound model.toAbstract context domain predicate
      domainInterpreted.toAbstract predicateInterpreted.toAbstract)

theorem termConversion_sound (context : ContextExpr S n) (term : TermExpr S n)
    (first second : TypeExpr S n) (termInterpreted : Interprets model (.term context term first))
    (typesInterpreted : Interprets model (.typeEq context first second)) :
    Interprets model (.term context term second) :=
  model.interprets_of_abstract
    (Abstract.ModelData.termConversion_sound model.toAbstract context term first second
      termInterpreted.toAbstract typesInterpreted.toAbstract)

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
