import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPairContextInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementCongruenceSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractComputationSoundness

/-!
# Computational equations of the independent dependent presentation

Product and sum beta/eta are interpreted using the supplied local operation
equations. Full pair-elimination equations use the actual packing/opening
arrows, whose agreement follows from authored substitution and the earned
model component readouts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open NativeLocalTypeFormers
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualPiEta
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u v

variable {S : Symbols.{v}} {C : Type u} [Category.{u} C]

namespace ModelData

attribute [local irreducible] products sums TypeOver.extensionSubstitution
  ContextualSumComprehension.normalize ContextualSumComprehension.reindexBody

variable (model : ModelData S C) {n : Nat}

theorem piBeta_sound (stable : StrictPiSubstitution model.products) (beta : PiBeta model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (term : TermExpr S (n + 1)) (argument : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (termInterpreted : Interprets model (.term (.snoc context domain) term body))
    (argumentInterpreted : Interprets model (.term context argument domain)) :
    Interprets model (.termEq context (.app domain body (.lam domain body term) argument)
      (term.substitute (instantiate argument)) (body.substitute (instantiate argument))) :=
  model.interprets_of_abstract
    (Abstract.ModelData.piBeta_sound model.toAbstract (model.stable_toAbstract stable)
      (model.beta_toAbstract beta) context domain body term argument domainInterpreted.toAbstract
      bodyInterpreted.toAbstract termInterpreted.toAbstract argumentInterpreted.toAbstract)

theorem piEta_sound (stable : StrictPiSubstitution model.products)
    (eta : PiEta model.products stable.1)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (function : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (functionInterpreted : Interprets model (.term context function (.pi domain body))) :
    Interprets model (.termEq context (.lam domain body (.app (domain.rename Fin.succ)
      (body.rename (liftRenaming Fin.succ)) (function.rename Fin.succ) (.var 0))) function (.pi domain body)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.piEta_sound model.toAbstract (model.stable_toAbstract stable)
      (model.eta_toAbstract stable eta) context domain body function domainInterpreted.toAbstract
      bodyInterpreted.toAbstract functionInterpreted.toAbstract)

theorem sigmaFirstBeta_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (first second : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (firstInterpreted : Interprets model (.term context first domain))
    (secondInterpreted : Interprets model (.term context second (body.substitute (instantiate first)))) :
    Interprets model (.termEq context (.fst domain body (.pair domain body first second)) first domain) :=
  model.interprets_of_abstract
    (Abstract.ModelData.sigmaFirstBeta_sound model.toAbstract (model.stable_toAbstract stable) context
      domain body first second domainInterpreted.toAbstract bodyInterpreted.toAbstract
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem sigmaSecondBeta_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (first second : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (firstInterpreted : Interprets model (.term context first domain))
    (secondInterpreted : Interprets model (.term context second (body.substitute (instantiate first)))) :
    Interprets model (.termEq context (.snd domain body (.pair domain body first second)) second
      (body.substitute (instantiate first))) :=
  model.interprets_of_abstract
    (Abstract.ModelData.sigmaSecondBeta_sound model.toAbstract (model.stable_toAbstract stable) context
      domain body first second domainInterpreted.toAbstract bodyInterpreted.toAbstract
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem sigmaEta_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (body : TypeExpr S (n + 1)) (pair : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (pairInterpreted : Interprets model (.term context pair (.sigma domain body))) :
    Interprets model (.termEq context (.pair domain body (.fst domain body pair) (.snd domain body pair))
      pair (.sigma domain body)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.sigmaEta_sound model.toAbstract context domain body pair
      domainInterpreted.toAbstract bodyInterpreted.toAbstract pairInterpreted.toAbstract)

set_option backward.isDefEq.respectTransparency false in
theorem pack_openComponents (stable : StrictPiSubstitution model.products)
    (Γ : Scope C n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (A : (NativeModel C).toCwf.Ty Γ.1) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ.1 A))
    (first second : TermExpr S n) (a : (NativeModel C).toCwf.Tm Γ.1 A)
    (b : (NativeModel C).toCwf.Tm Γ.1 ((NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf a)))
    (domainRead : model.evaluateType Γ domain = some A)
    (bodyRead : model.evaluateType (Γ.snoc A) body = some B)
    (firstRead : model.evaluateTerm Γ first = some ⟨A, a⟩)
    (secondRead : model.evaluateTerm Γ second = some ⟨_, b⟩) :
    (NativeModel C).toCwf.compS (pack model.sums A B) ((NativeModel C).toCwf.pair (selfExtend (NativeModel C).toCwf a) B b) =
      selfExtend (NativeModel C).toCwf (model.sums.operations.pair a b) := by
  let packMap := ModelSubstitution.packPair stable Γ domain body A B domainRead bodyRead
  let componentsMap := ModelSubstitution.openComponents Γ A B first second a b firstRead secondRead
  let combined := packMap.compose stable componentsMap
  let supplied := ModelSubstitution.openBinder Γ (model.sums.operations.sigma A B)
    (.pair domain body first second) (model.sums.operations.pair a b)
    (model.evaluate_pair Γ domain body A B domainRead bodyRead first second a b firstRead secondRead)
  have composedRead := combined.evaluate
  change model.evaluateSubstitution Γ (Γ.snoc (model.sums.operations.sigma A B))
    (composeSubstitution (packSubstitution domain body) (instantiateComponents first second)) =
      some ((NativeModel C).toCwf.compS (pack model.sums A B)
        ((NativeModel C).toCwf.pair (selfExtend (NativeModel C).toCwf a) B b)) at composedRead
  rw [packSubstitution_instantiate] at composedRead
  exact Option.some.inj (composedRead.symm.trans supplied.evaluate)

theorem sigmaEliminationBeta_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body motive : TypeExpr S (n + 1))
    (branch : TermExpr S (n + 2)) (first second : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (motiveInterpreted : Interprets model (.type (.snoc context (.sigma domain body)) motive))
    (branchInterpreted : Interprets model (.term (.snoc (.snoc context domain) body) branch
      (motive.substitute (packSubstitution domain body))))
    (firstInterpreted : Interprets model (.term context first domain))
    (secondInterpreted : Interprets model (.term context second (body.substitute (instantiate first)))) :
    Interprets model (.termEq context (.sigmaElim domain body motive branch (.pair domain body first second))
      (branch.substitute (instantiateComponents first second))
        (motive.substitute (instantiate (.pair domain body first second)))) :=
  model.interprets_of_abstract
    (Abstract.ModelData.sigmaEliminationBeta_sound model.toAbstract (model.stable_toAbstract stable)
      context domain body motive branch first second domainInterpreted.toAbstract
      bodyInterpreted.toAbstract motiveInterpreted.toAbstract branchInterpreted.toAbstract
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem sigmaEliminationEta_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body motive : TypeExpr S (n + 1))
    (term : TermExpr S (n + 1)) (pair : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (motiveInterpreted : Interprets model (.type (.snoc context (.sigma domain body)) motive))
    (termInterpreted : Interprets model (.term (.snoc context (.sigma domain body)) term motive))
    (pairInterpreted : Interprets model (.term context pair (.sigma domain body))) :
    Interprets model (.termEq context (.sigmaElim domain body motive
      (term.substitute (packSubstitution domain body)) pair)
        (term.substitute (instantiate pair)) (motive.substitute (instantiate pair))) :=
  model.interprets_of_abstract
    (Abstract.ModelData.sigmaEliminationEta_sound model.toAbstract (model.stable_toAbstract stable)
      context domain body motive term pair domainInterpreted.toAbstract bodyInterpreted.toAbstract
      motiveInterpreted.toAbstract termInterpreted.toAbstract pairInterpreted.toAbstract)

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
