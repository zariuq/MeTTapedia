import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualConstructorReadout
import Mettapedia.TypeTheory.ContextualLogicalMorphism
import Mettapedia.TypeTheory.ContextualCwfUniverseTypeLift

/-!
# Logical constructor preservation by contextual interpretation

The constructor evaluations determine the interpreted product and sum
classes and their complete sections. The selected source annotations are
retyped through the earned contextual extension comparison. The resulting
capabilities concern the actual constructed contextual morphism.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualLogicalMorphism
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open QuotientComprehensionSyntax DependentTypes
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

universe u c s t m p z
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c, s, t, m}}
variable (model : QualifiedModel.{u,c,s,t,m,p} D C)

set_option backward.isDefEq.respectTransparency false in
theorem section_value {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (argument : QuotientCwf.Tm context domain)
    (a : C.toCwf.Tm (contextValue model context.as).1 (typeValue model domain))
    (arguments : HEq (termValue model argument) a) :
    HEq ((quotientFunctor model).map (selfExtend (QuotientCwf.cwf D) argument))
      (selfExtend C.toCwf a) := by
  let sourceArgument : (SourceModel.{u, max c s t m} D).toCwf.Tm
      (ULift.up context) (ULift.up domain) := ULift.up argument
  let targetArgument : (TargetModel.{u, c, s, t, m} C).toCwf.Tm
      (ULift.up (contextValue model context.as).1) (ULift.up (typeValue model domain)) := ULift.up a
  have square := ContextualComprehensionMorphism.self_extension_heq (strictMorphism model)
    rfl HEq.rfl sourceArgument targetArgument (up_heq arguments)
  have endpoint := congrArg Sigma.fst (represented_extension model domain)
  have carrier := congrArg (C.toCwf.Sub (contextValue model context.as).1) endpoint
  have read := down_heq carrier square
  change HEq ((quotientFunctor model).map
      ((selfExtend (SourceModel.{u, max c s t m} D).toCwf sourceArgument).down))
    ((selfExtend (TargetModel.{u, c, s, t, m} C).toCwf targetArgument).down) at read
  have sourceRead : (selfExtend (SourceModel.{u, max c s t m} D).toCwf sourceArgument).down =
      selfExtend (QuotientCwf.cwf D) argument :=
    selfExtend_readout (C := QuotientCwf.cwf D) sourceArgument
  have targetRead : (selfExtend (TargetModel.{u, c, s, t, m} C).toCwf targetArgument).down =
      selfExtend C.toCwf a := selfExtend_readout (C := C.toCwf) targetArgument
  rw [sourceRead, targetRead] at read
  exact read

theorem instantiation_type_value {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} (body : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (argument : QuotientCwf.Tm context domain)
    (B : C.toCwf.Ty (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (bodies : HEq (typeValue model body) B)
    (a : C.toCwf.Tm (contextValue model context.as).1 (typeValue model domain))
    (arguments : HEq (termValue model argument) a) :
    typeValue model (QuotientCwf.tySub body (selfExtend (QuotientCwf.cwf D) argument)) =
      C.toCwf.tySub B (selfExtend C.toCwf a) := by
  exact (type_substitution model body (selfExtend (QuotientCwf.cwf D) argument)).trans
    (eq_of_heq (ContextualComprehensionMorphism.tySub_heq rfl
      (congrArg Sigma.fst (represented_extension model domain)) bodies
      (section_value model argument a arguments)))

theorem product_type_value {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (body : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (B : C.toCwf.Ty (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (bodies : HEq (typeValue model body) B) :
    typeValue model (Products.pi domain body) = model.localModel.products.pi (typeValue model domain) B := by
  let domainCode := (QuotientCwf.typeRepresentative domain).code
  let bodyCode := (QuotientCwf.typeRepresentative body).code
  have computed := model.data.evaluate_pi (contextValue model context.as) domainCode bodyCode
    (typeValue model domain) B (represented_type_readout model domain)
    (represented_body_readout model domain body B bodies)
  exact Option.some.inj ((type_readout model
    (rawPi (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative body))).symm.trans computed)

theorem product_abstraction_value {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} {body : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (term : QuotientCwf.Tm (QuotientCwf.ext context domain) body)
    (B : C.toCwf.Ty (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (bodies : HEq (typeValue model body) B)
    (value : C.toCwf.Tm (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)) B)
    (terms : HEq (termValue model term) value) :
    HEq (termValue model (Products.lam term)) (model.localModel.products.lam value) := by
  have computed := model.data.evaluate_lambda (contextValue model context.as)
    (QuotientCwf.typeRepresentative domain).code (QuotientCwf.typeRepresentative body).code
    (typeValue model domain) B (represented_type_readout model domain)
    (represented_body_readout model domain body B bodies) (chosenTerm term).code value
    (represented_body_term_readout model domain term B bodies value terms)
  have actual := represented_term_readout model (Products.lam term) (Products.rawLam (chosenTerm term)) rfl
  exact (Sigma.mk.inj (Option.some.inj (actual.symm.trans computed))).2

theorem product_application_value {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} {body : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (function : QuotientCwf.Tm context (Products.pi domain body))
    (argument : QuotientCwf.Tm context domain)
    (B : C.toCwf.Ty (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (bodies : HEq (typeValue model body) B)
    (f : C.toCwf.Tm (contextValue model context.as).1 (model.localModel.products.pi (typeValue model domain) B))
    (a : C.toCwf.Tm (contextValue model context.as).1 (typeValue model domain))
    (functions : HEq (termValue model function) f) (arguments : HEq (termValue model argument) a) :
    HEq (termValue model (Products.app function argument)) (model.localModel.products.app f a) := by
  have functionRead := native_term_readout_transport model rfl (Products.functionRepresentative function).code
    (heq_of_eq (product_type_value model domain body B bodies)) functions
    (represented_term_readout model function (Products.functionRepresentative function)
      (Products.functionRepresentative_class function))
  have argumentRead := native_term_readout_transport model rfl (chosenTerm argument).code HEq.rfl arguments
    (chosen_term_readout model argument)
  have computed := model.data.evaluate_application (contextValue model context.as)
    (QuotientCwf.typeRepresentative domain).code (QuotientCwf.typeRepresentative body).code
    (typeValue model domain) B (represented_type_readout model domain)
    (represented_body_readout model domain body B bodies)
    (Products.functionRepresentative function).code (chosenTerm argument).code f a functionRead argumentRead
  have actual := represented_term_readout model (Products.app function argument)
    (Products.rawApp (Products.functionRepresentative function) (chosenTerm argument)) rfl
  exact (Sigma.mk.inj (Option.some.inj (actual.symm.trans computed))).2

theorem sum_type_value {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (body : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (B : C.toCwf.Ty (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (bodies : HEq (typeValue model body) B) :
    typeValue model (Sums.sigma domain body) = model.localModel.sums.operations.sigma (typeValue model domain) B := by
  have computed := model.data.evaluate_sigma (contextValue model context.as)
    (QuotientCwf.typeRepresentative domain).code (QuotientCwf.typeRepresentative body).code
    (typeValue model domain) B (represented_type_readout model domain)
    (represented_body_readout model domain body B bodies)
  exact Option.some.inj ((type_readout model
    (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative body))).symm.trans computed)

theorem sum_pair_value {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} {body : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm context domain)
    (second : QuotientCwf.Tm context
      (QuotientCwf.tySub body (selfExtend (QuotientCwf.cwf D) first)))
    (B : C.toCwf.Ty (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (bodies : HEq (typeValue model body) B)
    (a : C.toCwf.Tm (contextValue model context.as).1 (typeValue model domain))
    (b : C.toCwf.Tm (contextValue model context.as).1 (C.toCwf.tySub B (selfExtend C.toCwf a)))
    (firsts : HEq (termValue model first) a) (seconds : HEq (termValue model second) b) :
    HEq (termValue model (Sums.pair first second)) (model.localModel.sums.operations.pair a b) := by
  have firstRead := native_term_readout_transport model rfl (chosenTerm first).code HEq.rfl firsts
    (chosen_term_readout model first)
  have secondRead := native_term_readout_transport model rfl (Sums.componentRepresentative first second).code
    (heq_of_eq (instantiation_type_value model body first B bodies a firsts)) seconds
    (represented_term_readout model second (Sums.componentRepresentative first second)
      (Sums.componentRepresentative_class first second))
  have computed := model.data.evaluate_pair (contextValue model context.as)
    (QuotientCwf.typeRepresentative domain).code (QuotientCwf.typeRepresentative body).code
    (typeValue model domain) B (represented_type_readout model domain)
    (represented_body_readout model domain body B bodies)
    (chosenTerm first).code (Sums.componentRepresentative first second).code a b firstRead secondRead
  have actual := represented_term_readout model (Sums.pair first second)
    (Sums.rawPair (chosenTerm first) (Sums.componentRepresentative first second)) rfl
  exact (Sigma.mk.inj (Option.some.inj (actual.symm.trans computed))).2

theorem sum_first_value {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} {body : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (pair : QuotientCwf.Tm context (Sums.sigma domain body))
    (B : C.toCwf.Ty (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (bodies : HEq (typeValue model body) B)
    (p : C.toCwf.Tm (contextValue model context.as).1 (model.localModel.sums.operations.sigma (typeValue model domain) B))
    (pairs : HEq (termValue model pair) p) :
    HEq (termValue model (Sums.fst pair)) (model.localModel.sums.operations.fst p) := by
  have pairRead := native_term_readout_transport model rfl (Sums.pairRepresentative pair).code
    (heq_of_eq (sum_type_value model domain body B bodies)) pairs
    (represented_term_readout model pair (Sums.pairRepresentative pair) (Sums.pairRepresentative_class pair))
  have computed := model.data.evaluate_first (contextValue model context.as)
    (QuotientCwf.typeRepresentative domain).code (QuotientCwf.typeRepresentative body).code
    (typeValue model domain) B (represented_type_readout model domain)
    (represented_body_readout model domain body B bodies) (Sums.pairRepresentative pair).code p pairRead
  have actual := represented_term_readout model (Sums.fst pair) (Sums.rawFst (Sums.pairRepresentative pair)) rfl
  exact (Sigma.mk.inj (Option.some.inj (actual.symm.trans computed))).2

theorem sum_second_value {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} {body : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (pair : QuotientCwf.Tm context (Sums.sigma domain body))
    (B : C.toCwf.Ty (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (bodies : HEq (typeValue model body) B)
    (p : C.toCwf.Tm (contextValue model context.as).1 (model.localModel.sums.operations.sigma (typeValue model domain) B))
    (pairs : HEq (termValue model pair) p) :
    HEq (termValue model (Sums.snd pair)) (model.localModel.sums.operations.snd p) := by
  have pairRead := native_term_readout_transport model rfl (Sums.pairRepresentative pair).code
    (heq_of_eq (sum_type_value model domain body B bodies)) pairs
    (represented_term_readout model pair (Sums.pairRepresentative pair) (Sums.pairRepresentative_class pair))
  have computed := model.data.evaluate_second (contextValue model context.as)
    (QuotientCwf.typeRepresentative domain).code (QuotientCwf.typeRepresentative body).code
    (typeValue model domain) B (represented_type_readout model domain)
    (represented_body_readout model domain body B bodies) (Sums.pairRepresentative pair).code p pairRead
  have actual := represented_term_readout model (Sums.snd pair) (Sums.rawSnd (Sums.pairRepresentative pair)) rfl
  exact (Sigma.mk.inj (Option.some.inj (actual.symm.trans computed))).2

theorem native_term_carrier {first second : C.toCwf.Ctx} (contexts : first = second)
    {A : C.toCwf.Ty first} {B : C.toCwf.Ty second} (types : HEq A B) :
    C.toCwf.Tm first A = C.toCwf.Tm second B := by
  cases contexts
  cases eq_of_heq types
  rfl

theorem termValue_heq {context : QuotientCwf.QContext D}
    {A B : QuotientCwf.Ty context} (types : A = B)
    {first : QuotientCwf.Tm context A} {second : QuotientCwf.Tm context B}
    (terms : HEq first second) : HEq (termValue model first) (termValue model second) := by
  cases types
  cases eq_of_heq terms
  rfl

noncomputable def sourceProducts (D : Signature S) :
    PiOperations (SourceModel.{u, z} D).toCwf :=
  liftProducts (Products.operations D)

noncomputable def sourceSums (D : Signature S) :
    SigmaOperations (SourceModel.{u, z} D).toCwf :=
  liftSums (Sums.operations D)

noncomputable def targetProducts : PiOperations (TargetModel.{u, c, s, t, m} C).toCwf :=
  liftProducts model.localModel.products

noncomputable def targetSums : SigmaOperations (TargetModel.{u, c, s, t, m} C).toCwf :=
  liftSums model.localModel.sums.operations

set_option backward.isDefEq.respectTransparency false in
theorem products_preserved :
    PiPreservation (strictMorphism model) (sourceProducts.{u, max c s t m} D) (targetProducts model) := by
  constructor
  · intro Γ Γ' contexts A A' domains B B' codomains
    cases contexts
    cases eq_of_heq domains
    have bodyTypes := down_heq
      (congrArg C.toCwf.Ty (congrArg Sigma.fst (represented_extension model A.down))) codomains
    exact up_heq (heq_of_eq (product_type_value model A.down B.down B'.down bodyTypes))
  · intro Γ Γ' contexts A A' domains B B' codomains body body' bodies
    cases contexts
    cases eq_of_heq domains
    have endpoints := congrArg Sigma.fst (represented_extension model A.down)
    have bodyTypes := down_heq (congrArg C.toCwf.Ty endpoints) codomains
    have bodyTerms := down_heq (native_term_carrier endpoints bodyTypes) bodies
    exact up_heq (product_abstraction_value model body.down B'.down bodyTypes body'.down bodyTerms)
  · intro Γ Γ' contexts A A' domains B B' codomains function function' argument argument' functions arguments
    cases contexts
    cases eq_of_heq domains
    have bodyTypes := down_heq
      (congrArg C.toCwf.Ty (congrArg Sigma.fst (represented_extension model A.down))) codomains
    have formation := product_type_value model A.down B.down B'.down bodyTypes
    have nativeFunctions := down_heq (congrArg (C.toCwf.Tm (contextValue model Γ.down.as).1) formation) functions
    have nativeArguments := down_heq rfl arguments
    have sourceTypes := congrArg (QuotientCwf.tySub B.down)
      (selfExtend_readout (C := QuotientCwf.cwf D) argument)
    have sourceRead := termValue_heq model sourceTypes
      (products_app_readout (Products.operations D) function argument)
    have computed := product_application_value model function.down argument.down B'.down bodyTypes
      function'.down argument'.down nativeFunctions nativeArguments
    exact (up_heq (sourceRead.trans computed)).trans
      (up_heq (products_app_readout model.localModel.products function' argument')).symm

set_option backward.isDefEq.respectTransparency false in
theorem sums_preserved :
    SigmaPreservation (strictMorphism model) (sourceSums.{u, max c s t m} D) (targetSums model) := by
  constructor
  · intro Γ Γ' contexts A A' domains B B' codomains
    cases contexts
    cases eq_of_heq domains
    have bodyTypes := down_heq
      (congrArg C.toCwf.Ty (congrArg Sigma.fst (represented_extension model A.down))) codomains
    exact up_heq (heq_of_eq (sum_type_value model A.down B.down B'.down bodyTypes))
  · intro Γ Γ' contexts A A' domains B B' codomains first first' second second' firsts seconds
    cases contexts
    cases eq_of_heq domains
    have bodyTypes := down_heq
      (congrArg C.toCwf.Ty (congrArg Sigma.fst (represented_extension model A.down))) codomains
    have nativeFirsts := down_heq rfl firsts
    have sourceTypes := congrArg (QuotientCwf.tySub B.down)
      (selfExtend_readout (C := QuotientCwf.cwf D) first)
    have targetTypes := congrArg (C.toCwf.tySub B'.down)
      (selfExtend_readout (C := C.toCwf) first')
    let nativeSecond := cast (congrArg (QuotientCwf.Tm Γ.down) sourceTypes) second.down
    let nativeSecond' := cast (congrArg (C.toCwf.Tm (contextValue model Γ.down.as).1) targetTypes) second'.down
    have semanticTypes := (congrArg (typeValue model) sourceTypes).trans
      ((instantiation_type_value model B.down first.down B'.down bodyTypes first'.down nativeFirsts).trans
        targetTypes.symm)
    have originalSeconds := down_heq
      (congrArg (C.toCwf.Tm (contextValue model Γ.down.as).1) semanticTypes) seconds
    have nativeSeconds : HEq (termValue model nativeSecond) nativeSecond' :=
      (termValue_heq model sourceTypes.symm (cast_heq _ second.down)).trans
        (originalSeconds.trans (cast_heq _ second'.down).symm)
    have computed := sum_pair_value model first.down nativeSecond B'.down bodyTypes
      first'.down nativeSecond' nativeFirsts nativeSeconds
    exact up_heq computed
  · intro Γ Γ' contexts A A' domains B B' codomains pair pair' pairs
    cases contexts
    cases eq_of_heq domains
    have bodyTypes := down_heq
      (congrArg C.toCwf.Ty (congrArg Sigma.fst (represented_extension model A.down))) codomains
    have formation := sum_type_value model A.down B.down B'.down bodyTypes
    have nativePairs := down_heq
      (congrArg (C.toCwf.Tm (contextValue model Γ.down.as).1) formation) pairs
    exact up_heq (sum_first_value model pair.down B'.down bodyTypes pair'.down nativePairs)
  · intro Γ Γ' contexts A A' domains B B' codomains pair pair' pairs
    cases contexts
    cases eq_of_heq domains
    have bodyTypes := down_heq
      (congrArg C.toCwf.Ty (congrArg Sigma.fst (represented_extension model A.down))) codomains
    have formation := sum_type_value model A.down B.down B'.down bodyTypes
    have nativePairs := down_heq
      (congrArg (C.toCwf.Tm (contextValue model Γ.down.as).1) formation) pairs
    have sourceTypes := congrArg (QuotientCwf.tySub B.down)
      (selfExtend_readout (C := QuotientCwf.cwf D)
        (ULift.up (Sums.fst pair.down) : (SourceModel.{u, max c s t m} D).toCwf.Tm Γ A))
    have sourceRead : HEq ((sourceSums.{u, max c s t m} D).snd pair).down (Sums.snd pair.down) := by
      unfold sourceSums liftSums
      dsimp
      exact cast_heq _ _
    have targetRead : HEq ((targetSums model).snd pair').down (model.localModel.sums.operations.snd pair'.down) := by
      unfold targetSums liftSums
      dsimp
      exact cast_heq _ _
    have computed := sum_second_value model pair.down B'.down bodyTypes pair'.down nativePairs
    exact (up_heq ((termValue_heq model sourceTypes sourceRead).trans computed)).trans
      (up_heq targetRead).symm

theorem logical_preservation :
    LogicalPreservation (strictMorphism model)
      (sourceProducts.{u, max c s t m} D) (targetProducts model)
      (sourceSums.{u, max c s t m} D) (targetSums model) :=
  ⟨products_preserved model, sums_preserved model⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation
