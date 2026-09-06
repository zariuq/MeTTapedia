import Mettapedia.Languages.SUMO.Native.DomainGuardElaboration
import Std.Data.String.ToNat

/-!
# Semantic realization of a finite SUMO source signature

The source elaborator extracts a finite arity/domain signature.  The native
model separately supplies denoted operator profiles.  This module states the
commuting law between those two levels and the object-language `domain`,
`domainSubclass`, `instance`, and `subclass` relations.

Positions in source declarations are one-based.  Positions in the native
operator profile are zero-based.  For a variable-arity operator, the native
profile entry at its minimum arity repeats the final source domain.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native.SignatureSemantics

open Mettapedia.Languages.SUMO.Native
open Mettapedia.Languages.SUMO.Native.SourceElaboration

universe uModel

/-- The source-domain position governing one zero-based argument position in
a denoted operator profile. -/
def sourceDomainPosition
    (model : Model String String) (operator : model.Carrier)
    (position : Nat) : Nat :=
  if model.variableArity operator &&
      model.operatorArity operator <= position then
    model.operatorArity operator
  else position + 1

/-- Object-language obligations induced by the currently asserted `domain`
and `domainSubclass` facts about one denoted operator position. -/
def objectLanguageDomainRequirement
    (model : Model String String) (operator argument : model.Carrier)
    (position : Nat) (world : model.World) : Prop :=
  let sourcePosition := sourceDomainPosition model operator position
  (forall classValue : model.Carrier,
      model.applyRelation (model.symbol "domain")
          [operator, model.symbol (toString sourcePosition), classValue] world ->
        model.applyRelation (model.symbol "instance")
          [argument, classValue] world) /\
    (forall classValue : model.Carrier,
      model.applyRelation (model.symbol "domainSubclass")
          [operator, model.symbol (toString sourcePosition), classValue] world ->
        model.applyRelation (model.symbol "subclass")
          [argument, classValue] world)

/-- One denoted operator's domain profile agrees with the model's own
object-language domain doctrine. -/
def ProfileCoherentAt
    (model : Model String String) (operator : model.Carrier) : Prop :=
  forall (argument : model.Carrier) (position : Nat) (world : model.World),
    model.inOperatorDomainAt operator position argument world <->
      objectLanguageDomainRequirement model operator argument position world

/-- Every denoted operator has an object-language-coherent domain profile. -/
def ProfileCoherent (model : Model String String) : Prop :=
  forall operator : model.Carrier, ProfileCoherentAt model operator

/-- Truth of one finite source restriction for a denoted argument. -/
def restrictionHolds
    (model : Model String String) (argument : model.Carrier)
    (restriction : DomainRestriction) (world : model.World) : Prop :=
  let predicate := match restriction.kind with
    | .object => "instance"
    | .class => "subclass"
  model.applyRelation (model.symbol predicate)
    [argument, model.symbol restriction.className] world

/-- Conjunction of every nonredundant source restriction at a one-based
argument position. -/
def restrictionsHold
    (signature : SourceSignature) (model : Model String String)
    (operator : String) (position : Nat) (argument : model.Carrier)
    (world : model.World) : Prop :=
  forall restriction,
    restriction ∈ signature.argumentRestrictions operator position ->
      restrictionHolds model argument restriction world

/-- Pointwise finite-signature obligations for an exact tail. -/
def everyTailRestrictionHolds
    (signature : SourceSignature) (model : Model String String)
    (operator : String) : Nat -> List model.Carrier -> model.World -> Prop
  | _, [], _ => True
  | position, argument :: rest, world =>
      restrictionsHold signature model operator (position + 1) argument world /\
        everyTailRestrictionHolds signature model operator
          (position + 1) rest world

/-- Exact finite-signature meaning of a tail beginning at a zero-based
position. -/
def tailRestrictionsHold
    (signature : SourceSignature) (model : Model String String)
    (operator : String) (firstPosition : Nat)
    (arguments : List model.Carrier) (world : model.World) : Prop :=
  (if signature.isVariableArityOperator operator then
      signature.declaredArity operator - firstPosition <= arguments.length
    else
      firstPosition <= signature.declaredArity operator /\
        arguments.length = signature.declaredArity operator - firstPosition) /\
    everyTailRestrictionHolds signature model operator firstPosition
      arguments world

/-- Semantic adequacy for one operator in a finite source signature.  The
fields separately expose call arity, the variadic discipline, denoted domains,
and agreement with the model's object-language domain facts. -/
structure RealizesOperator
    (signature : SourceSignature) (model : Model String String)
    (operator : String) : Prop where
  profileCoherent : ProfileCoherentAt model (model.symbol operator)
  arity : model.operatorArity (model.symbol operator) =
    signature.declaredArity operator
  variableArity : model.variableArity (model.symbol operator) =
    signature.isVariableArityOperator operator
  domain : forall (position : Nat) (argument : model.Carrier)
      (world : model.World),
    model.inOperatorDomainAt (model.symbol operator) position argument world <->
      restrictionsHold signature model operator (position + 1) argument world

/-- A model realizes a finite source signature when every operator actually
named by that source has its own semantic adequacy certificate. -/
structure RealizesSourceSignature
    (signature : SourceSignature) (model : Model String String) : Prop where
  operator : forall operator : String,
    operator ∈ signature.declaredOperators ->
      RealizesOperator signature model operator

namespace RealizesOperator

variable {signature : SourceSignature} {model : Model String String}

/-- The pointwise model guard and the finite source restriction conjunction
are the same judgment. -/
theorem point_guard_iff_source_restrictions
    {operator : String}
    (realizes : RealizesOperator signature model operator)
    (position : Nat) (argument : model.Carrier)
    (world : model.World) :
    model.inOperatorDomainAt (model.symbol operator) position argument world <->
      restrictionsHold signature model operator (position + 1) argument world :=
  realizes.domain position argument world

/-- Finite source restrictions and the native object-language domain doctrine
commute through the denoted operator-domain judgment. -/
theorem source_restrictions_iff_object_language
    {operator : String}
    (realizes : RealizesOperator signature model operator)
    (position : Nat) (argument : model.Carrier)
    (world : model.World) :
    restrictionsHold signature model operator (position + 1) argument world <->
      objectLanguageDomainRequirement model
        (model.symbol operator) argument position world := by
  exact (realizes.domain position argument world).symm.trans
    (realizes.profileCoherent argument position world)

private theorem everyTail_iff_source
    {operator : String}
    (realizes : RealizesOperator signature model operator) :
    forall (position : Nat)
      (arguments : List model.Carrier) (world : model.World),
    model.everyTailArgumentInDomain (model.symbol operator) position
        arguments world <->
      everyTailRestrictionHolds signature model operator position
        arguments world
  | _, [], _ => Iff.rfl
  | position, argument :: rest, world => by
      simp only [Model.everyTailArgumentInDomain,
        everyTailRestrictionHolds]
      rw [realizes.domain position argument world,
        everyTail_iff_source realizes (position + 1) rest world]

/-- The native exact-tail guard is equivalent to the complete finite source
arity/domain condition.  This is the central signature-realization square. -/
theorem tail_guard_iff_source_signature
    {operator : String}
    (realizes : RealizesOperator signature model operator)
    (firstPosition : Nat)
    (arguments : List model.Carrier) (world : model.World) :
    model.tailInOperatorDomainFrom (model.symbol operator) firstPosition
        arguments world <->
      tailRestrictionsHold signature model operator firstPosition
        arguments world := by
  unfold Model.tailInOperatorDomainFrom tailRestrictionsHold
  rw [realizes.arity, realizes.variableArity,
    everyTail_iff_source realizes firstPosition arguments world]

end RealizesOperator

/-! ## A nontrivial realization witness -/

namespace SignatureSemanticsCanary

/-- One variadic relation whose first argument is an object-domain member and
whose remaining arguments are class-domain members. -/
def exampleSignature : SourceSignature :=
  let restrictions : List DomainRestriction :=
    [⟨"mixed", 1, .object, "Human"⟩,
     ⟨"mixed", 2, .class, "Class"⟩]
  { domainRestrictions := restrictions
    operatorClasses := [("mixed", "VariableArityRelation")]
    restrictionTable := [("mixed", restrictions)]
    variableArityNames := ["mixed"]
    operatorArities := [("mixed", 2)] }

abbrev ExampleCarrier := Sum (Unit -> Prop) String

private def exampleSymbol (name : String) : ExampleCarrier :=
  .inr name

private def exampleRelation
    (operator : ExampleCarrier) (arguments : List ExampleCarrier) : Prop :=
  match operator with
  | .inl _ => False
  | .inr name =>
      if name = "instance" then
        match arguments with
        | [argument, .inr className] =>
            className = "Human" /\ argument = .inr "alice"
        | _ => False
      else if name = "subclass" then
        match arguments with
        | [argument, .inr className] =>
            className = "Class" /\ argument = .inr "Mammal"
        | _ => False
      else if name = "domain" then
        match arguments with
        | [.inr relation, .inr position, classValue] =>
            relation = "mixed" /\ position = toString (1 : Nat) /\
              classValue = .inr "Human"
        | _ => False
      else if name = "domainSubclass" then
        match arguments with
        | [.inr relation, .inr position, classValue] =>
            relation = "mixed" /\ position = toString (2 : Nat) /\
              classValue = .inr "Class"
        | _ => False
      else False

/-- A concrete nontrivial model: `alice` satisfies the first domain,
`Mammal` satisfies the repeated class domain, and unrelated values do not. -/
def exampleModel : Model String String where
  World := Unit
  Carrier := ExampleCarrier
  symbol := exampleSymbol
  literal := .inr
  applyFunction := fun _ _ => .inr "$result"
  applyRelation := fun operator arguments _ =>
    exampleRelation operator arguments
  operatorArity
    | .inr name => if name = "mixed" then 2 else 0
    | .inl _ => 0
  variableArity
    | .inr name => name = "mixed"
    | .inl _ => false
  operatorDomain
    | .inr name, 0 =>
        if name = "mixed" then .inr "$objectDomain"
        else .inr "$universalDomain"
    | .inr name, _ =>
        if name = "mixed" then .inr "$classDomain"
        else .inr "$universalDomain"
    | .inl _, _ => .inr "$universalDomain"
  domainMember
    | argument, .inr domain, _ =>
        if domain = "$objectDomain" then argument = .inr "alice"
        else if domain = "$classDomain" then argument = .inr "Mammal"
        else if domain = "$universalDomain" then True
        else False
    | _, .inl _, _ => False
  quote := .inl
  holds
    | .inl intension, world => intension world
    | .inr _, _ => False
  holds_quote := fun _ _ => Iff.rfl
  kappa := fun _ => .inr "$kappa"

private theorem example_arity :
    exampleSignature.declaredArity "mixed" = 2 := by
  rfl

private theorem example_variable_arity :
    exampleSignature.isVariableArityOperator "mixed" = true := by
  rfl

private theorem example_first_restrictions :
    exampleSignature.argumentRestrictions "mixed" 1 =
      [⟨"mixed", 1, .object, "Human"⟩] := by
  rfl

private theorem example_second_restriction_reduced :
    exampleSignature.reduceRestrictions
        [⟨"mixed", 2, .class, "Class"⟩] =
      [⟨"mixed", 2, .class, "Class"⟩] := by
  rfl

private theorem example_later_restrictions (position : Nat) :
    exampleSignature.argumentRestrictions "mixed" (position + 2) =
      [⟨"mixed", 2, .class, "Class"⟩] := by
  cases position with
  | zero => rfl
  | succ position =>
      unfold SourceSignature.argumentRestrictions
      rw [example_variable_arity]
      simp [
        SourceSignature.applicableRestrictions,
        SourceSignature.finalDeclaredPosition,
        SourceSignature.lookupTable?, exampleSignature]
      exact example_second_restriction_reduced

private theorem example_restrictions
    (position : Nat) (argument : exampleModel.Carrier) :
    restrictionsHold exampleSignature exampleModel "mixed" (position + 1)
        argument () <->
      if position = 0 then argument = .inr "alice"
      else argument = .inr "Mammal" := by
  cases position with
  | zero =>
      change restrictionsHold exampleSignature exampleModel "mixed" 1
          argument () <-> argument = .inr "alice"
      unfold restrictionsHold
      rw [example_first_restrictions]
      simp [restrictionHolds,
        exampleModel, exampleRelation, exampleSymbol]
  | succ position =>
      change restrictionsHold exampleSignature exampleModel "mixed"
          (position + 2) argument () <-> argument = .inr "Mammal"
      unfold restrictionsHold
      rw [example_later_restrictions]
      simp [restrictionHolds,
        exampleModel, exampleRelation, exampleSymbol]

private theorem example_profile_coherent :
    ProfileCoherentAt exampleModel (exampleModel.symbol "mixed") := by
  intro argument position world
  cases world
  cases position with
  | zero =>
      simp [Model.inOperatorDomainAt, Model.effectiveDomainPosition,
        objectLanguageDomainRequirement, sourceDomainPosition,
        exampleModel, exampleRelation, exampleSymbol]
  | succ position =>
      cases position with
      | zero =>
          simp [Model.inOperatorDomainAt, Model.effectiveDomainPosition,
            objectLanguageDomainRequirement, sourceDomainPosition,
            exampleModel, exampleRelation, exampleSymbol]
      | succ position =>
          have notSmall : ¬((position + 2) < 2) := by omega
          simp [Model.inOperatorDomainAt, Model.effectiveDomainPosition,
            objectLanguageDomainRequirement, sourceDomainPosition,
            exampleModel, exampleRelation, exampleSymbol, notSmall]

/-- The concrete model realizes the mixed operator's source arity, repeated
domain, and object-language domain facts. -/
theorem example_realizes_operator :
    RealizesOperator exampleSignature exampleModel "mixed" := by
  refine
    { profileCoherent := example_profile_coherent
      arity := ?_
      variableArity := ?_
      domain := ?_ }
  · simpa [exampleModel, exampleSymbol] using example_arity.symm
  · simpa [exampleModel, exampleSymbol] using example_variable_arity.symm
  · intro position argument world
    cases world
    rw [example_restrictions]
    cases position with
    | zero =>
        simp [Model.inOperatorDomainAt, Model.effectiveDomainPosition,
          exampleModel, exampleSymbol]
    | succ position =>
        by_cases firstOptional : position = 0
        · subst position
          simp [Model.inOperatorDomainAt, Model.effectiveDomainPosition,
            exampleModel, exampleSymbol]
        · have notSmall : ¬((position + 1) < 2) := by omega
          simp [Model.inOperatorDomainAt, Model.effectiveDomainPosition,
            exampleModel, exampleSymbol, firstOptional, notSmall]

/-- The one-operator inventory is realized as a whole finite source signature. -/
theorem example_realizes_source :
    RealizesSourceSignature exampleSignature exampleModel := by
  refine { operator := ?_ }
  intro operator membership
  have equality : operator = "mixed" := by
    simpa [SourceSignature.declaredOperators, exampleSignature] using membership
  subst operator
  exact example_realizes_operator

/-- The realized signature accepts a lawful optional class argument. -/
theorem example_optional_argument_accepted :
    exampleModel.inOperatorDomainAt (exampleModel.symbol "mixed") 4
      (exampleModel.symbol "Mammal") () := by
  rfl

/-- The same optional position rejects an ordinary object-domain member. -/
theorem example_optional_argument_rejected :
    Not (exampleModel.inOperatorDomainAt (exampleModel.symbol "mixed") 4
      (exampleModel.symbol "alice") ()) := by
  simp [Model.inOperatorDomainAt, Model.effectiveDomainPosition,
    exampleModel, exampleSymbol]

end SignatureSemanticsCanary

end Mettapedia.Languages.SUMO.Native.SignatureSemantics
