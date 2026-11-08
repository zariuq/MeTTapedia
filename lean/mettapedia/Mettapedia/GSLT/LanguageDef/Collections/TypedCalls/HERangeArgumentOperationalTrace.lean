import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeArgumentQueryTransport

/-!
# The comparison argument's actual demanded inference and state retention

The existing argument plan obtains its Bool family from the actual scoped
reader. Its kind and inferred roles remain distinct; fresh-name supply is
threaded through the reader, while the successful constant-type match keeps
the complete incoming type-substitution state unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeArgumentOperationalTrace

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeCallGraph NativeTypeSourcePorts
open RetainedTypePayloads (ExternalView)
open TypeReadSupply (Supply)
open HERangeTypeReadPrimitives (source)

def service (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) (question : NativeTypeDemand.Question Atom) :
    Option (NativeTypeDemand.ViewReply Atom Atom) × Supply :=
  match NativeTypeCallGraph.viewQuestion question with
  | .inl primitive => NativeTypeScopedReads.primitive source world supply primitive
  | .inr call => NativeTypeScopedReads.evaluate currentOps source world depth call supply

theorem boolean_match (world : ExternalView) (state : TypeScopeMatcher.State) :
    TypeScopeMatcher.unify world state (.symbol "Bool") (.symbol "Bool") = some state := by
  have solved : UnifyAtoms.unify (.symbol "Bool") (.symbol "Bool") =
      some (fun name => Mettapedia.Logic.LP.Term.var name) := by cbv
  simp [TypeScopeMatcher.unify, substA, RetainedTypePayloads.observe, TypeScopeMatcher.wildcard,
    TypeScopeMatcher.actualWildcard, TypeScopeMatcher.spaceClassBridge, TypeScopeMatcher.spaceValueType,
    Atom.undefinedType, Atom.atomType, solved]
  apply congrArg some
  funext name
  exact substA_var_self (state name)

theorem comparison_argument_trace (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (depth : Nat) (supply : Supply) (state : TypeScopeMatcher.State) (left right : Int) :
    let currentOps := HERangeTypeReadApplications.ops world active primitive unobservedClosure
    let subject := Atom.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)]
    let returned := NativeTypeScopedReads.evaluate currentOps source world (depth + 2) (.infer true subject) supply
    Mettapedia.Machines.QueryState.run (service currentOps world (depth + 2))
      (Mettapedia.Machines.ReadOnlyQueryDemand.demand
        (NativeTypeDemand.argsPlan currentOps [.symbol "Bool"] [subject] state)) supply =
      ⟨some (.ok (some state)), returned.2,
        [(.kind subject, some (.kind Atom.expressionType)), (.inferred subject, some (.types [.symbol "Bool"]))]⟩ := by
  dsimp only
  let currentOps := HERangeTypeReadApplications.ops world active primitive unobservedClosure
  let subject := Atom.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)]
  have kindReply : service currentOps world (depth + 2) supply (.kind subject) =
      (some (.kind Atom.expressionType), supply) := by
    simp [service, NativeTypeCallGraph.viewQuestion, NativeTypeScopedReads.primitive,
      NativeTypeSourcePorts.primitive, NativeTypeScopedReads.retain, getMetaType, subject]
  have inferReply : (service currentOps world (depth + 2) supply (.inferred subject)).1 =
      some (.types [.symbol "Bool"]) := HERangeTypeReadApplications.comparison_type world active primitive unobservedClosure depth supply left right
  have metaChoice : currentOps.metaCheck (currentOps.apply state (.symbol "Bool")) Atom.expressionType = none := rfl
  have matching : currentOps.unify state (.symbol "Bool") (currentOps.apply state (.symbol "Bool")) = some state := boolean_match world state
  change Mettapedia.Machines.QueryState.run (service currentOps world (depth + 2))
    (Mettapedia.Machines.ReadOnlyQueryDemand.demand (NativeTypeDemand.argsPlan currentOps [.symbol "Bool"] [subject] state)) supply = _
  simp only [NativeTypeDemand.argsPlan, NativeTypeDemand.typesRead,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    kindReply, metaChoice, inferReply, StampInference.firstResult, matching]
  rfl

/-- After the demanded Bool query, the two Atom arguments contribute only
their kind reads. Their inferred views can remain entirely unavailable. -/
theorem conditional_arguments_trace (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (depth : Nat) (supply : Supply) (state : TypeScopeMatcher.State) (left right : Int) (yes no : Atom) :
    let currentOps := HERangeTypeReadApplications.ops world active primitive unobservedClosure
    let subject := Atom.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)]
    let returned := NativeTypeScopedReads.evaluate currentOps source world (depth + 2) (.infer true subject) supply
    Mettapedia.Machines.QueryState.run (service currentOps world (depth + 2))
      (Mettapedia.Machines.ReadOnlyQueryDemand.demand
        (NativeTypeDemand.argsPlan currentOps [.symbol "Bool", Atom.atomType, Atom.atomType] [subject, yes, no] state)) supply =
      ⟨some (.ok (some state)), returned.2,
        [(.kind subject, some (.kind Atom.expressionType)), (.inferred subject, some (.types [.symbol "Bool"])),
         (.kind yes, some (.kind (getMetaType yes))), (.kind no, some (.kind (getMetaType no)))]⟩ := by
  dsimp only
  let currentOps := HERangeTypeReadApplications.ops world active primitive unobservedClosure
  let subject := Atom.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)]
  have kindReply (current : Supply) (value : Atom) : service currentOps world (depth + 2) current (.kind value) =
      (some (.kind (getMetaType value)), current) := by
    simp [service, NativeTypeCallGraph.viewQuestion, NativeTypeScopedReads.primitive,
      NativeTypeSourcePorts.primitive, NativeTypeScopedReads.retain]
  have inferReply : (service currentOps world (depth + 2) supply (.inferred subject)).1 =
      some (.types [.symbol "Bool"]) := HERangeTypeReadApplications.comparison_type world active primitive unobservedClosure depth supply left right
  have metaChoice : currentOps.metaCheck (currentOps.apply state (.symbol "Bool")) Atom.expressionType = none := rfl
  have held (kind : Atom) : currentOps.metaCheck (currentOps.apply state Atom.atomType) kind = some true := rfl
  have matching : currentOps.unify state (.symbol "Bool") (currentOps.apply state (.symbol "Bool")) = some state := boolean_match world state
  change Mettapedia.Machines.QueryState.run (service currentOps world (depth + 2))
    (Mettapedia.Machines.ReadOnlyQueryDemand.demand
      (NativeTypeDemand.argsPlan currentOps [.symbol "Bool", Atom.atomType, Atom.atomType] [subject, yes, no] state)) supply = _
  simp only [NativeTypeDemand.argsPlan, NativeTypeDemand.typesRead,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    kindReply, show getMetaType subject = Atom.expressionType from rfl,
    metaChoice, held, inferReply, StampInference.firstResult, matching]
  rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeArgumentOperationalTrace
