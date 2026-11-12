import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionTypeReadApplications
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEArgumentMetatypeRole

/-!
# A held unary application's actual inferred return type

An Atom formal succeeds at the syntactic-kind cut. Its raw application type
therefore needs no inference of the held operand, and no evaluation of that
operand. This supplies the outer let's query for its collapse operand.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionHeldTypeRead

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeCallGraph NativeTypeSourcePorts
open RetainedTypePayloads (ExternalView)
open TypeReadSupply (Supply)
open HECollectionTypeReadPrimitives

theorem unary (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (name returned : String) (depth : Nat) (supply : Supply) (argument : Atom)
    (closed : atomVariables argument = [])
    (declared : rawDeclarations source world (.symbol name) =
      [CompletedDelivery.arrowType [Atom.atomType] (.symbol returned)])
    (ordinary : nativeClassify (.symbol name) [argument] = .ordinary) :
    (NativeTypeScopedReads.evaluate (HERangeTypeReadApplications.ops world active primitive unobservedClosure) source world (depth + 2)
      (.infer true (.expression [.symbol name, argument])) supply).1 = some (.types [.symbol returned]) := by
  let currentOps := HERangeTypeReadApplications.ops world active primitive unobservedClosure
  let arrowType := CompletedDelivery.arrowType [Atom.atomType] (.symbol returned)
  have arrowClosed : atomVariables arrowType = [] := by
    simp [arrowType, CompletedDelivery.arrowType, atomVariables, atomListVariables, Atom.atomType]
  have classifyReply (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.classify (.symbol name) [argument]) = (some (.class_ .ordinary), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, ordinary, NativeTypeScopedReads.retain]
  have annotationReply (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.annotations (.expression [.symbol name, argument])) = (some (.types []), current) :=
    annotation_empty world current _ (by simp [atomVariables, atomListVariables, closed]) (no_expression_annotations world _)
  have headReply (current : Supply) := operator_singleton currentOps world depth current name arrowType declared arrowClosed
  have kindReply (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.kind argument) = (some (.kind (getMetaType argument)), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, NativeTypeScopedReads.retain]
  have arrow : currentOps.arrow arrowType = some ([Atom.atomType], .symbol returned) := rfl
  have initial : currentOps.initial = Atom.var := rfl
  have metaChoice (state : TypeScopeMatcher.State) :
      currentOps.metaCheck (currentOps.apply state Atom.atomType) (getMetaType argument) = some true := rfl
  have normalized : currentOps.normalize (currentOps.apply Atom.var (.symbol returned)) = .symbol returned := rfl
  change (NativeTypeScopedReads.evaluate currentOps source world (depth + 2)
    (.infer true (.expression [.symbol name, argument])) supply).1 = _
  rw [NativeTypeScopedReads.evaluate]
  simp only [NativeTypeCallGraph.body, NativeTypeCallGraph.node, NativeTypeCallGraph.ordinary,
    NativeTypeCallGraph.typesRead, NativeTypeCallGraph.finishTypes, NativeTypeCallGraph.mapTypes,
    NativeTypeCallGraph.liftViews, NativeTypeCallGraph.viewQuestion,
    NativeTypeDemand.rowsPlan, NativeTypeDemand.argsPlan, NativeTypeDemand.typesRead,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    Mettapedia.Machines.ReadOnlyQuery.bind, Mettapedia.Machines.ReadOnlyQuery.map,
    classifyReply, annotationReply, headReply, kindReply, arrow, initial, metaChoice, normalized,
    List.isEmpty_nil, List.any_cons, List.any_nil, Option.isSome_some, Bool.true_or, ite_true,
    NativeTypeRecursiveDriver.completed, Except.map]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionHeldTypeRead
