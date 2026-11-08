import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryProducts
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCurrentWorld

/-! # The native inference call-graph plans under growing private coordinates -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryCallGraph

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines.ReadOnlyQueryWorldRelation (Related)
open TypeReadQueryWorlds NativeTypeCallGraph
open TypeDependencyAdmission
open RetainedTypePayloads (ExternalView)

def ReplyAnswers (world : Coordinates) : Except Unit Reply → Except Unit Reply → Prop :=
  CheckedRelated (RepliesRelated world)

theorem typesRead {Result : Type} (answers : Coordinates → Result → Result → Prop)
    (world : Coordinates) (firstKey secondKey : Question) (keys : KeysRelated world firstKey secondKey)
    (first second : List Atom → Plan Result)
    (later : ∀ next, Grows world next → ∀ left right, TypesRelated next left right →
      Related worlds (fun world => CheckedRelated (answers world)) next (first left) (second right)) :
    Related worlds (fun world => CheckedRelated (answers world)) world
      (NativeTypeCallGraph.typesRead firstKey first) (NativeTypeCallGraph.typesRead secondKey second) := by
  apply Related.read keys
  intro next grown firstReply secondReply replies
  cases replies with
  | types types => exact later next grown _ _ types
  | kind _ | class_ _ => exact .pure .error

theorem finishTypes (world : Coordinates) {first second : List Atom} (types : TypesRelated world first second) :
    Related worlds ReplyAnswers world (NativeTypeCallGraph.finishTypes first) (NativeTypeCallGraph.finishTypes second) :=
  .pure (.ok (.types types))

theorem closeTypes (world : Coordinates) {first second : List Atom} (types : TypesRelated world first second) :
    Related worlds ReplyAnswers world (NativeTypeCallGraph.closeTypes first) (NativeTypeCallGraph.closeTypes second) := by
  apply typesRead RepliesRelated world (.inl (.closure first)) (.inl (.closure second))
    ⟨second, rfl, types⟩
  intro next _ left right returned
  exact finishTypes next returned

theorem mapTypes {world : Coordinates} {first second : Plan (List Atom)}
    (related : Related worlds TypeAnswers world first second) :
    Related worlds ReplyAnswers world (NativeTypeCallGraph.mapTypes first) (NativeTypeCallGraph.mapTypes second) := by
  apply Mettapedia.Machines.ReadOnlyQueryWorldRelation.map_related worlds TypeAnswers ReplyAnswers related
  intro next _ left right answers
  cases answers with
  | error => exact .error
  | ok types => exact .ok (.types types)

theorem types_empty {world : Coordinates} {first second : List Atom}
    (types : TypesRelated world first second) : second.isEmpty = first.isEmpty := by
  rw [types.2.2, List.isEmpty_map]

theorem types_append {world : Coordinates} {first second rest otherRest : List Atom}
    (types : TypesRelated world first second) (tails : TypesRelated world rest otherRest) :
    TypesRelated world (first ++ rest) (second ++ otherRest) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (resourceFreeList_iff _).mpr
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => (resourceFreeList_iff _).mp types.1 atom h)
      (fun h => (resourceFreeList_iff _).mp tails.1 atom h)
  · intro name member
    rw [atomListVariables_eq_flatMap, List.flatMap_append, List.mem_append] at member
    exact member.elim (fun h => types.2.1 (by simpa only [atomListVariables_eq_flatMap] using h))
      (fun h => tails.2.1 (by simpa only [atomListVariables_eq_flatMap] using h))
  · simp only [types.2.2, tails.2.2, List.map_append]

theorem types_filter {world : Coordinates} {first second : List Atom}
    (types : TypesRelated world first second) (left right : Atom → Bool)
    (agree : ∀ atom ∈ first, right (renameAtom world.names atom) = left atom) :
    TypesRelated world (first.filter left) (second.filter right) := by
  refine ⟨(resourceFreeList_iff _).mpr (fun atom member =>
    (resourceFreeList_iff _).mp types.1 atom (List.mem_of_mem_filter member)), ?_, ?_⟩
  · intro name member
    rw [atomListVariables_eq_flatMap, List.mem_flatMap] at member
    obtain ⟨atom, present, member⟩ := member
    exact (types_member types (List.mem_of_mem_filter present)).2.1 member
  · rw [types.2.2, List.filter_map]
    congr 1
    exact List.filter_congr agree

theorem supplement_related (external : ExternalView) {world : Coordinates}
    {firstPrefix secondPrefix firstDerived secondDerived : List Atom}
    (prefixes : TypesRelated world firstPrefix secondPrefix)
    (derived : TypesRelated world firstDerived secondDerived) :
    TypesRelated world
      (NativeTypeViews.supplement (fun l r => RetainedTypePayloads.observe external l ==
        RetainedTypePayloads.observe external r) firstPrefix firstDerived)
      (NativeTypeViews.supplement (fun l r => RetainedTypePayloads.observe external l ==
        RetainedTypePayloads.observe external r) secondPrefix secondDerived) := by
  have otherPrefixSafe : resourceFreeList secondPrefix = true := by
    rw [prefixes.2.2]
    rw [← renameAtomList_eq_map, renameList_resourceFree]
    exact prefixes.1
  have otherDerivedSafe : resourceFreeList secondDerived = true := by
    rw [derived.2.2]
    rw [← renameAtomList_eq_map, renameList_resourceFree]
    exact derived.1
  rw [NativeTypeCurrentWorld.supplement_observe external _ _ prefixes.1 derived.1,
    NativeTypeCurrentWorld.supplement_observe external _ _ otherPrefixSafe otherDerivedSafe]
  apply types_append prefixes
  apply types_filter derived
  intro atom _
  rw [prefixes.2.2, List.any_map]
  simp only [Function.comp_def]
  congr 1
  apply List.any_congr rfl
  intro other
  exact TypeNormalizationNames.equality_equivariant world.names other atom

theorem any_arrow (external : ExternalView) (firstNormalize secondNormalize : Atom → Atom)
    (firstSubtypes secondSubtypes : List Atom → List Atom) (world : Coordinates)
    {first second : List Atom} (types : TypesRelated world first second) :
    (second.any fun row => ((TypeScopeMatcher.ops external secondNormalize secondSubtypes).arrow row).isSome) =
      (first.any fun row => ((TypeScopeMatcher.ops external firstNormalize firstSubtypes).arrow row).isSome) := by
  rw [types.2.2, List.any_map]
  simp only [Function.comp_def, TypeRowFreshening.arrow_rename, Option.isSome_map]
  rfl

theorem tuple_keys (world : Coordinates) (head : Atom) (values : List Atom)
    (headFixed : Fixed world (atomVariables head)) (valuesFixed : Fixed world (atomListVariables values)) :
    ∀ key ∈ NativeTypeDemand.Question.tupleHead head :: values.map NativeTypeDemand.Question.tuplePart,
      viewWorlds.keys world key key := by
  intro key member
  rcases List.mem_cons.mp member with rfl | child
  · exact ⟨rfl, headFixed⟩
  · obtain ⟨value, present, rfl⟩ := List.mem_map.mp child
    exact ⟨rfl, fixed_member valuesFixed present⟩

theorem ordinary (external : ExternalView) (firstNormalize secondNormalize : Atom → Atom)
    (normalizers : TypeReadQueryRows.Normalizers firstNormalize secondNormalize)
    (firstSubtypes secondSubtypes : List Atom → List Atom) (world : Coordinates)
    (head : Atom) (values : List Atom) (headFixed : Fixed world (atomVariables head))
    (valuesFixed : Fixed world (atomListVariables values)) :
    Related worlds ReplyAnswers world
      (NativeTypeCallGraph.ordinary (TypeScopeMatcher.ops external firstNormalize firstSubtypes) head values)
      (NativeTypeCallGraph.ordinary (TypeScopeMatcher.ops external secondNormalize secondSubtypes) head values) := by
  apply typesRead RepliesRelated world (.inr (.operatorRows head)) (.inr (.operatorRows head)) ⟨rfl, headFixed⟩
  intro next grown firstRows secondRows rows
  rw [any_arrow external firstNormalize secondNormalize firstSubtypes secondSubtypes next rows]
  split
  · apply mapTypes
    exact TypeReadQueryArguments.liftViews TypeAnswers
      (TypeReadQueryRows.rowsPlan external firstNormalize secondNormalize normalizers firstSubtypes secondSubtypes
        firstRows next secondRows values rows (fixed_mono grown valuesFixed))
  · apply Mettapedia.Machines.ReadOnlyQueryWorldRelation.bind_related worlds
      TypeReadQueryProducts.ProductAnswers ReplyAnswers
    · exact TypeReadQueryArguments.liftViews TypeReadQueryProducts.ProductAnswers
        (TypeReadQueryProducts.productPlan _ next
          (tuple_keys next head values (fixed_mono grown headFixed) (fixed_mono grown valuesFixed)))
    · intro last _ firstProducts secondProducts products
      cases products with
      | error => exact .pure .error
      | ok products =>
          rename_i firstFamilies secondFamilies
          have tuples := TypeReadQueryProducts.tuple_families last products
          have sameEmpty : (secondFamilies.map Atom.expression).isEmpty =
              (firstFamilies.map Atom.expression).isEmpty := by rw [tuples.2.2, List.isEmpty_map]
          by_cases empty : (firstFamilies.map Atom.expression).isEmpty = true
          · have secondEmpty := sameEmpty.trans empty
            simpa only [TypeScopeMatcher.ops, empty, secondEmpty, if_true] using
              finishTypes last (first := [Atom.undefinedType]) (second := [Atom.undefinedType])
                ⟨rfl, by simp [atomListVariables, Atom.undefinedType, atomVariables], rfl⟩
          · have secondNonempty : (secondFamilies.map Atom.expression).isEmpty ≠ true := by
              rw [sameEmpty]
              exact empty
            simpa only [TypeScopeMatcher.ops, empty, secondNonempty, Bool.false_eq_true, if_false]
              using closeTypes last tuples

theorem annotated (external : ExternalView) (firstNormalize secondNormalize : Atom → Atom)
    (normalizers : TypeReadQueryRows.Normalizers firstNormalize secondNormalize)
    (firstSubtypes secondSubtypes : List Atom → List Atom) (world : Coordinates)
    (head : Atom) (values firstAnnotations secondAnnotations : List Atom)
    (headFixed : Fixed world (atomVariables head)) (valuesFixed : Fixed world (atomListVariables values))
    (annotations : TypesRelated world firstAnnotations secondAnnotations) :
    Related worlds ReplyAnswers world
      (NativeTypeCallGraph.annotated (TypeScopeMatcher.currentOps external firstNormalize firstSubtypes)
        head values firstAnnotations)
      (NativeTypeCallGraph.annotated (TypeScopeMatcher.currentOps external secondNormalize secondSubtypes)
        head values secondAnnotations) := by
  apply typesRead RepliesRelated world (.inl (.closure firstAnnotations)) (.inl (.closure secondAnnotations))
    ⟨secondAnnotations, rfl, annotations⟩
  intro next grown firstClosed secondClosed closed
  apply typesRead RepliesRelated next (.inr (.operatorRows head)) (.inr (.operatorRows head))
    ⟨rfl, fixed_mono grown headFixed⟩
  intro last extended firstRows secondRows rows
  have arrows := any_arrow external firstNormalize secondNormalize firstSubtypes secondSubtypes last rows
  change (secondRows.any fun row =>
    ((TypeScopeMatcher.currentOps external secondNormalize secondSubtypes).arrow row).isSome) =
      (firstRows.any fun row =>
        ((TypeScopeMatcher.currentOps external firstNormalize firstSubtypes).arrow row).isSome) at arrows
  rw [arrows]
  split
  · simp only [TypeScopeMatcher.currentOps, NativeTypeAnnotationPolicy.rowsPlan_policy]
    apply Mettapedia.Machines.ReadOnlyQueryWorldRelation.map_related worlds TypeAnswers ReplyAnswers
    · exact TypeReadQueryArguments.liftViews TypeAnswers
        (TypeReadQueryRows.rowsPlan external firstNormalize secondNormalize normalizers firstSubtypes secondSubtypes
          firstRows last secondRows values rows (fixed_mono extended (fixed_mono grown valuesFixed)))
    · intro final later firstAnswer secondAnswer answers
      cases answers with
      | error => exact .error
      | ok types => exact .ok (.types (supplement_related external
          (types_mono (grows_trans extended later) closed) types))
  · exact finishTypes last (types_mono extended closed)

theorem fixed_append {world : Coordinates} {first second : List String}
    (left : Fixed world first) (right : Fixed world second) : Fixed world (first ++ second) := by
  constructor
  · intro name member
    exact (List.mem_append.mp member).elim (fun h => left.1 h) (fun h => right.1 h)
  · intro name member
    exact (List.mem_append.mp member).elim (fun h => left.2 name h) (fun h => right.2 name h)

theorem node (external : ExternalView) (firstNormalize secondNormalize : Atom → Atom)
    (normalizers : TypeReadQueryRows.Normalizers firstNormalize secondNormalize)
    (firstSubtypes secondSubtypes : List Atom → List Atom) (world : Coordinates)
    (direct : Bool) (head : Atom) (values : List Atom)
    (headFixed : Fixed world (atomVariables head)) (valuesFixed : Fixed world (atomListVariables values)) :
    Related worlds ReplyAnswers world
      (NativeTypeCallGraph.node (TypeScopeMatcher.currentOps external firstNormalize firstSubtypes) direct head values)
      (NativeTypeCallGraph.node (TypeScopeMatcher.currentOps external secondNormalize secondSubtypes) direct head values) := by
  unfold NativeTypeCallGraph.node
  apply Related.read (show KeysRelated world (.inl (.classify head values))
    (.inl (.classify head values)) from ⟨rfl, fixed_append headFixed valuesFixed⟩)
  intro next grown firstReply secondReply replies
  cases replies with
  | types _ | kind _ => exact .pure .error
  | class_ kind =>
      cases kind with
      | nativeMork | listValue =>
          exact finishTypes next
            ⟨rfl, by simp [atomListVariables, TypeScopeMatcher.currentOps, TypeScopeMatcher.ops, atomVariables], rfl⟩
      | ordinary =>
          have plain := ordinary external firstNormalize secondNormalize normalizers firstSubtypes secondSubtypes
            next head values (fixed_mono grown headFixed) (fixed_mono grown valuesFixed)
          cases direct with
          | false =>
              simpa only [Bool.false_eq_true, if_false, TypeScopeMatcher.currentOps,
                NativeTypeAnnotationPolicy.ordinary_policy] using plain
          | true =>
              apply typesRead RepliesRelated next (.inl (.annotations (.expression (head :: values))))
                (.inl (.annotations (.expression (head :: values))))
                ⟨rfl, fixed_append (fixed_mono grown headFixed) (fixed_mono grown valuesFixed)⟩
              intro last extended firstTypes secondTypes types
              rw [types_empty types]
              split
              · change Related worlds ReplyAnswers last _ _
                simp only [TypeScopeMatcher.currentOps, NativeTypeAnnotationPolicy.ordinary_policy]
                exact ordinary external firstNormalize secondNormalize normalizers firstSubtypes secondSubtypes
                  last head values (fixed_mono extended (fixed_mono grown headFixed))
                    (fixed_mono extended (fixed_mono grown valuesFixed))
              · exact annotated external firstNormalize secondNormalize normalizers firstSubtypes secondSubtypes
                  last head values firstTypes secondTypes (fixed_mono extended (fixed_mono grown headFixed))
                    (fixed_mono extended (fixed_mono grown valuesFixed)) types

theorem keepTuple_rename (external : ExternalView) (firstNormalize secondNormalize : Atom → Atom)
    (firstSubtypes secondSubtypes : List Atom → List Atom) (names : Equiv.Perm String)
    (atHead : Bool) (atom : Atom) :
    NativeTypeCallGraph.keepTuple (TypeScopeMatcher.currentOps external secondNormalize secondSubtypes)
      atHead (renameAtom names atom) =
    NativeTypeCallGraph.keepTuple (TypeScopeMatcher.currentOps external firstNormalize firstSubtypes) atHead atom := by
  have equal := TypeNormalizationNames.equality_equivariant names atom Atom.undefinedType
  change (renameAtom names atom == Atom.undefinedType) = (atom == Atom.undefinedType) at equal
  unfold NativeTypeCallGraph.keepTuple
  change (!(renameAtom names atom == Atom.undefinedType) &&
    (!atHead || !((TypeScopeMatcher.ops external secondNormalize secondSubtypes).arrow (renameAtom names atom)).isSome)) = _
  rw [equal, TypeRowFreshening.arrow_rename, Option.isSome_map]
  rfl

theorem body (external : ExternalView) (firstNormalize secondNormalize : Atom → Atom)
    (normalizers : TypeReadQueryRows.Normalizers firstNormalize secondNormalize)
    (firstSubtypes secondSubtypes : List Atom → List Atom) (world : Coordinates)
    (call : Call) (fixed : Fixed world (questionNames (.inr call))) :
    Related worlds ReplyAnswers world
      (NativeTypeCallGraph.body (TypeScopeMatcher.currentOps external firstNormalize firstSubtypes) call)
      (NativeTypeCallGraph.body (TypeScopeMatcher.currentOps external secondNormalize secondSubtypes) call) := by
  have undef (point : Coordinates) : TypesRelated point [Atom.undefinedType] [Atom.undefinedType] :=
    ⟨rfl, by simp [atomListVariables, Atom.undefinedType, atomVariables], rfl⟩
  have empty (point : Coordinates) : TypesRelated point [] [] := ⟨rfl, by simp [atomListVariables], rfl⟩
  cases call with
  | infer direct atom =>
      cases atom with
      | var _ => exact finishTypes world (undef world)
      | grounded value =>
          apply typesRead RepliesRelated world (.inl (.intrinsic (.grounded value)))
            (.inl (.intrinsic (.grounded value))) ⟨rfl, fixed⟩
          intro next _ firstTypes secondTypes types
          rw [types_empty types]
          split
          · exact finishTypes next (undef next)
          · exact finishTypes next types
      | symbol name =>
          cases direct with
          | false => exact finishTypes world (undef world)
          | true =>
              apply typesRead RepliesRelated world (.inl (.annotations (.symbol name)))
                (.inl (.annotations (.symbol name))) ⟨rfl, fixed⟩
              intro next _ firstTypes secondTypes types
              rw [types_empty types]
              split
              · exact finishTypes next (undef next)
              · exact closeTypes next types
      | expression children =>
          cases children with
          | nil => exact finishTypes world (undef world)
          | cons head values =>
              exact node external firstNormalize secondNormalize normalizers firstSubtypes
                secondSubtypes world direct head values (fixed_head fixed) (fixed_tail fixed)
  | tuplePart atHead atom =>
      have filtered (next : Coordinates) (firstTypes secondTypes : List Atom)
          (types : TypesRelated next firstTypes secondTypes) :=
        finishTypes next (types_filter types
          (NativeTypeCallGraph.keepTuple (TypeScopeMatcher.currentOps external firstNormalize firstSubtypes) atHead)
          (NativeTypeCallGraph.keepTuple (TypeScopeMatcher.currentOps external secondNormalize secondSubtypes) atHead)
          (fun atom _ => keepTuple_rename external firstNormalize secondNormalize firstSubtypes secondSubtypes
            next.names atHead atom))
      cases atom with
      | var _ => exact finishTypes world (empty world)
      | grounded value =>
          apply typesRead RepliesRelated world (.inl (.intrinsic (.grounded value)))
            (.inl (.intrinsic (.grounded value))) ⟨rfl, fixed⟩
          intro next _ firstTypes secondTypes types
          exact filtered next firstTypes secondTypes types
      | symbol name =>
          apply typesRead RepliesRelated world (.inl (.annotations (.symbol name)))
            (.inl (.annotations (.symbol name))) ⟨rfl, fixed⟩
          intro next _ firstTypes secondTypes types
          exact filtered next firstTypes secondTypes types
      | expression children =>
          apply typesRead RepliesRelated world (.inr (.infer true (.expression children)))
            (.inr (.infer true (.expression children))) ⟨rfl, fixed⟩
          intro next _ firstTypes secondTypes types
          exact filtered next firstTypes secondTypes types
  | operatorRows atom =>
      apply typesRead RepliesRelated world (.inl (.annotations atom)) (.inl (.annotations atom)) ⟨rfl, fixed⟩
      intro next grown firstRows secondRows rows
      rw [types_empty rows]
      split
      · cases atom with
        | var _ | grounded _ | symbol _ => exact finishTypes next (empty next)
        | expression children =>
            apply typesRead RepliesRelated next (.inr (.infer true (.expression children)))
              (.inr (.infer true (.expression children))) ⟨rfl, fixed_mono grown fixed⟩
            intro last _ firstTypes secondTypes types
            apply finishTypes last
            apply types_filter types
            intro atom _
            simp only [TypeScopeMatcher.currentOps, TypeRowFreshening.arrow_rename, Option.isSome_map]
            rfl
      · exact finishTypes next rows

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryCallGraph
