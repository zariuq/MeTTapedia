import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryWorlds

/-!
# Actual primitive reads extend the private-coordinate world

These are local service laws for existing annotation, subtype-closure,
intrinsic, metatype and head-classification reads. Recursive inquiry handling
is not replaced by a total oracle. Original value subjects stay fixed while
private type variables in closure seeds and replies are transported.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryServices

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open NativeTypeCallGraph NativeTypeSourcePorts TypeReadQueryWorlds TypeDependencyAdmission
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)

theorem option_types_world (before : Coordinates) (captured : List String)
    (first second : Option (List Atom) × Supply) (names : Equiv.Perm String)
    (agrees : ∀ name ∈ before.live ++ captured, names name = before.names name)
    (carried : second.1 = first.1.map (List.map (renameAtom names)))
    (safe : ∀ types, first.1 = some types → resourceFreeList types = true)
    (firstProtected : (before.live ++ captured) ++ atomListVariables first.1.toList.flatten ⊆ first.2.used)
    (secondProtected : ((before.live ++ captured) ++ atomListVariables first.1.toList.flatten).map names ⊆ second.2.used) :
    ∃ after : Coordinates, Grows before after ∧ Protected after first.2 second.2 ∧
      Option.Rel (RepliesRelated after)
        (first.1.map (fun types => (NativeTypeDemand.ViewReply.types types : Reply)))
        (second.1.map (fun types => (NativeTypeDemand.ViewReply.types types : Reply))) := by
  let after : Coordinates := ⟨names, (before.live ++ captured) ++ atomListVariables first.1.toList.flatten⟩
  refine ⟨after, ⟨?_, ?_⟩, ⟨firstProtected, secondProtected⟩, ?_⟩
  · exact fun _ member => List.mem_append_left _ (List.mem_append_left _ member)
  · exact fun name member => agrees name (List.mem_append_left _ member)
  · rw [carried]
    cases found : first.1 with
    | none => exact .none
    | some types =>
        apply Option.Rel.some
        apply RepliesRelated.types
        refine ⟨safe types found, ?_, rfl⟩
        intro name member
        change name ∈ (before.live ++ captured) ++ atomListVariables first.1.toList.flatten
        simp only [found, Option.toList_some, List.flatten_cons, List.flatten_nil, List.append_nil]
        exact List.mem_append_right _ member

theorem annotation (source : Source) (external : ExternalView) (sourceSafe : NativeTypeSourcePorts.Safe source)
    (before : Coordinates) (first second : Supply) (protectedSupplies : Protected before first second)
    (subject : Atom) (fixed : Fixed before (atomVariables subject)) :
    ∃ after : Coordinates, Grows before after ∧
      Protected after
        (NativeTypeScopedReads.primitive source external first (.annotations subject)).2
        (NativeTypeScopedReads.primitive source external second (.annotations subject)).2 ∧
      Option.Rel (RepliesRelated after)
        (NativeTypeScopedReads.primitive source external first (.annotations subject)).1
        (NativeTypeScopedReads.primitive source external second (.annotations subject)).1 := by
  let schemas := rawDeclarations source external subject
  let left := TypeReadSupply.freshList (TypeReadSupply.remember first [subject]) schemas
  let right := TypeReadSupply.freshList (TypeReadSupply.remember second [subject]) schemas
  obtain ⟨names, agrees, carried, firstKeeps, secondKeeps⟩ :=
    TypeReadWorlds.extend_allocated_world before.names (before.live ++ atomVariables subject)
      (TypeReadSupply.remember first [subject]) (TypeReadSupply.remember second [subject])
      (NativeTypeReadWorlds.remember_protects before.live first subject protectedSupplies.1)
      (NativeTypeReadWorlds.remember_mapped_subject before.names before.live second subject protectedSupplies.2 fixed.2)
      schemas
  have safe : resourceFreeList left.1 = true := TypeReadSupply.freshList_resourceFree _ _
    (rawDeclarations_safe source sourceSafe external subject)
  have result := option_types_world before (atomVariables subject) (some left.1, left.2) (some right.1, right.2)
    names agrees (congrArg some carried)
    (fun types returned => by cases Option.some.inj returned; exact safe)
    (by simpa only [Option.toList_some, List.flatten_cons, List.flatten_nil, List.append_nil] using firstKeeps)
    (by simpa only [Option.toList_some, List.flatten_cons, List.flatten_nil, List.append_nil] using secondKeeps)
  exact result

theorem closure (source : Source) (external : ExternalView) (sourceSafe : NativeTypeSourcePorts.Safe source)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (before : Coordinates) (first second : Supply) (protectedSupplies : Protected before first second)
    (seeds otherSeeds : List Atom) (related : TypesRelated before seeds otherSeeds) :
    ∃ after : Coordinates, Grows before after ∧
      Protected after (NativeTypeScopedReads.primitive source external first (.closure seeds)).2
        (NativeTypeScopedReads.primitive source external second (.closure otherSeeds)).2 ∧
      Option.Rel (RepliesRelated after)
        (NativeTypeScopedReads.primitive source external first (.closure seeds)).1
        (NativeTypeScopedReads.primitive source external second (.closure otherSeeds)).1 := by
  have rowsSafe := ScopedSubtypeReadSafety.rowsSafe_of_resourceFree source.rows sourceSafe.1
  let left := ScopedSubtypeReads.completeTypes external source.rows source.subtypeFresh source.alpha
    source.subtypeBudget seeds first
  let right := ScopedSubtypeReads.completeTypes external source.rows source.subtypeFresh source.alpha
    source.subtypeBudget otherSeeds second
  obtain ⟨names, agrees, carried, firstKeeps, secondKeeps⟩ :=
    ScopedSubtypeClosureCoordinates.completeTypes_read_coordinates external source.rows rowsSafe source.subtypeFresh
      source.alpha alpha before.names before.live source.subtypeBudget seeds related.1 first second
      protectedSupplies.1 protectedSupplies.2
  rw [← related.2.2] at carried secondKeeps
  have result := option_types_world before (atomListVariables seeds) left right names agrees carried
    (fun types returned => ScopedSubtypeReadSafety.completeTypes_safe external source.rows rowsSafe source.subtypeFresh
      source.alpha source.subtypeBudget seeds related.1 first types returned) firstKeeps secondKeeps
  obtain ⟨after, grown, keeps, replies⟩ := result
  refine ⟨after, grown, ⟨?_, ?_⟩, replies⟩
  · exact fun _ member => NativeTypeScopedReads.retain_old _ _ (keeps.1 member)
  · exact fun _ member => NativeTypeScopedReads.retain_old _ _ (keeps.2 member)

theorem primitive (source : Source) (external : ExternalView) (sourceSafe : NativeTypeSourcePorts.Safe source)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (before : Coordinates) (first second : Supply) (protectedSupplies : Protected before first second)
    (firstKey secondKey : Primitive) (keys : KeysRelated before (.inl firstKey) (.inl secondKey)) :
    ∃ after : Coordinates, Grows before after ∧
      Protected after (NativeTypeScopedReads.primitive source external first firstKey).2
        (NativeTypeScopedReads.primitive source external second secondKey).2 ∧
      Option.Rel (RepliesRelated after)
        (NativeTypeScopedReads.primitive source external first firstKey).1
        (NativeTypeScopedReads.primitive source external second secondKey).1 := by
  cases firstKey with
  | annotations subject =>
      have same : secondKey = .annotations subject := Sum.inl.inj keys.1
      subst secondKey
      exact annotation source external sourceSafe before first second protectedSupplies subject keys.2
  | closure seeds =>
      obtain ⟨other, same, related⟩ := keys
      cases Sum.inl.inj same
      exact closure source external sourceSafe alpha before first second protectedSupplies seeds other related
  | kind atom =>
      have same : secondKey = .kind atom := Sum.inl.inj keys.1
      subst secondKey
      exact ⟨before, grows_refl before, protectedSupplies, .some (.kind _)⟩
  | classify head values =>
      have same : secondKey = .classify head values := Sum.inl.inj keys.1
      subst secondKey
      exact ⟨before, grows_refl before, protectedSupplies, .some (.class_ _)⟩
  | intrinsic atom =>
      have same : secondKey = .intrinsic atom := Sum.inl.inj keys.1
      subst secondKey
      cases atom with
      | symbol _ | var _ | expression _ => exact ⟨before, grows_refl before, protectedSupplies, .none⟩
      | grounded value =>
          cases value with
          | custom _ _ => exact ⟨before, grows_refl before, protectedSupplies, .none⟩
          | int _ | bool _ | string _ =>
              refine ⟨before, grows_refl before, protectedSupplies, .some (.types ?_)⟩
              exact ⟨rfl, by simp [atomListVariables, atomVariables, getGroundedType], rfl⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryServices
