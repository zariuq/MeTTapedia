import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadWorlds
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReadVariants

/-!
# Coordinate extension at the actual annotation-read port

The port reads the real ordered declaration family and freshens it under the
remembered subject. Unequal earlier allocation histories are related by an
extension that keeps retained names and the public subject fixed. The result
includes protection of the new names in both resulting supplies, not merely
an alpha equality of the current output. Recursive closure/cached-call
simulation remains a separate composition obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeReadWorlds

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open NativeTypeCallGraph NativeTypeSourcePorts TypeReadWorlds
open TypeReadSupply (Supply remember freshList)
open RetainedTypePayloads (ExternalView)

def renameReply (names : Equiv.Perm String) : Reply → Reply
  | .types types => .types (types.map (renameAtom names))
  | .kind kind => .kind (renameAtom names kind)
  | .class_ kind => .class_ kind

theorem remember_protects (live : List String) (supply : Supply) (subject : Atom)
    (covered : live ⊆ supply.used) :
    live ++ atomVariables subject ⊆ (remember supply [subject]).used := by
  intro name member
  rcases List.mem_append.mp member with old | subjectName
  · exact TypeReadSupply.remember_old supply [subject] (covered old)
  · apply TypeReadSupply.remember_new supply [subject]
    simpa only [atomListVariables, List.append_nil] using subjectName

theorem remember_mapped_subject (previous : Equiv.Perm String) (live : List String)
    (supply : Supply) (subject : Atom)
    (covered : live.map previous ⊆ supply.used)
    (fixed : ∀ name ∈ atomVariables subject, previous name = name) :
    (live ++ atomVariables subject).map previous ⊆ (remember supply [subject]).used := by
  intro name member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  rcases List.mem_append.mp present with old | subjectName
  · exact TypeReadSupply.remember_old supply [subject]
      (covered (List.mem_map.mpr ⟨original, old, rfl⟩))
  · rw [fixed original subjectName]
    apply TypeReadSupply.remember_new supply [subject]
    simpa only [atomListVariables, List.append_nil] using subjectName

/-- No already-computed typing is supplied as a premise: both replies are
the results of the existing annotation port on the same source and subject. -/
theorem annotation_coordinates (source : Source) (world : ExternalView)
    (previous : Equiv.Perm String) (live : List String) (first second : Supply)
    (firstProtected : live ⊆ first.used)
    (secondProtected : live.map previous ⊆ second.used)
    (subject : Atom) (fixedSubject : ∀ name ∈ atomVariables subject, previous name = name) :
    let schemas := rawDeclarations source world subject
    let leftTypes := (freshList (remember first [subject]) schemas).1
    let left := NativeTypeScopedReads.primitive source world first (.annotations subject)
    let right := NativeTypeScopedReads.primitive source world second (.annotations subject)
    ∃ next : Equiv.Perm String,
      (∀ name ∈ live ++ atomVariables subject, next name = previous name) ∧
      right.1 = left.1.map (renameReply next) ∧
      ((live ++ atomVariables subject) ++ atomListVariables leftTypes) ⊆ left.2.used ∧
      ((live ++ atomVariables subject) ++ atomListVariables leftTypes).map next ⊆ right.2.used := by
  dsimp only
  obtain ⟨next, agrees, carried, firstKeeps, secondKeeps⟩ :=
    extend_allocated_world previous (live ++ atomVariables subject)
      (remember first [subject]) (remember second [subject])
      (remember_protects live first subject firstProtected)
      (remember_mapped_subject previous live second subject secondProtected fixedSubject)
      (rawDeclarations source world subject)
  refine ⟨next, agrees, ?_, firstKeeps, secondKeeps⟩
  change some (.types (freshList (remember second [subject]) (rawDeclarations source world subject)).1) =
    some (renameReply next (.types (freshList (remember first [subject]) (rawDeclarations source world subject)).1))
  exact congrArg (fun types => some (NativeTypeDemand.ViewReply.types types : Reply)) carried

theorem annotation_keeps_existing_state (source : Source) (world : ExternalView)
    (previous : Equiv.Perm String) (live : List String) (first second : Supply)
    (firstProtected : live ⊆ first.used)
    (secondProtected : live.map previous ⊆ second.used)
    (subject : Atom) (fixedSubject : ∀ name ∈ atomVariables subject, previous name = name)
    (state : TypeScopeMatcher.State) (supported : Supported live state) :
    ∃ next : Equiv.Perm String,
      TypeScopeRenaming.renameState next state = TypeScopeRenaming.renameState previous state ∧
      (NativeTypeScopedReads.primitive source world second (.annotations subject)).1 =
        (NativeTypeScopedReads.primitive source world first (.annotations subject)).1.map (renameReply next) := by
  obtain ⟨next, agrees, reply, _, _⟩ := annotation_coordinates source world previous live first second
    firstProtected secondProtected subject fixedSubject
  exact ⟨next, supported_readout live state supported previous next
    (fun name member => agrees name (List.mem_append_left _ member)), reply⟩

namespace Controls

def source : Source where
  rows := [.expression [.symbol ":", .symbol "H", TypeReadWorlds.Controls.schema]]
  intrinsicRows := []
  rename := fun _ _ name => name
  subtypeBudget := 0
  subtypeFresh := "subtype"
  alpha := TypeAlphaComparison.check

def external : ExternalView := fun tag key => .grounded (.custom tag key)

theorem actual_same_subject_has_different_private_coordinates :
    (NativeTypeScopedReads.primitive source external TypeReadWorlds.Controls.before (.annotations (.symbol "H"))).1 ≠
      (NativeTypeScopedReads.primitive source external TypeReadWorlds.Controls.afterSkipped (.annotations (.symbol "H"))).1 := by
  cbv
  simp

theorem actual_read_extends_the_caller_map :
    ∃ next : Equiv.Perm String, next "caller" = "caller" ∧
      (NativeTypeScopedReads.primitive source external TypeReadWorlds.Controls.afterSkipped (.annotations (.symbol "H"))).1 =
        (NativeTypeScopedReads.primitive source external TypeReadWorlds.Controls.before (.annotations (.symbol "H"))).1.map
          (renameReply next) := by
  obtain ⟨next, fixed, reply, _, _⟩ := annotation_coordinates source external (Equiv.refl String)
    ["caller"] TypeReadWorlds.Controls.before TypeReadWorlds.Controls.afterSkipped
    (by simp [TypeReadWorlds.Controls.before]) (by simp [TypeReadWorlds.Controls.afterSkipped])
    (.symbol "H") (by simp [atomVariables])
  exact ⟨next, fixed "caller" (by simp), reply⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeReadWorlds
