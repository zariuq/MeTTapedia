import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryCallGraph
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryServices

/-!
# Recursive type inquiries across private allocation histories

Every recursive child uses the existing occurrence-scoped evaluator. Local
annotation and closure reads extend one correspondence, preserving all names
already exposed to their caller. The final result and supplies are related
without equating allocation counters. Immutable closed result families then
agree literally, in their original order and multiplicity.

This compares the same recursion and subtype budgets on two uncached runs.
It is the recursive coordinate theorem, not yet a theorem for arbitrary
cache-hit schedules or for equal physical work budgets.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryRecursive

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines
open NativeTypeCallGraph NativeTypeSourcePorts TypeReadQueryWorlds
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)

theorem completed_related {world : Coordinates} {first second : Option (Except Unit Reply)}
    (related : Option.Rel (TypeReadQueryCallGraph.ReplyAnswers world) first second) :
    Option.Rel (RepliesRelated world)
      (NativeTypeRecursiveDriver.completed first) (NativeTypeRecursiveDriver.completed second) := by
  cases related with
  | none => exact .none
  | some answers =>
      cases answers with
      | error => exact .none
      | ok replies => exact .some replies

theorem retain_protected {world : Coordinates} {first second : Supply}
    (protectedSupplies : Protected world first second) (firstReply secondReply : Option Reply) :
    Protected world (NativeTypeScopedReads.retain first firstReply) (NativeTypeScopedReads.retain second secondReply) :=
  ⟨fun _ member => NativeTypeScopedReads.retain_old _ _ (protectedSupplies.1 member),
    fun _ member => NativeTypeScopedReads.retain_old _ _ (protectedSupplies.2 member)⟩

theorem evaluate_coordinates (source : Source) (external : ExternalView) (sourceSafe : NativeTypeSourcePorts.Safe source)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (firstNormalize secondNormalize : Atom → Atom)
    (normalizers : TypeReadQueryRows.Normalizers firstNormalize secondNormalize)
    (firstSubtypes secondSubtypes : List Atom → List Atom) (depth : Nat) :
    ∀ (world : Coordinates) (call : Call) (first second : Supply),
      Fixed world (questionNames (.inr call)) → Protected world first second →
      ∃ after, Grows world after ∧
        Protected after
          (NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external firstNormalize firstSubtypes)
            source external depth call first).2
          (NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external secondNormalize secondSubtypes)
            source external depth call second).2 ∧
        Option.Rel (RepliesRelated after)
          (NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external firstNormalize firstSubtypes)
            source external depth call first).1
          (NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external secondNormalize secondSubtypes)
            source external depth call second).1 := by
  induction depth with
  | zero =>
      intro world call first second _ supplies
      exact ⟨world, grows_refl world, supplies, .none⟩
  | succ depth ih =>
      intro world call first second fixed supplies
      let firstService : Supply → Question → Option Reply × Supply := fun current => fun
        | .inl key => NativeTypeScopedReads.primitive source external current key
        | .inr child => NativeTypeScopedReads.evaluate
            (TypeScopeMatcher.currentOps external firstNormalize firstSubtypes) source external depth child current
      let secondService : Supply → Question → Option Reply × Supply := fun current => fun
        | .inl key => NativeTypeScopedReads.primitive source external current key
        | .inr child => NativeTypeScopedReads.evaluate
            (TypeScopeMatcher.currentOps external secondNormalize secondSubtypes) source external depth child current
      have services : ReadOnlyQueryWorldRelation.ServicesRelated worlds Protected firstService secondService := by
        intro before left right kept firstKey secondKey keys
        cases firstKey with
        | inl primitive =>
            cases secondKey with
            | inl other =>
                exact TypeReadQueryServices.primitive source external sourceSafe alpha
                  before left right kept primitive other keys
            | inr other =>
                cases primitive with
                | closure seeds => obtain ⟨_, impossible, _⟩ := keys; cases impossible
                | annotations _ | intrinsic _ | kind _ | classify _ _ => cases keys.1
        | inr child =>
            obtain ⟨same, childFixed⟩ := keys
            subst secondKey
            exact ih before child left right childFixed kept
      obtain ⟨after, grown, kept, answers, _trace⟩ :=
        ReadOnlyQueryWorldRelation.demand_run_related worlds TypeReadQueryCallGraph.ReplyAnswers Protected
          firstService secondService services
          (TypeReadQueryCallGraph.body external firstNormalize secondNormalize normalizers firstSubtypes secondSubtypes
            world call fixed) first second supplies
      exact ⟨after, grown, retain_protected kept _ _, completed_related answers⟩

/-- Closed immutable output is stronger than resource-free output: only
the former can be reused literally rather than as a fresh type family. -/
theorem retained_types_equal {world : Coordinates} {first second : List Atom}
    (related : TypesRelated world first second) (retained : RetainedTypePayloads.admittedList first = true) :
    second = first := by
  rw [related.2.2, ← renameAtomList_eq_map]
  exact TypeRowFreshening.admittedList_rename world.names first retained

theorem retained_evaluate_equal (source : Source) (external : ExternalView) (sourceSafe : NativeTypeSourcePorts.Safe source)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (firstNormalize secondNormalize : Atom → Atom)
    (normalizers : TypeReadQueryRows.Normalizers firstNormalize secondNormalize)
    (firstSubtypes secondSubtypes : List Atom → List Atom) (depth : Nat)
    (world : Coordinates) (call : Call) (first second : Supply)
    (fixed : Fixed world (questionNames (.inr call))) (supplies : Protected world first second)
    (types : List Atom)
    (returned : (NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external firstNormalize firstSubtypes)
      source external depth call first).1 = some (.types types))
    (retained : RetainedTypePayloads.admittedList types = true) :
    (NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external secondNormalize secondSubtypes)
      source external depth call second).1 = some (.types types) := by
  obtain ⟨after, _, _, related⟩ := evaluate_coordinates source external sourceSafe alpha
    firstNormalize secondNormalize normalizers firstSubtypes secondSubtypes depth world call first second fixed supplies
  rw [returned] at related
  cases reply : (NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external secondNormalize secondSubtypes)
      source external depth call second).1 with
  | none => simp only [reply, Option.not_rel_some_none] at related
  | some value =>
      simp only [reply, Option.rel_some_some] at related
      cases related with
      | types typesRelated => rw [retained_types_equal typesRelated retained]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryRecursive
