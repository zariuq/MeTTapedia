import Mettapedia.Languages.MeTTa.HE.HumanTypeConformance
import Mettapedia.Languages.MeTTa.HE.HumanTypeRuntimeRefinement
import MettaHyperonFull.Minimal.Interpreter
import Std.Data.HashMap.Lemmas

/-!
# LeaTTa type-lookup refinement boundary

The published evaluator pseudocode requests the types of an atom from the
space but does not state an application-result inference rule.  The human type
relation therefore exposes only direct annotations, intrinsic grounded types,
and the gradual `%Undefined%` fallback.

LeaTTa, following Hyperon's runtime type service, additionally infers the
return type of a well-typed application.  The theorem below pins one strict
extension witness.  It is deliberately downstream of the human semantics so
the extra executable behavior cannot be absorbed silently into the target
relation.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypeRefinement

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanTypeSpec
open HumanTypeConformance
open HumanTypeRuntimeRefinement
open HumanMatchMergeSpec

private def applicationSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "f",
      .expression [.symbol "->", .symbol "A", .symbol "B"]],
    .expression [.symbol ":", .symbol "a", .symbol "A"]]

private def applicationAtom : Atom :=
  .expression [.symbol "f", .symbol "a"]

private def applicationEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "f", .expr [.sym "->", .sym "A", .sym "B"]],
    .expr [.sym ":", .sym "a", .sym "A"]] []

private def applicationLeaAtom : Metta.Atom :=
  .expr [.sym "f", .sym "a"]

/-- The published direct-lookup relation assigns `%Undefined%` when the
application itself has no annotation. -/
theorem published_application_type_undefined :
    TypesOfRel applicationSpace applicationAtom [Atom.undefinedType] := by
  apply TypesOfRel.expressionUndefined
  exact AnnotationTypesRel.skip (by simp)
    (AnnotationTypesRel.skip (by simp)
      AnnotationTypesRel.nil)

/-- Negative half of the boundary: application return inference is not a
derivation of the published direct-lookup relation. -/
theorem published_application_not_inferred_B :
    ¬TypeOfRel applicationSpace applicationAtom (.symbol "B") := by
  rintro ⟨types, htypes, hmem⟩
  have hlookup := typesOfRel_eq_getAtomTypes htypes
  have hcanonical :=
    typesOfRel_eq_getAtomTypes published_application_type_undefined
  rw [hcanonical] at hlookup
  have htypesEq : types = [Atom.undefinedType] := hlookup.symm
  subst types
  simp [Atom.undefinedType] at hmem

/-- LeaTTa's runtime type service infers the declared arrow's return type. -/
theorem leatta_application_type_inferred_B :
    Metta.Minimal.getTypes applicationEnv applicationLeaAtom =
      [.sym "B"] := by
  simp [applicationEnv, applicationLeaAtom, Metta.Minimal.getTypes,
    Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
    Std.HashMap.getD_emptyWithCapacity, Metta.matchAtoms,
    Metta.matchAtomsWith, Metta.Bindings.merge, Metta.instantiate]

/-- Strict-refinement canary: the same application is `%Undefined%` in the
published direct-lookup relation and has inferred type `B` in LeaTTa. -/
theorem application_type_inference_strictly_extends_published_lookup :
    TypesOfRel applicationSpace applicationAtom [Atom.undefinedType] ∧
      ¬TypeOfRel applicationSpace applicationAtom (.symbol "B") ∧
      R1ApplicationResultRel applicationSpace applicationAtom (.symbol "B") ∧
      Metta.Minimal.getTypes applicationEnv applicationLeaAtom = [.sym "B"] :=
  ⟨published_application_type_undefined,
    published_application_not_inferred_B,
    r1_f_a_infers_B,
    leatta_application_type_inferred_B⟩

/-! ## Nested gradual-type refinement -/

/-- The published `match_types` pseudocode treats `%Undefined%` specially only
at the top level.  Its ordinary structural matcher therefore cannot match a
nested `%Undefined%` against `Number`. -/
theorem published_nested_undefined_not_typeMatch (output : Bindings) :
    ¬TypeMatchRel
      (.expression [.symbol "List", .symbol "%Undefined%"])
      (.expression [.symbol "List", .symbol "Number"])
      Bindings.empty output := by
  intro htype
  obtain ⟨_, hmatch, _⟩ :=
    htype.structural_of_nonWildcard
      (by decide) (by decide) (by decide) (by decide)
  cases hmatch with
  | expression hitems _ =>
      cases hitems with
      | cons _ _ htail =>
          cases htail with
          | cons hbad _ _ =>
              exact symbol_mismatch_not_match
                (p := equalityGroundedSemantic)
                (left := "%Undefined%") (right := "Number")
                (by decide) _ hbad

/-- LeaTTa follows Hyperon's richer runtime behavior: nested `%Undefined%` is
a gradual wildcard during reduced-type matching. -/
theorem leatta_nested_undefined_typeMatch :
    Metta.Minimal.matchType []
      (.expr [.sym "List", .sym "%Undefined%"])
      (.expr [.sym "List", .sym "Number"]) = some [] := by
  rfl

/-- Strict-refinement canary for nested gradual types. -/
theorem nested_undefined_strictly_extends_published_typeMatch :
    (∀ output,
      ¬TypeMatchRel
        (.expression [.symbol "List", .symbol "%Undefined%"])
        (.expression [.symbol "List", .symbol "Number"])
        Bindings.empty output) ∧
      R2ReducedTypeMatchRel
        (.expression [.symbol "List", .symbol "%Undefined%"])
        (.expression [.symbol "List", .symbol "Number"])
        Bindings.empty Bindings.empty ∧
      Metta.Minimal.matchType []
        (.expr [.sym "List", .sym "%Undefined%"])
        (.expr [.sym "List", .sym "Number"]) = some [] :=
  ⟨published_nested_undefined_not_typeMatch,
    r2_nested_undefined_number,
    leatta_nested_undefined_typeMatch⟩

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypeRefinement
