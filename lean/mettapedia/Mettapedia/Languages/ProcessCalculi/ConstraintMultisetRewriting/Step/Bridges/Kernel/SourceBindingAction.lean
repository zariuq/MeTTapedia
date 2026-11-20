import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.SourceSignatureAction

/-!
# Name actions through actual binder erasure and canonical typing

Typed variables retain both their name and type. The nearest-binder lookup
commutes with a bijective action, so canonicalization neither captures a
formerly free variable nor changes a bound index. The resulting canonical
term action uses the existing de Bruijn type checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceBindingAction

open Mettapedia.Languages.OpenTheory
open SourceNameAction SourceSignatureAction

def mapVariable (names : Names) (entry : SourceVar) : SourceVar :=
  ⟨names.variables entry.name, mapType names entry.ty⟩

theorem variable_roundtrip (names : Names) (entry : SourceVar) :
    mapVariable names.symm (mapVariable names entry) = entry := by
  cases entry
  simp [mapVariable, type_roundtrip]

theorem variable_injective (names : Names) : Function.Injective (mapVariable names) :=
  Function.LeftInverse.injective (variable_roundtrip names)

theorem variable_comparison (names : Names) (first second : SourceVar) :
    sourceVarSame (mapVariable names first) (mapVariable names second) = sourceVarSame first second := by
  apply Bool.eq_iff_iff.mpr
  simp only [sourceVarSame_eq_true_iff, (variable_injective names).eq_iff]

theorem binder_index (names : Names) (entry : SourceVar) (binders : List SourceVar) :
    boundIndex (mapVariable names entry) (binders.map (mapVariable names)) =
      boundIndex entry binders := by
  induction binders with
  | nil => rfl
  | cons binder rest ih =>
      simp only [List.map_cons, boundIndex, variable_comparison, ih]

def mapDB (names : Names) : DBTerm → DBTerm
  | .const constant annotation => .const (mapConstant names constant) (mapType names annotation)
  | .free entry => .free (mapVariable names entry)
  | .bound index => .bound index
  | .app function argument => .app (mapDB names function) (mapDB names argument)
  | .abs domain body => .abs (mapType names domain) (mapDB names body)

theorem db_roundtrip (names : Names) (term : DBTerm) :
    mapDB names.symm (mapDB names term) = term := by
  induction term <;> simp_all [mapDB, constant_roundtrip, type_roundtrip, variable_roundtrip]

theorem db_injective (names : Names) : Function.Injective (mapDB names) :=
  Function.LeftInverse.injective (db_roundtrip names)

theorem canonicalization (names : Names) (binders : List SourceVar) (term : SourceTerm) :
    (mapTerm names term).toDB (binders.map (mapVariable names)) = mapDB names (term.toDB binders) := by
  cases term with
  | const constant annotation => simp only [mapTerm, SourceTerm.toDB, mapDB]
  | var name annotation =>
      have index := binder_index names (⟨name,annotation⟩ : SourceVar) binders
      simp only [mapVariable] at index
      simp only [mapTerm, SourceTerm.toDB, index]
      cases boundIndex ⟨name,annotation⟩ binders <;> rfl
  | app function argument =>
      simp only [mapTerm, SourceTerm.toDB, mapDB,
        canonicalization names binders function, canonicalization names binders argument]
  | abs name annotation body =>
      simp only [mapTerm, SourceTerm.toDB, mapDB]
      have inside := canonicalization names (⟨name,annotation⟩ :: binders) body
      simpa only [List.map_cons, mapVariable] using congrArg (DBTerm.abs (mapType names annotation)) inside
termination_by sizeOf term

theorem db_inference (names : Names) (fixed : FunctionFixed names) (context : List Ty) (term : DBTerm) :
    (mapDB names term).inferType (context.map (mapType names)) =
      (term.inferType context).map (mapType names) := by
  induction term generalizing context with
  | const constant annotation => simp only [mapDB, DBTerm.inferType, Option.map_some]
  | free entry => simp only [mapDB, mapVariable, DBTerm.inferType, Option.map_some]
  | bound index => simp only [mapDB, DBTerm.inferType, List.getElem?_map]
  | abs domain body ih =>
      simp only [mapDB, DBTerm.inferType]
      rw [show mapType names domain :: context.map (mapType names) =
        (domain :: context).map (mapType names) from rfl, ih]
      cases body.inferType (domain :: context) <;> simp [function_type names fixed]
  | app function argument ihFunction ihArgument =>
      simp only [mapDB, DBTerm.inferType, ihFunction, ihArgument]
      cases function.inferType context with
      | none => rfl
      | some functionType =>
          cases argument.inferType context with
          | none => rfl
          | some argumentType =>
              simp only [Option.map_some, bind, Option.bind, function_view names fixed]
              cases functionType.destFunction? with
              | none => rfl
              | some pair =>
                  simp only [Option.map_some, type_comparison]
                  cases Ty.same pair.1 argumentType <;> rfl

def mapCanonical (names : Names) (fixed : FunctionFixed names) (term : CanonicalTerm) : CanonicalTerm :=
  ⟨mapDB names term.term, mapType names term.ty, by
    simpa only [List.map_nil, term.checked, Option.map_some] using db_inference names fixed [] term.term⟩

theorem canonical_injective (names : Names) (fixed : FunctionFixed names) :
    Function.Injective (mapCanonical names fixed) := by
  intro first second same
  apply CanonicalTerm.ext_term
  exact db_injective names (congrArg CanonicalTerm.term same)

theorem canonical_image (names : Names) (fixed : FunctionFixed names) (checked : CheckedSourceTerm) :
    mapCanonical names fixed checked.canonical =
      (⟨mapTerm names checked.source, mapType names checked.ty, by
        rw [inference names fixed, checked.checked]
        rfl⟩ : CheckedSourceTerm).canonical := by
  apply CanonicalTerm.ext_term
  exact (canonicalization names [] checked.source).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceBindingAction
