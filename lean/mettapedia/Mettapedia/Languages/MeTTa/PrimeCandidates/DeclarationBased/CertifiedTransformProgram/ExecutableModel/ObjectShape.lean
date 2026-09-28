import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectRules

/-!
# The root shape of the object package

The object package, the executable package with the program's codes, reduces
by the root computations of the executable package and by the decoding of
codes. Its roles are those of the executable package, except that the decoder
`holds` computes at arity one on its code, and implication, the quantifiers
`all@A` and the equations `eq@A` are constructors.

No name that is not rigid in the executable package is a code, so its root
steps keep their shape under these roles, and the decoding steps have theirs
by the laws of the decoder. A decoding redex is headed by `holds`, which is
rigid in the executable package, so no term is a redex of both. Hence the
object package has root shape, and the numbers keep their declared
constructors.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
namespace ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName)

namespace CodeModel

/-! ## The names that are not rigid in the executable package -/

/-- The names that are not rigid in the executable package: the numbers, their
constructors, and the constants with computation. -/
def nonrigidNames : List DeclName :=
  [numN, zeroN, sucN, numRecName, addN, powN, jName, eqAtName, sucMoveName, keepName,
    transportName, composeName, iterName, returnIterName, sucStepName]

/-- Every other name is rigid in the executable package. -/
theorem roles_of_not_mem {name : DeclName} (h : name ∉ nonrigidNames) : roles name = .rigid := by
  simp only [nonrigidNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅⟩ := h
  rw [roles.eq_1, if_neg h₁, behaviour.eq_1, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅,
    if_neg h₆, if_neg h₇, if_neg h₈, if_neg h₉, if_neg h₁₀, if_neg h₁₁, if_neg h₁₂, if_neg h₁₃,
    if_neg h₁₄, if_neg h₁₅]
  rfl

/-- None of them is a code. -/
theorem nonrigidNames_not_codes : ∀ name ∈ nonrigidNames, name ≠ holdsN ∧ name ≠ impN ∧
    SetProfile.allInstance? name = none ∧ SetProfile.eqInstance? name = none := by
  decide

/-! ## Roles -/

/-- The roles of the object package: the decoder computes at arity one with the
code as its scrutinee, implication and every quantifier and equation instance
are constructors, and every other name has its role in the executable
package. -/
def objectRoles : Roles Tower.Head := fun name =>
  if name = holdsN then .computes 1 (.split 0 .constructor fun _ => .leaf)
  else if name = impN then .constructor 2
  else if (SetProfile.allInstance? name).isSome then .constructor 1
  else if (SetProfile.eqInstance? name).isSome then .constructor 2
  else roles name

theorem objectRoles_of {name : DeclName} (hh : name ≠ holdsN) (hi : name ≠ impN)
    (ha : SetProfile.allInstance? name = none) (he : SetProfile.eqInstance? name = none) :
    objectRoles name = roles name := by
  simp only [objectRoles, if_neg hh, if_neg hi, ha, he, Option.isSome_none,
    Bool.false_eq_true, if_false]

theorem objectRoles_holds : objectRoles holdsN = .computes 1 (.split 0 .constructor fun _ => .leaf) :=
  if_pos rfl

theorem objectRoles_imp : objectRoles impN = .constructor 2 := by
  simp only [objectRoles, if_neg (show impN ≠ holdsN by decide), if_true]

theorem objectRoles_all {name : DeclName} {type : HOL.Ty SetProfile.SetBase}
    (found : SetProfile.allInstance? name = some type) : objectRoles name = .constructor 1 := by
  have hh : name ≠ holdsN := fun h => by
    rw [h, SetProfile.allInstance?_holdsName] at found; cases found
  have hi : name ≠ impN := fun h => by
    rw [h, SetProfile.allInstance?_impName] at found; cases found
  simp only [objectRoles, if_neg hh, if_neg hi, found, Option.isSome_some, if_true]

theorem objectRoles_eq {name : DeclName} {type : HOL.Ty SetProfile.SetBase}
    (found : SetProfile.eqInstance? name = some type) : objectRoles name = .constructor 2 := by
  have hh : name ≠ holdsN := fun h => by
    rw [h, SetProfile.eqInstance?_holdsName] at found; cases found
  have hi : name ≠ impN := fun h => by
    rw [h, SetProfile.eqInstance?_impName] at found; cases found
  have ha : SetProfile.allInstance? name = none := by
    rw [SetProfile.eqInstance?_eq_some found, SetProfile.allInstance?_eqName]
  simp only [objectRoles, if_neg hh, if_neg hi, ha, found, Option.isSome_none,
    Option.isSome_some, Bool.false_eq_true, if_false, if_true]

/-- A name that is not rigid in the package keeps its role. -/
theorem objectRoles_of_roles {name : DeclName} {role : Role Tower.Head}
    (declared : roles name = role) (nonrigid : role ≠ .rigid) : objectRoles name = role := by
  by_cases mem : name ∈ nonrigidNames
  · obtain ⟨hh, hi, ha, he⟩ := nonrigidNames_not_codes name mem
    exact (objectRoles_of hh hi ha he).trans declared
  · exact absurd (declared.symm.trans (roles_of_not_mem mem)) nonrigid

theorem objectRoles_num : objectRoles numN = .inductive ctors :=
  objectRoles_of_roles roles_num nofun

theorem objectRoles_zero : objectRoles zeroN = .constructor 0 :=
  objectRoles_of_roles roles_zero nofun

theorem objectRoles_suc : objectRoles sucN = .constructor 1 :=
  objectRoles_of_roles roles_suc nofun

/-- The only inductive type of the object package is the numbers. -/
theorem objectRoles_inductive {T : DeclName} {cs : List (DeclName × List CtorField)}
    (role : objectRoles T = .inductive cs) : T = numN ∧ cs = ctors := by
  by_cases hh : T = holdsN
  · subst hh; rw [objectRoles_holds] at role; cases role
  by_cases hi : T = impN
  · subst hi; rw [objectRoles_imp] at role; cases role
  cases ha : SetProfile.allInstance? T with
  | some _ => rw [objectRoles_all ha] at role; cases role
  | none =>
      cases he : SetProfile.eqInstance? T with
      | some _ => rw [objectRoles_eq he] at role; cases role
      | none =>
          rw [objectRoles_of hh hi ha he] at role
          exact roles_inductive role

/-- The numbers keep their constructors `zero` and `suc`. -/
theorem objectConstructorsDeclared : ConstructorsDeclared objectRoles where
  arity := by
    intro T cs k fields role mem
    obtain ⟨rfl, rfl⟩ := objectRoles_inductive role
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact objectRoles_zero
    · exact objectRoles_suc
  distinct := by
    intro T cs role
    obtain ⟨rfl, rfl⟩ := objectRoles_inductive role
    decide

/-- The code constants have the roles their decoding needs. -/
theorem objectDecoderRoles : DecoderRoles objectRoles programCodes.decoders where
  holds := objectRoles_holds
  imp := objectRoles_imp
  all := by
    intro a A carrier
    change (SetProfile.allInstance? a).map typeTerm = some A at carrier
    cases found : SetProfile.allInstance? a with
    | none => rw [found] at carrier; cases carrier
    | some _ => exact objectRoles_all found
  eq := by
    intro e A carrier
    change (SetProfile.eqInstance? e).map typeTerm = some A at carrier
    cases found : SetProfile.eqInstance? e with
    | none => rw [found] at carrier; cases carrier
    | some _ => exact objectRoles_eq found

/-! ## Root shape -/

/-- A canonical form of the executable package is canonical under the roles of
the object package. -/
theorem canonical_objectRoles {n : Nat} {a : Tower.Tm n} (canonical : Canonical roles a) :
    Canonical objectRoles a := by
  rcases canonical with refl | ⟨k, arity, args, role, rfl⟩
  · exact .inl refl
  · exact .inr ⟨k, arity, args, objectRoles_of_roles role nofun, rfl⟩

/-- The root steps of the executable package are spine-shaped under the roles of
the object package. -/
theorem rules_spine_objectRoles : SpineShaped objectRoles rules.computation := by
  intro n t u step
  obtain ⟨c, arity, scrutinee, args, role, rfl, length, accepts⟩ := shape.spine step
  exact ⟨c, arity, scrutinee, args, objectRoles_of_roles role nofun, rfl, length,
    accepts.of_constructors (fun constructor => objectRoles_of_roles constructor nofun)
      (roles_onlyConstructors role)⟩

/-- Implication is not an equation instance. -/
theorem programCodes_impNotEquation :
    programCodes.decoders.eqCarrier programCodes.decoders.imp = none := by
  change (SetProfile.eqInstance? impN).map typeTerm = none
  rw [SetProfile.eqInstance?_impName]
  rfl

/-- No term is both a root redex of the executable package and a decoding redex:
decoding redexes are headed by `holds`, which is rigid in the executable
package. -/
theorem rules_not_decoding {n : Nat} {t u u' : Tower.Tm n} (step : rules.computation.step t u)
    (decoding : DecoderStep programCodes.decoders t u') : False := by
  obtain ⟨c, arity, scrutinee, args, role, rfl, -⟩ := shape.spine step
  obtain ⟨args', same⟩ := decoderComputation_headed programCodes.decoders decoding
  obtain ⟨rfl, -⟩ := appSpine_const_injective same
  have rigid : roles holdsN = .rigid := roles_of_not_mem (by decide)
  exact nomatch rigid.symm.trans role

/-- **Root shape.** The object package has root shape under its roles. -/
theorem objectShape : RootShape objectRules objectRoles where
  spine := by
    intro n t u step
    rcases step with step | step
    · exact rules_spine_objectRoles step
    · exact decoderComputation_spine objectDecoderRoles step
  deterministic := by
    intro n t u u' step step'
    rcases step with step | step <;> rcases step' with step' | step'
    · exact shape.deterministic step step'
    · exact (rules_not_decoding step step').elim
    · exact (rules_not_decoding step' step).elim
    · exact decoderComputation_deterministic programCodes_impNotEquation step' step

end CodeModel

end ExecutableModel
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
