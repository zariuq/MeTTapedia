import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLBodySyntax

/-! # Types of the general preparation and admission parameters -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionTypes

open Mettapedia.Logic Mettapedia.Languages.OpenTheory

abbrev stateType : HOL.Ty AtomicTy := (Ty.var (Name.global "S")).toHOL
abbrev firingType : HOL.Ty AtomicTy := (Ty.var (Name.global "F")).toHOL
abbrev witnessType : HOL.Ty AtomicTy := (Ty.var (Name.global "P")).toHOL
abbrev solutionType : HOL.Ty AtomicTy := (Ty.var (Name.global "V")).toHOL
abbrev preparationType : HOL.Ty AtomicTy := .arr stateType (.arr firingType (.arr witnessType .prop))
abbrev resultType : HOL.Ty AtomicTy := .arr stateType (.arr firingType (.arr witnessType stateType))
abbrev readyType : HOL.Ty AtomicTy := .arr stateType (.arr firingType .prop)
abbrev solutionsType : HOL.Ty AtomicTy := .arr stateType (.arr firingType (.arr solutionType .prop))
abbrev holdsType : HOL.Ty AtomicTy := .arr stateType (.arr firingType (.arr witnessType (.arr solutionType .prop)))
abbrev preparedEventType : HOL.Ty AtomicTy := .arr preparationType (.arr resultType
  (.arr stateType (.arr firingType (.arr witnessType (.arr stateType .prop)))))
abbrev admittedEventType : HOL.Ty AtomicTy := .arr preparationType (.arr resultType (.arr preparationType
  (.arr stateType (.arr firingType (.arr witnessType (.arr stateType .prop))))))
abbrev solutionPreparationType : HOL.Ty AtomicTy := .arr readyType (.arr solutionsType (.arr preparationType preparationType))
abbrev guardProfileType : HOL.Ty AtomicTy := .arr solutionsType (.arr holdsType preparationType)
abbrev inclusionType : HOL.Ty AtomicTy := .arr preparationType (.arr preparationType (.arr preparationType .prop))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionTypes
