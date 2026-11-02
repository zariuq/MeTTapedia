import Mettapedia.Logic.HOL.FiniteConstructorProgramReadout
import Mettapedia.Logic.HOL.FiniteConstructorGuardElimination
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.IndexedPredicateInduction

/-!
# Controls for retained constructor readout and guard elimination

Different nullary occurrences remain distinct. Program readout retains both
original fields. An existential telescope is eliminated using fresh field
variables, and the indexed-motive consumer keeps its supplied target index.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RetainedConstructorProofControls
open FiniteConstructorEncoding CurriedPredicates

inductive Symbol : Ty Unit → Type

namespace Payload
abbrev context : Ctx Unit := [.prop, .prop, .prop, .prop]
def signature : List (List (Ty Unit)) := [[.prop, .prop], [.prop, .prop]]
def first : Fin signature.length := ⟨0, by decide⟩
def second : Fin signature.length := ⟨1, by decide⟩
def firstArguments : Arguments Symbol context (signature.get first) :=
  (.var .vz, .var (.vs .vz), PUnit.unit)
def secondArguments : Arguments Symbol context (signature.get first) :=
  (.var (.vs (.vs .vz)), .var (.vs (.vs (.vs .vz))), PUnit.unit)

def programs (occurrence : Fin signature.length) : Term Symbol context (FunctionType (signature.get occurrence) .prop) := by
  rcases occurrence with ⟨index, bound⟩
  cases index with
  | zero => exact .lam (.lam (.and (.var (.vs .vz)) (.var .vz)))
  | succ index =>
    cases index with
    | zero => exact .lam (.lam (.or (.var (.vs .vz)) (.var .vz)))
    | succ index => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 index) bound)

def samePayload : Formula Symbol context := .eq
  (encode signature first firstArguments) (encode signature first secondArguments)

def programReadout : ProofSyntax Symbol [samePayload] (.eq
    (applyFields (signature.get first) (programs first) firstArguments)
    (applyFields (signature.get first) (programs first) secondArguments)) :=
  program_equal_of_payload signature programs first first firstArguments secondArguments (.hyp 0)

theorem programReadout_free : programReadout.FunctionExtensionalityFree :=
  program_equal_of_payload_free signature programs first first firstArguments secondArguments
    (show ProofSyntax Symbol [samePayload] samePayload from .hyp 0) True.intro

def nullaryEquality : ClosedFormula Symbol := .eq
    (encode [[], []] ⟨0, by decide⟩ PUnit.unit)
    (encode [[], []] ⟨1, by decide⟩ PUnit.unit)

def nullaryPremise : ProofSyntax Symbol [nullaryEquality] nullaryEquality := .hyp ⟨0, by decide⟩

theorem nullaryPremise_free : nullaryPremise.FunctionExtensionalityFree := by
  simp only [nullaryPremise, ProofSyntax.FunctionExtensionalityFree]

def nullarySeparation : ProofSyntax Symbol ([] : List (ClosedFormula Symbol)) (.not nullaryEquality) :=
  .notI (separate_occurrences [[], []] ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
    PUnit.unit PUnit.unit nullaryPremise)

theorem nullarySeparation_free : nullarySeparation.FunctionExtensionalityFree :=
  separate_occurrences_free (Base := Unit) (Const := Symbol) (Γ := [])
    (assumptions := [nullaryEquality]) [[], []] ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
    PUnit.unit PUnit.unit nullaryPremise nullaryPremise_free
end Payload

namespace Telescope
def fields : List (Ty Unit) := [.prop, .prop]
def predicate : ClosedTerm Symbol (handlerType fields) :=
  .lam (.lam (.and (.var (.vs .vz)) (.var .vz)))
def target : ClosedFormula Symbol := .ex (.var .vz)

def branches : ProofSyntax Symbol [] (argumentBranches fields predicate target) := by
  refine .allI (.allI (.impI ?_))
  have beta : ProofSyntax Symbol [applyArguments fields (weaken (weaken predicate))
      ((.var (.vs .vz) : Term Symbol [.prop, .prop] .prop), .var .vz, PUnit.unit)]
      (.eq (applyArguments fields (weaken (weaken predicate)) (.var (.vs .vz), .var .vz, PUnit.unit))
        (.and (.var (.vs .vz)) (.var .vz))) := by
    apply ProofSyntax.castIndices rfl ?_
      (CurriedGuardProgramProofs.beta2 (.and (.var (.vs .vz)) (.var .vz))
        (.var (.vs .vz)) (.var .vz))
    rfl
  exact .exI (.var (.vs .vz)) (.andEL (.impE (.eqPropEL beta) (.hyp 0)))

def present : ProofSyntax Symbol [] (existsArguments fields predicate) := by
  apply existsArguments_intro fields predicate (.top, .top, PUnit.unit)
  apply ProofSyntax.impE (.eqPropER (CurriedGuardProgramProofs.beta2
    (.and (.var (.vs .vz)) (.var .vz)) .top .top))
  exact .andI .topI .topI

def eliminated : ProofSyntax Symbol [] target := existsArguments_elim fields predicate target present branches

theorem branches_free : branches.FunctionExtensionalityFree := by
  simp [branches, ProofSyntax.FunctionExtensionalityFree, CurriedGuardProgramProofs.beta2_free]

theorem present_free : present.FunctionExtensionalityFree := by
  unfold present
  apply existsArguments_intro_free
  exact ⟨CurriedGuardProgramProofs.beta2_free _ _ _, True.intro, True.intro⟩

theorem eliminated_free : eliminated.FunctionExtensionalityFree :=
  existsArguments_elim_free fields predicate target present branches present_free branches_free
end Telescope

namespace Indexed
abbrev context : Ctx Unit := [.prop, .prop, .prop ⇒ .prop ⇒ .prop, .prop ⇒ .prop ⇒ .prop]
def point : Term Symbol context .prop := .var .vz
def target : Term Symbol context .prop := .var (.vs .vz)
def root : Term Symbol context (.prop ⇒ .prop ⇒ .prop) := .var (.vs (.vs .vz))
def property : Term Symbol context (.prop ⇒ .prop ⇒ .prop) := .var (.vs (.vs (.vs .vz)))
def assumptions : List (Formula Symbol context) :=
  [.app (IndexedPredicateInduction.lift root property) point, .app (.app root point) target]

def liftedPremise : ProofSyntax Symbol assumptions (.app (IndexedPredicateInduction.lift root property) point) :=
  .hyp ⟨0, by decide⟩
def rootPremise : ProofSyntax Symbol assumptions (.app (.app root point) target) :=
  .hyp ⟨1, by decide⟩

def atTarget : ProofSyntax Symbol assumptions (.app (.app property point) target) :=
  IndexedPredicateInduction.eliminate root property point target liftedPremise rootPremise

theorem atTarget_free : atTarget.FunctionExtensionalityFree :=
  IndexedPredicateInduction.eliminate_free root property point target liftedPremise rootPremise True.intro True.intro
end Indexed

#print axioms Payload.programReadout_free
#print axioms Payload.nullarySeparation
#print axioms Telescope.eliminated
#print axioms Indexed.atTarget_free

end Mettapedia.Logic.HOL.RetainedConstructorProofControls
