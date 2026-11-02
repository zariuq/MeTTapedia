import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedContextLogicalClosure
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeGuardedRealizabilityControls
import Mettapedia.Logic.HOL.FiniteConstructorEncodingControls

/-!
# Empty and inhabited input fibres for logical witness closure

A source type parameter is represented by a predicate on propositions.
An actual source variable constructs the existential result. Hiding that
variable produces a conditional rule, while an independent empty-predicate
valuation refutes deleting the existential premise. No source or target
carrier is replaced by an empty type.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.GuardedLogicalClosureControls

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open HOL
open FiniteConstructorEncoding.Controls (Constants model)

def profile := NativeGuardedRealizability.Controls.profile
def theory := NativeNaturalVectorFamilies.Programs.Annotated.church profile
def universeHead := NativeGuardedRealizability.Controls.universeHead
def nextHead := NativeGuardedRealizability.Controls.nextHead
abbrev predicates : Ty Empty := .prop ⇒ .prop

def fullCode : ClosedTerm Constants (predicates ⇒ .prop) := PredicateProducts.full predicates
def lex : LexicalReading Tower.Head Empty Constants where
  constCode? _ := none
  headCode? head := if head = universeHead then some ⟨predicates ⇒ .prop, fullCode⟩ else none

def base : GuardedContext theory lex [predicates] where
  source := .snoc .nil (.head universeHead)
  telescope := .snoc .nil fullCode
  formed := .snoc .nil ⟨nextHead, by decide +kernel, .headType (by decide +kernel)⟩
  reading := .snoc .nil (.head (by simp [lex, fullCode]))

def domain : CTm Tower.Head 1 := .var 0
def predicate : Term Constants [predicates] predicates := .var .vz
theorem domain_read : Reads (Γ := [predicates]) lex domain predicate :=
  Reads.var (lex := lex) (Γ := [predicates]) (.vz : Var [predicates] predicates)
theorem domain_formed : CIsType theory base.source domain := ⟨universeHead, by decide +kernel, .var 0⟩
def valueContext := base.snoc predicate domain_read domain_formed
def value := GuardedRealizer.ofVariable [] valueContext (.vz : Var [.prop, predicates] .prop)

def goal : Formula Constants [predicates] := .ex (.app (weaken predicate) (.var .vz))
def continuation : ProofSyntax Constants (valueContext.hypotheses []) (weaken goal) := value.witness
theorem continuation_free : continuation.FunctionExtensionalityFree :=
  GuardedRealizer.witness_free value (GuardedRealizer.ofVariable_free [] valueContext .vz)

def conditional : ProofSyntax Constants (base.hypotheses []) (.imp goal goal) :=
  base.closeWitness predicate domain_read domain_formed goal continuation
theorem conditional_free : conditional.FunctionExtensionalityFree :=
  base.closeWitness_free predicate domain_read domain_formed goal continuation continuation_free

def emptyWorld : model.Valuation [predicates]
  | _, .vz => fun _ => ⟨False⟩
def inhabitedWorld : model.Valuation [predicates]
  | _, .vz => fun proposition => proposition

theorem emptyWorld_has_base_guards : Soundness.SatisfiesHyps model emptyWorld (base.hypotheses []) := by
  intro formula member
  simp only [GuardedContext.hypotheses, base, assumptions, List.map_nil, List.nil_append,
    PredicateContexts.Telescope.hypotheses, weakenHyps, List.mem_singleton] at member
  subst formula
  trivial

theorem inhabited_result : (model.denote goal inhabitedWorld).down := by
  change ∃ proposition : ULift.{1} Prop, True ∧ proposition.down
  exact ⟨⟨True⟩, True.intro, True.intro⟩

theorem empty_result : ¬ (model.denote goal emptyWorld).down := by
  change ¬ ∃ _proposition : ULift.{1} Prop, True ∧ False
  rintro ⟨_, _, impossible⟩
  exact impossible

theorem dropping_existential_premise_refused : ¬ Nonempty (ProofSyntax Constants (base.hypotheses []) goal) := by
  rintro ⟨proof⟩
  have result := Soundness.extDerivation_sound proof.erase (M := model) (ρ := @emptyWorld)
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ _; trivial) emptyWorld_has_base_guards
  exact empty_result result

#print axioms conditional_free
#print axioms dropping_existential_premise_refused

end Mettapedia.GSLT.LanguageDef.GuardedLogicalClosureControls
