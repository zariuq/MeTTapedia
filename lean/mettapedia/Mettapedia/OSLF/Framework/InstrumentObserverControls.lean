import Mettapedia.OSLF.Framework.InstrumentRuntime
import Mettapedia.CategoryTheory.FiniteActionTreeAssays

/-!
# Nonconstant instrument, equation, runtime and future-assay controls
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentObserverControls

open InstrumentObservations InstrumentRuntime
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open ObserverExtension ObserverReconstruction
open Mettapedia.CategoryTheory

inductive Symbol where
  | c | d | e | hidden
  deriving DecidableEq

def arity : Symbol → Nat
  | .c | .d => 0
  | .e | .hidden => 1

abbrev Term := Tree Symbol arity

def c : Term := .node .c Fin.elim0
def d : Term := .node .d Fin.elim0
def e (body : Term) : Term := .node .e (fun _ => body)
def hidden (body : Term) : Term := .node .hidden (fun _ => body)
def kit : List Symbol := [.c, .e]
def larger : List Symbol := [.c, .e, .hidden]
def all : List Symbol := [.c, .d, .e, .hidden]

def firstReadout : View Symbol arity → View Symbol arity
  | .visible .e arguments | .visible .hidden arguments => arguments (0 : Fin 1)
  | _ => .opaque

theorem opaque_descendants_agree :
    Bisimilar (fun constructor => constructor ∈ kit)
      (.term (e (hidden c))) (.term (e (hidden d))) := by
  apply (term_bisimilar_iff_view _ _ _).2
  simp [e, hidden, kit, view]

theorem opening_ancestor_separates :
    ¬ Bisimilar (fun constructor => constructor ∈ larger)
      (.term (e (hidden c))) (.term (e (hidden d))) := by
  intro related
  have same := (term_bisimilar_iff_view _ _ _).1 related
  have exposed := congrArg (fun reading => firstReadout (firstReadout reading)) same
  simp [e, hidden, c, d, larger, view, firstReadout] at exposed

theorem kit_is_smaller : ∀ constructor, constructor ∈ kit → constructor ∈ larger := by
  intro constructor member
  simp only [kit, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [larger]

theorem strict_monotonicity_control :
    Bisimilar (fun constructor => constructor ∈ kit)
      (.term (e (hidden c))) (.term (e (hidden d))) ∧
    ¬ Bisimilar (fun constructor => constructor ∈ larger)
      (.term (e (hidden c))) (.term (e (hidden d))) :=
  ⟨opaque_descendants_agree, opening_ancestor_separates⟩

def exposedTest : Formula Symbol arity :=
  .headed .e (fun _ => .headed .hidden (fun _ => .headed .c Fin.elim0))

theorem test_reads_actual_tree : Satisfies exposedTest (e (hidden c)) := by
  refine ⟨_, rfl, fun _ => ⟨_, rfl, fun _ => ⟨_, rfl, fun position => position.elim0⟩⟩⟩

theorem hidden_test_not_admitted :
    ¬ AdmittedFormula (fun constructor => constructor ∈ kit) exposedTest := by
  intro admitted
  cases admitted with
  | headed _ _ _ children =>
    have inside := children (0 : Fin 1)
    cases inside with
    | headed _ _ permission _ => simp [kit] at permission

theorem exposed_test_admitted :
    AdmittedFormula (fun constructor => constructor ∈ larger) exposedTest :=
  .headed Symbol.e _ (by simp [larger]) (fun _ =>
    .headed Symbol.hidden _ (by simp [larger]) (fun _ =>
      .headed Symbol.c _ (by simp [larger]) (fun position => position.elim0)))

theorem actual_partial_test_characterization :
    Bisimilar (fun constructor => constructor ∈ kit) (.term (e c)) (.term (e d)) ↔
      LogicallyEquivalent (fun constructor => constructor ∈ kit) (e c) (e d) :=
  partial_observer_characterization kit (e c) (e d)

theorem complete_control (first second : Term) :
    Bisimilar (fun constructor => constructor ∈ all) (.term first) (.term second) ↔
      first = second :=
  complete_kit_reconstruction _ (by intro constructor; cases constructor <;> simp [all]) _ _

def aliasGenerators (first second : Term) : Prop :=
  first = hidden c ∧ second = hidden d

theorem admitted_alias : LocalEquationAdmission (fun constructor => constructor ∈ kit)
    aliasGenerators := by
  rintro first second ⟨rfl, rfl⟩
  simp [hidden, kit, view]

theorem actual_alias_equation : Equation aliasGenerators (hidden c) (hidden d) :=
  .generator ⟨rfl, rfl⟩

theorem alias_really_changes_syntax : hidden c ≠ hidden d := by
  intro same
  have child := congrFun (eq_of_heq (Tree.node.inj same).2) (0 : Fin 1)
  have distinct := (Tree.node.inj child).1
  cases distinct

theorem alias_calibrates : Bisimilar (fun constructor => constructor ∈ kit)
    (.term (hidden c)) (.term (hidden d)) :=
  equation_calibration _ admitted_alias actual_alias_equation

theorem alias_quotient_readout :
    quotientView (fun constructor => constructor ∈ kit) aliasGenerators admitted_alias
      (Quotient.mk _ (hidden c)) =
    quotientView (fun constructor => constructor ∈ kit) aliasGenerators admitted_alias
      (Quotient.mk _ (hidden d)) :=
  congrArg (quotientView (fun constructor => constructor ∈ kit) aliasGenerators admitted_alias)
    (Quotient.sound actual_alias_equation)

theorem alias_rejected_by_larger_kit :
    ¬ LocalEquationAdmission (fun constructor => constructor ∈ larger) aliasGenerators := by
  intro admission
  have reading := admission _ _ ⟨rfl, rfl⟩
  have exposed := congrArg firstReadout reading
  simp [hidden, c, d, larger, view, firstReadout] at exposed

def declaration : Symbol → GrammarRule
  | .c => Gap.declC
  | .d => Gap.declD
  | .e => Gap.declE
  | .hidden => {
      label := "H"
      category := "T"
      params := [.simple "x" (.base "T")]
      syntaxPattern := [.terminal "H"] }

def language : LanguageDef where
  name := "FourConstructorInstruments"
  types := [.plain "T"]
  terms := [declaration .c, declaration .d, declaration .e, declaration .hidden]
  equations := []
  rewrites := []

def presentation : Presentation Symbol arity where
  language := language
  declaration := declaration
  declared := by intro constructor; cases constructor <;> simp [language]
  arity_eq := by intro constructor; cases constructor <;> rfl
  names_injective := by
    intro first second same
    cases first <;> cases second <;>
      simp_all [declaration, Gap.declC, Gap.declD, Gap.declE]
  projectable := by
    intro constructor position
    cases constructor with
    | c => exact position.elim0
    | d => exact position.elim0
    | e =>
      have index : position.val = 0 := by have bounded := position.isLt; simp [arity] at bounded; omega
      exact ⟨"T", by simp [declaration, Gap.declE, Gap.sortT, projectablePositions, index]⟩
    | hidden =>
      have index : position.val = 0 := by have bounded := position.isLt; simp [arity] at bounded; omega
      exact ⟨"T", by simp [declaration, projectablePositions, index]⟩

def opening (origin : Nat) : Receipt Nat (fun constructor => constructor ∈ kit)
    (.term (e c)) (.ask .e) (.bundle (e c)) :=
  ⟨origin, .ask .e (fun _ => c) (by simp [kit])⟩

def projection (origin : Nat) : Receipt Nat (fun constructor => constructor ∈ kit)
    (.bundle (e c)) (.get .e (0 : Fin 1)) (.term c) :=
  ⟨origin, .get Symbol.e (fun _ => c) (by simp [kit]) (0 : Fin 1)⟩

def building (origin : Nat) : Receipt Nat (fun constructor => constructor ∈ kit)
    (.bundle (e c)) (.build .e) (.term (e c)) :=
  ⟨origin, .build .e (fun _ => c) (by simp [kit])⟩

theorem actual_opening (base : BasePremiseEvaluator) :
    Step base (observerExtension language .hashBag (openedNames presentation kit))
      (.collection .hashBag [.apply (askLabel "E") [], .apply "E" [.apply "C" []]] none)
      (.apply (argsLabel "E") [.apply "C" []]) :=
  (realizeReceipt presentation kit .hashBag (opening 7)).step base

theorem actual_projection (base : BasePremiseEvaluator) :
    Step base (observerExtension language .hashBag (openedNames presentation kit))
      (.apply (getLabel "E" 0) [.apply (argsLabel "E") [.apply "C" []]]) (.apply "C" []) :=
  (realizeReceipt presentation kit .hashBag (projection 8)).step base

theorem actual_building (base : BasePremiseEvaluator) :
    Step base (observerExtension language .hashBag (openedNames presentation kit))
      (.apply (buildLabel "E") [.apply (argsLabel "E") [.apply "C" []]])
      (.apply "E" [.apply "C" []]) :=
  (realizeReceipt presentation kit .hashBag (building 9)).step base

theorem retained_distinct_origins :
    (realizeReceipt presentation kit .hashBag (opening 7)).supplied.origin ≠
      (realizeReceipt presentation kit .hashBag (opening 8)).supplied.origin := by decide

theorem empty_origins_do_not_support :
    ¬ Nonempty (Receipt PEmpty (fun constructor => constructor ∈ kit)
      (.term (e c)) (.ask .e) (.bundle (e c))) := by
  rintro ⟨receipt⟩
  exact receipt.origin.elim

def binderDeclaration : GrammarRule where
  label := "Binder"
  category := "T"
  params := [.abstractionWithBinder "x" "body" (.base "T")]
  syntaxPattern := [.terminal "Binder"]

theorem binder_has_no_projection : projectablePositions binderDeclaration = [] := rfl

def localEvaluator : BasePremiseEvaluator := fun _ _ _ => []

theorem actual_settings (constructor : Symbol) :
    ObserverSetting localEvaluator language .hashBag (openedNames presentation kit)
      (declaration constructor).label where
  fresh := by decide
  confined := evaluatorAvoids_of_barren (fun _ _ _ => rfl) _
  tame := {
    noSteps := by intro rule member; cases member
    clean := by intro rule member; cases member
    rights := by intro rule member; cases member }
  rigid := by intro rule member; cases member
  cited := by intro rule member; cases member
  arities := by
    intro first firstMember second secondMember same
    change first ∈ [declaration .c, declaration .e] at firstMember
    change second ∈ [declaration .c, declaration .e] at secondMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at firstMember secondMember
    rcases firstMember with rfl | rfl <;> rcases secondMember with rfl | rfl <;>
      simp_all [declaration, Gap.declC, Gap.declE]

theorem actual_projection_unique {target : Pattern}
    (stepped : Step localEvaluator
      (observerExtension language .hashBag (openedNames presentation kit))
      (.apply (getLabel "E" 0) [.apply (argsLabel "E") [.apply "C" []]]) target) :
    target = .apply "C" [] :=
  runtime_projection_reflects presentation kit .hashBag localEvaluator .e
    (by simp [kit]) (actual_settings .e) (fun _ => c) (0 : Fin 1) stepped

theorem actual_runtime_tests {relation : Pattern → Pattern → Prop}
    (bisimulation : IsInstrumentBisimulation localEvaluator language .hashBag
      (openedNames presentation kit) relation)
    {first second : Term} (related : relation (lower presentation first) (lower presentation second)) :
    LogicallyEquivalent (fun constructor => constructor ∈ kit) first second :=
  runtime_bisimulation_preserves_tests presentation kit .hashBag localEvaluator relation bisimulation
    (fun constructor _ => actual_settings constructor) related

/-- A fresh request namespace still permits authored synchronization to fire on
the wrong head. Transition existence by itself cannot stand in for the bundle
response and explicit interference conditions used above. -/
theorem fresh_namespace_does_not_prove_interactive_adequacy :
    AdministrativeFresh Interference.absorbing ["C"] ∧
      (∃ target, target ∈ rewriteAt Interference.evaluator Interference.extended 3
        (.collection .hashBag [Interference.askC, Interference.termA] none)) ∧
      ¬ ∃ arguments : List Pattern, Interference.termA = .apply "C" arguments :=
  ⟨Interference.absorbing_fresh, Interference.transition_does_not_determine_head⟩

inductive AssayState where
  | firstRoot | secondRoot | firstLeaf | secondLeaf
  deriving DecidableEq

def successors : AssayState → PUnit → Finset AssayState
  | .firstRoot, _ => {.firstLeaf}
  | .secondRoot, _ => {.secondLeaf}
  | .firstLeaf, _ | .secondLeaf, _ => ∅

def assay : AssayState → Bool
  | .firstLeaf => true
  | _ => false

def rootAndLeafPairs (first second : AssayState) : Prop :=
  (first = .firstRoot ∧ second = .secondRoot) ∨
    (first = .firstLeaf ∧ second = .secondLeaf)

theorem uncoloured_admitted : FiniteActionTreeAssays.Admitted successors successors
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) rootAndLeafPairs := by
  rintro first second (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · refine ⟨rfl, fun _ => ?_⟩
    constructor
    · intro target member
      have shape : target = .firstLeaf := by simpa [successors] using member
      subst target
      exact ⟨.secondLeaf, by simp [successors], Or.inr ⟨rfl, rfl⟩⟩
    · intro target member
      have shape : target = .secondLeaf := by simpa [successors] using member
      subst target
      exact ⟨.firstLeaf, by simp [successors], Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, fun _ => ⟨by simp [successors], by simp [successors]⟩⟩

theorem root_assays_agree : assay .firstRoot = assay .secondRoot := rfl

theorem uncoloured_future_agrees :
    FiniteActionTreeAssays.Bisimilar successors successors (fun _ => PUnit.unit)
      (fun _ => PUnit.unit) .firstRoot .secondRoot :=
  ⟨rootAndLeafPairs, uncoloured_admitted, Or.inl ⟨rfl, rfl⟩⟩

theorem future_reassay_separates :
    ¬ FiniteActionTreeAssays.Bisimilar successors successors assay assay
      .firstRoot .secondRoot := by
  rintro ⟨relation, admitted, roots⟩
  obtain ⟨matched, member, leaves⟩ :=
    ((admitted _ _ roots).2 PUnit.unit).1 .firstLeaf (by simp [successors])
  have shape : matched = .secondLeaf := by simpa [successors] using member
  subst matched
  have readouts := (admitted _ _ leaves).1
  cases readouts

theorem root_intersection_is_insufficient :
    assay .firstRoot = assay .secondRoot ∧
      FiniteActionTreeAssays.Bisimilar successors successors (fun _ => PUnit.unit)
        (fun _ => PUnit.unit) .firstRoot .secondRoot ∧
      ¬ FiniteActionTreeAssays.Bisimilar successors successors assay assay
        .firstRoot .secondRoot :=
  ⟨root_assays_agree, uncoloured_future_agrees, future_reassay_separates⟩

end Mettapedia.OSLF.Framework.InstrumentObserverControls
