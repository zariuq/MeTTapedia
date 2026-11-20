import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Syntax.Readings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ComputableSettler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklistSolver
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerChoices

/-!
# A computable settler for the typed-syntax package

The package computes (`typed`, `val`, the transports, the recursion principle), so a rigid-clash
refutation would be unsound for it; its solver step is built from the tree's parts with the package's
own conversion, as for the vectors package:

* the package's executable conversion (`syntaxReducer`, from its thirty-six rows) drives the typed η
  conversion scan;
* the newest-unknown dispatcher solves a definition of the newest declaration, checked by the
  executable checker of the package, with its declared types formed (`syntaxDeclared`);
* nothing is refuted (`synRound_never_refutes`).

**Deciding admission** (`synAdmits?`) has three outcomes: `some true` is sound (`synAdmits?_sound`),
`some false` is sound (`synAdmits?_refuted`), `none` claims nothing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Syntax

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate
open Interface.DependentFull (Make State Firing enabled_iff)
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerVectorsModel (unit tt unitRec void voidRec add unitCtors U0 numC zeroC succC unitC ttC addC
  unitRecC voidC voidRecC)
open TowerSyntaxModel

/-! ## The package's declared types are formed -/

/-- **Every declared type of the package is a type.** -/
theorem syntaxDeclared (lv : LevelExpr Nat) : DeclaredTypesFormed (rules lv) := by
  intro name type declared
  have tw := tw_rules lv
  have tNum : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed (rules lv) Δ numC U0 := fun {_ _} => num_typed lv
  have tBool : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed (rules lv) Δ boolC U0 := fun {_ _} => bool_typed lv
  have tRaw : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed (rules lv) Δ rawC U0 := fun {_ _} => raw_typed lv
  obtain ⟨mem, found⟩ := restrict_declared lv (names := TowerSyntaxModel.allNames) declared
  simp only [TowerSyntaxModel.allNames, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> cases found
  · exact ⟨_, tw.isUniverse _, .headType (tw.headTyping _)⟩
  · exact ⟨u, tw.isUniverse _, tNum⟩
  · exact ⟨u, tw.isUniverse _, tw.pi_small tNum tNum⟩
  · obtain ⟨w, hw, t⟩ := TowerNumbersModel.recType_typed lv
    exact ⟨w, hw, Derivable.mono (sub_numbers₂ lv) t⟩
  · exact ⟨_, tw.isUniverse _, .headType (tw.headTyping _)⟩
  · exact ⟨u, tw.isUniverse _, unit_typed lv⟩
  · exact tw.unitRecType_typed rfl rfl lv
  · exact ⟨_, tw.isUniverse _, .headType (tw.headTyping _)⟩
  · exact voidRecType_typed' lv tw rfl
  · exact ⟨_, tw.isUniverse _, .headType (tw.headTyping _)⟩
  · exact ⟨u, tw.isUniverse _, tBool⟩
  · exact ⟨u, tw.isUniverse _, tBool⟩
  · exact twoRecType_typed lv tw (T := bool) (k₁ := btrue) (k₂ := bfalse) rfl rfl rfl
  · exact ⟨_, tw.isUniverse _, .headType (tw.headTyping _)⟩
  · exact ⟨u, tw.isUniverse _, ty_typed lv⟩
  · exact ⟨u, tw.isUniverse _, ty_typed lv⟩
  · exact twoRecType_typed lv tw (T := ty) (k₁ := tnum) (k₂ := tbool) rfl rfl rfl
  · exact ⟨_, tw.isUniverse _, .headType (tw.headTyping _)⟩
  · exact ⟨u, tw.isUniverse _, tw.pi_small tNum tRaw⟩
  · exact ⟨u, tw.isUniverse _, tw.pi_small tBool tRaw⟩
  · exact ⟨u, tw.isUniverse _, tw.pi_small tRaw (tw.pi_small tRaw tRaw)⟩
  · exact ⟨u, tw.isUniverse _, tw.pi_small tRaw (tw.pi_small tRaw (tw.pi_small tRaw tRaw))⟩
  · exact ⟨u, tw.isUniverse _, tw.pi_small tRaw tRaw⟩
  · exact RawDeclared.recType_typed lv (rawD lv)
  · exact ⟨u, tw.isUniverse _, tw.pi_small tNum (tw.pi_small tNum tNum)⟩
  · exact ⟨u, tw.isUniverse _, tw.pi_small tNum tBool⟩
  · exact ⟨_, tw.isUniverse _, tyFamily_typed tw rfl⟩
  · exact ⟨_, tw.isUniverse _, tyFamily_typed tw rfl⟩
  · exact ⟨_, tw.isUniverse _, tyFamily_typed tw rfl⟩
  · exact ⟨_, tw.isUniverse _, .piForm tRaw (tw.isUniverse _) (tyFamily_typed tw rfl) (tw.isUniverse _)
      (tw.join _ _)⟩
  · obtain ⟨w, hw, t⟩ := atType_typed lv (c := tnum) (f := isNum) rfl rfl
    exact ⟨w, hw, Derivable.mono (sub_restrict lv _ (by decide)) t⟩
  · obtain ⟨w, hw, t⟩ := atType_typed lv (c := tbool) (f := isBool) rfl rfl
    exact ⟨w, hw, Derivable.mono (sub_restrict lv _ (by decide)) t⟩
  · obtain ⟨w, hw, t⟩ := synType_typed lv
    exact ⟨w, hw, Derivable.mono (sub_restrict lv _ (by decide)) t⟩

/-! ## The solver step of the package -/

/-- The level of the step side: the recursors' motives land in the small types. -/
abbrev level0 : LevelExpr Nat := .const 0

/-- The package at level zero, as a setting. -/
abbrev synS : Setting Tower.Head ℕ := TowerSyntaxModel.setting level0 fun _ => 0

instance synHeadEqDecidable : DecidableRel synS.R.headEq := fun left right =>
  LevelTower.instDecidableHeadEq left right

instance synCumulativeDecidable : DecidableRel synS.R.cumulative := fun left right =>
  LevelTower.instDecidableCumulative left right

instance synUniverseDecidable (head : Tower.Head) : Decidable (synS.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

/-- The tower's head choices, for the package. -/
def synChoices : ExecutableChecking.HeadChoices synS.R where
  typing head := ExecutableTowerChoices.choices.typing head
  join := ExecutableTowerChoices.choices.join

/-- **One round of the package's solver**: discharge the equations the package's conversion makes
true, else define the newest declaration; otherwise stuck. It refutes nothing. -/
def synRound (fuel : Nat) {Γ : Context synS.R} (problem : EquationStore (TotalTerm Γ)) :
    ContextualDependentWorklist.Round synS.levels (ContextualDependentWorklist.size (S := synS)) problem :=
  if shorter : (Conversion.scan (S := synS) (TowerSyntaxModel.facts level0) (TowerSyntaxModel.roots level0)
      (TowerSyntaxModel.heads level0) (TowerSyntaxModel.algebra level0) (syntaxReducer level0) fuel
      problem).length < problem.length then
    .progress (ContextualDependentUpdate.conversion (S := synS) (TowerSyntaxModel.facts level0)
      (TowerSyntaxModel.roots level0) (TowerSyntaxModel.heads level0) (TowerSyntaxModel.algebra level0)
      (syntaxReducer level0) fuel problem) (Prod.Lex.right _ shorter)
  else
    match ContextualDependentWorklist.newestOf (S := synS) (TowerSyntaxModel.facts level0)
        (TowerSyntaxModel.roots level0) (TowerSyntaxModel.heads level0) (TowerSyntaxModel.algebra level0)
        (syntaxDeclared level0) synChoices (syntaxReducer level0) fuel Γ with
    | none => .stuck
    | some view =>
        match ContextualDependentWorklist.throughNewest (S := synS) view problem
            (ContextualDependentWorklist.dispatchNewest (S := synS) (TowerSyntaxModel.facts level0)
              (TowerSyntaxModel.roots level0) (TowerSyntaxModel.heads level0)
              (TowerSyntaxModel.algebra level0) (syntaxDeclared level0) synChoices (syntaxReducer level0) fuel
              view.type) with
        | none => .stuck
        | some ⟨update, smaller⟩ => .progress update (Prod.Lex.left _ _ smaller)

/-- **The package's solver step.** -/
def synSolver (fuel : Nat) : ContextualDependentWorklist.Solver synS.levels where
  rank := ContextualDependentWorklist.size (S := synS)
  round := synRound fuel

/-- **The round never refutes.** -/
theorem synRound_never_refutes (fuel : Nat) {Γ : Context synS.R} {problem : EquationStore (TotalTerm Γ)}
    (missing : ¬ (frames synS.levels).Solvable problem) : synRound fuel problem ≠ .refuted missing := by
  unfold synRound
  split
  · exact fun same => by cases same
  · split
    · exact fun same => by cases same
    · split
      · exact fun same => by cases same
      · exact fun same => by cases same

/-- **The package's decided family**: the worklist driver over the package's solver step. -/
def synFamily (fuel budget : Nat) : Family synS.levels :=
  driverFamily synS.levels (synSolver fuel) budget

/-- **The package's computable settler.** -/
def synSettler (fuel budget : Nat) : Settler synS.levels :=
  Settler.ofFamilies synS.levels [synFamily fuel budget]

/-! ## Deciding admission -/

/-- The checks at a settled answer. -/
def synChecksAt (fuel : Nat) {s : State synS.R Nat} (f : Firing synS.levels s)
    (frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B)
    {M : Context synS.R} (σ : M ⟶ f.helpers.frame) : Bool :=
  f.makes.attach.all (fun m => (Conversion.compareTypes (S := synS) (TowerSyntaxModel.facts level0)
      (TowerSyntaxModel.roots level0) (TowerSyntaxModel.heads level0)
      (TowerSyntaxModel.algebra level0) (syntaxReducer level0) fuel ((frameType m.1 m.2).1.reindex σ)
      (m.1.2.type.reindex σ)).isSome) &&
    decide (f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧
      f.reads.length = f.read.length) &&
    decide ((∀ o ∈ f.taken, o ∈ s.present) ∧ (∀ o ∈ f.read, o ∈ s.present) ∧
      (∀ o ∈ f.taken, o ∉ f.read) ∧ ∀ o ∈ f.made, o ∉ s.present)

/-- The verdict of admission at a decision on the information. -/
def synAdmitsAt? (fuel : Nat) {s : State synS.R Nat} (f : Firing synS.levels s)
    (frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B) :
    Decision synS.levels f.information → Option Bool
  | .settled _ σ _ => if synChecksAt fuel f frameType σ then some true else none
  | .refuted _ => some false
  | .undecided => none

/-- **The decision of admission of the computable converting step over the package**, with three
outcomes. -/
def synAdmits? (families : List (Family synS.levels)) (fuel : Nat) {s : State synS.R Nat}
    (f : Firing synS.levels s)
    (frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B) : Option Bool :=
  if f.guards.isEmpty && f.queries.isEmpty then
    synAdmitsAt? fuel f frameType (firstDecisionAt synS.levels f.information families)
  else none

/-- **`some true` is sound**: the computable converting step admits the firing. -/
theorem synAdmits?_sound {families : List (Family synS.levels)} {fuel : Nat} {s : State synS.R Nat}
    {f : Firing synS.levels s}
    {frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B}
    (decided : synAdmits? families fuel f frameType = some true) :
    (convertingStep synS.levels Nat (Settler.ofFamilies synS.levels families)).Admits f := by
  unfold synAdmits? at decided
  by_cases empty : (f.guards.isEmpty && f.queries.isEmpty) = true
  · rw [if_pos empty] at decided
    obtain ⟨noGuards, noQueries⟩ := Bool.and_eq_true_iff.mp empty
    have noGuards : f.guards = [] := List.isEmpty_iff.mp noGuards
    have noQueries : f.queries = [] := List.isEmpty_iff.mp noQueries
    cases first : firstDecisionAt synS.levels f.information families with
    | settled M σ initial =>
        rw [first] at decided
        by_cases checks : synChecksAt fuel f frameType σ = true
        · unfold synChecksAt at checks
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checks
          obtain ⟨⟨rows, a, b, c, d⟩, enabled⟩ := checks
          have verdict : Settler.ofFamilies synS.levels families f.information = .settled M σ initial := by
            unfold Settler.ofFamilies
            rw [first]
            rfl
          rw [converting_admits_iff_of_settled synS.levels _ noQueries verdict, noGuards]
          refine ⟨⟨a, b, c, d, fun m member => ?_⟩, (enabled_iff f).mpr enabled, Frames.models_nil _⟩
          obtain ⟨certificate, -⟩ := Option.isSome_iff_exists.mp (rows ⟨m, member⟩ (List.mem_attach _ _))
          exact ⟨(frameType m member).1, (frameType m member).2, below_of_typeEq certificate.down⟩
        · have none : synAdmitsAt? fuel f frameType (.settled M σ initial) = none := by
            simp only [synAdmitsAt?, checks, if_false, Bool.false_eq_true]
          rw [none] at decided
          cases decided
    | refuted none =>
        rw [first] at decided
        cases decided
    | undecided =>
        rw [first] at decided
        cases decided
  · rw [if_neg empty] at decided
    cases decided

/-- **`some false` is sound**: no settler's converting step admits the firing. -/
theorem synAdmits?_refuted {families : List (Family synS.levels)} {fuel : Nat} {s : State synS.R Nat}
    {f : Firing synS.levels s}
    {frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B}
    (decided : synAdmits? families fuel f frameType = some false) (settler : Settler synS.levels) :
    ¬ (convertingStep synS.levels Nat settler).Admits f := by
  intro admitted
  unfold synAdmits? at decided
  by_cases empty : (f.guards.isEmpty && f.queries.isEmpty) = true
  · rw [if_pos empty] at decided
    cases first : firstDecisionAt synS.levels f.information families with
    | settled M σ initial =>
        rw [first] at decided
        by_cases checks : synChecksAt fuel f frameType σ = true
        · have some : synAdmitsAt? fuel f frameType (.settled M σ initial) = some true := by
            simp only [synAdmitsAt?, checks, if_true]
          rw [some] at decided
          cases decided
        · have none : synAdmitsAt? fuel f frameType (.settled M σ initial) = none := by
            simp only [synAdmitsAt?, checks, if_false, Bool.false_eq_true]
          rw [none] at decided
          cases decided
    | refuted none => exact none admitted.2.2.1
    | undecided =>
        rw [first] at decided
        cases decided
  · rw [if_neg empty] at decided
    cases decided

end NativeTypesOnTheStep.Computing.Syntax

#print axioms NativeTypesOnTheStep.Computing.Syntax.syntaxDeclared
#print axioms NativeTypesOnTheStep.Computing.Syntax.synRound
#print axioms NativeTypesOnTheStep.Computing.Syntax.synRound_never_refutes
#print axioms NativeTypesOnTheStep.Computing.Syntax.synSettler
#print axioms NativeTypesOnTheStep.Computing.Syntax.synAdmits?_sound
#print axioms NativeTypesOnTheStep.Computing.Syntax.synAdmits?_refuted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
