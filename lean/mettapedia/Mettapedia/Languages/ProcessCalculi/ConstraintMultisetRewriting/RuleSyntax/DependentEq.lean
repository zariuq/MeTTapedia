import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFull
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces

/-!
# The dependent full step restricted to a program is the step of the program at typed frames

At the typed βη frames of the dependent unifier (`ContextualDependentEta.frames`), with telescopes of
fresh helpers as the extensions (`helperExtensions`), the step of a program (`step`) and the
existing dependent full step (`Interface.DependentFull.step`) are compared through two maps.

* **States** are the same four fields (`toState`, `ofState`, mutually inverse).
* **Firings**: a firing of the program goes to the dependent firing with the same helper telescope and
  selection, the opened take and read patterns, the opened made rows as checked made rows
  (`Make.ofRow`), the opened tells, the opened equation checks as guards, and as predicate queries the
  opened predicate and count checks (`Query.predicate`, `Query.count`) and the opened collect patterns with
  their seen sets (`collectQuery`) (`toDependent`).

**The dependent full step restricted to a program** (`dependentOn`) admits the dependent firings that
are the image of a firing of the program whose opening is fresh.

* `admits_toDependent_iff`: a firing of the program is admitted exactly when its image is admitted by
  the dependent full step, its opening is fresh, and it has one made row per made identity and one
  seen set per collect pattern.
* `result_toDependent`: its result is the image of the dependent result.
* **`dependent_eq`**: through `toState`, the transition relation of the restricted dependent full
  step is the transition relation of the step of the program.

## What the dependent full step has beyond rule syntax

The unrestricted dependent full step is not the step of any program. Its firings are rule
**instances** at the extended frame: their patterns, tells and guards may mention the state's own
unknowns directly (no rule of a program can, since its unknowns are opened fresh), and its predicate
queries are arbitrary regions that read through solutions, with arbitrary answer predicates on the
seen rows, where rule syntax has the regions of patterns with the answers "empty", "this many" and
"exactly these". Its made rows are raw codes checked against types at admission; a rule's made rows
are typed terms, so their check holds by construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface (Frames)
open Interface.DependentFull (Helpers Make Query)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)

variable {Head : Type} {rules : Rules Head}

/-- Typed terms at a formed frame. -/
abbrev Terms (rules : Rules Head) : Context rules → Type := fun Γ => TotalTerm Γ

/-- **Helper telescopes as extensions**: a firing extends its frame by a telescope of fresh helpers
and moves along the weakening. -/
def helperExtensions : Extensions (fun Γ Δ : Context rules => Δ ⟶ Γ) where
  Ext Γ := Helpers Γ
  target h := h.frame
  weaken h := h.weaken

variable {O : Type}

/-- A dependent state, as a state of the rule-syntax step. -/
def toState (s : Interface.DependentFull.State rules O) : State (Terms rules) O :=
  ⟨s.frame, s.knowledge, s.present, s.label⟩

/-- A state of the rule-syntax step, as a dependent state. -/
def ofState (s : State (Terms rules) O) : Interface.DependentFull.State rules O :=
  ⟨s.frame, s.knowledge, s.present, s.label⟩

theorem toState_ofState (s : State (Terms rules) O) : toState (ofState s) = s := rfl

theorem ofState_toState (s : Interface.DependentFull.State rules O) : ofState (toState s) = s := rfl

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

/-- The guard of an equation check. -/
def guardOf {Δ : Context rules} : Check (TotalTerm Δ) → Option (Equation (TotalTerm Δ))
  | .equal left right => some (left, right)
  | .predicate _ _ => none
  | .count _ _ => none

variable (O) in
/-- The predicate query of a none query or count check. -/
def queryOf {Δ : Context rules} : Check (TotalTerm Δ) → Option (Query levels O Δ)
  | .equal _ _ => none
  | .predicate q pattern => some (Query.predicate levels O q pattern)
  | .count pattern number => some (Query.count levels O pattern number)

/-- **A collect pattern as a dependent predicate query**: its region is the rows a solution equates with
the pattern, and its answer is exactly the claimed rows. -/
def collectQuery {Δ : Context rules} (pattern : TotalTerm Δ) (claimed : Finset O) : Query levels O Δ where
  region τ t := Query.matching levels pattern τ t
  reads := fun {_} τ {_ _} same => Query.matching_reads levels pattern τ same
  answer found := found = claimed

variable {P : Program (Terms rules)}

/-- **The dependent firing of a firing of a program.** -/
def toDependent {s : Interface.DependentFull.State rules O}
    (g : Firing O (helperExtensions (rules := rules)) P s.frame) :
    Interface.DependentFull.Firing levels s where
  helpers := g.ext
  taken := g.selection.taken
  read := g.selection.read
  takes := (g.opened (frames levels)).take
  reads := (g.opened (frames levels)).read
  makes := g.selection.made.zip ((g.opened (frames levels)).produce.map Make.ofRow)
  tells := (g.opened (frames levels)).tell
  guards := (g.opened (frames levels)).checks.filterMap guardOf
  queries := (g.opened (frames levels)).checks.filterMap (queryOf O levels) ++
    ((g.collectOpened (frames levels)).zip g.seen).map fun q => collectQuery levels q.1 q.2

/-! ## Information, guards and results agree -/

section Agreement

variable {levels}

theorem information_toDependent {s : Interface.DependentFull.State rules O}
    (g : Firing O (helperExtensions (rules := rules)) P s.frame) :
    (toDependent levels g).information = g.information (frames levels) (toState s) := by
  unfold Interface.DependentFull.Firing.information Interface.DependentFull.Firing.matching
    Firing.information Firing.matching
  rw [← List.map_uncurry_zip_eq_zipWith, ← List.map_uncurry_zip_eq_zipWith]
  rfl

theorem made_toDependent {s : Interface.DependentFull.State rules O}
    (g : Firing O (helperExtensions (rules := rules)) P s.frame)
    (lengths : g.rule.body.produce.length = g.selection.made.length) :
    (toDependent levels g).made = g.selection.made := by
  unfold Interface.DependentFull.Firing.made
  apply List.map_fst_zip
  show g.selection.made.length ≤
    ((g.rule.body.produce.map ((frames levels).act g.opening)).map Make.ofRow).length
  rw [List.length_map, List.length_map, lengths]

theorem count_holds_iff {Δ Θ : Context rules} (pattern : TotalTerm Δ) (number : Nat)
    (present : Finset O) (row : O → TotalTerm Δ) (τ : Θ ⟶ Δ) :
    (Query.count levels O pattern number).Holds present row τ ↔
      (matchesAt (frames levels) τ row present pattern).card = number := by
  constructor
  · rintro ⟨seen, members, card⟩
    have same : seen = matchesAt (frames levels) τ row present pattern := by
      ext o
      rw [members o, mem_matchesAt]
      exact Iff.rfl
    rw [← same]
    exact card
  · intro card
    refine ⟨matchesAt (frames levels) τ row present pattern, fun o => ?_, card⟩
    rw [mem_matchesAt]
    exact Iff.rfl

theorem collect_holds_iff {Δ Θ : Context rules} (pattern : TotalTerm Δ) (claimed : Finset O)
    (present : Finset O) (row : O → TotalTerm Δ) (τ : Θ ⟶ Δ) :
    (collectQuery levels pattern claimed).Holds present row τ ↔
      matchesAt (frames levels) τ row present pattern = claimed := by
  constructor
  · rintro ⟨seen, members, rfl⟩
    ext o
    rw [members o, mem_matchesAt]
    exact Iff.rfl
  · intro same
    refine ⟨claimed, fun o => ?_, rfl⟩
    rw [← same, mem_matchesAt]
    exact Iff.rfl

theorem check_holds_iff {Δ Θ : Context rules} (c : Check (TotalTerm Δ)) (present : Finset O)
    (row : O → TotalTerm Δ) (τ : Θ ⟶ Δ) :
    checkHolds (frames levels) τ row present c ↔
      (∀ e, guardOf c = some e → (frames levels).Solves τ e) ∧
        ∀ q, queryOf O levels c = some q → q.Holds present row τ := by
  cases c with
  | equal left right =>
      constructor
      · intro holds
        refine ⟨fun e same => ?_, fun q same => by simp [queryOf] at same⟩
        simp only [guardOf, Option.some.injEq] at same
        subst same
        exact holds
      · rintro ⟨guard, -⟩
        exact guard (left, right) rfl
  | predicate quantifier pattern =>
      constructor
      · intro holds
        refine ⟨fun e same => by simp [guardOf] at same, fun q same => ?_⟩
        simp only [queryOf, Option.some.injEq] at same
        subst same
        exact (Query.predicate_holds_iff quantifier pattern present row τ).mpr holds
      · rintro ⟨-, query⟩
        exact (Query.predicate_holds_iff quantifier pattern present row τ).mp (query _ rfl)
  | count pattern number =>
      constructor
      · intro holds
        refine ⟨fun e same => by simp [guardOf] at same, fun q same => ?_⟩
        simp only [queryOf, Option.some.injEq] at same
        subst same
        exact (count_holds_iff pattern number present row τ).mpr holds
      · rintro ⟨-, query⟩
        exact (count_holds_iff pattern number present row τ).mp (query _ rfl)

/-- **The guard predicate is the dependent one.** -/
theorem holds_toDependent {s : Interface.DependentFull.State rules O}
    (g : Firing O (helperExtensions (rules := rules)) P s.frame) {Θ : Context rules}
    (τ : Θ ⟶ g.ext.frame) :
    (toDependent levels g).Holds τ ↔ g.Holds (frames levels) (toState s) τ := by
  unfold Interface.DependentFull.Firing.Holds Firing.Holds
  have checks : ∀ cs : List (Check (TotalTerm g.ext.frame)),
      ((frames levels).Models τ (cs.filterMap guardOf) ∧
        ∀ q ∈ cs.filterMap (queryOf O levels), q.Holds s.present (toDependent levels g).row τ) ↔
      ∀ c ∈ cs, checkHolds (frames levels) τ (g.row (frames levels) (toState s)) s.present c := by
    intro cs
    constructor
    · rintro ⟨guards, queries⟩ c member
      refine (check_holds_iff c s.present _ τ).mpr ⟨fun e same => ?_, fun q same => ?_⟩
      · exact guards e (List.mem_filterMap.mpr ⟨c, member, same⟩)
      · exact queries q (List.mem_filterMap.mpr ⟨c, member, same⟩)
    · intro all
      refine ⟨fun e member => ?_, fun q member => ?_⟩
      · obtain ⟨c, inside, same⟩ := List.mem_filterMap.mp member
        exact ((check_holds_iff c s.present _ τ).mp (all c inside)).1 e same
      · obtain ⟨c, inside, same⟩ := List.mem_filterMap.mp member
        exact ((check_holds_iff c s.present _ τ).mp (all c inside)).2 q same
  constructor
  · rintro ⟨guards, queries⟩
    refine ⟨(checks _).mp ⟨guards, fun q member => queries q (List.mem_append_left _ member)⟩, ?_⟩
    intro q member
    exact (collect_holds_iff q.1 q.2 s.present _ τ).mp
      (queries _ (List.mem_append_right _ (List.mem_map.mpr ⟨q, member, rfl⟩)))
  · rintro ⟨all, collect⟩
    obtain ⟨guards, queries⟩ := (checks _).mpr all
    refine ⟨guards, fun q member => ?_⟩
    rcases List.mem_append.mp member with query | counted
    · exact queries q query
    · obtain ⟨pair, inside, rfl⟩ := List.mem_map.mp counted
      exact (collect_holds_iff pair.1 pair.2 s.present _ τ).mpr (collect pair inside)

variable [DecidableEq O]

theorem relabel_ofRow {Δ : Context rules} (row : O → TotalTerm Δ) :
    ∀ (made : List O) (rows : List (TotalTerm Δ))
      (typed : ∀ m ∈ made.zip (rows.map Make.ofRow), m.2.WellTyped),
      Interface.DependentFull.relabel row (made.zip (rows.map Make.ofRow)) typed = relabel row made rows
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | o' :: os, t :: ts, typed => by
      funext o
      simp only [List.map_cons, List.zip_cons_cons, Interface.DependentFull.relabel, relabel]
      split_ifs with same
      · rfl
      · exact congrFun (relabel_ofRow row os ts _) o

end Agreement

/-! ## Admission and results agree -/

variable {levels} [DecidableEq O]

/-- **Admission agrees.** -/
theorem admits_toDependent_iff (s : Interface.DependentFull.State rules O)
    (g : Firing O (helperExtensions (rules := rules)) P s.frame) :
    (step (frames levels) O helperExtensions P).Admits (s := toState s) g ↔
      ((Interface.DependentFull.step levels O).Admits (s := s) (toDependent levels g) ∧
        g.Fresh (frames levels) (toState s) ∧
        g.rule.body.produce.length = g.selection.made.length ∧
        g.rule.collect.length = g.seen.length) := by
  show g.Admits (frames levels) (toState s) ↔ ((toDependent levels g).Admits ∧ _)
  unfold Firing.Admits Firing.Shapes Interface.DependentFull.Firing.Admits
    Interface.DependentFull.Firing.Shapes
  have takeLength : (g.opened (frames levels)).take.length = g.rule.body.take.length :=
    List.length_map _
  have readLength : (g.opened (frames levels)).read.length = g.rule.body.read.length :=
    List.length_map _
  have typed : ∀ m ∈ (toDependent levels g).makes, m.2.WellTyped := by
    intro m member
    obtain ⟨-, inside⟩ := List.of_mem_zip member
    obtain ⟨t, -, same⟩ := List.mem_map.mp inside
    rw [← same]
    exact Make.ofRow_wellTyped t
  have entails : (frames levels).Entails (toDependent levels g).information
        (fun _ τ => (toDependent levels g).Holds τ) ↔
      (frames levels).Entails (g.information (frames levels) (toState s))
        (fun _ τ => g.Holds (frames levels) (toState s) τ) := by
    rw [information_toDependent]
    exact forall₂_congr fun _ τ => imp_congr_right fun _ => holds_toDependent g τ
  rw [entails, information_toDependent]
  constructor
  · rintro ⟨⟨fresh, takenNodup, madeNodup, take, read, produce, collect⟩, enabled, solvable, asks⟩
    have made := made_toDependent (levels := levels) g produce
    have selection : (toDependent levels g).selection = g.selection := by
      show (⟨g.selection.taken, g.selection.read, (toDependent levels g).made⟩ : Selection O) = g.selection
      rw [made]
    refine ⟨⟨⟨takenNodup, made ▸ madeNodup, takeLength.trans take, readLength.trans read, typed⟩,
      selection ▸ enabled, solvable, asks⟩, fresh, produce, collect⟩
  · rintro ⟨⟨⟨takenNodup, madeNodup, take, read, -⟩, enabled, solvable, asks⟩, fresh, produce, collect⟩
    have made := made_toDependent (levels := levels) g produce
    have selection : (toDependent levels g).selection = g.selection := by
      show (⟨g.selection.taken, g.selection.read, (toDependent levels g).made⟩ : Selection O) = g.selection
      rw [made]
    refine ⟨⟨fresh, takenNodup, made ▸ madeNodup, takeLength.symm.trans take,
      readLength.symm.trans read, produce, collect⟩, selection ▸ enabled, solvable, asks⟩

/-- **Results agree**: the result of an admitted firing of the program is the image of the dependent
result. -/
theorem result_toDependent (s : Interface.DependentFull.State rules O)
    (g : Firing O (helperExtensions (rules := rules)) P s.frame)
    (admitted : (Interface.DependentFull.step levels O).Admits (s := s) (toDependent levels g))
    (lengths : g.rule.body.produce.length = g.selection.made.length) :
    g.result (frames levels) (toState s) = toState ((toDependent levels g).after admitted) := by
  have made := made_toDependent (levels := levels) g lengths
  unfold Firing.result Interface.DependentFull.Firing.after toState
  simp only [State.mk.injEq]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact heq_of_eq (information_toDependent g).symm
  · show _ = fire s.present (⟨g.selection.taken, g.selection.read, (toDependent levels g).made⟩ :
      Selection O).commit
    rw [made]
  · apply heq_of_eq
    exact (relabel_ofRow (g.row (frames levels) (toState s)) g.selection.made
      (g.opened (frames levels)).produce _).symm

/-- The dependent firings that open a rule of the program freshly. -/
def OpensProgram (s : Interface.DependentFull.State rules O)
    (f : Interface.DependentFull.Firing levels s) : Prop :=
  ∃ g : Firing O (helperExtensions (rules := rules)) P s.frame,
    g.Fresh (frames levels) (toState s) ∧ g.rule.body.produce.length = g.selection.made.length ∧
      g.rule.collect.length = g.seen.length ∧ toDependent levels g = f

variable (levels P) in
/-- **The dependent full step restricted to a program**: its admitted firings that open a rule of the
program freshly. -/
def dependentOn :
    Interface.Step (frames levels) O (Interface.DependentFull.State rules O)
      (Interface.DependentFull.Firing levels) :=
  Spaces.restrict (Interface.DependentFull.step levels O).toStep
    (fun {s} f => OpensProgram (P := P) s f)

/-- **The restricted dependent step admits exactly the images of the admitted firings of the
program.** -/
theorem dependentOn_admits_iff (s : Interface.DependentFull.State rules O)
    (f : Interface.DependentFull.Firing levels s) :
    (dependentOn levels P).Admits (s := s) f ↔
      ∃ g : Firing O (helperExtensions (rules := rules)) P s.frame, toDependent levels g = f ∧
        (step (frames levels) O helperExtensions P).Admits (s := toState s) g := by
  constructor
  · rintro ⟨admitted, g, fresh, produce, collect, rfl⟩
    exact ⟨g, rfl, (admits_toDependent_iff s g).mpr ⟨admitted, fresh, produce, collect⟩⟩
  · rintro ⟨g, rfl, admitted⟩
    obtain ⟨dependentAdmitted, fresh, produce, collect⟩ := (admits_toDependent_iff s g).mp admitted
    exact ⟨dependentAdmitted, g, fresh, produce, collect, rfl⟩

/-- **The dependent full step restricted to a program is the step of the program at typed frames**:
through `toState`, the two transition relations are equal. -/
theorem dependent_eq (s s' : Interface.DependentFull.State rules O) :
    Succ (dependentOn levels P) s s' ↔
      Succ (step (frames levels) O helperExtensions P).toStep (toState s) (toState s') := by
  constructor
  · rintro ⟨f, admitted, reached⟩
    obtain ⟨g, rfl, stepAdmitted⟩ := (dependentOn_admits_iff s f).mp admitted
    obtain ⟨dependentAdmitted, -, produce, -⟩ := (admits_toDependent_iff s g).mp stepAdmitted
    refine ⟨g, stepAdmitted, ?_⟩
    show g.result (frames levels) (toState s) = toState s'
    rw [result_toDependent s g dependentAdmitted produce]
    exact congrArg toState reached
  · rintro ⟨g, stepAdmitted, reached⟩
    obtain ⟨dependentAdmitted, fresh, produce, collect⟩ := (admits_toDependent_iff s g).mp stepAdmitted
    refine ⟨toDependent levels g, ⟨dependentAdmitted, g, fresh, produce, collect, rfl⟩, ?_⟩
    have result := result_toDependent s g dependentAdmitted produce
    have same : toState ((toDependent levels g).after dependentAdmitted) = toState s' :=
      result.symm.trans reached
    exact congrArg ofState same

/-! ## Both sides are inhabited -/

/-- Moving along the identity and then a morphism acts as the morphism. -/
theorem act_id_equiv {Obj' : Type*} {Tm' : Obj' → Type*} {Hom' : Obj' → Obj' → Type*}
    (X : Frames Tm' Hom') {a b : Obj'} (g : Hom' a b) (t : Tm' a) :
    X.E (X.act g (X.act (X.id a) t)) (X.act g t) := by
  rw [X.act_id]
  exact (X.equivalence b).refl _

/-- The rule that takes, reads, tells, asks and makes nothing, with the given unknowns. -/
def skip (ρ : Context rules) : Rule (Terms rules) := ⟨ρ, ⟨[], [], [], [], []⟩, []⟩

/-- A state with no knowledge. -/
def blank (Γ : Context rules) (present : Finset O) (label : O → TotalTerm Γ) :
    Interface.DependentFull.State rules O := ⟨Γ, [], present, label⟩

/-- **The rule with no terms is admitted at every state without knowledge**, opened along the
identity with no helpers. So the step of a program containing it, and through `dependent_eq` the
restricted dependent full step, have transitions; these are the trivial ones. -/
theorem skip_admitted (Γ : Context rules) (present : Finset O) (label : O → TotalTerm Γ)
    (member : skip Γ ∈ P) :
    (step (frames levels) O helperExtensions P).Admits (s := toState (blank Γ present label))
      (⟨skip Γ, member, Helpers.nil Γ, 𝟙 Γ, ⟨[], [], []⟩, []⟩ :
        Firing O (helperExtensions (rules := rules)) P Γ) := by
  refine (admits_iff _).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩,
    enabled_nil present, ⟨Γ, 𝟙 Γ, fun e member => ?_⟩, fun c member => ?_, fun q member => ?_⟩
  · intro b g h
    refine ⟨g, fun t _ => act_id_equiv (frames levels) g t, fun t inside => ?_⟩
    change t ∈ ([] : List (TotalTerm Γ)) at inside
    cases inside
  · change e ∈ ([] : EquationStore (TotalTerm Γ)) at member
    cases member
  · change c ∈ ([] : List (Check (TotalTerm Γ))) at member
    cases member
  · change q ∈ ([] : List (TotalTerm Γ × Finset O)) at member
    cases member

/-- **The restricted dependent full step has transitions.** -/
theorem dependentOn_inhabited (Γ : Context rules) (present : Finset O) (label : O → TotalTerm Γ)
    (member : skip Γ ∈ P) :
    ∃ s', Succ (dependentOn levels P) (blank Γ present label) s' := by
  let g : Firing O (helperExtensions (rules := rules)) P Γ :=
    ⟨skip Γ, member, Helpers.nil Γ, 𝟙 Γ, ⟨[], [], []⟩, []⟩
  refine ⟨ofState (g.result (frames levels) (toState (blank Γ present label))), ?_⟩
  exact (dependent_eq _ _).mpr ⟨g, skip_admitted Γ present label member, rfl⟩

#print axioms skip_admitted
#print axioms dependentOn_inhabited
#print axioms information_toDependent
#print axioms holds_toDependent
#print axioms admits_toDependent_iff
#print axioms result_toDependent
#print axioms dependentOn_admits_iff
#print axioms dependent_eq

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Dependent
