import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.PresentationMeetsStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy
import Mathlib.Logic.Equiv.Finset

/-!
# The authored presentation meets the first-order step

`PresentationMeetsStep` compares the presentation's diamond with a step's, through an exact
encoding of the step's states and firings into patterns. A first-order firing carries predicate
queries, whose regions no pattern codes (`PresentationMeetsStep.no_pattern_code`). Queries add no
successor (`ProgramAdequacy.program_succ_iff`), so the comparison goes through the firings without
them:

* `comapCore`: an effect core read through a map of firings;
* `plainProgram`: the first-order step under a rule set, on plain firings (a rule and a selection),
  read as first-order firings with no predicate queries (`annotate`); it has the same successors as
  the first-order step (`plainProgram_succ_iff`);
* `encodablePresentation`: every encodable type has an exact pattern presentation, by its code;
  so for encodable terms and identities the plain step has an exact encoding
  (`firstOrderEncoding`);
* **`firstOrder_diamond_meets_successors`**: possibility over the first-order step's successors,
  under every rule set, is the presentation's possibility after a choice of firing, pulled back
  along the state's code.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.FirstOrderPresentation

open Interface
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.DerivedModalities
open Presentation
open StepSpan ProgramAdequacy PresentationMeetsStep

universe uO uT uH uOcc uS uF uF'

/-! ## An effect core read through a map of firings -/

section Comap

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {Firing' : State → Type uF'}

/-- **An effect core read through a map of firings**: every effect of a firing is the effect of
its image. -/
def comapCore (E : EffectCore X O State Firing) (embed : ∀ {s : State}, Firing' s → Firing s) :
    EffectCore X O State Firing' where
  frame := E.frame
  knowledge := E.knowledge
  present := E.present
  selection f := E.selection (embed f)
  target f := E.target (embed f)
  extension f := E.extension (embed f)
  information f := E.information (embed f)
  information_refines f := E.information_refines (embed f)
  Shapes f := E.Shapes (embed f)
  preparedResult f p := E.preparedResult (embed f) p
  present_preparedResult f p := E.present_preparedResult (embed f) p
  preparedSettle f p := E.preparedSettle (embed f) p
  result_refines f p := E.result_refines (embed f) p

end Comap

/-! ## The first-order step on plain firings -/

section Plain

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- A firing without predicate queries: a rule and a selection. -/
abbrev PlainFiring (T : Type uT) (O : Type uO) := RuleInstance T × ConstraintMultisetRewriting.Selection O

/-- A plain firing, as a first-order firing with no predicate queries. -/
def annotate (f : PlainFiring T O) : AnnotatedRuns.Firing T S O := ⟨f.1, [], f.2⟩

/-- **The first-order step under a rule set, on plain firings.** -/
def plainProgram (R : Set (RuleInstance T)) :
    Interface.Step (Frames.ofSubstitution A) O (Configuration T O) (fun _ => PlainFiring T O) :=
  Interface.Step.ofEffect
    (comapCore (AnnotatedRuns.firstOrder A label).toStep.effectCore fun f => annotate (S := S) f)
    fun {C} f _ => (annotate (S := S) f).Valid A label C ∧ f.1 ∈ R

/-- **The plain step has the first-order step's successors**: predicate queries add none. -/
theorem plainProgram_succ_iff (R : Set (RuleInstance T)) (C C' : Configuration T O) :
    Succ (plainProgram A label R) C C' ↔ Succ (program A label R) C C' := by
  rw [program_succ_iff]
  constructor
  · rintro ⟨⟨rule, sel⟩, ⟨_, valid, member⟩, reached⟩
    exact ⟨rule, sel, member, valid.firing, reached⟩
  · rintro ⟨rule, sel, member, valid, reached⟩
    have fValid : (annotate (S := S) (rule, sel)).Valid A label C :=
      (PredicateQueryAdmission.valid_empty_iff A label rule C sel).mpr valid
    exact ⟨(rule, sel), ⟨(AnnotatedRuns.firstOrder A label).toStep.prepares fValid, fValid, member⟩,
      reached⟩

theorem plainProgram_succ_eq (R : Set (RuleInstance T)) :
    Succ (plainProgram A label R) = Succ (program A label R) := by
  funext C C'
  exact propext (plainProgram_succ_iff A label R C C')

end Plain

/-! ## Exact codes for encodable states and firings -/

section Codes

/-- **Every encodable type has an exact pattern presentation**: a value is viewed as the index of
its code, and read back by decoding. -/
def encodablePresentation (α : Type*) [Encodable α] (key : Mettapedia.GSLT.Parsing.ExactPresentation.Key) :
    PatternPresentation α where
  key := key
  expand p := match p with
    | .bvar n => Encodable.decode n
    | _ => none
  view a := .bvar (Encodable.encode a)
  expand_view a := Encodable.encodek a

variable {T : Type uT} {O : Type uO} [Encodable T] [Encodable O]

local instance checkEncodable : Encodable (Check T) :=
  Encodable.ofEquiv ((T × T) ⊕ T ⊕ (T × ℕ))
    { toFun := fun c => match c with
        | .equal l r => .inl (l, r)
        | .absent p => .inr (.inl p)
        | .count p n => .inr (.inr (p, n))
      invFun := fun x => match x with
        | .inl (l, r) => .equal l r
        | .inr (.inl p) => .absent p
        | .inr (.inr (p, n)) => .count p n
      left_inv := fun c => by cases c <;> rfl
      right_inv := fun x => by rcases x with ⟨l, r⟩ | p | ⟨p, n⟩ <;> rfl }

local instance ruleEncodable : Encodable (RuleInstance T) :=
  Encodable.ofEquiv (List T × List T × List (T × T) × List (Check T) × List T)
    { toFun := fun r => (r.take, r.read, r.tell, r.checks, r.produce)
      invFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

local instance selectionEncodable : Encodable (ConstraintMultisetRewriting.Selection O) :=
  Encodable.ofEquiv (List O × List O × List O)
    { toFun := fun s => (s.taken, s.read, s.made)
      invFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

local instance configurationEncodable : Encodable (Configuration T O) :=
  Encodable.ofEquiv (List (T × T) × Finset O)
    { toFun := fun C => (C.equations, C.present)
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **An exact encoding of the plain first-order step**, for encodable terms and identities. -/
def firstOrderEncoding : Encoding (Configuration T O) (fun _ => PlainFiring T O) :=
  ⟨encodablePresentation (Configuration T O) ⟨"tcalc.first-order-store", 1⟩,
    encodablePresentation ((_ : Configuration T O) × PlainFiring T O) ⟨"tcalc.first-order-firing", 1⟩⟩

end Codes

/-! ## The presentation meets the first-order step -/

section Meets

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] [Encodable T] [Encodable O]
  (A : SubstitutionAction T S) (label : O → T)

/-- **The presentation meets the first-order step**: under every rule set, possibility over the
first-order step's successors is the presentation's possibility after a choice of firing, pulled
back along the state's code. -/
theorem firstOrder_diamond_meets_successors (R : Set (RuleInstance T)) (ψ : Pattern → Prop) :
    pb (atOf (firstOrderEncoding (T := T) (O := O)))
        (derivedDiamond (chooseSpan (firstOrderEncoding (T := T) (O := O)))
          (derivedDiamond (presentationSpan (plainProgram A label R) firstOrderEncoding
            (Decisions.ofClassical _ _)) ψ)) =
      derivedDiamond (FragmentsOfTheStep.TransitionMaps.span (Succ (program A label R)))
        (pb (atOf (firstOrderEncoding (T := T) (O := O))) ψ) := by
  rw [diamond_meets_successors, plainProgram_succ_eq]

end Meets

#print axioms comapCore
#print axioms plainProgram_succ_iff
#print axioms plainProgram_succ_eq
#print axioms encodablePresentation
#print axioms firstOrderEncoding
#print axioms firstOrder_diamond_meets_successors

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.FirstOrderPresentation
