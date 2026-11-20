import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualDiamond

/-!
# Rule syntax over a binding signature: declaration frames

At the canonical frames of a binding signature (`Interface.Frames.contextual S`: declaration families,
contextual assignments, terms with metavariables applied to their parameters), a firing extends its
frame by new declarations (`declarations`): the extended frame declares the old names and the new ones,
and the weakening sends each old name to itself.

* **Freshness is the coproduct property** (`canonical_fresh`): a rule opened at the extension by its
  own declarations, each unknown sent to its own new name (`canonicalOpening`), is fresh at every state,
  whatever its store and knowledge. At one frame the freshness of an opening depends on what the state
  mentions; for this opening it does not.
* **No hidden coupling** (`information_amalgamates`, any frame action): when a firing with a fresh
  opening takes and reads no row, every solution of the knowledge and every solution of the rule's
  own tells extend together to a solution of its information, which agrees with the first on every
  term the state mentions and with the second on the rule's terms. Through such a firing its new
  unknowns are related to what the state mentions only as the knowledge and the rule's tells relate
  them. Freshness (`Firing.Fresh`) asks agreement only on the terms the state mentions, so this says
  nothing about names of the frame that the state does not mention.

The helper step of the tree (`Interface.Helpers.helperStep`) tells a fresh helper's value as a term
over the state's own frame, without a row. At every solution of its information the helper is its
value read at the old names (`helper_coupled`); with the value an old name `m` and no knowledge, no
solution sends `m` to `1` and the helper to `2` (`HelperControl.nameHelper_coupled`). The two
statements do not meet at that control: its state mentions nothing, so `information_amalgamates`
says nothing about `m` there, and at that state a fresh firing of a program that takes and reads no
row couples a new unknown to `m` in the same way (`CouplingControls.coupling_admitted`,
`CouplingControls.coupling_couples`, in `ContextualCoupling`). They meet where the state mentions the
old name: there the helper firing still couples (`CouplingControls.mentionedHelper_coupled`), the
same program firing is refused (`CouplingControls.coupling_refused_when_mentioned`), and every fresh
firing of a program that takes and reads no row adds no relation between its new unknowns and what
the state mentions beyond the knowledge and the rule's tells (`information_amalgamates`). That the
helper step's transition relation is the relation of no program, under every embedding of its
states, is not stated here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc

/-! ## No hidden coupling, at every frame action -/

section Amalgamation

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **No hidden coupling**: a firing with a fresh opening that takes and reads no row has, for every
solution of the knowledge and every solution of the rule's own tells, a solution of its information
that agrees with the first on every term the state mentions and with the second on the rule's
terms. -/
theorem information_amalgamates {s : State Tm O} (f : Firing O E P s.frame) (fresh : f.Fresh X s)
    (noTake : f.selection.taken = []) (noRead : f.selection.read = []) {b : Obj}
    (g : Hom s.frame b) (h : Hom f.rule.locals b) (known : X.Models g s.knowledge)
    (told : X.Models h f.rule.body.tell) :
    ∃ u : Hom (E.target f.ext) b, X.Models u (f.information X s) ∧
      (∀ t, s.Mentions t → X.E (X.act u (X.act (E.weaken f.ext) t)) (X.act g t)) ∧
      ∀ t ∈ f.rule.terms, X.E (X.act u (X.act f.opening t)) (X.act h t) := by
  obtain ⟨u, state, rule⟩ := fresh b g h
  refine ⟨u, ?_, state, rule⟩
  have symm := fun {x y : Tm b} (same : X.E x y) => (X.equivalence b).symm same
  have trans := fun {x y z : Tm b} (one : X.E x y) (two : X.E y z) => (X.equivalence b).trans one two
  intro e member
  unfold Firing.information Firing.matching at member
  rw [noTake, noRead, List.zipWith_nil_right, List.zipWith_nil_right, List.append_nil,
    List.append_nil] at member
  rcases List.mem_append.mp member with old | opened
  · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp old
    have left := state original.1 (Or.inl (List.mem_map_of_mem inside))
    have right := state original.2 (Or.inr (Or.inl (List.mem_map_of_mem inside)))
    exact trans left (trans (known original inside) (symm right))
  · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp opened
    have firstTerm : original.1 ∈ f.rule.terms := by
      unfold Rule.terms
      simp only [List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨original, inside, rfl⟩))))
    have secondTerm : original.2 ∈ f.rule.terms := by
      unfold Rule.terms
      simp only [List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨original, inside, rfl⟩)))
    exact trans (rule original.1 firstTerm) (trans (told original inside) (symm (rule original.2 secondTerm)))

end Amalgamation

/-! ## Declaration frames -/

namespace Contextual

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface.Frames (Frame)

variable (S : Signature)

/-- Terms at a declaration frame: observations of terms with its metavariables. -/
abbrev Terms : Frame S → Type := fun F => Observation S F.arity

/-- The frame declaring the old names and the new ones. -/
abbrev extend (F N : Frame S) : Frame S := ⟨F.Names ⊕ N.Names, Sum.elim F.arity N.arity⟩

/-- Each old name, as itself in the extended frame. -/
def weakenNames (F N : Frame S) : Assignment F.arity (extend S F N).arity :=
  fun name => generator (extend S F N).arity (.inl name)

/-- **Extensions by declarations**: a firing extends a frame by new names with their arities; the
weakening sends each old name to itself. -/
def declarations : Extensions (fun F G : Frame S => Assignment F.arity G.arity) where
  Ext _ := Frame S
  target {F} N := extend S F N
  weaken {F} N := weakenNames S F N

/-- **The canonical opening**: each of the rule's unknowns goes to its own new name. -/
def canonicalOpening (F N : Frame S) : Assignment N.arity (extend S F N).arity :=
  fun name => generator (extend S F N).arity (.inr name)

/-- The two parts of an instantiation of the extended frame. -/
def copair {F N B : Frame S} (g : Assignment F.arity B.arity) (h : Assignment N.arity B.arity) :
    Assignment (extend S F N).arity B.arity
  | .inl name => g name
  | .inr name => h name

theorem copair_weaken {F N B : Frame S} (g : Assignment F.arity B.arity)
    (h : Assignment N.arity B.arity) (t : Terms S F) :
    instantiateObservation (copair S g h) (instantiateObservation (weakenNames S F N) t) =
      instantiateObservation g t := by
  rw [instantiateObservation_comp]
  congr 1
  funext name
  exact instantiate_generator (copair S g h) (.inl name)

theorem copair_opening {F N B : Frame S} (g : Assignment F.arity B.arity)
    (h : Assignment N.arity B.arity) (t : Terms S N) :
    instantiateObservation (copair S g h) (instantiateObservation (canonicalOpening S F N) t) =
      instantiateObservation h t := by
  rw [instantiateObservation_comp]
  congr 1
  funext name
  exact instantiate_generator (copair S g h) (.inr name)

variable {S} {O : Type} {P : Program (Terms S)}

/-- **The canonical firing**: a rule of the program, opened at the extension by its own
declarations. -/
def canonical {F : Frame S} (r : Rule (Terms S)) (member : r ∈ P) (selection : Selection O)
    (seen : List (Finset O)) : Firing O (declarations S) P F :=
  ⟨r, member, r.locals, canonicalOpening S F r.locals, selection, seen⟩

/-- **At declaration frames the canonical opening is fresh at every state**: freshness is the
coproduct property of the extended frame, whatever the store and the knowledge. -/
theorem canonical_fresh (s : State (Terms S) O) (r : Rule (Terms S)) (member : r ∈ P)
    (selection : Selection O) (seen : List (Finset O)) :
    (canonical (F := s.frame) r member selection seen).Fresh (Frames.contextual S) s := by
  intro B g h
  exact ⟨copair S g h, fun t _ => copair_weaken S g h t, fun t _ => copair_opening S g h t⟩

/-! ## The helper step couples a new unknown with old names without a row -/

section HelperStep

variable {O' : Type}

/-- **The helper step couples**: at every solution of a helper firing's information, the helper is its
value read at the old names. -/
theorem helper_coupled {s : Interface.Helpers.State S O'} (f : Interface.Helpers.Firing s)
    {B : Frame S} (u : Assignment (Interface.Helpers.extend s.frame f.helper).arity B.arity)
    (solved : (Frames.contextual S).Models u f.information) :
    instantiate u (Interface.Helpers.fresh s.frame f.helper) =
      instantiate (Assignment.compose u (Interface.Helpers.incl s.frame f.helper)) f.value := by
  have told := solved f.tell (List.mem_append_right _ (List.mem_singleton_self _))
  have same : observe (instantiate u (Interface.Helpers.fresh s.frame f.helper)) =
      observe (instantiate u (instantiate (Interface.Helpers.incl s.frame f.helper) f.value)) := told
  rw [Assignment.instantiate_compose]
  exact observe_injective same

end HelperStep

namespace HelperControl

open Interface.Helpers.Consumer (tiny constant)

/-- One old name `m`. -/
abbrev oneName : Frame tiny := ⟨Unit, fun _ => ([], ())⟩

/-- No knowledge and no occurrences at that frame. -/
abbrev start : Interface.Helpers.State tiny ℕ := ⟨oneName, [], ∅⟩

/-- Make occurrence `0` and a helper whose value is the old name `m`. -/
def nameHelper : Interface.Helpers.Firing start := ⟨0, ([], ()), generator oneName.arity (), []⟩

/-- **The helper is the old name at every solution**: although the knowledge allows every value of
`m`, no solution of the information sends `m` to `1` and the helper to `2`. -/
theorem nameHelper_coupled :
    ¬ ∃ (B : Frame tiny) (u : Assignment (Interface.Helpers.extend oneName ([], ())).arity B.arity),
      (Frames.contextual tiny).Models u nameHelper.information ∧ u (.inl ()) = constant 1 ∧
        u (.inr ()) = constant 2 := by
  rintro ⟨B, u, solved, old, new⟩
  have coupled := helper_coupled nameHelper u solved
  have helperValue : instantiate u (Interface.Helpers.fresh oneName ([], ())) = u (.inr ()) :=
    instantiate_generator u (.inr ())
  have oldValue : instantiate (Assignment.compose u (Interface.Helpers.incl oneName ([], ())))
      (generator oneName.arity ()) = u (.inl ()) := by
    rw [instantiate_generator]
    exact instantiate_generator u (.inl ())
  have same : u (.inr ()) = u (.inl ()) := helperValue.symm.trans (coupled.trans oldValue)
  rw [old, new] at same
  simp [constant] at same

end HelperControl

end Contextual

#print axioms Contextual.helper_coupled
#print axioms Contextual.HelperControl.nameHelper_coupled
#print axioms information_amalgamates
#print axioms Contextual.copair_weaken
#print axioms Contextual.copair_opening
#print axioms Contextual.canonical_fresh

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
