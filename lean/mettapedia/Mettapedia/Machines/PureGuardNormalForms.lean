import Mettapedia.Machines.OrderedGuardPipeline
import Mathlib.Tactic

/-!
# Pure guard normal forms and sufficient observer information

Finite pure guards normalize to an ordered list of signed observations and
literals. Empty alternatives disappear, negations compose without a depth
cap, and explicitly inert metadata disappears. The normalizer preserves
answer order and multiplicity, not merely a Boolean disjunction. A singleton
recognizer consequently survives these certified equivalent spellings.

The source extractor must prove purity, finite completion, argument behavior
and metadata inertness for its active profile. An empty answer list alone is
not such a certificate: an effect followed by failure is a counterexample in
the existing operational semantics. No arbitrary typed declaration is erased.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PureGuardNormalForms

variable {Key Meta State Answer : Type}

inductive Form (Key Meta : Type) where
  | test (key : Key)
  | literal (value : Bool)
  | empty
  | alternatives (left right : Form Key Meta)
  | neg (body : Form Key Meta)
  | inert (metadata : Meta) (body : Form Key Meta)
  deriving DecidableEq

def eval (observe : Key → Bool) : Form Key Meta → List Bool
  | .test key => [observe key]
  | .literal b => [b]
  | .empty => []
  | .alternatives l r => eval observe l ++ eval observe r
  | .neg body => (eval observe body).map Bool.not
  | .inert _ body => eval observe body

inductive Signed (Key : Type) where
  | test (negated : Bool) (key : Key)
  | literal (value : Bool)
  deriving DecidableEq

def Signed.flip : Signed Key → Signed Key
  | .test b key => .test (!b) key
  | .literal b => .literal (!b)

def Signed.eval (observe : Key → Bool) : Signed Key → Bool
  | .test b key => if b then !(observe key) else observe key
  | .literal b => b

def normalize : Form Key Meta → List (Signed Key)
  | .test key => [.test false key]
  | .literal b => [.literal b]
  | .empty => []
  | .alternatives l r => normalize l ++ normalize r
  | .neg body => (normalize body).map Signed.flip
  | .inert _ body => normalize body

theorem flip_eval (observe : Key → Bool) (a : Signed Key) :
    a.flip.eval observe = !(a.eval observe) := by
  cases a with
  | test b key => cases b <;> simp [Signed.flip, Signed.eval]
  | literal b => rfl

theorem flip_flip (a : Signed Key) : a.flip.flip = a := by
  cases a <;> simp [Signed.flip]

theorem normalize_correct (observe : Key → Bool) (form : Form Key Meta) :
    (normalize form).map (Signed.eval observe) = eval observe form := by
  induction form with
  | test key => rfl
  | literal b => rfl
  | empty => rfl
  | alternatives l r ihl ihr => simp [normalize, eval, ihl, ihr]
  | neg body ih =>
      simp only [normalize, List.map_map, Function.comp_def, flip_eval, eval]
      rw [← ih, List.map_map]
      rfl
  | inert metadata body ih => exact ih

theorem dead_alternative (form : Form Key Meta) :
    normalize (.alternatives form .empty) = normalize form ∧
      normalize (.alternatives .empty form) = normalize form := by simp [normalize]

theorem double_negation (form : Form Key Meta) :
    normalize (.neg (.neg form)) = normalize form := by
  simp [normalize, List.map_map, Function.comp_def, flip_flip]

/-- Recognition after normalization, rather than a source equation count. -/
def singleton (form : Form Key Meta) : Option (Signed Key) :=
  match normalize form with
  | [one] => some one
  | _ => none

theorem singleton_sound (observe : Key → Bool) (form : Form Key Meta) (one : Signed Key)
    (accepted : singleton form = some one) : eval observe form = [one.eval observe] := by
  unfold singleton at accepted
  split at accepted
  · rename_i entry exactForm
    have same : entry = one := Option.some.inj accepted
    subst entry
    rw [← normalize_correct observe form, exactForm]
    rfl
  · contradiction

theorem singleton_dead_alternative (form : Form Key Meta) :
    singleton (.alternatives form .empty) = singleton form := by
  simp [singleton, (dead_alternative form).1]

theorem singleton_inert (form : Form Key Meta) (metadata : Meta) :
    singleton (.inert metadata form) = singleton form := rfl

theorem singleton_double_negation (form : Form Key Meta) :
    singleton (.neg (.neg form)) = singleton form := by rw [singleton, double_negation]; rfl

/-- Normalized answers can replace the pure provider under arbitrary
effectful continuations of the existing guard semantics. -/
theorem continuation_preserved {Local World Result : Type}
    (observe : Local → Key → Bool) (form : Form Key Meta)
    (materialize : Local → List Bool → List Local)
    (next : ScopedCommit.Body Local World) (state : Local)
    (success : ScopedCommit.Success Local World Result)
    (failure saved : ScopedCommit.Failure World Result) (world : World) :
    ScopedCommit.eval
      (OrderedGuardPipeline.guard
        (fun s => materialize s ((normalize form).map (Signed.eval (observe s)))) next)
      state success failure saved world =
    ScopedCommit.eval
      (OrderedGuardPipeline.guard (fun s => materialize s (eval (observe s) form)) next)
      state success failure saved world := by
  apply OrderedGuardPipeline.guard_congr
  rw [normalize_correct]

/-- Sufficient retained information must distinguish every pair of states
that the declared observer distinguishes. -/
def Sufficient (retain : State → Key) (observe : State → Answer) : Prop :=
  ∀ a b, retain a = retain b → observe a = observe b

noncomputable def lifted (retain : State → Key) (observe : State → Answer)
    (key : Set.range retain) : Answer := observe (Classical.choose key.property)

theorem sufficient_factors (retain : State → Key) (observe : State → Answer)
    (sufficient : Sufficient retain observe) (s : State) :
    lifted retain observe ⟨retain s, s, rfl⟩ = observe s := by
  apply sufficient
  exact Classical.choose_spec (show ∃ original, retain original = retain s from ⟨s, rfl⟩)

theorem dropped_information_refutes_sufficiency (retain : State → Key) (observe : State → Answer)
    (a b : State) (same : retain a = retain b) (different : observe a ≠ observe b) :
    ¬ Sufficient retain observe := fun sufficient => different (sufficient a b same)

namespace Controls

def original : Form Nat Unit := .neg (.test 0)

example : singleton (.alternatives original .empty) = some (.test true 0) := rfl
example : singleton (.inert () original) = some (.test true 0) := rfl
example : singleton (.neg (.neg original)) = some (.test true 0) := rfl
example : singleton (.alternatives original original) = none := rfl

theorem duplicate_answers_are_not_a_single_guard :
    eval (fun _ : Nat => true) (.alternatives (.test 0 : Form Nat Unit) (.test 0)) = [true, true] := rfl

def effectThenEmpty : ScopedCommit.Body Unit Nat :=
  .effect (fun state world => (state, world + 1)) .fail

theorem empty_answers_do_not_imply_inertness :
    (ScopedCommit.run effectThenEmpty () 0).1 = [] ∧
    ScopedCommit.run effectThenEmpty () 0 ≠ ScopedCommit.run (.fail : ScopedCommit.Body Unit Nat) () 0 := by
  decide

theorem result_projection_can_lose_a_guard :
    ¬ Sufficient (Prod.fst : Nat × Bool → Nat) Prod.snd :=
  dropped_information_refutes_sufficiency _ _ (7, true) (7, false) rfl (by decide)

end Controls

#print axioms normalize_correct
#print axioms continuation_preserved
#print axioms sufficient_factors
#print axioms Controls.empty_answers_do_not_imply_inertness

end Mettapedia.Machines.PureGuardNormalForms
