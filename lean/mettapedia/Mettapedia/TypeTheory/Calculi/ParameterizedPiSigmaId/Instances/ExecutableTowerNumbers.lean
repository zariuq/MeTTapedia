import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerChoices
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableRawChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerAccumulators

/-!
# A constructed computing instance of executable checking

The rule package is the existing cumulative natural-number model. The root
procedure recognizes the two actual recursor equations, with its dependent
motive and both methods retained. Its declaration-formation and normalization
facts come from that model. They are not algorithm inputs or uninstantiated
existence assumptions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableTowerNumbers

open Mettapedia.TypeTheory.UniverseLevel
open TowerNumbersModel

variable (level : LevelExpr Nat)

instance (head : Tower.Head) : Decidable ((rules level).isUniverse head) :=
  ExecutableTowerChoices.universeDecidable head

instance : DecidableRel (rules level).headEq :=
  fun first second => LevelTower.instDecidableHeadEq first second

instance : DecidableRel (rules level).cumulative :=
  fun first second => LevelTower.instDecidableCumulative first second

def choices : ExecutableChecking.HeadChoices (rules level) where
  typing head := some (ExecutableTowerChoices.typing head)
  join := ExecutableTowerChoices.join

def root : ExecutableReduction.RootEvaluator (rules level) :=
  fun {_} term => match term with
  | .app (.app (.app (.app (.const name) motive) base) step) (.const constructor) =>
      if isRec : name = numRec then
        if isZero : constructor = zero then
          some ⟨base, by
            subst name constructor
            exact ⟨motive, [base, step], 0, zero, [], [], base,
              rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
        else none
      else none
  | .app (.app (.app (.app (.const name) motive) base) step)
        (.app (.const constructor) child) =>
      if isRec : name = numRec then
        if isSucc : constructor = succ then
          some ⟨.app (.app step child) (recApp numRec [motive, base, step] child), by
            subst name constructor
            exact ⟨motive, [base, step], 1, succ, [.recursive], [child], step,
              rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
        else none
      else none
  | _ => none

@[simp] theorem root_zero {n : Nat} (motive base step : Tm Tower.Head n) :
    (root level (recApp numRec [motive, base, step] (.const zero))).map Subtype.val =
      some base := by
  simp [root, recApp, appSpine]

@[simp] theorem root_succ {n : Nat} (motive base step child : Tm Tower.Head n) :
    (root level (recApp numRec [motive, base, step] (.app (.const succ) child))).map Subtype.val =
      some (.app (.app step child) (recApp numRec [motive, base, step] child)) := by
  simp [root, recApp, appSpine]

theorem declaredTypesFormed : DeclaredTypesFormed (rules level) :=
  TowerAccumulatorsModel.numbers_typesFormed level (fun _ => 0)

/-- The full contextual reduction strategy of this computing model. -/
def fullReducer : ExecutableReduction.Reducer (rules level) :=
  ExecutableReduction.normalize (rules level) (root level)

/-- Recognition decisions for the already constructed normalization setting. -/
instance : DecidableRel (setting level (fun _ => 0)).R.headEq :=
  fun first second => LevelTower.instDecidableHeadEq first second

instance : DecidableRel (setting level (fun _ => 0)).R.cumulative :=
  fun first second => LevelTower.instDecidableCumulative first second

instance (head : Tower.Head) : Decidable ((setting level (fun _ => 0)).R.isUniverse head) :=
  ExecutableTowerChoices.universeDecidable head

/-- The checking decision for this constructed computing model. -/
def accepts {n : Nat} (fuel : Nat) (context : Ctx Tower.Head n) (term type : Tm Tower.Head n) :
    Bool := ExecutableChecking.accepts (rules level) (choices level) (fullReducer level)
      fuel context term type

/-- General soundness at the instantiated model; formation, declaration and
computation obligations have all been discharged here. -/
theorem accepts_sound {n fuel : Nat} {context : Ctx Tower.Head n} {term type : Tm Tower.Head n}
    (accepted : accepts level fuel context term type = true) :
    Typed (rules level) context term type := by
  let : DecidableRel (setting level (fun _ => 0)).R.headEq :=
    fun first second => LevelTower.instDecidableHeadEq first second
  let : DecidableRel (setting level (fun _ => 0)).R.cumulative :=
    fun first second => LevelTower.instDecidableCumulative first second
  let : ∀ head, Decidable ((setting level (fun _ => 0)).R.isUniverse head) :=
    fun head => ExecutableTowerChoices.universeDecidable head
  exact ExecutableChecking.accepts_sound (S := setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level) (declaredTypesFormed level)
    (choices level) (fullReducer level) accepted

/-- Source checking retains every authored domain, including context entries. -/
def acceptsSource {n : Nat} (fuel : Nat)
    (context : ExecutableWrittenChecking.SourceContext Tower.Head n) (term type : ATm Tower.Head n) :
    Bool := ExecutableWrittenChecking.acceptsSource (setting level (fun _ => 0))
      (facts level) (roots level) (heads level) (algebra level) (declaredTypesFormed level)
      (choices level) (fullReducer level) fuel context term type

theorem acceptsSource_sound {n fuel : Nat}
    {context : ExecutableWrittenChecking.SourceContext Tower.Head n} {term type : ATm Tower.Head n}
    (accepted : acceptsSource level fuel context term type = true) :
    ATyped (rules level) context.erase term type.erase :=
  ExecutableWrittenChecking.acceptsSource_sound (setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level) (declaredTypesFormed level)
    (choices level) (fullReducer level) accepted

/-- Raw source checking is scope recovery followed by that annotated procedure. -/
def acceptsRaw {n : Nat} (fuel : Nat)
    (context : ExecutableWrittenChecking.SourceContext Tower.Head n)
    (term type : NativeSyntax.Raw Tower.Head) : Bool :=
  ExecutableRawChecking.accepts (setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level) (declaredTypesFormed level)
    (choices level) (fullReducer level) fuel context term type

theorem acceptsRaw_sound {n fuel : Nat}
    {context : ExecutableWrittenChecking.SourceContext Tower.Head n} {term type : NativeSyntax.Raw Tower.Head}
    (accepted : acceptsRaw level fuel context term type = true) :
    ∃ source expected : ATm Tower.Head n,
      NativeSyntax.decode n term = some source ∧ NativeSyntax.decode n type = some expected ∧
      NativeSyntax.encode source = term ∧ NativeSyntax.encode expected = type ∧
      ATyped (rules level) context.erase source expected.erase :=
  ExecutableRawChecking.accepts_sound (setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level) (declaredTypesFormed level)
    (choices level) (fullReducer level) accepted

end TypedEquality.Normalization.ExecutableTowerNumbers
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
