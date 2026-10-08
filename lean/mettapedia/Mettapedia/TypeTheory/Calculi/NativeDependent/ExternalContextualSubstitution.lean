import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalJudgments

/-!
# Admitted substitutions for external generated judgments

An admitted telescope has an actual generated formation proof for each entry.
Substitution components and their equations are interpreted as the authored
typing and equality judgments. The complete substitution judgment is recovered
from these ordered components; no model interpretation is used.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External
namespace Contextual

universe u
variable {S : Symbols.{u}} {D : Signature S}

abbrev Holds (D : Signature S) (judgment : Judgment S) : Prop :=
  Nonempty (Derivation D judgment)

def PremisesHold (D : Signature S) : List (Judgment S) → Prop
  | [] => True
  | judgment :: remaining => Holds D judgment ∧ PremisesHold D remaining

theorem PremisesHold.get {premises : List (Judgment S)}
    (admitted : PremisesHold D premises) (position : Fin premises.length) :
    Holds D (premises.get position) := by
  induction premises with
  | nil => exact Fin.elim0 position
  | cons first remaining ih =>
    cases position using Fin.cases with
    | zero => exact admitted.1
    | succ position => exact ih admitted.2 position

/-- Build an actual generated rule occurrence from the admitted premise trees. -/
theorem conclude (rule : RuleCode D) (premises : PremisesHold D rule.premises) :
    Holds D rule.conclusion := by
  classical
  exact ⟨derive rule (fun position => Classical.choice (premises.get position))⟩

inductive Formed (D : Signature S) : {n : Nat} → ContextExpr S n → Prop where
  | nil : Formed D .nil
  | snoc {n : Nat} {context : ContextExpr S n} {type : TypeExpr S n}
      (previous : Formed D context) (formed : Holds D (.type context type)) :
      Formed D (.snoc context type)

theorem Formed.judgment {n : Nat} {context : ContextExpr S n}
    (formed : Formed D context) : Holds D (.context context) := by
  induction formed with
  | nil => exact conclude .contextNil trivial
  | snoc _ typed ih => exact conclude (.contextExtend _ _) ⟨ih, typed, trivial⟩

def ContextFormationResult (D : Signature S) : Judgment S → Prop
  | .context context => Formed D context
  | _ => True

/-- All generated context formation trees give the same admitted telescope shape. -/
theorem derivationContextFormation {judgment : Judgment S} (tree : Derivation D judgment) :
    ContextFormationResult D judgment := by
  refine JudgmentDerivation.Derivation.rec (S := judgmentSignature D)
    (motive := fun judgment _ => ContextFormationResult D judgment)
    (fun rule premises ih => ?_) tree
  rcases rule with ⟨code, rfl⟩
  cases code <;> try exact trivial
  case contextNil => exact .nil
  case contextExtend context type =>
    exact .snoc (ih ⟨⟨0, by change 0 < 2; decide⟩⟩)
      ⟨premises ⟨⟨1, by change 1 < 2; decide⟩⟩⟩

theorem formed_iff {n : Nat} (context : ContextExpr S n) :
    Formed D context ↔ Holds D (.context context) := by
  constructor
  · exact Formed.judgment
  · rintro ⟨tree⟩
    exact derivationContextFormation tree

theorem typeSubstitute {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {type : TypeExpr S m}
    (admitted : Holds D (.substitution source target substitution))
    (formed : Holds D (.type target type)) :
    Holds D (.type source (type.substitute substitution)) :=
  conclude (.substituteType source target substitution type) ⟨admitted, formed, trivial⟩

theorem termSubstitute {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {term : TermExpr S m} {type : TypeExpr S m}
    (admitted : Holds D (.substitution source target substitution))
    (typed : Holds D (.term target term type)) :
    Holds D (.term source (term.substitute substitution) (type.substitute substitution)) :=
  conclude (.substituteTerm source target substitution term type) ⟨admitted, typed, trivial⟩

theorem Formed.lookup {n : Nat} {context : ContextExpr S n}
    (formed : Formed D context) (index : Fin n) : Holds D (.type context (context.lookup index)) := by
  induction formed with
  | nil => exact Fin.elim0 index
  | @snoc n context type previous typed ih =>
    have projection := conclude (.substitutionWeaken context type) ⟨typed, trivial⟩
    cases index using Fin.cases with
    | zero =>
      simpa only [ContextExpr.lookup_zero, TypeExpr.substitute_variables] using
        typeSubstitute projection typed
    | succ index =>
      simpa only [ContextExpr.lookup_succ, TypeExpr.substitute_variables] using
        typeSubstitute projection (ih index)

def Components {n m : Nat} (source : ContextExpr S n) (target : ContextExpr S m)
    (substitution : Substitution S m n) : Prop :=
  ∀ index, Holds D (.term source (substitution index) ((target.lookup index).substitute substitution))

theorem substitutionComponents {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} (targetFormed : Formed D target)
    (admitted : Holds D (.substitution source target substitution)) :
    Components (D := D) source target substitution := by
  intro index
  have entry := conclude (.variable target index) ⟨targetFormed.judgment, trivial⟩
  exact termSubstitute admitted entry

def tail {n m : Nat} (substitution : Substitution S (m + 1) n) : Substitution S m n :=
  fun index => substitution index.succ

theorem substitute_weaken {n m : Nat} (type : TypeExpr S m)
    (substitution : Substitution S (m + 1) n) :
    (type.rename Fin.succ).substitute substitution = type.substitute (tail substitution) :=
  TypeExpr.substitute_rename Fin.succ substitution type

theorem extend_tail {n m : Nat} (substitution : Substitution S (m + 1) n) :
    extendSubstitution (tail substitution) (substitution 0) = substitution := by
  funext index
  cases index using Fin.cases <;> rfl

theorem componentsTail {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {type : TypeExpr S m} {substitution : Substitution S (m + 1) n}
    (typed : Components (D := D) source (.snoc target type) substitution) :
    Components (D := D) source target (tail substitution) := by
  intro index
  simpa only [tail, ContextExpr.lookup_succ, substitute_weaken] using typed index.succ

/-- Every actual typed component is used to assemble the authored substitution. -/
theorem componentsSubstitution {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    (sourceFormed : Formed D source) (targetFormed : Formed D target)
    (substitution : Substitution S m n) (typed : Components (D := D) source target substitution) :
    Holds D (.substitution source target substitution) := by
  induction targetFormed with
  | nil =>
    have unique : substitution = Fin.elim0 := by funext index; exact Fin.elim0 index
    subst substitution
    exact conclude (.substitutionNil source) ⟨sourceFormed.judgment, trivial⟩
  | @snoc m target type previous formed ih =>
    have admitted := ih (tail substitution) (componentsTail typed)
    have head : Holds D (.term source (substitution 0) (type.substitute (tail substitution))) := by
      simpa only [ContextExpr.lookup_zero, substitute_weaken] using typed 0
    have paired := conclude (.substitutionExtend source target type (tail substitution) (substitution 0))
      ⟨admitted, formed, head, trivial⟩
    simpa only [RuleCode.conclusion, extend_tail] using paired

def ComponentEquations {n m : Nat} (source : ContextExpr S n) (target : ContextExpr S m)
    (first second : Substitution S m n) : Prop :=
  ∀ index, Holds D (.termEq source (first index) (second index)
    ((target.lookup index).substitute first))

theorem componentEquationsTail {n m : Nat} {source : ContextExpr S n}
    {target : ContextExpr S m} {type : TypeExpr S m} {first second : Substitution S (m + 1) n}
    (same : ComponentEquations (D := D) source (.snoc target type) first second) :
    ComponentEquations (D := D) source target (tail first) (tail second) := by
  intro index
  simpa only [tail, ContextExpr.lookup_succ, substitute_weaken] using same index.succ

/-- The generated substitution equation is earned from all typed component equations. -/
theorem componentEquationsSubstitution {n m : Nat} {source : ContextExpr S n}
    {target : ContextExpr S m} (sourceFormed : Formed D source) (targetFormed : Formed D target)
    (first second : Substitution S m n) (firstTyped : Components (D := D) source target first)
    (secondTyped : Components (D := D) source target second)
    (same : ComponentEquations (D := D) source target first second) :
    Holds D (.substitutionEq source target first second) := by
  induction targetFormed with
  | nil =>
    have firstUnique : first = Fin.elim0 := by funext index; exact Fin.elim0 index
    have secondUnique : second = Fin.elim0 := by funext index; exact Fin.elim0 index
    rw [firstUnique, secondUnique]
    exact conclude (.substitutionReflexivity source .nil Fin.elim0)
      ⟨conclude (.substitutionNil source) ⟨sourceFormed.judgment, trivial⟩, trivial⟩
  | @snoc m target type previous formed ih =>
    have prior := ih (tail first) (tail second) (componentsTail firstTyped)
      (componentsTail secondTyped) (componentEquationsTail same)
    have head : Holds D (.termEq source (first 0) (second 0) (type.substitute (tail first))) := by
      simpa only [ContextExpr.lookup_zero, substitute_weaken] using same 0
    have secondHead : Holds D (.term source (second 0) (type.substitute (tail second))) := by
      simpa only [ContextExpr.lookup_zero, substitute_weaken] using secondTyped 0
    have paired := conclude (.substitutionExtendEquality source target type
      (tail first) (tail second) (first 0) (second 0)) ⟨prior, formed, head, secondHead, trivial⟩
    simpa only [RuleCode.conclusion, extend_tail] using paired

/-- Projection congruence reads each component of an authored substitution equation. -/
theorem substitutionComponentEquations {n m : Nat} {source : ContextExpr S n}
    {target : ContextExpr S m} {first second : Substitution S m n}
    (targetFormed : Formed D target) (same : Holds D (.substitutionEq source target first second)) :
    ComponentEquations (D := D) source target first second := by
  intro index
  have entry := conclude (.variable target index) ⟨targetFormed.judgment, trivial⟩
  exact conclude (.termSubstitutionCongruence source target first second (.var index)
    (target.lookup index)) ⟨same, entry, trivial⟩

theorem substitutionEquality_iff {n m : Nat} {source : ContextExpr S n}
    {target : ContextExpr S m} (sourceFormed : Formed D source) (targetFormed : Formed D target)
    (first second : Substitution S m n) (firstTyped : Components (D := D) source target first)
    (secondTyped : Components (D := D) source target second) :
    Holds D (.substitutionEq source target first second) ↔
      ComponentEquations (D := D) source target first second :=
  ⟨substitutionComponentEquations targetFormed,
    componentEquationsSubstitution sourceFormed targetFormed first second firstTyped secondTyped⟩

theorem substitutionEquality_refl {n m : Nat} {source : ContextExpr S n}
    {target : ContextExpr S m} {substitution : Substitution S m n}
    (admitted : Holds D (.substitution source target substitution)) :
    Holds D (.substitutionEq source target substitution substitution) :=
  conclude (.substitutionReflexivity source target substitution) ⟨admitted, trivial⟩

theorem substitutionEquality_symm {n m : Nat} {source : ContextExpr S n}
    {target : ContextExpr S m} {first second : Substitution S m n}
    (same : Holds D (.substitutionEq source target first second)) :
    Holds D (.substitutionEq source target second first) :=
  conclude (.substitutionSymmetry source target first second) ⟨same, trivial⟩

theorem substitutionEquality_trans {n m : Nat} {source : ContextExpr S n}
    {target : ContextExpr S m} {first middle last : Substitution S m n}
    (earlier : Holds D (.substitutionEq source target first middle))
    (later : Holds D (.substitutionEq source target middle last)) :
    Holds D (.substitutionEq source target first last) :=
  conclude (.substitutionTransitivity source target first middle last) ⟨earlier, later, trivial⟩

theorem substitutionCompose {n m k : Nat} {source : ContextExpr S n} {middle : ContextExpr S m}
    {target : ContextExpr S k} {earlier : Substitution S m n} {later : Substitution S k m}
    (firstTyped : Holds D (.substitution source middle earlier))
    (secondTyped : Holds D (.substitution middle target later)) :
    Holds D (.substitution source target (composeSubstitution later earlier)) :=
  conclude (.substitutionCompose source middle target earlier later) ⟨firstTyped, secondTyped, trivial⟩

theorem substitutionEquality_precompose {n m k : Nat} {source : ContextExpr S n}
    {middle : ContextExpr S m} {target : ContextExpr S k}
    (sourceFormed : Formed D source) (targetFormed : Formed D target)
    {earlier : Substitution S m n} {first second : Substitution S k m}
    (earlierTyped : Holds D (.substitution source middle earlier))
    (firstTyped : Holds D (.substitution middle target first))
    (secondTyped : Holds D (.substitution middle target second))
    (same : Holds D (.substitutionEq middle target first second)) :
    Holds D (.substitutionEq source target
      (composeSubstitution first earlier) (composeSubstitution second earlier)) := by
  apply componentEquationsSubstitution sourceFormed targetFormed
    (composeSubstitution first earlier) (composeSubstitution second earlier)
    (substitutionComponents targetFormed (substitutionCompose earlierTyped firstTyped))
    (substitutionComponents targetFormed (substitutionCompose earlierTyped secondTyped))
  intro index
  have equation := substitutionComponentEquations targetFormed same index
  have transported := conclude (.substituteTermEquality source middle earlier (first index)
    (second index) ((target.lookup index).substitute first)) ⟨earlierTyped, equation, trivial⟩
  change Holds D (.termEq source ((first index).substitute earlier) ((second index).substitute earlier)
    (((target.lookup index).substitute first).substitute earlier)) at transported
  rw [TypeExpr.substitute_comp] at transported
  exact transported

theorem substitutionEquality_postcompose {n m k : Nat} {source : ContextExpr S n}
    {middle : ContextExpr S m} {target : ContextExpr S k}
    (sourceFormed : Formed D source) (targetFormed : Formed D target)
    {first second : Substitution S m n} {later : Substitution S k m}
    (firstTyped : Holds D (.substitution source middle first))
    (secondTyped : Holds D (.substitution source middle second))
    (laterTyped : Holds D (.substitution middle target later))
    (same : Holds D (.substitutionEq source middle first second)) :
    Holds D (.substitutionEq source target
      (composeSubstitution later first) (composeSubstitution later second)) := by
  apply componentEquationsSubstitution sourceFormed targetFormed
    (composeSubstitution later first) (composeSubstitution later second)
    (substitutionComponents targetFormed (substitutionCompose firstTyped laterTyped))
    (substitutionComponents targetFormed (substitutionCompose secondTyped laterTyped))
  intro index
  have component := substitutionComponents targetFormed laterTyped index
  have transported := conclude (.termSubstitutionCongruence source middle first second (later index)
    ((target.lookup index).substitute later)) ⟨same, component, trivial⟩
  change Holds D (.termEq source ((later index).substitute first) ((later index).substitute second)
    (((target.lookup index).substitute later).substitute first)) at transported
  rw [TypeExpr.substitute_comp] at transported
  exact transported

end Contextual
end Mettapedia.TypeTheory.Calculi.NativeDependent.External
