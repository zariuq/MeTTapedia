import Mettapedia.Languages.Metamath.MM0Transfer.ParsedFrames

/-!
# A finite check for the actual parsed source-axiom profile

The input consists of the original operational frames and expressions. Every
raw distinctness pair is resolved through the owner's actual floating-variable
map. Missing endpoints and self-pairs are refused, rather than disappearing in
the semantic relation's filter. Accepted pairs have a bound-sort endpoint and
mandatory endpoints. This establishes a syntactic axiom profile, not a proof
of any target theorem or of a source parser/converter.

Concrete source qualification still must tie the complete accepted `$a` event
set to this finite input and check its exact source identity. No such whole
database certificate is assumed or claimed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM0Transfer.FiniteProfile

open _root_.Metamath
open _root_.Metamath.Spec.Equivalence
open _root_.Metamath.Spec.StoredStatement
open DistinctnessProjection

/-- The exact mandatory support calculated by the existing stored-statement
projection, exposed without the proposition-valued distinctness field. -/
def mandatoryVariables (frame : Spec.Frame) (expression : Spec.Expr) : List VR :=
  (exprToFormula (varMapOfFrame frame) expression ::
    frame.hyps.map (hypToDeclarativeFormula (varMapOfFrame frame))).flatMap
      (fun formula => formula.2.vars)

theorem mandatoryVariables_exact (frame : Spec.Frame) (expression : Spec.Expr) :
    mandatoryVariables frame expression = (statementOfFrame frame expression).vars := rfl

def checkPair (boundSort : CN → Bool) (frame : Spec.Frame)
    (mandatory : List VR) (pair : Spec.Variable × Spec.Variable) : Bool :=
  match findVR (varMapOfFrame frame) pair.1,
      findVR (varMapOfFrame frame) pair.2 with
  | some left, some right =>
      decide (left ≠ right) && (boundSort left.type || boundSort right.type) &&
        decide (left ∈ mandatory ∧ right ∈ mandatory)
  | _, _ => false

def checkAxiom (boundSort : CN → Bool) (frame : Spec.Frame)
    (expression : Spec.Expr) : Bool :=
  !boundSort expression.typecode.c &&
    frame.dv.all (checkPair boundSort frame (mandatoryVariables frame expression))

theorem checked_pair {boundSort : CN → Bool} {frame : Spec.Frame}
    {mandatory : List VR} {pair : Spec.Variable × Spec.Variable}
    {left right : VR} (leftLookup : findVR (varMapOfFrame frame) pair.1 = some left)
    (rightLookup : findVR (varMapOfFrame frame) pair.2 = some right)
    (checked : checkPair boundSort frame mandatory pair = true) :
    left ≠ right ∧ (boundSort left.type = true ∨ boundSort right.type = true) ∧
      left ∈ mandatory ∧ right ∈ mandatory := by
  simpa only [checkPair, leftLookup, rightLookup, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, and_assoc] using checked

/-- The finite checker resolves every pair used by the actual semantic
conversion; no fallback variable or unexamined endpoint is introduced. -/
theorem checked_mapped_pair {boundSort : CN → Bool} {frame : Spec.Frame}
    {expression : Spec.Expr} (checked : checkAxiom boundSort frame expression = true)
    {left right : VR}
    (present : (left, right) ∈ frame.dv.filterMap (fun pair =>
      match findVR (varMapOfFrame frame) pair.1, findVR (varMapOfFrame frame) pair.2 with
      | some first, some second => some (first, second)
      | _, _ => none)) :
    (boundSort left.type = true ∨ boundSort right.type = true) ∧
      left ∈ (statementOfFrame frame expression).vars ∧
      right ∈ (statementOfFrame frame expression).vars := by
  obtain ⟨pair, member, mapped⟩ := List.mem_filterMap.mp present
  have checks : (!boundSort expression.typecode.c) = true ∧
      frame.dv.all (checkPair boundSort frame (mandatoryVariables frame expression)) = true := by
    simpa only [checkAxiom, Bool.and_eq_true] using checked
  have allPairs : ∀ pair ∈ frame.dv,
      checkPair boundSort frame (mandatoryVariables frame expression) pair = true := by
    exact List.all_eq_true.mp checks.2
  cases first : findVR (varMapOfFrame frame) pair.1 with
  | none => simp [first] at mapped
  | some firstValue =>
      cases second : findVR (varMapOfFrame frame) pair.2 with
      | none => simp [first, second] at mapped
      | some secondValue =>
          have pairEqual : (firstValue, secondValue) = (left, right) := by
            simpa only [first, second, Option.some.injEq] using mapped
          rcases Prod.mk.inj pairEqual with ⟨rfl, rfl⟩
          have result := checked_pair first second (allPairs pair member)
          simpa only [mandatoryVariables_exact] using result.2

/-- A successful check certifies the syntactic profile of the original
stored-statement object, including its actual hypothesis support. -/
theorem checked_axiom_profile {boundSort : CN → Bool} {frame : Spec.Frame}
    {expression : Spec.Expr} (checked : checkAxiom boundSort frame expression = true) :
    ¬ boundSort (statementOfFrame frame expression).fmla.1 = true ∧
      ∀ left right, (statementOfFrame frame expression).ctx.dj left right →
        (boundSort left.type = true ∨ boundSort right.type = true) ∧
          left ∈ (statementOfFrame frame expression).vars ∧
          right ∈ (statementOfFrame frame expression).vars := by
  have checks : (!boundSort expression.typecode.c) = true ∧
      frame.dv.all (checkPair boundSort frame (mandatoryVariables frame expression)) = true := by
    simpa only [checkAxiom, Bool.and_eq_true] using checked
  refine ⟨?_, ?_⟩
  · change ¬ boundSort expression.typecode.c = true
    intro bound
    simp [bound] at checks
  · intro left right distinct
    rcases distinct.2 with present | present
    · exact checked_mapped_pair checked present
    · have result := checked_mapped_pair checked present
      exact ⟨result.1.symm, result.2.2, result.2.1⟩

/-- A finite source-axiom catalog uses the original parsed frame/expression
objects, with no derived theorem silently admitted as a source axiom. -/
def axioms (frames : List (Spec.Frame × Spec.Expr)) (statement : Statement) : Prop :=
  ∃ frame expression, (frame, expression) ∈ frames ∧
    statement = statementOfFrame frame expression

def check (boundSort : CN → Bool) (frames : List (Spec.Frame × Spec.Expr)) : Bool :=
  frames.all fun entry => checkAxiom boundSort entry.1 entry.2

theorem check_sound {boundSort : CN → Bool} {frames : List (Spec.Frame × Spec.Expr)}
    (checked : check boundSort frames = true) :
    AxiomProfile (fun sort => boundSort sort = true) (axioms frames) := by
  have each : ∀ entry ∈ frames, checkAxiom boundSort entry.1 entry.2 = true :=
    List.all_eq_true.mp checked
  constructor
  · rintro _ ⟨frame, expression, member, rfl⟩
    exact (checked_axiom_profile (each _ member)).1
  · rintro _ ⟨frame, expression, member, rfl⟩ left right pair
    exact ((checked_axiom_profile (each _ member)).2 left right pair).1
  · rintro _ ⟨frame, expression, member, rfl⟩ left right pair
    exact ((checked_axiom_profile (each _ member)).2 left right pair).2

/-- Exact source-event membership can restrict the finite certified catalog.
This is only a syntactic subset law, not an assumed translation theorem. -/
theorem check_sound_for_subset {boundSort : CN → Bool}
    {frames : List (Spec.Frame × Spec.Expr)} {sourceAxioms : Statement → Prop}
    (checked : check boundSort frames = true)
    (sourceIncluded : ∀ statement, sourceAxioms statement → axioms frames statement) :
    AxiomProfile (fun sort => boundSort sort = true) sourceAxioms where
  noBoundConclusion statement accepted :=
    (check_sound checked).noBoundConclusion statement (sourceIncluded statement accepted)
  distinctHasBound statement accepted :=
    (check_sound checked).distinctHasBound statement (sourceIncluded statement accepted)
  mandatoryDistinct statement accepted :=
    (check_sound checked).mandatoryDistinct statement (sourceIncluded statement accepted)

end Mettapedia.Languages.Metamath.MM0Transfer.FiniteProfile
