import Mettapedia.Logic.ConstraintTypes.PatternContracts

/-!
# Unshared parameters impose no check of their own

A signature's parameters constrain values only through their occurrences. If a
parameter appears exactly once, as the whole check of one input, then no other
position mentions it. Accepting that input then only requires that its value
belongs to some proper type, and the remaining checks are unaffected by how the
parameter is chosen. In a model where every value has a proper type, the
check can be replaced by the explicit wildcard without changing any answer.

The hypothesis is necessary: a value that belongs to no proper type is rejected
by the parameter and accepted by the wildcard. Values here are finite trees, so
finiteness is part of the value domain rather than something a check enforces.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.UnsharedParameters

open SymbolicTypes ScopedConstraints CheckingPatterns PatternContracts

variable {Kind : Type} {sig : CheckingPatterns.Signature Kind} {Carrier : Kind → Type}
  {Context P Q C : Type} {typeArity : C → Nat} {valueKind : Kind} {n : Nat}

/-- The parameters a checking pattern mentions. -/
def mentioned : {s : Kind} → Pattern sig P Q C typeArity s → List P
  | _, .any => []
  | _, .proper type => type.variables
  | _, .apply op arguments => (List.finRange (sig.arity op)).flatMap fun i => mentioned (arguments i)

/-- A check depends on an assignment only through the parameters it mentions. -/
theorem matches_congr (model : Model sig Carrier Context Q C typeArity)
    (left right : P → Closed Q C typeArity) {s : Kind} (pattern : Pattern sig P Q C typeArity s)
    (agree : ∀ p ∈ mentioned pattern, left p = right p) (context : Context) (subject : Carrier s) :
    Matches model left pattern context subject ↔ Matches model right pattern context subject := by
  induction pattern generalizing context with
  | any => exact ⟨fun _ => .any _ _, fun _ => .any _ _⟩
  | proper type =>
      rw [matches_proper_iff, matches_proper_iff, TypeExpr.substitute_congr left right type agree]
  | apply op arguments ih =>
      have inner : ∀ i, ∀ p ∈ mentioned (arguments i), left p = right p := fun i p member =>
        agree p (List.mem_flatMap.2 ⟨i, List.mem_finRange i, member⟩)
      rw [matches_apply_iff, matches_apply_iff]
      constructor <;> rintro ⟨branch, present, checked⟩ <;> refine ⟨branch, present, fun query member => ?_⟩
      · exact (ih query.index (inner query.index) query.context query.subject).1 (checked query member)
      · exact (ih query.index (inner query.index) query.context query.subject).2 (checked query member)

/-- The declaration with input `slot` replaced by the explicit wildcard. Its
evaluation mode is unchanged. -/
def waive (declaration : Declaration sig P Q C typeArity valueKind n) (slot : Fin n) :
    Declaration sig P Q C typeArity valueKind n where
  input i := if i = slot then ⟨(declaration.input i).evaluation, .any⟩ else declaration.input i
  output := declaration.output

theorem waive_evaluation (declaration : Declaration sig P Q C typeArity valueKind n) (slot i : Fin n) :
    ((waive declaration slot).input i).evaluation = (declaration.input i).evaluation := by
  by_cases same : i = slot <;> simp [waive, same]

/-- The joint relation of one signature: one assignment fits every input and the result. -/
def Joint (model : Model sig Carrier Context Q C typeArity) (before after : Context)
    (arguments : Fin n → Carrier valueKind) (value : Carrier valueKind)
    (declaration : Declaration sig P Q C typeArity valueKind n) : Prop :=
  ∃ parameters : P → Closed Q C typeArity,
    (∀ i, Matches model parameters (declaration.input i).check before (arguments i)) ∧
      Matches model parameters declaration.output after value

/-- The entry relation of one signature: one assignment fits every input. -/
def Entry (model : Model sig Carrier Context Q C typeArity) (context : Context)
    (arguments : Fin n → Carrier valueKind)
    (declaration : Declaration sig P Q C typeArity valueKind n) : Prop :=
  ∃ parameters : P → Closed Q C typeArity,
    ∀ i, Matches model parameters (declaration.input i).check context (arguments i)

theorem allowed_iff_joint (model : Model sig Carrier Context Q C typeArity) (before after : Context)
    (arguments : Fin n → Carrier valueKind) (value : Carrier valueKind)
    (declarations : List (Declaration sig P Q C typeArity valueKind n)) :
    Allowed model before after arguments value declarations ↔
      ∃ declaration ∈ declarations, Joint model before after arguments value declaration := Iff.rfl

theorem admits_iff_entry (model : Model sig Carrier Context Q C typeArity) (context : Context)
    (arguments : Fin n → Carrier valueKind)
    (declarations : List (Declaration sig P Q C typeArity valueKind n)) :
    AdmitsInput model context arguments declarations ↔
      ∃ declaration ∈ declarations, Entry model context arguments declaration := Iff.rfl

/-- The parameter is the whole check of `slot` and occurs in no other input. -/
structure UnsharedInput (declaration : Declaration sig P Q C typeArity valueKind n)
    (slot : Fin n) (parameter : P) : Prop where
  whole : (declaration.input slot).check = .proper (.parameter parameter)
  elsewhere : ∀ i, i ≠ slot → parameter ∉ mentioned (declaration.input i).check

/-- In addition, the result does not mention the parameter. -/
structure Unshared (declaration : Declaration sig P Q C typeArity valueKind n)
    (slot : Fin n) (parameter : P) : Prop extends UnsharedInput declaration slot parameter where
  result : parameter ∉ mentioned declaration.output

theorem update_agrees [DecidableEq P] {X : Type} (parameters : P → X) (parameter : P) (value : X)
    (others : List P) (absent : parameter ∉ others) :
    ∀ q ∈ others, Function.update parameters parameter value q = parameters q := by
  intro q member
  have different : q ≠ parameter := fun same => absent (same ▸ member)
  simp [Function.update, different]

/-- Waiving a check never rejects more calls. -/
theorem waive_weakens_entry (model : Model sig Carrier Context Q C typeArity) (context : Context)
    (arguments : Fin n → Carrier valueKind) (declaration : Declaration sig P Q C typeArity valueKind n)
    (slot : Fin n) :
    Entry model context arguments declaration → Entry model context arguments (waive declaration slot) := by
  rintro ⟨parameters, inputs⟩
  refine ⟨parameters, fun i => ?_⟩
  by_cases same : i = slot
  · simp only [waive, same, if_true]; exact .any _ _
  · simp only [waive, same, if_false]; exact inputs i

/-- An unshared parameter check is exactly the wildcard on a value that has a
proper type. -/
theorem waive_entry_iff [DecidableEq P] (model : Model sig Carrier Context Q C typeArity) (context : Context)
    (arguments : Fin n → Carrier valueKind) (declaration : Declaration sig P Q C typeArity valueKind n)
    (slot : Fin n) (parameter : P) (unshared : UnsharedInput declaration slot parameter)
    (typed : ∃ type : Closed Q C typeArity, model.member context (arguments slot) type) :
    Entry model context arguments (waive declaration slot) ↔ Entry model context arguments declaration := by
  refine ⟨?_, waive_weakens_entry model context arguments declaration slot⟩
  rintro ⟨parameters, inputs⟩
  obtain ⟨type, member⟩ := typed
  refine ⟨Function.update parameters parameter type, fun i => ?_⟩
  by_cases same : i = slot
  · subst same
    rw [unshared.whole, matches_proper_iff]
    simpa [TypeExpr.substitute] using member
  · have checked := inputs i
    simp only [waive, same, if_false] at checked
    exact (matches_congr model _ _ _
      (update_agrees parameters parameter type _ (unshared.elsewhere i same)) _ _).2 checked

theorem waive_joint_iff [DecidableEq P] (model : Model sig Carrier Context Q C typeArity)
    (before after : Context) (arguments : Fin n → Carrier valueKind) (value : Carrier valueKind)
    (declaration : Declaration sig P Q C typeArity valueKind n) (slot : Fin n) (parameter : P)
    (unshared : Unshared declaration slot parameter)
    (typed : ∃ type : Closed Q C typeArity, model.member before (arguments slot) type) :
    Joint model before after arguments value (waive declaration slot) ↔
      Joint model before after arguments value declaration := by
  constructor
  · rintro ⟨parameters, inputs, output⟩
    obtain ⟨type, member⟩ := typed
    refine ⟨Function.update parameters parameter type, fun i => ?_, ?_⟩
    · by_cases same : i = slot
      · subst same
        rw [unshared.whole, matches_proper_iff]
        simpa [TypeExpr.substitute] using member
      · have checked := inputs i
        simp only [waive, same, if_false] at checked
        exact (matches_congr model _ _ _
          (update_agrees parameters parameter type _ (unshared.elsewhere i same)) _ _).2 checked
    · exact (matches_congr model _ _ _
        (update_agrees parameters parameter type _ unshared.result) _ _).2 output
  · rintro ⟨parameters, inputs, output⟩
    refine ⟨parameters, fun i => ?_, output⟩
    by_cases same : i = slot
    · simp only [waive, same, if_true]; exact .any _ _
    · simp only [waive, same, if_false]; exact inputs i

/-- The hypothesis cannot be dropped: a value with no proper type fails the
parameter check, while the wildcard accepts it. -/
theorem untyped_value_rejected (model : Model sig Carrier Context Q C typeArity) (context : Context)
    (arguments : Fin n → Carrier valueKind) (declaration : Declaration sig P Q C typeArity valueKind n)
    (slot : Fin n) (parameter : P) (unshared : UnsharedInput declaration slot parameter)
    (untyped : ¬ ∃ type : Closed Q C typeArity, model.member context (arguments slot) type) :
    ¬ Entry model context arguments declaration := by
  rintro ⟨parameters, inputs⟩
  have checked := inputs slot
  rw [unshared.whole, matches_proper_iff] at checked
  exact untyped ⟨_, checked⟩

/-- Rewriting each declaration by a relation-preserving map preserves the
call's admission and its allowed results. -/
theorem allowed_map_iff (model : Model sig Carrier Context Q C typeArity) (before after : Context)
    (arguments : Fin n → Carrier valueKind) (value : Carrier valueKind)
    (declarations : List (Declaration sig P Q C typeArity valueKind n))
    (rewrite : Declaration sig P Q C typeArity valueKind n → Declaration sig P Q C typeArity valueKind n)
    (preserves : ∀ declaration ∈ declarations,
      Joint model before after arguments value (rewrite declaration) ↔
        Joint model before after arguments value declaration) :
    Allowed model before after arguments value (declarations.map rewrite) ↔
      Allowed model before after arguments value declarations := by
  simp only [allowed_iff_joint, List.mem_map]
  constructor
  · rintro ⟨_, ⟨declaration, member, rfl⟩, joint⟩
    exact ⟨declaration, member, (preserves declaration member).1 joint⟩
  · rintro ⟨declaration, member, joint⟩
    exact ⟨rewrite declaration, ⟨declaration, member, rfl⟩, (preserves declaration member).2 joint⟩

end Mettapedia.Logic.ConstraintTypes.UnsharedParameters
