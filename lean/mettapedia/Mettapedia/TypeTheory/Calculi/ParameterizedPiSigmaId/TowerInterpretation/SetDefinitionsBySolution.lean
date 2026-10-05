import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDefinitions

/-!
# A definition admitted on the evidence of a solution in sets

A definition by equations can be admitted without any check of its recursion, on evidence that
some value satisfies its equations. The evidence proves one statement written from the
definition: *some `g` of the declared type satisfies every equation, with `g` in place of the
defined name*. This module reads that statement in a set model of the package before the
definition (`SolutionStatement`) and proves that it is enough for a set model of the package
with the definition.

**From evidence to a model** (`definition_setModel_of_evidence`). Let the package before the
definition have a set model at every assignment that agrees with a base one on the names it
declares, let the defined name be new to it, and let the declared type and the equations
mention only the names declared before and the defined name (`MentionsDeclared`; a typed term
mentions only declared names, so the typing of the type and of the equations gives it). If the
statement is true at the base assignment, then for some value the package with the definition
has a set model at every assignment that agrees with the base one extended by the value. Every
`g` that satisfies the statement is such a value (`definition_setModel_of_solution`). The model
is the one of `definition_setModel_of_value`; the condition on the names carries the truth of
the statement at the base assignment to the other assignments.

**Pointwise is enough for a function result** (`equationHolds_iff_atPosition`). When the result
of the defined function is a function, the statement gives each equation at every position:
one more variable, the position, and both sides applied to it (`DefiningEquation.atPosition`).
That is the equation itself when both sides lie in the set of one function type at every
instance (the hypothesis `functions`): two trace functions of one type with the same values
are one set (`tracePiSet_ext`). The typing of the two sides gives the hypothesis: a term typed
in the package that declares the defined name at its type, with no equations, lies in its
type whenever the name is read as a member of the declared type (`typing_holds_of_mem`).

Positive examples, in the executable model of the candidate: the endless stream
`from n ⟶ scons n (from (suc n))` at `num → (num → num)`, on the evidence `λ n k. n + k` given
position by position (`Trinity/Stream/AdmittedBySetSolution.lean`), and `log2` on the evidence
of its solution in sets (`Trinity/Log2/AdmittedBySetSolution.lean`).

Negative examples:
* *Pointwise without function sides is not enough* (`atPosition_needs_functions`): `refl c` is
  read as the empty set and `c = c` as `{∅}`; applied to any position both are the empty set.
* *The value is not unique*: `spin n ⟶ spin n` is admitted on the evidence `λ n. zero`, and it
  has set models that give `spin` different values (in the module of `log2`).
* *Without evidence there is no model*: `loop n ⟶ suc (loop n)` at the numbers has no
  solution, so its statement is false and no evidence exists, and a copy of the theorem without
  the evidence is false at it (in the module of `log2`).

**What this does not give.** Nothing about running or conversion. A kernel may fire the rules of
such a definition only at closed arguments (and closed positions); that is a fact about the
kernel, and that such rules stop at closed arguments is not claimed here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain (termConsts)
open Mettapedia.Logic.HOL.Embedding
open ZFSetTraceProducts (traceApp mem_traceApp traceApp_empty)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u

variable {Head : Type} {R : Rules Head} (heads : Head → ZFSet.{u})

/-! ## The statement the evidence proves -/

/-- **An equation holds at an assignment**: its two sides have one value at every environment
of its telescope. -/
def EquationHolds (consts : DeclName → ZFSet.{u}) (e : DefiningEquation Head) : Prop :=
  ∀ η : Env.{u} e.arity, Sat heads consts e.telescope η →
    ev heads consts e.left η = ev heads consts e.right η

/-- **The statement of a solution**, read at an assignment: some member `g` of the set of the
declared type satisfies every equation with `g` in place of the defined name. -/
def SolutionStatement (consts : DeclName → ZFSet.{u}) (f : DeclName) (A : CTm Head 0)
    (eqs : List (DefiningEquation Head)) : Prop :=
  ∃ g ∈ ev heads consts A Fin.elim0, ∀ e ∈ eqs, EquationHolds heads (Function.update consts f g) e

/-- **A definition mentions only declared names**: its declared type mentions only names that
the package before it declares, and the telescope and both sides of each equation mention only
those names and the defined name. -/
structure MentionsDeclared (B : ChurchRules R) (f : DeclName) (A : CTm Head 0)
    (eqs : List (DefiningEquation Head)) : Prop where
  type : ∀ c ∈ termConsts A, B.constantType c ≠ none
  telescope : ∀ e ∈ eqs, ∀ i, ∀ c ∈ termConsts (e.telescope.lookup i),
    c = f ∨ B.constantType c ≠ none
  left : ∀ e ∈ eqs, ∀ c ∈ termConsts e.left, c = f ∨ B.constantType c ≠ none
  right : ∀ e ∈ eqs, ∀ c ∈ termConsts e.right, c = f ∨ B.constantType c ≠ none

variable {B : ChurchRules R} {f : DeclName} {A : CTm Head 0} {eqs : List (DefiningEquation Head)}

/-- **An equation of such a definition holds at every assignment that agrees on the names it
may mention.** -/
theorem MentionsDeclared.equationHolds_congr (mentions : MentionsDeclared B f A eqs)
    {consts consts' : DeclName → ZFSet.{u}}
    (same : ∀ c, c = f ∨ B.constantType c ≠ none → consts c = consts' c)
    {e : DefiningEquation Head} (member : e ∈ eqs) (holds : EquationHolds heads consts e) :
    EquationHolds heads consts' e := by
  intro η sat
  have satAt : Sat heads consts e.telescope η := fun i => by
    rw [ev_congr_consts heads consts _
      (fun c mem => same c (mentions.telescope e member i c mem)) η]
    exact sat i
  rw [← ev_congr_consts heads consts e.left (fun c mem => same c (mentions.left e member c mem)) η,
    ← ev_congr_consts heads consts e.right (fun c mem => same c (mentions.right e member c mem)) η]
  exact holds η satAt

/-! ## From evidence to a model -/

/-- **A definition has a set model at every value that satisfies its equations.** The package
before the definition has a set model at every assignment that agrees with the base assignment
on the names it declares; the defined name is new to it; the definition mentions only declared
names. If `g` lies in the set of the declared type and satisfies every equation at the base
assignment with `g` in place of the defined name, the package with the definition has a set
model at every assignment that agrees, on the names it declares, with the base assignment
extended by `g`. -/
theorem definition_setModel_of_solution (B : ChurchRules R) {base : DeclName → ZFSet.{u}}
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : B.constantType f = none) (mentions : MentionsDeclared B f A eqs) {g : ZFSet.{u}}
    (typed : g ∈ ev heads base A Fin.elim0)
    (solves : ∀ e ∈ eqs, EquationHolds heads (Function.update base f g) e)
    (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, (withDefinition B f A eqs).constantType c ≠ none →
      consts c = Function.update base f g c) :
    SetModel heads consts (withDefinition B f A eqs) :=
  definition_setModel_of_value B baseModel new g
    (fun consts agreesBase _ => by
      rwa [ev_congr_consts heads consts A (fun c mem => agreesBase c (mentions.type c mem))])
    (fun consts agreesBase atDefined e member =>
      mentions.equationHolds_congr heads (fun c named => by
        rcases named with rfl | declared
        · rw [Function.update_self, atDefined]
        · rw [Function.update_of_ne (fun same : c = f => declared (same ▸ new)),
            agreesBase c declared])
        member (solves e member))
    consts agrees

/-- **From evidence to a model.** The package before the definition has a set model at every
assignment that agrees with the base assignment on the names it declares; the defined name is
new to it; the definition mentions only declared names; and the statement of a solution is
true at the base assignment. Then for some value in the set of the declared type, the package
with the definition has a set model at every assignment that agrees, on the names it declares,
with the base assignment extended by the value. -/
theorem definition_setModel_of_evidence (B : ChurchRules R) {base : DeclName → ZFSet.{u}}
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : B.constantType f = none) (mentions : MentionsDeclared B f A eqs)
    (evidence : SolutionStatement heads base f A eqs) :
    ∃ value ∈ ev heads base A Fin.elim0, ∀ consts : DeclName → ZFSet.{u},
      (∀ c, (withDefinition B f A eqs).constantType c ≠ none →
        consts c = Function.update base f value c) →
      SetModel heads consts (withDefinition B f A eqs) := by
  obtain ⟨g, typed, solves⟩ := evidence
  exact ⟨g, typed, definition_setModel_of_solution heads B baseModel new mentions typed solves⟩

/-! ## Pointwise is enough for a function result -/

/-- **An equation read at a position**: one more variable after those of the equation, a
position in `D`, and both sides applied to it. -/
def _root_.Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated.DefiningEquation.atPosition
    (e : DefiningEquation Head) (D : CTm Head e.arity) : DefiningEquation Head where
  arity := e.arity + 1
  telescope := e.telescope.snoc D
  left := .app (e.left.rename wk) (.var 0)
  right := .app (e.right.rename wk) (.var 0)

/-- **Pointwise is enough for a function result.** When both sides of an equation lie in the set
of one function type `Π D. C` at every environment of its telescope (`functions`), the equation
holds exactly when it holds at every position in `D`. -/
theorem equationHolds_iff_atPosition {consts : DeclName → ZFSet.{u}} {e : DefiningEquation Head}
    {D : CTm Head e.arity} {C : CTm Head (e.arity + 1)}
    (functions : ∀ η : Env.{u} e.arity, Sat heads consts e.telescope η →
      ev heads consts e.left η ∈ ev heads consts (.pi D C) η ∧
        ev heads consts e.right η ∈ ev heads consts (.pi D C) η) :
    EquationHolds heads consts (e.atPosition D) ↔ EquationHolds heads consts e := by
  constructor
  · intro pointwise η sat
    obtain ⟨left, right⟩ := functions η sat
    refine tracePiSet_ext left right fun x hx => ?_
    have atX := pointwise (extend η x) ((sat_snoc heads consts).mpr ⟨sat, hx⟩)
    change traceApp (ev heads consts (e.left.rename wk) (extend η x)) x =
      traceApp (ev heads consts (e.right.rename wk) (extend η x)) x at atX
    rwa [ev_rename_wk, ev_rename_wk] at atX
  · intro holds (η : Env.{u} (e.arity + 1)) sat
    have satTail : Sat heads consts e.telescope (η ∘ wk) := fun i => by
      have member := sat i.succ
      change η i.succ ∈ ev heads consts ((e.telescope.lookup i).rename wk) η at member
      rwa [ev_rename] at member
    change traceApp (ev heads consts (e.left.rename wk) η) (η 0) =
      traceApp (ev heads consts (e.right.rename wk) η) (η 0)
    rw [ev_rename, ev_rename, holds (η ∘ wk) satTail]

/-- **Typing gives membership at every value of the declared type.** A term typed in the package
that declares the defined name at its type, with no equations, lies in its type at every
environment of its context, at the base assignment extended by any member of the declared
type. So the two sides of an equation typed at a function type satisfy `functions`. -/
theorem typing_holds_of_mem (B : ChurchRules R) {base : DeclName → ZFSet.{u}}
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : B.constantType f = none) (type : ∀ c ∈ termConsts A, B.constantType c ≠ none)
    {g : ZFSet.{u}} (typed : g ∈ ev heads base A Fin.elim0) {n : Nat} {Γ : CCtx Head n}
    {t T : CTm Head n} (derivation : CTyped (withDefinition B f A []) Γ t T) :
    Holds heads (Function.update base f g) (.typing Γ t T) :=
  CDerivable.sound (definition_setModel_of_solution heads B baseModel new (eqs := [])
    ⟨type, (fun _ member => nomatch member), (fun _ member => nomatch member),
      (fun _ member => nomatch member)⟩
    typed (fun _ member => nomatch member) _ fun _ _ => rfl) derivation

/-- The equation `refl c = (c = c)`, with no variables. -/
def reflTruthEquation (c : DeclName) : DefiningEquation Head where
  arity := 0
  telescope := .nil
  left := .refl (.const c)
  right := .id (.const c) (.const c) (.const c)

/-- Negative example: **pointwise without function sides is not enough.** `refl c` is read as
the empty set and `c = c` as `{∅}`. Applied to any position both give the empty set, since
neither holds a pair; so the equation holds at every position, and it does not hold. -/
theorem atPosition_needs_functions (consts : DeclName → ZFSet.{u}) (c : DeclName)
    (D : CTm Head 0) :
    EquationHolds heads consts ((reflTruthEquation c).atPosition D) ∧
      ¬ EquationHolds heads consts (reflTruthEquation c) := by
  have truth : truthCode.{u} (consts c = consts c) = {∅} := by
    apply ZFSet.ext
    intro z
    rw [mem_truthCode, ZFSet.mem_singleton]
    exact ⟨And.left, fun empty => ⟨empty, rfl⟩⟩
  refine ⟨fun (η : Env.{u} 1) _ => ?_, fun holds => ?_⟩
  · change traceApp ∅ (η 0) = traceApp (truthCode (consts c = consts c)) (η 0)
    rw [traceApp_empty, truth]
    apply ZFSet.ext
    intro z
    rw [mem_traceApp, ZFSet.mem_singleton]
    refine ⟨fun h => absurd h (ZFSet.notMem_empty z), fun pairEmpty => ?_⟩
    have member : ({η 0} : ZFSet.{u}) ∈ ZFSet.pair (η 0) z := ZFSet.mem_pair.mpr (Or.inl rfl)
    rw [pairEmpty] at member
    exact absurd member (ZFSet.notMem_empty _)
  · have equal := holds Fin.elim0 (sat_nil heads consts Fin.elim0)
    change (∅ : ZFSet.{u}) = truthCode (consts c = consts c) at equal
    rw [truth] at equal
    have member : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
    rw [← equal] at member
    exact ZFSet.notMem_empty _ member

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
