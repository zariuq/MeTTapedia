import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetRecursion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LaterArguments

/-!
# A definition by structural recursion, as it is written, has a set model

`SetRecursion.lean` gives the set model of a definition by structural recursion whose right
sides take the later arguments by abstraction. This module gives it for the equations as they
are written, with the later arguments on the left (`laterEquations`): the same value, and each
written equation holds at it.

**Telescopes in the model.** For a telescope over a context: the environment of the context
under an environment of the extension (`teleDrop`); the values of the telescope's variables
lie in its entries (`TeleSat`); an environment satisfies the extension exactly when its
restriction satisfies the context and the telescope's values lie in the entries
(`sat_extend`). The abstraction over a telescope denotes the traced graph over it
(`teleGraph`, `ev_lams`); a term applied to the telescope's variables denotes its value
applied to their values (`teleApply`, `ev_etaBody`); and the graph applied to values in the
entries gives the body there (`teleApply_teleGraph`, β over a telescope in the model). A
telescope under a substitution is read at the environment of the substituted terms
(`teleDrop_substEnv`, `teleSat_subst`, `teleApply_subst`).

**The written equations hold** (`laterEquation_valid`): at an environment of the fields and
the later arguments, the defined constant at the constructor form applied to the later
arguments has the value of the body with the recursive calls in place of the hypotheses. The
proof takes the equation of the abstracted form at the fields (`recursionEquation_valid`) and
applies both sides to the later arguments.

**The theorem** (`laterArguments_setModel`): a package with a set model and a reading of a
declared datatype with distinct constructor names at every assignment that agrees on its
names, extended by a function
defined by its written equations (structural recursion on its first argument, any later
arguments, bodies typed in their contexts), has a set model at every assignment that agrees on
the names it declares with the base assignment extended by the recursion's value. Consistency
follows (`laterArguments_no_closed_inhabitant`).

Positive example: the append of two lists and the addition of two numbers of a declared
datatype by the equations a programmer writes (`ObjectRecursiveDefinitions.lean`, in the
executable model of the MeTTa candidate). Negative example: without the typing of a body in
its context there is no instance of the theorem; `bad ⟶ suc bad` is not of this form and has
no set model (`ObjectAppendByEquations.lean`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization (ctorTele appSpine recPositions LevelModel)
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.TypeTheory.UniverseLevel (LevelOrder)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp traceApp_graph_beta)

universe u

local notation "DeclField" => TypedEquality.Normalization.Field

variable {Head : Type}

/-! ## Telescopes in the model -/

/-- The environment of the context a telescope extends, under an environment of the
extension. -/
def teleDrop : {n m : Nat} → CTele Head n m → Env.{u} m → Env.{u} n
  | _, _, .nil, η => η
  | _, _, .cons _ rest, η => teleDrop rest η ∘ Fin.succ

variable (heads : Head → ZFSet.{u}) (consts : DeclName → ZFSet.{u})

/-- The values of a telescope's variables lie in its entries. -/
def TeleSat : {n m : Nat} → CTele Head n m → Env.{u} m → Prop
  | _, _, .nil, _ => True
  | _, _, .cons A rest, η =>
      teleDrop rest η 0 ∈ ev heads consts A (teleDrop rest η ∘ Fin.succ) ∧ TeleSat rest η

/-- A trace function applied to the values of a telescope's variables, the first first. -/
noncomputable def teleApply : {n m : Nat} → CTele Head n m → ZFSet.{u} → Env.{u} m → ZFSet.{u}
  | _, _, .nil, g, _ => g
  | _, _, .cons _ rest, g, η => teleApply rest (traceApp g (teleDrop rest η 0)) η

/-- The traced graph of a family of values over a telescope, at an environment of the context
it extends. -/
noncomputable def teleGraph : {n m : Nat} → CTele Head n m → (Env.{u} m → ZFSet.{u}) →
    Env.{u} n → ZFSet.{u}
  | _, _, .nil, body, ρ => body ρ
  | _, _, .cons A rest, body, ρ =>
      traceLam (graph (ev heads consts A ρ) fun x => teleGraph rest body (extend ρ x))

/-- **An environment satisfies the extension of a context by a telescope** exactly when its
restriction satisfies the context and the telescope's values lie in the entries. -/
theorem sat_extend : ∀ {n m : Nat} (tele : CTele Head n m) (Γ : CCtx Head n) (η : Env.{u} m),
    Sat heads consts (tele.extend Γ) η ↔
      Sat heads consts Γ (teleDrop tele η) ∧ TeleSat heads consts tele η
  | _, _, .nil, _, _ => ⟨fun sat => ⟨sat, trivial⟩, fun both => both.1⟩
  | _, _, .cons A rest, Γ, η => by
    show Sat heads consts (rest.extend (Γ.snoc A)) η ↔
      Sat heads consts Γ (teleDrop rest η ∘ Fin.succ) ∧
        (teleDrop rest η 0 ∈ ev heads consts A (teleDrop rest η ∘ Fin.succ) ∧
          TeleSat heads consts rest η)
    rw [sat_extend rest (Γ.snoc A) η]
    constructor
    · rintro ⟨satSnoc, later⟩
      obtain ⟨older, newest⟩ := sat_tail heads consts satSnoc
      exact ⟨older, newest, later⟩
    · rintro ⟨older, newest, later⟩
      refine ⟨?_, later⟩
      rw [← extend_tail_head (teleDrop rest η)]
      exact (sat_snoc heads consts).mpr ⟨older, newest⟩

/-- **The abstraction over a telescope denotes the traced graph over it.** -/
theorem ev_lams : ∀ {n m : Nat} (tele : CTele Head n m) (b : CTm Head m) (ρ : Env.{u} n),
    ev heads consts (tele.lams b) ρ =
      teleGraph heads consts tele (fun η => ev heads consts b η) ρ
  | _, _, .nil, _, _ => rfl
  | _, _, .cons A rest, b, ρ => by
    show traceLam (graph (ev heads consts A ρ)
        fun x => ev heads consts (rest.lams b) (extend ρ x)) =
      traceLam (graph (ev heads consts A ρ)
        fun x => teleGraph heads consts rest (fun η => ev heads consts b η) (extend ρ x))
    congr 2
    funext x
    exact ev_lams rest b (extend ρ x)

/-- **A term applied to the variables of a telescope** denotes its value applied to their
values. -/
theorem ev_etaBody : ∀ {n m : Nat} (tele : CTele Head n m) (g : CTm Head n) (η : Env.{u} m),
    ev heads consts (tele.etaBody g) η =
      teleApply tele (ev heads consts g (teleDrop tele η)) η
  | _, _, .nil, _, _ => rfl
  | _, _, .cons A rest, g, η => by
    show ev heads consts (rest.etaBody (.app (g.rename wk) (.var 0))) η =
      teleApply rest (traceApp (ev heads consts g (teleDrop rest η ∘ Fin.succ))
        (teleDrop rest η 0)) η
    rw [ev_etaBody rest (.app (g.rename wk) (.var 0)) η]
    show teleApply rest (traceApp (ev heads consts (g.rename wk) (teleDrop rest η))
      (teleDrop rest η 0)) η = _
    rw [ev_rename]
    rfl

/-- **β over a telescope in the model**: the traced graph over a telescope, applied to values
that lie in its entries, gives the family's value there. -/
theorem teleApply_teleGraph : ∀ {n m : Nat} (tele : CTele Head n m)
    (body : Env.{u} m → ZFSet.{u}) (η : Env.{u} m), TeleSat heads consts tele η →
      teleApply tele (teleGraph heads consts tele body (teleDrop tele η)) η = body η
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons A rest, body, η, sat => by
    show teleApply rest (traceApp (traceLam (graph
        (ev heads consts A (teleDrop rest η ∘ Fin.succ))
        fun x => teleGraph heads consts rest body (extend (teleDrop rest η ∘ Fin.succ) x)))
      (teleDrop rest η 0)) η = body η
    rw [traceApp_graph_beta _ sat.1, extend_tail_head]
    exact teleApply_teleGraph rest body η sat.2

/-! ## Telescopes under substitution, in the model -/

/-- The environment of the substituted terms: the values, at an environment of a substituted
telescope's extension, of the substitution lifted along the telescope. -/
noncomputable def substEnv {n m : Nat} (tele : CTele Head n m) {k : Nat} (σ : CSub Head n k)
    (η : Env.{u} (tele.endAt k)) : Env.{u} m :=
  fun i => ev heads consts (tele.liftAlong σ i) η

/-- Under the environment of the substituted terms, the context a telescope extends has the
values of the substitution. -/
theorem teleDrop_substEnv : ∀ {n m : Nat} (tele : CTele Head n m) {k : Nat} (σ : CSub Head n k)
    (η : Env.{u} (tele.endAt k)),
    teleDrop tele (substEnv heads consts tele σ η) =
      fun i => ev heads consts (σ i) (teleDrop (tele.subst σ) η)
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons A rest, _, σ, η => by
    show teleDrop rest (substEnv heads consts rest (CTm.liftSub σ) η) ∘ Fin.succ =
      fun i => ev heads consts (σ i) (teleDrop (rest.subst (CTm.liftSub σ)) η ∘ Fin.succ)
    rw [teleDrop_substEnv rest (CTm.liftSub σ) η]
    funext i
    show ev heads consts ((σ i).rename wk) (teleDrop (rest.subst (CTm.liftSub σ)) η) = _
    rw [ev_rename]
    rfl

/-- **The values of a substituted telescope's variables lie in its entries** exactly when,
under the environment of the substituted terms, those of the telescope do. -/
theorem teleSat_subst : ∀ {n m : Nat} (tele : CTele Head n m) {k : Nat} (σ : CSub Head n k)
    (η : Env.{u} (tele.endAt k)),
    TeleSat heads consts (tele.subst σ) η ↔
      TeleSat heads consts tele (substEnv heads consts tele σ η)
  | _, _, .nil, _, _, _ => Iff.rfl
  | _, _, .cons A rest, _, σ, η => by
    have dropped := teleDrop_substEnv heads consts rest (CTm.liftSub σ) η
    have head : teleDrop rest (substEnv heads consts rest (CTm.liftSub σ) η) 0 =
        teleDrop (rest.subst (CTm.liftSub σ)) η 0 := by
      rw [dropped]
      rfl
    have tail : teleDrop rest (substEnv heads consts rest (CTm.liftSub σ) η) ∘ Fin.succ =
        fun i => ev heads consts (σ i) (teleDrop (rest.subst (CTm.liftSub σ)) η ∘ Fin.succ) := by
      rw [dropped]
      funext i
      show ev heads consts ((σ i).rename wk) (teleDrop (rest.subst (CTm.liftSub σ)) η) = _
      rw [ev_rename]
      rfl
    show (teleDrop (rest.subst (CTm.liftSub σ)) η 0 ∈
          ev heads consts (A.subst σ) (teleDrop (rest.subst (CTm.liftSub σ)) η ∘ Fin.succ) ∧
        TeleSat heads consts (rest.subst (CTm.liftSub σ)) η) ↔
      (teleDrop rest (substEnv heads consts rest (CTm.liftSub σ) η) 0 ∈
          ev heads consts A
            (teleDrop rest (substEnv heads consts rest (CTm.liftSub σ) η) ∘ Fin.succ) ∧
        TeleSat heads consts rest (substEnv heads consts rest (CTm.liftSub σ) η))
    rw [head, tail, ev_subst, teleSat_subst rest (CTm.liftSub σ) η]

/-- A trace function applied to the values of a substituted telescope's variables is the
function applied to the telescope's values under the environment of the substituted terms. -/
theorem teleApply_subst : ∀ {n m : Nat} (tele : CTele Head n m) {k : Nat} (σ : CSub Head n k)
    (g : ZFSet.{u}) (η : Env.{u} (tele.endAt k)),
    teleApply tele g (substEnv heads consts tele σ η) = teleApply (tele.subst σ) g η
  | _, _, .nil, _, _, _, _ => rfl
  | _, _, .cons A rest, _, σ, g, η => by
    have head : teleDrop rest (substEnv heads consts rest (CTm.liftSub σ) η) 0 =
        teleDrop (rest.subst (CTm.liftSub σ)) η 0 := by
      rw [teleDrop_substEnv heads consts rest (CTm.liftSub σ) η]
      rfl
    show teleApply rest (traceApp g
        (teleDrop rest (substEnv heads consts rest (CTm.liftSub σ) η) 0))
        (substEnv heads consts rest (CTm.liftSub σ) η) =
      teleApply (rest.subst (CTm.liftSub σ))
        (traceApp g (teleDrop (rest.subst (CTm.liftSub σ)) η 0)) η
    rw [head]
    exact teleApply_subst rest (CTm.liftSub σ) _ η

/-! ## The written equations in the model -/

variable {heads consts} {m : Nat} {T : DeclName} {Ξ : CTele Head 1 m} {C : CTm Head m}
  {ctors : List (DeclName × List (DeclField Head))}
  {body : (k : DeclName) → (fields : List (DeclField Head)) →
    CTm Head (Ξ.endAt (fields.length + (recPositions fields).length))}
  {R : Rules Head} {B : ChurchRules R} {v : Head} {rec f : DeclName}

/-- **A written equation holds in the model**: at an environment of the fields and the later
arguments, the defined constant at the constructor form applied to the later arguments has the
value of the body with the recursive calls in place of the hypotheses. -/
theorem laterEquation_valid (model : SetModel heads consts B)
    (names : (ctors.map (·.1)).Nodup) (reading : InductiveReading heads consts T v ctors rec)
    (abstracted : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CTyped B (methodCtx T (Ξ.pis C) fields (recPositions fields).length)
          (abstractedBody Ξ k fields (body k fields))
          ((Ξ.pis C).subst fun _ => ctorAt k fields.length (recPositions fields).length))
    (value : consts f = recursionValue heads consts T (Ξ.pis C) ctors
      fun k fields => abstractedBody Ξ k fields (body k fields))
    {i : Nat} {k : DeclName} {fields : List (DeclField Head)}
    (entry : ctors[i]? = some (k, fields))
    (η : Env.{u} ((laterTele Ξ k fields).endAt fields.length))
    (sat : Sat heads consts ((writtenTele f Ξ k fields).extend (liftCtx (ctorTele T fields)))
      η) :
    ev heads consts ((writtenTele f Ξ k fields).etaBody
        (.app (.const f) (liftTm (appSpine (.const k) (metaVars fields.length))))) η =
      ev heads consts
        ((body k fields).subst ((laterTele Ξ k fields).liftAlong (callSub f fields))) η := by
  obtain ⟨satFields, satLater⟩ :=
    (sat_extend heads consts (writtenTele f Ξ k fields) _ η).mp sat
  have atFields := recursionEquation_valid model names reading abstracted value entry
    (teleDrop (writtenTele f Ξ k fields) η) satFields
  have satBody : TeleSat heads consts (laterTele Ξ k fields)
      (substEnv heads consts (laterTele Ξ k fields) (callSub f fields) η) :=
    (teleSat_subst heads consts (laterTele Ξ k fields) (callSub f fields) η).mp satLater
  rw [ev_etaBody, atFields, ev_subst]
  show teleApply (writtenTele f Ξ k fields)
      (ev heads consts ((laterTele Ξ k fields).lams (body k fields))
        fun j => ev heads consts (callSub f fields j) (teleDrop (writtenTele f Ξ k fields) η))
      η = _
  have dropped : (fun j => ev heads consts (callSub f fields j)
        (teleDrop (writtenTele f Ξ k fields) η)) =
      teleDrop (laterTele Ξ k fields)
        (substEnv heads consts (laterTele Ξ k fields) (callSub f fields) η) :=
    (teleDrop_substEnv heads consts (laterTele Ξ k fields) (callSub f fields) η).symm
  have applied : ∀ g : ZFSet.{u}, teleApply (writtenTele f Ξ k fields) g η =
      teleApply (laterTele Ξ k fields) g
        (substEnv heads consts (laterTele Ξ k fields) (callSub f fields) η) :=
    fun g => (teleApply_subst heads consts (laterTele Ξ k fields) (callSub f fields) g η).symm
  rw [ev_lams, dropped, applied, teleApply_teleGraph heads consts _ _ _ satBody, ev_subst]
  rfl

/-! ## The theorem -/

variable {base : DeclName → ZFSet.{u}} {L : Type} [LevelOrder L]

/-- **A function defined by its written equations, by structural recursion on its first
argument, has a set model.** The package before the definition has a set model, and a reading
of the datatype, at every assignment that agrees with the base assignment on the names it
declares; the constructor names of the datatype are distinct; the defined name is new to the
package; the result family and the closed field types are
typed in it; and for each constructor the context of the body is formed, the result type is a
type there, and the body has it. The model is at every assignment that agrees, on the names
the package with the definition declares, with the base assignment extended by the value of
the recursion. -/
theorem laterArguments_setModel (levels : LevelModel R L) (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (names : (ctors.map (·.1)).Nodup)
    (readings : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
        InductiveReading heads consts T v ctors rec)
    (new : B.constantType f = none) (typeDeclared : B.constantType T ≠ none) {w : Head}
    (motive : CTyped B (.snoc .nil (.const T)) (Ξ.pis C) (.head w))
    (fieldsFormed : FieldsFormed B ctors)
    (formed : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) → CCtxFormed B (laterCtx T Ξ C k fields))
    (resultType : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CIsType B (laterCtx T Ξ C k fields) (laterResult Ξ C k fields))
    (bodies : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CTyped B (laterCtx T Ξ C k fields) (body k fields) (laterResult Ξ C k fields))
    (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, (withDefinition B f (.pi (.const T) (Ξ.pis C))
        (laterEquations f T Ξ ctors body)).constantType c ≠ none →
      consts c = Function.update base f
        (recursionValue heads base T (Ξ.pis C) ctors
          fun k fields => abstractedBody Ξ k fields (body k fields)) c) :
    SetModel heads consts
      (withDefinition B f (.pi (.const T) (Ξ.pis C)) (laterEquations f T Ξ ctors body)) := by
  have abstracted : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CTyped B (methodCtx T (Ξ.pis C) fields (recPositions fields).length)
          (abstractedBody Ξ k fields (body k fields))
          ((Ξ.pis C).subst fun _ => ctorAt k fields.length (recPositions fields).length) :=
    fun entry => abstractedBody_typed levels (formed entry) (resultType entry) (bodies entry)
  have valueAt : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
        recursionValue heads base T (Ξ.pis C) ctors
            (fun k fields => abstractedBody Ξ k fields (body k fields)) =
          recursionValue heads consts T (Ξ.pis C) ctors
            (fun k fields => abstractedBody Ξ k fields (body k fields)) :=
    fun consts agreesBase => recursionValue_congr
      (fun c declared => (agreesBase c declared).symm) typeDeclared motive fieldsFormed
      abstracted
  refine definition_setModel_of_value B baseModel new _
    (fun consts agreesBase _ => ?_) (fun consts agreesBase atDefined e member η sat => ?_)
    consts agrees
  · rw [valueAt consts agreesBase]
    exact recursionValue_mem (baseModel consts agreesBase) names (readings consts agreesBase)
      abstracted
  · obtain ⟨i, k, fields, entry, rfl⟩ := mem_laterEquations member
    exact laterEquation_valid (baseModel consts agreesBase) names (readings consts agreesBase)
      abstracted (atDefined.trans (valueAt consts agreesBase)) entry η sat

/-- **Consistency**: a closed type whose set is empty has no closed term in a package with a
function defined by its written equations. -/
theorem laterArguments_no_closed_inhabitant (levels : LevelModel R L) (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (names : (ctors.map (·.1)).Nodup)
    (readings : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
        InductiveReading heads consts T v ctors rec)
    (new : B.constantType f = none) (typeDeclared : B.constantType T ≠ none) {w : Head}
    (motive : CTyped B (.snoc .nil (.const T)) (Ξ.pis C) (.head w))
    (fieldsFormed : FieldsFormed B ctors)
    (formed : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) → CCtxFormed B (laterCtx T Ξ C k fields))
    (resultType : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CIsType B (laterCtx T Ξ C k fields) (laterResult Ξ C k fields))
    (bodies : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CTyped B (laterCtx T Ξ C k fields) (body k fields) (laterResult Ξ C k fields))
    {A : CTm Head 0}
    (empty : ∀ z, z ∉ ev heads (Function.update base f
      (recursionValue heads base T (Ξ.pis C) ctors
        fun k fields => abstractedBody Ξ k fields (body k fields))) A Fin.elim0)
    (t : CTm Head 0) :
    ¬ CTyped (withDefinition B f (.pi (.const T) (Ξ.pis C)) (laterEquations f T Ξ ctors body))
      .nil t A :=
  CDerivable.no_closed_inhabitant
    (laterArguments_setModel levels B baseModel names readings new typeDeclared motive
      fieldsFormed formed resultType bodies _ fun _ _ => rfl)
    empty t

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
