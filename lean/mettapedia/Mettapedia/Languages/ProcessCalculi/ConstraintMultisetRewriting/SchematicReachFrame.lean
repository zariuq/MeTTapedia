import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachInformation
import Mettapedia.OSLF.Syntax.ContextualFamilySupport

/-!+# Semantic framing by equation dependency

An untouched occurrence may still change meaning when its shared variables
are constrained. The untouched variables below are outside the connected
component of the actual new equations in the old equation graph. Model
amalgamation preserves every reading on that untouched component. Different
model declaration families are combined explicitly rather than assumed to
have enough declarations already.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach.Frame

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W X : Type} {source : V → MetaArity S}
    (left : W → MetaArity S) (right : X → MetaArity S)

def intoLeft : Assignment left (Sum.elim left right) :=
  fun identity => generator (Sum.elim left right) (.inl identity)

def intoRight : Assignment right (Sum.elim left right) :=
  fun identity => generator (Sum.elim left right) (.inr identity)

theorem intoLeft_generatorOp {Γ : Ctx S} (identity : W)
    (arguments : Args (signature S left) ((left identity).1.map (fun sort => ([],sort))) Γ) :
    instantiate (intoLeft left right) (.op (.inr (.mk identity)) arguments) =
      Term.op (S := signature S (Sum.elim left right))
        (.inr (Operator.mk (declaration := Sum.elim left right) (Sum.inl identity)))
        (instantiateArgs (intoLeft left right) arguments) := by
  simp only [instantiate,intoLeft,generator,Mettapedia.OSLF.Binding.bind]
  exact congrArg (Term.op (S := signature S (Sum.elim left right))
    (.inr (Operator.mk (declaration := Sum.elim left right) (.inl identity))))
      (bindArgs_selfArgs (T := signature S (Sum.elim left right)) (left identity).1
        (instantiateArgs (intoLeft left right) arguments))

def intoLeftOperator : ∀ {sort : S.Srt}, Operator left sort → Operator (Sum.elim left right) sort
  | _,.mk identity => Operator.mk (declaration := Sum.elim left right) (Sum.inl identity)

theorem intoLeftOperator_key {sort : S.Srt} (operator : Operator left sort) :
    (intoLeftOperator left right operator).key = .inl operator.key := by
  cases operator
  rfl

theorem intoLeftOperator_injective {sort : S.Srt} :
    Function.Injective (intoLeftOperator left right (sort := sort)) := by
  intro first second same
  apply Operator.key_injective
  exact Sum.inl.inj (by simpa only [intoLeftOperator_key] using congrArg Operator.key same)

theorem intoLeftArity {sort : S.Srt} (operator : Operator left sort) :
    (signature S (Sum.elim left right)).arity (.inr (intoLeftOperator left right operator)) =
      (signature S left).arity (.inr operator) := by
  cases operator
  rfl

def intoLeftArguments {Γ : Ctx S} {sort : S.Srt} (operator : Operator left sort)
    (arguments : Args (signature S left) ((signature S left).arity (.inr operator)) Γ) :=
  cast (congrArg (fun arities => Args (signature S (Sum.elim left right)) arities Γ)
    (intoLeftArity left right operator).symm) (instantiateArgs (intoLeft left right) arguments)

theorem intoLeft_op {Γ : Ctx S} {sort : S.Srt} (operator : Operator left sort)
    (arguments : Args (signature S left) ((signature S left).arity (.inr operator)) Γ) :
    instantiate (intoLeft left right) (.op (.inr operator) arguments) =
      .op (.inr (intoLeftOperator left right operator)) (intoLeftArguments left right operator arguments) := by
  cases operator with
  | mk identity =>
      rw [intoLeft_generatorOp]
      congr 1

mutual

theorem intoLeft_injective : ∀ {Γ : Ctx S} {sort : S.Srt}
    (first second : Term (signature S left) Γ sort),
    instantiate (intoLeft left right) first = instantiate (intoLeft left right) second → first = second
  | _,_,.var first,.var second,same => congrArg (Term.var (S := signature S left)) (Term.var.inj (S := signature S (Sum.elim left right)) same)
  | _,_,.var _,.op (.inl _) _,same => by cases same
  | _,_,.var _,.op (.inr (.mk operator)) arguments,same => by rw [intoLeft_op] at same; cases same
  | _,_,.op (.inl _) _,.var _,same => by cases same
  | _,_,.op (.inr (.mk operator)) arguments,.var _,same => by rw [intoLeft_op] at same; cases same
  | _,_,.op (.inl operator) arguments,.op (.inl other) others,same => by
      have operators := Sum.inl.inj (Term.op.inj same).1
      subst other
      exact congrArg (Term.op (S := signature S left) (.inl operator))
        (intoLeftArgs_injective arguments others (eq_of_heq (Term.op.inj same).2))
  | _,_,.op (.inl _) _,.op (.inr (.mk operator)) arguments,same => by
      rw [intoLeft_op] at same
      cases (Term.op.inj same).1
  | _,_,.op (.inr (.mk operator)) arguments,.op (.inl _) _,same => by
      rw [intoLeft_op] at same
      cases (Term.op.inj same).1
  | _,_,.op (.inr operator) arguments,.op (.inr other) others,same => by
      rw [intoLeft_op,intoLeft_op] at same
      have identical := intoLeftOperator_injective left right (Sum.inr.inj (Term.op.inj same).1)
      subst other
      have sameArgs := (Term.op.inj same).2
      dsimp only [intoLeftArguments] at sameArgs
      have original : HEq (instantiateArgs (intoLeft left right) arguments)
          (instantiateArgs (intoLeft left right) others) :=
        (cast_heq _ _).symm.trans (sameArgs.trans (cast_heq _ _))
      exact congrArg (Term.op (S := signature S left) (.inr operator))
        (intoLeftArgs_injective arguments others (eq_of_heq original))

theorem intoLeftArgs_injective : ∀ {Γ : Ctx S} {arities : List (List S.Srt × S.Srt)}
    (first second : Args (signature S left) arities Γ),
    instantiateArgs (intoLeft left right) first = instantiateArgs (intoLeft left right) second → first = second
  | _,_,.nil,.nil,_ => rfl
  | _,_,.cons first rest,.cons second tail,same => by
      have components := Args.cons.inj same
      exact congrArg₂ Args.cons (intoLeft_injective first second components.1)
        (intoLeftArgs_injective rest tail components.2)

end

variable {left right} {Γ : Ctx S} {sort : S.Srt}

def equationSupport (equation : Equation (Term (signature S source) Γ sort)) : List V :=
  support equation.1 ++ support equation.2

def Roots (extra : EquationStore (Term (signature S source) Γ sort)) : Set V :=
  {identity | ∃ equation ∈ extra, identity ∈ equationSupport equation}

def Variables (old extra : EquationStore (Term (signature S source) Γ sort)) (identity : V) : Prop :=
  ∀ closed : Set V, Roots extra ⊆ closed →
    (∀ equation ∈ old, (∃ v ∈ equationSupport equation, v ∈ closed) →
      ∀ v ∈ equationSupport equation, v ∈ closed) → identity ∈ closed

theorem Variables.root {old extra : EquationStore (Term (signature S source) Γ sort)}
    {identity : V} (root : identity ∈ Roots extra) : Variables old extra identity :=
  fun _ contains _ => contains root

theorem variables_empty_iff {extra : EquationStore (Term (signature S source) Γ sort)} {identity : V} :
    Variables [] extra identity ↔ identity ∈ Roots extra := by
  constructor
  · intro reached
    exact reached (Roots extra) (fun _ member => member) (by simp)
  · exact Variables.root

theorem Variables.closed {old extra : EquationStore (Term (signature S source) Γ sort)}
    {equation : Equation (Term (signature S source) Γ sort)} (member : equation ∈ old)
    (touches : ∃ v ∈ equationSupport equation, Variables old extra v) :
    ∀ v ∈ equationSupport equation, Variables old extra v := by
  intro v present closed contains closure
  apply closure equation member _ v present
  obtain ⟨w,inEquation,reached⟩ := touches
  exact ⟨w,inEquation,reached closed contains closure⟩

theorem equation_separated (old extra : EquationStore (Term (signature S source) Γ sort))
    {equation : Equation (Term (signature S source) Γ sort)} (member : equation ∈ old) :
    (∀ v ∈ equationSupport equation, Variables old extra v) ∨
      (∀ v ∈ equationSupport equation, ¬ Variables old extra v) := by
  classical
  by_cases touches : ∃ v ∈ equationSupport equation, Variables old extra v
  · exact Or.inl (Variables.closed member touches)
  · exact Or.inr (fun v present reached => touches ⟨v,present,reached⟩)

noncomputable def amalgamate (old extra : EquationStore (Term (signature S source) Γ sort))
    (prior : Assignment source left) (joint : Assignment source right) :
    Assignment source (Sum.elim left right) := by
  classical
  exact fun identity => if Variables old extra identity then instantiate (intoRight left right) (joint identity)
    else instantiate (intoLeft left right) (prior identity)

theorem amalgamate_untouched (old extra : EquationStore (Term (signature S source) Γ sort))
    (prior : Assignment source left) (joint : Assignment source right)
    {context : Ctx S} {result : S.Srt} (term : Term (signature S source) context result)
    (untouched : ∀ identity ∈ support term, ¬ Variables old extra identity) :
    instantiate (amalgamate old extra prior joint) term =
      instantiate (intoLeft left right) (instantiate prior term) := by
  rw [instantiate_comp]
  apply instantiate_congr
  intro identity member
  simp only [amalgamate,untouched identity member,ite_false]

theorem amalgamate_affected (old extra : EquationStore (Term (signature S source) Γ sort))
    (prior : Assignment source left) (joint : Assignment source right)
    {context : Ctx S} {result : S.Srt} (term : Term (signature S source) context result)
    (affected : ∀ identity ∈ support term, Variables old extra identity) :
    instantiate (amalgamate old extra prior joint) term =
      instantiate (intoRight left right) (instantiate joint term) := by
  rw [instantiate_comp]
  apply instantiate_congr
  intro identity member
  simp only [amalgamate,affected identity member,ite_true]

theorem amalgamate_models {old extra : EquationStore (Term (signature S source) Γ sort)}
    {prior : Assignment source left} {joint : Assignment source right}
    (priorModel : ContextualFrameUnifier.Models prior old)
    (jointModel : ContextualFrameUnifier.Models joint (old ++ extra)) :
    ContextualFrameUnifier.Models (amalgamate old extra prior joint) (old ++ extra) := by
  have parts := (ContextualFrameUnifier.models_append joint old extra).mp jointModel
  apply (ContextualFrameUnifier.models_append _ old extra).mpr
  constructor
  · intro equation member
    rcases equation_separated old extra member with affected | untouched
    · rw [amalgamate_affected old extra prior joint equation.1 (fun v vm => affected v (List.mem_append_left _ vm)),
        amalgamate_affected old extra prior joint equation.2 (fun v vm => affected v (List.mem_append_right _ vm)),
        parts.1 equation member]
    · rw [amalgamate_untouched old extra prior joint equation.1 (fun v vm => untouched v (List.mem_append_left _ vm)),
        amalgamate_untouched old extra prior joint equation.2 (fun v vm => untouched v (List.mem_append_right _ vm)),
        priorModel equation member]
  · intro equation member
    have affected : ∀ v ∈ equationSupport equation, Variables old extra v :=
      fun v vm => Variables.root ⟨equation,member,vm⟩
    rw [amalgamate_affected old extra prior joint equation.1 (fun v vm => affected v (List.mem_append_left _ vm)),
      amalgamate_affected old extra prior joint equation.2 (fun v vm => affected v (List.mem_append_right _ vm)),
      parts.2 equation member]

def Entails (store : EquationStore (Term (signature S source) Γ sort))
    {context : Ctx S} {result : S.Srt} (first second : Term (signature S source) context result) : Prop :=
  ∀ {Future : Type} (future : Future → MetaArity S) (candidate : Assignment source future),
    ContextualFrameUnifier.Models candidate store → instantiate candidate first = instantiate candidate second

/-- Protected observations have exactly the same equality consequences.
The reverse direction constructs a model; it does not assume that the
later solver fixes the untouched variables. -/
theorem entails_iff {old extra : EquationStore (Term (signature S source) Γ sort)}
    (consistent : ContextualFrameUnifier.Solvable (old ++ extra))
    {context : Ctx S} {result : S.Srt} (first second : Term (signature S source) context result)
    (untouched : ∀ identity ∈ support first ++ support second, ¬ Variables old extra identity) :
    Entails (old ++ extra) first second ↔ Entails old first second := by
  constructor
  · intro after Future future prior model
    obtain ⟨Other,other,joint,jointModel⟩ := consistent
    have combined := after (Sum.elim future other) (amalgamate old extra prior joint)
      (amalgamate_models model jointModel)
    rw [amalgamate_untouched old extra prior joint first
      (fun v vm => untouched v (List.mem_append_left _ vm)),
      amalgamate_untouched old extra prior joint second
      (fun v vm => untouched v (List.mem_append_right _ vm))] at combined
    exact intoLeft_injective (left := future) (right := other) _ _ combined
  · intro before Future future candidate model
    exact before future candidate ((ContextualFrameUnifier.models_append candidate old extra).mp model).1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach.Frame
