import Mettapedia.OSLF.Syntax.HereditaryBetaEtaFramework
import Mettapedia.OSLF.Syntax.HereditaryBetaEtaObject
import Mettapedia.OSLF.Syntax.HereditaryBetaEtaModel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternTermination

/-!
# Three readings of beta and eta on the candidate step

The candidate step is parametric in a category of frames acting on terms
(`Interface.Frames`). Its canonical instance `Frames.contextual` relates terms
by equality: framework binders are canonical by construction, and object
terms are data. An admitted object conversion gives a second instance,
`admitted`, whose equivalence is object beta-eta conversion
(`HereditaryBetaEtaObject.Conv`). Instantiation preserves that conversion, so
`admitted` is again a frame category and the step's definitions apply to it
unchanged.

On the canonical instance, an assignment models an observed store exactly
when the lazy instances of the two sides of every equation are convertible
by framework beta steps (`models_iff_framework_convertible`): the existing
solver already unifies modulo framework beta-eta.

The examples separate the readings.

* A stored redex and its reduct are distinct atoms under equality and one
  class under conversion (`StoredRedex.distinct`, `StoredRedex.converts`). A
  readout of the head operator separates them, so it is not a function on
  conversion classes (`StoredRedex.head_readout_not_invariant`).
* Against the stored redex `(λx. pair x x) 1`, the pattern `app F X` has its
  parts determined syntactically (`Application.redex_parts_determined`); modulo
  beta a solution with other parts exists
  (`Application.redex_parts_not_determined_modulo_beta`).
* The pattern `app F X` against the stored `pair 1 1` has no syntactic model
  in any frame, and the actual pattern driver refutes it
  (`Application.driver_refutes`). Modulo beta it is solvable
  (`Application.solvable_modulo_beta`), so the driver's refutation is not a
  refutation for the admitted frames (`Application.refutation_not_admitted`).
* The eta-expanded pattern `λx. F x` and the pattern `F` are convertible at
  every assignment (`EtaExpansion.converts`), but only `F` matches the stored
  `λx. pair x x` syntactically (`EtaExpansion.plain_model`,
  `EtaExpansion.expanded_no_model`).
* Under a binder, a parameterless hole cannot capture the bound variable
  (`BinderBody.parameterless_no_model`). The second-order hole `F[x]` has
  exactly one model (`BinderBody.second_order_unique`); its problem is a
  pattern problem, and the driver solves it (`BinderBody.second_order_solved`).
* The non-pattern problem `F[1] = pair 1 1` has four distinct models
  (`NonPattern.four_models`, `NonPattern.images_distinct`), fails the pattern
  checker (`NonPattern.not_pattern`), and has no principal answer in any
  frame (`NonPattern.no_principal_answer`). The flex-flex problem
  `F[1] = G[1]` is solvable and fails the checker, and no run of the driver
  refutes it (`FlexFlex.never_refuted`).
* The admitted frames are not trivial: distinct constants are not solvable
  (`admitted_not_trivial`, from the standard model).
* Syntactic solutions are admitted solutions
  (`admitted_models_of_contextual`), and an admitted store that is solvable
  has a solution into the frame with one parameterless metavariable per sort
  (`admitted_solvable_iff_firstOrder`), as for the canonical instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.OSLF.Binding.HereditaryBetaEtaObject

/-! ## The frame category of the admitted conversion -/

section Admitted

variable {V W : Type} {declaration : V → MetaArity sig} {target : W → MetaArity sig}

/-- Observations related by the admitted conversion, at one context and sort. -/
inductive ObservedConv : Observation sig declaration → Observation sig declaration → Prop where
  | mk {Γ : Ctx sig} {sort : Ty} {first second : Term (signature sig declaration) Γ sort} :
      Conv first second → ObservedConv ⟨Γ, sort, first⟩ ⟨Γ, sort, second⟩

theorem ObservedConv.refl : ∀ (observation : Observation sig declaration),
    ObservedConv observation observation
  | ⟨_, _, term⟩ => .mk (.refl term)

theorem ObservedConv.symm {first second : Observation sig declaration}
    (related : ObservedConv first second) : ObservedConv second first := by
  cases related with
  | mk related => exact .mk (.symm related)

theorem ObservedConv.trans {first middle last : Observation sig declaration}
    (one : ObservedConv first middle) (two : ObservedConv middle last) : ObservedConv first last := by
  cases one with
  | mk related =>
      cases two with
      | mk related' => exact .mk (.trans related related')

theorem observedConv_instantiate (assignment : Assignment declaration target)
    {first second : Observation sig declaration} (related : ObservedConv first second) :
    ObservedConv (instantiateObservation assignment first) (instantiateObservation assignment second) := by
  cases related with
  | mk related => exact .mk (conv_instantiate assignment related)

end Admitted

/-- **The frame category of the admitted conversion.** Frames, morphisms and
the action are those of `Frames.contextual`; terms are related by object
beta-eta conversion. -/
def admitted : Interface.Frames (fun F : Interface.Frames.Frame sig => Observation sig F.arity)
    (fun F G : Interface.Frames.Frame sig => Assignment F.arity G.arity) where
  E := fun first second => ObservedConv first second
  equivalence _ := ⟨ObservedConv.refl, ObservedConv.symm, ObservedConv.trans⟩
  act := fun f t => instantiateObservation f t
  id F := generator F.arity
  comp := fun g f => Assignment.compose g f
  act_id := instantiateObservation_identity
  act_comp := fun g f t => (instantiateObservation_comp f g t).symm
  preserves := fun {_ _} f {_ _} related => observedConv_instantiate f related

/-- Syntactic solutions are admitted solutions. -/
theorem admitted_models_of_contextual {F G : Interface.Frames.Frame sig}
    (assignment : Assignment F.arity G.arity) (store : EquationStore (Observation sig F.arity))
    (solved : (Interface.Frames.contextual sig).Models assignment store) :
    admitted.Models assignment store := by
  intro equation member
  have same : instantiateObservation assignment equation.1 = instantiateObservation assignment equation.2 :=
    solved equation member
  show ObservedConv (instantiateObservation assignment equation.1)
    (instantiateObservation assignment equation.2)
  rw [same]
  exact ObservedConv.refl _

theorem admitted_solvable_of_contextual {F : Interface.Frames.Frame sig}
    (store : EquationStore (Observation sig F.arity))
    (solvable : (Interface.Frames.contextual sig).Solvable store) : admitted.Solvable store := by
  obtain ⟨G, assignment, solved⟩ := solvable
  exact ⟨G, assignment, admitted_models_of_contextual assignment store solved⟩

/-- Existence never needs a higher-order helper in the admitted frames either. -/
theorem admitted_solvable_iff_firstOrder {F : Interface.Frames.Frame sig}
    (store : EquationStore (Observation sig F.arity)) :
    admitted.Solvable store ↔
      ∃ assignment : Assignment F.arity (Interface.Frames.firstOrderFrame sig).arity,
        admitted.Models assignment store :=
  Interface.Frames.solvable_iff_into (X := admitted) Interface.Frames.firstOrderFrame_weaklyTerminal store

/-- No declarations. -/
def closed (impossible : Empty) : MetaArity sig := nomatch impossible

/-! ## The canonical instance is conversion modulo framework beta-eta -/

/-- **The driver's equations are equations modulo framework conversion.** An
assignment models an observed store exactly when, at every equation, the lazy
instances of the two sides, with every metavariable occurrence an explicit
framework redex, are convertible. -/
theorem models_iff_framework_convertible {S : Signature} {V W : Type} {source : V → MetaArity S}
    {target : W → MetaArity S} (assignment : Assignment source target) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort)) :
    ContextualResidual.Models assignment (ContextualResidual.observeProblem problem) ↔
      ∀ equation ∈ problem, Relation.EqvGen HereditaryBetaEta.Contracts
        (HereditaryBetaEta.lazy assignment (HereditaryBetaEta.incl equation.1))
        (HereditaryBetaEta.lazy assignment (HereditaryBetaEta.incl equation.2)) := by
  rw [ContextualResidual.models_observeProblem]
  constructor
  · intro solved equation member
    exact (HereditaryBetaEta.convertible_lazy_iff assignment equation.1 equation.2).mpr
      (solved equation member)
  · intro converted equation member
    exact (HereditaryBetaEta.convertible_lazy_iff assignment equation.1 equation.2).mp
      (converted equation member)

/-! ## Rigid terms -/

section Rigid

variable {S : Signature} {V W : Type} {declaration : V → MetaArity S} {target : W → MetaArity S}

mutual

/-- Whether a term contains a metavariable occurrence. -/
def hasMeta : {Γ : Ctx S} → {sort : S.Srt} → Term (signature S declaration) Γ sort → Bool
  | _, _, .var _ => false
  | _, _, .op (.inl _) arguments => hasMetaArgs arguments
  | _, _, .op (.inr _) _ => true

def hasMetaArgs : {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args (signature S declaration) arities Γ → Bool
  | _, _, .nil => false
  | _, _, .cons head tail => hasMeta head || hasMetaArgs tail

end

mutual

/-- Object substitution keeps every metavariable occurrence. -/
theorem hasMeta_bind : ∀ {Γ Δ : Ctx S} {sort : S.Srt} (environment : Sub (signature S declaration) Γ Δ)
    (term : Term (signature S declaration) Γ sort), hasMeta term = true →
      hasMeta (bind environment term) = true
  | _, _, _, _, .var _, present => by cases present
  | _, _, _, environment, .op (.inl _) arguments, present => by
      show hasMetaArgs (bindArgs environment arguments) = true
      exact hasMetaArgs_bindArgs environment arguments present
  | _, _, _, _, .op (.inr _) _, _ => rfl

theorem hasMetaArgs_bindArgs : ∀ {arities : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S}
    (environment : Sub (signature S declaration) Γ Δ) (arguments : Args (signature S declaration) arities Γ),
    hasMetaArgs arguments = true → hasMetaArgs (bindArgs environment arguments) = true
  | _, _, _, _, .nil, present => by cases present
  | _, _, _, environment, .cons (bs := binders) head tail, present => by
      have split : (hasMeta head || hasMetaArgs tail) = true := present
      show (hasMeta (bind (liftSub environment binders) head) || hasMetaArgs (bindArgs environment tail)) = true
      cases inHead : hasMeta head with
      | true =>
          rw [hasMeta_bind (liftSub environment binders) head inHead]
          rfl
      | false =>
          have inTail : hasMetaArgs tail = true := by
            rw [inHead] at split
            exact split
          rw [hasMetaArgs_bindArgs environment tail inTail, Bool.or_true]

end

mutual

/-- A term without metavariable occurrences is instantiated the same way by
every assignment. -/
theorem instantiate_eq_of_noMeta : ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S declaration) Γ sort),
    hasMeta term = false → ∀ (first second : Assignment declaration target),
      instantiate first term = instantiate second term
  | _, _, .var _, _, _, _ => rfl
  | _, _, .op (.inl _) arguments, absent, first, second => by
      have same := instantiateArgs_eq_of_noMeta arguments absent first second
      simp only [instantiate, same]
  | _, _, .op (.inr _) _, absent, _, _ => by cases absent

theorem instantiateArgs_eq_of_noMeta : ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (arguments : Args (signature S declaration) arities Γ), hasMetaArgs arguments = false →
      ∀ (first second : Assignment declaration target),
        instantiateArgs first arguments = instantiateArgs second arguments
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons head tail, absent, first, second => by
      have split : (hasMeta head || hasMetaArgs tail) = false := absent
      cases inHead : hasMeta head with
      | true =>
          rw [inHead] at split
          cases split
      | false =>
          have inTail : hasMetaArgs tail = false := by
            rw [inHead] at split
            exact split
          show Args.cons (instantiate first head) (instantiateArgs first tail) =
            Args.cons (instantiate second head) (instantiateArgs second tail)
          rw [instantiate_eq_of_noMeta head inHead first second,
            instantiateArgs_eq_of_noMeta tail inTail first second]

end

end Rigid

/-! ## A stored redex -/

namespace StoredRedex

def redex : Term (signature sig closed) [] .base := app (lam (pair (.var .zero) (.var .zero))) (symbol 1)

def reduct : Term (signature sig closed) [] .base := pair (symbol 1) (symbol 1)

/-- Under equality, the stored redex is its own atom. -/
theorem distinct : redex ≠ reduct := by
  intro same
  have heads := (Term.op.inj same).1
  cases heads

/-- Under the admitted conversion, it is its reduct. -/
theorem converts : Conv redex reduct :=
  .root (.beta (pair (.var .zero) (.var .zero)) (symbol 1))

/-- Whether an observation is headed by an application. -/
def isApplication {V : Type} {declaration : V → MetaArity sig} : Observation sig declaration → Bool
  | ⟨_, _, .op (.inl (.app _ _)) _⟩ => true
  | _ => false

/-- **Reading the head of stored data is not a function on conversion classes.** -/
theorem head_readout_not_invariant :
    ObservedConv (observe redex) (observe reduct) ∧
      isApplication (observe redex) ≠ isApplication (observe reduct) :=
  ⟨.mk converts, by decide⟩

end StoredRedex

/-! ## Matching an application pattern against data -/

namespace Application

/-- A hole of function sort and a hole of base sort. -/
def holes : Bool → MetaArity sig
  | true => ([], .arrow .base .base)
  | false => ([], .base)

/-- The pattern `app F X`. -/
def applied : Term (signature sig holes) [] .base :=
  app (.op (.inr (.mk true)) .nil) (.op (.inr (.mk false)) .nil)

def stored : Term (signature sig holes) [] .base := pair (symbol 1) (symbol 1)

def problem : ContextualResidual.Problem holes := [(observe applied, observe stored)]

theorem no_syntactic_model {Next : Type} (next : Next → MetaArity sig) (candidate : Assignment holes next) :
    ¬ ContextualResidual.Models candidate problem := by
  intro solved
  have same : app (instantiate candidate (.op (.inr (.mk true)) .nil))
      (instantiate candidate (.op (.inr (.mk false)) .nil)) = pair (symbol 1) (symbol 1) :=
    (ContextualResidual.models_observed_iff candidate applied stored).mp solved
  have heads := (Term.op.inj same).1
  cases heads

theorem patterned : ContextualPatternFragment.ProblemPattern problem :=
  (ContextualPatternFragment.checkProblem_iff problem).mp (by decide +kernel)

/-- **The actual pattern driver refutes the application pattern.** -/
theorem driver_refutes :
    ∃ fuel proof, ContextualFrameWorklist.run fuel holes problem = .refuted proof :=
  ContextualPatternTermination.refutes_of_no_model problem patterned no_syntactic_model

/-- `F := λx. pair x x` and `X := 1`. -/
def betaWitness : Assignment holes closed
  | true => lam (pair (.var .zero) (.var .zero))
  | false => symbol 1

theorem witness_converts :
    Conv (instantiate betaWitness applied) (instantiate betaWitness stored) :=
  .root (.beta (pair (.var .zero) (.var .zero)) (symbol 1))

/-- **Modulo beta, the refuted problem is solvable.** -/
theorem solvable_modulo_beta : admitted.Solvable (a := ⟨Bool, holes⟩) problem := by
  refine ⟨⟨Empty, closed⟩, betaWitness, ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  show ObservedConv (observe (instantiate betaWitness applied)) (observe (instantiate betaWitness stored))
  exact ObservedConv.mk witness_converts

/-- **The driver's refutation is not a refutation for the admitted frames.** -/
theorem refutation_not_admitted :
    (∃ fuel proof, ContextualFrameWorklist.run fuel holes problem = .refuted proof) ∧
      admitted.Solvable (a := ⟨Bool, holes⟩) problem :=
  ⟨driver_refutes, solvable_modulo_beta⟩

/-- The stored redex `(λx. pair x x) 1`. -/
def storedRedex : Term (signature sig holes) [] .base := app (lam (pair (.var .zero) (.var .zero))) (symbol 1)

def redexProblem : ContextualResidual.Problem holes := [(observe applied, observe storedRedex)]

/-- **Syntactically, matching determines the parts of a stored redex.** -/
theorem redex_parts_determined {Next : Type} {next : Next → MetaArity sig} (assignment : Assignment holes next)
    (same : instantiate assignment applied = instantiate assignment storedRedex) :
    instantiate assignment (.op (.inr (.mk true)) .nil : Term (signature sig holes) [] (.arrow .base .base)) =
        lam (pair (.var .zero) (.var .zero)) ∧
      instantiate assignment (.op (.inr (.mk false)) .nil : Term (signature sig holes) [] .base) = symbol 1 := by
  have parts := Args.cons.inj (eq_of_heq (Term.op.inj same).2)
  exact ⟨parts.1, (Args.cons.inj parts.2).1⟩

/-- `F := λx. pair 1 1` and `X := 7`. -/
def constantWitness : Assignment holes closed
  | true => lam (pair (symbol 1) (symbol 1))
  | false => symbol 7

/-- Modulo beta, a solution with different parts. -/
theorem constant_witness_converts :
    Conv (instantiate constantWitness applied) (instantiate constantWitness storedRedex) :=
  .trans (.root (.beta (pair (symbol 1) (symbol 1)) (symbol 7)))
    (.symm (.root (.beta (pair (.var .zero) (.var .zero)) (symbol 1))))

/-- **Modulo beta, matching does not determine the parts of a stored redex.**
The constant witness solves the problem modulo beta, but its argument part is
`7`, not the stored `1`, so it is not a syntactic solution. -/
theorem redex_parts_not_determined_modulo_beta :
    admitted.Solvable (a := ⟨Bool, holes⟩) redexProblem ∧
      instantiate constantWitness (.op (.inr (.mk false)) .nil : Term (signature sig holes) [] .base) ≠
        symbol 1 := by
  refine ⟨⟨⟨Empty, closed⟩, constantWitness, ?_⟩, ?_⟩
  · intro equation member
    obtain rfl := List.mem_singleton.mp member
    show ObservedConv (observe (instantiate constantWitness applied))
      (observe (instantiate constantWitness storedRedex))
    exact ObservedConv.mk constant_witness_converts
  · intro same
    have heads : Sum.inl (Op.symbol 7) = Sum.inl (Op.symbol 1) := (Term.op.inj same).1
    have numbers := Op.symbol.inj (Sum.inl.inj heads)
    omega

end Application

/-- **The admitted frames are not trivial.** Two distinct constants are not
solvable modulo the conversion, in any frame. -/
theorem admitted_not_trivial :
    ¬ admitted.Solvable (a := ⟨Empty, closed⟩)
      [(observe (symbol (declaration := closed) (Γ := []) 1),
        observe (symbol (declaration := closed) (Γ := []) 2))] := by
  rintro ⟨G, assignment, solved⟩
  have converted : ObservedConv (observe (symbol (declaration := G.arity) (Γ := []) 1))
      (observe (symbol (declaration := G.arity) (Γ := []) 2)) :=
    solved _ (List.mem_singleton_self _)
  cases converted with
  | mk related => exact Mettapedia.OSLF.Binding.HereditaryBetaEtaModel.symbols_not_convertible (by decide) related

/-! ## An eta-expanded pattern -/

namespace EtaExpansion

def hole (_ : Unit) : MetaArity sig := ([], .arrow .base .base)

/-- The pattern `F`. -/
def plain : Term (signature sig hole) [] (.arrow .base .base) := .op (.inr (.mk ())) .nil

/-- The pattern `λx. F x`. -/
def expanded : Term (signature sig hole) [] (.arrow .base .base) := lam (app (weaken plain) (.var .zero))

def stored : Term (signature sig hole) [] (.arrow .base .base) := lam (pair (.var .zero) (.var .zero))

/-- **Eta expansion of a pattern is invisible to the admitted conversion.** -/
theorem converts {Next : Type} {next : Next → MetaArity sig} (assignment : Assignment hole next) :
    Conv (instantiate assignment expanded) (instantiate assignment plain) := by
  unfold expanded
  rw [instantiate_lam, instantiate_app, instantiate_weaken]
  exact .root (.eta _)

def plainModel : Assignment hole closed := fun _ => lam (pair (.var .zero) (.var .zero))

/-- The plain pattern matches the stored function syntactically. -/
theorem plain_model : instantiate plainModel plain = instantiate plainModel stored := rfl

/-- **The eta-expanded pattern does not.** -/
theorem expanded_no_model {Next : Type} {next : Next → MetaArity sig} (assignment : Assignment hole next) :
    instantiate assignment expanded ≠ instantiate assignment stored := by
  intro same
  have unfolded : lam (app (instantiate assignment (weaken plain)) (.var .zero)) =
      lam (pair (.var .zero) (.var .zero)) := same
  have bodies := (Args.cons.inj (eq_of_heq (Term.op.inj unfolded).2)).1
  have heads := (Term.op.inj bodies).1
  cases heads

end EtaExpansion

/-! ## A hole under a binder -/

namespace BinderBody

/-- A parameterless base hole, and a base hole with one base parameter. -/
def holes : Bool → MetaArity sig
  | true => ([], .base)
  | false => ([.base], .base)

/-- `λx. B`. -/
def parameterless : Term (signature sig holes) [] (.arrow .base .base) := lam (.op (.inr (.mk true)) .nil)

/-- `λx. F[x]`. -/
def secondOrder : Term (signature sig holes) [] (.arrow .base .base) :=
  lam (.op (.inr (.mk false)) (.cons (.var .zero) .nil))

def stored : Term (signature sig holes) [] (.arrow .base .base) := lam (pair (.var .zero) (.var .zero))

def fromEmpty {T : Signature} {Δ : Ctx T} : Ren T [] Δ := fun _ position => nomatch position

theorem bind_fromEmpty {T : Signature} {Δ : Ctx T} {sort : T.Srt} (sigma : Sub T [] Δ)
    (term : Term T [] sort) : bind sigma term = rename fromEmpty term := by
  rw [← bind_var_eq_rename]
  congr 1
  funext _ position
  nomatch position

/-- **A parameterless hole cannot capture the bound variable.** -/
theorem parameterless_no_model {Next : Type} {next : Next → MetaArity sig}
    (assignment : Assignment holes next) :
    instantiate assignment parameterless ≠ instantiate assignment stored := by
  intro same
  have bodies : bind (argsToSub (S := signature sig next) (bs := []) (Γ := [Ty.base]) Args.nil)
      (assignment true) = pair (.var .zero) (.var .zero) :=
    (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1
  have emptied : bind (argsToSub (S := signature sig next) (bs := []) (Γ := [Ty.base]) Args.nil)
      (assignment true) = rename fromEmpty (assignment true) := bind_fromEmpty _ _
  have zero : countVar (S := signature sig next) (Var.zero : Var [Ty.base] Ty.base)
      (rename fromEmpty (assignment true)) = 0 :=
    countVar_rename_of_miss fromEmpty Var.zero (fun _ position => nomatch position) (assignment true)
  have counted : countVar (S := signature sig next) (Var.zero : Var [Ty.base] Ty.base)
      (rename fromEmpty (assignment true)) = 2 :=
    (congrArg (countVar (S := signature sig next) (Var.zero : Var [Ty.base] Ty.base))
      (emptied.symm.trans bodies)).trans rfl
  omega

def secondOrderModel : Assignment holes closed
  | true => symbol 0
  | false => pair (.var .zero) (.var .zero)

theorem second_order_model :
    instantiate secondOrderModel secondOrder = instantiate secondOrderModel stored := rfl

/-- **The second-order hole has exactly one model.** -/
theorem second_order_unique {Next : Type} {next : Next → MetaArity sig}
    (assignment : Assignment holes next)
    (same : instantiate assignment secondOrder = instantiate assignment stored) :
    assignment false = pair (.var .zero) (.var .zero) := by
  have bodies : bind (argsToSub (S := signature sig next) (bs := [Ty.base]) (Γ := [Ty.base])
      (Args.cons (Term.var Var.zero) Args.nil)) (assignment false) = pair (.var .zero) (.var .zero) :=
    (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1
  have spine : argsToSub (S := signature sig next) (bs := [Ty.base]) (Γ := [Ty.base])
      (Args.cons (Term.var Var.zero) Args.nil) = fun _ position => Term.var position := by
    funext _ position
    cases position with
    | zero => rfl
    | succ position => nomatch position
  rw [spine] at bodies
  exact (bind_id (assignment false)).symm.trans bodies

def secondOrderProblem : ContextualResidual.Problem holes := [(observe secondOrder, observe stored)]

theorem second_order_patterned : ContextualPatternFragment.ProblemPattern secondOrderProblem :=
  (ContextualPatternFragment.checkProblem_iff secondOrderProblem).mp (by decide +kernel)

/-- **The driver solves the second-order binder problem.** -/
theorem second_order_solved :
    ∃ fuel, ∃ update : ContextualFrameUpdate.Update secondOrderProblem,
      ContextualFrameWorklist.run fuel holes secondOrderProblem = .residual update ∧
        update.remaining = [] := by
  obtain ⟨fuel, solved | refused⟩ :=
    ContextualPatternTermination.solves_or_refutes secondOrderProblem second_order_patterned
  · obtain ⟨update, computed, empty, _, _⟩ := solved
    exact ⟨fuel, update, computed, empty⟩
  · obtain ⟨proof, _⟩ := refused
    exact absurd ((ContextualResidual.models_observed_iff secondOrderModel secondOrder stored).mpr
      second_order_model) (proof closed secondOrderModel)

end BinderBody

/-! ## Outside the pattern fragment -/

namespace NonPattern

def hole (_ : Unit) : MetaArity sig := ([.base], .base)

/-- `F[1]`: the hole applied to a constant. -/
def applied : Term (signature sig hole) [] .base := .op (.inr (.mk ())) (.cons (symbol 1) .nil)

def stored : Term (signature sig hole) [] .base := pair (symbol 1) (symbol 1)

/-- The images `pair x x`, `pair x 1`, `pair 1 x` and `pair 1 1`. -/
def image (first second : Bool) : Term (signature sig closed) [.base] .base :=
  pair (if first then .var .zero else symbol 1) (if second then .var .zero else symbol 1)

def model (first second : Bool) : Assignment hole closed := fun _ => image first second

theorem four_models (first second : Bool) :
    instantiate (model first second) applied = instantiate (model first second) stored := by
  cases first <;> cases second <;> rfl

theorem images_distinct :
    ∀ first second first' second' : Bool,
      image first second = image first' second' → first = first' ∧ second = second' := by
  decide

theorem not_pattern : ContextualPatternFragment.check applied = false := by decide +kernel

/-- **No principal answer.** The non-pattern problem has no solution through
which every solution factors, in any frame: its solutions are not the
instances of one most general solution. -/
theorem no_principal_answer {M : Type} {middle : M → MetaArity sig} (answer : Assignment hole middle) :
    ¬ ContextualFrameUnifier.Principal [(applied, stored)] answer := by
  intro principal
  have sound : bind (argsToSub (S := signature sig middle) (bs := [Ty.base]) (Γ := [])
      (Args.cons (symbol 1) Args.nil)) (answer ()) = pair (symbol 1) (symbol 1) :=
    principal.sound _ (List.mem_singleton_self _)
  have rigid : hasMeta (answer ()) = false := by
    cases computed : hasMeta (answer ()) with
    | false => rfl
    | true =>
        have kept := hasMeta_bind (argsToSub (S := signature sig middle) (bs := [Ty.base]) (Γ := [])
          (Args.cons (symbol 1) Args.nil)) (answer ()) computed
        rw [sound] at kept
        cases kept
  have solves (first second : Bool) :
      ContextualFrameUnifier.Models (model first second) [(applied, stored)] := by
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    exact four_models first second
  obtain ⟨one, oneFactors⟩ := principal.factors closed (model true true) (solves true true)
  obtain ⟨two, twoFactors⟩ := principal.factors closed (model false false) (solves false false)
  have same : image true true = image false false :=
    (oneFactors ()).trans ((instantiate_eq_of_noMeta (answer ()) rigid one two).trans (twoFactors ()).symm)
  exact absurd (images_distinct true true false false same) (by decide)

end NonPattern

namespace FlexFlex

def holes (_ : Bool) : MetaArity sig := ([.base], .base)

/-- `F[1] = G[1]`. -/
def left : Term (signature sig holes) [] .base := .op (.inr (.mk true)) (.cons (symbol 1) .nil)
def right : Term (signature sig holes) [] .base := .op (.inr (.mk false)) (.cons (symbol 1) .nil)

def problem : ContextualResidual.Problem holes := [(observe left, observe right)]

def model : Assignment holes closed := fun _ => symbol 7

theorem solvable : ContextualResidual.Models model problem :=
  (ContextualResidual.models_observed_iff model left right).mpr rfl

theorem not_pattern : ContextualPatternFragment.checkProblem problem = false := by decide +kernel

/-- **No run of the driver refutes the flex-flex problem.** -/
theorem never_refuted (fuel : Nat) :
    ∀ proof, ContextualFrameWorklist.run fuel holes problem ≠ .refuted proof :=
  fun proof _ => proof closed model solvable

end FlexFlex

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms admitted
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms admitted_models_of_contextual
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms admitted_solvable_iff_firstOrder
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms StoredRedex.distinct
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms StoredRedex.converts
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms StoredRedex.head_readout_not_invariant
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms Application.driver_refutes
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms Application.solvable_modulo_beta
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms Application.refutation_not_admitted
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms EtaExpansion.converts
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms EtaExpansion.plain_model
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms EtaExpansion.expanded_no_model
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms BinderBody.parameterless_no_model
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms BinderBody.second_order_unique
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms BinderBody.second_order_solved
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms NonPattern.four_models
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms NonPattern.images_distinct
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms NonPattern.not_pattern
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms FlexFlex.not_pattern
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms FlexFlex.never_refuted
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms models_iff_framework_convertible
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms NonPattern.no_principal_answer
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms Application.redex_parts_determined
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms Application.redex_parts_not_determined_modulo_beta
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BetaEtaReadings in
#print axioms admitted_not_trivial
