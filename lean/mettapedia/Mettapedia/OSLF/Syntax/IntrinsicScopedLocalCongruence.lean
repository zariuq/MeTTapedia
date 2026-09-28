import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalTreeSubstitution
import Mettapedia.OSLF.Syntax.BindingCompatibleDerivations
import Mettapedia.OSLF.Syntax.PositionEnumeration
import Mettapedia.OSLF.Syntax.BoundPrefixProjection

/-!
# Constructor congruence with a rule-local output metavariable

A selected argument of any binding operator determines one conditional rule.
Its telescope contains all input arguments and a separate result for the
selected argument. The premise relates that input to that result beneath
exactly its declared binders. The other argument occurrences are unchanged.

The result metavariable is supplied by the premise, so matching the source
alone does not determine an entire occurrence. Interpretation and compatible
closure below do not assume otherwise.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalCongruence

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial

variable {S : Signature}

/-- Read an argument by its ordered occurrence, including its local scope. -/
def getArg {Γ : Ctx S} : {arity : List (MetaArity S)} →
    (args : Args S arity Γ) → (position : Fin arity.length) →
      Term S ((arity.get position).1 ++ Γ) (arity.get position).2
  | _ :: _, .cons head _, ⟨0, _⟩ => head
  | _ :: _, .cons _ tail, ⟨n + 1, bound⟩ => getArg tail ⟨n, Nat.lt_of_succ_lt_succ bound⟩

/-- Assemble an ordered argument tuple from its scope-indexed entries. -/
def tabulateArgs {Γ : Ctx S} : (arity : List (MetaArity S)) →
    ((position : Fin arity.length) →
      Term S ((arity.get position).1 ++ Γ) (arity.get position).2) → Args S arity Γ
  | [], _ => .nil
  | _ :: rest, entries => .cons (entries 0) (tabulateArgs rest (fun i => entries i.succ))

theorem tabulateArgs_getArg {Γ : Ctx S} : ∀ {arity : List (MetaArity S)}
    (args : Args S arity Γ), tabulateArgs arity (getArg args) = args
  | _, .nil => rfl
  | _, .cons head tail => congrArg (Args.cons head) (tabulateArgs_getArg tail)

theorem getArg_tabulateArgs {Γ : Ctx S} : ∀ (arity : List (MetaArity S))
    (entries : (position : Fin arity.length) →
      Term S ((arity.get position).1 ++ Γ) (arity.get position).2)
    (position : Fin arity.length), getArg (tabulateArgs arity entries) position = entries position
  | _ :: _, _, ⟨0, _⟩ => rfl
  | _ :: rest, entries, ⟨n + 1, bound⟩ =>
      getArg_tabulateArgs rest (fun i => entries i.succ) ⟨n, Nat.lt_of_succ_lt_succ bound⟩

/-- Change one argument occurrence, without comparing argument sorts. -/
def replaceArg {Γ : Ctx S} : {arity : List (MetaArity S)} →
    (args : Args S arity Γ) → (position : Fin arity.length) →
      Term S ((arity.get position).1 ++ Γ) (arity.get position).2 → Args S arity Γ
  | _ :: _, .cons _ tail, ⟨0, _⟩, replacement => .cons replacement tail
  | _ :: _, .cons head tail, ⟨n + 1, bound⟩, replacement =>
      .cons head (replaceArg tail ⟨n, Nat.lt_of_succ_lt_succ bound⟩ replacement)

theorem getArg_replaceArg {Γ : Ctx S} : ∀ {arity : List (MetaArity S)}
    (args : Args S arity Γ) (position : Fin arity.length)
    (replacement : Term S ((arity.get position).1 ++ Γ) (arity.get position).2),
    getArg (replaceArg args position replacement) position = replacement
  | _ :: _, .cons _ _, ⟨0, _⟩, _ => rfl
  | _ :: _, .cons _ tail, ⟨n + 1, bound⟩, replacement =>
      getArg_replaceArg tail ⟨n, Nat.lt_of_succ_lt_succ bound⟩ replacement

/-- Supply a metavariable with exactly its own bound variables. -/
def slot {M : List (MetaArity S)} (index : Fin M.length) :
    Term (withMetas S M) ((M.get index).1 ++ []) (M.get index).2 :=
  .op (Sum.inr (.mk index)) (prefixArgs (T := withMetas S M) (Γ := []) (M.get index).1)

def emptyClose (Γ : Ctx S) : Sub S [] Γ := fun _ var => nomatch var

/-- Joining the dependency and ambient injections is the full variable map. -/
theorem join_injections {Γ : Ctx S} : ∀ (binders : Ctx S) {Δ : Ctx S}
    (rho : Ren S (binders ++ Γ) Δ),
    ContextualAssignment.joinSub
        (fun _ v => Term.var (rho _ (injPrefix binders v)))
        (fun _ v => Term.var (rho _ (weakenVar binders v))) =
      (fun _ v => Term.var (rho _ v))
  | [], _, _ => rfl
  | _ :: binders, _, rho => by
      funext sort var
      cases var with
      | zero => rfl
      | succ old =>
          exact congrFun (congrFun
            (join_injections binders (fun _ v => rho _ (.succ v))) sort) old

/-- A contextual slot applied to its dependency variables reads back its
whole value, including all ambient variables. -/
theorem instantiate_slot {M : List (MetaArity S)} {Γ : Ctx S}
    (valuation : ContextualAssignment S M Γ) (index : Fin M.length) :
    ContextualAssignment.instantiate valuation
        (ContextualAssignment.weakenSub (M.get index).1 (fun _ v => .var v))
        (liftSub (emptyClose Γ) (M.get index).1) (slot index) = valuation index := by
  change bind (ContextualAssignment.joinSub _ _) (valuation index) = valuation index
  have arguments :
      argsToSub (ContextualAssignment.instantiateArgs valuation
        (ContextualAssignment.weakenSub (M.get index).1 (fun _ v => .var v))
        (liftSub (emptyClose Γ) (M.get index).1)
        (prefixArgs (T := withMetas S M) (Γ := []) (M.get index).1)) =
      (fun _ v => Term.var (injPrefix (Γ := Γ) (M.get index).1 v)) := by
    funext sort var
    rw [ContextualAssignment.argsToSub_instantiateArgs, argsToSub_prefixArgs]
    simp only [ContextualAssignment.instantiate, injPrefix_withMetas]
    exact liftSub_injPrefix (emptyClose Γ) (M.get index).1 var
  rw [arguments]
  change bind (ContextualAssignment.joinSub
    (fun _ v => Term.var (injPrefix (Γ := Γ) (M.get index).1 v))
    (fun _ v => Term.var (weakenVar (M.get index).1 v))) (valuation index) = _
  rw [join_injections (M.get index).1 (fun _ v => v)]
  exact bind_id _

theorem interpret_slot {M : List (MetaArity S)} {Γ : Ctx S}
    (valuation : Valuation (M := M) (BindingCloneAlgebra.terms S) Γ)
    (index : Fin M.length) :
    interpretSchema (BindingCloneAlgebra.terms S) valuation
        (weakenEnvironment (BindingCloneAlgebra.terms S) (M.get index).1
          (fun _ v => .var v))
        ((BindingCloneAlgebra.terms S).substitution.liftEnvironment
          (emptyClose Γ) (M.get index).1) (slot index) = valuation index := by
  erw [interpretSchema_terms, weakenEnvironment_terms,
    BindingSubstitutionAlgebra.terms_liftEnvironment_eq_liftSub]
  exact instantiate_slot valuation index

abbrev telescope {sort : S.Srt} (op : S.Op sort) (position : Fin (S.arity op).length) :
    List (MetaArity S) := (S.arity op).get position :: S.arity op

def sourceArgs {sort : S.Srt} (op : S.Op sort) (position : Fin (S.arity op).length) :
    Args (withMetas S (telescope op position)) (S.arity op) [] :=
  tabulateArgs (S := withMetas S (telescope op position)) (Γ := [])
    (S.arity op) (fun index => slot (M := telescope op position) index.succ)

def targetArgs {sort : S.Srt} (op : S.Op sort) (position : Fin (S.arity op).length) :
    Args (withMetas S (telescope op position)) (S.arity op) [] :=
  replaceArg (sourceArgs op position) position (slot (M := telescope op position) ⟨0, Nat.zero_lt_succ _⟩)

/-- Generic congruence: one input occurrence changes according to one child
derivation, with a separate output value in the local telescope. -/
def rule {sort : S.Srt} (op : S.Op sort) (position : Fin (S.arity op).length) :
    LocalRule S :=
  ⟨telescope op position,
    { conclusion :=
        let lhs := Term.op (Sum.inl op) (sourceArgs op position)
        ⟨[], sort, lhs, .op (Sum.inl op) (targetArgs op position), rootPosition lhs⟩
      premises := [⟨((S.arity op).get position).1, ((S.arity op).get position).2,
        slot (M := telescope op position) position.succ,
        slot (M := telescope op position) ⟨0, Nat.zero_lt_succ _⟩⟩] }⟩

/-- Populate every input from the actual argument tuple and the result from
the selected premise's output. -/
def valuation {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (position : Fin (S.arity op).length) (args : Args S (S.arity op) Γ)
    (result : Term S (((S.arity op).get position).1 ++ Γ) ((S.arity op).get position).2) :
    ContextualAssignment S (telescope op position) Γ
  | ⟨0, _⟩ => result
  | ⟨n + 1, bound⟩ => getArg args ⟨n, Nat.lt_of_succ_lt_succ bound⟩

/-- Recover the entire ordered input tuple from the local valuation. -/
def inputs {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (position : Fin (S.arity op).length)
    (values : ContextualAssignment S (telescope op position) Γ) : Args S (S.arity op) Γ :=
  tabulateArgs (S.arity op) (fun index => values index.succ)

/-- The local valuation has exactly an input tuple and the produced result. -/
theorem valuation_recovery {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (position : Fin (S.arity op).length)
    (values : ContextualAssignment S (telescope op position) Γ) :
    valuation op position (inputs op position values) (values 0) = values := by
  funext index
  match index with
  | ⟨0, _⟩ => rfl
  | ⟨n + 1, bound⟩ =>
      exact getArg_tabulateArgs (S.arity op) (fun index => values index.succ)
        ⟨n, Nat.lt_of_succ_lt_succ bound⟩

theorem instantiateArgs_tabulate {M : List (MetaArity S)} {Γ : Ctx S}
    (values : ContextualAssignment S M Γ) : ∀ (arity : List (MetaArity S))
    (entries : (position : Fin arity.length) →
      Term (withMetas S M) ((arity.get position).1 ++ []) (arity.get position).2),
    ContextualAssignment.instantiateArgs values (fun _ v => .var v) (emptyClose Γ)
        (tabulateArgs (S := withMetas S M) arity entries) =
      tabulateArgs arity (fun position =>
        ContextualAssignment.instantiate values
          (ContextualAssignment.weakenSub (arity.get position).1 (fun _ v => .var v))
          (liftSub (emptyClose Γ) (arity.get position).1) (entries position))
  | [], _ => rfl
  | _ :: rest, entries => by
      exact congrArg (Args.cons _) (instantiateArgs_tabulate values rest (fun i => entries i.succ))

theorem instantiateArgs_replace {M : List (MetaArity S)} {Γ : Ctx S}
    (values : ContextualAssignment S M Γ) : ∀ {arity : List (MetaArity S)}
    (args : Args (withMetas S M) arity []) (position : Fin arity.length)
    (result : Term (withMetas S M) ((arity.get position).1 ++ []) (arity.get position).2),
    ContextualAssignment.instantiateArgs values (fun _ v => .var v) (emptyClose Γ)
        (replaceArg args position result) =
      replaceArg (ContextualAssignment.instantiateArgs values
        (fun _ v => .var v) (emptyClose Γ) args) position
        (ContextualAssignment.instantiate values
          (ContextualAssignment.weakenSub (arity.get position).1 (fun _ v => .var v))
          (liftSub (emptyClose Γ) (arity.get position).1) result)
  | _ :: _, .cons _ _, ⟨0, _⟩, _ => rfl
  | _ :: _, .cons _head tail, ⟨n + 1, bound⟩, result =>
      congrArg (Args.cons _) (instantiateArgs_replace values tail
        ⟨n, Nat.lt_of_succ_lt_succ bound⟩ result)

/-- The generic source schema reads exactly the supplied tuple of inputs. -/
theorem instantiate_sourceArgs {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (position : Fin (S.arity op).length) (args : Args S (S.arity op) Γ)
    (result : Term S (((S.arity op).get position).1 ++ Γ) ((S.arity op).get position).2) :
    ContextualAssignment.instantiateArgs (valuation op position args result)
      (fun _ v => .var v) (emptyClose Γ) (sourceArgs op position) = args := by
  rw [sourceArgs, instantiateArgs_tabulate]
  have entries : (fun index : Fin (S.arity op).length =>
      ContextualAssignment.instantiate (valuation op position args result)
        (ContextualAssignment.weakenSub ((S.arity op).get index).1 (fun _ v => .var v))
        (liftSub (emptyClose Γ) ((S.arity op).get index).1) (slot (M := telescope op position) index.succ)) =
      getArg args := by
    funext index
    exact instantiate_slot (valuation op position args result) index.succ
  rw [entries, tabulateArgs_getArg]

theorem instantiate_targetArgs {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (position : Fin (S.arity op).length) (args : Args S (S.arity op) Γ)
    (result : Term S (((S.arity op).get position).1 ++ Γ) ((S.arity op).get position).2) :
    ContextualAssignment.instantiateArgs (valuation op position args result)
      (fun _ v => .var v) (emptyClose Γ) (targetArgs op position) =
      replaceArg args position result := by
  rw [targetArgs, instantiateArgs_replace, instantiate_sourceArgs]
  exact congrArg (replaceArg args position)
    (instantiate_slot (valuation op position args result) ⟨0, Nat.zero_lt_succ _⟩)

/-- The source does not constrain the premise-produced output. -/
theorem source_independent_output {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (position : Fin (S.arity op).length) (args : Args S (S.arity op) Γ)
    (first second : Term S (((S.arity op).get position).1 ++ Γ) ((S.arity op).get position).2) :
    ContextualAssignment.instantiateArgs (valuation op position args first)
        (fun _ v => .var v) (emptyClose Γ) (sourceArgs op position) =
      ContextualAssignment.instantiateArgs (valuation op position args second)
        (fun _ v => .var v) (emptyClose Γ) (sourceArgs op position) :=
  (instantiate_sourceArgs op position args first).trans
    (instantiate_sourceArgs op position args second).symm

theorem produced_output_distinguishes_valuation {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (position : Fin (S.arity op).length) (args : Args S (S.arity op) Γ)
    {first second : Term S (((S.arity op).get position).1 ++ Γ) ((S.arity op).get position).2}
    (different : first ≠ second) :
    valuation op position args first ≠ valuation op position args second := by
  intro same
  exact different (congrFun same 0)

def occurrence {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (position : Fin (S.arity op).length) (args : Args S (S.arity op) Γ)
    (result : Term S (((S.arity op).get position).1 ++ Γ) ((S.arity op).get position).2) :
    Instance [rule op position] (BindingCloneAlgebra.terms S) where
  index := 0
  ambient := Γ
  valuation := valuation op position args result
  close := emptyClose Γ

theorem conclusion_occurrence {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (position : Fin (S.arity op).length) (args : Args S (S.arity op) Γ)
    (result : Term S (((S.arity op).get position).1 ++ Γ) ((S.arity op).get position).2) :
    conclusionJudgment [rule op position] (BindingCloneAlgebra.terms S)
        (occurrence op position args result) =
      (⟨Γ, sort, .op op args, .op op (replaceArg args position result)⟩ :
        Judgment (BindingCloneAlgebra.terms S)) := by
  exact congrArg (fun endpoints : Term S Γ sort × Term S Γ sort =>
    (⟨Γ, sort, endpoints⟩ : Judgment (BindingCloneAlgebra.terms S)))
    (congrArg₂ Prod.mk
      ((interpretSchema_terms (valuation op position args result)
        (fun _ v => .var v) (emptyClose Γ)
        (.op (Sum.inl op) (sourceArgs op position))).trans
        (congrArg (Term.op op) (instantiate_sourceArgs op position args result)))
      ((interpretSchema_terms (valuation op position args result)
        (fun _ v => .var v) (emptyClose Γ)
        (.op (Sum.inl op) (targetArgs op position))).trans
        (congrArg (Term.op op) (instantiate_targetArgs op position args result))))

theorem child_occurrence {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (position : Fin (S.arity op).length) (args : Args S (S.arity op) Γ)
    (result : Term S (((S.arity op).get position).1 ++ Γ) ((S.arity op).get position).2) :
    childJudgment [rule op position] (BindingCloneAlgebra.terms S)
        (occurrence op position args result) ⟨0, Nat.zero_lt_succ _⟩ =
      (⟨((S.arity op).get position).1 ++ Γ, ((S.arity op).get position).2,
        getArg args position, result⟩ : Judgment (BindingCloneAlgebra.terms S)) := by
  exact congrArg (fun endpoints :
    Term S (((S.arity op).get position).1 ++ Γ) ((S.arity op).get position).2 ×
    Term S (((S.arity op).get position).1 ++ Γ) ((S.arity op).get position).2 =>
    (⟨((S.arity op).get position).1 ++ Γ, ((S.arity op).get position).2,
      endpoints⟩ : Judgment (BindingCloneAlgebra.terms S)))
    (congrArg₂ Prod.mk
      (interpret_slot (valuation op position args result) position.succ)
      (interpret_slot (valuation op position args result) ⟨0, Nat.zero_lt_succ _⟩))

/-- The same occurrence is a selected-argument compatible derivation. -/
def compatibleAt {R : CompatibleDerivations.RootFamily S} {Γ : Ctx S} :
    {arity : List (MetaArity S)} → (args : Args S arity Γ) →
    (position : Fin arity.length) →
    (result : Term S ((arity.get position).1 ++ Γ) (arity.get position).2) →
    CompatibleDerivations.Step R (getArg args position) result →
    CompatibleDerivations.ArgsStep R args (replaceArg args position result)
  | _ :: _, .cons _ tail, ⟨0, _⟩, _, child => .head tail child
  | _ :: _, .cons head tail, ⟨n + 1, bound⟩, result, child =>
      .tail head (compatibleAt tail ⟨n, Nat.lt_of_succ_lt_succ bound⟩ result child)

#print axioms instantiate_slot
#print axioms conclusion_occurrence
#print axioms child_occurrence
#print axioms compatibleAt
#print axioms valuation_recovery
#print axioms source_independent_output

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalCongruence
