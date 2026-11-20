import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.DataEmbedding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBinders

/-!
# Finite first-order templates in the existing binder-equation language

Templates are ordinary binding terms over a finite family of zero-argument
holes. A constructed rule is an actual `ProgramBinders.Equation`. Instantiation
uses the existing contextual assignment operation, with literals retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuleBuilder

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration

abbrev FoArity (n : Nat) : Fin n → MetaArity MSig := fun _ => ([], ())
abbrev Template (n : Nat) := Term (signature MSig (FoArity n)) [] ()

def slot {n : Nat} (index : Fin n) : Template n := .op (.inr (.mk index)) .nil

def node {n : Nat} (tag : String) (children : List (Template n)) : Template n :=
  Toolkit.tupleAt (Toolkit.symAt tag :: children)

def literal {n : Nat} (datum : MClosed) : Template n := Rigid.includeTerm (FoArity n) datum

def equation {n : Nat} (lhs rhs : Template n) : ProgramBinders.Equation MSig [] () where
  Holes := Fin n
  holesEq := inferInstance
  arity := FoArity n
  lhs := lhs
  rhs := rhs

@[simp] theorem instantiate_slot {X : Type} {target : X → MetaArity MSig} {n : Nat}
    (assignment : Assignment (FoArity n) target) (index : Fin n) :
    instantiate assignment (slot index) = assignment index := by
  change bind (argsToSub (S := signature MSig target) (bs := []) (Γ := []) .nil)
    (assignment index) = _
  rw [Toolkit.argsToSub_nil, bind_id]

@[simp] theorem instantiate_literal {X : Type} {target : X → MetaArity MSig} {n : Nat}
    (assignment : Assignment (FoArity n) target) (datum : MClosed) :
    instantiate assignment (literal datum) = Rigid.includeTerm target datum :=
  Rigid.instantiate_include assignment datum

private theorem argsCons_heq {X : Type} {target : X → MetaArity MSig} {n m : Nat}
    (lengths : n = m) (first : Term (signature MSig target) [] ())
    {left : Args (signature MSig target) (List.replicate n ([], ())) []}
    {right : Args (signature MSig target) (List.replicate m ([], ())) []}
    (same : HEq left right) : HEq (Args.cons (bs := []) first left) (Args.cons (bs := []) first right) := by
  cases lengths
  have arguments : left = right := eq_of_heq same
  exact heq_of_eq (congrArg (fun rest => Args.cons (bs := []) first rest) arguments)

private theorem tuples_eq {X : Type} {target : X → MetaArity MSig} {n m : Nat}
    (lengths : n = m)
    {left : Args (signature MSig target) (List.replicate n ([], ())) []}
    {right : Args (signature MSig target) (List.replicate m ([], ())) []}
    (same : HEq left right) :
    Term.op (S := signature MSig target) (Sum.inl (MOp.tup n)) left =
      Term.op (S := signature MSig target) (Sum.inl (MOp.tup m)) right := by
  cases lengths
  have arguments : left = right := eq_of_heq same
  exact congrArg (fun fields => Term.op (S := signature MSig target) (Sum.inl (MOp.tup n)) fields) arguments

private theorem instantiate_arguments {X Y : Type} {source : X → MetaArity MSig}
    {target : Y → MetaArity MSig} (assignment : Assignment source target)
    (children : List (Term (signature MSig source) [] ())) :
    HEq (instantiateArgs assignment (Toolkit.tupleArgsAt children))
      (Toolkit.tupleArgsAt (children.map (instantiate assignment))) := by
  induction children with
  | nil => rfl
  | cons first rest ih =>
      exact argsCons_heq (List.length_map (instantiate assignment)).symm
        (instantiate assignment first) ih

theorem instantiate_tuple {X Y : Type} {source : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment source target) (children : List (Term (signature MSig source) [] ())) :
    instantiate assignment (Toolkit.tupleAt children) =
      Toolkit.tupleAt (children.map (instantiate assignment)) :=
  tuples_eq (List.length_map (instantiate assignment)).symm (instantiate_arguments assignment children)

@[simp] theorem instantiate_node {X : Type} {target : X → MetaArity MSig} {n : Nat}
    (assignment : Assignment (FoArity n) target) (tag : String) (children : List (Template n)) :
    instantiate assignment (node tag children) =
      Toolkit.tupleAt (Toolkit.symAt tag :: children.map (instantiate assignment)) :=
  instantiate_tuple assignment (Toolkit.symAt tag :: children)

def values {n : Nat} (environment : Fin n → MClosed) :
    Assignment (FoArity n) (ProgramBinders.ground MSig) :=
  fun index => Rigid.includeTerm (ProgramBinders.ground MSig) (environment index)

/-- Instantiate a template with ordinary closed source data. -/
def materialize {n : Nat} (environment : Fin n → MClosed) (template : Template n) : MClosed :=
  ProgramBinders.decode (instantiate (values environment) template)

theorem include_materialize {n : Nat} (environment : Fin n → MClosed) (template : Template n) :
    Rigid.includeTerm (ProgramBinders.ground MSig) (materialize environment template) =
      instantiate (values environment) template :=
  ProgramBinders.include_decode _

@[simp] theorem materialize_slot {n : Nat} (environment : Fin n → MClosed) (index : Fin n) :
    materialize environment (slot index) = environment index := by
  apply Rigid.include_injective (ProgramBinders.ground MSig)
  rw [include_materialize, instantiate_slot]
  rfl

@[simp] theorem materialize_literal {n : Nat} (environment : Fin n → MClosed) (datum : MClosed) :
    materialize environment (literal datum) = datum := by
  apply Rigid.include_injective (ProgramBinders.ground MSig)
  rw [include_materialize, instantiate_literal]

theorem materialize_tuple {n : Nat} (environment : Fin n → MClosed) (children : List (Template n)) :
    materialize environment (Toolkit.tupleAt children) = ctuple (children.map (materialize environment)) := by
  apply Rigid.include_injective (ProgramBinders.ground MSig)
  rw [include_materialize, instantiate_tuple, DataEmbedding.include_ctuple, List.map_map]
  apply congrArg (fun values : List (Term (signature MSig (ProgramBinders.ground MSig)) [] ()) =>
    Toolkit.tupleAt values)
  apply List.map_congr_left
  intro child _
  exact (include_materialize environment child).symm

@[simp] theorem materialize_node {n : Nat} (environment : Fin n → MClosed)
    (tag : String) (children : List (Template n)) :
    materialize environment (node tag children) = nodeC tag (children.map (materialize environment)) := by
  have head : materialize environment (Toolkit.symAt tag) = csym tag :=
    materialize_literal environment (csym tag)
  simpa only [node, nodeC, List.map_cons, head] using
    materialize_tuple environment (Toolkit.symAt tag :: children)

theorem matches_iff {n : Nat} (lhs rhs : Template n) (environment : Fin n → MClosed) (call : MClosed) :
    ProgramBinders.Matches (equation lhs rhs) call environment ↔ materialize environment lhs = call := by
  change instantiate (values environment) lhs = Rigid.includeTerm (ProgramBinders.ground MSig) call ↔ _
  rw [← include_materialize]
  exact ⟨Rigid.include_injective (ProgramBinders.ground MSig) _ _, congrArg _⟩

theorem answers_iff {n : Nat} (lhs rhs : Template n) (call answer : MClosed) :
    ProgramBinders.Answers (equation lhs rhs) call answer ↔
      ∃ environment : Fin n → MClosed,
        materialize environment lhs = call ∧ materialize environment rhs = answer := by
  constructor
  · rintro ⟨environment, matched, result⟩
    refine ⟨environment, (matches_iff lhs rhs environment call).mp matched, ?_⟩
    apply Rigid.include_injective (ProgramBinders.ground MSig)
    exact (include_materialize environment rhs).trans result
  · rintro ⟨environment, rfl, rfl⟩
    exact ⟨environment, (include_materialize environment lhs).symm,
      (include_materialize environment rhs).symm⟩

theorem instantiated_answer {n : Nat} (lhs rhs : Template n) (environment : Fin n → MClosed) :
    ProgramBinders.Answers (equation lhs rhs) (materialize environment lhs) (materialize environment rhs) := by
  refine ⟨environment, ?_, ?_⟩
  · exact (include_materialize environment lhs).symm
  · exact (include_materialize environment rhs).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuleBuilder
