import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.Substitution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# Literal native data in contextual families and finite substitution environments

Closed native encodings can be included in any family of hosted metavariables.
The inclusion keeps every tuple field and commutes with changing that family.
Finite substitution arrays use the existing raw algorithm with an explicit
lookup; scoped inputs never inspect the default outside the array.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.DataEmbedding

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration

def closedArguments : (length : Nat) → Args MSig (List.replicate length ([], ())) [] → List MClosed
  | 0, .nil => []
  | length + 1, .cons first rest => first :: closedArguments length rest

def tupleContents : MClosed → Option (List MClosed)
  | .op (.tup length) arguments => some (closedArguments length arguments)
  | _ => none

theorem closedArguments_ctupleArgs (children : List MClosed) :
    closedArguments children.length (ctupleArgs children) = children := by
  induction children with
  | nil => rfl
  | cons first rest ih => exact congrArg (List.cons first) ih

@[simp] theorem tupleContents_ctuple (children : List MClosed) :
    tupleContents (ctuple children) = some children :=
  congrArg some (closedArguments_ctupleArgs children)

theorem ctuple_injective : Function.Injective ctuple := by
  intro first second same
  have read := congrArg tupleContents same
  simpa only [tupleContents_ctuple, Option.some.injEq] using read

private def symbolContents : MClosed → Option String
  | .op (.sym name) _ => some name
  | _ => none

theorem nodeC_eq_iff {first second : String} {left right : List MClosed} :
    nodeC first left = nodeC second right ↔ first = second ∧ left = right := by
  constructor
  · intro same
    have lists := ctuple_injective same
    obtain ⟨heads, tails⟩ := List.cons.inj lists
    exact ⟨Option.some.inj (congrArg symbolContents heads), tails⟩
  · rintro ⟨rfl, rfl⟩
    rfl

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

private theorem include_arguments {X : Type} (target : X → MetaArity MSig) (children : List MClosed) :
    HEq (Rigid.includeArgs target (ctupleArgs children))
      (Toolkit.tupleArgsAt (children.map (Rigid.includeTerm target))) := by
  induction children with
  | nil => rfl
  | cons first rest ih =>
      exact argsCons_heq (List.length_map (Rigid.includeTerm target)).symm
        (Rigid.includeTerm target first) ih

theorem include_ctuple {X : Type} (target : X → MetaArity MSig) (children : List MClosed) :
    Rigid.includeTerm target (ctuple children) =
      Toolkit.tupleAt (children.map (Rigid.includeTerm target)) := by
  exact tuples_eq (List.length_map (Rigid.includeTerm target)).symm (include_arguments target children)

theorem include_nodeC {X : Type} (target : X → MetaArity MSig)
    (tag : String) (children : List MClosed) :
    Rigid.includeTerm target (nodeC tag children) =
      Toolkit.tupleAt (Toolkit.symAt tag :: children.map (Rigid.includeTerm target)) :=
  include_ctuple target (csym tag :: children)

theorem include_nodeD (tag : String) (children : List MClosed) :
    Rigid.includeTerm (fam mkeys) (nodeC tag children) =
      nodeD tag (children.map (Rigid.includeTerm (fam mkeys))) := by
  have arguments : ∀ values : List MData, Toolkit.tupleArgsAt values = tupleArgs values := by
    intro values
    induction values with
    | nil => rfl
    | cons first rest ih => exact congrArg (Args.cons (bs := []) first) ih
  rw [include_nodeC]
  unfold Toolkit.tupleAt nodeD tuple
  rw [arguments]
  rfl

theorem encoded_equality_reflected {X : Type} (target : X → MetaArity MSig)
    {n : Nat} {first second : Tower.Tm n}
    (same : Rigid.includeTerm target (encodeTm first) = Rigid.includeTerm target (encodeTm second)) :
    first = second := encodeTm_injective (Rigid.include_injective target _ _ same)

theorem encoded_meta_support_empty {X : Type} (target : X → MetaArity MSig)
    {n : Nat} (term : Tower.Tm n) : support (Rigid.includeTerm target (encodeTm term)) = [] :=
  Rigid.support_include target _

theorem instantiate_encoded {X Y : Type} {source : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment source target) {n : Nat} (term : Tower.Tm n) :
    instantiate assignment (Rigid.includeTerm source (encodeTm term)) =
      Rigid.includeTerm target (encodeTm term) :=
  Rigid.instantiate_include assignment _

def rawEnvironment {n m : Nat} (substitution : Sub Tower.Head n m) : List (NativeSyntax.Raw Tower.Head) :=
  List.ofFn (fun index : Fin n => rawTm (substitution index))

def rawLookup (environment : List (NativeSyntax.Raw Tower.Head)) (index : Nat) : NativeSyntax.Raw Tower.Head :=
  environment[index]?.getD (.const .anonymous)

theorem rawLookup_environment {n m : Nat} (substitution : Sub Tower.Head n m) (index : Fin n) :
    rawLookup (rawEnvironment substitution) index.val = rawTm (substitution index) := by
  simp [rawLookup, rawEnvironment, index.isLt]

theorem finite_substitution {n m : Nat} (substitution : Sub Tower.Head n m) (term : Tower.Tm n) :
    quoteRaw (NativeSyntax.substRaw (rawLookup (rawEnvironment substitution)) (rawTm term)) =
      encodeTm (subst substitution term) :=
  quoteRaw_subst substitution _ (rawLookup_environment substitution) term

theorem outside_lookup_is_not_a_scoped_variable {m : Nat}
    (substitution : Sub Tower.Head 0 m) :
    rawLookup (rawEnvironment substitution) 0 = .const .anonymous ∧
      ¬ ∃ index : Fin 0, index.val = 0 := by
  exact ⟨rfl, fun ⟨index, _⟩ => Fin.elim0 index⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.DataEmbedding
