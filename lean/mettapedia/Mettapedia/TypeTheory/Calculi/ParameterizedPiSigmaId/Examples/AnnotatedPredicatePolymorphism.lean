import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicatePolymorphismBoundary

/-!
# Polymorphism and explicit specialization controls

One formed source context permits the same polymorphic variable at a ground
type and its function type. A fixed-carrier lexical reading cannot read both
applications. The two separately specialized identities do have readings in
the same lexical environment, at their distinct simple function types.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.AnnotatedPredicatePolymorphism
open Mettapedia.Logic
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
namespace Boundary
export PolymorphismBoundary (sourceContext sourceContext_formed at_base at_function_type type_and_function_type_cannot_both_apply)
end Boundary

def rules : Rules Nat where
  headTyping h u := u = h + 1
  isUniverse u := 0 < u
  join u v w := w = max u v
  cumulative u v := u ≤ v
  headEq h k := h = k

def church : ChurchRules rules := .empty rules (fun _ => rfl)

theorem formed_source : CCtxFormed church (Boundary.sourceContext 1) :=
  Boundary.sourceContext_formed church 1 2 rfl (by change 0 < 1; decide) (by change 0 < 2; decide) rfl rfl

theorem source_at_ground : CTyped church (Boundary.sourceContext 1)
    (.app (.var 0) (.head 0)) (CTm.inst0 (.head 0) (.pi (.var 0) (.var 1))) :=
  Boundary.at_base church 0 1 rfl

theorem source_at_function : CTyped church (Boundary.sourceContext 1)
    (.app (.var 0) (.pi (.head 0) (.head 0)))
    (CTm.inst0 (.pi (.head 0) (.head 0)) (.pi (.var 0) (.var 1))) :=
  Boundary.at_function_type church 0 1 rfl (by change 0 < 1; decide) rfl

abbrev Base := Unit
def Symbol (_ : HOL.Ty Base) : Type := Empty
def element : HOL.Ty Base := .base ()

def lexical : LexicalReading Nat Base Symbol where
  constCode? _ := none
  headCode? h := if h = 0 then some ⟨.arr element .prop,HOL.PredicateProducts.full element⟩
    else if h = 1 then some ⟨.arr (.arr element .prop) .prop,HOL.PredicateProducts.full (.arr element .prop)⟩
    else none

theorem no_joint_shallow_reading (target : HOL.Ty Base) :
    ¬ ((∃ result, ∃ code : HOL.Term Symbol [target] result,
        Reads lexical (.app (.var 0) (.head 0)) code) ∧
      (∃ result, ∃ code : HOL.Term Symbol [target] result,
        Reads lexical (.app (.var 0) (.pi (.head 0) (.head 0))) code)) :=
  Boundary.type_and_function_type_cannot_both_apply 0
    (HOL.weakenCtx [target] (HOL.PredicateProducts.full element)) (.head rfl) (.head rfl)

def specializedIdentity {n : Nat} (type : CTm Nat n) : CTm Nat n := .lam type (.var 0)

def polymorphicIdentity : CTm Nat 0 := .lam (.head 1) (.lam (.var 0) (.var 0))

private theorem identityBody_typed : CTyped church (.snoc .nil (.head 1))
    (.lam (.var 0) (.var 0)) (.pi (.var 0) (.var 1)) := by
  apply CDerivable.lamIntro (CDerivable.var 0) (by change 0 < 1; decide)
    (CDerivable.piForm (CDerivable.var 0) (by change 0 < 1; decide)
      (CDerivable.var 1) (by change 0 < 1; decide) (show rules.join 1 1 1 from rfl))
    (by change 0 < 1; decide)
  exact CDerivable.var 0

theorem polymorphic_identity_typed : CTyped church .nil polymorphicIdentity
    (PolymorphismBoundary.polymorphicType 1) :=
  .lamIntro (.headType rfl) (by change 0 < 2; decide)
    (PolymorphismBoundary.polymorphicType_formed church 1 2 rfl
      (by change 0 < 1; decide) (by change 0 < 2; decide) rfl rfl)
    (by change 0 < 2; decide) identityBody_typed

theorem specialize_at_ground : CEqual church .nil (.app polymorphicIdentity (.head 0))
    (specializedIdentity (.head 0)) (.pi (.head 0) (.head 0)) :=
  .betaPi (PolymorphismBoundary.polymorphicType_formed church 1 2 rfl
    (by change 0 < 1; decide) (by change 0 < 2; decide) rfl rfl)
    (by change 0 < 2; decide) identityBody_typed (.headType rfl)

theorem specialize_at_function : CEqual church .nil
    (.app polymorphicIdentity (.pi (.head 0) (.head 0)))
    (specializedIdentity (.pi (.head 0) (.head 0)))
    (.pi (.pi (.head 0) (.head 0)) (.pi (.head 0) (.head 0))) :=
  .betaPi (PolymorphismBoundary.polymorphicType_formed church 1 2 rfl
    (by change 0 < 1; decide) (by change 0 < 2; decide) rfl rfl)
    (by change 0 < 2; decide) identityBody_typed
    (.piForm (.headType rfl) (by change 0 < 1; decide) (.headType rfl)
      (by change 0 < 1; decide) (show rules.join 1 1 1 from rfl))

theorem ground_identity_read : Reads (Γ := []) lexical (specializedIdentity (.head 0) : CTm Nat 0)
    (.lam (.var .vz) : HOL.ClosedTerm Symbol (.arr element element)) := by
  apply Reads.abstraction (.head rfl)
  exact Reads.var (HOL.Var.vz : HOL.Var [element] element)

theorem function_identity_read : Reads (Γ := []) lexical
    (specializedIdentity (.pi (.head 0) (.head 0)) : CTm Nat 0)
    (.lam (.var .vz) : HOL.ClosedTerm Symbol (.arr (.arr element element) (.arr element element))) := by
  apply Reads.abstraction (.product (.head rfl) (.head rfl))
  exact Reads.var (HOL.Var.vz : HOL.Var [.arr element element] (.arr element element))

abbrev functionContext : HOL.Ctx Base := [.arr (.arr element .prop) (.arr element element)]

theorem first_application_reads : Reads (Γ := functionContext) lexical
    (.app (.var 0) (.head 0) : CTm Nat 1)
    (.app (.var .vz) (HOL.weakenCtx functionContext (HOL.PredicateProducts.full element))) := by
  apply Reads.application ?_ (.head rfl)
  exact Reads.var (HOL.Var.vz : HOL.Var functionContext (.arr (.arr element .prop) (.arr element element)))

theorem second_application_refused :
    Reader.infer? lexical functionContext (.app (.var 0) (.pi (.head 0) (.head 0))) = none := by
  cases found : Reader.infer? lexical functionContext (.app (.var 0) (.pi (.head 0) (.head 0))) with
  | none => rfl
  | some code =>
      exact False.elim (no_joint_shallow_reading _ ⟨⟨_,_,first_application_reads⟩,
        ⟨_,_,Reader.infer?_sound _ _ _ _ _ found⟩⟩)

#print axioms formed_source
#print axioms source_at_function
#print axioms no_joint_shallow_reading
#print axioms ground_identity_read
#print axioms function_identity_read
#print axioms specialize_at_ground
#print axioms specialize_at_function
#print axioms second_application_refused
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.AnnotatedPredicatePolymorphism
