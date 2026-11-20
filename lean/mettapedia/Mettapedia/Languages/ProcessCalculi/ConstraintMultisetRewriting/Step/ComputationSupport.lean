import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationEvolution

/-!
# Factored constant footprints for local certificate reuse

The footprint of a plugged term is the union of the fixed context's footprint
and its hole's footprint, including under binders. A submitted context cache
is checked against that context before reuse. The resulting scope check
derives the previously proved fresh-rule normality license.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSupport

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open ComputationSyntax ComputationEvolution

variable {Head : Type}

def support : {n : Nat} → Tm Head n → Finset DeclName
  | _, .var _ | _, .head _ => ∅
  | _, .const name => {name}
  | _, .pi first second | _, .sigma first second => support first ∪ support second
  | _, .id type left right => support type ∪ support left ∪ support right
  | _, .lam body => support body
  | _, .app first second | _, .pair first second => support first ∪ support second
  | _, .fst inner | _, .snd inner | _, .refl inner => support inner

theorem mem_support (name : DeclName) {n : Nat} (term : Tm Head n) :
    name ∈ support term ↔ Uses name term := by
  induction term <;> simp_all [support, Uses]

def fixed : {n m : Nat} → Context Head n m → Finset DeclName
  | _, _, .hole => ∅
  | _, _, .piDom inner sibling | _, _, .sigmaDom inner sibling |
      _, _, .appFun inner sibling | _, _, .pairFst inner sibling => fixed inner ∪ support sibling
  | _, _, .piCod sibling inner | _, _, .sigmaCod sibling inner |
      _, _, .appArg sibling inner | _, _, .pairSnd sibling inner => support sibling ∪ fixed inner
  | _, _, .idType inner left right => fixed inner ∪ support left ∪ support right
  | _, _, .idLeft type inner right => support type ∪ fixed inner ∪ support right
  | _, _, .idRight type left inner => support type ∪ support left ∪ fixed inner
  | _, _, .lam inner | _, _, .fst inner | _, _, .snd inner | _, _, .refl inner => fixed inner

theorem plug_support {n m : Nat} (context : Context Head n m) (term : Tm Head m) :
    support (context.plug term) = fixed context ∪ support term := by
  induction context <;>
    simp_all [Context.plug, support, fixed, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]

structure Cache (Head : Type) (n m : Nat) where
  context : Context Head n m
  footprint : Finset DeclName

def Cache.check {n m : Nat} (cache : Cache Head n m) : Bool := decide (cache.footprint = fixed cache.context)

def Cache.scope {n m : Nat} (cache : Cache Head n m) (term : Tm Head m) (name : DeclName) : Bool :=
  decide (name ∉ cache.footprint ∪ support term)

theorem Cache.scope_correct {n m : Nat} (cache : Cache Head n m) (valid : cache.check = true)
    (term : Tm Head m) (name : DeclName) :
    cache.scope term name = true ↔ ¬ Uses name (cache.context.plug term) := by
  have exact : cache.footprint = fixed cache.context := of_decide_eq_true valid
  simp only [Cache.scope, decide_eq_true_eq, exact, ← plug_support, ← mem_support]

theorem Cache.licenses_roots {old next : Rules Head} {n m : Nat}
    (cache : Cache Head n m) (valid : cache.check = true) (term : Tm Head m) (name : DeclName)
    (accepted : cache.scope term name = true)
    (newRules : ∀ {arity : Nat} {left right : Tm Head arity}, next.computation.step left right →
      old.computation.step left right ∨ Uses name left) :
    RootAgreementAt (old := old) (next := next) (cache.context.plug term) :=
  fresh_name_license name newRules ((cache.scope_correct valid term name).mp accepted)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSupport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSupport.plug_support
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSupport.Cache.licenses_roots
