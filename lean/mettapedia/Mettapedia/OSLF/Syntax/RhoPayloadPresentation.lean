import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionModels
import Mettapedia.OSLF.Syntax.PositionEnumeration

/-!
# The reflective calculus with payload binding

An input binds the process it receives. The received name is the quotation
of that process variable, and dropping the received name is the process
variable itself. Communication therefore instantiates the continuation at
the payload, and ordinary substitution performs the reflective substitution
of the calculus: name occurrences become the quoted payload and drops of the
received name become the payload.

A quotation of closed code contains no variable, so substitution leaves it
unchanged. A name built from an open payload in an open context is the
quotation of an open term and follows substitution, as reduction stability
under substitution requires. The name equation is quote/drop cancellation.
A drop of a quotation is inert in the strict profile; the book profile adds
its execution as a separate rule.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open CategoryTheory.Limits
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

/-- Names and processes. -/
inductive Srt where
  | nm
  | pr
  deriving DecidableEq, Repr

/-- The term formers. A free name is a constant; `inp` binds a process. -/
inductive Op : Srt → Type where
  | nil : Op Srt.pr
  | par : Op Srt.pr
  | out : Op Srt.pr
  | inp : Op Srt.pr
  | drp : Op Srt.pr
  | quo : Op Srt.nm
  | free : String → Op Srt.nm

/-- The input former opens its continuation under the received process. -/
abbrev sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} o => match o with
    | .nil => []
    | .par => [([], Srt.pr), ([], Srt.pr)]
    | .out => [([], Srt.nm), ([], Srt.pr)]
    | .inp => [([], Srt.nm), ([Srt.pr], Srt.pr)]
    | .drp => [([], Srt.nm)]
    | .quo => [([], Srt.pr)]
    | .free _ => []

/-- The continuation of communication: a process open in one process. -/
abbrev metas : List (MetaArity sig) := [([Srt.pr], Srt.pr)]

abbrev schemaSig : Signature := withMetas sig metas

section Terms

variable {Γ : Ctx sig}

def nilT : Term sig Γ Srt.pr := .op Op.nil .nil

def parT (left right : Term sig Γ Srt.pr) : Term sig Γ Srt.pr :=
  .op Op.par (.cons left (.cons right .nil))

def outT (channel : Term sig Γ Srt.nm) (payload : Term sig Γ Srt.pr) :
    Term sig Γ Srt.pr :=
  .op Op.out (.cons channel (.cons payload .nil))

def inpT (channel : Term sig Γ Srt.nm)
    (body : Term sig (Srt.pr :: Γ) Srt.pr) : Term sig Γ Srt.pr :=
  .op Op.inp (.cons channel (.cons body .nil))

def drpT (name : Term sig Γ Srt.nm) : Term sig Γ Srt.pr :=
  .op Op.drp (.cons name .nil)

def quoT (process : Term sig Γ Srt.pr) : Term sig Γ Srt.nm :=
  .op Op.quo (.cons process .nil)

def freeT (label : String) : Term sig Γ Srt.nm :=
  .op (Op.free label) .nil

/-- The name received by the nearest input. -/
def received : Term sig (Srt.pr :: Γ) Srt.nm :=
  quoT (.var .zero)

end Terms

section Schema

variable {Γ : Ctx schemaSig}

private def sPar (left right : Term schemaSig Γ Srt.pr) :
    Term schemaSig Γ Srt.pr :=
  .op (Sum.inl Op.par) (.cons left (.cons right .nil))

private def sOut (channel : Term schemaSig Γ Srt.nm)
    (payload : Term schemaSig Γ Srt.pr) : Term schemaSig Γ Srt.pr :=
  .op (Sum.inl Op.out) (.cons channel (.cons payload .nil))

private def sInp (channel : Term schemaSig Γ Srt.nm)
    (body : Term schemaSig (Srt.pr :: Γ) Srt.pr) : Term schemaSig Γ Srt.pr :=
  .op (Sum.inl Op.inp) (.cons channel (.cons body .nil))

private def sDrp (name : Term schemaSig Γ Srt.nm) : Term schemaSig Γ Srt.pr :=
  .op (Sum.inl Op.drp) (.cons name .nil)

private def sQuo (process : Term schemaSig Γ Srt.pr) :
    Term schemaSig Γ Srt.nm :=
  .op (Sum.inl Op.quo) (.cons process .nil)

private def sNil : Term schemaSig Γ Srt.pr :=
  .op (Sum.inl Op.nil) .nil

/-- The continuation metavariable applied to a process. -/
private def cont (argument : Term schemaSig Γ Srt.pr) :
    Term schemaSig Γ Srt.pr :=
  .op (Sum.inr (MetaOp.mk (M := metas) 0)) (.cons argument .nil)

/-- The variables of communication: a channel and an emitted process. -/
private abbrev commCtx : Ctx sig := [Srt.nm, Srt.pr]

/-- `n!(q) | for(p <- n) K[p]`. -/
private def commLhs : Term schemaSig commCtx Srt.pr :=
  sPar (sOut (.var .zero) (.var (.succ .zero)))
    (sInp (.var .zero) (cont (.var .zero)))

/-- `K[q]`: the continuation receives the payload itself. -/
private def commRhs : Term schemaSig commCtx Srt.pr :=
  cont (.var (.succ .zero))

/-- Communication. -/
def comm : Rule sig metas where
  conclusion := {
    ctx := commCtx
    sort := Srt.pr
    lhs := commLhs
    rhs := commRhs
    position := rootPosition commLhs }
  premises := []

private abbrev congCtx : Ctx sig := [Srt.pr, Srt.pr, Srt.pr]

private def parCongLhs : Term schemaSig congCtx Srt.pr :=
  sPar (.var .zero) (.var (.succ (.succ .zero)))

private def parCongRhs : Term schemaSig congCtx Srt.pr :=
  sPar (.var (.succ .zero)) (.var (.succ (.succ .zero)))

/-- A step of one parallel component, with the rest unchanged. -/
def parCong : Rule sig metas where
  conclusion := {
    ctx := congCtx
    sort := Srt.pr
    lhs := parCongLhs
    rhs := parCongRhs
    position := rootPosition parCongLhs }
  premises := [{
    binders := []
    sort := Srt.pr
    source := .var .zero
    target := .var (.succ .zero) }]

private abbrev dropCtx : Ctx sig := [Srt.pr]

private def dropLhs : Term schemaSig dropCtx Srt.pr :=
  sDrp (sQuo (.var .zero))

/-- The book's extra rule: a dropped quotation executes its code. -/
def drop : Rule sig metas where
  conclusion := {
    ctx := dropCtx
    sort := Srt.pr
    lhs := dropLhs
    rhs := .var .zero
    position := rootPosition dropLhs }
  premises := []

/-- Commutativity of parallel composition. -/
def commPar : EqAxiom sig metas where
  ctx := [Srt.pr, Srt.pr]
  sort := Srt.pr
  lhs := sPar (.var .zero) (.var (.succ .zero))
  rhs := sPar (.var (.succ .zero)) (.var .zero)

/-- Associativity of parallel composition. -/
def assocPar : EqAxiom sig metas where
  ctx := [Srt.pr, Srt.pr, Srt.pr]
  sort := Srt.pr
  lhs := sPar (sPar (.var .zero) (.var (.succ .zero))) (.var (.succ (.succ .zero)))
  rhs := sPar (.var .zero) (sPar (.var (.succ .zero)) (.var (.succ (.succ .zero))))

/-- The null process is a unit of parallel composition. -/
def unitPar : EqAxiom sig metas where
  ctx := [Srt.pr]
  sort := Srt.pr
  lhs := sPar (.var .zero) sNil
  rhs := .var .zero

/-- Quote/drop cancellation: quoting the drop of a name is that name. -/
def quoteDrop : EqAxiom sig metas where
  ctx := [Srt.nm]
  sort := Srt.nm
  lhs := sQuo (sDrp (.var .zero))
  rhs := .var .zero

end Schema

/-- The equations: parallel composition is a commutative monoid, and names
satisfy quote/drop cancellation. -/
abbrev equations : List (EqAxiom sig metas) :=
  [commPar, assocPar, unitPar, quoteDrop]

/-- The strict core: communication and parallel congruence. -/
abbrev strictRules : List (Rule sig metas) := [comm, parCong]

/-- The book's profile adds the execution of a dropped quotation. -/
abbrev bookRules : List (Rule sig metas) := [comm, parCong, drop]

/-- The strict reflective calculus as an initial substitution-compatible
operational model. -/
noncomputable def strictInitial :
    IsInitial (SubstitutionOperationalModel.presented strictRules equations) :=
  SubstitutionOperationalModel.presentedIsInitial strictRules equations

/-- The book's profile as an initial substitution-compatible operational
model. -/
noncomputable def bookInitial :
    IsInitial (SubstitutionOperationalModel.presented bookRules equations) :=
  SubstitutionOperationalModel.presentedIsInitial bookRules equations

#print axioms strictInitial
#print axioms bookInitial

/-! ## Equation instances -/

section EquationInstances

variable {Γ : Ctx sig}

/-- The substitution closing the one name of the quote/drop equation. -/
private def singleName (m : Term sig Γ Srt.nm) : Sub sig [Srt.nm] Γ
  | _, .zero => m

/-- A body for the continuation metavariable; the name equation does not
mention it. -/
private def someBody : (k : Fin metas.length) → Term sig (metas.get k).1 (metas.get k).2
  | ⟨0, _⟩ => .var .zero

/-- Quote/drop cancellation, as an instance of the presented equation. -/
theorem quoteDrop_equiv (m : Term sig Γ Srt.nm) :
    EqClosure equations (quoT (drpT m)) m :=
  EqClosure.ax (E := equations) (Γ := Γ) 3 someBody (singleName m)

theorem equiv_drpT {a b : Term sig Γ Srt.nm} (h : EqClosure equations a b) :
    EqClosure equations (drpT a) (drpT b) := by
  unfold drpT
  exact EqClosure.cong (E := equations) Op.drp (.cons h .nil)

theorem equiv_quoT {a b : Term sig Γ Srt.pr} (h : EqClosure equations a b) :
    EqClosure equations (quoT a) (quoT b) := by
  unfold quoT
  exact EqClosure.cong (E := equations) Op.quo (.cons h .nil)

theorem equiv_parT {a a' b b' : Term sig Γ Srt.pr}
    (ha : EqClosure equations a a') (hb : EqClosure equations b b') :
    EqClosure equations (parT a b) (parT a' b') := by
  unfold parT
  exact EqClosure.cong (E := equations) Op.par (.cons ha (.cons hb .nil))

theorem equiv_outT {c c' : Term sig Γ Srt.nm} {a a' : Term sig Γ Srt.pr}
    (hc : EqClosure equations c c') (ha : EqClosure equations a a') :
    EqClosure equations (outT c a) (outT c' a') := by
  unfold outT
  exact EqClosure.cong (E := equations) Op.out (.cons hc (.cons ha .nil))

theorem equiv_inpT {c c' : Term sig Γ Srt.nm} {K K' : Term sig (Srt.pr :: Γ) Srt.pr}
    (hc : EqClosure equations c c') (hK : EqClosure equations K K') :
    EqClosure equations (inpT c K) (inpT c' K') := by
  unfold inpT
  exact EqClosure.cong (E := equations) Op.inp (.cons hc (.cons hK .nil))

private def pairProcs (a b : Term sig Γ Srt.pr) : Sub sig [Srt.pr, Srt.pr] Γ
  | _, .zero => a
  | _, .succ .zero => b

private def tripleProcs (a b c : Term sig Γ Srt.pr) : Sub sig [Srt.pr, Srt.pr, Srt.pr] Γ
  | _, .zero => a
  | _, .succ .zero => b
  | _, .succ (.succ .zero) => c

private def singleProc (a : Term sig Γ Srt.pr) : Sub sig [Srt.pr] Γ
  | _, .zero => a

theorem parT_comm (a b : Term sig Γ Srt.pr) :
    EqClosure equations (parT a b) (parT b a) :=
  EqClosure.ax (E := equations) (Γ := Γ) 0 someBody (pairProcs a b)

theorem parT_assoc (a b c : Term sig Γ Srt.pr) :
    EqClosure equations (parT (parT a b) c) (parT a (parT b c)) :=
  EqClosure.ax (E := equations) (Γ := Γ) 1 someBody (tripleProcs a b c)

theorem parT_nil (a : Term sig Γ Srt.pr) : EqClosure equations (parT a nilT) a :=
  EqClosure.ax (E := equations) (Γ := Γ) 2 someBody (singleProc a)

theorem nil_parT (a : Term sig Γ Srt.pr) : EqClosure equations (parT nilT a) a :=
  (parT_comm nilT a).trans (parT_nil a)

theorem parT_swap (a b c : Term sig Γ Srt.pr) :
    EqClosure equations (parT a (parT b c)) (parT b (parT a c)) :=
  (parT_assoc a b c).symm.trans
    ((equiv_parT (parT_comm a b) (.refl c)).trans (parT_assoc b a c))

end EquationInstances

/-! ## Firings over terms

Both profiles begin with communication and parallel congruence, so their
occurrences are shared. -/

section Firings

open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

variable (rest : List (Rule sig metas))

/-- The continuation, as the value of the one metavariable. -/
def continuation {Γ : Ctx sig} (K : Term sig (Srt.pr :: Γ) Srt.pr) :
    Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ
  | ⟨0, _⟩ => K

/-- The channel and the emitted process of a communication. -/
def commClose {Γ : Ctx sig} (channel : Term sig Γ Srt.nm)
    (payload : Term sig Γ Srt.pr) : Sub sig [Srt.nm, Srt.pr] Γ
  | _, .zero => channel
  | _, .succ .zero => payload

/-- The stepping component, its reduct and the unchanged component. -/
def parCongClose {Γ : Ctx sig} (source target other : Term sig Γ Srt.pr) :
    Sub sig [Srt.pr, Srt.pr, Srt.pr] Γ
  | _, .zero => source
  | _, .succ .zero => target
  | _, .succ (.succ .zero) => other

/-- A communication in any ambient context. -/
def commOccurrence {Γ : Ctx sig} (channel : Term sig Γ Srt.nm)
    (payload : Term sig Γ Srt.pr) (K : Term sig (Srt.pr :: Γ) Srt.pr) :
    Instance (comm :: parCong :: rest) (BindingCloneAlgebra.terms sig) where
  index := ⟨0, by simp⟩
  ambient := Γ
  valuation := continuation K
  close := commClose channel payload

/-- A parallel congruence in any ambient context. -/
def parCongOccurrence {Γ : Ctx sig} (source target other : Term sig Γ Srt.pr) :
    Instance (comm :: parCong :: rest) (BindingCloneAlgebra.terms sig) where
  index := ⟨1, by simp⟩
  ambient := Γ
  valuation := continuation (.var .zero)
  close := parCongClose source target other

/-- The identity environment beneath the received process. -/
private def receivedIdentity (Γ : Ctx sig) : Sub sig (Srt.pr :: Γ) (Srt.pr :: Γ) :=
  joinEnvironment
    (fun _ var => match var with
      | .zero => Term.var Var.zero
      | .succ old => nomatch old : Sub sig [Srt.pr] (Srt.pr :: Γ))
    (fun _ var => Term.var (.succ var) : Sub sig Γ (Srt.pr :: Γ))

private theorem receivedIdentity_bind (Γ : Ctx sig) (K : Term sig (Srt.pr :: Γ) Srt.pr) :
    bind (receivedIdentity Γ) K = K := by
  have identity : receivedIdentity Γ = (fun _ var => Term.var var) := by
    funext sort var
    cases var with
    | zero => rfl
    | succ _ => rfl
  rw [identity]
  exact bind_id K

theorem commConclusion {Γ : Ctx sig} (channel : Term sig Γ Srt.nm)
    (payload : Term sig Γ Srt.pr) (K : Term sig (Srt.pr :: Γ) Srt.pr) :
    conclusionJudgment (comm :: parCong :: rest) (BindingCloneAlgebra.terms sig)
        (commOccurrence rest channel payload K) =
      (⟨Γ, Srt.pr, parT (outT channel payload) (inpT channel K), inst K payload⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  have lhs : interpretSchema (BindingCloneAlgebra.terms sig) (continuation K)
      (fun _ var => Term.var var) (commClose channel payload) commLhs =
        parT (outT channel payload) (inpT channel (bind (receivedIdentity Γ) K)) := rfl
  have rhs : interpretSchema (BindingCloneAlgebra.terms sig) (continuation K)
      (fun _ var => Term.var var) (commClose channel payload) commRhs =
        inst K payload := by
    unfold inst
    change bind _ K = bind (extend payload) K
    congr 1
    funext sort var
    cases var with
    | zero => rfl
    | succ _ => rfl
  change (⟨Γ, Srt.pr,
      interpretSchema (BindingCloneAlgebra.terms sig) (continuation K)
        (fun _ var => Term.var var) (commClose channel payload) commLhs,
      interpretSchema (BindingCloneAlgebra.terms sig) (continuation K)
        (fun _ var => Term.var var) (commClose channel payload) commRhs⟩ :
      Judgment (BindingCloneAlgebra.terms sig)) = _
  rw [lhs, rhs, receivedIdentity_bind]

theorem parCongConclusion {Γ : Ctx sig} (source target other : Term sig Γ Srt.pr) :
    conclusionJudgment (comm :: parCong :: rest) (BindingCloneAlgebra.terms sig)
        (parCongOccurrence rest source target other) =
      (⟨Γ, Srt.pr, parT source other, parT target other⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := rfl

theorem parCongChild {Γ : Ctx sig} (source target other : Term sig Γ Srt.pr)
    (position : Fin ((comm :: parCong :: rest).get
      (parCongOccurrence rest source target other).index).premises.length) :
    childJudgment (comm :: parCong :: rest) (BindingCloneAlgebra.terms sig)
        (parCongOccurrence rest source target other) position =
      (⟨Γ, Srt.pr, source, target⟩ : Judgment (BindingCloneAlgebra.terms sig)) := by
  have atZero : position = ⟨0, Nat.zero_lt_one⟩ := by
    apply Fin.ext
    have bounded : position.val < 1 := position.isLt
    change position.val = 0
    omega
  subst position
  rfl

/-- Communication fires in every ambient context. -/
theorem comm_reduces {Γ : Ctx sig} (channel : Term sig Γ Srt.nm)
    (payload : Term sig Γ Srt.pr) (K : Term sig (Srt.pr :: Γ) Srt.pr) :
    Reduces (comm :: parCong :: rest)
      (⟨Γ, Srt.pr, parT (outT channel payload) (inpT channel K), inst K payload⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  have base := reduces_ruleClosed (comm :: parCong :: rest)
    (commOccurrence rest channel payload K) (by intro position; nomatch position)
  exact (congrArg (Reduces (comm :: parCong :: rest))
    (commConclusion rest channel payload K)).mp base

/-- A step of one parallel component is a step of the composition. -/
theorem parCong_reduces {Γ : Ctx sig} {source target : Term sig Γ Srt.pr}
    (other : Term sig Γ Srt.pr)
    (child : Reduces (comm :: parCong :: rest)
      (⟨Γ, Srt.pr, source, target⟩ : Judgment (BindingCloneAlgebra.terms sig))) :
    Reduces (comm :: parCong :: rest)
      (⟨Γ, Srt.pr, parT source other, parT target other⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) :=
  reduces_ruleClosed (comm :: parCong :: rest)
    (parCongOccurrence rest source target other)
    (fun position => (congrArg (Reduces (comm :: parCong :: rest))
      (parCongChild rest source target other position)).mpr child)

/-- A dropped quotation in any ambient context. -/
def dropOccurrence {Γ : Ctx sig} (code : Term sig Γ Srt.pr) :
    Instance bookRules (BindingCloneAlgebra.terms sig) where
  index := ⟨2, by simp⟩
  ambient := Γ
  valuation := continuation (.var .zero)
  close := fun _ var => match var with
    | .zero => code

/-- In the book's profile a dropped quotation runs its code. -/
theorem drop_reduces {Γ : Ctx sig} (code : Term sig Γ Srt.pr) :
    Reduces bookRules
      (⟨Γ, Srt.pr, drpT (quoT code), code⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) :=
  reduces_ruleClosed bookRules (dropOccurrence code)
    (by intro position; nomatch position)

end Firings

/-! ## Steps between equation classes

The presented model's carrier is the quotient by the equations. A step there
between two processes is a firing tree of the presented model between their
classes. -/

section Classes

open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

/-- The quotient of terms by the equations of the calculus. -/
noncomputable abbrev classes : FreeBindingClone.Hom (BindingCloneAlgebra.terms sig)
    (FreeBindingEquationModel.presented equations).algebra :=
  BindingEquationQuotientModel.projection equations

/-- A step of the presented calculus between the classes of two processes:
some firing tree of the presented model has exactly these endpoints. -/
def Steps (R : List (Rule sig metas)) {Γ : Ctx sig}
    (source target : Term sig Γ Srt.pr) : Prop :=
  Reduces R (A := (FreeBindingEquationModel.presented equations).algebra)
    (mapJudgment classes
      (⟨Γ, Srt.pr, source, target⟩ : Judgment (BindingCloneAlgebra.terms sig)))

variable {R : List (Rule sig metas)} {Γ : Ctx sig}

theorem steps_of_reduces {source target : Term sig Γ Srt.pr}
    (reduces : Reduces R
      (⟨Γ, Srt.pr, source, target⟩ : Judgment (BindingCloneAlgebra.terms sig))) :
    Steps R source target :=
  reduces_map R classes reduces

/-- Steps are between equation classes. -/
theorem steps_of_equiv {source source' target target' : Term sig Γ Srt.pr}
    (hsource : EqClosure equations source source')
    (htarget : EqClosure equations target' target)
    (step : Steps R source' target') : Steps R source target := by
  have hs : classes.raw.map source = classes.raw.map source' := Quotient.sound hsource
  have ht : classes.raw.map target' = classes.raw.map target := Quotient.sound htarget
  unfold Steps at step ⊢
  simp only [mapJudgment] at step ⊢
  rw [hs, ← ht]
  exact step

variable (rest : List (Rule sig metas))

/-- Communication is a step of either profile. -/
theorem steps_comm (channel : Term sig Γ Srt.nm) (payload : Term sig Γ Srt.pr)
    (K : Term sig (Srt.pr :: Γ) Srt.pr) :
    Steps (comm :: parCong :: rest) (parT (outT channel payload) (inpT channel K))
      (inst K payload) :=
  steps_of_reduces (comm_reduces rest channel payload K)

/-- Parallel congruence acts on steps between classes. -/
theorem steps_parCong {source target : Term sig Γ Srt.pr} (other : Term sig Γ Srt.pr)
    (child : Steps (comm :: parCong :: rest) source target) :
    Steps (comm :: parCong :: rest) (parT source other) (parT target other) := by
  let occurrence := mapInstance (comm :: parCong :: rest) classes
    (parCongOccurrence rest source target other)
  have conclusion : conclusionJudgment (comm :: parCong :: rest) _ occurrence =
      mapJudgment classes
        (⟨Γ, Srt.pr, parT source other, parT target other⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) :=
    (mapInstance_conclusion (comm :: parCong :: rest) classes _).trans
      (congrArg (mapJudgment classes) (parCongConclusion rest source target other))
  have children : ∀ position : Fin ((comm :: parCong :: rest).get
      occurrence.index).premises.length,
      Reduces (comm :: parCong :: rest)
        (childJudgment (comm :: parCong :: rest) _ occurrence position) := by
    intro position
    have child' := (mapInstance_child (comm :: parCong :: rest) classes
      (parCongOccurrence rest source target other) position).trans
        (congrArg (mapJudgment classes) (parCongChild rest source target other position))
    exact (congrArg (Reduces (comm :: parCong :: rest)) child').mpr child
  exact (congrArg (Reduces (comm :: parCong :: rest)) conclusion).mp
    (reduces_ruleClosed (comm :: parCong :: rest) occurrence children)

/-- In the book's profile a dropped quotation steps to its code. -/
theorem steps_drop (code : Term sig Γ Srt.pr) :
    Steps bookRules (drpT (quoT code)) code :=
  steps_of_reduces (drop_reduces code)

end Classes

/-! ## Communication needs an output

Count the outputs at the top level of parallel composition. The count is
invariant under the equations, every strict-core conclusion has a positive
count, and so a process without an output has no strict-core step. A dropped
quotation is such a process: it is inert in the strict core and runs in the
book's profile. -/

section ActiveOutputs

open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

/-- Outputs at the top level of parallel composition. -/
def activeOutputs {Γ : Ctx sig} {s : Srt} : Term sig Γ s → Nat
  | .op Op.par (.cons a (.cons b .nil)) => activeOutputs a + activeOutputs b
  | .op Op.out _ => 1
  | _ => 0

/-- The count of each argument. -/
def argsOutputs {Γ : Ctx sig} : {ars : List (List Srt × Srt)} → Args sig ars Γ → List Nat
  | _, .nil => []
  | _, .cons head tail => activeOutputs head :: argsOutputs tail

/-- The count of an operator from the counts of its arguments. -/
def opWeight {s : Srt} : Op s → List Nat → Nat
  | .par, counts => counts.getD 0 0 + counts.getD 1 0
  | .out, _ => 1
  | _, _ => 0

theorem activeOutputs_op {Γ : Ctx sig} {s : Srt} (o : Op s)
    (args : Args sig (sig.arity o) Γ) :
    activeOutputs (.op o args) = opWeight o (argsOutputs args) := by
  cases o with
  | par =>
      match args with
      | .cons a (.cons b .nil) => rfl
  | out => rfl
  | nil => rfl
  | inp => rfl
  | drp => rfl
  | quo => rfl
  | free _ => rfl

theorem activeOutputs_name {Γ : Ctx sig} (t : Term sig Γ Srt.nm) : activeOutputs t = 0 := by
  cases t with
  | var _ => rfl
  | op o args =>
      cases o with
      | quo => rfl
      | free _ => rfl

/-- The count is invariant under the equations. -/
theorem activeOutputs_equiv {Γ : Ctx sig} {s : Srt} {t u : Term sig Γ s}
    (h : EqClosure equations t u) : activeOutputs t = activeOutputs u := by
  refine EqClosure.rec
    (motive_1 := fun t u _ => activeOutputs t = activeOutputs u)
    (motive_2 := fun as as' _ => argsOutputs as = argsOutputs as')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro i Γ body close
    fin_cases i
    · exact Nat.add_comm _ _
    · exact Nat.add_assoc _ _ _
    · exact Nat.add_zero _
    · exact (activeOutputs_name _).trans (activeOutputs_name _).symm
  · intro Γ s t
    rfl
  · intro Γ s t u _ ih
    exact ih.symm
  · intro Γ s t u v _ _ ih₁ ih₂
    exact ih₁.trans ih₂
  · intro Γ s o as as' _ ih
    rw [activeOutputs_op, activeOutputs_op, ih]
  · intro Γ
    rfl
  · intro bs s ars Γ h h' t t' _ _ ihh iht
    change activeOutputs h :: argsOutputs t = activeOutputs h' :: argsOutputs t'
    rw [ihh, iht]

/-- The count of an equation class. -/
noncomputable def activeOutputsQ {Γ : Ctx sig} {s : Srt} :
    (FreeBindingEquationModel.presented equations).algebra.substitution.Carrier Γ s → Nat :=
  Quotient.lift activeOutputs (fun _ _ h => activeOutputs_equiv h)

theorem activeOutputsQ_classes {Γ : Ctx sig} {s : Srt} (t : Term sig Γ s) :
    activeOutputsQ (classes.raw.map t) = activeOutputs t := rfl

private theorem activeOutputsQ_out {Γ : Ctx sig} {s : Srt}
    (x : (FreeBindingEquationModel.presented equations).algebra.substitution.Carrier Γ s) :
    activeOutputs (Quotient.out x) = activeOutputsQ x := by
  conv_rhs => rw [← Quotient.out_eq x]
  rfl

/-- Every strict-core step starts from a class with an output. -/
theorem strict_source_has_output
    {j : Judgment (FreeBindingEquationModel.presented equations).algebra}
    (reduces : Reduces strictRules j) : 1 ≤ activeOutputsQ j.2.2.1 := by
  refine reduces_least strictRules (fun j => 1 ≤ activeOutputsQ j.2.2.1) ?_ j reduces
  intro occurrence premises
  rcases occurrence with ⟨index, ambient, valuation, close⟩
  fin_cases index
  · change 1 ≤ activeOutputs (Quotient.out _) + activeOutputs (Quotient.out _)
    erw [activeOutputsQ_out, activeOutputsQ_out]
    change 1 ≤ 1 + _
    omega
  · have child := premises ⟨0, Nat.zero_lt_one⟩
    change 1 ≤ activeOutputs (Quotient.out _) + activeOutputs (Quotient.out _)
    erw [activeOutputsQ_out, activeOutputsQ_out]
    exact le_trans child (Nat.le_add_right _ _)

/-- A process without an output has no strict-core step. -/
theorem no_strict_step_of_no_output {Γ : Ctx sig} {source target : Term sig Γ Srt.pr}
    (none : activeOutputs source = 0) : ¬ Steps strictRules source target := by
  intro step
  have := strict_source_has_output step
  change 1 ≤ activeOutputs source at this
  omega

/-- A dropped quotation is inert in the strict core. -/
theorem drop_inert_strict {Γ : Ctx sig} (code target : Term sig Γ Srt.pr) :
    ¬ Steps strictRules (drpT (quoT code)) target :=
  no_strict_step_of_no_output rfl

/-- In the book's profile the same dropped quotation runs its code. -/
theorem drop_runs_book {Γ : Ctx sig} (code : Term sig Γ Srt.pr) :
    Steps bookRules (drpT (quoT code)) code :=
  steps_drop code

end ActiveOutputs

/-! ## Parallel atoms of an equation class

A process is a parallel composition of atoms: outputs, inputs, drops and
process variables. The equations are the commutative monoid laws on `par`
and a name law, so the multiset of the classes of its atoms, and of the
components of its outputs and inputs, are invariants of the class. -/

section Spine

/-- Equation classes. -/
abbrev Cls (Γ : Ctx sig) (s : Srt) : Type :=
  (FreeBindingEquationModel.presented equations).algebra.substitution.Carrier Γ s

/-- Agreement of a function on corresponding arguments. -/
def ArgsAgree {α : Ctx sig → Type} (f : ∀ {Γ : Ctx sig} {s : Srt}, Term sig Γ s → α Γ)
    {Γ : Ctx sig} : {ars : List (List Srt × Srt)} → Args sig ars Γ → Args sig ars Γ → Prop
  | _, .nil, .nil => True
  | _, .cons h t, .cons h' t' => f h = f h' ∧ ArgsAgree f t t'

/-- A function additive along parallel composition, zero on names and on the
null process, and determined up to congruence on every other process former,
is an invariant of equation classes. -/
theorem spine_invariant {α : Ctx sig → Type} [∀ Γ, AddCommMonoid (α Γ)]
    (f : ∀ {Γ : Ctx sig} {s : Srt}, Term sig Γ s → α Γ)
    (hpar : ∀ {Γ : Ctx sig} (a b : Term sig Γ Srt.pr), f (parT a b) = f a + f b)
    (hnil : ∀ {Γ : Ctx sig}, f (nilT : Term sig Γ Srt.pr) = 0)
    (hname : ∀ {Γ : Ctx sig} (t : Term sig Γ Srt.nm), f t = 0)
    (hatom : ∀ {Γ : Ctx sig} (o : Op Srt.pr) (as as' : Args sig (sig.arity o) Γ),
      o ≠ Op.par → EqArgs equations as as' → f (.op o as) = f (.op o as'))
    {Γ : Ctx sig} {s : Srt} {t u : Term sig Γ s} (h : EqClosure equations t u) :
    f t = f u := by
  refine EqClosure.rec
    (motive_1 := fun t u _ => f t = f u)
    (motive_2 := fun as as' _ => ArgsAgree f as as')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro i Γ body close
    fin_cases i
    · change f (parT (close _ .zero) (close _ (.succ .zero))) =
        f (parT (close _ (.succ .zero)) (close _ .zero))
      rw [hpar, hpar, add_comm]
    · change f (parT (parT (close _ .zero) (close _ (.succ .zero)))
          (close _ (.succ (.succ .zero)))) =
        f (parT (close _ .zero) (parT (close _ (.succ .zero))
          (close _ (.succ (.succ .zero)))))
      rw [hpar, hpar, hpar, hpar, add_assoc]
    · change f (parT (close _ .zero) nilT) = f (close _ .zero)
      rw [hpar, hnil, add_zero]
    · exact (hname _).trans (hname _).symm
  · intro Γ s t
    rfl
  · intro Γ s t u _ ih
    exact ih.symm
  · intro Γ s t u v _ _ ih₁ ih₂
    exact ih₁.trans ih₂
  · intro Γ s o as as' hargs ih
    cases s with
    | nm => exact (hname _).trans (hname _).symm
    | pr =>
        by_cases hpar' : o = Op.par
        · subst hpar'
          match as, as', ih with
          | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
              change f (parT a b) = f (parT a' b')
              rw [hpar, hpar]
              exact congrArg₂ (· + ·) ha hb
        · exact hatom o as as' hpar' hargs
  · intro Γ
    trivial
  · intro bs s ars Γ h h' t t' _ _ ihh iht
    exact ⟨ihh, iht⟩

/-- The class of a term. -/
noncomputable abbrev cls {Γ : Ctx sig} {s : Srt} (t : Term sig Γ s) : Cls Γ s :=
  classes.raw.map t

theorem cls_eq {Γ : Ctx sig} {s : Srt} {t u : Term sig Γ s}
    (h : EqClosure equations t u) : cls t = cls u :=
  Quotient.sound h

theorem cls_eq_iff {Γ : Ctx sig} {s : Srt} {t u : Term sig Γ s} :
    cls t = cls u ↔ EqClosure equations t u :=
  ⟨Quotient.exact, cls_eq⟩

/-- The classes of the parallel atoms of a process. -/
noncomputable def atoms {Γ : Ctx sig} : {s : Srt} → Term sig Γ s → Multiset (Cls Γ Srt.pr)
  | Srt.pr, .op Op.par (.cons a (.cons b .nil)) => atoms a + atoms b
  | Srt.pr, .op Op.nil _ => 0
  | Srt.pr, t => {cls t}
  | Srt.nm, _ => 0

/-- The channels and payloads of the parallel outputs. -/
noncomputable def outParts {Γ : Ctx sig} :
    {s : Srt} → Term sig Γ s → Multiset (Cls Γ Srt.nm × Cls Γ Srt.pr)
  | Srt.pr, .op Op.par (.cons a (.cons b .nil)) => outParts a + outParts b
  | Srt.pr, .op Op.out (.cons c (.cons x .nil)) => {(cls c, cls x)}
  | _, _ => 0

/-- The channels and continuations of the parallel inputs. -/
noncomputable def inpParts {Γ : Ctx sig} :
    {s : Srt} → Term sig Γ s → Multiset (Cls Γ Srt.nm × Cls (Srt.pr :: Γ) Srt.pr)
  | Srt.pr, .op Op.par (.cons a (.cons b .nil)) => inpParts a + inpParts b
  | Srt.pr, .op Op.inp (.cons c (.cons K .nil)) => {(cls c, cls K)}
  | _, _ => 0

/-- The names of the parallel drops. -/
noncomputable def dropParts {Γ : Ctx sig} : {s : Srt} → Term sig Γ s → Multiset (Cls Γ Srt.nm)
  | Srt.pr, .op Op.par (.cons a (.cons b .nil)) => dropParts a + dropParts b
  | Srt.pr, .op Op.drp (.cons n .nil) => {cls n}
  | _, _ => 0

theorem atoms_invariant {Γ : Ctx sig} {s : Srt} {t u : Term sig Γ s}
    (h : EqClosure equations t u) : atoms t = atoms u := by
  refine spine_invariant (α := fun Γ => Multiset (Cls Γ Srt.pr)) atoms
    (fun _ _ => rfl) rfl (fun t => by cases t <;> rfl) ?_ h
  intro Γ o as as' hpar hargs
  cases o with
  | par => exact absurd rfl hpar
  | nil => rfl
  | out => exact congrArg (fun x => ({x} : Multiset _)) (cls_eq (EqClosure.cong _ hargs))
  | inp => exact congrArg (fun x => ({x} : Multiset _)) (cls_eq (EqClosure.cong _ hargs))
  | drp => exact congrArg (fun x => ({x} : Multiset _)) (cls_eq (EqClosure.cong _ hargs))

theorem outParts_invariant {Γ : Ctx sig} {s : Srt} {t u : Term sig Γ s}
    (h : EqClosure equations t u) : outParts t = outParts u := by
  refine spine_invariant (α := fun Γ => Multiset (Cls Γ Srt.nm × Cls Γ Srt.pr)) outParts
    (fun _ _ => rfl) rfl (fun t => by cases t <;> rfl) ?_ h
  intro Γ o as as' hpar hargs
  cases o with
  | par => exact absurd rfl hpar
  | out =>
      match as, as', hargs with
      | .cons c (.cons x .nil), .cons c' (.cons x' .nil), .cons hc (.cons hx .nil) =>
          change ({(cls c, cls x)} : Multiset _) = {(cls c', cls x')}
          rw [cls_eq hc, cls_eq hx]
  | nil => rfl
  | inp => rfl
  | drp => rfl

theorem inpParts_invariant {Γ : Ctx sig} {s : Srt} {t u : Term sig Γ s}
    (h : EqClosure equations t u) : inpParts t = inpParts u := by
  refine spine_invariant
    (α := fun Γ => Multiset (Cls Γ Srt.nm × Cls (Srt.pr :: Γ) Srt.pr)) inpParts
    (fun _ _ => rfl) rfl (fun t => by cases t <;> rfl) ?_ h
  intro Γ o as as' hpar hargs
  cases o with
  | par => exact absurd rfl hpar
  | inp =>
      match as, as', hargs with
      | .cons c (.cons K .nil), .cons c' (.cons K' .nil), .cons hc (.cons hK .nil) =>
          change ({(cls c, cls K)} : Multiset _) = {(cls c', cls K')}
          rw [cls_eq hc, cls_eq hK]
  | nil => rfl
  | out => rfl
  | drp => rfl

theorem dropParts_invariant {Γ : Ctx sig} {s : Srt} {t u : Term sig Γ s}
    (h : EqClosure equations t u) : dropParts t = dropParts u := by
  refine spine_invariant (α := fun Γ => Multiset (Cls Γ Srt.nm)) dropParts
    (fun _ _ => rfl) rfl (fun t => by cases t <;> rfl) ?_ h
  intro Γ o as as' hpar hargs
  cases o with
  | par => exact absurd rfl hpar
  | drp =>
      match as, as', hargs with
      | .cons n .nil, .cons n' .nil, .cons hn .nil =>
          change ({cls n} : Multiset _) = {cls n'}
          rw [cls_eq hn]
  | nil => rfl
  | out => rfl
  | inp => rfl

/-- Parallel composition of classes. -/
noncomputable def parQ {Γ : Ctx sig} : Cls Γ Srt.pr → Cls Γ Srt.pr → Cls Γ Srt.pr :=
  Quotient.map₂ parT (fun _ _ ha _ _ hb => equiv_parT ha hb)

theorem parQ_cls {Γ : Ctx sig} (a b : Term sig Γ Srt.pr) :
    parQ (cls a) (cls b) = cls (parT a b) := rfl

theorem parQ_assoc {Γ : Ctx sig} (x y z : Cls Γ Srt.pr) :
    parQ (parQ x y) z = parQ x (parQ y z) := by
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  induction z using Quotient.inductionOn
  exact Quotient.sound (parT_assoc _ _ _)

theorem parQ_comm {Γ : Ctx sig} (x y : Cls Γ Srt.pr) : parQ x y = parQ y x := by
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  exact Quotient.sound (parT_comm _ _)

theorem parQ_nil {Γ : Ctx sig} (x : Cls Γ Srt.pr) : parQ x (cls nilT) = x := by
  induction x using Quotient.inductionOn
  exact Quotient.sound (parT_nil _)

instance {Γ : Ctx sig} : LeftCommutative (parQ (Γ := Γ)) :=
  ⟨fun x y z => by rw [← parQ_assoc, parQ_comm x y, parQ_assoc]⟩

/-- Parallel composition of a multiset of classes. -/
noncomputable def foldQ {Γ : Ctx sig} (atoms : Multiset (Cls Γ Srt.pr)) : Cls Γ Srt.pr :=
  Multiset.foldr parQ (cls nilT) atoms

theorem foldQ_add {Γ : Ctx sig} (s t : Multiset (Cls Γ Srt.pr)) :
    foldQ (s + t) = parQ (foldQ s) (foldQ t) := by
  unfold foldQ
  rw [Multiset.foldr_add]
  induction s using Multiset.induction_on with
  | empty =>
      rw [Multiset.foldr_zero, Multiset.foldr_zero, parQ_comm, parQ_nil]
  | cons x s ih =>
      rw [Multiset.foldr_cons, Multiset.foldr_cons, ih, parQ_assoc]

theorem foldQ_atom {Γ : Ctx sig} (x : Cls Γ Srt.pr) : x = foldQ {x} := by
  rw [foldQ, Multiset.foldr_singleton, parQ_nil]

/-- A process is the parallel composition of its atoms. -/
theorem cls_eq_foldQ {Γ : Ctx sig} : (t : Term sig Γ Srt.pr) → cls t = foldQ (atoms t)
  | .var v => foldQ_atom _
  | .op Op.par (.cons a (.cons b .nil)) => by
      change cls (parT a b) = foldQ (atoms a + atoms b)
      rw [foldQ_add, ← cls_eq_foldQ a, ← cls_eq_foldQ b]
      rfl
  | .op Op.nil .nil => rfl
  | .op Op.out args => foldQ_atom _
  | .op Op.inp args => foldQ_atom _
  | .op Op.drp args => foldQ_atom _
termination_by t => termSize t
decreasing_by all_goals (simp_wf; simp only [termSize, argsSize]; omega)

/-- Processes with the same atoms are equal up to the equations. -/
theorem cls_eq_of_atoms_eq {Γ : Ctx sig} {t u : Term sig Γ Srt.pr}
    (h : atoms t = atoms u) : cls t = cls u := by
  rw [cls_eq_foldQ t, cls_eq_foldQ u, h]

end Spine

/-! ## The core of a name

Quote/drop cancellation makes quotation non-injective on classes: the
quotation of a single dropped name is that name. Every name class has a core:
a variable, a free name, or the class of the quoted code when that code is
not a single drop. The core is a complete invariant of name classes. -/

section NameCore

/-- The core of a name class. -/
inductive QKey (Γ : Ctx sig) where
  | var (v : Var Γ Srt.nm)
  | free (label : String)
  | quo (code : Cls Γ Srt.pr)

/-- The name-core invariant: for a name its core, and for a process that is
a single drop the core of the dropped name. -/
noncomputable def key {Γ : Ctx sig} : {s : Srt} → Term sig Γ s → Option (QKey Γ)
  | Srt.nm, .var v => some (.var v)
  | _, .op (Op.free label) _ => some (.free label)
  | _, .op Op.quo (.cons p .nil) =>
      some (match key p with
        | some k => k
        | none => .quo (cls p))
  | _, .op Op.par (.cons a (.cons b .nil)) =>
      if Multiset.card (atoms b) = 0 then key a
      else if Multiset.card (atoms a) = 0 then key b
      else none
  | _, .op Op.drp (.cons m .nil) => key m
  | _, _ => none

/-- The core of a name. -/
noncomputable def qcore {Γ : Ctx sig} (n : Term sig Γ Srt.nm) : QKey Γ :=
  (key n).getD (.free "")

theorem key_name {Γ : Ctx sig} (n : Term sig Γ Srt.nm) : key n = some (qcore n) := by
  cases n with
  | var v => rfl
  | op o args =>
      cases o with
      | quo =>
          match args with
          | .cons p .nil => rfl
      | free label => rfl

theorem key_par {Γ : Ctx sig} (a b : Term sig Γ Srt.pr) :
    key (parT a b) =
      if Multiset.card (atoms b) = 0 then key a
      else if Multiset.card (atoms a) = 0 then key b
      else none := rfl

theorem key_nil {Γ : Ctx sig} : key (nilT : Term sig Γ Srt.pr) = none := rfl

theorem key_drp {Γ : Ctx sig} (m : Term sig Γ Srt.nm) : key (drpT m) = some (qcore m) :=
  key_name m

theorem qcore_quo {Γ : Ctx sig} (p : Term sig Γ Srt.pr) :
    qcore (quoT p) = match key p with
      | some k => k
      | none => .quo (cls p) := rfl

/-- A process without atoms is not a single drop. -/
theorem key_of_card_zero {Γ : Ctx sig} :
    (t : Term sig Γ Srt.pr) → Multiset.card (atoms t) = 0 → key t = none
  | .var v, h => by
      change Multiset.card ({cls (.var v)} : Multiset (Cls Γ Srt.pr)) = 0 at h
      simp at h
  | .op Op.par (.cons a (.cons b .nil)), h => by
      change Multiset.card (atoms a + atoms b) = 0 at h
      rw [Multiset.card_add] at h
      change key (parT a b) = none
      rw [key_par, if_pos (by omega), key_of_card_zero a (by omega)]
  | .op Op.nil .nil, _ => key_nil
  | .op Op.out args, h => by
      change Multiset.card ({cls (.op Op.out args)} : Multiset (Cls Γ Srt.pr)) = 0 at h
      simp at h
  | .op Op.inp args, h => by
      change Multiset.card ({cls (.op Op.inp args)} : Multiset (Cls Γ Srt.pr)) = 0 at h
      simp at h
  | .op Op.drp args, h => by
      change Multiset.card ({cls (.op Op.drp args)} : Multiset (Cls Γ Srt.pr)) = 0 at h
      simp at h
termination_by t => termSize t
decreasing_by all_goals (simp_wf; simp only [termSize, argsSize]; omega)

private theorem key_par_comm {Γ : Ctx sig} (x y : Term sig Γ Srt.pr) :
    key (parT x y) = key (parT y x) := by
  rw [key_par, key_par]
  by_cases hx : Multiset.card (atoms x) = 0 <;> by_cases hy : Multiset.card (atoms y) = 0 <;>
    simp [hx, hy, key_of_card_zero x, key_of_card_zero y]

private theorem key_par_assoc {Γ : Ctx sig} (x y z : Term sig Γ Srt.pr) :
    key (parT (parT x y) z) = key (parT x (parT y z)) := by
  have hxy : atoms (parT x y) = atoms x + atoms y := rfl
  have hyz : atoms (parT y z) = atoms y + atoms z := rfl
  rw [key_par, key_par, key_par, key_par, hxy, hyz]
  by_cases hx : Multiset.card (atoms x) = 0 <;> by_cases hy : Multiset.card (atoms y) = 0 <;>
    by_cases hz : Multiset.card (atoms z) = 0 <;>
    simp [hx, hy, hz, Multiset.card_add, key_of_card_zero x]

/-- **The name core is an invariant of classes.** -/
theorem key_invariant {Γ : Ctx sig} {s : Srt} {t u : Term sig Γ s}
    (h : EqClosure equations t u) : key t = key u := by
  refine EqClosure.rec
    (motive_1 := fun t u _ => key t = key u)
    (motive_2 := fun as as' _ => ArgsAgree key as as')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro i Γ body close
    fin_cases i
    · exact key_par_comm _ _
    · exact key_par_assoc _ _ _
    · change key (parT (close _ .zero) nilT) = key (close _ .zero)
      exact if_pos rfl
    · change key (quoT (drpT (close _ .zero))) = key (close _ .zero)
      rw [key_name (close _ .zero)]
      change some (qcore (quoT (drpT (close _ .zero)))) = _
      rw [qcore_quo, key_drp]
  · intro Γ s t
    rfl
  · intro Γ s t u _ ih
    exact ih.symm
  · intro Γ s t u v _ _ ih₁ ih₂
    exact ih₁.trans ih₂
  · intro Γ s o as as' hargs ih
    cases o with
    | nil => rfl
    | out => rfl
    | inp => rfl
    | free label => rfl
    | par =>
        match as, as', ih, hargs with
        | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩,
            .cons ea (.cons eb .nil) =>
            change key (parT a b) = key (parT a' b')
            rw [key_par, key_par, atoms_invariant ea, atoms_invariant eb]
            rw [show key a = key a' from ha, show key b = key b' from hb]
    | drp =>
        match as, as', ih with
        | .cons m .nil, .cons m' .nil, ⟨hm, _⟩ => exact hm
    | quo =>
        match as, as', ih, hargs with
        | .cons p .nil, .cons p' .nil, ⟨hp, _⟩, .cons ep .nil =>
            change some (qcore (quoT p)) = some (qcore (quoT p'))
            rw [qcore_quo, qcore_quo, show key p = key p' from hp, cls_eq ep]
  · intro Γ
    trivial
  · intro bs s ars Γ h h' t t' _ _ ihh iht
    exact ⟨ihh, iht⟩

theorem qcore_invariant {Γ : Ctx sig} {m m' : Term sig Γ Srt.nm}
    (h : EqClosure equations m m') : qcore m = qcore m' := by
  have := key_invariant h
  rw [key_name, key_name] at this
  exact Option.some.inj this

/-- A representative of a core. -/
noncomputable def coreRep {Γ : Ctx sig} : QKey Γ → Term sig Γ Srt.nm
  | .var v => .var v
  | .free label => freeT label
  | .quo code => quoT (Quotient.out code)

mutual
/-- Every name is equal to the representative of its core. -/
theorem name_equiv_coreRep {Γ : Ctx sig} :
    (n : Term sig Γ Srt.nm) → EqClosure equations n (coreRep (qcore n))
  | .var v => .refl _
  | .op (Op.free label) .nil => .refl _
  | .op Op.quo (.cons p .nil) => by
      change EqClosure equations (quoT p) (coreRep (qcore (quoT p)))
      rw [qcore_quo]
      cases hk : key p with
      | some k =>
          obtain ⟨m, hp, hmk, hm⟩ := drop_of_key p k hk
          exact (equiv_quoT hp).trans ((quoteDrop_equiv m).trans (hmk ▸ hm))
      | none =>
          exact equiv_quoT (Quotient.exact (Quotient.out_eq (cls p)).symm)
termination_by n => termSize n
decreasing_by all_goals (simp_wf; simp only [termSize, argsSize]; omega)

/-- A process that is a single drop is that drop, and its name is equal to
the representative of its core. -/
theorem drop_of_key {Γ : Ctx sig} :
    (p : Term sig Γ Srt.pr) → (k : QKey Γ) → key p = some k →
      ∃ m, EqClosure equations p (drpT m) ∧ qcore m = k ∧
        EqClosure equations m (coreRep (qcore m))
  | .var _, k, h => by cases h
  | .op Op.par (.cons a (.cons b .nil)), k, h => by
      change key (parT a b) = some k at h
      rw [key_par] at h
      by_cases hb : Multiset.card (atoms b) = 0
      · rw [if_pos hb] at h
        obtain ⟨m, hp, hmk, hm⟩ := drop_of_key a k h
        have hbnil : EqClosure equations b nilT := cls_eq_iff.mp
          (cls_eq_of_atoms_eq (Multiset.card_eq_zero.mp hb))
        exact ⟨m, (equiv_parT hp hbnil).trans (parT_nil _), hmk, hm⟩
      · rw [if_neg hb] at h
        by_cases ha : Multiset.card (atoms a) = 0
        · rw [if_pos ha] at h
          obtain ⟨m, hp, hmk, hm⟩ := drop_of_key b k h
          have hanil : EqClosure equations a nilT := cls_eq_iff.mp
            (cls_eq_of_atoms_eq (Multiset.card_eq_zero.mp ha))
          exact ⟨m, (equiv_parT hanil hp).trans (nil_parT _), hmk, hm⟩
        · rw [if_neg ha] at h
          cases h
  | .op Op.nil .nil, k, h => by cases h
  | .op Op.out _, k, h => by cases h
  | .op Op.inp _, k, h => by cases h
  | .op Op.drp (.cons m .nil), k, h => by
      change key (drpT m) = some k at h
      rw [key_drp] at h
      cases h
      exact ⟨m, .refl _, rfl, name_equiv_coreRep m⟩
termination_by p => termSize p
decreasing_by all_goals (simp_wf; simp only [termSize, argsSize]; omega)
end

/-- **Names with one core are one class.** -/
theorem cls_eq_of_qcore_eq {Γ : Ctx sig} {m m' : Term sig Γ Srt.nm}
    (h : qcore m = qcore m') : EqClosure equations m m' :=
  (name_equiv_coreRep m).trans (h ▸ (name_equiv_coreRep m').symm)

end NameCore

/-! ## Inverting a step between classes

Every occurrence over the quotient is the image of an occurrence over terms.
A strict-core step therefore consumes one output and one input on the same
channel class and puts the instantiated continuation in their place; the
book's profile may instead consume one dropped quotation. -/

section Inversion

open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables

/-- The atoms of a class, of any sort. -/
noncomputable def atomsQ {Γ : Ctx sig} {s : Srt} : Cls Γ s → Multiset (Cls Γ Srt.pr) :=
  Quotient.lift atoms (fun _ _ h => atoms_invariant h)

theorem atomsQ_cls {Γ : Ctx sig} {s : Srt} (t : Term sig Γ s) : atomsQ (cls t) = atoms t := rfl

/-- Every occurrence over the quotient is the image of one over terms. -/
theorem occurrence_image {R : List (Rule sig metas)}
    (occurrence : Instance R (FreeBindingEquationModel.presented equations).algebra) :
    ∃ rep : Instance R (BindingCloneAlgebra.terms sig), mapInstance R classes rep = occurrence := by
  rcases occurrence with ⟨index, ambient, valuation, close⟩
  refine ⟨⟨index, ambient, fun k => Quotient.out (valuation k),
    fun s v => Quotient.out (close s v)⟩, ?_⟩
  simp only [mapInstance]
  congr 1
  · funext k
    exact Quotient.out_eq _
  · funext s v
    exact Quotient.out_eq _

variable (rest : List (Rule sig metas))

theorem comm_occurrence_eta {Γ : Ctx sig} (h : 0 < (comm :: parCong :: rest).length)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ)
    (close : Sub sig [Srt.nm, Srt.pr] Γ) :
    (⟨⟨0, h⟩, Γ, valuation, close⟩ :
        Instance (comm :: parCong :: rest) (BindingCloneAlgebra.terms sig)) =
      commOccurrence rest (close _ .zero) (close _ (.succ .zero))
        (valuation ⟨0, Nat.zero_lt_one⟩) := by
  unfold commOccurrence
  congr 1
  · funext k
    match k with
    | ⟨0, _⟩ => rfl
  · funext s v
    match v with
    | .zero => rfl
    | .succ .zero => rfl

variable {rest}

/-- The shape of a step of a profile containing communication and parallel
congruence, with the extra rules' shapes supplied by `Extra`. -/
def CommShape {Γ : Ctx sig} {s : Srt} (source target : Cls Γ s) : Prop :=
  ∃ (c : Term sig Γ Srt.nm) (q : Term sig Γ Srt.pr) (K : Term sig (Srt.pr :: Γ) Srt.pr)
    (others : Multiset (Cls Γ Srt.pr)),
    atomsQ source = cls (outT c q) ::ₘ cls (inpT c K) ::ₘ others ∧
      atomsQ target = atoms (inst K q) + others

/-- A dropped quotation is consumed and its code put in its place. -/
def DropShape {Γ : Ctx sig} {s : Srt} (source target : Cls Γ s) : Prop :=
  ∃ (code : Term sig Γ Srt.pr) (others : Multiset (Cls Γ Srt.pr)),
    atomsQ source = cls (drpT (quoT code)) ::ₘ others ∧ atomsQ target = atoms code + others

private theorem commShape_conclusion {Γ : Ctx sig} (c : Term sig Γ Srt.nm)
    (q : Term sig Γ Srt.pr) (K : Term sig (Srt.pr :: Γ) Srt.pr) :
    CommShape (cls (parT (outT c q) (inpT c K))) (cls (inst K q)) :=
  ⟨c, q, K, 0, rfl, (add_zero _).symm⟩

private theorem commShape_par {Γ : Ctx sig} {a b : Term sig Γ Srt.pr} (r : Term sig Γ Srt.pr)
    (h : CommShape (cls a) (cls b)) : CommShape (cls (parT a r)) (cls (parT b r)) := by
  obtain ⟨c, q, K, others, hs, ht⟩ := h
  refine ⟨c, q, K, others + atoms r, ?_, ?_⟩
  · change atoms a + atoms r = _
    rw [show atoms a = atomsQ (cls a) from rfl, hs]
    simp
  · change atoms b + atoms r = _
    rw [show atoms b = atomsQ (cls b) from rfl, ht, add_assoc]

private theorem dropShape_par {Γ : Ctx sig} {a b : Term sig Γ Srt.pr} (r : Term sig Γ Srt.pr)
    (h : DropShape (cls a) (cls b)) : DropShape (cls (parT a r)) (cls (parT b r)) := by
  obtain ⟨code, others, hs, ht⟩ := h
  refine ⟨code, others + atoms r, ?_, ?_⟩
  · change atoms a + atoms r = _
    rw [show atoms a = atomsQ (cls a) from rfl, hs]
    simp
  · change atoms b + atoms r = _
    rw [show atoms b = atomsQ (cls b) from rfl, ht, add_assoc]

/-- Inversion for the profiles: every step between classes has the COMM
shape, or, when the rules after parallel congruence include Drop, the Drop
shape. -/
theorem steps_inversion (hrest : rest = [] ∨ rest = [drop])
    {j : Judgment (FreeBindingEquationModel.presented equations).algebra}
    (reduces : Reduces (comm :: parCong :: rest) j) :
    CommShape j.2.2.1 j.2.2.2 ∨ (rest = [drop] ∧ DropShape j.2.2.1 j.2.2.2) := by
  refine reduces_least (comm :: parCong :: rest)
    (fun j => CommShape j.2.2.1 j.2.2.2 ∨ (rest = [drop] ∧ DropShape j.2.2.1 j.2.2.2))
    ?_ j reduces
  intro occurrence premises
  obtain ⟨rep, rfl⟩ := occurrence_image occurrence
  refine (congrArg
    (fun j : Judgment (FreeBindingEquationModel.presented equations).algebra =>
      CommShape j.2.2.1 j.2.2.2 ∨ (rest = [drop] ∧ DropShape j.2.2.1 j.2.2.2))
    (mapInstance_conclusion (comm :: parCong :: rest) classes rep)).mpr ?_
  rcases rep with ⟨⟨i, hi⟩, ambient, valuation, close⟩
  match i, hi with
  | 0, hi =>
      rw [comm_occurrence_eta rest hi valuation close]
      refine (congrArg
        (fun j : Judgment (BindingCloneAlgebra.terms sig) =>
          CommShape (mapJudgment classes j).2.2.1 (mapJudgment classes j).2.2.2 ∨
            (rest = [drop] ∧
              DropShape (mapJudgment classes j).2.2.1 (mapJudgment classes j).2.2.2))
        (commConclusion rest _ _ _)).mpr ?_
      exact .inl (commShape_conclusion _ _ _)
  | 1, hi =>
      have child := premises ⟨0, Nat.zero_lt_one⟩
      have childEq := mapInstance_child (comm :: parCong :: rest) classes
        ⟨⟨1, hi⟩, ambient, valuation, close⟩ ⟨0, Nat.zero_lt_one⟩
      replace child := (congrArg
        (fun j : Judgment (FreeBindingEquationModel.presented equations).algebra =>
          CommShape j.2.2.1 j.2.2.2 ∨ (rest = [drop] ∧ DropShape j.2.2.1 j.2.2.2))
        childEq).mp child
      change CommShape (cls (close _ .zero)) (cls (close _ (.succ .zero))) ∨
        (rest = [drop] ∧ DropShape (cls (close _ .zero)) (cls (close _ (.succ .zero))))
        at child
      change CommShape (cls (parT (close _ .zero) (close _ (.succ (.succ .zero)))))
          (cls (parT (close _ (.succ .zero)) (close _ (.succ (.succ .zero))))) ∨
        (rest = [drop] ∧ DropShape
          (cls (parT (close _ .zero) (close _ (.succ (.succ .zero)))))
          (cls (parT (close _ (.succ .zero)) (close _ (.succ (.succ .zero))))))
      rcases child with h | ⟨hdrop, h⟩
      · exact .inl (commShape_par _ h)
      · exact .inr ⟨hdrop, dropShape_par _ h⟩
  | 2, hi =>
      rcases hrest with rfl | rfl
      · exact absurd hi (by decide)
      · refine .inr ⟨rfl, ?_⟩
        change DropShape (cls (drpT (quoT (close _ .zero)))) (cls (close _ .zero))
        exact ⟨close _ .zero, 0, rfl, (add_zero _).symm⟩
  | n + 3, hi =>
      rcases hrest with rfl | rfl
      · exact absurd hi (by simp)
      · exact absurd hi (by simp)

end Inversion

end Mettapedia.OSLF.Binding.RhoPayloadPresentation
