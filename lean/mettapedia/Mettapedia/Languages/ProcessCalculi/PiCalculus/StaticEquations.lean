import Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
import Mettapedia.GSLT.LanguageDef.BindingSignatureSubstitution
import Mettapedia.OSLF.Syntax.ContextualEquationInstances
import Mettapedia.OSLF.Syntax.EquationalQuotient

/-!
# Typed scope equations on the authored pi signature

The operators below are derived from the actual constructors of `piCalc`.
Eight equations use the existing binding-signature templates and equation
closure: restriction of inaction, exchange of restrictions and scope extrusion,
and the five laws of replication (unfolding, replicated inaction, idempotence,
distribution over parallel composition, duplication). Every instance retains the
separately typed dependency prefix and ambient context of its metavariable bodies.
A guarded server unfolds as an instance of the general unfolding (`unfold_guarded`).

These laws supplement the parallel collection algebra. They are intrinsic
static equations over the authored signature of processes and names; they do not change
`piCalc.equations`, its bag canonical section, or its directed rewrite list.
The raw equation compiler currently does not accept binding metavariables, and
no automatic compilation or full named-structural-congruence comparison is
asserted here. Atomic-name admissibility remains a separate fragment boundary.
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.StaticEquations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance

set_option autoImplicit false

abbrev signature := signatureOf piCalc
abbrev processSort : TypeExpr := .base "Proc"
abbrev nameSort : TypeExpr := .base "Name"

def nilOperator : signature.Op processSort :=
  .constructor piCalc.terms[0] (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, piCalc]) .nil

def parallelOperator : signature.Op processSort :=
  .collectionConstructor piCalc.terms[1] (List.getElem_mem (by decide))
    "ps" .hashBag processSort rfl 2

def inputOperator : signature.Op processSort :=
  .constructor piCalc.terms[2] (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, piCalc])
    (.cons (.simple "x" nameSort)
      (.cons (.abstraction none "body" nameSort processSort) .nil))

def outputOperator : signature.Op processSort :=
  .constructor piCalc.terms[3] (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, piCalc])
    (.cons (.simple "x" nameSort) (.cons (.simple "z" nameSort) .nil))

def restrictionOperator : signature.Op processSort :=
  .constructor piCalc.terms[4] (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, piCalc])
    (.cons (.abstraction none "body" nameSort processSort) .nil)

def replicationOperator : signature.Op processSort :=
  .constructor piCalc.terms[5] (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, piCalc])
    (.cons (.simple "p" processSort) .nil)

def nilTerm {Γ : Ctx signature} : Term signature Γ processSort :=
  .op nilOperator .nil

def parallelTerm {Γ : Ctx signature}
    (left right : Term signature Γ processSort) : Term signature Γ processSort :=
  .op parallelOperator (.cons left (.cons right .nil))

def inputTerm {Γ : Ctx signature} (channel : Term signature Γ nameSort)
    (body : Term signature (nameSort :: Γ) processSort) : Term signature Γ processSort :=
  .op inputOperator (.cons channel (.cons body .nil))

def outputTerm {Γ : Ctx signature} (channel datum : Term signature Γ nameSort) :
    Term signature Γ processSort :=
  .op outputOperator (.cons channel (.cons datum .nil))

def restrictionTerm {Γ : Ctx signature}
    (body : Term signature (nameSort :: Γ) processSort) : Term signature Γ processSort :=
  .op restrictionOperator (.cons body .nil)

def replicationTerm {Γ : Ctx signature} (process : Term signature Γ processSort) :
    Term signature Γ processSort :=
  .op replicationOperator (.cons process .nil)

@[simp] theorem erase_nilTerm {Γ : Ctx signature} :
    erase (nilTerm (Γ := Γ)) = .apply "PiNil" [] := rfl

@[simp] theorem erase_parallelTerm {Γ : Ctx signature}
    (left right : Term signature Γ processSort) :
    erase (parallelTerm left right) =
      .collection .hashBag [erase left, erase right] none := rfl

@[simp] theorem erase_restrictionTerm {Γ : Ctx signature}
    (body : Term signature (nameSort :: Γ) processSort) :
    erase (restrictionTerm body) = .apply "PiNu" [.lambda none (erase body)] := rfl

@[simp] theorem erase_inputTerm {Γ : Ctx signature} (channel : Term signature Γ nameSort)
    (body : Term signature (nameSort :: Γ) processSort) :
    erase (inputTerm channel body) = .apply "PiInp" [erase channel, .lambda none (erase body)] := rfl

@[simp] theorem erase_outputTerm {Γ : Ctx signature}
    (channel datum : Term signature Γ nameSort) :
    erase (outputTerm channel datum) = .apply "PiOut" [erase channel, erase datum] := rfl

@[simp] theorem erase_replicationTerm {Γ : Ctx signature} (process : Term signature Γ processSort) :
    erase (replicationTerm process) = .apply "PiRep" [erase process] := rfl

/-- The body of a scope law may depend on one or two local names. The extruded component has no local dependency
prefix, nor have the processes of the replication laws; distribution takes two of them. -/
abbrev metavariables : List (MetaArity signature) :=
  [([nameSort], processSort), ([nameSort, nameSort], processSort), ([], processSort), ([], processSort)]

abbrev oneIndex : Fin metavariables.length := ⟨0, by decide⟩
abbrev twoIndex : Fin metavariables.length := ⟨1, by decide⟩
abbrev outsideIndex : Fin metavariables.length := ⟨2, by decide⟩
abbrev otherIndex : Fin metavariables.length := ⟨3, by decide⟩
abbrev schemaSignature := withMetas signature metavariables

private def schemaNil {Γ : Ctx schemaSignature} : Term schemaSignature Γ processSort :=
  .op (.inl nilOperator) .nil

private def schemaParallel {Γ : Ctx schemaSignature}
    (left right : Term schemaSignature Γ processSort) : Term schemaSignature Γ processSort :=
  .op (.inl parallelOperator) (.cons left (.cons right .nil))

private def schemaRestriction {Γ : Ctx schemaSignature}
    (body : Term schemaSignature (nameSort :: Γ) processSort) :
    Term schemaSignature Γ processSort :=
  .op (.inl restrictionOperator) (.cons body .nil)

private def schemaInput {Γ : Ctx schemaSignature} (channel : Term schemaSignature Γ nameSort)
    (body : Term schemaSignature (nameSort :: Γ) processSort) :
    Term schemaSignature Γ processSort :=
  .op (.inl inputOperator) (.cons channel (.cons body .nil))

private def schemaReplication {Γ : Ctx schemaSignature} (process : Term schemaSignature Γ processSort) :
    Term schemaSignature Γ processSort :=
  .op (.inl replicationOperator) (.cons process .nil)

/-- Exchange the two local restriction variables while keeping each ambient
variable at its original position. -/
def exchangeRestrictions {Γ : List TypeExpr} (sort : TypeExpr)
    (position : Var (nameSort :: nameSort :: Γ) sort) :
    Var (nameSort :: nameSort :: Γ) sort := by
  cases position with
  | zero => exact .succ .zero
  | succ position =>
    cases position with
    | zero => exact .zero
    | succ position => exact .succ (.succ position)

@[simp] theorem exchangeRestrictions_involution {Γ : List TypeExpr}
    {sort : TypeExpr} (position : Var (nameSort :: nameSort :: Γ) sort) :
    exchangeRestrictions sort (exchangeRestrictions sort position) = position := by
  cases position with
  | zero => rfl
  | succ position => cases position <;> rfl

def restrictionNil : EqAxiom signature metavariables where
  ctx := []
  sort := processSort
  lhs := schemaRestriction schemaNil
  rhs := schemaNil

def restrictionExchange : EqAxiom signature metavariables where
  ctx := []
  sort := processSort
  lhs := schemaRestriction (schemaRestriction (metaVar twoIndex))
  rhs := schemaRestriction (schemaRestriction
    (rename (exchangeRestrictions (Γ := [])) (metaVar twoIndex)))

def restrictionExtrusion : EqAxiom signature metavariables where
  ctx := []
  sort := processSort
  lhs := schemaRestriction
    (schemaParallel (metaVar oneIndex) (weaken (t := nameSort) (metaVar outsideIndex)))
  rhs := schemaParallel (schemaRestriction (metaVar oneIndex)) (metaVar outsideIndex)

/-- `!P = {P, !P}`: a replicated process unfolds into a copy beside itself. -/
def replicationUnfold : EqAxiom signature metavariables where
  ctx := []
  sort := processSort
  lhs := schemaReplication (metaVar outsideIndex)
  rhs := schemaParallel (metaVar outsideIndex) (schemaReplication (metaVar outsideIndex))

/-- `!0 = 0` -/
def replicationNil : EqAxiom signature metavariables where
  ctx := []
  sort := processSort
  lhs := schemaReplication schemaNil
  rhs := schemaNil

/-- `!!P = !P` -/
def replicationTwice : EqAxiom signature metavariables where
  ctx := []
  sort := processSort
  lhs := schemaReplication (schemaReplication (metaVar outsideIndex))
  rhs := schemaReplication (metaVar outsideIndex)

/-- `!{P, Q} = {!P, !Q}` -/
def replicationPar : EqAxiom signature metavariables where
  ctx := []
  sort := processSort
  lhs := schemaReplication (schemaParallel (metaVar outsideIndex) (metaVar otherIndex))
  rhs := schemaParallel (schemaReplication (metaVar outsideIndex)) (schemaReplication (metaVar otherIndex))

/-- `{!P, !P} = !P` -/
def replicationIdempotent : EqAxiom signature metavariables where
  ctx := []
  sort := processSort
  lhs := schemaParallel (schemaReplication (metaVar outsideIndex)) (schemaReplication (metaVar outsideIndex))
  rhs := schemaReplication (metaVar outsideIndex)

/-- The eight non-monoid static laws of `piCalc`: three of restriction, five of replication. -/
def equations : List (EqAxiom signature metavariables) :=
  [restrictionNil, restrictionExchange, restrictionExtrusion, replicationUnfold, replicationNil, replicationTwice,
    replicationPar, replicationIdempotent]

private def identitySub (Γ : Ctx signature) : Sub signature Γ Γ := fun _ v => .var v
private def emptySub (Γ : Ctx signature) : Sub signature [] Γ := fun _ v => nomatch v
private def localOne (Γ : Ctx signature) : Sub signature [nameSort] (nameSort :: Γ) :=
  liftSub (emptySub Γ) [nameSort]
private def localTwo (Γ : Ctx signature) :
    Sub signature [nameSort, nameSort] (nameSort :: nameSort :: Γ) :=
  liftSub (emptySub Γ) [nameSort, nameSort]
private def ambientOne (Γ : Ctx signature) : Sub signature Γ (nameSort :: Γ) :=
  ContextualAssignment.weakenSub (S := signature) [nameSort] (identitySub Γ)
private def ambientTwo (Γ : Ctx signature) :
    Sub signature Γ (nameSort :: nameSort :: Γ) :=
  ContextualAssignment.weakenSub (S := signature) [nameSort] (ambientOne Γ)

private theorem join_one_identity (Γ : Ctx signature) :
    ContextualAssignment.joinSub (localOne Γ) (ambientOne Γ) =
      identitySub (nameSort :: Γ) := by
  funext sort position
  cases position <;> rfl

private theorem join_two_identity (Γ : Ctx signature) :
    ContextualAssignment.joinSub (localTwo Γ) (ambientTwo Γ) =
      identitySub (nameSort :: nameSort :: Γ) := by
  funext sort position
  cases position with
  | zero => rfl
  | succ position => cases position <;> rfl

private theorem join_two_exchanged (Γ : Ctx signature) :
    ContextualAssignment.joinSub
      (fun sort position => localTwo Γ sort (exchangeRestrictions (Γ := []) sort position))
      (ambientTwo Γ) =
      (fun sort position => Term.var (exchangeRestrictions sort position)) := by
  funext sort position
  cases position with
  | zero => rfl
  | succ position => cases position <;> rfl

private theorem interpret_one {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualAssignment.instantiate body (ambientOne Γ) (localOne Γ) (metaVar oneIndex) =
      body oneIndex := by
  rw [ContextualAssignment.instantiate_metaVar body (ambientOne Γ) oneIndex (localOne Γ)]
  unfold ContextualAssignment.apply
  rw [join_one_identity]
  exact bind_id _

private theorem interpret_two {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualAssignment.instantiate body (ambientTwo Γ) (localTwo Γ) (metaVar twoIndex) =
      body twoIndex := by
  rw [ContextualAssignment.instantiate_metaVar body (ambientTwo Γ) twoIndex (localTwo Γ)]
  unfold ContextualAssignment.apply
  rw [join_two_identity]
  exact bind_id _

private theorem interpret_two_exchanged {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualAssignment.instantiate body (ambientTwo Γ) (localTwo Γ)
      (rename (exchangeRestrictions (Γ := [])) (metaVar twoIndex)) =
      rename exchangeRestrictions (body twoIndex) := by
  rw [ContextualAssignment.instantiate_rename]
  trans ContextualAssignment.apply body twoIndex
    (fun sort position => localTwo Γ sort (exchangeRestrictions (Γ := []) sort position))
    (ambientTwo Γ)
  · exact ContextualAssignment.instantiate_metaVar body (ambientTwo Γ) twoIndex _
  · unfold ContextualAssignment.apply
    exact (congrArg (fun valuation => bind valuation (body twoIndex))
      (join_two_exchanged Γ)).trans (bind_var_eq_rename _ _)

private theorem interpret_outside {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar outsideIndex) =
      body outsideIndex := by
  rw [ContextualAssignment.instantiate_metaVar body (identitySub Γ) outsideIndex (emptySub Γ)]
  change bind (identitySub Γ) (body outsideIndex) = body outsideIndex
  exact bind_id _

private theorem interpret_outside_under_binder {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualAssignment.instantiate body (ambientOne Γ) (localOne Γ)
      (weaken (t := nameSort) (metaVar outsideIndex)) =
      weaken (t := nameSort) (body outsideIndex) := by
  rw [weaken, ContextualAssignment.instantiate_rename,
    ContextualAssignment.instantiate_metaVar (S := signature) (M := metavariables)]
  change bind (ambientOne Γ) (body outsideIndex) = weaken (body outsideIndex)
  exact bind_var_eq_rename _ _

private theorem interpret_other {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar otherIndex) =
      body otherIndex := by
  rw [ContextualAssignment.instantiate_metaVar body (identitySub Γ) otherIndex (emptySub Γ)]
  change bind (identitySub Γ) (body otherIndex) = body otherIndex
  exact bind_id _

theorem restrictionNil_interprets {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualEquationInstances.instantiateAt restrictionNil body (emptySub Γ) =
      (restrictionTerm (nilTerm (Γ := nameSort :: Γ)), nilTerm (Γ := Γ)) := rfl

theorem restrictionExchange_interprets {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualEquationInstances.instantiateAt restrictionExchange body (emptySub Γ) =
      (restrictionTerm (restrictionTerm (body twoIndex)),
       restrictionTerm (restrictionTerm (rename exchangeRestrictions (body twoIndex)))) := by
  apply Prod.ext
  · change restrictionTerm (restrictionTerm
      (ContextualAssignment.instantiate body (ambientTwo Γ) (localTwo Γ) (metaVar twoIndex))) = _
    rw [interpret_two]
  · change restrictionTerm (restrictionTerm
      (ContextualAssignment.instantiate body (ambientTwo Γ) (localTwo Γ)
        (rename (exchangeRestrictions (Γ := [])) (metaVar twoIndex)))) = _
    rw [interpret_two_exchanged]

theorem restrictionExtrusion_interprets {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualEquationInstances.instantiateAt restrictionExtrusion body (emptySub Γ) =
      (restrictionTerm (parallelTerm (body oneIndex) (weaken (body outsideIndex))),
       parallelTerm (restrictionTerm (body oneIndex)) (body outsideIndex)) := by
  apply Prod.ext
  · change restrictionTerm (parallelTerm
      (ContextualAssignment.instantiate body (ambientOne Γ) (localOne Γ) (metaVar oneIndex))
      (ContextualAssignment.instantiate body (ambientOne Γ) (localOne Γ)
        (weaken (t := nameSort) (metaVar outsideIndex)))) = _
    rw [interpret_one, interpret_outside_under_binder]
  · change parallelTerm
      (restrictionTerm (ContextualAssignment.instantiate body (ambientOne Γ) (localOne Γ)
        (metaVar oneIndex)))
      (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ)
        (metaVar outsideIndex)) = _
    rw [interpret_one, interpret_outside]

theorem replicationUnfold_interprets {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualEquationInstances.instantiateAt replicationUnfold body (emptySub Γ) =
      (replicationTerm (body outsideIndex),
        parallelTerm (body outsideIndex) (replicationTerm (body outsideIndex))) := by
  apply Prod.ext
  · change replicationTerm
      (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar outsideIndex)) = _
    rw [interpret_outside]
  · change parallelTerm
      (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar outsideIndex))
      (replicationTerm
        (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar outsideIndex))) = _
    rw [interpret_outside]

theorem replicationNil_interprets {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualEquationInstances.instantiateAt replicationNil body (emptySub Γ) =
      (replicationTerm (nilTerm (Γ := Γ)), nilTerm (Γ := Γ)) := rfl

theorem replicationTwice_interprets {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualEquationInstances.instantiateAt replicationTwice body (emptySub Γ) =
      (replicationTerm (replicationTerm (body outsideIndex)), replicationTerm (body outsideIndex)) := by
  apply Prod.ext
  · change replicationTerm (replicationTerm
      (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar outsideIndex))) = _
    rw [interpret_outside]
  · change replicationTerm
      (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar outsideIndex)) = _
    rw [interpret_outside]

theorem replicationPar_interprets {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualEquationInstances.instantiateAt replicationPar body (emptySub Γ) =
      (replicationTerm (parallelTerm (body outsideIndex) (body otherIndex)),
       parallelTerm (replicationTerm (body outsideIndex)) (replicationTerm (body otherIndex))) := by
  apply Prod.ext
  · change replicationTerm (parallelTerm
      (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar outsideIndex))
      (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar otherIndex))) = _
    rw [interpret_outside, interpret_other]
  · change parallelTerm
      (replicationTerm (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar outsideIndex)))
      (replicationTerm (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar otherIndex))) = _
    rw [interpret_outside, interpret_other]

theorem replicationIdempotent_interprets {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualEquationInstances.instantiateAt replicationIdempotent body (emptySub Γ) =
      (parallelTerm (replicationTerm (body outsideIndex)) (replicationTerm (body outsideIndex)),
       replicationTerm (body outsideIndex)) := by
  apply Prod.ext
  · change parallelTerm
      (replicationTerm
        (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar outsideIndex)))
      (replicationTerm
        (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar outsideIndex))) = _
    rw [interpret_outside]
  · change replicationTerm
      (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar outsideIndex)) = _
    rw [interpret_outside]

/-- All ambient contexts and typed captured values enter the existing axiom
constructor, rather than a new equation relation. -/
theorem declared_instance {Γ : Ctx signature} (index : Fin equations.length)
    (body : ContextualAssignment signature metavariables Γ)
    (ordinary : Sub signature (equations.get index).ctx Γ) :
    EqClosure equations
      (ContextualEquationInstances.instantiateAt (equations.get index) body ordinary).1
      (ContextualEquationInstances.instantiateAt (equations.get index) body ordinary).2 := by
  exact EqClosure.ax index body (fun _ position => .var position) ordinary

theorem restriction_nil {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    EqClosure equations (restrictionTerm (nilTerm (Γ := nameSort :: Γ)))
      (nilTerm (Γ := Γ)) := by
  have instance' := declared_instance ⟨0, by decide⟩ body (emptySub Γ)
  change EqClosure equations
    (ContextualEquationInstances.instantiateAt restrictionNil body (emptySub Γ)).1
    (ContextualEquationInstances.instantiateAt restrictionNil body (emptySub Γ)).2 at instance'
  rw [restrictionNil_interprets] at instance'
  exact instance'

theorem restriction_exchange {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    EqClosure equations (restrictionTerm (restrictionTerm (body twoIndex)))
      (restrictionTerm (restrictionTerm (rename exchangeRestrictions (body twoIndex)))) := by
  have instance' := declared_instance ⟨1, by decide⟩ body (emptySub Γ)
  change EqClosure equations
    (ContextualEquationInstances.instantiateAt restrictionExchange body (emptySub Γ)).1
    (ContextualEquationInstances.instantiateAt restrictionExchange body (emptySub Γ)).2 at instance'
  rw [restrictionExchange_interprets] at instance'
  exact instance'

theorem restriction_extrusion {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    EqClosure equations
      (restrictionTerm (parallelTerm (body oneIndex) (weaken (body outsideIndex))))
      (parallelTerm (restrictionTerm (body oneIndex)) (body outsideIndex)) := by
  have instance' := declared_instance ⟨2, by decide⟩ body (emptySub Γ)
  change EqClosure equations
    (ContextualEquationInstances.instantiateAt restrictionExtrusion body (emptySub Γ)).1
    (ContextualEquationInstances.instantiateAt restrictionExtrusion body (emptySub Γ)).2 at instance'
  rw [restrictionExtrusion_interprets] at instance'
  exact instance'

theorem replication_unfold {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    EqClosure equations (replicationTerm (body outsideIndex))
      (parallelTerm (body outsideIndex) (replicationTerm (body outsideIndex))) := by
  have instance' := declared_instance ⟨3, by decide⟩ body (emptySub Γ)
  change EqClosure equations
    (ContextualEquationInstances.instantiateAt replicationUnfold body (emptySub Γ)).1
    (ContextualEquationInstances.instantiateAt replicationUnfold body (emptySub Γ)).2 at instance'
  rw [replicationUnfold_interprets] at instance'
  exact instance'

theorem replication_nil {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    EqClosure equations (replicationTerm (nilTerm (Γ := Γ))) (nilTerm (Γ := Γ)) := by
  have instance' := declared_instance ⟨4, by decide⟩ body (emptySub Γ)
  change EqClosure equations
    (ContextualEquationInstances.instantiateAt replicationNil body (emptySub Γ)).1
    (ContextualEquationInstances.instantiateAt replicationNil body (emptySub Γ)).2 at instance'
  rw [replicationNil_interprets] at instance'
  exact instance'

theorem replication_twice {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    EqClosure equations (replicationTerm (replicationTerm (body outsideIndex)))
      (replicationTerm (body outsideIndex)) := by
  have instance' := declared_instance ⟨5, by decide⟩ body (emptySub Γ)
  change EqClosure equations
    (ContextualEquationInstances.instantiateAt replicationTwice body (emptySub Γ)).1
    (ContextualEquationInstances.instantiateAt replicationTwice body (emptySub Γ)).2 at instance'
  rw [replicationTwice_interprets] at instance'
  exact instance'

theorem replication_par {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    EqClosure equations (replicationTerm (parallelTerm (body outsideIndex) (body otherIndex)))
      (parallelTerm (replicationTerm (body outsideIndex)) (replicationTerm (body otherIndex))) := by
  have instance' := declared_instance ⟨6, by decide⟩ body (emptySub Γ)
  change EqClosure equations
    (ContextualEquationInstances.instantiateAt replicationPar body (emptySub Γ)).1
    (ContextualEquationInstances.instantiateAt replicationPar body (emptySub Γ)).2 at instance'
  rw [replicationPar_interprets] at instance'
  exact instance'

theorem replication_idempotent {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    EqClosure equations (parallelTerm (replicationTerm (body outsideIndex)) (replicationTerm (body outsideIndex)))
      (replicationTerm (body outsideIndex)) := by
  have instance' := declared_instance ⟨7, by decide⟩ body (emptySub Γ)
  change EqClosure equations
    (ContextualEquationInstances.instantiateAt replicationIdempotent body (emptySub Γ)).1
    (ContextualEquationInstances.instantiateAt replicationIdempotent body (emptySub Γ)).2 at instance'
  rw [replicationIdempotent_interprets] at instance'
  exact instance'

/-- Supply arbitrary typed values at each declared dependency prefix. -/
def assignment {Γ : Ctx signature}
    (one : Term signature (nameSort :: Γ) processSort)
    (two : Term signature (nameSort :: nameSort :: Γ) processSort)
    (outside : Term signature Γ processSort) (other : Term signature Γ processSort := nilTerm) :
    ContextualAssignment signature metavariables Γ :=
  fun index => Fin.cases one
    (fun index => Fin.cases two
      (fun index => Fin.cases outside
        (fun index => Fin.cases other (fun index => Fin.elim0 index) index) index) index) index

/-- Restricting inaction is valid in every ambient context. -/
theorem restrict_inaction (Γ : Ctx signature) :
    EqClosure equations (restrictionTerm (nilTerm (Γ := nameSort :: Γ)))
      (nilTerm (Γ := Γ)) :=
  restriction_nil (assignment nilTerm nilTerm nilTerm)

/-- Exchange restrictions by transporting their bodies along the exchange of
the two local variables, rather than leaving a de Bruijn body unchanged. -/
theorem exchange_scopes {Γ : Ctx signature}
    (body : Term signature (nameSort :: nameSort :: Γ) processSort) :
    EqClosure equations (restrictionTerm (restrictionTerm body))
      (restrictionTerm (restrictionTerm (rename exchangeRestrictions body))) :=
  restriction_exchange (assignment nilTerm body nilTerm)

/-- The outside component has only the ambient context. Weakening it under the
restriction is the intrinsic freshness condition for extrusion. -/
theorem extrude_scope {Γ : Ctx signature}
    (inside : Term signature (nameSort :: Γ) processSort)
    (outside : Term signature Γ processSort) :
    EqClosure equations
      (restrictionTerm (parallelTerm inside (weaken outside)))
      (parallelTerm (restrictionTerm inside) outside) :=
  restriction_extrusion (assignment inside nilTerm outside)

/-- A replicated process unfolds in every ambient context. -/
theorem unfold_replication {Γ : Ctx signature} (process : Term signature Γ processSort) :
    EqClosure equations (replicationTerm process) (parallelTerm process (replicationTerm process)) :=
  replication_unfold (assignment nilTerm nilTerm process)

/-- Replicated inaction is inaction in every ambient context. -/
theorem replicate_inaction (Γ : Ctx signature) :
    EqClosure equations (replicationTerm (nilTerm (Γ := Γ))) (nilTerm (Γ := Γ)) :=
  replication_nil (assignment nilTerm nilTerm nilTerm)

/-- Replication is idempotent. -/
theorem replicate_twice {Γ : Ctx signature} (process : Term signature Γ processSort) :
    EqClosure equations (replicationTerm (replicationTerm process)) (replicationTerm process) :=
  replication_twice (assignment nilTerm nilTerm process)

/-- Replication distributes over parallel composition. -/
theorem replicate_parallel {Γ : Ctx signature} (first second : Term signature Γ processSort) :
    EqClosure equations (replicationTerm (parallelTerm first second))
      (parallelTerm (replicationTerm first) (replicationTerm second)) :=
  replication_par (assignment nilTerm nilTerm first second)

/-- Two replications of one process are one. -/
theorem replicate_duplicate {Γ : Ctx signature} (process : Term signature Γ processSort) :
    EqClosure equations (parallelTerm (replicationTerm process) (replicationTerm process)) (replicationTerm process) :=
  replication_idempotent (assignment nilTerm nilTerm process)

/-- **A guarded server unfolds**: `!x(y).P = {x(y).P, !x(y).P}`, the general unfolding at an input. -/
theorem unfold_guarded {Γ : Ctx signature}
    (channel : Term signature Γ nameSort)
    (body : Term signature (nameSort :: Γ) processSort) :
    EqClosure equations (replicationTerm (inputTerm channel body))
      (parallelTerm (inputTerm channel body) (replicationTerm (inputTerm channel body))) :=
  unfold_replication (inputTerm channel body)

/-- Actual instances retain the authored result sort and a common ambient
context at both endpoints. -/
theorem declared_instance_endpoints {Γ : Ctx signature} (index : Fin equations.length)
    (body : ContextualAssignment signature metavariables Γ)
    (ordinary : Sub signature (equations.get index).ctx Γ) :
    HasType piCalc FreeTypeContext.empty Γ
        (erase (ContextualEquationInstances.instantiateAt (equations.get index) body ordinary).1)
        (equations.get index).sort ∧
      HasType piCalc FreeTypeContext.empty Γ
        (erase (ContextualEquationInstances.instantiateAt (equations.get index) body ordinary).2)
        (equations.get index).sort ∧
      (erase (ContextualEquationInstances.instantiateAt (equations.get index) body ordinary).1).isWellScopedAt
        Γ.length = true ∧
      (erase (ContextualEquationInstances.instantiateAt (equations.get index) body ordinary).2).isWellScopedAt
        Γ.length = true :=
  ⟨erase_typed _, erase_typed _, erase_wellScoped _, erase_wellScoped _⟩

/-- Substitution transports the declared instance itself as well as its
equality proof, including substitutions into captured ambient values. -/
theorem declared_instance_substitution {Γ Δ : Ctx signature} (index : Fin equations.length)
    (body : ContextualAssignment signature metavariables Γ)
    (ordinary : Sub signature (equations.get index).ctx Γ) (sigma : Sub signature Γ Δ) :
    EqClosure equations
        (bind sigma (ContextualEquationInstances.instantiateAt (equations.get index) body ordinary).1)
        (bind sigma (ContextualEquationInstances.instantiateAt (equations.get index) body ordinary).2) ∧
      Prod.map (bind sigma) (bind sigma)
        (ContextualEquationInstances.instantiateAt (equations.get index) body ordinary) =
        ContextualEquationInstances.instantiateAt (equations.get index)
          (ContextualAssignment.mapSub sigma body) (fun sort position => bind sigma (ordinary sort position)) :=
  ⟨eqClosure_bind sigma (declared_instance index body ordinary),
    ContextualEquationInstances.instantiateAt_substitution _ body ordinary sigma⟩

theorem declared_instance_renaming {Γ Δ : Ctx signature} (index : Fin equations.length)
    (body : ContextualAssignment signature metavariables Γ)
    (ordinary : Sub signature (equations.get index).ctx Γ) (rho : Ren signature Γ Δ) :
    EqClosure equations
        (rename rho (ContextualEquationInstances.instantiateAt (equations.get index) body ordinary).1)
        (rename rho (ContextualEquationInstances.instantiateAt (equations.get index) body ordinary).2) ∧
      Prod.map (rename rho) (rename rho)
        (ContextualEquationInstances.instantiateAt (equations.get index) body ordinary) =
        ContextualEquationInstances.instantiateAt (equations.get index)
          (ContextualAssignment.mapRen rho body) (fun sort position => rename rho (ordinary sort position)) :=
  ⟨eqClosure_rename rho (declared_instance index body ordinary),
    ContextualEquationInstances.instantiateAt_renaming _ body ordinary rho⟩

theorem parallel_congr {Γ : Ctx signature}
    {left left' right right' : Term signature Γ processSort}
    (first : EqClosure equations left left') (second : EqClosure equations right right') :
    EqClosure equations (parallelTerm left right) (parallelTerm left' right') :=
  .cong parallelOperator (.cons first (.cons second .nil))

theorem restriction_congr {Γ : Ctx signature}
    {body body' : Term signature (nameSort :: Γ) processSort}
    (related : EqClosure equations body body') :
    EqClosure equations (restrictionTerm body) (restrictionTerm body') :=
  .cong restrictionOperator (.cons related .nil)

theorem input_congr {Γ : Ctx signature}
    {channel channel' : Term signature Γ nameSort}
    {body body' : Term signature (nameSort :: Γ) processSort}
    (channels : EqClosure equations channel channel')
    (bodies : EqClosure equations body body') :
    EqClosure equations (inputTerm channel body) (inputTerm channel' body') :=
  .cong inputOperator (.cons channels (.cons bodies .nil))

theorem replication_congr {Γ : Ctx signature}
    {process process' : Term signature Γ processSort}
    (related : EqClosure equations process process') :
    EqClosure equations (replicationTerm process) (replicationTerm process') :=
  .cong replicationOperator (.cons related .nil)

namespace Controls

theorem restriction_nil_instance_in_closure :
    EqClosure equations (restrictionTerm (nilTerm (Γ := [nameSort])))
      (nilTerm (Γ := [])) :=
  restrict_inaction []

def exchangeBody : Term signature [nameSort, nameSort] processSort :=
  outputTerm (.var .zero) (.var (.succ .zero))

def extrusionInside : Term signature [nameSort, nameSort] processSort :=
  outputTerm (.var .zero) (.var (.succ .zero))

def extrusionOutside : Term signature [nameSort] processSort :=
  outputTerm (.var .zero) (.var .zero)

def exchangeAssignment : ContextualAssignment signature metavariables [] :=
  assignment nilTerm exchangeBody nilTerm

def extrusionAssignment : ContextualAssignment signature metavariables [nameSort] :=
  assignment extrusionInside nilTerm extrusionOutside

theorem exchange_instance_has_permuted_endpoint :
    Prod.map erase erase
      (ContextualEquationInstances.instantiateAt restrictionExchange exchangeAssignment (emptySub [])) =
      (.apply "PiNu" [.lambda none (.apply "PiNu" [.lambda none
        (.apply "PiOut" [.bvar 0, .bvar 1])])],
       .apply "PiNu" [.lambda none (.apply "PiNu" [.lambda none
        (.apply "PiOut" [.bvar 1, .bvar 0])])]) := by
  rw [restrictionExchange_interprets]
  rfl

/-- Keeping the original body's indices gives a different endpoint from the
declared exchange instance. -/
theorem exchange_endpoint_differs_without_permutation :
    erase (ContextualEquationInstances.instantiateAt restrictionExchange
      exchangeAssignment (emptySub [])).2 ≠
      .apply "PiNu" [.lambda none (.apply "PiNu" [.lambda none
        (.apply "PiOut" [.bvar 0, .bvar 1])])] := by
  rw [restrictionExchange_interprets]
  decide

theorem exchange_instance_in_closure :
    EqClosure equations (restrictionTerm (restrictionTerm exchangeBody))
      (restrictionTerm (restrictionTerm (rename exchangeRestrictions exchangeBody))) :=
  exchange_scopes exchangeBody

theorem extrusion_instance_preserves_ambient_reference :
    Prod.map erase erase
      (ContextualEquationInstances.instantiateAt restrictionExtrusion
        extrusionAssignment (emptySub [nameSort])) =
      (.apply "PiNu" [.lambda none (.collection .hashBag
        [.apply "PiOut" [.bvar 0, .bvar 1], .apply "PiOut" [.bvar 1, .bvar 1]] none)],
       .collection .hashBag
        [.apply "PiNu" [.lambda none (.apply "PiOut" [.bvar 0, .bvar 1])],
         .apply "PiOut" [.bvar 0, .bvar 0]] none) := by
  rw [restrictionExtrusion_interprets]
  rfl

theorem extrusion_instance_in_closure :
    EqClosure equations (restrictionTerm (parallelTerm extrusionInside (weaken extrusionOutside)))
      (parallelTerm (restrictionTerm extrusionInside) extrusionOutside) :=
  extrude_scope extrusionInside extrusionOutside

private theorem lifted_pattern_not_zero (pattern : Pattern) :
    liftBVars 0 1 pattern ≠ .bvar 0 := by
  cases pattern <;> simp [liftBVars]

private theorem lifted_pattern_not_dependent_output (pattern : Pattern) :
    liftBVars 0 1 pattern ≠ .apply "PiOut" [.bvar 0, .bvar 0] := by
  cases pattern with
  | apply constructor arguments =>
    cases arguments with
    | nil => simp [liftBVars, liftBVarsList]
    | cons first rest =>
      intro equality
      exact lifted_pattern_not_zero first (List.cons.inj (Pattern.apply.inj equality).2).1
  | bvar index => simp [liftBVars]
  | fvar name => simp [liftBVars]
  | lambda name body => simp [liftBVars]
  | multiLambda count names body => simp [liftBVars]
  | subst body value => simp [liftBVars]
  | collection kind elements rest => simp [liftBVars]

/-- An outside value, in any ambient context, cannot acquire a reference to
the newly introduced restriction variable through weakening. -/
theorem dependent_component_cannot_be_extruded {Γ : Ctx signature}
    (outside : Term signature Γ processSort) :
    erase (weaken (t := nameSort) outside) ≠
      .apply "PiOut" [.bvar 0, .bvar 0] := by
  rw [erase_weaken]
  exact lifted_pattern_not_dependent_output _

def guardedChannel : Term signature [nameSort] nameSort := .var .zero

def guardedBody : Term signature [nameSort, nameSort] processSort :=
  outputTerm (.var (.succ .zero)) (.var .zero)

theorem guarded_instance_retains_server :
    Prod.map erase erase
      (ContextualEquationInstances.instantiateAt replicationUnfold
        (assignment nilTerm nilTerm (inputTerm guardedChannel guardedBody)) (emptySub [nameSort])) =
      (.apply "PiRep" [.apply "PiInp" [.bvar 0, .lambda none (.apply "PiOut" [.bvar 1, .bvar 0])]],
       .collection .hashBag
        [.apply "PiInp" [.bvar 0, .lambda none (.apply "PiOut" [.bvar 1, .bvar 0])],
         .apply "PiRep" [.apply "PiInp" [.bvar 0, .lambda none (.apply "PiOut" [.bvar 1, .bvar 0])]]] none) := by
  rw [replicationUnfold_interprets]
  rfl

theorem guarded_instance_in_closure :
    EqClosure equations (replicationTerm (inputTerm guardedChannel guardedBody))
      (parallelTerm (inputTerm guardedChannel guardedBody)
        (replicationTerm (inputTerm guardedChannel guardedBody))) :=
  unfold_guarded guardedChannel guardedBody

end Controls

end Mettapedia.Languages.ProcessCalculi.PiCalculus.StaticEquations
