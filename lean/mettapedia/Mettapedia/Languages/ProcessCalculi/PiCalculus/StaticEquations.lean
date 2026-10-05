import Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
import Mettapedia.GSLT.LanguageDef.BindingSignatureSubstitution
import Mettapedia.OSLF.Syntax.ContextualEquationInstances
import Mettapedia.OSLF.Syntax.EquationalQuotient

/-!
# Typed scope equations on the authored pi signature

The operators below are derived from the actual constructors of `piCalc`.
Four equations use the existing binding-signature templates and equation
closure: restriction of inaction, exchange of restrictions, scope extrusion,
and guarded replication unfolding. Every instance retains the separately typed
dependency prefix and ambient context of its metavariable bodies.

These laws supplement the parallel collection algebra. They are intrinsic
static equations over the authored one-sort signature; they do not change
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

def nilOperator : signature.Op processSort :=
  .constructor piCalc.terms[0] (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, piCalc]) .nil

def parallelOperator : signature.Op processSort :=
  .collectionConstructor piCalc.terms[1] (List.getElem_mem (by decide))
    "ps" .hashBag processSort rfl 2

def inputOperator : signature.Op processSort :=
  .constructor piCalc.terms[2] (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, piCalc])
    (.cons (.simple "x" processSort)
      (.cons (.abstraction none "body" processSort processSort) .nil))

def outputOperator : signature.Op processSort :=
  .constructor piCalc.terms[3] (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, piCalc])
    (.cons (.simple "x" processSort) (.cons (.simple "z" processSort) .nil))

def restrictionOperator : signature.Op processSort :=
  .constructor piCalc.terms[4] (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, piCalc])
    (.cons (.abstraction none "body" processSort processSort) .nil)

def replicationOperator : signature.Op processSort :=
  .constructor piCalc.terms[5] (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, piCalc])
    (.cons (.simple "x" processSort)
      (.cons (.abstraction none "body" processSort processSort) .nil))

def nilTerm {Γ : Ctx signature} : Term signature Γ processSort :=
  .op nilOperator .nil

def parallelTerm {Γ : Ctx signature}
    (left right : Term signature Γ processSort) : Term signature Γ processSort :=
  .op parallelOperator (.cons left (.cons right .nil))

def inputTerm {Γ : Ctx signature} (channel : Term signature Γ processSort)
    (body : Term signature (processSort :: Γ) processSort) : Term signature Γ processSort :=
  .op inputOperator (.cons channel (.cons body .nil))

def outputTerm {Γ : Ctx signature} (channel datum : Term signature Γ processSort) :
    Term signature Γ processSort :=
  .op outputOperator (.cons channel (.cons datum .nil))

def restrictionTerm {Γ : Ctx signature}
    (body : Term signature (processSort :: Γ) processSort) : Term signature Γ processSort :=
  .op restrictionOperator (.cons body .nil)

def replicationTerm {Γ : Ctx signature} (channel : Term signature Γ processSort)
    (body : Term signature (processSort :: Γ) processSort) : Term signature Γ processSort :=
  .op replicationOperator (.cons channel (.cons body .nil))

@[simp] theorem erase_nilTerm {Γ : Ctx signature} :
    erase (nilTerm (Γ := Γ)) = .apply "PiNil" [] := rfl

@[simp] theorem erase_parallelTerm {Γ : Ctx signature}
    (left right : Term signature Γ processSort) :
    erase (parallelTerm left right) =
      .collection .hashBag [erase left, erase right] none := rfl

@[simp] theorem erase_restrictionTerm {Γ : Ctx signature}
    (body : Term signature (processSort :: Γ) processSort) :
    erase (restrictionTerm body) = .apply "PiNu" [.lambda none (erase body)] := rfl

@[simp] theorem erase_inputTerm {Γ : Ctx signature} (channel : Term signature Γ processSort)
    (body : Term signature (processSort :: Γ) processSort) :
    erase (inputTerm channel body) = .apply "PiInp" [erase channel, .lambda none (erase body)] := rfl

@[simp] theorem erase_outputTerm {Γ : Ctx signature}
    (channel datum : Term signature Γ processSort) :
    erase (outputTerm channel datum) = .apply "PiOut" [erase channel, erase datum] := rfl

@[simp] theorem erase_replicationTerm {Γ : Ctx signature}
    (channel : Term signature Γ processSort)
    (body : Term signature (processSort :: Γ) processSort) :
    erase (replicationTerm channel body) =
      .apply "PiRep" [erase channel, .lambda none (erase body)] := rfl

/-- The body of a scope law may depend on one or two local variables. The
extruded component and listening channel have no local dependency prefix. -/
abbrev metavariables : List (MetaArity signature) :=
  [([processSort], processSort), ([processSort, processSort], processSort),
   ([], processSort), ([], processSort)]

abbrev oneIndex : Fin metavariables.length := ⟨0, by decide⟩
abbrev twoIndex : Fin metavariables.length := ⟨1, by decide⟩
abbrev outsideIndex : Fin metavariables.length := ⟨2, by decide⟩
abbrev channelIndex : Fin metavariables.length := ⟨3, by decide⟩
abbrev schemaSignature := withMetas signature metavariables

private def schemaNil {Γ : Ctx schemaSignature} : Term schemaSignature Γ processSort :=
  .op (.inl nilOperator) .nil

private def schemaParallel {Γ : Ctx schemaSignature}
    (left right : Term schemaSignature Γ processSort) : Term schemaSignature Γ processSort :=
  .op (.inl parallelOperator) (.cons left (.cons right .nil))

private def schemaRestriction {Γ : Ctx schemaSignature}
    (body : Term schemaSignature (processSort :: Γ) processSort) :
    Term schemaSignature Γ processSort :=
  .op (.inl restrictionOperator) (.cons body .nil)

private def schemaInput {Γ : Ctx schemaSignature} (channel : Term schemaSignature Γ processSort)
    (body : Term schemaSignature (processSort :: Γ) processSort) :
    Term schemaSignature Γ processSort :=
  .op (.inl inputOperator) (.cons channel (.cons body .nil))

private def schemaReplication {Γ : Ctx schemaSignature}
    (channel : Term schemaSignature Γ processSort)
    (body : Term schemaSignature (processSort :: Γ) processSort) :
    Term schemaSignature Γ processSort :=
  .op (.inl replicationOperator) (.cons channel (.cons body .nil))

/-- Exchange the two local restriction variables while keeping each ambient
variable at its original position. -/
def exchangeRestrictions {Γ : List TypeExpr} (sort : TypeExpr)
    (position : Var (processSort :: processSort :: Γ) sort) :
    Var (processSort :: processSort :: Γ) sort := by
  cases position with
  | zero => exact .succ .zero
  | succ position =>
    cases position with
    | zero => exact .zero
    | succ position => exact .succ (.succ position)

@[simp] theorem exchangeRestrictions_involution {Γ : List TypeExpr}
    {sort : TypeExpr} (position : Var (processSort :: processSort :: Γ) sort) :
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
    (schemaParallel (metaVar oneIndex) (weaken (t := processSort) (metaVar outsideIndex)))
  rhs := schemaParallel (schemaRestriction (metaVar oneIndex)) (metaVar outsideIndex)

def guardedUnfolding : EqAxiom signature metavariables where
  ctx := []
  sort := processSort
  lhs := schemaReplication (metaVar channelIndex) (metaVar oneIndex)
  rhs := schemaParallel
    (schemaInput (metaVar channelIndex) (metaVar oneIndex))
    (schemaReplication (metaVar channelIndex) (metaVar oneIndex))

/-- The four non-monoid static laws of the maintained guarded pi dialect. -/
def equations : List (EqAxiom signature metavariables) :=
  [restrictionNil, restrictionExchange, restrictionExtrusion, guardedUnfolding]

private def identitySub (Γ : Ctx signature) : Sub signature Γ Γ := fun _ v => .var v
private def emptySub (Γ : Ctx signature) : Sub signature [] Γ := fun _ v => nomatch v
private def localOne (Γ : Ctx signature) : Sub signature [processSort] (processSort :: Γ) :=
  liftSub (emptySub Γ) [processSort]
private def localTwo (Γ : Ctx signature) :
    Sub signature [processSort, processSort] (processSort :: processSort :: Γ) :=
  liftSub (emptySub Γ) [processSort, processSort]
private def ambientOne (Γ : Ctx signature) : Sub signature Γ (processSort :: Γ) :=
  ContextualAssignment.weakenSub (S := signature) [processSort] (identitySub Γ)
private def ambientTwo (Γ : Ctx signature) :
    Sub signature Γ (processSort :: processSort :: Γ) :=
  ContextualAssignment.weakenSub (S := signature) [processSort] (ambientOne Γ)

private theorem join_one_identity (Γ : Ctx signature) :
    ContextualAssignment.joinSub (localOne Γ) (ambientOne Γ) =
      identitySub (processSort :: Γ) := by
  funext sort position
  cases position <;> rfl

private theorem join_two_identity (Γ : Ctx signature) :
    ContextualAssignment.joinSub (localTwo Γ) (ambientTwo Γ) =
      identitySub (processSort :: processSort :: Γ) := by
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
      (weaken (t := processSort) (metaVar outsideIndex)) =
      weaken (t := processSort) (body outsideIndex) := by
  rw [weaken, ContextualAssignment.instantiate_rename,
    ContextualAssignment.instantiate_metaVar (S := signature) (M := metavariables)]
  change bind (ambientOne Γ) (body outsideIndex) = weaken (body outsideIndex)
  exact bind_var_eq_rename _ _

private theorem interpret_channel {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ) (metaVar channelIndex) =
      body channelIndex := by
  rw [ContextualAssignment.instantiate_metaVar body (identitySub Γ) channelIndex (emptySub Γ)]
  change bind (identitySub Γ) (body channelIndex) = body channelIndex
  exact bind_id _

theorem restrictionNil_interprets {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualEquationInstances.instantiateAt restrictionNil body (emptySub Γ) =
      (restrictionTerm (nilTerm (Γ := processSort :: Γ)), nilTerm (Γ := Γ)) := rfl

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
        (weaken (t := processSort) (metaVar outsideIndex)))) = _
    rw [interpret_one, interpret_outside_under_binder]
  · change parallelTerm
      (restrictionTerm (ContextualAssignment.instantiate body (ambientOne Γ) (localOne Γ)
        (metaVar oneIndex)))
      (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ)
        (metaVar outsideIndex)) = _
    rw [interpret_one, interpret_outside]

theorem guardedUnfolding_interprets {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    ContextualEquationInstances.instantiateAt guardedUnfolding body (emptySub Γ) =
      (replicationTerm (body channelIndex) (body oneIndex),
       parallelTerm (inputTerm (body channelIndex) (body oneIndex))
         (replicationTerm (body channelIndex) (body oneIndex))) := by
  apply Prod.ext
  · change replicationTerm
      (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ)
        (metaVar channelIndex))
      (ContextualAssignment.instantiate body (ambientOne Γ) (localOne Γ)
        (metaVar oneIndex)) = _
    rw [interpret_channel, interpret_one]
  · change parallelTerm
      (inputTerm
        (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ)
          (metaVar channelIndex))
        (ContextualAssignment.instantiate body (ambientOne Γ) (localOne Γ)
          (metaVar oneIndex)))
      (replicationTerm
        (ContextualAssignment.instantiate body (identitySub Γ) (emptySub Γ)
          (metaVar channelIndex))
        (ContextualAssignment.instantiate body (ambientOne Γ) (localOne Γ)
          (metaVar oneIndex))) = _
    rw [interpret_channel, interpret_one]

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
    EqClosure equations (restrictionTerm (nilTerm (Γ := processSort :: Γ)))
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

theorem guarded_unfolding {Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Γ) :
    EqClosure equations (replicationTerm (body channelIndex) (body oneIndex))
      (parallelTerm (inputTerm (body channelIndex) (body oneIndex))
        (replicationTerm (body channelIndex) (body oneIndex))) := by
  have instance' := declared_instance ⟨3, by decide⟩ body (emptySub Γ)
  change EqClosure equations
    (ContextualEquationInstances.instantiateAt guardedUnfolding body (emptySub Γ)).1
    (ContextualEquationInstances.instantiateAt guardedUnfolding body (emptySub Γ)).2 at instance'
  rw [guardedUnfolding_interprets] at instance'
  exact instance'

/-- Supply arbitrary typed values at each declared dependency prefix. -/
def assignment {Γ : Ctx signature}
    (one : Term signature (processSort :: Γ) processSort)
    (two : Term signature (processSort :: processSort :: Γ) processSort)
    (outside channel : Term signature Γ processSort) :
    ContextualAssignment signature metavariables Γ :=
  fun index => Fin.cases one
    (fun index => Fin.cases two
      (fun index => Fin.cases outside
        (fun index => Fin.cases channel (fun index => Fin.elim0 index) index) index) index) index

/-- Restricting inaction is valid in every ambient context. -/
theorem restrict_inaction (Γ : Ctx signature) :
    EqClosure equations (restrictionTerm (nilTerm (Γ := processSort :: Γ)))
      (nilTerm (Γ := Γ)) :=
  restriction_nil (assignment nilTerm nilTerm nilTerm nilTerm)

/-- Exchange restrictions by transporting their bodies along the exchange of
the two local variables, rather than leaving a de Bruijn body unchanged. -/
theorem exchange_scopes {Γ : Ctx signature}
    (body : Term signature (processSort :: processSort :: Γ) processSort) :
    EqClosure equations (restrictionTerm (restrictionTerm body))
      (restrictionTerm (restrictionTerm (rename exchangeRestrictions body))) :=
  restriction_exchange (assignment nilTerm body nilTerm nilTerm)

/-- The outside component has only the ambient context. Weakening it under the
restriction is the intrinsic freshness condition for extrusion. -/
theorem extrude_scope {Γ : Ctx signature}
    (inside : Term signature (processSort :: Γ) processSort)
    (outside : Term signature Γ processSort) :
    EqClosure equations
      (restrictionTerm (parallelTerm inside (weaken outside)))
      (parallelTerm (restrictionTerm inside) outside) :=
  restriction_extrusion (assignment inside nilTerm outside nilTerm)

theorem unfold_guarded {Γ : Ctx signature}
    (channel : Term signature Γ processSort)
    (body : Term signature (processSort :: Γ) processSort) :
    EqClosure equations (replicationTerm channel body)
      (parallelTerm (inputTerm channel body) (replicationTerm channel body)) :=
  guarded_unfolding (assignment body nilTerm nilTerm channel)

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
    {body body' : Term signature (processSort :: Γ) processSort}
    (related : EqClosure equations body body') :
    EqClosure equations (restrictionTerm body) (restrictionTerm body') :=
  .cong restrictionOperator (.cons related .nil)

theorem input_congr {Γ : Ctx signature}
    {channel channel' : Term signature Γ processSort}
    {body body' : Term signature (processSort :: Γ) processSort}
    (channels : EqClosure equations channel channel')
    (bodies : EqClosure equations body body') :
    EqClosure equations (inputTerm channel body) (inputTerm channel' body') :=
  .cong inputOperator (.cons channels (.cons bodies .nil))

theorem replication_congr {Γ : Ctx signature}
    {channel channel' : Term signature Γ processSort}
    {body body' : Term signature (processSort :: Γ) processSort}
    (channels : EqClosure equations channel channel')
    (bodies : EqClosure equations body body') :
    EqClosure equations (replicationTerm channel body) (replicationTerm channel' body') :=
  .cong replicationOperator (.cons channels (.cons bodies .nil))

namespace Controls

theorem restriction_nil_instance_in_closure :
    EqClosure equations (restrictionTerm (nilTerm (Γ := [processSort])))
      (nilTerm (Γ := [])) :=
  restrict_inaction []

def exchangeBody : Term signature [processSort, processSort] processSort :=
  outputTerm (.var .zero) (.var (.succ .zero))

def extrusionInside : Term signature [processSort, processSort] processSort :=
  outputTerm (.var .zero) (.var (.succ .zero))

def extrusionOutside : Term signature [processSort] processSort :=
  outputTerm (.var .zero) (.var .zero)

def exchangeAssignment : ContextualAssignment signature metavariables [] :=
  assignment nilTerm exchangeBody nilTerm nilTerm

def extrusionAssignment : ContextualAssignment signature metavariables [processSort] :=
  assignment extrusionInside nilTerm extrusionOutside nilTerm

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
        extrusionAssignment (emptySub [processSort])) =
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
    erase (weaken (t := processSort) outside) ≠
      .apply "PiOut" [.bvar 0, .bvar 0] := by
  rw [erase_weaken]
  exact lifted_pattern_not_dependent_output _

def guardedChannel : Term signature [processSort] processSort := .var .zero

def guardedBody : Term signature [processSort, processSort] processSort :=
  outputTerm (.var (.succ .zero)) (.var .zero)

theorem guarded_instance_retains_server :
    Prod.map erase erase
      (ContextualEquationInstances.instantiateAt guardedUnfolding
        (assignment guardedBody nilTerm nilTerm guardedChannel) (emptySub [processSort])) =
      (.apply "PiRep" [.bvar 0, .lambda none (.apply "PiOut" [.bvar 1, .bvar 0])],
       .collection .hashBag
        [.apply "PiInp" [.bvar 0, .lambda none (.apply "PiOut" [.bvar 1, .bvar 0])],
         .apply "PiRep" [.bvar 0, .lambda none (.apply "PiOut" [.bvar 1, .bvar 0])]] none) := by
  rw [guardedUnfolding_interprets]
  rfl

theorem guarded_instance_in_closure :
    EqClosure equations (replicationTerm guardedChannel guardedBody)
      (parallelTerm (inputTerm guardedChannel guardedBody)
        (replicationTerm guardedChannel guardedBody)) :=
  unfold_guarded guardedChannel guardedBody

end Controls

end Mettapedia.Languages.ProcessCalculi.PiCalculus.StaticEquations
