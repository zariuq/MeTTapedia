import Mettapedia.Logic.HOL.GuardedConstructorMethod
import Mettapedia.Logic.HOL.IndexedConstructorInductionControls

/-!
# A guarded method with a genuine proposition-valued index

The constructor retains one proposition field. Its admissibility predicate
and result index read that field. The motive requires that index, so the
false-field case cannot be admitted merely by deleting the field guard.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.GuardedConstructorMethodControls

open FiniteConstructorEncoding CurriedPredicates IndexedConstructorGuards
open IndexedConstructorInductionControls (Base Symbol number space fields only property constructor children)

def inventory {Γ : Ctx Base} : ConstructorPrograms Symbol Γ where
  fields := fields
  number := number
  index := .prop
  numeral := fun value => .const (.numeral value)
  allowed := Fin.cases (.lam (.var .vz)) (fun impossible => Fin.elim0 impossible)
  result := Fin.cases (.lam (.var .vz)) (fun impossible => Fin.elim0 impossible)

def positions {Γ : Ctx Base} : PositionPrograms (inventory (Γ := Γ)) where
  graph := Fin.cases (.lam (.lam (.lam .bot))) (fun impossible => Fin.elim0 impossible)

theorem inventory_subst {Γ Ξ : Ctx Base} (images : Subst Symbol Γ Ξ) :
    (inventory (Γ := Γ)).subst images = inventory := by
  unfold inventory ConstructorPrograms.subst
  simp only [HOL.subst]
  congr 1
  all_goals
    funext occurrence
    refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    rfl

theorem property_weaken {Γ : Ctx Base} {bound : Ty Base} :
    weaken (σ := bound) (property (Γ := Γ)) = property := rfl

def cases {Γ : Ctx Base} {assumptions : List (Formula Symbol Γ)}
    (construct : Term Symbol Γ (number ⇒ payloadType fields ⇒ (number ⇒ space) ⇒ space))
    (descendants : Term Symbol Γ (number ⇒ space))
    (condition : Term Symbol Γ (payloadType fields ⇒ .prop)) :
    inventory.IndexedCases construct descendants condition property assumptions := by
  intro Ξ images occurrence arguments
  have same : occurrence = only := Fin.ext (by
    change occurrence.val = 0
    have bound : occurrence.val < 1 := occurrence.isLt
    omega)
  subst occurrence
  rcases arguments with ⟨field, ⟨⟩⟩
  let localInventory := inventory.subst images
  let value := localInventory.constructorValue (HOL.subst images construct) only
    (field, PUnit.unit) (HOL.subst images descendants)
  let result := applyFields [.prop] (localInventory.result only) (field, PUnit.unit)
  let hypotheses := applyArguments [.prop] (localInventory.allowed only) (field, PUnit.unit) ::
    .app (HOL.subst images condition) (encode fields only (field, PUnit.unit)) :: assumptions.map (HOL.subst images)
  have allowed : ProofSyntax Symbol hypotheses result := .hyp 0
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.impE (ProofSyntax.eqPropER (IndexedConstructorInductionControls.property_beta value result)) allowed)
  simp only [property, HOL.subst, Subst.lift]
  rfl

theorem cases_free {Γ : Ctx Base} {assumptions : List (Formula Symbol Γ)}
    (construct : Term Symbol Γ (number ⇒ payloadType fields ⇒ (number ⇒ space) ⇒ space))
    (descendants : Term Symbol Γ (number ⇒ space))
    (condition : Term Symbol Γ (payloadType fields ⇒ .prop))
    {Ξ : Ctx Base} (images : Subst Symbol Γ Ξ) occurrence arguments :
    (cases (assumptions := assumptions) construct descendants condition images occurrence arguments).FunctionExtensionalityFree := by
  have same : occurrence = only := Fin.ext (by
    change occurrence.val = 0
    have bound : occurrence.val < 1 := occurrence.isLt
    omega)
  subst occurrence
  rcases arguments with ⟨field, ⟨⟩⟩
  unfold cases
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨IndexedConstructorInductionControls.property_beta_free _ _, trivial⟩

def zero : ClosedTerm Symbol space := .const .bottom
def injectivity : ClosedFormula Symbol := ConstructorInjectivity.statement constructor

def rows (occurrence : Fin inventory.fields.length) :
    ProofSyntax Symbol (weakenHyps (σ := number ⇒ space)
      (weakenHyps (σ := payloadType fields) (weakenHyps (σ := number) [injectivity])))
      (positions.methodRow zero constructor property occurrence) := by
  let signature := positions.contextual zero constructor
  let images : Subst Symbol [] signature.constructorContext := positions.methodScope zero constructor
  let condition := signature.constructorScope.childPredicate
    (weaken (weaken (weaken (positions.strengthened zero constructor property)))) signature.constructorChildren
  apply (inventory.subst images).clausesOfCases (HOL.subst images constructor) signature.constructorChildren condition
    (weaken (weaken (weaken property)))
  intro Ξ later row arguments
  have same : row = only := Fin.ext (by
    change row.val = 0
    have bound : row.val < 1 := row.isLt
    omega)
  subst row
  exact cases (assumptions := weakenHyps (σ := number ⇒ space)
    (weakenHyps (σ := payloadType fields) (weakenHyps (σ := number) [injectivity])))
    (HOL.subst images constructor) signature.constructorChildren condition later only arguments

def method : ProofSyntax Symbol [injectivity] ((positions.contextual zero constructor).closedMethod
    (positions.strengthened zero constructor property)
    (IndexedPredicateInduction.lift (inventory.rootProgram constructor) property)) :=
  positions.methodFromRows zero constructor property (.hyp 0) rows

theorem rows_free (occurrence : Fin inventory.fields.length) : (rows occurrence).FunctionExtensionalityFree := by
  unfold rows
  apply ConstructorPrograms.clausesOfCases_free
  intro Ξ images row arguments
  have same : row = only := Fin.ext (by
    change row.val = 0
    have bound : row.val < 1 := row.isLt
    omega)
  subst row
  exact cases_free _ _ _ _ _ _

theorem method_free : method.FunctionExtensionalityFree := by
  unfold method
  apply PositionPrograms.methodFromRows_free
  · trivial
  · exact rows_free

theorem false_field_guard_cannot_be_dropped :
    ¬ Nonempty (ProofSyntax Symbol []
      (.app (.app property (inventory.constructorValue constructor only (.bot, PUnit.unit) children))
        (applyFields [.prop] (inventory.result only) (.bot, PUnit.unit)))) := by
  rintro ⟨proof⟩
  have invalid := Soundness.extTheorem_sound proof.erase IndexedConstructorInductionControls.model
    (IndexedConstructorInductionControls.model.functionsRespectEqv_of_fullDomains IndexedConstructorInductionControls.full)
  change False at invalid
  exact invalid

#print axioms method_free
#print axioms false_field_guard_cannot_be_dropped

end Mettapedia.Logic.HOL.GuardedConstructorMethodControls
