import Mettapedia.Logic.HOL.IndexedConstructorInduction
import Mettapedia.Logic.HOL.ConstructorNonbottom

/-!
# Retained non-bottom induction over finite constructor programs

The existing position-program induction engine consumes cases at their
ordered fields and computed result indices. The complete child-condition
premise is retained. This construction needs only finite syntax programs,
not their source registry or a semantic interpretation of the carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms

open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (inventory : ConstructorPrograms Const Γ) {space : Ty Base}
    (bottom : Term Const Γ space)
    (constructor : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (children : Term Const Γ (inventory.number ⇒ space))
    (childCondition : Term Const Γ (payloadType inventory.fields ⇒ .prop))
    {assumptions : List (Formula Const Γ)}

def nonbottomIndexedCases
    (separation : ProofSyntax Const assumptions (ConstructorNonbottom.separation constructor bottom)) :
    inventory.IndexedCases constructor children childCondition
      (ConstructorNonbottom.motive bottom inventory.index) assumptions := by
  intro Ξ images occurrence arguments
  let shifted := inventory.subst images
  let currentConstructor := HOL.subst images constructor
  let currentBottom := HOL.subst images bottom
  let descendants := HOL.subst images children
  let data := encode inventory.fields occurrence arguments
  let value := shifted.constructorValue currentConstructor occurrence arguments descendants
  let index := applyFields _ (shifted.result occurrence) arguments
  let fieldGuard := applyArguments _ (shifted.allowed occurrence) arguments
  let childGuard := Term.app (HOL.subst images childCondition) data
  let moved := ProofSyntax.castIndices rfl (ConstructorNonbottom.subst_separation constructor bottom images)
    (ProofSyntax.subst images separation)
  let available := (moved.prepend childGuard).prepend fieldGuard
  apply ProofSyntax.castIndices rfl
    (congrArg (fun term => Term.app (Term.app term value) index)
      (ConstructorNonbottom.subst_motive bottom inventory.index images).symm)
  exact .impE (.eqPropER (ConstructorNonbottom.motive_beta currentBottom value index))
    (ConstructorNonbottom.specialize currentConstructor currentBottom
      (shifted.numeral occurrence.val) data descendants available)

theorem nonbottomIndexedCases_free
    (separation : ProofSyntax Const assumptions (ConstructorNonbottom.separation constructor bottom))
    (free : separation.FunctionExtensionalityFree) {Ξ : Ctx Base}
    (images : Subst Const Γ Ξ) occurrence arguments :
    (inventory.nonbottomIndexedCases bottom constructor children childCondition separation
      images occurrence arguments).FunctionExtensionalityFree := by
  unfold nonbottomIndexedCases
  dsimp only [id]
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨ConstructorNonbottom.motive_beta_free _ _ _, ?_⟩
  apply ConstructorNonbottom.specialize_free
  simp only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
    ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.functionExtensionalityFree_subst]
  exact free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {inventory : ConstructorPrograms Const Γ} (positions : PositionPrograms inventory) {space : Ty Base}
    (bottom : Term Const Γ space)
    (constructor : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))

private theorem scope_subst (signature : RecursiveSpacePredicate.Contextual Const Γ)
    {type : Ty Base} (term : Term Const Γ type) {Ξ : Ctx Base}
    (images : Subst Const signature.constructorContext Ξ) :
    HOL.subst images (weaken (weaken (weaken term))) =
      HOL.subst (Subst.comp images (Subst.ofRename signature.constructorRenaming)) term := by
  rw [← signature.rename_constructorRenaming, ← subst_ofRename, HOL.subst_comp]

def nonbottomCases (extra : Formula Const Γ) :
    positions.ScopedIndexedCases bottom constructor
      (PredicateFixedPoint.intersection (positions.contextual bottom constructor).least
        (IndexedPredicateInduction.lift (inventory.rootProgram constructor)
          (ConstructorNonbottom.motive bottom inventory.index)))
      (ConstructorNonbottom.motive bottom inventory.index)
      [extra, ConstructorInjectivity.statement constructor, ConstructorNonbottom.separation constructor bottom] := by
  let signature := positions.contextual bottom constructor
  let scope : Subst Const Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
  intro Ξ images occurrence arguments
  let shifted := (inventory.subst scope).subst images
  let descendants := HOL.subst images signature.constructorChildren
  let tag := shifted.numeral occurrence.val
  let encoded := encode inventory.fields occurrence arguments
  let currentConstructor := HOL.subst images (HOL.subst scope constructor)
  let currentBottom := HOL.subst images (HOL.subst scope bottom)
  let value := shifted.constructorValue currentConstructor occurrence arguments descendants
  let index := applyFields _ (shifted.result occurrence) arguments
  let motive := ConstructorNonbottom.motive bottom inventory.index
  let predicate := PredicateFixedPoint.intersection signature.least
    (IndexedPredicateInduction.lift (inventory.rootProgram constructor) motive)
  let condition := signature.constructorScope.childPredicate
    (weaken (weaken (weaken predicate))) signature.constructorChildren
  let assumptions := [extra, ConstructorInjectivity.statement constructor,
    ConstructorNonbottom.separation constructor bottom]
  let hypotheses := applyArguments _ (shifted.allowed occurrence) arguments ::
    .app (HOL.subst images condition) encoded ::
    (signature.methodAssumptions (assumptions := assumptions) predicate).map (HOL.subst images)
  change ProofSyntax Const hypotheses
    (.app (.app (HOL.subst images (weaken (weaken (weaken motive)))) value) index)
  have motiveSame : HOL.subst images (weaken (weaken (weaken motive))) =
      ConstructorNonbottom.motive currentBottom inventory.index := by
    rw [scope_subst signature, ConstructorNonbottom.subst_motive]
    exact congrArg (fun term => ConstructorNonbottom.motive term inventory.index)
      (HOL.subst_comp images scope bottom).symm
  have separationSame : HOL.subst images
      (weaken (weaken (weaken (ConstructorNonbottom.separation constructor bottom)))) =
      ConstructorNonbottom.separation currentConstructor currentBottom := by
    rw [scope_subst signature, ConstructorNonbottom.subst_separation]
    simp only [currentConstructor, currentBottom, HOL.subst_comp]
    rfl
  let inherited : ProofSyntax Const hypotheses
      (HOL.subst images (weaken (weaken (weaken (ConstructorNonbottom.separation constructor bottom))))) :=
    .hyp ⟨6, by simp [hypotheses, RecursiveSpacePredicate.Contextual.methodAssumptions, assumptions, weakenHyps]⟩
  let available := ProofSyntax.castIndices rfl separationSame inherited
  apply ProofSyntax.castIndices rfl
    (congrArg (fun term => Term.app (Term.app term value) index) motiveSame.symm)
  exact .impE (.eqPropER (ConstructorNonbottom.motive_beta currentBottom value index))
    (ConstructorNonbottom.specialize currentConstructor currentBottom tag encoded descendants available)

theorem nonbottomCases_free (extra : Formula Const Γ) {Ξ : Ctx Base}
    (images : Subst Const (positions.contextual bottom constructor).constructorContext Ξ)
    occurrence arguments :
    (positions.nonbottomCases bottom constructor extra images occurrence arguments).FunctionExtensionalityFree := by
  unfold nonbottomCases
  dsimp only [id]
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨ConstructorNonbottom.motive_beta_free _ _ _, ?_⟩
  apply ConstructorNonbottom.specialize_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def nonbottomMember (value : Term Const Γ space) (index : Term Const Γ inventory.index) : Formula Const Γ :=
  .app (.app ((positions.contextual bottom constructor).memberProgram (inventory.rootProgram constructor)) value) index

def nonbottomProof (value : Term Const Γ space) (index : Term Const Γ inventory.index) :
    ProofSyntax Const [ConstructorInjectivity.statement constructor, ConstructorNonbottom.separation constructor bottom]
      (.imp (positions.nonbottomMember bottom constructor value index) (.not (.eq value bottom))) := by
  apply ProofSyntax.impI
  have derived := positions.induction_from_cases bottom constructor
    (ConstructorNonbottom.motive bottom inventory.index) (ProofSyntax.hyp ⟨1, by simp⟩)
    (positions.nonbottomCases bottom constructor (positions.nonbottomMember bottom constructor value index))
    value index (ProofSyntax.hyp ⟨0, by simp⟩)
  exact .impE (.eqPropEL (ConstructorNonbottom.motive_beta bottom value index)) derived

theorem nonbottomProof_free (value : Term Const Γ space) (index : Term Const Γ inventory.index) :
    (positions.nonbottomProof bottom constructor value index).FunctionExtensionalityFree := by
  unfold nonbottomProof
  refine ⟨ConstructorNonbottom.motive_beta_free _ _ _, ?_⟩
  apply induction_from_cases_free
  · trivial
  · exact nonbottomCases_free _ _ _ _
  · trivial

#print axioms nonbottomCases_free
#print axioms nonbottomProof
#print axioms nonbottomProof_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
