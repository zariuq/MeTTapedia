import Mettapedia.TypeTheory.ContextualPredicateScopeMorphism
import Mettapedia.TypeTheory.ContextualLogicalMorphismComposition

/-!
# Composition of local predicate and refinement preservation

Predicate fibre maps compose as actual Heyting homomorphisms. Ordinary
propositions, satisfying assumption contexts and complete refinement values
are preserved through both stages. Intermediate binder predicates and
inhabitants use the earned comprehension comparison, retaining their supplied
values. No whole-expression preservation law is a field of this construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.ContextualPredicateMorphism

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualPredicateModel
open ContextualComprehensionMorphism ContextualPredicateScopeMorphism
open ContextualStrictMorphismComposition
open ContextualProductComparison (selfExtend)

universe c s t m p q r
variable {C D E : CwfWithTerminal.{c,s,t,m}}
  {F : StrictCwfMorphism C D} {G : StrictCwfMorphism D E}
  {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
  {middle : PredicateDoctrine.{c,s,t,m,q} D.toCwf}
  {target : PredicateDoctrine.{c,s,t,m,r} E.toCwf}

theorem mappedPredicate_heq (preserved : DoctrinePreservation G middle target)
    {Γ Δ : D.toCwf.Ctx} (contexts : Γ = Δ)
    {first : middle.Predicate Γ} {second : middle.Predicate Δ} (values : HEq first second) :
    HEq (preserved.hom Γ first) (preserved.hom Δ second) := by
  cases contexts
  cases eq_of_heq values
  rfl

def DoctrinePreservation.identity (doctrine : PredicateDoctrine.{c,s,t,m,p} C.toCwf) :
    DoctrinePreservation (StrictCwfMorphism.identity C) doctrine doctrine where
  hom Γ := HeytingHom.id (doctrine.Predicate Γ)
  natural _ _ := rfl
  all := by
    intro Γ A predicate body readings
    cases eq_of_heq readings
    rfl
  some := by
    intro Γ A predicate body readings
    cases eq_of_heq readings
    rfl

def DoctrinePreservation.comp (earlier : DoctrinePreservation F source middle)
    (later : DoctrinePreservation G middle target) :
    DoctrinePreservation (compose F G) source target where
  hom Γ := (later.hom (context F Γ)).comp (earlier.hom Γ)
  natural := by
    intro Γ Δ substitution predicate
    exact (congrArg (later.hom (context F Γ)) (earlier.natural substitution predicate)).trans
      (later.natural (F.toFamilyMorphism.base.map substitution) (earlier.hom Δ predicate))
  all := by
    intro Γ A predicate body readings
    let intermediate := imagePredicate earlier (context_ext F Γ A) predicate
    have firstRead := imagePredicate_heq earlier (context_ext F Γ A) predicate
    have finalRead := (mappedPredicate_heq later (context_ext F Γ A) firstRead).symm.trans readings
    exact (congrArg (later.hom (context F Γ)) (earlier.all A predicate intermediate firstRead)).trans
      (later.all (F.toFamilyMorphism.mapType A) intermediate body finalRead)
  some := by
    intro Γ A predicate body readings
    let intermediate := imagePredicate earlier (context_ext F Γ A) predicate
    have firstRead := imagePredicate_heq earlier (context_ext F Γ A) predicate
    have finalRead := (mappedPredicate_heq later (context_ext F Γ A) firstRead).symm.trans readings
    exact (congrArg (later.hom (context F Γ)) (earlier.some A predicate intermediate firstRead)).trans
      (later.some (F.toFamilyMorphism.mapType A) intermediate body finalRead)

theorem DoctrinePreservation.ext_hom
    {first second : DoctrinePreservation F source middle} (same : first.hom = second.hom) :
    first = second := by
  cases first
  cases second
  cases same
  rfl

theorem PropositionPreservation.identity (operations : PropositionOperations source) :
    PropositionPreservation (DoctrinePreservation.identity source) operations operations where
  formation _ := rfl
  quote _ := HEq.rfl

theorem PropositionPreservation.comp
    {earlier : DoctrinePreservation F source middle} {later : DoctrinePreservation G middle target}
    {sourceOperations : PropositionOperations source} {middleOperations : PropositionOperations middle}
    {targetOperations : PropositionOperations target}
    (first : PropositionPreservation earlier sourceOperations middleOperations)
    (second : PropositionPreservation later middleOperations targetOperations) :
    PropositionPreservation (earlier.comp later) sourceOperations targetOperations where
  formation Γ := (congrArg (fun type : D.toCwf.Ty (context F Γ) => G.toFamilyMorphism.mapType type)
    (first.formation Γ)).trans (second.formation (context F Γ))
  quote predicate := (mappedTerm_heq G rfl (heq_of_eq (first.formation _))
    (first.quote predicate)).trans (second.quote (earlier.hom _ predicate))

theorem AssumptionPreservation.identity (operations : AssumptionOperations source) :
    AssumptionPreservation (DoctrinePreservation.identity source) operations operations where
  assumed _ _ := rfl
  inclusion := by
    intro Γ predicate
    let arrow : (⟨operations.assumed Γ predicate⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ :=
      operations.inclusion predicate
    change arrow = (𝟙 (⟨operations.assumed Γ predicate⟩ : C.toCwf.base.Context)) ≫ arrow
    exact (Category.id_comp arrow).symm

theorem AssumptionPreservation.comp
    {earlier : DoctrinePreservation F source middle} {later : DoctrinePreservation G middle target}
    {sourceOperations : AssumptionOperations source} {middleOperations : AssumptionOperations middle}
    {targetOperations : AssumptionOperations target}
    (first : AssumptionPreservation earlier sourceOperations middleOperations)
    (second : AssumptionPreservation later middleOperations targetOperations) :
    AssumptionPreservation (earlier.comp later) sourceOperations targetOperations where
  assumed Γ predicate := (congrArg G.toFamilyMorphism.base.obj (first.assumed Γ predicate)).trans
    (second.assumed (context F Γ) (earlier.hom Γ predicate))
  inclusion := by
    intro Γ predicate
    change G.toFamilyMorphism.base.map
      (F.toFamilyMorphism.base.map (sourceOperations.inclusion predicate)) = _
    calc
      _ = G.toFamilyMorphism.base.map
          (eqToHom (first.assumed Γ predicate) ≫ middleOperations.inclusion (earlier.hom Γ predicate)) :=
        congrArg G.toFamilyMorphism.base.map (first.inclusion predicate)
      _ = G.toFamilyMorphism.base.map (eqToHom (first.assumed Γ predicate)) ≫
          G.toFamilyMorphism.base.map (middleOperations.inclusion (earlier.hom Γ predicate)) :=
        G.toFamilyMorphism.base.map_comp _ _
      _ = eqToHom (congrArg G.toFamilyMorphism.base.obj (first.assumed Γ predicate)) ≫
          (eqToHom (second.assumed (context F Γ) (earlier.hom Γ predicate)) ≫
            targetOperations.inclusion (later.hom (context F Γ) (earlier.hom Γ predicate))) := by
        rw [eqToHom_map, second.inclusion]
      _ = _ := by
        rw [← Category.assoc, eqToHom_trans]
        rfl

theorem RefinementPreservation.identity (operations : RefinementOperations source) :
    RefinementPreservation (DoctrinePreservation.identity source) operations operations where
  formation := by
    intro Γ A predicate body readings
    cases eq_of_heq readings
    rfl
  intro := by
    intro Γ A predicate body readings term guard transportedGuard
    cases eq_of_heq readings
    rfl
  forget := by
    intro Γ A predicate body readings term value terms
    cases eq_of_heq readings
    cases eq_of_heq terms
    rfl

theorem RefinementPreservation.comp
    {earlier : DoctrinePreservation F source middle} {later : DoctrinePreservation G middle target}
    {sourceOperations : RefinementOperations source} {middleOperations : RefinementOperations middle}
    {targetOperations : RefinementOperations target}
    (first : RefinementPreservation earlier sourceOperations middleOperations)
    (second : RefinementPreservation later middleOperations targetOperations) :
    RefinementPreservation (earlier.comp later) sourceOperations targetOperations where
  formation := by
    intro Γ A predicate body readings
    let intermediate := imagePredicate earlier (context_ext F Γ A) predicate
    have firstRead := imagePredicate_heq earlier (context_ext F Γ A) predicate
    have finalRead := (mappedPredicate_heq later (context_ext F Γ A) firstRead).symm.trans readings
    exact (congrArg (fun type : D.toCwf.Ty (context F Γ) => G.toFamilyMorphism.mapType type)
      (first.formation A predicate intermediate firstRead)).trans
        (second.formation (F.toFamilyMorphism.mapType A) intermediate body finalRead)
  intro := by
    intro Γ A predicate body readings term guard transportedGuard
    let intermediate := imagePredicate earlier (context_ext F Γ A) predicate
    have firstRead := imagePredicate_heq earlier (context_ext F Γ A) predicate
    have finalRead := (mappedPredicate_heq later (context_ext F Γ A) firstRead).symm.trans readings
    have guardRead := substituted_predicate_heq earlier rfl (context_ext F Γ A) firstRead
      (self_extension_heq F rfl HEq.rfl term (F.toFamilyMorphism.mapTerm term) HEq.rfl)
    rw [guard, map_top] at guardRead
    have intermediateGuard : middle.reindex (selfExtend D.toCwf (F.toFamilyMorphism.mapTerm term))
        intermediate = ⊤ := (eq_of_heq guardRead).symm
    have formation := first.formation A predicate intermediate firstRead
    have introduction := first.intro A predicate intermediate firstRead term guard intermediateGuard
    exact (mappedTerm_heq G rfl (heq_of_eq formation) introduction).trans
      (second.intro (F.toFamilyMorphism.mapType A) intermediate body finalRead
        (F.toFamilyMorphism.mapTerm term) intermediateGuard transportedGuard)
  forget := by
    intro Γ A predicate body readings term value terms
    let intermediate := imagePredicate earlier (context_ext F Γ A) predicate
    have firstRead := imagePredicate_heq earlier (context_ext F Γ A) predicate
    have finalRead := (mappedPredicate_heq later (context_ext F Γ A) firstRead).symm.trans readings
    have formation := first.formation A predicate intermediate firstRead
    let intermediateTerm := imageAtType F rfl
      (middleOperations.refined (F.toFamilyMorphism.mapType A) intermediate) (heq_of_eq formation) term
    have firstTerms := imageAtType_heq F rfl
      (middleOperations.refined (F.toFamilyMorphism.mapType A) intermediate) (heq_of_eq formation) term
    have finalTerms := (mappedTerm_heq G rfl (heq_of_eq formation) firstTerms).symm.trans terms
    have forgetting := first.forget A predicate intermediate firstRead term intermediateTerm firstTerms
    exact (mappedTerm_heq G rfl HEq.rfl forgetting).trans
      (second.forget (F.toFamilyMorphism.mapType A) intermediate body finalRead
        intermediateTerm value finalTerms)

def PredicateLogicalPreservation.identity (model : LocalModel.{c,s,t,m,p} C) :
    PredicateLogicalPreservation (StrictCwfMorphism.identity C) model model where
  doctrine := DoctrinePreservation.identity model.doctrine
  propositions := PropositionPreservation.identity model.propositions
  assumptions := AssumptionPreservation.identity model.assumptions
  refinements := RefinementPreservation.identity model.refinements

def PredicateLogicalPreservation.comp
    {sourceModel : LocalModel.{c,s,t,m,p} C} {middleModel : LocalModel.{c,s,t,m,q} D}
    {targetModel : LocalModel.{c,s,t,m,r} E}
    (first : PredicateLogicalPreservation F sourceModel middleModel)
    (second : PredicateLogicalPreservation G middleModel targetModel) :
    PredicateLogicalPreservation (compose F G) sourceModel targetModel where
  doctrine := first.doctrine.comp second.doctrine
  propositions := first.propositions.comp second.propositions
  assumptions := first.assumptions.comp second.assumptions
  refinements := first.refinements.comp second.refinements

theorem PropositionPreservation.proof_unique
    {preserved : DoctrinePreservation F source middle}
    {sourceOperations : PropositionOperations source} {targetOperations : PropositionOperations middle}
    (first second : PropositionPreservation preserved sourceOperations targetOperations) :
    first = second := by
  cases first
  cases second
  rfl

theorem AssumptionPreservation.proof_unique
    {preserved : DoctrinePreservation F source middle}
    {sourceOperations : AssumptionOperations source} {targetOperations : AssumptionOperations middle}
    (first second : AssumptionPreservation preserved sourceOperations targetOperations) :
    first = second := by
  cases first
  cases second
  rfl

theorem RefinementPreservation.proof_unique
    {preserved : DoctrinePreservation F source middle}
    {sourceOperations : RefinementOperations source} {targetOperations : RefinementOperations middle}
    (first second : RefinementPreservation preserved sourceOperations targetOperations) :
    first = second := by
  cases first
  cases second
  rfl

/-- The predicate homomorphisms are data; only the local preservation
certificates are proof irrelevant. -/
theorem PredicateLogicalPreservation.ext_hom
    {sourceModel : LocalModel.{c,s,t,m,p} C} {targetModel : LocalModel.{c,s,t,m,q} D}
    {first second : PredicateLogicalPreservation F sourceModel targetModel}
    (same : first.doctrine.hom = second.doctrine.hom) : first = second := by
  cases first with
  | mk firstDoctrine firstPropositions firstAssumptions firstRefinements =>
    cases second with
    | mk secondDoctrine secondPropositions secondAssumptions secondRefinements =>
      have doctrines : firstDoctrine = secondDoctrine := DoctrinePreservation.ext_hom same
      cases doctrines
      cases PropositionPreservation.proof_unique firstPropositions secondPropositions
      cases AssumptionPreservation.proof_unique firstAssumptions secondAssumptions
      cases RefinementPreservation.proof_unique firstRefinements secondRefinements
      rfl

end Mettapedia.TypeTheory.ContextualPredicateMorphism

namespace Mettapedia.TypeTheory.ContextualPredicateScopeMorphism

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualPredicateModelScopes
open ContextualComprehensionMorphism ContextualStrictMorphismComposition

universe c s t m p q r
variable {C D E : CwfWithTerminal.{c,s,t,m}}
  {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
  {middle : PredicateDoctrine.{c,s,t,m,q} D.toCwf}
  {target : PredicateDoctrine.{c,s,t,m,r} E.toCwf}
  {sourceAssumptions : AssumptionOperations source}
  {middleAssumptions : AssumptionOperations middle}
  {targetAssumptions : AssumptionOperations target}

theorem ScopeImage.identity {n : Nat} (Γ : Scope C source sourceAssumptions n) :
    ScopeImage (StrictCwfMorphism.identity C) Γ Γ :=
  ⟨rfl, fun index => valueImage_identity (Γ.2.lookup index)⟩

theorem ScopeImage.comp (F : StrictCwfMorphism C D) (G : StrictCwfMorphism D E)
    {n : Nat} {Γ : Scope C source sourceAssumptions n}
    {Δ : Scope D middle middleAssumptions n} {Θ : Scope E target targetAssumptions n}
    (earlier : ScopeImage F Γ Δ) (later : ScopeImage G Δ Θ) :
    ScopeImage (compose F G) Γ Θ :=
  ⟨(congrArg (context G) earlier.contexts).trans later.contexts,
    fun index => valueImage_comp F G earlier.contexts
      (earlier.variableReadouts index) (later.variableReadouts index)⟩

end Mettapedia.TypeTheory.ContextualPredicateScopeMorphism
