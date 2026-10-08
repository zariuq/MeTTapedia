import Mettapedia.TypeTheory.ContextualLogicalMorphism

/-!
# Dependent-product context components are determined by evaluation

The generic function and its generic argument give an actual evaluation
substitution into the codomain's display context. Product eta and local
substitution make these readings determine the function-context component.
The comparisons retain the supplied strict contextual and product action.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualProductCellUniqueness

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations ContextualPiEta ContextualComprehensionMorphism
open ContextualLogicalMorphism

universe u v w w'

variable {C : Cwf.{u,v,w,w'}}

/-- Product eta detects complete functions from their generic applications. -/
theorem genericSection_injective (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products) (eta : PiEta products formed)
    {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)} :
    Function.Injective (genericSection products formed (A := A) (B := B)) := by
  intro first second readings
  exact (eta first).symm.trans ((congrArg products.lam readings).trans (eta second))

/-- The selected product variable, retyped only by actual product formation. -/
def genericFunction (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products)
    {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Tm (C.ext Γ (products.pi A B))
      (products.pi (C.tySub A (C.wk (products.pi A B)))
        (C.tySub B (TypeOver.extensionSubstitution (C.wk (products.pi A B)) A))) :=
  cast (congrArg (C.Tm (C.ext Γ (products.pi A B)))
    (formed (C.wk (products.pi A B)) A B)) (C.vz (products.pi A B))

theorem genericFunction_heq (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products)
    {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    HEq (genericFunction products formed A B) (C.vz (products.pi A B)) := cast_heq _ _

/-- Supply the actual newest argument of the generic function. -/
def evaluation (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products)
    {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Sub (C.ext (C.ext Γ (products.pi A B))
      (C.tySub A (C.wk (products.pi A B)))) (C.ext (C.ext Γ A) B) :=
  C.pair (TypeOver.extensionSubstitution (C.wk (products.pi A B)) A) B
    (genericSection products formed (genericFunction products formed A B))

theorem evaluation_projection (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products)
    {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.compS (C.wk B) (evaluation products formed A B) =
      TypeOver.extensionSubstitution (C.wk (products.pi A B)) A := C.wk_pair _ _ _

theorem evaluation_variable (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products)
    {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    HEq (C.tmSub (C.vz B) (evaluation products formed A B))
      (genericSection products formed (genericFunction products formed A B)) :=
  (heq_of_eq (C.vz_pair _ _ _)).trans (cast_heq _ _)

theorem lambda_heq (products : PiOperations C)
    {Γ Δ : C.Ctx} (contexts : Γ = Δ)
    {A : C.Ty Γ} {A' : C.Ty Δ} (domains : HEq A A')
    {B : C.Ty (C.ext Γ A)} {B' : C.Ty (C.ext Δ A')} (codomains : HEq B B')
    {body : C.Tm (C.ext Γ A) B} {body' : C.Tm (C.ext Δ A') B'}
    (terms : HEq body body') : HEq (products.lam body) (products.lam body') := by
  cases contexts
  cases eq_of_heq domains
  cases eq_of_heq codomains
  cases eq_of_heq terms
  rfl

/-- Retype only the source of the actual cartesian lift, when its domain
annotation is unchanged by the supplied endomorphism. -/
def endoLift {Γ : C.Ctx} (σ : C.Sub Γ Γ) (A : C.Ty Γ)
    (invariant : C.tySub A σ = A) : C.Sub (C.ext Γ A) (C.ext Γ A) :=
  cast (congrArg (fun Ω => C.Sub Ω (C.ext Γ A)) (congrArg (C.ext Γ) invariant))
    (TypeOver.extensionSubstitution σ A)

theorem endoLift_heq {Γ : C.Ctx} (σ : C.Sub Γ Γ) (A : C.Ty Γ)
    (invariant : C.tySub A σ = A) :
    HEq (endoLift σ A invariant) (TypeOver.extensionSubstitution σ A) :=
  cast_heq _ _

theorem endoLift_projection {Γ : C.Ctx} (σ : C.Sub Γ Γ) (A : C.Ty Γ)
    (invariant : C.tySub A σ = A) :
    C.compS (C.wk A) (endoLift σ A invariant) = C.compS σ (C.wk A) := by
  have sources := congrArg (C.ext Γ) invariant
  have computed := heq_of_eq (TypeOver.wk_extensionSubstitution σ A)
  have mapped : HEq (C.compS (C.wk A) (endoLift σ A invariant))
      (C.compS (C.wk A) (TypeOver.extensionSubstitution σ A)) :=
    comp_heq sources.symm rfl rfl HEq.rfl (endoLift_heq σ A invariant)
  have target : HEq (C.compS σ (C.wk (C.tySub A σ))) (C.compS σ (C.wk A)) :=
    comp_heq sources rfl rfl HEq.rfl (wk_heq rfl (heq_of_eq invariant))
  exact eq_of_heq (mapped.trans (computed.trans target))

theorem endoLift_variable {Γ : C.Ctx} (σ : C.Sub Γ Γ) (A : C.Ty Γ)
    (invariant : C.tySub A σ = A) :
    HEq (C.tmSub (C.vz A) (endoLift σ A invariant)) (C.vz A) := by
  have sources := congrArg (C.ext Γ) invariant
  exact (tmSub_heq sources.symm rfl HEq.rfl HEq.rfl (endoLift_heq σ A invariant)).trans
    ((TypeOver.vz_extensionSubstitution σ A).trans (vz_heq rfl (heq_of_eq invariant)))

/-- The complete generic section fixes its abstraction once the actual
lift, domain and codomain have their earned invariant readings. -/
theorem abstraction_fixed (products : PiOperations C)
    (stable : StrictPiSubstitution products) (eta : PiEta products stable.1)
    {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (function : C.Tm Γ (products.pi A B)) (σ : C.Sub Γ Γ)
    (lift : C.Sub (C.ext Γ A) (C.ext Γ A))
    (domains : C.tySub A σ = A)
    (lifts : HEq (TypeOver.extensionSubstitution σ A) lift)
    (codomains : C.tySub B lift = B)
    (readings : HEq (C.tmSub (genericSection products stable.1 function) lift)
      (genericSection products stable.1 function)) :
    HEq (C.tmSub function σ) function := by
  let body := genericSection products stable.1 function
  have extensions := congrArg (C.ext Γ) domains
  have bodyTypes := (tySub_heq extensions rfl HEq.rfl lifts).trans (heq_of_eq codomains)
  have bodies := (tmSub_heq extensions rfl HEq.rfl HEq.rfl lifts).trans readings
  have lambdas := lambda_heq products rfl (heq_of_eq domains) bodyTypes bodies
  exact (heq_of_eq (congrArg (fun f => C.tmSub f σ) (eta function).symm)).trans
    ((stable.2.1 σ body).trans (lambdas.trans (heq_of_eq (eta function))))

/-- The two projections and the full generic evaluation detect every
endomorphism of a product display context. The argument-context component
is supplied only with its actual naturality readings, never as an identity. -/
theorem evaluation_joint_cancel (products : PiOperations C)
    (stable : StrictPiSubstitution products) (eta : PiEta products stable.1)
    {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (component : C.Sub (C.ext Γ (products.pi A B)) (C.ext Γ (products.pi A B)))
    (argumentComponent : C.Sub
      (C.ext (C.ext Γ (products.pi A B)) (C.tySub A (C.wk (products.pi A B))))
      (C.ext (C.ext Γ (products.pi A B)) (C.tySub A (C.wk (products.pi A B)))))
    (base : C.compS (C.wk (products.pi A B)) component = C.wk (products.pi A B))
    (argumentBase : C.compS (C.wk (C.tySub A (C.wk (products.pi A B)))) argumentComponent =
      C.compS component (C.wk (C.tySub A (C.wk (products.pi A B)))))
    (argument : C.compS (TypeOver.extensionSubstitution (C.wk (products.pi A B)) A)
      argumentComponent = TypeOver.extensionSubstitution (C.wk (products.pi A B)) A)
    (evaluated : C.compS (evaluation products stable.1 A B) argumentComponent =
      evaluation products stable.1 A B) :
    component = C.idS _ := by
  let P := products.pi A B
  let Aw := C.tySub A (C.wk P)
  let lifted := TypeOver.extensionSubstitution (C.wk P) A
  let Bw := C.tySub B lifted
  have domains : C.tySub Aw component = Aw := by
    dsimp only [Aw]
    rw [← C.tySub_comp, base]
  have codomains : C.tySub Bw argumentComponent = Bw := by
    dsimp only [Bw]
    rw [← C.tySub_comp, argument]
  have variableTypes : C.tySub (C.tySub A (C.wk A)) lifted = C.tySub Aw (C.wk Aw) := by
    dsimp only [lifted, Aw]
    rw [← C.tySub_comp, TypeOver.wk_extensionSubstitution, C.tySub_comp]
  have argumentReading : HEq (C.tmSub (C.vz Aw) argumentComponent) (C.vz Aw) := by
    have unchanged : HEq (C.tmSub (C.vz A) (C.compS lifted argumentComponent))
        (C.tmSub (C.vz A) lifted) := by rw [argument]
    exact (TypeOver.tmSub_heq variableTypes
      (TypeOver.vz_extensionSubstitution (C.wk P) A) argumentComponent).symm.trans
      ((TypeOver.tmSub_comp_heq (C.vz A) lifted argumentComponent).symm.trans
        (unchanged.trans (TypeOver.vz_extensionSubstitution (C.wk P) A)))
  have actualLift : argumentComponent = endoLift component Aw domains := by
    apply TypeOver.substitution_ext
    · exact argumentBase.trans (endoLift_projection component Aw domains).symm
    · exact argumentReading.trans (endoLift_variable component Aw domains).symm
  have lifts : HEq (TypeOver.extensionSubstitution component Aw) argumentComponent :=
    (endoLift_heq component Aw domains).symm.trans (heq_of_eq actualLift).symm
  have readings : HEq
      (C.tmSub (genericSection products stable.1 (genericFunction products stable.1 A B))
        argumentComponent)
      (genericSection products stable.1 (genericFunction products stable.1 A B)) := by
    have unchanged : HEq (C.tmSub (C.vz B)
        (C.compS (evaluation products stable.1 A B) argumentComponent))
        (C.tmSub (C.vz B) (evaluation products stable.1 A B)) := by rw [evaluated]
    have types : C.tySub (C.tySub B (C.wk B)) (evaluation products stable.1 A B) = Bw := by
      rw [← C.tySub_comp, evaluation_projection]
    exact (TypeOver.tmSub_heq types (evaluation_variable products stable.1 A B)
      argumentComponent).symm.trans
      ((TypeOver.tmSub_comp_heq (C.vz B) _ _).symm.trans
        (unchanged.trans (evaluation_variable products stable.1 A B)))
  have fixed := abstraction_fixed products stable eta
    (genericFunction products stable.1 A B) component argumentComponent domains lifts codomains readings
  have functionTypes := stable.1 (C.wk P) A B
  have functionReading : HEq (C.tmSub (C.vz P) component) (C.vz P) :=
    (TypeOver.tmSub_heq functionTypes
      (genericFunction_heq products stable.1 A B).symm component).trans
      (fixed.trans (genericFunction_heq products stable.1 A B))
  apply TypeOver.substitution_ext
  · exact base.trans (C.comp_id (C.wk P)).symm
  · exact functionReading.trans
      ((heq_of_eq (C.tmSub_id (C.vz P))).trans (cast_heq _ _)).symm

variable {S T : CwfWithTerminal.{u,v,w,w'}}

/-- Complete generic application is preserved by the local product and
comprehension capabilities, without an all-syntax preservation premise. -/
theorem genericSection_preserved (F : StrictCwfMorphism S T)
    (source : PiOperations S.toCwf) (target : PiOperations T.toCwf)
    (sourceFormed : StrictPiFormationSubstitution source)
    (targetFormed : StrictPiFormationSubstitution target)
    (preserves : PiPreservation F source target)
    {Γ : S.toCwf.Ctx} {Γ' : T.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : S.toCwf.Ty Γ} {A' : T.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : S.toCwf.Ty (S.toCwf.ext Γ A)} {B' : T.toCwf.Ty (T.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B')
    (function : S.toCwf.Tm Γ (source.pi A B))
    (function' : T.toCwf.Tm Γ' (target.pi A' B'))
    (functions : HEq (F.toFamilyMorphism.mapTerm function) function') :
    HEq (F.toFamilyMorphism.mapTerm (genericSection source sourceFormed function))
      (genericSection target targetFormed function') := by
  have extensions := extension_images F contexts domains
  have weakenings := (projection_heq F Γ A).trans (wk_heq contexts domains)
  have products := preserves.formation contexts domains codomains
  have domainAt := substituted_type_heq F extensions contexts domains weakenings
  have lifts := lifted_substitution_heq F extensions contexts domains
    (S.toCwf.wk A) (T.toCwf.wk A') weakenings
  have codomainAt := substituted_type_heq F
    (extension_images F extensions domainAt) extensions codomains lifts
  have weakenedFunction :=
    (F.mapTerm_heq (sourceFormed (S.toCwf.wk A) A B).symm
      (reindexFunction_heq source sourceFormed (S.toCwf.wk A) function)).trans
      ((substituted_term_heq F extensions contexts products functions weakenings).trans
        (reindexFunction_heq target targetFormed (T.toCwf.wk A') function').symm)
  have newest := (variable_heq F Γ A).trans (vz_heq contexts domains)
  have applications := preserves.application extensions domainAt codomainAt
    (reindexFunction source sourceFormed (S.toCwf.wk A) function)
    (reindexFunction target targetFormed (T.toCwf.wk A') function')
    (S.toCwf.vz A) (T.toCwf.vz A') weakenedFunction newest
  exact (F.mapTerm_heq (generic_result_type A B).symm
    (genericSection_heq source sourceFormed function)).trans
      (applications.trans (genericSection_heq target targetFormed function').symm)

/-- The full evaluator map is preserved using its actual generic section,
the local application operation, and the earned contextual pairing action. -/
theorem evaluation_preserved (F : StrictCwfMorphism S T)
    (source : PiOperations S.toCwf) (target : PiOperations T.toCwf)
    (sourceFormed : StrictPiFormationSubstitution source)
    (targetFormed : StrictPiFormationSubstitution target)
    (preserves : PiPreservation F source target)
    {Γ : S.toCwf.Ctx} {Γ' : T.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : S.toCwf.Ty Γ} {A' : T.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : S.toCwf.Ty (S.toCwf.ext Γ A)} {B' : T.toCwf.Ty (T.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B') :
    HEq (F.toFamilyMorphism.base.map (evaluation source sourceFormed A B))
      (evaluation target targetFormed A' B') := by
  have products := preserves.formation contexts domains codomains
  have productContexts := extension_images F contexts products
  have weakenings := (projection_heq F Γ (source.pi A B)).trans (wk_heq contexts products)
  have argumentTypes := substituted_type_heq F productContexts contexts domains weakenings
  have lifts := lifted_substitution_heq F productContexts contexts domains
    (S.toCwf.wk (source.pi A B)) (T.toCwf.wk (target.pi A' B')) weakenings
  have bodyTypes := substituted_type_heq F
    (extension_images F productContexts argumentTypes) (extension_images F contexts domains)
    codomains lifts
  have functions :=
    (F.mapTerm_heq (sourceFormed (S.toCwf.wk (source.pi A B)) A B).symm
      (genericFunction_heq source sourceFormed A B)).trans
      ((variable_heq F Γ (source.pi A B)).trans
        ((vz_heq contexts products).trans (genericFunction_heq target targetFormed A' B').symm))
  have sections := genericSection_preserved F source target sourceFormed targetFormed preserves
    productContexts argumentTypes bodyTypes (genericFunction source sourceFormed A B)
    (genericFunction target targetFormed A' B') functions
  exact pairing_images_heq F (extension_images F productContexts argumentTypes)
    (extension_images F contexts domains) codomains _ _ lifts _ _ sections

/-- Retain the exact equal image presentation of one context component. -/
def contextComponent (F : StrictCwfMorphism S T)
    (cell : F.toFamilyMorphism.base ⟶ F.toFamilyMorphism.base)
    {Γ : S.toCwf.Ctx} {Γ' : T.toCwf.Ctx} (same : context F Γ = Γ') :
    T.toCwf.Sub Γ' Γ' :=
  let objects : F.toFamilyMorphism.base.obj ⟨Γ⟩ =
      (⟨Γ'⟩ : T.toCwf.base.Context) := ContextualBase.Context.ext same
  eqToHom objects.symm ≫ cell.app ⟨Γ⟩ ≫ eqToHom objects

theorem transported_identity_iff {B : Type u} [Category.{v} B]
    {Γ Δ : B} (same : Γ = Δ) (component : Γ ⟶ Γ) :
    eqToHom same.symm ≫ component ≫ eqToHom same = 𝟙 Δ ↔ component = 𝟙 Γ := by
  cases same
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem contextComponent_fixed (F : StrictCwfMorphism S T)
    (cell : F.toFamilyMorphism.base ⟶ F.toFamilyMorphism.base)
    {Γ : S.toCwf.Ctx} {Γ' : T.toCwf.Ctx} (same : context F Γ = Γ') :
    contextComponent F cell same = T.toCwf.idS Γ' ↔
      cell.app ⟨Γ⟩ = 𝟙 (F.toFamilyMorphism.base.obj ⟨Γ⟩) := by
  let objects : F.toFamilyMorphism.base.obj ⟨Γ⟩ =
      (⟨Γ'⟩ : T.toCwf.base.Context) := ContextualBase.Context.ext same
  exact transported_identity_iff objects (cell.app ⟨Γ⟩)

theorem transported_naturality {B E : Type u} [Category.{v} B] [Category.{v} E]
    (F : B ⥤ E) (cell : F ⟶ F) {Γ Δ : B} {Γ' Δ' : E}
    (sources : F.obj Γ = Γ') (targets : F.obj Δ = Δ')
    (σ : Γ ⟶ Δ) (σ' : Γ' ⟶ Δ')
    (diagram : F.map σ ≫ eqToHom targets = eqToHom sources ≫ σ') :
    (eqToHom sources.symm ≫ cell.app Γ ≫ eqToHom sources) ≫ σ' =
      σ' ≫ (eqToHom targets.symm ≫ cell.app Δ ≫ eqToHom targets) := by
  cases sources
  cases targets
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at diagram ⊢
  rw [← diagram]
  exact (cell.naturality σ).symm

/-- Naturality survives the actual equal image presentations at both
endpoints; the mapped arrow is independently supplied and compared. -/
theorem contextComponent_naturality (F : StrictCwfMorphism S T)
    (cell : F.toFamilyMorphism.base ⟶ F.toFamilyMorphism.base)
    {Γ Δ : S.toCwf.Ctx} {Γ' Δ' : T.toCwf.Ctx}
    (sources : context F Γ = Γ') (targets : context F Δ = Δ')
    (σ : S.toCwf.Sub Γ Δ) (σ' : T.toCwf.Sub Γ' Δ')
    (arrows : HEq (F.toFamilyMorphism.base.map σ) σ') :
    T.toCwf.compS σ' (contextComponent F cell sources) =
      T.toCwf.compS (contextComponent F cell targets) σ' := by
  let sourceObjects : F.toFamilyMorphism.base.obj ⟨Γ⟩ =
      (⟨Γ'⟩ : T.toCwf.base.Context) := ContextualBase.Context.ext sources
  let targetObjects : F.toFamilyMorphism.base.obj ⟨Δ⟩ =
      (⟨Δ'⟩ : T.toCwf.base.Context) := ContextualBase.Context.ext targets
  have diagram := diagram_of_heq sourceObjects targetObjects
    (F.toFamilyMorphism.base.map σ) σ' arrows
  exact transported_naturality F.toFamilyMorphism.base cell sourceObjects targetObjects σ σ' diagram

/-- Fixed base, domain and codomain display contexts force the dependent
product display context to be fixed. Naturality supplies the complete
argument and evaluator equations used by product eta. -/
theorem product_fixed_at_images (F : StrictCwfMorphism S T)
    (cell : F.toFamilyMorphism.base ⟶ F.toFamilyMorphism.base)
    (source : PiOperations S.toCwf) (target : PiOperations T.toCwf)
    (sourceFormed : StrictPiFormationSubstitution source)
    (targetStable : StrictPiSubstitution target) (targetEta : PiEta target targetStable.1)
    (preserves : PiPreservation F source target)
    {Γ : S.toCwf.Ctx} {Γ' : T.toCwf.Ctx} (contexts : context F Γ = Γ')
    (A : S.toCwf.Ty Γ) (A' : T.toCwf.Ty Γ')
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    (B : S.toCwf.Ty (S.toCwf.ext Γ A)) (B' : T.toCwf.Ty (T.toCwf.ext Γ' A'))
    (codomains : HEq (F.toFamilyMorphism.mapType B) B')
    (baseFixed : cell.app ⟨Γ⟩ = 𝟙 (F.toFamilyMorphism.base.obj ⟨Γ⟩))
    (domainFixed : cell.app ⟨S.toCwf.ext Γ A⟩ =
      𝟙 (F.toFamilyMorphism.base.obj ⟨S.toCwf.ext Γ A⟩))
    (codomainFixed : cell.app ⟨S.toCwf.ext (S.toCwf.ext Γ A) B⟩ =
      𝟙 (F.toFamilyMorphism.base.obj ⟨S.toCwf.ext (S.toCwf.ext Γ A) B⟩)) :
    cell.app ⟨S.toCwf.ext Γ (source.pi A B)⟩ =
      𝟙 (F.toFamilyMorphism.base.obj ⟨S.toCwf.ext Γ (source.pi A B)⟩) := by
  have products := preserves.formation contexts domains codomains
  have productContexts := extension_images F contexts products
  have domainContexts := extension_images F contexts domains
  have codomainContexts := extension_images F domainContexts codomains
  have productProjections :=
    (projection_heq F Γ (source.pi A B)).trans (wk_heq contexts products)
  have argumentTypes := substituted_type_heq F productContexts contexts domains productProjections
  have argumentContexts := extension_images F productContexts argumentTypes
  have argumentProjections :=
    (projection_heq F _ (S.toCwf.tySub A (S.toCwf.wk (source.pi A B)))).trans
      (wk_heq productContexts argumentTypes)
  have lifts := lifted_substitution_heq F productContexts contexts domains
    (S.toCwf.wk (source.pi A B)) (T.toCwf.wk (target.pi A' B')) productProjections
  let component := contextComponent F cell productContexts
  let argumentComponent := contextComponent F cell argumentContexts
  have fixedBase := (contextComponent_fixed F cell contexts).mpr baseFixed
  have fixedDomain := (contextComponent_fixed F cell domainContexts).mpr domainFixed
  have fixedCodomain := (contextComponent_fixed F cell codomainContexts).mpr codomainFixed
  have base : T.toCwf.compS (T.toCwf.wk (target.pi A' B')) component =
      T.toCwf.wk (target.pi A' B') := by
    have natural := contextComponent_naturality F cell productContexts contexts
      (S.toCwf.wk (source.pi A B)) (T.toCwf.wk (target.pi A' B')) productProjections
    rw [fixedBase, T.toCwf.id_comp] at natural
    exact natural
  have argumentBase :
      T.toCwf.compS (T.toCwf.wk (T.toCwf.tySub A' (T.toCwf.wk (target.pi A' B'))))
        argumentComponent =
      T.toCwf.compS component
        (T.toCwf.wk (T.toCwf.tySub A' (T.toCwf.wk (target.pi A' B')))) :=
    contextComponent_naturality F cell argumentContexts productContexts _ _ argumentProjections
  have argument :
      T.toCwf.compS (TypeOver.extensionSubstitution (T.toCwf.wk (target.pi A' B')) A')
        argumentComponent = TypeOver.extensionSubstitution (T.toCwf.wk (target.pi A' B')) A' := by
    have natural := contextComponent_naturality F cell argumentContexts domainContexts
      (TypeOver.extensionSubstitution (S.toCwf.wk (source.pi A B)) A)
      (TypeOver.extensionSubstitution (T.toCwf.wk (target.pi A' B')) A') lifts
    rw [fixedDomain, T.toCwf.id_comp] at natural
    exact natural
  have evaluated :
      T.toCwf.compS (evaluation target targetStable.1 A' B') argumentComponent =
        evaluation target targetStable.1 A' B' := by
    have evaluators := evaluation_preserved F source target sourceFormed targetStable.1
      preserves contexts domains codomains
    have natural := contextComponent_naturality F cell argumentContexts codomainContexts
      (evaluation source sourceFormed A B) (evaluation target targetStable.1 A' B') evaluators
    rw [fixedCodomain, T.toCwf.id_comp] at natural
    exact natural
  exact (contextComponent_fixed F cell productContexts).mp
    (evaluation_joint_cancel target targetStable targetEta A' B' component argumentComponent
      base argumentBase argument evaluated)

/-- The canonical image presentations discharge all image qualifications
in the dependent-product identity propagation theorem. -/
theorem product_fixed (F : StrictCwfMorphism S T)
    (cell : F.toFamilyMorphism.base ⟶ F.toFamilyMorphism.base)
    (source : PiOperations S.toCwf) (target : PiOperations T.toCwf)
    (sourceFormed : StrictPiFormationSubstitution source)
    (targetStable : StrictPiSubstitution target) (targetEta : PiEta target targetStable.1)
    (preserves : PiPreservation F source target)
    {Γ : S.toCwf.Ctx} (A : S.toCwf.Ty Γ) (B : S.toCwf.Ty (S.toCwf.ext Γ A))
    (baseFixed : cell.app ⟨Γ⟩ = 𝟙 (F.toFamilyMorphism.base.obj ⟨Γ⟩))
    (domainFixed : cell.app ⟨S.toCwf.ext Γ A⟩ =
      𝟙 (F.toFamilyMorphism.base.obj ⟨S.toCwf.ext Γ A⟩))
    (codomainFixed : cell.app ⟨S.toCwf.ext (S.toCwf.ext Γ A) B⟩ =
      𝟙 (F.toFamilyMorphism.base.obj ⟨S.toCwf.ext (S.toCwf.ext Γ A) B⟩)) :
    cell.app ⟨S.toCwf.ext Γ (source.pi A B)⟩ =
      𝟙 (F.toFamilyMorphism.base.obj ⟨S.toCwf.ext Γ (source.pi A B)⟩) := by
  let B' : T.toCwf.Ty (T.toCwf.ext (context F Γ) (F.toFamilyMorphism.mapType A)) :=
    cast (congrArg T.toCwf.Ty (context_ext F Γ A)) (F.toFamilyMorphism.mapType B)
  have codomains : HEq (F.toFamilyMorphism.mapType B) B' := (cast_heq _ _).symm
  exact product_fixed_at_images F cell source target sourceFormed targetStable targetEta
    preserves rfl A (F.toFamilyMorphism.mapType A) HEq.rfl B B' codomains
    baseFixed domainFixed codomainFixed

end Mettapedia.TypeTheory.ContextualProductCellUniqueness
