import Mettapedia.TypeTheory.MaterialSets.Hypersets.DependentProduct
import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.TypeTheory.ContextualProductComparison
import Mettapedia.TypeTheory.ContextualSumComparison
import Mettapedia.GSLT.Core.ContextualTypeReindexing
import Mettapedia.TypeTheory.ContextualTypeOperations

/-!
# Material hyperset contexts and dependent families

Contexts are actual hypersets, substitutions are functions on their member
types, dependent types are hyperset-valued families, and terms are dependent
sections of membership.  Context extension is the material set of ordered
pairs.  Its proved decoding into dependent pairs supplies comprehension and
its laws.
Pointwise material sums and function-graph products supply the common Pi/Sigma
interfaces, with beta, eta and semantic substitution laws.  Explicit family
equality casts retain the actual member values.

The construction takes an explicit presentation for dependent replacement.
Its identity laws are ordinary Lean identity in this extensional semantic
model.  They do not assert higher identity rules for a native language or
select a set-theory axiom package.  All carriers stay at `Type (u + 1)`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyCwf

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u uIndex uValue

private theorem dependentFunction_heq {I : Sort uIndex} {F G : I → Sort uValue}
    {s : (i : I) → F i} {t : (i : I) → G i} (same : ∀ i, HEq (s i) (t i)) : HEq s t := by
  have codomainEq : F = G := funext fun i => type_eq_of_heq (same i)
  cases codomainEq
  exact heq_of_eq (funext fun i => eq_of_heq (same i))

/-- The actual members of a hyperset, with proposition-valued membership. -/
abbrev Elements (X : HSet.{u}) := El (fun x X : HSet.{u} => x ∈ X) X

abbrev Family (Γ : HSet.{u}) := Elements Γ → HSet.{u}
abbrev Section {Γ : HSet.{u}} (A : Family Γ) := (γ : Elements Γ) → Elements (A γ)
abbrev Substitution (Γ Δ : HSet.{u}) := Elements Γ → Elements Δ

/-- Material context comprehension uses the existing dependent-pair set. -/
def extension (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) : HSet.{u} :=
  sigmaSet (HSet.dependentReplacement p) HSet.union HSet.kuratowski Γ A

/-- The proved decoding of actual material comprehension members. -/
def extensionDecode (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Elements (extension p A) ≃ Σ' γ : Elements Γ, Elements (A γ) :=
  HSet.sigmaSetEquiv p Γ A

def projection (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Substitution (extension p A) Γ := fun γ => (extensionDecode p A γ).1

def lastVariable (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Section (fun γ => A (projection p A γ)) := fun γ => (extensionDecode p A γ).2

/-- Pairing constructs an actual Kuratowski pair as a material context member. -/
def pair (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) (t : Section (fun γ => A (σ γ))) :
    Substitution Γ (extension p A) :=
  fun γ => (extensionDecode p A).symm ⟨σ γ, t γ⟩

/-- The material value of a paired substitution is the actual ordered pair. -/
theorem pair_value (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) (t : Section (fun γ => A (σ γ)))
    (γ : Elements Γ) : (pair p σ A t γ).1 = HSet.kpair (σ γ).1 (t γ).1 := rfl

theorem projection_pair (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) (t : Section (fun γ => A (σ γ))) :
    projection p A ∘ pair p σ A t = σ := by
  funext γ
  exact congrArg PSigma.fst ((extensionDecode p A).apply_symm_apply ⟨σ γ, t γ⟩)

/-- The last variable of a paired context retains the supplied dependent
value, across the equality of its indexed fibre. -/
theorem variable_pair_heq (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) (t : Section (fun γ => A (σ γ))) :
    HEq (fun γ => lastVariable p A (pair p σ A t γ)) t := by
  apply dependentFunction_heq
  intro γ
  exact (PSigma.mk.inj_iff.mp ((extensionDecode p A).apply_symm_apply ⟨σ γ, t γ⟩)).2

/-- Comprehension's uniqueness law reconstructs the whole material member. -/
theorem pair_eta (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (A : Family Δ) (σ : Substitution Γ (extension p A)) :
    pair p (projection p A ∘ σ) A (fun γ => lastVariable p A (σ γ)) = σ := by
  funext γ
  exact (extensionDecode p A).symm_apply_apply (σ γ)

/-- Actual material hyperset contexts inhabit the library's common CwF core. -/
def hypersetCwf (p : HSet.Presentation.{u}) : Cwf.{u + 1, u + 1, u + 1, u + 1} where
  Ctx := HSet.{u}
  Sub := Substitution
  idS _ := id
  compS σ τ := σ ∘ τ
  id_comp _ := rfl
  comp_id _ := rfl
  comp_assoc _ _ _ := rfl
  Ty := Family
  tySub A σ := A ∘ σ
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  Tm _ := Section
  tmSub t σ := fun γ => t (σ γ)
  tmSub_id _ := rfl
  tmSub_comp _ _ _ := rfl
  ext _ := extension p
  wk := projection p
  vz := lastVariable p
  pair := pair p
  wk_pair σ A t := projection_pair p σ A t
  vz_pair σ A t := eq_of_heq ((variable_pair_heq p σ A t).trans (cast_heq _ t).symm)
  pair_eta A σ := pair_eta p A σ

/-- Lift a substitution through actual material comprehension, retaining the
last member and re-encoding the substituted base member. -/
def liftSubstitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) :
    Substitution (extension p (A ∘ σ)) (extension p A) :=
  fun q => (extensionDecode p A).symm
    ⟨σ (projection p (A ∘ σ) q), lastVariable p (A ∘ σ) q⟩

/-- The concrete material lift is the common CwF's canonical comprehension
substitution, including its supplied dependent variable. -/
theorem extensionSubstitution_eq_lift (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) :
    TypeOver.extensionSubstitution (C := hypersetCwf p) σ A = liftSubstitution p σ A := rfl

theorem liftSubstitution_projection (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) :
    projection p A ∘ liftSubstitution p σ A = σ ∘ projection p (A ∘ σ) := by
  funext q
  exact congrArg PSigma.fst ((extensionDecode p A).apply_symm_apply
    ⟨σ (projection p (A ∘ σ) q), lastVariable p (A ∘ σ) q⟩)

/-- The material lift retains the last variable, across the projection
equality needed to identify its dependent type. -/
theorem liftSubstitution_variable_heq (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) :
    HEq (fun q => lastVariable p A (liftSubstitution p σ A q))
      (lastVariable p (A ∘ σ)) := by
  apply dependentFunction_heq
  intro q
  exact (PSigma.mk.inj_iff.mp ((extensionDecode p A).apply_symm_apply
    ⟨σ (projection p (A ∘ σ) q), lastVariable p (A ∘ σ) q⟩)).2

/-- On an encoded material pair, lifting changes precisely its base member. -/
theorem liftSubstitution_pair (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) (γ : Elements Γ) (x : Elements (A (σ γ))) :
    liftSubstitution p σ A ((extensionDecode p (A ∘ σ)).symm ⟨γ, x⟩) =
      (extensionDecode p A).symm ⟨σ γ, x⟩ :=
  congrArg (fun q : Σ' γ : Elements Γ, Elements (A (σ γ)) =>
    (extensionDecode p A).symm ⟨σ q.1, q.2⟩)
    ((extensionDecode p (A ∘ σ)).apply_symm_apply ⟨γ, x⟩)

theorem liftSubstitution_id (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    liftSubstitution p id A = id := by
  funext q
  exact (extensionDecode p A).symm_apply_apply q

theorem liftSubstitution_comp (p : HSet.Presentation.{u}) {Γ Δ Θ : HSet.{u}}
    (σ : Substitution Δ Θ) (τ : Substitution Γ Δ) (A : Family Θ) :
    liftSubstitution p (σ ∘ τ) A = liftSubstitution p σ A ∘ liftSubstitution p τ (A ∘ σ) := by
  funext q
  obtain ⟨ab, rfl⟩ := (extensionDecode p (A ∘ (σ ∘ τ))).symm.surjective q
  rcases ab with ⟨γ, x⟩
  calc
    _ = (extensionDecode p A).symm ⟨σ (τ γ), x⟩ :=
      liftSubstitution_pair p (σ ∘ τ) A γ x
    _ = liftSubstitution p σ A ((extensionDecode p (A ∘ σ)).symm ⟨τ γ, x⟩) :=
      (liftSubstitution_pair p σ A (τ γ) x).symm
    _ = _ := congrArg (liftSubstitution p σ A) (liftSubstitution_pair p τ (A ∘ σ) γ x).symm

/-- Pulling back the family selected by an argument commutes with material
context substitution and its actual comprehension lift. -/
theorem argumentFamily_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) (B : Family (extension p A)) (argument : Section A) :
    (fun γ => B (pair p id A argument (σ γ))) =
      fun γ => B (liftSubstitution p σ A
        (pair p id (A ∘ σ) (fun δ => argument (σ δ)) γ)) := by
  funext γ
  exact (congrArg B (liftSubstitution_pair p σ A γ (argument (σ γ)))).symm

/-- Transport a dependent section along a proved equality of type families. -/
def sectionTransport {Γ : HSet.{u}} {A B : Family Γ} (same : A = B) (t : Section A) :
    Section B := same ▸ t

theorem sectionTransport_heq {Γ : HSet.{u}} {A B : Family Γ} (same : A = B) (t : Section A) :
    HEq (sectionTransport same t) t := by
  cases same
  rfl

/-- The semantic equality cast keeps every supplied hyperset member value. -/
theorem sectionTransport_value {Γ : HSet.{u}} {A B : Family Γ} (same : A = B)
    (t : Section A) (γ : Elements Γ) : (sectionTransport same t γ).1 = (t γ).1 := by
  cases same
  rfl

/-- A singleton material context is terminal because it has one member. -/
def terminalContext : HSet.{u} := {∅}

def toTerminal (Γ : HSet.{u}) : Substitution Γ terminalContext :=
  fun _ => ⟨∅, HSet.mem_singleton_self ∅⟩

theorem toTerminal_unique (Γ : HSet.{u}) (σ : Substitution Γ terminalContext) :
    σ = toTerminal Γ := by
  funext γ
  exact El.ext HSet.propositional (HSet.mem_singleton.mp (σ γ).2)

/-- The same material CwF also has an actual terminal context. -/
def hypersetCwfWithTerminal (p : HSet.Presentation.{u}) :
    CwfWithTerminal.{u + 1, u + 1, u + 1, u + 1} where
  toCwf := hypersetCwf p
  empty := terminalContext
  toEmpty := toTerminal
  toEmpty_unique := toTerminal_unique

/-- An empty material set cannot replace the terminal context: it receives
no substitution from the singleton context. -/
theorem no_terminal_to_empty : ¬ Nonempty (Substitution terminalContext.{u} ∅) := by
  rintro ⟨σ⟩
  let value := σ ⟨∅, HSet.mem_singleton_self ∅⟩
  exact HSet.notMem_empty value.1 value.2

/-! ## Material dependent products over material comprehension -/

/-- Restrict the codomain on material comprehension to one base member's
argument fibre, using actual material pair construction. -/
def fibreFamily (p : HSet.Presentation.{u}) {Γ : HSet.{u}}
    (A : Family Γ) (B : Family (extension p A)) (γ : Elements Γ) : Family (A γ) :=
  fun x => B ((extensionDecode p A).symm ⟨γ, x⟩)

/-- Each contextual product type is the material set of dependent function
graphs at its base member. -/
def piFamily (p : HSet.Presentation.{u}) {Γ : HSet.{u}}
    (A : Family Γ) (B : Family (extension p A)) : Family Γ :=
  fun γ => HSet.dependentProduct p (A γ) (fibreFamily p A B γ)

/-- Product formation commutes with material context substitution as an
equality of the selected hyperset-valued families. -/
theorem piFamily_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) (B : Family (extension p A)) :
    piFamily p A B ∘ σ = piFamily p (A ∘ σ) (B ∘ liftSubstitution p σ A) := by
  funext γ
  apply congrArg (HSet.dependentProduct p (A (σ γ)))
  funext x
  exact (congrArg B (liftSubstitution_pair p σ A γ x)).symm

def piDecode (p : HSet.Presentation.{u}) {Γ : HSet.{u}}
    (A : Family Γ) (B : Family (extension p A)) (γ : Elements Γ) :
    Elements (piFamily p A B γ) ≃
      ((x : Elements (A γ)) → Elements (B ((extensionDecode p A).symm ⟨γ, x⟩))) :=
  HSet.piSetEquiv p (A γ) (fibreFamily p A B γ)

/-- Contextual abstraction builds actual material function graphs. -/
def lam (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (body : Section B) : Section (piFamily p A B) :=
  fun γ => (piDecode p A B γ).symm fun x => body ((extensionDecode p A).symm ⟨γ, x⟩)

/-- Application evaluates the material function graph at the chosen argument. -/
def app (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (f : Section (piFamily p A B)) (argument : Section A) :
    Section (fun γ => B (pair p id A argument γ)) :=
  fun γ => piDecode p A B γ (f γ) (argument γ)

/-- Beta retains the body value after substitution into material comprehension. -/
theorem app_lam (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (body : Section B) (argument : Section A) :
    app p (lam p body) argument = fun γ => body (pair p id A argument γ) := by
  funext γ
  exact congrFun ((piDecode p A B γ).apply_symm_apply
    (fun x => body ((extensionDecode p A).symm ⟨γ, x⟩))) (argument γ)

/-- Application's material value is the graph row evaluated by the existing
union/replacement/separation construction. -/
theorem app_value (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (f : Section (piFamily p A B)) (argument : Section A)
    (γ : Elements Γ) :
    (app p f argument γ).1 = graphValue (HSet.dependentReplacement p) HSet.union HSet.kuratowski
      HSet.separation (f γ).1 (argument γ).1 := rfl

/-- Abstraction commutes with substitution after the explicit product-family
cast, preserving the complete material function graph. -/
theorem lam_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) {A : Family Δ} {B : Family (extension p A)} (body : Section B) :
    sectionTransport (piFamily_substitution p σ A B) (fun γ => lam p body (σ γ)) =
      lam p (fun q => body (liftSubstitution p σ A q)) := by
  funext γ
  apply El.ext HSet.propositional
  rw [sectionTransport_value]
  change HSet.image p (A (σ γ)) (fun x =>
      HSet.kpair x.1 (body ((extensionDecode p A).symm ⟨σ γ, x⟩)).1) =
    HSet.image p (A (σ γ)) (fun x =>
      HSet.kpair x.1 (body (liftSubstitution p σ A ((extensionDecode p (A ∘ σ)).symm ⟨γ, x⟩))).1)
  apply congrArg (HSet.image p (A (σ γ)))
  funext x
  exact (congrArg (fun q => HSet.kpair x.1 (body q).1)
    (liftSubstitution_pair p σ A γ x)).symm

/-- Application commutes with substitution with both result and function
family casts explicit. Every cast preserves the original member value. -/
theorem app_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) {A : Family Δ} {B : Family (extension p A)}
    (f : Section (piFamily p A B)) (argument : Section A) :
    sectionTransport (argumentFamily_substitution p σ A B argument)
        (fun γ => app p f argument (σ γ)) =
      app p (sectionTransport (piFamily_substitution p σ A B) (fun γ => f (σ γ)))
        (fun γ => argument (σ γ)) := by
  funext γ
  apply El.ext HSet.propositional
  rw [sectionTransport_value, app_value, app_value, sectionTransport_value]

/-- Uncurry a contextual function into a body over the actual material
extension; the decoder's inverse law transports its dependent result. -/
def evaluationBody (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (f : Section (piFamily p A B)) : Section B :=
  fun q => transport (Mem := fun x X : HSet.{u} => x ∈ X)
    (congrArg B ((extensionDecode p A).symm_apply_apply q))
    (piDecode p A B (projection p A q) (f (projection p A q)) (lastVariable p A q))

/-- The equality transport in the evaluation body keeps the actual returned
hyperset, rather than selecting a replacement member. -/
theorem evaluationBody_value (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (f : Section (piFamily p A B))
    (q : Elements (extension p A)) :
    (evaluationBody p f q).1 =
      (piDecode p A B (projection p A q) (f (projection p A q)) (lastVariable p A q)).1 :=
  transport_fst _ _

/-- The full evaluation body agrees with application on every actual
material pair member. -/
theorem evaluationBody_pair (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (f : Section (piFamily p A B))
    (γ : Elements Γ) (x : Elements (A γ)) :
    evaluationBody p f ((extensionDecode p A).symm ⟨γ, x⟩) = piDecode p A B γ (f γ) x := by
  apply El.ext HSet.propositional
  rw [evaluationBody_value]
  exact congrArg (fun q : Σ' γ : Elements Γ, Elements (A γ) =>
    (piDecode p A B q.1 (f q.1) q.2).1) ((extensionDecode p A).apply_symm_apply ⟨γ, x⟩)

/-- Abstracting the full evaluation body recovers the entire material
function graph at each contextual point. -/
theorem lam_eta (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (f : Section (piFamily p A B)) :
    lam p (evaluationBody p f) = f := by
  funext γ
  apply (piDecode p A B γ).injective
  change piDecode p A B γ ((piDecode p A B γ).symm _) = piDecode p A B γ (f γ)
  rw [Equiv.apply_symm_apply]
  funext x
  exact evaluationBody_pair p f γ x

/-- Evaluating an abstraction on the full material comprehension restores
the original dependent body, including its member value. -/
theorem evaluationBody_lam (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (body : Section B) : evaluationBody p (lam p body) = body := by
  funext q
  obtain ⟨ab, rfl⟩ := (extensionDecode p A).symm.surjective q
  rw [evaluationBody_pair]
  exact congrFun ((piDecode p A B ab.1).apply_symm_apply
    (fun x => body ((extensionDecode p A).symm ⟨ab.1, x⟩))) ab.2

/-- Terms over material comprehension correspond to terms of the material
dependent product through actual abstraction and evaluation. -/
def piSectionEquiv (p : HSet.Presentation.{u}) {Γ : HSet.{u}}
    (A : Family Γ) (B : Family (extension p A)) : Section B ≃ Section (piFamily p A B) where
  toFun := lam p
  invFun := evaluationBody p
  left_inv := evaluationBody_lam p
  right_inv := lam_eta p

/-- The material dependent products inhabit the same beta interface used by
the displayed-presheaf CwF. -/
def hypersetProducts (p : HSet.Presentation.{u}) : DependentProductBeta (hypersetCwf p) where
  pi := piFamily p
  lam := lam p
  app := app p
  beta := app_lam p

/-- The formation square is also stated through the common product and CwF
interfaces, with their canonical extension substitution. -/
theorem hypersetProducts_formation_substitution (p : HSet.Presentation.{u})
    {Γ Δ : (hypersetCwf p).Ctx} (σ : (hypersetCwf p).Sub Γ Δ)
    (A : (hypersetCwf p).Ty Δ) (B : (hypersetCwf p).Ty ((hypersetCwf p).ext Δ A)) :
    (hypersetCwf p).tySub ((hypersetProducts p).pi A B) σ =
      (hypersetProducts p).pi ((hypersetCwf p).tySub A σ)
        ((hypersetCwf p).tySub B (TypeOver.extensionSubstitution σ A)) :=
  piFamily_substitution p σ A B

/-! ## Material dependent sums over material comprehension -/

/-- Each contextual sum type is the material set of ordered pairs at its
base member, with codomain indexed through actual comprehension. -/
def sigmaFamily (p : HSet.Presentation.{u}) {Γ : HSet.{u}}
    (A : Family Γ) (B : Family (extension p A)) : Family Γ :=
  fun γ => sigmaSet (HSet.dependentReplacement p) HSet.union HSet.kuratowski
    (A γ) (fibreFamily p A B γ)

theorem sigmaFamily_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) (B : Family (extension p A)) :
    sigmaFamily p A B ∘ σ = sigmaFamily p (A ∘ σ) (B ∘ liftSubstitution p σ A) := by
  funext γ
  apply congrArg (sigmaSet (HSet.dependentReplacement p) HSet.union HSet.kuratowski (A (σ γ)))
  funext x
  exact (congrArg B (liftSubstitution_pair p σ A γ x)).symm

def sigmaDecode (p : HSet.Presentation.{u}) {Γ : HSet.{u}}
    (A : Family Γ) (B : Family (extension p A)) (γ : Elements Γ) :
    Elements (sigmaFamily p A B γ) ≃
      Σ' x : Elements (A γ), Elements (B ((extensionDecode p A).symm ⟨γ, x⟩)) :=
  HSet.sigmaSetEquiv p (A γ) (fibreFamily p A B γ)

/-- Introduce a contextual dependent sum as an actual material ordered pair. -/
def sigmaPair (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (first : Section A)
    (second : Section (fun γ => B (pair p id A first γ))) : Section (sigmaFamily p A B) :=
  fun γ => (sigmaDecode p A B γ).symm ⟨first γ, second γ⟩

def sigmaFirst (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (value : Section (sigmaFamily p A B)) : Section A :=
  fun γ => (sigmaDecode p A B γ (value γ)).1

/-- The second projection retains its dependence on the recovered first
member through material context comprehension. -/
def sigmaSecond (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (value : Section (sigmaFamily p A B)) :
    Section (fun γ => B (pair p id A (sigmaFirst p value) γ)) :=
  fun γ => (sigmaDecode p A B γ (value γ)).2

theorem sigmaPair_value (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (first : Section A)
    (second : Section (fun γ => B (pair p id A first γ))) (γ : Elements Γ) :
    (sigmaPair p first second γ).1 = HSet.kpair (first γ).1 (second γ).1 := rfl

theorem sigmaFirst_value (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (value : Section (sigmaFamily p A B)) (γ : Elements Γ) :
    (sigmaFirst p value γ).1 = HSet.fst (value γ).1 := rfl

theorem sigmaSecond_value (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (value : Section (sigmaFamily p A B)) (γ : Elements Γ) :
    (sigmaSecond p value γ).1 = HSet.snd (value γ).1 := rfl

/-- Dependent pair introduction commutes with material substitution; both
the result-family and second-component casts are explicit and value-retaining. -/
theorem sigmaPair_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) {A : Family Δ} {B : Family (extension p A)}
    (first : Section A) (second : Section (fun γ => B (pair p id A first γ))) :
    sectionTransport (sigmaFamily_substitution p σ A B)
        (fun γ => sigmaPair p first second (σ γ)) =
      sigmaPair p (fun γ => first (σ γ))
        (sectionTransport (argumentFamily_substitution p σ A B first)
          (fun γ => second (σ γ))) := by
  funext γ
  apply El.ext HSet.propositional
  rw [sectionTransport_value, sigmaPair_value, sigmaPair_value, sectionTransport_value]

/-- The first projection commutes with substitution of the complete material
sum member, after its explicit family cast. -/
theorem sigmaFirst_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) {A : Family Δ} {B : Family (extension p A)}
    (value : Section (sigmaFamily p A B)) :
    (fun γ => sigmaFirst p value (σ γ)) =
      sigmaFirst p (sectionTransport (sigmaFamily_substitution p σ A B)
        (fun γ => value (σ γ))) := by
  funext γ
  apply El.ext HSet.propositional
  rw [sigmaFirst_value, sigmaFirst_value, sectionTransport_value]

/-- The second-projection fibre is preserved under substitution, accounting
for both comprehension's lift and the actual reindexed first projection. -/
theorem sigmaSecondFamily_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) {A : Family Δ} {B : Family (extension p A)}
    (value : Section (sigmaFamily p A B)) :
    (fun γ => B (pair p id A (sigmaFirst p value) (σ γ))) =
      fun γ => B (liftSubstitution p σ A
        (pair p id (A ∘ σ)
          (sigmaFirst p (sectionTransport (sigmaFamily_substitution p σ A B)
            (fun γ => value (σ γ)))) γ)) :=
  (argumentFamily_substitution p σ A B (sigmaFirst p value)).trans
    (congrArg (fun first : Section (A ∘ σ) =>
      fun γ => B (liftSubstitution p σ A (pair p id (A ∘ σ) first γ)))
      (sigmaFirst_substitution p σ value))

/-- The dependent second projection commutes with substitution across the
explicit proved equality of its indexed fibres. -/
theorem sigmaSecond_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) {A : Family Δ} {B : Family (extension p A)}
    (value : Section (sigmaFamily p A B)) :
    sectionTransport (sigmaSecondFamily_substitution p σ value)
        (fun γ => sigmaSecond p value (σ γ)) =
      sigmaSecond p (sectionTransport (sigmaFamily_substitution p σ A B)
        (fun γ => value (σ γ))) := by
  funext γ
  apply El.ext HSet.propositional
  rw [sectionTransport_value, sigmaSecond_value, sigmaSecond_value, sectionTransport_value]

theorem sigmaFirst_pair (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (first : Section A)
    (second : Section (fun γ => B (pair p id A first γ))) :
    sigmaFirst p (sigmaPair p first second) = first := by
  funext γ
  exact congrArg PSigma.fst ((sigmaDecode p A B γ).apply_symm_apply ⟨first γ, second γ⟩)

theorem sigmaSecond_pair_heq (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (first : Section A)
    (second : Section (fun γ => B (pair p id A first γ))) :
    HEq (sigmaSecond p (sigmaPair p first second)) second := by
  apply dependentFunction_heq
  intro γ
  exact (PSigma.mk.inj_iff.mp
    ((sigmaDecode p A B γ).apply_symm_apply ⟨first γ, second γ⟩)).2

/-- Re-pairing both dependent projections recovers the complete material
sum member at each contextual point. -/
theorem sigma_eta (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (value : Section (sigmaFamily p A B)) :
    sigmaPair p (sigmaFirst p value) (sigmaSecond p value) = value := by
  funext γ
  exact (sigmaDecode p A B γ).symm_apply_apply (value γ)

/-- The material sums inhabit the same dependent-sum beta interface as the
other semantic and syntactic contextual models. -/
def hypersetSums (p : HSet.Presentation.{u}) : DependentSumBeta (hypersetCwf p) where
  sigma := sigmaFamily p
  pair := sigmaPair p
  fst := sigmaFirst p
  snd := sigmaSecond p
  fst_pair := sigmaFirst_pair p
  snd_pair := sigmaSecond_pair_heq p

theorem hypersetSums_formation_substitution (p : HSet.Presentation.{u})
    {Γ Δ : (hypersetCwf p).Ctx} (σ : (hypersetCwf p).Sub Γ Δ)
    (A : (hypersetCwf p).Ty Δ) (B : (hypersetCwf p).Ty ((hypersetCwf p).ext Δ A)) :
    (hypersetCwf p).tySub ((hypersetSums p).sigma A B) σ =
      (hypersetSums p).sigma ((hypersetCwf p).tySub A σ)
        ((hypersetCwf p).tySub B (TypeOver.extensionSubstitution σ A)) :=
  sigmaFamily_substitution p σ A B

/-! ## The common semantic substitution interfaces -/

def hypersetPiOperations (p : HSet.Presentation.{u}) : PiOperations (hypersetCwf p) :=
  PiOperations.ofQualified (hypersetProducts p)

def hypersetSigmaOperations (p : HSet.Presentation.{u}) : SigmaOperations (hypersetCwf p) :=
  SigmaOperations.ofQualified (hypersetSums p)

/-- Semantic representative equality and heterogeneous term equality are
proved for the actual material products. This is the common interface's
`Strict` predicate, not a native judgmental-conversion theorem. -/
theorem hypersetPiOperations_substitution (p : HSet.Presentation.{u}) :
    StrictPiSubstitution (hypersetPiOperations p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Γ Δ σ A B
    exact piFamily_substitution p σ A B
  · intro Γ Δ σ A B body
    exact (sectionTransport_heq (piFamily_substitution p σ A B)
      (fun γ => lam p body (σ γ))).symm.trans (heq_of_eq (lam_substitution p σ body))
  · intro Γ Δ σ A B f argument reindexedFunction same
    have canonical : sectionTransport (piFamily_substitution p σ A B)
        (fun γ => f (σ γ)) = reindexedFunction :=
      eq_of_heq ((sectionTransport_heq (piFamily_substitution p σ A B)
        (fun γ => f (σ γ))).trans same)
    cases canonical
    exact (sectionTransport_heq (argumentFamily_substitution p σ A B argument)
      (fun γ => app p f argument (σ γ))).symm.trans (heq_of_eq (app_substitution p σ f argument))

/-- The actual material sums satisfy formation, introduction and both
projection substitution laws through the same semantic interface. -/
theorem hypersetSigmaOperations_substitution (p : HSet.Presentation.{u}) :
    StrictSigmaSubstitution (hypersetSigmaOperations p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Γ Δ σ A B
    exact sigmaFamily_substitution p σ A B
  · intro Γ Δ σ A B first second reindexedSecond same
    have canonical : sectionTransport (argumentFamily_substitution p σ A B first)
        (fun γ => second (σ γ)) = reindexedSecond :=
      eq_of_heq ((sectionTransport_heq (argumentFamily_substitution p σ A B first)
        (fun γ => second (σ γ))).trans same)
    cases canonical
    exact (sectionTransport_heq (sigmaFamily_substitution p σ A B)
      (fun γ => sigmaPair p first second (σ γ))).symm.trans
        (heq_of_eq (sigmaPair_substitution p σ first second))
  · intro Γ Δ σ A B value reindexedValue same
    have canonical : sectionTransport (sigmaFamily_substitution p σ A B)
        (fun γ => value (σ γ)) = reindexedValue :=
      eq_of_heq ((sectionTransport_heq (sigmaFamily_substitution p σ A B)
        (fun γ => value (σ γ))).trans same)
    cases canonical
    refine ⟨heq_of_eq (sigmaFirst_substitution p σ value), ?_⟩
    exact (sectionTransport_heq (sigmaSecondFamily_substitution p σ value)
      (fun γ => sigmaSecond p value (σ γ))).symm.trans
        (heq_of_eq (sigmaSecond_substitution p σ value))

theorem hypersetPiOperations_beta (p : HSet.Presentation.{u}) :
    PiBeta (hypersetPiOperations p) := PiOperations.ofQualified_beta (hypersetProducts p)

theorem hypersetSigmaOperations_beta (p : HSet.Presentation.{u}) :
    SigmaBeta (hypersetSigmaOperations p) := SigmaOperations.ofQualified_beta (hypersetSums p)

/-! ## Non-well-founded and genuinely dependent controls -/

/-- A material argument family containing the self-membered quine atom. -/
def quineFamily : Family terminalContext.{u} := fun _ => {HSet.quineAtom}

def quineArgument : Section quineFamily.{u} :=
  fun _ => ⟨HSet.quineAtom, HSet.mem_singleton_self HSet.quineAtom⟩

/-- Material comprehension retains the non-well-founded argument as an
ordinary member; no foundation restriction is imposed on contextual types. -/
theorem quine_comprehension_value (p : HSet.Presentation.{u}) (γ : Elements terminalContext) :
    (pair p id quineFamily quineArgument γ).1 = HSet.kpair γ.1 HSet.quineAtom :=
  pair_value p id quineFamily quineArgument γ

/-- Decoding that actual material pair recovers the same quine-valued last
variable, not a well-founded approximation. -/
theorem quine_lastVariable_value (p : HSet.Presentation.{u}) (γ : Elements terminalContext) :
    (lastVariable p quineFamily (pair p id quineFamily quineArgument γ)).1 = HSet.quineAtom :=
  congrArg (fun ab : Σ' γ : Elements terminalContext, Elements (quineFamily γ) => ab.2.1)
    ((extensionDecode p quineFamily).apply_symm_apply ⟨γ, quineArgument γ⟩)

def quineBody (p : HSet.Presentation.{u}) :
    Section (fun _ : Elements (extension p quineFamily) => {HSet.quineAtom}) :=
  fun _ => ⟨HSet.quineAtom, HSet.mem_singleton_self HSet.quineAtom⟩

/-- The contextual material product admits and computes an actual
non-well-founded argument/result, using its proved graph evaluation. -/
theorem quine_application_value (p : HSet.Presentation.{u}) (γ : Elements terminalContext) :
    (app p (lam p (quineBody p)) quineArgument γ).1 = HSet.quineAtom := by
  rw [app_lam]
  rfl

/-- A context with two set members supporting a genuinely varying family. -/
def varyingBase : HSet.{u} := {∅, {∅}}

def memberFamily : Family varyingBase.{u} := fun γ => γ.1

theorem memberFamily_not_constant :
    ¬ ∃ X : HSet.{u}, ∀ γ : Elements varyingBase, memberFamily γ = X := by
  rintro ⟨X, h⟩
  have emptyEq := h ⟨∅, HSet.mem_pair.mpr (Or.inl rfl)⟩
  have singletonEq := h ⟨{∅}, HSet.mem_pair.mpr (Or.inr rfl)⟩
  exact HSet.empty_ne_singleton_empty (emptyEq.trans singletonEq.symm)

/-- There is no total section of the varying family: at its empty member,
the required dependent result has no inhabitant. -/
theorem no_memberFamily_section : ¬ Nonempty (Section memberFamily.{u}) := by
  rintro ⟨s⟩
  let result := s ⟨∅, HSet.mem_pair.mpr (Or.inl rfl)⟩
  exact HSet.notMem_empty result.1 result.2

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyCwf
