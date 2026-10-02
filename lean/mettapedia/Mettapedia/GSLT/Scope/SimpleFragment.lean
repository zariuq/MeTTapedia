import Mettapedia.GSLT.Scope.Simulation
import Mettapedia.GSLT.Scope.Arrows
import Mettapedia.GSLT.Scope.ConsumerDescent
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision
import Mettapedia.OSLF.Syntax.LambdaBetaEtaContextQuotient
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SimpleFragment

/-!
# The four kinds of scope change on the candidate's simple fragment

The simple fragment of the candidate dependent type theory is the intrinsic
one-base simply typed λ-calculus, embedded into the candidate's sealed tower
by erasure (`TowerDTT.eraseTerm`).  Both are GSLTs with syntactic equations:
β-reduction on intrinsic terms (`simpleSystem`) and the tower's one-step
reduction on raw terms (`towerSystem`).  Erasure preserves every β-step, so
it is an operational translation (`eraseTranslation`), the arrow of the
operational equipment between them.  It also reflects every step of the
tower out of an erased term (`erase_liftStep`), so it is a bounded morphism
(`erase_isBoundedMorphism`) and a covered translation (`eraseCovered`): the
slice is closed under the candidate's reduction, every Hennessy–Milner
formula has the same truth at a simple term and at its erasure
(`sat_erase_iff`), and terms with one erasure are bisimilar
(`bisimilar_of_erase_eq`), such as the two distinct discarded identities
(`discardIdentities_bisimilar`).

Two scopes read the fragment.
* **The equational scope**: an interpretation of terms into some type
  satisfies an equation when it identifies both sides (`equates`).  The
  consequences of the β-equations are β-conversion (`consequences_beta`), and
  the consequences of the tower's steps are tower conversion
  (`consequences_tower`).
* **The program scope**: terms satisfy predicates; an observer is an
  equivalence on terms.

Each kind of scope change, with its law from the scope algebra, a positive
instance and a failing control:

* translate along erasure (`Translation.conservative_iff_hostsFaithfully`):
  positive `erase_conservative_beta`, control `erase_not_conservative_empty`;
* restrict programs to the slice (`restrict_conservative_iff_hostsFaithfully`):
  positive `slice_hostsFaithfully_membership`, control `slice_gains_sn` with
  `slice_not_conservative`;
* restrict models to the slice's reducts (the same law): positive
  `slice_hostsFaithfully_beta`, control `standardModels_not_hostsFaithfully`;
* identify by equations, a carve (`carve_conservative_iff`): positive
  `carve_derivable_conservative`, control `carve_eta_not_conservative`;
* forget to a coarser observer (`function_descends_iff`,
  `mem_observable_iff_factors`): positive `denote_descends_betaEta`, control
  `normalForm_not_descends_betaEta`.

**Translation.**  Erasure translates equations forward and pulls
interpretations of raw terms back (`eraseScope`).  Into the models of the
tower's conversion it is conservative over the β-theory
(`erase_conservative_beta`): this is `towerConv_iff_betaConv`, read as the
conservativity law.  It is not conservative over the empty theory
(`erase_not_conservative_empty`): erasure forgets application-domain
annotations, so two distinct terms, convertible but not equal, have one
erasure.

**Restriction of programs.**  Among the raw terms of the candidate's
executable package, restricting to the erased simple terms gains strong
normalization (`slice_gains_sn`), the package's own normalization theorem
for its simple fragment; over all raw terms it fails at the self-application
`Ω` (`omega_not_sn`), so the restriction is not conservative
(`slice_not_conservative`).  This is the carve-out reading: the fragment's
property is a theorem about the fragment, not a restriction of the ambient
judgment.

**Restriction of models.**  By the translation law, the tower's conversion models seen
through erasure, the universe of reducts on the slice, host the β-theory
faithfully (`slice_hostsFaithfully_beta`).  Restricting instead to the
standard function-space models gains the η-equation
(`eta_mem_standardModels`), so they do not host the β-theory faithfully
(`standardModels_not_hostsFaithfully`); the generic model of any theory
does (`generic_hostsFaithfully`).

**Identification.**  Carving the interpretations by η is not conservative over
β (`carve_eta_not_conservative`), since η is not a β-consequence
(`eta_not_consequence`); carving by a β-derivable equation is
(`carve_derivable_conservative`).

**Forgetting.**  The βη observer is coarser than the β observer
(`beta_le_betaEta`).  The denotation in every function space descends to βη
classes (`denote_descends_betaEta`).  The β-normal form, the answer of the
fragment's native normalization service, descends to β classes
(`normalForm_descends_beta`) and not to βη classes
(`normalForm_not_descends_betaEta`): the predicate "has this β-normal form"
is visible to the β observer and not to the βη observer
(`normalFormPredicate_observable_beta`,
`normalFormPredicate_not_observable_betaEta`).

**Axioms.**  The results that mention β-conversion of distinct normal forms
inherit `Classical.choice` from the fragment's normalization and the tower's
confluence (`ConversionDecision.towerConv_iff_betaConv`,
`ConversionDecision.eta_not_betaConvertible`); the others use at most
`propext` and `Quot.sound`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.SimpleFragment

open Set
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Logic.TheoryModel
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision

/-! ## The fragment and the candidate as GSLTs -/

/-- The simple fragment at a context and a type, with β-reduction. -/
abbrev simpleSystem (Γ : List Ty) (A : Ty) : GSLT :=
  transitionSystem (@BetaStep Γ A)

/-- One-step reduction of the candidate's sealed tower. -/
abbrev TowerStep (n : ℕ) : Presentation.Tower.Tm n → Presentation.Tower.Tm n → Prop :=
  Presentation.StepCore Presentation.Tower.rules.computation Presentation.Tower.rules.headEq

/-- The candidate's sealed tower on raw terms with `n` free variables. -/
abbrev towerSystem (n : ℕ) : GSLT :=
  transitionSystem (TowerStep n)

/-- **The GSLT morphism**: erasure into the candidate preserves every
β-step. -/
def eraseTranslation (Γ : List Ty) (A : Ty) :
    OperationalTranslation (simpleSystem Γ A) (towerSystem Γ.length) :=
  operationalOfPreserves fun _ _ step => BetaStep.erase step

@[simp] theorem eraseTranslation_mapTerm (Γ : List Ty) (A : Ty) :
    (eraseTranslation Γ A).mapTerm = TowerDTT.eraseTerm :=
  rfl

/-- Erasure maps every β-reduction path to a candidate execution path of the
same length. -/
theorem erase_path_length {Γ : List Ty} {A : Ty} {first last : Term Γ A}
    (path : ExecutionPath (simpleSystem Γ A) first last) :
    ((eraseTranslation Γ A).mapRoute path).length = path.length :=
  OperationalTranslation.mapRoute_length _ path

/-! ### Erasure is a functional bisimulation -/

section Bisimulation

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.SubstitutionTranslation

variable {Γ : List Ty} {A : Ty}

/-- A raw variable takes no step of the sealed tower. -/
theorem towerStep_var_inv {n : ℕ} {i : Fin n} {u : Presentation.Tower.Tm n} :
    ¬ TowerStep n (.var i) u := by
  intro step
  cases step with
  | root impossible => exact impossible.elim

/-- A step out of a raw abstraction is a step of its body. -/
theorem towerStep_lam_inv {n : ℕ} {body : Presentation.Tower.Tm (n + 1)}
    {u : Presentation.Tower.Tm n} (step : TowerStep n (.lam body) u) :
    ∃ body', TowerStep (n + 1) body body' ∧ u = .lam body' := by
  cases step with
  | root impossible => exact impossible.elim
  | congLam inner => exact ⟨_, inner, rfl⟩

/-- A step out of a raw application is a root β-step or a step of one of its
two parts. -/
theorem towerStep_app_inv {n : ℕ} {function argument u : Presentation.Tower.Tm n}
    (step : TowerStep n (.app function argument) u) :
    (∃ body, function = .lam body ∧ u = Presentation.inst0 argument body) ∨
      (∃ function', TowerStep n function function' ∧ u = .app function' argument) ∨
      ∃ argument', TowerStep n argument argument' ∧ u = .app function argument' := by
  cases step with
  | betaPi body _ => exact Or.inl ⟨body, rfl, rfl⟩
  | root impossible => exact impossible.elim
  | congAppFun inner => exact Or.inr (Or.inl ⟨_, inner, rfl⟩)
  | congAppArg inner => exact Or.inr (Or.inr ⟨_, inner, rfl⟩)

/-- **Erasure reflects the candidate's steps**: every step of the sealed tower
out of an erased simple term is the erasure of a β-step. -/
theorem erase_liftStep : ∀ {Γ : List Ty} {A : Ty} (t : Term Γ A)
    {u : Presentation.Tower.Tm Γ.length},
    TowerStep Γ.length (TowerDTT.eraseTerm t) u →
      ∃ t', BetaStep t t' ∧ TowerDTT.eraseTerm t' = u
  | _, _, .var _, _, step => (towerStep_var_inv step).elim
  | _, _, .lam body, _, step => by
      obtain ⟨_, inner, rfl⟩ := towerStep_lam_inv step
      obtain ⟨t', reduces, rfl⟩ := erase_liftStep body inner
      exact ⟨.lam t', .lam reduces, rfl⟩
  | _, _, .app function argument, _, step => by
      rcases towerStep_app_inv step with ⟨body, isLam, rfl⟩ | ⟨_, inner, rfl⟩ | ⟨_, inner, rfl⟩
      · cases function with
        | var _ => cases isLam
        | app _ _ => cases isLam
        | lam functionBody =>
            injection isLam with _ sameBody
            subst sameBody
            exact ⟨functionBody.instantiateNewest argument, .beta functionBody argument,
              eraseTerm_instantiateNewest functionBody argument⟩
      · obtain ⟨t', reduces, rfl⟩ := erase_liftStep function inner
        exact ⟨.app t' argument, .appLeft reduces, rfl⟩
      · obtain ⟨t', reduces, rfl⟩ := erase_liftStep argument inner
        exact ⟨.app function t', .appRight reduces, rfl⟩

/-- **Erasure is a bounded morphism** from β-reduction of the simple fragment
to the reduction of the sealed tower. -/
theorem erase_isBoundedMorphism (Γ : List Ty) (A : Ty) :
    IsBoundedMorphism (@BetaStep Γ A) (TowerStep Γ.length) TowerDTT.eraseTerm :=
  ⟨fun _ _ reduces => BetaStep.erase reduces, fun t _ step => erase_liftStep t step⟩

/-- **Erasure is a covered translation**: the slice is closed under the
candidate's reduction, which adds no step to it. -/
def eraseCovered (Γ : List Ty) (A : Ty) :
    CoveredTranslation (simpleSystem Γ A) (towerSystem Γ.length) :=
  coveredOfBoundedMorphism (erase_isBoundedMorphism Γ A)

/-- **Every Hennessy–Milner formula has the same truth at a simple term and at
its erasure.** -/
theorem sat_erase_iff (formula : Mettapedia.GSLT.HennessyMilner.Formula PEmpty Unit)
    (t : Term Γ A) :
    (hmSystem (@BetaStep Γ A)).sat formula t ↔
      (hmSystem (TowerStep Γ.length)).sat formula (TowerDTT.eraseTerm t) :=
  sat_iff_of_isBoundedMorphism (erase_isBoundedMorphism Γ A) formula t

/-- **Terms with one erasure are bisimilar**: the raw erasure collision is
invisible to reduction. -/
theorem bisimilar_of_erase_eq {left right : Term Γ A}
    (same : TowerDTT.eraseTerm left = TowerDTT.eraseTerm right) :
    Bisimilar (@BetaStep Γ A) (@BetaStep Γ A) left right :=
  (erase_isBoundedMorphism Γ A).bisimilar_of_eq (erase_isBoundedMorphism Γ A) same

/-- The two discarded identities are distinct and bisimilar. -/
theorem discardIdentities_bisimilar :
    ErasureBoundary.discardAtomicIdentity ≠ ErasureBoundary.discardFunctionIdentity ∧
      Bisimilar (@BetaStep [] (.arr .atom .atom)) (@BetaStep [] (.arr .atom .atom))
        ErasureBoundary.discardAtomicIdentity ErasureBoundary.discardFunctionIdentity :=
  ⟨ErasureBoundary.discardIdentities_ne,
    bisimilar_of_erase_eq ErasureBoundary.erase_discardIdentities_eq⟩

/-- **Erasure supports β-reduction as a nondeterministic update**: its kernel is
a bisimulation. -/
theorem erase_relSupports : RelSupports TowerDTT.eraseTerm (@BetaStep Γ A) :=
  relSupports_iff_exists_isBoundedMorphism.mpr ⟨_, erase_isBoundedMorphism Γ A⟩

end Bisimulation

/-! ## The equational scope -/

variable {Γ : List Ty} {A : Ty}

/-- The β-equations of the fragment: one-step reductions read as equations. -/
def betaEquations (Γ : List Ty) (A : Ty) : Set (Term Γ A × Term Γ A) :=
  {pair | BetaStep pair.1 pair.2}

/-- **The β-theory is β-conversion.** -/
theorem consequences_beta :
    theoryOf equates (models equates (betaEquations Γ A)) = {pair | BetaConv pair.1 pair.2} :=
  consequences_equations _

/-- The tower's one-step reductions read as equations. -/
def towerEquations (n : ℕ) : Set (Presentation.Tower.Tm n × Presentation.Tower.Tm n) :=
  {pair | TowerStep n pair.1 pair.2}

/-- **The tower's theory is tower conversion.** -/
theorem consequences_tower (n : ℕ) :
    theoryOf equates (models equates (towerEquations n)) =
      {pair | Presentation.Conv Presentation.Tower.HeadEq pair.1 pair.2} :=
  consequences_equations _

/-- The interpretations of raw terms that satisfy the tower's conversion. -/
abbrev towerModels (n : ℕ) : Set (Σ Y : Type, Presentation.Tower.Tm n → Y) :=
  models equates (towerEquations n)

/-! ### Translation along erasure -/

/-- **Erasure as a translation of equational scopes**: equations are erased,
and interpretations of raw terms in a universe `U` are pulled back along
erasure. -/
def eraseScope (Γ : List Ty) (A : Ty) (U : Set (Σ Y : Type, Presentation.Tower.Tm Γ.length → Y)) :
    Translation (equates (X := Term Γ A)) (restrictSat equates U) where
  translate pair := (TowerDTT.eraseTerm pair.1, TowerDTT.eraseTerm pair.2)
  reduct model := ⟨model.1.1, fun t => model.1.2 (TowerDTT.eraseTerm t)⟩
  sat_iff _ _ := Iff.rfl

/-- Every model of the tower's conversion satisfies the erased β-equations. -/
theorem towerModel_sat_erased_beta (model : towerModels Γ.length) :
    model ∈ models (restrictSat equates (towerModels Γ.length))
      ((eraseScope Γ A (towerModels Γ.length)).translate '' betaEquations Γ A) := by
  rintro _ ⟨pair, reduces, rfl⟩
  exact model.2 (show TowerStep Γ.length (TowerDTT.eraseTerm pair.1)
    (TowerDTT.eraseTerm pair.2) from BetaStep.erase reduces)

/-- **Erasure is conservative over the candidate's conversion**: a simple
equation is a β-consequence exactly when its erasure is a consequence of
tower conversion.  This is `towerConv_iff_betaConv` in the form of the
conservativity law. -/
theorem erase_conservative_beta (pair : Term Γ A × Term Γ A) :
    pair ∈ theoryOf equates (models equates (betaEquations Γ A)) ↔
      (eraseScope Γ A (towerModels Γ.length)).translate pair ∈
        theoryOf (restrictSat equates (towerModels Γ.length))
          (models (restrictSat equates (towerModels Γ.length))
            ((eraseScope Γ A (towerModels Γ.length)).translate '' betaEquations Γ A)) := by
  rw [consequences_beta]
  change BetaConv pair.1 pair.2 ↔ _
  rw [← towerConv_iff_betaConv]
  constructor
  · intro converts model _
    have entailed : (TowerDTT.eraseTerm pair.1, TowerDTT.eraseTerm pair.2) ∈
        theoryOf equates (models equates (towerEquations Γ.length)) := by
      rw [consequences_tower]
      exact converts
    exact entailed model.2
  · intro entailed
    have inTower : (TowerDTT.eraseTerm pair.1, TowerDTT.eraseTerm pair.2) ∈
        theoryOf equates (models equates (towerEquations Γ.length)) :=
      fun model isModel => entailed (a := ⟨model, isModel⟩) (towerModel_sat_erased_beta _)
    rw [consequences_tower] at inTower
    exact inTower

/-- **Control: erasure is not conservative over the empty theory.**  Two
distinct closed terms have one erasure. -/
theorem erase_not_conservative_empty
    (U : Set (Σ Y : Type, Presentation.Tower.Tm 0 → Y)) :
    ¬ ∀ pair : Term [] (.arr .atom .atom) × Term [] (.arr .atom .atom),
      pair ∈ theoryOf equates (models equates (∅ : Set (Term [] (.arr .atom .atom) ×
          Term [] (.arr .atom .atom)))) ↔
        (eraseScope [] (.arr .atom .atom) U).translate pair ∈
          theoryOf (restrictSat equates U)
            (models (restrictSat equates U)
              ((eraseScope [] (.arr .atom .atom) U).translate '' ∅)) := by
  intro conservative
  have collide : (eraseScope [] (.arr .atom .atom) U).translate
      (ErasureBoundary.discardAtomicIdentity, ErasureBoundary.discardFunctionIdentity) ∈
        theoryOf (restrictSat equates U)
          (models (restrictSat equates U) ((eraseScope [] (.arr .atom .atom) U).translate '' ∅)) :=
    fun model _ => congrArg model.1.2 ErasureBoundary.erase_discardIdentities_eq
  have entailed := (conservative _).mpr collide
  rw [consequences_equations] at entailed
  exact ErasureBoundary.discardIdentities_ne (eq_of_eqvGen_empty entailed)

/-! ### Restriction -/

/-- **The candidate's conversion models, seen on the slice, host the β-theory
faithfully**: restricting to the slice's universe of reducts gains no
theorem.  This is the translation law applied to `erase_conservative_beta`. -/
theorem slice_hostsFaithfully_beta :
    HostsFaithfully equates (range (eraseScope Γ A (towerModels Γ.length)).reduct)
      (betaEquations Γ A) :=
  ((eraseScope Γ A (towerModels Γ.length)).conservative_iff_hostsFaithfully _).mp
    erase_conservative_beta

/-- **The generic model hosts every equational theory faithfully**: the
quotient by the equivalence closure. -/
theorem generic_hostsFaithfully {X : Type} (R : Set (X × X)) :
    HostsFaithfully equates {quotientInterpretation R} R := by
  unfold HostsFaithfully
  rw [consequences_equations]
  ext pair
  constructor
  · intro validated
    exact Quot.eqvGen_exact (validated ⟨rfl, quotientInterpretation_mem_models R⟩)
  · intro generated model hosted
    have entailed : pair ∈ theoryOf equates (models equates R) := by
      rw [consequences_equations]
      exact generated
    exact entailed hosted.2

/-- The standard model over a ground type: the denotation of terms as
functions of the environment. -/
def standardModel (Γ : List Ty) (A : Ty) (Ground : Type) : Σ Y : Type, Term Γ A → Y :=
  ⟨Environment Ground Γ → A.denote Ground, fun t environment => t.denote environment⟩

/-- The standard models, over every ground type. -/
def standardModels (Γ : List Ty) (A : Ty) : Set (Σ Y : Type, Term Γ A → Y) :=
  range (standardModel Γ A)

/-- Every standard model satisfies the β-equations. -/
theorem standardModel_mem_models_beta (Ground : Type) :
    standardModel Γ A Ground ∈ models equates (betaEquations Γ A) :=
  fun _ reduces => funext fun environment => BetaStep.denote reduces environment

/-- The η-equation for a variable of function type. -/
def etaPair :
    Term [.arr .atom .atom] (.arr .atom .atom) × Term [.arr .atom .atom] (.arr .atom .atom) :=
  (etaVariable, etaExpansion)

/-- **The standard models validate η.** -/
theorem eta_mem_standardModels :
    etaPair ∈ consequencesIn equates (standardModels [.arr .atom .atom] (.arr .atom .atom))
      (betaEquations [.arr .atom .atom] (.arr .atom .atom)) := by
  rintro _ ⟨⟨Ground, rfl⟩, _⟩
  exact funext fun environment => eta_same_denotation environment

/-- **η is not a β-consequence.** -/
theorem eta_not_consequence :
    etaPair ∉
      theoryOf equates (models equates (betaEquations [.arr .atom .atom] (.arr .atom .atom))) := by
  rw [consequences_beta]
  exact eta_not_betaConvertible

/-- **Control: restricting to the standard models gains η**, so they do not host
the β-theory faithfully. -/
theorem standardModels_not_hostsFaithfully :
    ¬ HostsFaithfully equates (standardModels [.arr .atom .atom] (.arr .atom .atom))
      (betaEquations [.arr .atom .atom] (.arr .atom .atom)) := fun faithful =>
  eta_not_consequence (faithful ▸ eta_mem_standardModels)

/-- Restriction transfers theorems forward: every β-consequence holds in the
standard models. -/
theorem beta_consequences_subset_standard :
    consequencesIn equates univ (betaEquations Γ A) ⊆
      consequencesIn equates (standardModels Γ A) (betaEquations Γ A) :=
  (restrict_transfer (subset_univ _) _).1

/-! ### Restriction of the candidate's programs to the slice -/

section Programs

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
open ExecutableModel
open Presentation.TypedEquality.StrongNormalization (SN Reduces)

/-- The slice: raw terms of the candidate that are erasures of simple terms in
the context `Γ`. -/
def sliceTerms (Γ : List Ty) : Set (Presentation.Tower.Tm Γ.length) :=
  {t | ∃ (A : Ty) (s : Term Γ A), TowerDTT.eraseTerm s = t}

/-- The strongly normalizing raw terms of the executable package. -/
def snTerms (n : ℕ) : Set (Presentation.Tower.Tm n) :=
  {t | SN CodeModel.objectRules t}

/-- **Restricting to the slice gains strong normalization**: every program of
the slice satisfies it. -/
theorem slice_gains_sn :
    snTerms Γ.length ∈ consequencesIn predicateSat (sliceTerms Γ) ∅ := by
  rintro _ ⟨⟨A, s, rfl⟩, _⟩
  exact (simple_sn s).1

/-- Half of the self-application. -/
def omegaHalf : Presentation.Tower.Tm 0 :=
  .lam (.app (.var 0) (.var 0))

/-- The self-application `Ω`. -/
def omega : Presentation.Tower.Tm 0 :=
  .app omegaHalf omegaHalf

/-- `Ω` reduces to itself in every rule package. -/
theorem omega_reduces (R : Presentation.Rules Presentation.Tower.Head) :
    Reduces R omega omega :=
  Presentation.StepCore.betaPi _ omegaHalf

/-- A relation with a loop at `x` is not accessible at `x`. -/
theorem not_acc_of_loop {α : Type*} {r : α → α → Prop} {x : α} (loop : r x x) : ¬ Acc r x := by
  intro accessible
  revert loop
  induction accessible with
  | intro y _ ih => exact fun loopAt => ih y loopAt loopAt

/-- **`Ω` is not strongly normalizing.** -/
theorem omega_not_sn : omega ∉ snTerms 0 :=
  not_acc_of_loop (r := fun u t => Reduces CodeModel.objectRules t u) (omega_reduces _)

/-- Strong normalization is not a theorem of all raw programs. -/
theorem sn_not_valid : snTerms 0 ∉ consequencesIn predicateSat univ ∅ :=
  fun valid => omega_not_sn (valid ⟨mem_univ omega, fun _ member => member.elim⟩)

/-- **Control: restricting the candidate's raw programs to the slice is not
conservative.** -/
theorem slice_not_conservative :
    consequencesIn predicateSat (sliceTerms []) ∅ ≠ consequencesIn predicateSat univ ∅ :=
  fun equal => sn_not_valid (equal ▸ slice_gains_sn)

/-- **Positive: the slice hosts its own membership faithfully.** -/
theorem slice_hostsFaithfully_membership :
    HostsFaithfully predicateSat (sliceTerms Γ) {sliceTerms Γ} := by
  apply Subset.antisymm
  · intro S validated t model
    exact validated ⟨model rfl, model⟩
  · exact fun S entailed t hosted => entailed hosted.2

end Programs

/-! ### Identification -/

/-- **Control: identifying by η is not conservative over β.** -/
theorem carve_eta_not_conservative :
    consequencesIn equates (carve equates univ {etaPair})
        (betaEquations [.arr .atom .atom] (.arr .atom .atom)) ≠
      consequencesIn equates univ (betaEquations [.arr .atom .atom] (.arr .atom .atom)) := by
  intro conservative
  have sub := (carve_conservative_iff univ {etaPair} _).mp conservative (mem_singleton etaPair)
  rw [consequencesIn_univ] at sub
  exact eta_not_consequence sub

/-- **Identifying by a β-derivable equation is conservative.** -/
theorem carve_derivable_conservative :
    consequencesIn equates
        (carve equates univ
          {(ErasureBoundary.discardAtomicIdentity, ErasureBoundary.discardFunctionIdentity)})
        (betaEquations [] (.arr .atom .atom)) =
      consequencesIn equates univ (betaEquations [] (.arr .atom .atom)) := by
  apply (carve_conservative_iff univ _ _).mpr
  rintro _ rfl
  rw [consequencesIn_univ, consequences_beta]
  exact discarded_identities_convert

/-! ## The program scope: forgetting to βη -/

/-- The β observer. -/
abbrev betaObserver (Γ : List Ty) (A : Ty) : Setoid (Term Γ A) :=
  betaSetoid Γ A

/-- The βη observer. -/
abbrev betaEtaObserver (Γ : List Ty) (A : Ty) : Setoid (Term Γ A) :=
  Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.termSetoid Γ A

/-- **Forgetting from β to βη**: the βη observer is coarser. -/
theorem beta_le_betaEta : betaObserver Γ A ≤ betaEtaObserver Γ A :=
  fun _ _ converts =>
    Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.Conv.ofBetaConv converts

/-- Every βη-equation holds in every function space. -/
theorem betaEtaEquation_denote {Ground : Type} :
    ∀ {Γ : List Ty} {A : Ty} {left right : Term Γ A},
      Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.Equation left right →
        ∀ environment : Environment Ground Γ,
          left.denote environment = right.denote environment
  | _, _, _, _, .beta body argument, environment =>
      BetaClaim.shallowValid ⟨body, argument⟩ environment
  | _, _, _, _, .eta f, environment => by
      funext value
      change (f.rename weakening).denote (environment.extend value) value =
        f.denote environment value
      rw [Term.denote_rename]
      rfl
  | _, _, _, _, .lam inner, environment =>
      funext fun value => betaEtaEquation_denote inner (environment.extend value)
  | _, _, _, _, .appLeft inner, environment =>
      congrFun (betaEtaEquation_denote inner environment) _
  | _, _, _, _, .appRight inner, environment =>
      congrArg _ (betaEtaEquation_denote inner environment)

/-- **The denotation descends to βη classes.** -/
theorem denote_descends_betaEta (Ground : Type) :
    Factors (Quotient.mk (betaEtaObserver Γ A)) fun t (environment : Environment Ground Γ) =>
      t.denote environment := by
  refine (function_descends_iff (betaEtaObserver Γ A) _).mpr fun left right related => ?_
  funext environment
  induction related with
  | rel _ _ equation => exact betaEtaEquation_denote equation environment
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- The β-normal form computed by the fragment's normalization. -/
noncomputable def normalForm (t : Term Γ A) : Term Γ A :=
  (Normalization.normalize t).normalForm

/-- **The β-normal form descends to β classes.** -/
theorem normalForm_descends_beta : Factors (Quotient.mk (betaObserver Γ A)) normalForm :=
  (function_descends_iff (betaObserver Γ A) normalForm).mpr fun left right converts =>
    (normalize_eq_iff_betaConv left right).mpr converts

theorem etaVariable_normal : Normal etaVariable :=
  Normal.neutral (.var .zero)

theorem etaExpansion_normal : Normal etaExpansion :=
  Normal.lam (.neutral (.app (.var (.succ .zero)) (.neutral (.var .zero))))

theorem normalForm_etaVariable : normalForm etaVariable = etaVariable :=
  Normalization.normalize_of_irreducible _ etaVariable_normal.no_betaStep

theorem normalForm_etaExpansion : normalForm etaExpansion = etaExpansion :=
  Normalization.normalize_of_irreducible _ etaExpansion_normal.no_betaStep

/-- The η pair is βη-related. -/
theorem eta_related : betaEtaObserver _ _ etaExpansion etaVariable :=
  Relation.EqvGen.rel _ _
    (show Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.Equation etaExpansion
        etaVariable from
      Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient.Equation.eta (Γ := [.arr .atom .atom])
        (A := .atom) (B := .atom) (.var .zero))

/-- **Control: the β-normal form does not descend to βη classes.** -/
theorem normalForm_not_descends_betaEta :
    ¬ Factors (Quotient.mk (betaEtaObserver [.arr .atom .atom] (.arr .atom .atom))) normalForm :=
  NonTrivialFiber.not_factors
    ⟨etaExpansion, etaVariable, Quotient.sound eta_related, by
      rw [normalForm_etaExpansion, normalForm_etaVariable]
      intro equal
      cases equal⟩

/-- The predicate "has this β-normal form". -/
def normalFormPredicate (target : Term Γ A) : Set (Term Γ A) :=
  {t | normalForm t = target}

/-- **The β observer can evaluate the normal-form predicate.** -/
theorem normalFormPredicate_observable_beta (target : Term Γ A) :
    normalFormPredicate target ∈ observable predicateSat (betaObserver Γ A) := by
  intro left right converts
  change (Normalization.normalize left).normalForm = target ↔
    (Normalization.normalize right).normalForm = target
  rw [(normalize_eq_iff_betaConv left right).mpr converts]

/-- **Control: the βη observer cannot evaluate it.** -/
theorem normalFormPredicate_not_observable_betaEta :
    normalFormPredicate etaVariable ∉
      observable predicateSat (betaEtaObserver [.arr .atom .atom] (.arr .atom .atom)) := by
  intro visible
  have transfer := (visible (Relation.EqvGen.symm _ _ eta_related :
    betaEtaObserver _ _ etaVariable etaExpansion)).mp
  have atExpansion : normalForm etaExpansion = etaVariable :=
    transfer normalForm_etaVariable
  rw [normalForm_etaExpansion] at atExpansion
  cases atExpansion

end Mettapedia.GSLT.Scope.SimpleFragment
