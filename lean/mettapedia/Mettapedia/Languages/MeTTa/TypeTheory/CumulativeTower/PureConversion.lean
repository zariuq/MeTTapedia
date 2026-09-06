import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AlgebraicParallelSubstitution
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveBeta

/-!
# Conversion coherence for presentations without declared root equations

The existing algebraic parallel relation, specialized to no authored root
equations, has a complete development whenever head equality is symmetric.
This proves Church--Rosser for the original full presentation conversion:
Pi, Sigma, identity types, opaque declaration constants, binders,
applications and projections are all retained. Universe-head identities are
not erased.

The actual `Tower.rules` package satisfies these hypotheses. Its Pi
conversion boundary and formation-sensitive root beta preservation therefore
need no additional conversion assumption. Declared delta/iota extensions
are not covered by the empty-root hypothesis. Church--Rosser is not strong
normalization, and this result neither chooses a runtime evaluation strategy
nor adopts this rule package as a global profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PureConversion

open AlgebraicParallel ConversionCoherence

variable {Head : Type} {headEq : Head → Head → Prop} {n : Nat}

/-- The schema family for a rule package with no declaration-specific root
equations. Built-in beta and projection equations remain in `ParRed`. -/
def noSchemas : AlgebraicSchema.SchemaFamily Head := fun _ _ => False

/-- Exact schema presentation of an empty declaration-specific computation. -/
def emptySchemaPresentation (rules : Rules Head)
    (empty : rules.computation = RootComputation.empty) : SchemaPresentation rules where
  schema := noSchemas
  sound := by
    intro arity ambient left right impossible substitution
    exact impossible.elim
  cover := by
    intro n source target impossible
    rw [empty] at impossible
    exact impossible.elim

private theorem lam_components_aux {source target : Tm Head n}
    (reduction : ParRed headEq noSchemas source target) :
    ∀ {body : Tm Head (n + 1)}, source = .lam body →
      ∃ body', target = .lam body' ∧ ParRed headEq noSchemas body body' := by
  cases reduction with
  | lam inner =>
      intro body equality
      cases equality
      exact ⟨_, rfl, inner⟩
  | algebraic impossible _ _ _ => exact impossible.elim
  | _ => intro body equality; cases equality

private theorem lam_components {body : Tm Head (n + 1)} {target : Tm Head n}
    (reduction : ParRed headEq noSchemas (.lam body) target) :
    ∃ body', target = .lam body' ∧ ParRed headEq noSchemas body body' :=
  lam_components_aux reduction rfl

private theorem pair_components_aux {source target : Tm Head n}
    (reduction : ParRed headEq noSchemas source target) :
    ∀ {first second : Tm Head n}, source = .pair first second →
      ∃ first' second', target = .pair first' second' ∧
        ParRed headEq noSchemas first first' ∧ ParRed headEq noSchemas second second' := by
  cases reduction with
  | pair left right =>
      intro first second equality
      cases equality
      exact ⟨_, _, rfl, left, right⟩
  | algebraic impossible _ _ _ => exact impossible.elim
  | _ => intro first second equality; cases equality

private theorem pair_components {first second target : Tm Head n}
    (reduction : ParRed headEq noSchemas (.pair first second) target) :
    ∃ first' second', target = .pair first' second' ∧
      ParRed headEq noSchemas first first' ∧ ParRed headEq noSchemas second second' :=
  pair_components_aux reduction rfl

/-- Contract every redex visible in the input while recursively developing
its components. Newly exposed redexes need not be contracted. -/
def develop {n : Nat} : Tm Head n → Tm Head n
  | .var index => .var index
  | .const name => .const name
  | .head value => .head value
  | .pi domain codomain => .pi (develop domain) (develop codomain)
  | .sigma domain codomain => .sigma (develop domain) (develop codomain)
  | .id carrier left right => .id (develop carrier) (develop left) (develop right)
  | .lam body => .lam (develop body)
  | .app (.lam body) argument => inst0 (develop argument) (develop body)
  | .app function argument => .app (develop function) (develop argument)
  | .pair first second => .pair (develop first) (develop second)
  | .fst (.pair first _) => develop first
  | .fst pair => .fst (develop pair)
  | .snd (.pair _ second) => develop second
  | .snd pair => .snd (develop pair)
  | .refl term => .refl (develop term)

/-- Every parallel reduct reaches the same complete development, retaining
the actual head identities through the symmetric head relation. -/
theorem par_develop (symmetric : Std.Symm headEq) {n : Nat} {source target : Tm Head n} :
    ParRed headEq noSchemas source target →
      ParRed headEq noSchemas target (develop source)
  | .var index => .var index
  | .const name => .const name
  | .head value => .head value
  | .headRel equality => .headRel (symmetric.symm _ _ equality)
  | .pi domain codomain =>
      .pi (par_develop symmetric domain) (par_develop symmetric codomain)
  | .sigma domain codomain =>
      .sigma (par_develop symmetric domain) (par_develop symmetric codomain)
  | .id carrier left right =>
      .id (par_develop symmetric carrier) (par_develop symmetric left)
        (par_develop symmetric right)
  | .lam body => .lam (par_develop symmetric body)
  | @ParRed.app _ _ _ _ function function' argument argument' functionStep argumentStep => by
      have functionDevelop := par_develop symmetric functionStep
      have argumentDevelop := par_develop symmetric argumentStep
      cases function with
      | lam body =>
          obtain ⟨body', rfl, _⟩ := lam_components functionStep
          obtain ⟨body'', equality, bodyDevelop⟩ := lam_components functionDevelop
          have same : body'' = develop body := by
            exact (Tm.lam.inj equality).symm
          subst body''
          exact .betaPi bodyDevelop argumentDevelop
      | _ => exact .app functionDevelop argumentDevelop
  | .pair first second =>
      .pair (par_develop symmetric first) (par_develop symmetric second)
  | @ParRed.fst _ _ _ _ pair pair' pairStep => by
      have pairDevelop := par_develop symmetric pairStep
      cases pair with
      | pair first second =>
          obtain ⟨first', second', rfl, _, _⟩ := pair_components pairStep
          obtain ⟨first'', second'', equality, firstDevelop, secondDevelop⟩ :=
            pair_components pairDevelop
          obtain ⟨rfl, rfl⟩ := Tm.pair.inj equality
          exact .betaSigmaFst firstDevelop secondDevelop
      | _ => exact .fst pairDevelop
  | @ParRed.snd _ _ _ _ pair pair' pairStep => by
      have pairDevelop := par_develop symmetric pairStep
      cases pair with
      | pair first second =>
          obtain ⟨first', second', rfl, _, _⟩ := pair_components pairStep
          obtain ⟨first'', second'', equality, firstDevelop, secondDevelop⟩ :=
            pair_components pairDevelop
          obtain ⟨rfl, rfl⟩ := Tm.pair.inj equality
          exact .betaSigmaSnd firstDevelop secondDevelop
      | _ => exact .snd pairDevelop
  | .refl term => .refl (par_develop symmetric term)
  | .betaPi body argument =>
      par_inst0 (par_develop symmetric argument) (par_develop symmetric body)
  | .betaSigmaFst first _ => by
      simpa only [develop] using par_develop symmetric first
  | .betaSigmaSnd _ second => by
      simpa only [develop] using par_develop symmetric second
  | .algebraic impossible _ _ _ => impossible.elim

/-- The complete-development witness is proved for the selected schema
presentation, rather than required as an additional assumption. -/
def completeDevelopment (rules : Rules Head)
    (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) :
    CompleteDevelopment (emptySchemaPresentation rules empty) where
  develop := develop
  reaches := par_develop symmetric

/-- Full raw conversion has Church--Rosser for this exact root-free rule
package; no typing or normalization hypothesis is used. -/
theorem churchRosser (rules : Rules Head)
    (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) : ChurchRosser rules :=
  churchRosserOfCompleteDevelopment (emptySchemaPresentation rules empty)
    (completeDevelopment rules empty symmetric)

/-- Empty declared computation cannot rewrite a Pi or a head at its root. -/
def rootPiHeadNeutral (rules : Rules Head)
    (empty : rules.computation = RootComputation.empty) : RootPiHeadNeutral rules where
  pi := by rw [empty]; exact not_false
  head := by rw [empty]; exact not_false

/-- Exact component injectivity and Pi/head separation for the original
conversion relation, without erasing or identifying its heads. -/
def piConversionBoundary (rules : Rules Head)
    (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) : PiConversionBoundary rules :=
  piConversionBoundaryOfChurchRosser (rootPiHeadNeutral rules empty)
    (churchRosser rules empty symmetric)

end PureConversion

namespace Tower

theorem headEq_symmetric : Std.Symm HeadEq := by
  constructor
  intro left right equality
  cases left <;> cases right <;> simp only [HeadEq] at equality ⊢
  intro valuation
  exact (equality valuation).symm

/-- Church--Rosser for all constructors of the actual Tower rule package. -/
theorem churchRosser : ConversionCoherence.ChurchRosser rules :=
  PureConversion.churchRosser rules rfl headEq_symmetric

/-- The actual Tower package satisfies its Pi-conversion qualification. -/
def piConversionBoundary : Presentation.PiConversionBoundary rules :=
  PureConversion.piConversionBoundary rules rfl headEq_symmetric

end Tower

namespace FormationSensitive

variable {n : Nat}

/-- Root beta preservation for the actual Tower package, with the conversion
boundary and universe regularity discharged by their proved instances. -/
theorem Typing.betaPi_tower {Γ : Tower.Ctx n} {body : Tower.Tm (n + 1)}
    {argument displayed : Tower.Tm n}
    (typing : Typing Tower.rules Γ (.app (.lam body) argument) displayed)
    (context : ContextFormation Tower.rules Γ) :
    Typing Tower.rules Γ (inst0 argument body) displayed :=
  typing.betaPi towerUniverseRegularity Tower.piConversionBoundary context

theorem Judgment.betaPi_tower {Γ : Tower.Ctx n} {body : Tower.Tm (n + 1)}
    {argument displayed : Tower.Tm n}
    (judgment : Judgment Tower.rules Γ (.app (.lam body) argument) displayed) :
    Judgment Tower.rules Γ (inst0 argument body) displayed :=
  ⟨judgment.context, judgment.typing.betaPi_tower judgment.context⟩

namespace PureConversionExamples

/-- A genuine overlap between beta contraction and semantic universe-head
equality has a common reduct, with every displayed arrow an actual step. -/
theorem beta_head_peak (level : LevelExpr) :
    let redundant : Tower.Tm n := sortTm (.max level level)
    let canonical : Tower.Tm n := sortTm level
    let identity : Tower.Tm n := .lam (.var 0)
    Step Tower.HeadEq (.app identity redundant) redundant ∧
      Step Tower.HeadEq (.app identity redundant) (.app identity canonical) ∧
      Step Tower.HeadEq redundant canonical ∧
      Step Tower.HeadEq (.app identity canonical) canonical := by
  have equality : Tower.HeadEq (.sort (.max level level)) (.sort level) := by
    intro valuation
    exact Nat.max_self _
  exact ⟨.betaPi _ _, .congAppArg (.head equality), .head equality, .betaPi _ _⟩

/-- The genuine type-dependent specialization now uses no assumed
Pi-conversion qualification. -/
theorem polymorphic_identity_beta {Γ : Tower.Ctx n} {A : Tower.Tm n}
    {level : LevelExpr} (context : ContextFormation Tower.rules Γ)
    (formed : Typing Tower.rules Γ A (sortTm level)) :
    Typing Tower.rules Γ (.lam (.var 0)) (.pi A (rename wk A)) :=
  BetaExamples.polymorphic_identity_beta context formed Tower.piConversionBoundary

/-- Non-normal Pi components are allowed: no term of the full Tower syntax
can make an outer Pi convertible to the opaque ground head. -/
theorem pi_ne_ground (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1)) :
    ¬ Conv Tower.HeadEq (.pi domain codomain) (.head .legacyGround) :=
  Tower.piConversionBoundary.headDisjoint

end PureConversionExamples
end FormationSensitive

#print axioms AlgebraicParallel.par_substitute
#print axioms PureConversion.par_develop
#print axioms PureConversion.churchRosser
#print axioms PureConversion.piConversionBoundary
#print axioms Tower.churchRosser
#print axioms Tower.piConversionBoundary
#print axioms FormationSensitive.Typing.betaPi_tower
#print axioms FormationSensitive.Judgment.betaPi_tower
#print axioms FormationSensitive.PureConversionExamples.beta_head_peak
#print axioms FormationSensitive.PureConversionExamples.polymorphic_identity_beta
#print axioms FormationSensitive.PureConversionExamples.pi_ne_ground

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
