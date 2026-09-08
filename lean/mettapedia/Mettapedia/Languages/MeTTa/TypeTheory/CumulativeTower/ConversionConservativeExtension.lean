import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SigmaConversionBoundary

/-!
# Conversion-conservative extensions of a reduction presentation

An auxiliary reduction may add shortcuts that are already convertible in the
authored presentation. Local root inclusion and root soundness imply equality
of the entire contextual conversion relations. They do not imply that an
auxiliary step is a forward run of the authored presentation.

Consequently, constructor injectivity proved using an auxiliary Church--Rosser
argument transfers to the authored conversion without claiming Church--Rosser
for its original oriented reduction. Typing rules and runtime evaluation are
not changed by this construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

variable {Head : Type} {n : Nat} {source target : Rules Head}

/-- Primitive obligations for an auxiliary reduction with exactly the authored
conversion theory. No law concerning whole conversion paths is assumed. -/
structure ConversionConservativeExtension (source target : Rules Head) : Prop where
  headEq_eq : source.headEq = target.headEq
  root_inclusion {n : Nat} {left right : Tm Head n} :
    source.computation.step left right → target.computation.step left right
  root_sound {n : Nat} {left right : Tm Head n} :
    target.computation.step left right →
      Conv source.headEq left right source.computation

namespace ConversionConservativeExtension

/-- Every authored contextual step remains an auxiliary contextual step. -/
theorem step_inclusion (extension : ConversionConservativeExtension source target)
    {left right : Tm Head n}
    (step : Step source.headEq left right source.computation) :
    Step target.headEq left right target.computation := by
  induction step with
  | betaPi body argument => exact .betaPi body argument
  | betaSigmaFst first second => exact .betaSigmaFst first second
  | betaSigmaSnd first second => exact .betaSigmaSnd first second
  | head equality => exact .head (extension.headEq_eq ▸ equality)
  | root equation => exact .root (extension.root_inclusion equation)
  | congPiDom _ ih => exact .congPiDom ih
  | congPiCod _ ih => exact .congPiCod ih
  | congSigmaDom _ ih => exact .congSigmaDom ih
  | congSigmaCod _ ih => exact .congSigmaCod ih
  | congIdTy _ ih => exact .congIdTy ih
  | congIdLeft _ ih => exact .congIdLeft ih
  | congIdRight _ ih => exact .congIdRight ih
  | congLam _ ih => exact .congLam ih
  | congAppFun _ ih => exact .congAppFun ih
  | congAppArg _ ih => exact .congAppArg ih
  | congPairFst _ ih => exact .congPairFst ih
  | congPairSnd _ ih => exact .congPairSnd ih
  | congFst _ ih => exact .congFst ih
  | congSnd _ ih => exact .congSnd ih
  | congRefl _ ih => exact .congRefl ih

/-- Each auxiliary contextual step is already an authored conversion. The
conclusion deliberately permits reversal of authored steps. -/
theorem step_sound (extension : ConversionConservativeExtension source target)
    {left right : Tm Head n}
    (step : Step target.headEq left right target.computation) :
    Conv source.headEq left right source.computation := by
  induction step with
  | betaPi body argument => exact .rel _ _ (.betaPi body argument)
  | betaSigmaFst first second => exact .rel _ _ (.betaSigmaFst first second)
  | betaSigmaSnd first second => exact .rel _ _ (.betaSigmaSnd first second)
  | head equality => exact .rel _ _ (.head (extension.headEq_eq.symm ▸ equality))
  | root equation => exact extension.root_sound equation
  | congPiDom _ ih => exact Conv.congPi ih (.refl _)
  | congPiCod _ ih => exact Conv.congPi (.refl _) ih
  | congSigmaDom _ ih => exact Conv.congSigma ih (.refl _)
  | congSigmaCod _ ih => exact Conv.congSigma (.refl _) ih
  | congIdTy _ ih => exact Conv.congId ih (.refl _) (.refl _)
  | congIdLeft _ ih => exact Conv.congId (.refl _) ih (.refl _)
  | congIdRight _ ih => exact Conv.congId (.refl _) (.refl _) ih
  | congLam _ ih => exact Conv.congLam ih
  | congAppFun _ ih => exact Conv.congApp ih (.refl _)
  | congAppArg _ ih => exact Conv.congApp (.refl _) ih
  | congPairFst _ ih => exact Conv.congPair ih (.refl _)
  | congPairSnd _ ih => exact Conv.congPair (.refl _) ih
  | congFst _ ih => exact Conv.mapCompatible Tm.fst (fun h => .congFst h) ih
  | congSnd _ ih => exact Conv.mapCompatible Tm.snd (fun h => .congSnd h) ih
  | congRefl _ ih => exact Conv.mapCompatible Tm.refl (fun h => .congRefl h) ih

theorem conversion_forward (extension : ConversionConservativeExtension source target)
    {left right : Tm Head n}
    (conversion : Conv source.headEq left right source.computation) :
    Conv target.headEq left right target.computation := by
  induction conversion with
  | rel _ _ step => exact .rel _ _ (extension.step_inclusion step)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem conversion_backward (extension : ConversionConservativeExtension source target)
    {left right : Tm Head n}
    (conversion : Conv target.headEq left right target.computation) :
    Conv source.headEq left right source.computation := by
  induction conversion with
  | rel _ _ step => exact extension.step_sound step
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- Exact conversion equivalence on all open terms, not just formed inputs. -/
theorem conversion_iff (extension : ConversionConservativeExtension source target)
    (left right : Tm Head n) :
    Conv source.headEq left right source.computation ↔
      Conv target.headEq left right target.computation :=
  ⟨extension.conversion_forward, extension.conversion_backward⟩

/-- Auxiliary Pi injectivity and separation qualify the authored conversion. -/
def piConversionBoundary (extension : ConversionConservativeExtension source target)
    (boundary : PiConversionBoundary target) : PiConversionBoundary source where
  components := by
    intro n A A' B B' conversion
    obtain ⟨domains, codomains⟩ := boundary.components
      (extension.conversion_forward conversion)
    exact ⟨extension.conversion_backward domains, extension.conversion_backward codomains⟩
  headDisjoint := by
    intro n A B head conversion
    exact boundary.headDisjoint (extension.conversion_forward conversion)

/-- Auxiliary Sigma injectivity and separation qualify the authored conversion. -/
def sigmaConversionBoundary (extension : ConversionConservativeExtension source target)
    (boundary : SigmaConversionBoundary target) : SigmaConversionBoundary source where
  components := by
    intro n A A' B B' conversion
    obtain ⟨domains, codomains⟩ := boundary.components
      (extension.conversion_forward conversion)
    exact ⟨extension.conversion_backward domains, extension.conversion_backward codomains⟩
  headDisjoint := by
    intro n A B head conversion
    exact boundary.headDisjoint (extension.conversion_forward conversion)

/-- A Church--Rosser auxiliary reduction suffices for authored Pi conversion
qualification; authored Church--Rosser is not asserted. -/
def piConversionBoundaryOfChurchRosser
    (extension : ConversionConservativeExtension source target)
    (neutral : ConversionCoherence.RootPiHeadNeutral target)
    (churchRosser : ConversionCoherence.ChurchRosser target) :
    PiConversionBoundary source :=
  extension.piConversionBoundary
    (ConversionCoherence.piConversionBoundaryOfChurchRosser neutral churchRosser)

end ConversionConservativeExtension

namespace ConversionCoherence

/-- Root neutrality for dependent-pair types and universe heads. -/
structure RootSigmaHeadNeutral (rules : Rules Head) : Prop where
  sigma {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} {target : Tm Head n} :
    ¬ rules.computation.step (.sigma A B) target
  head {n : Nat} {source : Head} {target : Tm Head n} :
    ¬ rules.computation.step (.head source) target

private theorem sigma_step_decomp {R : Rules Head} (neutral : RootSigmaHeadNeutral R)
    {A : Tm Head n} {B : Tm Head (n + 1)} {target : Tm Head n}
    (step : Step R.headEq (.sigma A B) target R.computation) :
    ∃ A' B', target = .sigma A' B' ∧ StepStar R A A' ∧ StepStar R B B' := by
  cases step with
  | root equation => exact False.elim (neutral.sigma equation)
  | congSigmaDom inner => exact ⟨_, _, rfl, .tail .refl inner, .refl⟩
  | congSigmaCod inner => exact ⟨_, _, rfl, .refl, .tail .refl inner⟩

/-- Forward auxiliary reduction exposes every Sigma component path. -/
theorem sigma_stepStar_decomp {R : Rules Head} (neutral : RootSigmaHeadNeutral R)
    {A : Tm Head n} {B : Tm Head (n + 1)} {target : Tm Head n}
    (steps : StepStar R (.sigma A B) target) :
    ∃ A' B', target = .sigma A' B' ∧ StepStar R A A' ∧ StepStar R B B' := by
  induction steps with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | tail previous finalStep ih =>
      obtain ⟨A', B', rfl, first, second⟩ := ih
      obtain ⟨A'', B'', rfl, lastFirst, lastSecond⟩ := sigma_step_decomp neutral finalStep
      exact ⟨_, _, rfl, first.trans lastFirst, second.trans lastSecond⟩

private theorem sigma_head_stepStar_shape {R : Rules Head}
    (neutral : RootSigmaHeadNeutral R) {head : Head} {target : Tm Head n}
    (steps : StepStar R (.head head) target) : ∃ head', target = .head head' := by
  induction steps with
  | refl => exact ⟨_, rfl⟩
  | tail previous finalStep ih =>
      obtain ⟨head', rfl⟩ := ih
      cases finalStep with
      | head equality => exact ⟨_, rfl⟩
      | root equation => exact False.elim (neutral.head equation)

/-- Church--Rosser plus Sigma/head root neutrality yields the actual pair
conversion boundary, allowing arbitrary root rules elsewhere. -/
def sigmaConversionBoundaryOfChurchRosser {R : Rules Head}
    (neutral : RootSigmaHeadNeutral R) (churchRosser : ChurchRosser R) :
    SigmaConversionBoundary R where
  components := by
    intro n A A' B B' conversion
    obtain ⟨common, firstSteps, secondSteps⟩ := churchRosser conversion
    obtain ⟨firstA, firstB, firstShape, firstAPath, firstBPath⟩ :=
      sigma_stepStar_decomp neutral firstSteps
    obtain ⟨secondA, secondB, secondShape, secondAPath, secondBPath⟩ :=
      sigma_stepStar_decomp neutral secondSteps
    have equality := firstShape.symm.trans secondShape
    injection equality with domains codomains
    subst secondA
    subst secondB
    exact ⟨.trans _ _ _ (stepStar_implies_conv firstAPath)
      (.symm _ _ (stepStar_implies_conv secondAPath)),
      .trans _ _ _ (stepStar_implies_conv firstBPath)
        (.symm _ _ (stepStar_implies_conv secondBPath))⟩
  headDisjoint := by
    intro n A B head conversion
    obtain ⟨common, sigmaSteps, headSteps⟩ := churchRosser conversion
    obtain ⟨A', B', sigmaShape, _, _⟩ := sigma_stepStar_decomp neutral sigmaSteps
    obtain ⟨head', headShape⟩ := sigma_head_stepStar_shape neutral headSteps
    rw [sigmaShape] at headShape
    cases headShape

end ConversionCoherence

namespace ConversionConservativeExtension

def sigmaConversionBoundaryOfChurchRosser
    (extension : ConversionConservativeExtension source target)
    (neutral : ConversionCoherence.RootSigmaHeadNeutral target)
    (churchRosser : ConversionCoherence.ChurchRosser target) :
    SigmaConversionBoundary source :=
  extension.sigmaConversionBoundary
    (ConversionCoherence.sigmaConversionBoundaryOfChurchRosser neutral churchRosser)

/-- An auxiliary root that identifies a Pi with a head cannot be conversion
conservative over a source whose Pi/head separation has been proved. -/
theorem no_extension_of_pi_head_root (boundary : PiConversionBoundary source)
    {A : Tm Head n} {B : Tm Head (n + 1)} {head : Head}
    (collapse : target.computation.step (.pi A B) (.head head)) :
    ¬ ConversionConservativeExtension source target := by
  intro extension
  exact boundary.headDisjoint (extension.root_sound collapse)

end ConversionConservativeExtension

/-! ## Controls -/

namespace ConversionConservativeExtensionExamples

def doubleIdentity (term : Tm Head n) : Tm Head n :=
  .app (.lam (.var 0)) (.app (.lam (.var 0)) term)

/-- A genuine two-beta shortcut, not an arbitrary equation oracle. -/
inductive ShortcutStep : {n : Nat} → Tm Head n → Tm Head n → Prop where
  | doubleIdentity (term : Tm Head n) : ShortcutStep (doubleIdentity term) term

def shortcutRoot : RootComputation Head where
  step := ShortcutStep
  rename := by
    intro n m rho left right step
    cases step
    exact .doubleIdentity _
  substitute := by
    intro n m sigma left right step
    cases step
    exact .doubleIdentity _

def shortcutRules (R : Rules Head) : Rules Head :=
  { R with computation := shortcutRoot }

/-- The shortcut certificate is independently justified by the two authored
beta steps. Every rule package without declared root computation supports it. -/
def shortcutExtension (R : Rules Head) (empty : R.computation = RootComputation.empty) :
    ConversionConservativeExtension R (shortcutRules R) where
  headEq_eq := rfl
  root_inclusion := by
    intro n left right impossible
    rw [empty] at impossible
    exact impossible.elim
  root_sound := by
    intro n left right step
    cases step with
    | doubleIdentity =>
        exact .trans _ _ _ (.rel _ _ (.betaPi (.var 0) _))
          (.rel _ _ (.betaPi (.var 0) _))

/-- The added shortcut really is a new root step even though conversion is
unchanged for every term. -/
theorem shortcut_adds_root_without_adding_conversion (term : Tower.Tm n) :
    (shortcutRules Tower.rules).computation.step (doubleIdentity term) term ∧
      ¬ Tower.rules.computation.step (doubleIdentity term) term ∧
      (∀ left right : Tower.Tm n,
        Conv Tower.HeadEq left right ↔
          Conv Tower.HeadEq left right (shortcutRules Tower.rules).computation) :=
  ⟨.doubleIdentity term, not_false,
    (shortcutExtension Tower.rules rfl).conversion_iff⟩

end ConversionConservativeExtensionExamples

#print axioms ConversionConservativeExtension.step_inclusion
#print axioms ConversionConservativeExtension.step_sound
#print axioms ConversionConservativeExtension.conversion_iff
#print axioms ConversionConservativeExtension.piConversionBoundary
#print axioms ConversionConservativeExtension.sigmaConversionBoundary
#print axioms ConversionCoherence.sigma_stepStar_decomp
#print axioms ConversionCoherence.sigmaConversionBoundaryOfChurchRosser
#print axioms ConversionConservativeExtension.piConversionBoundaryOfChurchRosser
#print axioms ConversionConservativeExtension.sigmaConversionBoundaryOfChurchRosser
#print axioms ConversionConservativeExtension.no_extension_of_pi_head_root
#print axioms ConversionConservativeExtensionExamples.shortcutExtension
#print axioms ConversionConservativeExtensionExamples.shortcut_adds_root_without_adding_conversion

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
