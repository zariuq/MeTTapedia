import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Controls

/-!
# Eta and the program's conversion

The program's conversion has no eta rule.  A variable function `h` and its
expansion `λ e. h e` are different terms without computation steps, so they are
not convertible, and reflexivity at `h` is not evidence that they are equal.

Eta cannot be added by comparing normal forms.  Take any equivalence that
contains the program's conversion, relates a variable function to its
expansion, and is closed under substitution.  Instantiating the variable at the
partial application `keepCert num eqAt zero` relates it to
`λ e. keepCert num eqAt zero e`, whose body computes by the equation of
`keepCert`, so the equivalence relates `keepCert num eqAt zero` to
`λ e. pair zero e`.  These two are different terms without steps, and eta
contraction leaves both unchanged.

So a checker that decides equality by comparing eta-contracted normal forms
relates a variable `h` to `λ e. h e` but not `keepCert num eqAt zero` to its
expansion: its equality is not closed under substitution.  A definition checked
through eta at an open argument then has instances that the same checker
rejects.  If eta is wanted, it belongs to a conversion directed by types, which
expands a function at its dependent-product type before comparing and so does
identify `keepCert num eqAt zero` with `λ e. pair zero e`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.EtaConversion

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence
open Presentation.ConstructorSystem (Normal)
open SetProfile (zeroNative)
open CertifiedTransformProgram.Package CertifiedTransformProgram.Confluence
open CertifiedTransformProgram.Preservation
open CertifiedTransformProgram.Controls (no_root numeral_normal)

/-! ## Eta redexes -/

/-- `λ x. f x`, with `x` not free in `f`. -/
def EtaRedex {n : Nat} (term : Tower.Tm n) : Prop :=
  ∃ function : Tower.Tm n, term = .lam (.app (rename wk function) (.var 0))

/-- `λ e. h e` for the variable function `h`. -/
abbrev expansion : Tower.Tm 1 := .lam (.app (.var 1) (.var 0))

theorem expansion_etaRedex : EtaRedex expansion := ⟨.var 0, rfl⟩

/-- `keepCert num eqAt zero`, awaiting its evidence. -/
abbrev keepPartial {n : Nat} : Tower.Tm n :=
  .app (.app (.app (.const keepName) numT) (.const eqAtName)) zeroNative

/-- Its expansion with the body computed, `λ e. pair zero e`. -/
abbrev keepExpanded {n : Nat} : Tower.Tm n := .lam (.pair zeroNative (.var 0))

theorem keepPartial_not_etaRedex {n : Nat} : ¬ EtaRedex (keepPartial : Tower.Tm n) := by
  rintro ⟨_, shape⟩
  cases shape

theorem keepExpanded_not_etaRedex {n : Nat} : ¬ EtaRedex (keepExpanded : Tower.Tm n) := by
  rintro ⟨_, shape⟩
  cases shape

/-! ## Terms without steps -/

/-- In every program defined by constructor patterns, the expansion of a
variable function has no step. -/
theorem expansion_normal {rules : Rules Tower.Head}
    (equations : Presentation.ConstructorSystem.ConstructorPresentation rules) :
    Normal rules expansion := by
  intro target step
  cases step with
  | root rootStep => exact equations.no_root_of_spineHead rootStep rfl
  | congLam inner =>
      exact Normal.app (equations.normal_var 1) (equations.normal_var 0)
        (fun _ equal => by cases equal)
        (fun rootStep => equations.no_root_of_spineHead rootStep rfl) inner

theorem keepPartial_normal {n : Nat} : Normal linearRules (keepPartial : Tower.Tm n) :=
  Normal.app
    (Normal.app
      (Normal.app (Normal.const _ (fun step => no_root step rfl rfl rfl (fun _ => rfl)))
        (Normal.const _ (fun step => no_root step rfl rfl rfl (fun _ => rfl)))
        (fun _ equal => by cases equal)
        (fun step => no_root step rfl rfl rfl (fun _ => rfl)))
      (Normal.const _ (fun step => no_root step rfl rfl rfl (fun _ => rfl)))
      (fun _ equal => by cases equal)
      (fun step => no_root step rfl rfl rfl (fun _ => rfl)))
    (numeral_normal 0) (fun _ equal => by cases equal)
    (fun step => no_root step rfl rfl rfl (fun _ => rfl))

theorem keepExpanded_normal {n : Nat} : Normal linearRules (keepExpanded : Tower.Tm n) := by
  intro target step
  cases step with
  | root rootStep => exact linearConstructors.no_root_of_spineHead rootStep rfl
  | congLam inner =>
      cases inner with
      | root rootStep => exact linearConstructors.no_root_of_spineHead rootStep rfl
      | congPairFst inner => exact numeral_normal 0 inner
      | congPairSnd inner => exact linearConstructors.normal_var 0 inner

/-! ## No eta in the program's conversion -/

/-- In every program defined by constructor patterns, a variable function is
not convertible to its expansion. -/
theorem expansion_not_converted {rules : Rules Tower.Head}
    (equations : Presentation.ConstructorSystem.ConstructorPresentation rules) :
    ¬ Conv rules.headEq (.var 0 : Tower.Tm 1) expansion rules.computation := by
  intro conversion
  have same := equations.eq_of_normal (equations.normal_var 0) (expansion_normal equations) conversion
  cases same

/-- In every host defined by constructor patterns, reflexivity at a variable
function `h : num → num` is not evidence for `Id (num → num) h (λ e. h e)`. -/
theorem eta_not_typed (host : Host)
    (equations : Presentation.ConstructorSystem.ConstructorPresentation host.rules) :
    ¬ Typing host.rules (.snoc .nil (.pi numT numT)) (.refl (.var 0))
      (.id (.pi numT numT) (.var 0) expansion) := by
  intro typed
  obtain ⟨_, toEndpoint⟩ := host.refl_endpoints typed
  exact expansion_not_converted equations toEndpoint

/-- In particular in the linearized program. -/
theorem eta_not_typed_linear :
    ¬ Typing linearRules (.snoc .nil (.pi numT numT)) (.refl (.var 0))
      (.id (.pi numT numT) (.var 0) expansion) :=
  eta_not_typed linearHost linearConstructors

/-- `keepCert num eqAt zero` and `λ e. pair zero e` are not convertible. -/
theorem keep_apart :
    ¬ Conv linearRules.headEq (keepPartial : Tower.Tm 0) keepExpanded linearRules.computation := by
  intro conversion
  have same := linearConstructors.eq_of_normal keepPartial_normal keepExpanded_normal conversion
  cases same

/-- Under the binder, the expansion of `keepCert num eqAt zero` computes by the
equation of `keepCert`. -/
theorem keep_expansion_runs :
    StepStar linearRules (.lam (.app (rename wk (keepPartial : Tower.Tm 0)) (.var 0)))
      keepExpanded :=
  .single (.congLam (.root (linearSchema_sound
    (.package (List.getElem_mem (l := linearEquations) (n := 5) (by decide)))
    (Execution.patternValues ![numT, .const eqAtName, zeroNative, .var 0]))))

/-! ## Eta by comparison of normal forms is not substitutive -/

/-- Every equivalence that contains the program's conversion, relates a variable
function to its expansion and is closed under substitution relates
`keepCert num eqAt zero` to `λ e. pair zero e`. -/
theorem eta_identifies
    (E : ∀ {n : Nat}, Tower.Tm n → Tower.Tm n → Prop)
    (contains : ∀ {n : Nat} {left right : Tower.Tm n},
      Conv linearRules.headEq left right linearRules.computation → E left right)
    (trans : ∀ {n : Nat} {first second third : Tower.Tm n},
      E first second → E second third → E first third)
    (substitutive : ∀ {n m : Nat} (σ : Sub Tower.Head n m) {left right : Tower.Tm n},
      E left right → E (subst σ left) (subst σ right))
    (eta : E (.var 0 : Tower.Tm 1) expansion) :
    E (keepPartial : Tower.Tm 0) keepExpanded :=
  trans (substitutive (fun _ => keepPartial) eta)
    (contains (stepStar_implies_conv keep_expansion_runs))

/-- So no equivalence with those properties keeps apart the two terms, although
both are without steps and eta contraction leaves both unchanged. -/
theorem eta_not_separating
    (E : ∀ {n : Nat}, Tower.Tm n → Tower.Tm n → Prop)
    (contains : ∀ {n : Nat} {left right : Tower.Tm n},
      Conv linearRules.headEq left right linearRules.computation → E left right)
    (trans : ∀ {n : Nat} {first second third : Tower.Tm n},
      E first second → E second third → E first third)
    (substitutive : ∀ {n m : Nat} (σ : Sub Tower.Head n m) {left right : Tower.Tm n},
      E left right → E (subst σ left) (subst σ right))
    (eta : E (.var 0 : Tower.Tm 1) expansion)
    (separates : ¬ E (keepPartial : Tower.Tm 0) keepExpanded) : False :=
  separates (eta_identifies E contains trans substitutive eta)

#print axioms expansion_not_converted
#print axioms eta_not_typed
#print axioms eta_not_typed_linear
#print axioms keep_apart
#print axioms keep_expansion_runs
#print axioms eta_identifies
#print axioms eta_not_separating

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.EtaConversion
