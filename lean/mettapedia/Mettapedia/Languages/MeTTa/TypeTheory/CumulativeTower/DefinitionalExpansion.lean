import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ConstantExpansion
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PureConversion
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationSignature

/-!
# Conversion qualification by definitional expansion

Two local obligations qualify a constant expansion: each constant is convertible
to its selected closed body in the source, and each source root equation becomes
pure conversion after expansion. These primitive obligations yield preservation
and reflection of the entire contextual conversion relation, Pi injectivity,
Pi/head separation, and refined beta preservation.

The target retains the source's universe heads and their equality. It removes
only declared root computation. This is not an untyped erasure or a termination
claim; arbitrary recursive equations need not satisfy the obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ConstantExpansion

variable {Head : Type} {n : Nat} {R : Rules Head}

/-- The same presentation with no declaration-specific root equations. -/
def pureRules (R : Rules Head) : Rules Head :=
  { R with computation := RootComputation.empty }

/-- A qualification contains only certificates for constants and primitive
root equations, not a preservation theorem for arbitrary conversion paths. -/
structure Qualification (R : Rules Head) where
  bodies : Bodies Head
  constants : ∀ name, Conv R.headEq (.const name) (bodies name) R.computation
  roots {n : Nat} {left right : Tm Head n} : R.computation.step left right →
    Conv R.headEq (expand bodies left) (expand bodies right)

/-- Pure conversion remains available in every declaration package. -/
theorem include_pure {left right : Tm Head n}
    (conversion : Conv R.headEq left right) :
    Conv R.headEq left right R.computation := by
  simpa only [Tm.mapHead_id] using
    conversion.mapHead (fun head => head) (fun equality => equality)
      (targetRoot := R.computation) (by intro k a b impossible; exact impossible.elim)

/-- Expansion both preserves and reflects the full source conversion relation.
The reverse direction uses the separately certified meaning of each constant. -/
theorem Qualification.conversion_iff (qualification : Qualification R)
    (left right : Tm Head n) :
    Conv R.headEq left right R.computation ↔
      Conv R.headEq (expand qualification.bodies left)
        (expand qualification.bodies right) := by
  constructor
  · exact conv_expand qualification.bodies qualification.roots
  · intro conversion
    exact .trans _ _ _
      (term_conv_expand qualification.bodies qualification.constants left)
      (.trans _ _ _ (include_pure conversion)
        (.symm _ _
          (term_conv_expand qualification.bodies qualification.constants right)))

/-- No Pi injectivity or confluence premise about the source is required.
The previously proved pure conversion boundary supplies the target argument. -/
def Qualification.piConversionBoundary (qualification : Qualification R)
    (symmetric : Std.Symm R.headEq) : PiConversionBoundary R where
  components := by
    intro n A A' B B' conversion
    have expanded := (qualification.conversion_iff _ _).mp conversion
    have boundary := PureConversion.piConversionBoundary (pureRules R) rfl symmetric
    obtain ⟨domains, codomains⟩ := boundary.components expanded
    exact ⟨(qualification.conversion_iff _ _).mpr domains,
      (qualification.conversion_iff _ _).mpr codomains⟩
  headDisjoint := by
    intro n A B head conversion
    have expanded := (qualification.conversion_iff _ _).mp conversion
    exact (PureConversion.piConversionBoundary (pureRules R) rfl symmetric).headDisjoint
      expanded

/-- A root equation collapsing Pi into a head refutes every such expansion,
even if its endpoints have independently formed types. -/
theorem no_qualification_of_pi_head
    (symmetric : Std.Symm R.headEq) {domain : Tm Head n}
    {codomain : Tm Head (n + 1)} {head : Head}
    (collapse : Conv R.headEq (.pi domain codomain) (.head head) R.computation) :
    ¬ Nonempty (Qualification R) := by
  rintro ⟨qualification⟩
  exact (qualification.piConversionBoundary symmetric).headDisjoint collapse

/-- Application beta preserves the formation-sensitive judgment for every
qualified declaration package, every formed context, and every displayed type. -/
theorem Qualification.betaPi (qualification : Qualification R)
    (symmetric : Std.Symm R.headEq)
    (universes : FormationSensitive.UniverseRegularity R)
    {Γ : Ctx Head n} {body : Tm Head (n + 1)} {argument displayed : Tm Head n}
    (judgment : FormationSensitive.Judgment R Γ (.app (.lam body) argument) displayed) :
    FormationSensitive.Judgment R Γ (inst0 argument body) displayed :=
  judgment.betaPi universes (qualification.piConversionBoundary symmetric)

/-- Assemble the qualification for the actual declaration-signature API.
Transparent definitions must agree with their expanded bodies; any additional
declared computation must be justified separately. -/
def Qualification.ofSignature (base : Rules Head)
    (signature : Declaration.Signature Head)
    (baseEmpty : base.computation = RootComputation.empty)
    (bodies : Bodies Head)
    (constants : ∀ name, Conv base.headEq (.const name) (bodies name)
      (Declaration.rootComputation base signature))
    (definitions : ∀ name value, signature.valueOf? name = some value →
      Conv base.headEq (bodies name) (expand bodies value))
    (declared : ∀ {k : Nat} {left right : Tm Head k},
      signature.computation.step left right →
        Conv base.headEq (expand bodies left) (expand bodies right)) :
    Qualification (Declaration.extendRules base signature) where
  bodies := bodies
  constants := constants
  roots := by
    intro n left right equation
    cases equation with
    | inherited inherited => rw [baseEmpty] at inherited; exact inherited.elim
    | @delta name value lookup =>
        change Conv base.headEq (liftClosed (bodies name))
          (expand bodies (liftClosed value))
        rw [expand_liftClosed]
        exact (definitions name value lookup).renameTerms Fin.elim0
    | declared equation => exact declared equation

#print axioms include_pure
#print axioms Qualification.conversion_iff
#print axioms Qualification.piConversionBoundary
#print axioms no_qualification_of_pi_head
#print axioms Qualification.betaPi
#print axioms Qualification.ofSignature

end ConstantExpansion
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
