import Mettapedia.Cybernetics.ObservedVariety

/-!
# Distinction conservation

A transformation conserves a selected distinction when every distinction in
its source remains a distinction in its target.  The relation is deliberately
parameterized: observer-relative distinctions and exact inequality are useful
instances, but neither is installed as the only possible notion.

For exact inequality, conservation is equivalent to injectivity.  This gives a
small reusable bridge from Francis Heylighen's distinction-conservation
criterion to independently defined faithfulness conditions in operational
semantics.  The micro/macro canary shows why the selected distinctions must
remain explicit.

Reference:

- F. Heylighen, *Causality as Distinction Conservation: a theory of
  predictability, reversibility and time order* (1989).
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics

universe uSource uTarget uSourceView uTargetView

namespace Distinction

/-- `transform` conserves every selected source distinction. -/
def Conserves {Source : Type uSource} {Target : Type uTarget}
    (sourceDistinction : Source → Source → Prop)
    (targetDistinction : Target → Target → Prop)
    (transform : Source → Target) : Prop :=
  ∀ first second,
    sourceDistinction first second →
      targetDistinction (transform first) (transform second)

/-- Exact inequality as a distinction relation. -/
def inequality (Alpha : Type uSource) : Alpha → Alpha → Prop :=
  fun first second => first ≠ second

/-- Conserving exact inequality is precisely injectivity.  This result is the
bridge used downstream; neither side is defined in terms of the other. -/
theorem conserves_inequality_iff_injective
    {Source : Type uSource} {Target : Type uTarget}
    (transform : Source → Target) :
    Conserves (inequality Source) (inequality Target) transform ↔
      Function.Injective transform := by
  constructor
  · intro conserves first second sameImage
    by_contra distinct
    exact conserves first second distinct sameImage
  · intro injective first second distinct sameImage
    exact distinct (injective sameImage)

theorem conserves_id {Alpha : Type uSource}
    (distinction : Alpha → Alpha → Prop) :
    Conserves distinction distinction id := by
  intro first second distinguished
  exact distinguished

theorem Conserves.comp
    {Source : Type uSource} {Middle : Type*} {Target : Type uTarget}
    {sourceDistinction : Source → Source → Prop}
    {middleDistinction : Middle → Middle → Prop}
    {targetDistinction : Target → Target → Prop}
    {earlier : Source → Middle} {later : Middle → Target}
    (earlierConserves :
      Conserves sourceDistinction middleDistinction earlier)
    (laterConserves :
      Conserves middleDistinction targetDistinction later) :
    Conserves sourceDistinction targetDistinction (later ∘ earlier) := by
  intro first second distinguished
  exact laterConserves _ _
    (earlierConserves first second distinguished)

/-! ## Observer-indexed conservation -/

/-- Conservation relative to selected source and target observers. -/
def ConservesObserved
    {Source : Type uSource} {Target : Type uTarget}
    {SourceView : Type uSourceView} {TargetView : Type uTargetView}
    (source : Observer Source SourceView)
    (target : Observer Target TargetView)
    (transform : Source → Target) : Prop :=
  Conserves source.Distinguishes target.Distinguishes transform

/-- An exact change of presentation conserves every observed distinction. -/
theorem exactPresentation_conserves
    {Source : Type uSource} {Target : Type uTarget}
    {SourceView : Type uSourceView} {TargetView : Type uTargetView}
    {source : Observer Source SourceView}
    {target : Observer Target TargetView}
    (presentation : Observer.ExactPresentation source target) :
    ConservesObserved source target presentation.stateEquiv := by
  intro first second distinguished
  exact (presentation.distinguishes_iff first second).mp distinguished

/-- Coarsening the micro observer to the macro observer destroys a real
distinction even though the underlying state map is the identity. -/
theorem microToMacro_not_conserves :
    ¬ ConservesObserved Observer.ObserverRelativity.micro
        Observer.ObserverRelativity.macroView id := by
  intro conserves
  exact Observer.ObserverRelativity.macro_identifies_hidden_coordinate
    (conserves _ _
      Observer.ObserverRelativity.micro_distinguishes_hidden_coordinate)

end Distinction

end Mettapedia.Cybernetics

#print axioms Mettapedia.Cybernetics.Distinction.conserves_inequality_iff_injective
#print axioms Mettapedia.Cybernetics.Distinction.microToMacro_not_conserves
