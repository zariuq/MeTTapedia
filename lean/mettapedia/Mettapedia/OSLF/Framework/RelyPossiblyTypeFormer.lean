import Mettapedia.OSLF.Framework.GeneratedModality
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.GSLT.LanguageDef.DerivedEquationCanaries

/-!
# The rely-possibly modality as a type former

`GeneratedModality` builds a raw relational modality and conditional introduction,
step and elimination laws. A predicate on terms is not yet a type of
the generated logic: the generated OSLF's types at a sort are the predicates the
equations cannot see past, and an arbitrary predicate on representatives is not
one of those.

This module saturates that predicate under equations. Transporting executable
consequences back to the original representative requires explicit invariance.

**What the passage costs, stated rather than hidden.**  The raw modality is a
predicate on representatives, and nothing makes it invariant: it mentions its
argument under `applyBindings`, and two equivalent arguments need not have
equivalent images unless substitution respects the equations.  So the type
former is the *saturation* of the raw modality, its characterisation is up to
the equations, and it agrees with the raw modality exactly on presentations
where the raw modality is already invariant.  That last condition is named and
carried, not assumed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RelyPossiblyTypeFormer

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.GeneratedModality

variable (relEnv : RelationEnv) (lang : LanguageDef)

/-! ## The former -/

/-- **The rely-possibly modality as a type of the generated logic.**  Its
continuation argument is a type of that logic rather than a bare predicate, and
its value is one too. -/
def relyPossiblyType (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing relEnv lang)) :
    EquationPredicate (langGSLTUsing relEnv lang) :=
  saturatePredicate (langGSLTUsing relEnv lang)
    (RelyPossibly (engineBasePremises relEnv) lang rule pos A B.1)

/-- **The characterisation.**  A term inhabits the type exactly when some
presentation of it inhabits the raw modality — which is what passing to the
predicates of the generated logic means. -/
theorem relyPossiblyType_spec (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing relEnv lang)) (term : Pattern) :
    (relyPossiblyType relEnv lang rule pos A B).1 term ↔
      ∃ representative, (langGSLTUsing relEnv lang).Equiv term representative ∧
        RelyPossibly (engineBasePremises relEnv) lang rule pos A B.1 representative :=
  Iff.rfl

/-- The raw modality entails the type: a term inhabiting the modality inhabits
it at its own presentation. -/
theorem relyPossiblyType_of_relyPossibly (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing relEnv lang)) {term : Pattern}
    (holds : RelyPossibly (engineBasePremises relEnv) lang rule pos A B.1 term) :
    (relyPossiblyType relEnv lang rule pos A B).1 term :=
  ⟨term, (langGSLTUsing relEnv lang).equations.iseqv.refl term, holds⟩

/-- **And the converse holds exactly when the raw modality is already
invariant**, which is the condition the passage costs. -/
theorem relyPossibly_of_relyPossiblyType (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing relEnv lang))
    (invariant : EquationInvariant (langGSLTUsing relEnv lang)
      (RelyPossibly (engineBasePremises relEnv) lang rule pos A B.1))
    {term : Pattern}
    (holds : (relyPossiblyType relEnv lang rule pos A B).1 term) :
    RelyPossibly (engineBasePremises relEnv) lang rule pos A B.1 term := by
  obtain ⟨representative, equivalent, raw⟩ := holds
  exact (invariant equivalent).mpr raw

/-! ## The rules, at the type level

Each is a relational theorem transported through saturation. Rely-parameter
congruence and introduction transport directly. Step and elimination require
invariance to recover the raw predicate at the original representative.
No sorted source formation judgment is constructed by this transport. -/

/-- Rely-parameter congruence: predicates outside the position's rely family
do not affect the saturated modality. This is not the sorted M-FORM judgment. -/
theorem relyPossiblyType_congr_relyVars (rule : RewriteRule) (pos : Position)
    {A A' : String → Pattern → Prop}
    (B : EquationPredicate (langGSLTUsing relEnv lang))
    (agree : ∀ name ∈ relyVars rule.left pos, A name = A' name) (term : Pattern) :
    (relyPossiblyType relEnv lang rule pos A B).1 term ↔
      (relyPossiblyType relEnv lang rule pos A' B).1 term := by
  constructor
  · rintro ⟨representative, equivalent, raw⟩
    exact ⟨representative, equivalent, (relyPossibly_congr_relyVars agree).mp raw⟩
  · rintro ⟨representative, equivalent, raw⟩
    exact ⟨representative, equivalent, (relyPossibly_congr_relyVars agree).mpr raw⟩

/-- **M-INTRO.**  The focus of a stable redex position inhabits the type,
whenever the right-hand side instance inhabits the continuation type on every
firing instantiation meeting the rely assumptions. -/
theorem relyPossiblyType_intro (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing relEnv lang)) {term : Pattern}
    (stable : StablePath rule.left pos = true)
    (focus : subtermAt rule.left pos = some term)
    (continuation : ∀ bindings : Bindings,
      RelySatisfied rule pos A bindings →
      RuleFires (engineBasePremises relEnv) lang rule bindings →
      B.1 (Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings rule bindings)) :
    (relyPossiblyType relEnv lang rule pos A B).1 term :=
  relyPossiblyType_of_relyPossibly relEnv lang rule pos A B
    (relyPossibly_intro stable focus continuation)

/-- Under invariance, rely assumptions and firing, the instantiated context
has some successor. The conclusion does not specify the authored right-hand side. -/
theorem relyPossiblyType_step (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing relEnv lang))
    (invariant : EquationInvariant (langGSLTUsing relEnv lang)
      (RelyPossibly (engineBasePremises relEnv) lang rule pos A B.1))
    {term : Pattern} {bindings : Bindings}
    (holds : (relyPossiblyType relEnv lang rule pos A B).1 term)
    (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires (engineBasePremises relEnv) lang rule bindings) :
    ∃ source target : Pattern,
      plug (applyBindings bindings rule.left) pos (applyBindings bindings term)
          = some source ∧
        Step (engineBasePremises relEnv) lang source target :=
  relyPossibly_step
    (relyPossibly_of_relyPossiblyType relEnv lang rule pos A B invariant holds)
    rely fires

/-- Under the same assumptions, some successor inhabits the continuation
predicate. This is weaker than typing the specified right-hand-side instance. -/
theorem relyPossiblyType_elim (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing relEnv lang))
    (invariant : EquationInvariant (langGSLTUsing relEnv lang)
      (RelyPossibly (engineBasePremises relEnv) lang rule pos A B.1))
    {term : Pattern} {bindings : Bindings}
    (holds : (relyPossiblyType relEnv lang rule pos A B).1 term)
    (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires (engineBasePremises relEnv) lang rule bindings) :
    ∃ target : Pattern, B.1 target ∧
      ∃ source : Pattern,
        plug (applyBindings bindings rule.left) pos (applyBindings bindings term)
            = some source ∧ Step (engineBasePremises relEnv) lang source target :=
  relyPossibly_elim
    (relyPossibly_of_relyPossiblyType relEnv lang rule pos A B invariant holds)
    rely fires

/-! ## It is a type of the generated system

The current relational `langOSLFUsing` has constant Pattern fibers at every
String sort. Its satisfaction reads this predicate without establishing
signature-indexed formation or that the supplied sort is declared. -/

/-- **The former lands in the generated OSLF's predicates**, and inhabitation is
the system's own satisfaction relation rather than a second notion beside it. -/
theorem satisfies_relyPossiblyType (procSort : String) (rule : RewriteRule)
    (pos : Position) (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing relEnv lang)) (term : Pattern) :
    (langOSLFUsing relEnv lang procSort).satisfies
        (S := procSort) term (relyPossiblyType relEnv lang rule pos A B) ↔
      ∃ representative, (langGSLTUsing relEnv lang).Equiv term representative ∧
        RelyPossibly (engineBasePremises relEnv) lang rule pos A B.1 representative :=
  Iff.rfl

/-! ## The invariance condition in the equation-free fragment

The equation-free fragment supplies an instance of the condition. Its validity
for the principal equational presentations is not established here.

The class is not everything, and the boundary is exactly where one would expect
it: an equation-free presentation has equality for its equivalence, so every
predicate is invariant and the passage to types costs nothing.  A presentation
with a derived collection carrier does not, and there the condition reduces to
substitution respecting the equations — which is a theorem about that
presentation, not about the modality. -/

/-- **The invariance condition holds for every equation-free presentation.**
No property of the modality is used: on such a presentation the equivalence is
equality. -/
theorem relyPossibly_invariant_of_equationFree
    (equationFree : lang.isEquationFree = true) (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing relEnv lang)) :
    EquationInvariant (langGSLTUsing relEnv lang)
      (RelyPossibly (engineBasePremises relEnv) lang rule pos A B.1) :=
  equationInvariant_langGSLTUsing_of_equation_free relEnv equationFree _

/-- **So there the former is the raw modality**, with nothing carried. -/
theorem relyPossiblyType_iff_relyPossibly_of_equationFree
    (equationFree : lang.isEquationFree = true) (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing relEnv lang)) (term : Pattern) :
    (relyPossiblyType relEnv lang rule pos A B).1 term ↔
      RelyPossibly (engineBasePremises relEnv) lang rule pos A B.1 term :=
  ⟨relyPossibly_of_relyPossiblyType relEnv lang rule pos A B
      (relyPossibly_invariant_of_equationFree relEnv lang equationFree rule pos A B),
    relyPossiblyType_of_relyPossibly relEnv lang rule pos A B⟩

/-- **M-STEP with no hypothesis left standing**, on an equation-free
presentation. -/
theorem relyPossiblyType_step_of_equationFree
    (equationFree : lang.isEquationFree = true) (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing relEnv lang))
    {term : Pattern} {bindings : Bindings}
    (holds : (relyPossiblyType relEnv lang rule pos A B).1 term)
    (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires (engineBasePremises relEnv) lang rule bindings) :
    ∃ source target : Pattern,
      plug (applyBindings bindings rule.left) pos (applyBindings bindings term)
          = some source ∧
        Step (engineBasePremises relEnv) lang source target :=
  relyPossiblyType_step relEnv lang rule pos A B
    (relyPossibly_invariant_of_equationFree relEnv lang equationFree rule pos A B)
    holds rely fires

/-- **And M-ELIM.** -/
theorem relyPossiblyType_elim_of_equationFree
    (equationFree : lang.isEquationFree = true) (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing relEnv lang))
    {term : Pattern} {bindings : Bindings}
    (holds : (relyPossiblyType relEnv lang rule pos A B).1 term)
    (rely : RelySatisfied rule pos A bindings)
    (fires : RuleFires (engineBasePremises relEnv) lang rule bindings) :
    ∃ target : Pattern, B.1 target ∧
      ∃ source : Pattern,
        plug (applyBindings bindings rule.left) pos (applyBindings bindings term)
            = some source ∧ Step (engineBasePremises relEnv) lang source target :=
  relyPossiblyType_elim relEnv lang rule pos A B
    (relyPossibly_invariant_of_equationFree relEnv lang equationFree rule pos A B)
    holds rely fires

/-! ### A presentation in the class, and one outside it -/

namespace Discharged

open Mettapedia.GSLT.LanguageDef.DerivedEquationCanaries

/-- The vector presentation is equation-free, so it meets the condition. -/
theorem vec_invariant (env : RelationEnv) (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing env vecLanguage)) :
    EquationInvariant (langGSLTUsing env vecLanguage)
      (RelyPossibly (engineBasePremises env) vecLanguage rule pos A B.1) :=
  relyPossibly_invariant_of_equationFree env vecLanguage vecLanguage_equationFree rule pos A B

/-- **And there the type former is the raw modality on the nose.** -/
theorem vec_type_iff_raw (env : RelationEnv) (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop)
    (B : EquationPredicate (langGSLTUsing env vecLanguage)) (term : Pattern) :
    (relyPossiblyType env vecLanguage rule pos A B).1 term ↔
      RelyPossibly (engineBasePremises env) vecLanguage rule pos A B.1 term :=
  relyPossiblyType_iff_relyPossibly_of_equationFree env vecLanguage
    vecLanguage_equationFree rule pos A B term

/-- **The boundary is real.**  The bag presentation is not equation-free, so
this route does not reach it; there the condition is a statement about
substitution respecting the derived collection laws, and the type former is the
saturation rather than the modality itself. -/
theorem bag_outside_class : bagLanguage.isEquationFree = false :=
  bagLanguage_not_equationFree

end Discharged

end Mettapedia.OSLF.Framework.RelyPossiblyTypeFormer
