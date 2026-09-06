import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicMILHypothesis
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ConversionCoherence
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ConversionConservativeExtension

/-!
# Conversion-coherent completion of native hypothesis computation

This proof-only presentation permits the repeated metadata of an eliminator
and its constructor to be different terms when their conversion in the
authored package is already established. Every completed root is proved
convertible by the original rules. The authored runtime relation is unchanged.

The completion is not a conversion decision procedure: its guards retain
derivations in the existing conversion relation. It is intended for a
constructor-coherence argument without assuming raw beta/iota confluence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILConversionCompletion

open Presentation Presentation.Declaration IntrinsicMILHypothesis

variable {n m : Nat}

abbrev AuthoredConv (left right : Tower.Tm n) : Prop :=
  Conv IntrinsicMILHypothesis.rules.headEq left right
    IntrinsicMILHypothesis.rules.computation

/-- Conversion evidence for metadata survives independent conversion of
both occurrences; the representatives need not have identical syntax. -/
theorem coherent_transport {left right left' right' : Tower.Tm n}
    (coherent : AuthoredConv left right)
    (first : AuthoredConv left left') (second : AuthoredConv right right') :
    AuthoredConv left' right' :=
  .trans _ _ _ (.symm _ _ first) (.trans _ _ _ coherent second)

inductive Root : Tower.Tm n → Tower.Tm n → Prop where
  | primitive {sorts primitives motive primitiveCase chainCase source target
      innerSorts innerPrimitives innerSource innerTarget symbol : Tower.Tm n} :
      AuthoredConv innerSorts sorts → AuthoredConv innerPrimitives primitives →
      AuthoredConv innerSource source → AuthoredConv innerTarget target →
      Root
        (eliminateApp sorts primitives motive primitiveCase chainCase source target
          (primitiveApp innerSorts innerPrimitives innerSource innerTarget symbol))
        (.app (.app (.app primitiveCase source) target) symbol)
  | chain {sorts primitives motive primitiveCase chainCase source middle target
      innerSorts innerPrimitives innerSource innerTarget earlier later : Tower.Tm n} :
      AuthoredConv innerSorts sorts → AuthoredConv innerPrimitives primitives →
      AuthoredConv innerSource source → AuthoredConv innerTarget target →
      Root
        (eliminateApp sorts primitives motive primitiveCase chainCase source target
          (chainApp innerSorts innerPrimitives innerSource middle innerTarget earlier later))
        (.app
          (.app (.app (.app (.app (.app (.app chainCase source) middle) target) earlier) later)
            (eliminateApp sorts primitives motive primitiveCase chainCase source middle earlier))
          (eliminateApp sorts primitives motive primitiveCase chainCase middle target later))

theorem Root.rename {left right : Tower.Tm n} (root : Root left right)
    (rho : Ren n m) : Root (rename rho left) (rename rho right) := by
  cases root with
  | primitive first second third fourth =>
      exact .primitive (first.renameTerms rho) (second.renameTerms rho)
        (third.renameTerms rho) (fourth.renameTerms rho)
  | chain first second third fourth =>
      exact .chain (first.renameTerms rho) (second.renameTerms rho)
        (third.renameTerms rho) (fourth.renameTerms rho)

theorem Root.substitute {left right : Tower.Tm n} (root : Root left right)
    (substitution : Sub Tower.Head n m) :
    Root (subst substitution left) (subst substitution right) := by
  cases root with
  | primitive first second third fourth =>
      exact .primitive (first.substitute substitution) (second.substitute substitution)
        (third.substitute substitution) (fourth.substitute substitution)
  | chain first second third fourth =>
      exact .chain (first.substitute substitution) (second.substitute substitution)
        (third.substitute substitution) (fourth.substitute substitution)

def computation : RootComputation Tower.Head where
  step := Root
  rename := by
    intro n m rho left right root
    exact root.rename rho
  substitute := by
    intro n m substitution left right root
    exact root.substitute substitution

/-- Only the proof presentation of root computation changes; declaration
types, universe policy and head equality are retained literally. -/
def rules : Rules Tower.Head :=
  { IntrinsicMILHypothesis.rules with computation := computation }

theorem primitiveApp_congr
    {sorts primitives source target sorts' primitives' source' target' symbol symbol' : Tower.Tm n}
    (first : AuthoredConv sorts sorts') (second : AuthoredConv primitives primitives')
    (third : AuthoredConv source source') (fourth : AuthoredConv target target')
    (last : AuthoredConv symbol symbol') :
    AuthoredConv (primitiveApp sorts primitives source target symbol)
      (primitiveApp sorts' primitives' source' target' symbol') :=
  Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp
    (Conv.congApp (.refl _) first) second) third) fourth) last

theorem chainApp_congr
    {sorts primitives source middle target earlier later
      sorts' primitives' source' middle' target' earlier' later' : Tower.Tm n}
    (first : AuthoredConv sorts sorts') (second : AuthoredConv primitives primitives')
    (third : AuthoredConv source source') (fourth : AuthoredConv middle middle')
    (fifth : AuthoredConv target target') (sixth : AuthoredConv earlier earlier')
    (seventh : AuthoredConv later later') :
    AuthoredConv (chainApp sorts primitives source middle target earlier later)
      (chainApp sorts' primitives' source' middle' target' earlier' later') :=
  Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp
    (Conv.congApp (Conv.congApp (.refl _) first) second) third) fourth) fifth) sixth) seventh

/-- A completed root first converts its inner metadata to the outer
representatives, then uses one actual authored iota rule. -/
theorem Root.sound {left right : Tower.Tm n} (root : Root left right) :
    AuthoredConv left right := by
  cases root with
  | primitive first second third fourth =>
      exact .trans _ _ _
        (Conv.congApp (.refl _) (primitiveApp_congr first second third fourth (.refl _)))
        (.rel _ _ (.root (.declared ⟨.primitive _ _ _ _ _ _ _ _⟩)))
  | chain first second third fourth =>
      exact .trans _ _ _
        (Conv.congApp (.refl _)
          (chainApp_congr first second third (.refl _) fourth (.refl _) (.refl _)))
        (.rel _ _ (.root (.declared ⟨.chain _ _ _ _ _ _ _ _ _ _⟩)))

/-- The exact diagonal includes every authored native iota rule. -/
theorem Root.of_iota {left right : Tower.Tm n}
    (evidence : IotaEvidence n left right) : Root left right := by
  cases evidence with
  | primitive => exact .primitive (.refl _) (.refl _) (.refl _) (.refl _)
  | chain => exact .chain (.refl _) (.refl _) (.refl _) (.refl _)

/-- Completing metadata coherence does not change which reduct a root
selects. This is a local root property, not contextual confluence. -/
theorem Root.target_unique {source first second : Tower.Tm n}
    (one : Root source first) (two : Root source second) : first = second := by
  cases one <;> cases two <;> rfl

theorem root_inclusion {left right : Tower.Tm n}
    (root : IntrinsicMILHypothesis.rules.computation.step left right) : Root left right := by
  cases root with
  | inherited impossible => exact impossible.elim
  | delta lookup => rw [rawSignature_valueOf_none] at lookup; cases lookup
  | declared evidence => obtain ⟨evidence⟩ := evidence; exact Root.of_iota evidence

def rootPiHeadNeutral : ConversionCoherence.RootPiHeadNeutral rules where
  pi := by intro n domain codomain target impossible; cases impossible
  head := by intro n head target impossible; cases impossible

theorem root_sigma_neutral {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    {target : Tower.Tm n} : ¬ Root (.sigma domain codomain) target := by
  intro impossible
  cases impossible

/-- The completed presentation has exactly the authored conversion theory,
by proved local root inclusion and soundness rather than an assumed path law. -/
def conservative : ConversionConservativeExtension IntrinsicMILHypothesis.rules rules where
  headEq_eq := rfl
  root_inclusion := root_inclusion
  root_sound := Root.sound

theorem conversion_iff (left right : Tower.Tm n) :
    AuthoredConv left right ↔ Conv rules.headEq left right rules.computation :=
  conservative.conversion_iff left right

namespace Examples

def ground : Tower.Tm n := .head .legacyGround
def betaGround : Tower.Tm n := .app (.lam (.var 0)) ground

def mixed : Tower.Tm n :=
  eliminateApp ground ground ground (.const hypothesisName) ground ground ground
    (primitiveApp betaGround ground ground ground ground)

def result : Tower.Tm n := .app (.app (.app (.const hypothesisName) ground) ground) ground

theorem mixed_root : Root (mixed : Tower.Tm n) result :=
  .primitive (.rel _ _ (.betaPi _ _)) (.refl _) (.refl _) (.refl _)

theorem mixed_authored_conversion : AuthoredConv (mixed : Tower.Tm n) result :=
  mixed_root.sound

/-- The proof-only completion can expose a root that the exact authored
matcher does not yet see. This is not a runtime-step equivalence. -/
theorem mixed_not_authored_root :
    ¬ IntrinsicMILHypothesis.rules.computation.step (mixed : Tower.Tm n) result := by
  intro root
  cases root with
  | inherited impossible => exact impossible.elim
  | declared evidence =>
      obtain ⟨evidence⟩ := evidence
      cases evidence

end Examples

#print axioms coherent_transport
#print axioms Root.rename
#print axioms Root.substitute
#print axioms Root.sound
#print axioms Root.of_iota
#print axioms Root.target_unique
#print axioms root_inclusion
#print axioms rootPiHeadNeutral
#print axioms root_sigma_neutral
#print axioms conservative
#print axioms conversion_iff
#print axioms Examples.mixed_root
#print axioms Examples.mixed_authored_conversion
#print axioms Examples.mixed_not_authored_root

end MILConversionCompletion
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
