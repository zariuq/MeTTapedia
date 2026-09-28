import Mettapedia.Languages.Agda.Structural.Syntax
import Mettapedia.OSLF.Syntax.BindingCompatibleDerivations

/-!
# Computation of explicit elimination spines

These are the computational and administrative rules of the structural
presentation. Beta consumes the first application and retains the remaining
spine. Empty-spine elimination and spine concatenation are administrative.
Neither type-directed eta nor unfolding a user declaration is an untyped
rule of this fragment.

Root occurrences and compatible derivations are Type-valued. Their
connection with the separately sourced Agda specification belongs to the
adequacy modules, rather than to either definition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural

open Mettapedia.OSLF.Binding

inductive Root : {Γ : Ctx sig} → {s : Srt} →
    Term sig Γ s → Term sig Γ s → Type where
  | beta {Γ} (body : Tm (.term :: Γ)) (argument : Tm Γ) (rest : Spine Γ) :
      Root (eliminate (lam body) (cons (apply argument) rest))
        (eliminate (inst body argument) rest)
  | betaNoAbs {Γ} (body argument : Tm Γ) (rest : Spine Γ) :
      Root (eliminate (lamNoAbs body) (cons (apply argument) rest)) (eliminate body rest)
  | eliminateEmpty {Γ} (head : Tm Γ) : Root (eliminate head nil) head
  | eliminateAppend {Γ} (head : Tm Γ) (first second : Spine Γ) :
      Root (eliminate (eliminate head first) second) (eliminate head (append first second))
  | appendEmpty {Γ} (rest : Spine Γ) : Root (append nil rest) rest
  | appendCons {Γ} (head : Elim Γ) (first second : Spine Γ) :
      Root (append (cons head first) second) (cons head (append first second))

def Root.substitute {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ) {s : Srt}
    {source target : Term sig Γ s} (occurrence : Root source target) :
    Root (bind σ source) (bind σ target) := by
  cases occurrence with
  | beta body argument rest =>
      change Root
        (eliminate (lam (bind (liftSub σ [.term]) body))
          (cons (apply (bind σ argument)) (bind σ rest)))
        (eliminate (bind σ (inst body argument)) (bind σ rest))
      rw [substitute_inst]
      exact .beta _ _ _
  | betaNoAbs body argument rest => exact .betaNoAbs _ _ _
  | eliminateEmpty head => exact .eliminateEmpty _
  | eliminateAppend head first second => exact .eliminateAppend _ _ _
  | appendEmpty rest => exact .appendEmpty _
  | appendCons head first second => exact .appendCons _ _ _

abbrev Step {Γ : Ctx sig} {s : Srt} (source target : Term sig Γ s) :=
  CompatibleDerivations.Step Root source target
abbrev ArgsStep {Γ : Ctx sig} {arity : List (List Srt × Srt)}
    (source target : Args sig arity Γ) :=
  CompatibleDerivations.ArgsStep Root source target

def Step.substitute {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ) {s : Srt}
    {source target : Term sig Γ s} (derivation : Step source target) :
    Step (bind σ source) (bind σ target) :=
  CompatibleDerivations.substitute Root.substitute σ derivation

theorem Step.height_substitute {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ) {s : Srt}
    {source target : Term sig Γ s} (derivation : Step source target) :
    CompatibleDerivations.height (Step.substitute σ derivation) =
      CompatibleDerivations.height derivation :=
  CompatibleDerivations.height_substitute Root.substitute σ derivation

theorem variable_inert {Γ : Ctx sig} {s : Srt} (var : Var Γ s)
    (target : Term sig Γ s) : IsEmpty (Step (.var var) target) := by
  constructor
  intro derivation
  cases derivation with
  | root occurrence => cases occurrence

theorem literal_inert {Γ : Ctx sig} (value : Nat) (target : Tm Γ) :
    IsEmpty (Step (natLiteral value) target) := by
  constructor
  intro derivation
  cases derivation with
  | root occurrence => cases occurrence
  | congr op arguments => cases arguments

namespace Controls

def identity : Tm [] := lam (.var .zero)
def identityCall : Tm [] := eliminate identity (cons (apply (natLiteral 7)) nil)

def identityBeta : Step identityCall (eliminate (natLiteral 7) nil) :=
  .root (.beta (.var .zero) (natLiteral 7) nil)
def identityFinish : Step (Γ := []) (eliminate (natLiteral 7) nil) (natLiteral 7) :=
  .root (.eliminateEmpty _)

/-- An untyped two-step cycle prevents claiming termination from scoping. -/
def selfApply : Tm [] :=
  lam (eliminate (.var .zero) (cons (apply (.var .zero)) nil))
def omega : Tm [] := eliminate selfApply (cons (apply selfApply) nil)
def omegaBeta : Step omega (eliminate omega nil) :=
  .root (.beta _ _ _)
def omegaFinish : Step (eliminate omega nil) omega := .root (.eliminateEmpty _)

def overlapSource : Tm [] := eliminate (eliminate (natLiteral 0) nil) nil
def overlapTarget : Tm [] := eliminate (natLiteral 0) nil

def outerOccurrence : Step overlapSource overlapTarget :=
  .root (.eliminateEmpty _)
def innerOccurrence : Step overlapSource overlapTarget := by
  change CompatibleDerivations.Step Root
    (.op Op.eliminate (.cons (eliminate (natLiteral 0) nil) (.cons nil .nil)))
    (.op Op.eliminate (.cons (natLiteral 0) (.cons nil .nil)))
  exact CompatibleDerivations.Step.congr (R := Root) Op.eliminate
    (.head (.cons nil .nil) (.root (Root.eliminateEmpty (natLiteral 0))))

/-- Equal endpoints do not identify distinct computational occurrences. -/
theorem overlapping_occurrences_distinct : outerOccurrence ≠ innerOccurrence := by
  intro impossible
  cases impossible

def newRedex : Sub sig [.term] [] := fun _ var => match var with
  | .zero => identityCall

def afterSubstitution :
    Step (bind newRedex (.var .zero : Tm [.term])) (eliminate (natLiteral 7) nil) :=
  identityBeta

theorem beforeSubstitution_inert :
    ∀ target : Tm [.term], IsEmpty (Step (.var .zero) target) := variable_inert .zero

end Controls

end Mettapedia.Languages.Agda.Structural
