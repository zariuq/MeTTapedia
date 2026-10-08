import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTyping
import Mettapedia.TypeTheory.JudgmentDerivation

/-!
# Proof-retaining rules for the existing formation-sensitive judgments

The signature uses the independently authored scoped syntax and its actual
fourteen typing rules. Formation and conversion premises remain explicit.
The generated rule trees are sound and complete for `Typing`, but retain
their premise positions and rule choices when the proposition forgets them.

Its initiality concerns local typing-rule algebras. Interpretation into an
arbitrary category with families still needs its context/type interpretation,
conversion laws and substitution comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveRuleSignature

open JudgmentDerivation

variable {Head : Type}

structure Judgment (Head : Type) where
  arity : Nat
  context : Ctx Head arity
  subject : Tm Head arity
  type : Tm Head arity

abbrev judgment {n : Nat} (Γ : Ctx Head n) (term type : Tm Head n) : Judgment Head :=
  ⟨n, Γ, term, type⟩

/-- Local side conditions are the primitive rule-package decisions. Child
typing judgments occur only as generated premises, never as rule fields. -/
inductive Rule (R : Rules Head) : Judgment Head → Type where
  | headType {n : Nat} {Γ : Ctx Head n} {h u : Head} (typed : R.headTyping h u) :
      Rule R (judgment Γ (.head h) (.head u))
  | var {n : Nat} {Γ : Ctx Head n} (i : Fin n) :
      Rule R (judgment Γ (.var i) (Ctx.lookup Γ i))
  | const {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0} {u : Head}
      (known : R.constantType name = some type) (universeWitness : R.isUniverse u) :
      Rule R (judgment Γ (.const name) (liftClosed type))
  | piForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {u v w : Head} (universeA : R.isUniverse u) (universeB : R.isUniverse v)
      (join : R.join u v w) : Rule R (judgment Γ (.pi A B) (.head w))
  | sigmaForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {u v w : Head} (universeA : R.isUniverse u) (universeB : R.isUniverse v)
      (join : R.join u v w) : Rule R (judgment Γ (.sigma A B) (.head w))
  | lamIntro {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
      {body B : Tm Head (n + 1)} {u : Head} (universeWitness : R.isUniverse u) :
      Rule R (judgment Γ (.lam body) (.pi A B))
  | appElim {n : Nat} {Γ : Ctx Head n} {g a A : Tm Head n} {B : Tm Head (n + 1)} :
      Rule R (judgment Γ (.app g a) (inst0 a B))
  | pairIntro {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
      {B : Tm Head (n + 1)} {u : Head} (universeWitness : R.isUniverse u) :
      Rule R (judgment Γ (.pair a b) (.sigma A B))
  | fstElim {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)} :
      Rule R (judgment Γ (.fst p) A)
  | sndElim {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)} :
      Rule R (judgment Γ (.snd p) (inst0 (.fst p) B))
  | idForm {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {u : Head}
      (universeWitness : R.isUniverse u) : Rule R (judgment Γ (.id A a b) (.head u))
  | reflIntro {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} :
      Rule R (judgment Γ (.refl a) (.id A a a))
  | cumul {n : Nat} {Γ : Ctx Head n} {t : Tm Head n} {u v : Head}
      (order : R.cumulative u v) : Rule R (judgment Γ t (.head v))
  | convert {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n} {u : Head}
      (universeWitness : R.isUniverse u) (conversion : Conv R.headEq A B R.computation) :
      Rule R (judgment Γ t B)

abbrev premiseCount {R : Rules Head} {j : Judgment Head} : Rule R j → Nat
  | .headType _ | .var _ => 0
  | .const _ _ | .fstElim | .sndElim | .reflIntro | .cumul _ => 1
  | .piForm _ _ _ | .sigmaForm _ _ _ | .lamIntro _ | .appElim | .convert _ _ => 2
  | .pairIntro _ | .idForm _ => 3

abbrev hypothesis {R : Rules Head} {j : Judgment Head} (rule : Rule R j) :
    Fin (premiseCount rule) → Judgment Head := by
  cases rule with
  | headType _ | var _ => exact Fin.elim0
  | @const n Γ name type u _ _ => exact fun _ => judgment .nil type (.head u)
  | @piForm n Γ A B u v w _ _ _ | @sigmaForm n Γ A B u v w _ _ _ =>
      exact Fin.cases (judgment Γ A (.head u)) (fun _ => judgment (.snoc Γ A) B (.head v))
  | @lamIntro n Γ A body B u _ =>
      exact Fin.cases (judgment Γ (.pi A B) (.head u))
        (fun _ => judgment (.snoc Γ A) body B)
  | @appElim n Γ g a A B =>
      exact Fin.cases (judgment Γ g (.pi A B)) (fun _ => judgment Γ a A)
  | @pairIntro n Γ a b A B u _ =>
      exact Fin.cases (judgment Γ (.sigma A B) (.head u))
        (Fin.cases (judgment Γ a A) (fun _ => judgment Γ b (inst0 a B)))
  | @fstElim n Γ p A B | @sndElim n Γ p A B =>
      exact fun _ => judgment Γ p (.sigma A B)
  | @idForm n Γ A a b u _ =>
      exact Fin.cases (judgment Γ A (.head u))
        (Fin.cases (judgment Γ a A) (fun _ => judgment Γ b A))
  | @reflIntro n Γ a A => exact fun _ => judgment Γ a A
  | @cumul n Γ t u v _ => exact fun _ => judgment Γ t (.head u)
  | @convert n Γ t A B u _ _ =>
      exact Fin.cases (judgment Γ t A) (fun _ => judgment Γ B (.head u))

abbrev signature (R : Rules Head) : Signature where
  Judgment := Judgment Head
  Rule := Rule R
  Premise rule := Fin (premiseCount rule)
  hypothesis := hypothesis

abbrev Tree (R : Rules Head) (j : Judgment Head) := Derivation (signature R) j

def typingAlgebra (R : Rules Head) : Algebra (signature R) where
  Carrier j := PLift (FormationSensitive.Typing R j.context j.subject j.type)
  conclude rule premises := ⟨by
    cases rule with
    | headType typed => exact .headType typed
    | var index => exact .var index
    | const known universeWitness => exact .const known (premises 0).down universeWitness
    | piForm universeA universeB join =>
        exact .piForm (premises 0).down universeA (premises 1).down universeB join
    | sigmaForm universeA universeB join =>
        exact .sigmaForm (premises 0).down universeA (premises 1).down universeB join
    | lamIntro universeWitness => exact .lamIntro (premises 0).down universeWitness (premises 1).down
    | appElim => exact .appElim (premises 0).down (premises 1).down
    | pairIntro universeWitness =>
        exact .pairIntro (premises 0).down universeWitness (premises 1).down (premises 2).down
    | fstElim => exact .fstElim (premises 0).down
    | sndElim => exact .sndElim (premises 0).down
    | idForm universeWitness =>
        exact .idForm (premises 0).down universeWitness (premises 1).down (premises 2).down
    | reflIntro => exact .reflIntro (premises 0).down
    | cumul order => exact .cumul (premises 0).down order
    | convert universeWitness converted =>
        exact .conv (premises 0).down (premises 1).down universeWitness converted⟩

theorem sound {R : Rules Head} {j : Judgment Head} (tree : Tree R j) :
    FormationSensitive.Typing R j.context j.subject j.type :=
  (interpret (typingAlgebra R) tree).down

/-- Completeness produces a retained rule tree without requiring a checker
or decisions for universeWitness rules and conversion. -/
theorem complete {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {term type : Tm Head n}
    (typed : FormationSensitive.Typing R Γ term type) :
    Nonempty (Tree R (judgment Γ term type)) := by
  induction typed with
  | headType typed => exact ⟨.node (.headType typed) (fun position => nomatch position)⟩
  | var index => exact ⟨.node (.var index) (fun position => nomatch position)⟩
  | const known _ universeWitness ih =>
      obtain ⟨formation⟩ := ih
      exact ⟨.node (.const known universeWitness) (fun _ => formation)⟩
  | piForm _ universeA _ universeB join ihA ihB =>
      obtain ⟨a⟩ := ihA
      obtain ⟨b⟩ := ihB
      exact ⟨.node (.piForm universeA universeB join) (Fin.cases a (fun _ => b))⟩
  | sigmaForm _ universeA _ universeB join ihA ihB =>
      obtain ⟨a⟩ := ihA
      obtain ⟨b⟩ := ihB
      exact ⟨.node (.sigmaForm universeA universeB join) (Fin.cases a (fun _ => b))⟩
  | lamIntro _ universeWitness _ ihFormation ihBody =>
      obtain ⟨formed⟩ := ihFormation
      obtain ⟨body⟩ := ihBody
      exact ⟨.node (.lamIntro universeWitness) (Fin.cases formed (fun _ => body))⟩
  | @appElim n Γ g a A B _ _ ihFunction ihArgument =>
      obtain ⟨function⟩ := ihFunction
      obtain ⟨argument⟩ := ihArgument
      exact ⟨.node (.appElim (A := A) (B := B))
        (Fin.cases function (fun _ => argument))⟩
  | pairIntro _ universeWitness _ _ ihFormation ihFirst ihSecond =>
      obtain ⟨formed⟩ := ihFormation
      obtain ⟨first⟩ := ihFirst
      obtain ⟨second⟩ := ihSecond
      exact ⟨.node (.pairIntro universeWitness)
        (Fin.cases formed (Fin.cases first (fun _ => second)))⟩
  | @fstElim n Γ p A B _ ih =>
      obtain ⟨pair⟩ := ih
      exact ⟨.node (.fstElim (B := B)) (fun _ => pair)⟩
  | @sndElim n Γ p A B _ ih =>
      obtain ⟨pair⟩ := ih
      exact ⟨.node (.sndElim (A := A) (B := B)) (fun _ => pair)⟩
  | idForm _ universeWitness _ _ ihFormation ihLeft ihRight =>
      obtain ⟨formed⟩ := ihFormation
      obtain ⟨left⟩ := ihLeft
      obtain ⟨right⟩ := ihRight
      exact ⟨.node (.idForm universeWitness) (Fin.cases formed (Fin.cases left (fun _ => right)))⟩
  | reflIntro _ ih => obtain ⟨term⟩ := ih; exact ⟨.node .reflIntro (fun _ => term)⟩
  | cumul _ order ih => obtain ⟨term⟩ := ih; exact ⟨.node (.cumul order) (fun _ => term)⟩
  | conv _ _ universeWitness converted ihSource ihFormation =>
      obtain ⟨source⟩ := ihSource
      obtain ⟨formation⟩ := ihFormation
      exact ⟨.node (.convert universeWitness converted) (Fin.cases source (fun _ => formation))⟩

theorem derivable_iff {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {term type : Tm Head n} :
    Nonempty (Tree R (judgment Γ term type)) ↔ FormationSensitive.Typing R Γ term type :=
  ⟨fun ⟨tree⟩ => sound tree, complete⟩

/-- The complete existing rule presentation has a unique proof-retaining
interpretation into every local rule algebra. -/
def ruleAlgebraInitiality (R : Rules Head) :
    _root_.CategoryTheory.Limits.IsInitial (generated (signature R)) :=
  generatedIsInitial (signature R)

end FormationSensitiveRuleSignature
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
