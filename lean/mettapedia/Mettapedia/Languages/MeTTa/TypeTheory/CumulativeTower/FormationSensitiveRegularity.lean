import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveTyping

/-!
# Regularity of formation-sensitive cumulative typing

The refined judgment has a formed result type whenever its context is formed
and its universe rules satisfy the separate regularity interface. Formation
of dependent elimination results follows from substitution and inversion of
the displayed type's formation derivation; no conversion injectivity premise
is required for this result.

This is a presupposition theorem for the candidate judgment on the existing
cumulative syntax. It is not a subject-reduction, consistency, normalization,
or profile-adoption theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive

variable {Head : Type} {R : Rules Head} {n m : Nat}

/-- Every telescope entry is formed by the candidate judgment itself. -/
inductive ContextFormation (R : Rules Head) :
    {n : Nat} → Ctx Head n → Prop where
  | nil : ContextFormation R .nil
  | snoc {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {u : Head} :
      ContextFormation R Γ → Typing R Γ A (.head u) → R.isUniverse u →
      ContextFormation R (.snoc Γ A)

/-- Variable lookup retains the universe formation of its telescope entry. -/
theorem ContextFormation.lookup_formed {Γ : Ctx Head n}
    (context : ContextFormation R Γ) (index : Fin n) :
    ∃ u, R.isUniverse u ∧ Typing R Γ (Ctx.lookup Γ index) (.head u) := by
  induction context with
  | nil => exact Fin.elim0 index
  | @snoc n Γ A u context formed universeWitness ih =>
      refine Fin.cases ?_ ?_ index
      · exact ⟨u, universeWitness, by
          simpa only [Ctx.lookup_snoc_zero, rename] using
            (formed.weaken (extension := A))⟩
      · intro prior
        obtain ⟨v, isUniverse, entryFormed⟩ := ih prior
        exact ⟨v, isUniverse, by
          simpa only [Ctx.lookup_snoc_succ, rename] using
            (entryFormed.weaken (extension := A))⟩

namespace Typing

private theorem constFormationAux {Γ : Ctx Head n} {term type : Tm Head n}
    (typing : Typing R Γ term type) :
    ∀ {name : DeclName}, term = .const name →
      ∃ declaredType u,
        R.constantType name = some declaredType ∧
        Typing R .nil declaredType (.head u) ∧ R.isUniverse u := by
  induction typing with
  | const known formed universeWitness _ =>
      intro name equality
      cases equality
      exact ⟨_, _, known, formed, universeWitness⟩
  | cumul _ _ ih =>
      intro name equality
      exact ih equality
  | conv _ _ _ _ ih _ =>
      intro name equality
      exact ih equality
  | _ =>
      intro name equality
      cases equality

/-- Every use of a constant retains a formed closed declared type, even when
the displayed result was subsequently converted or raised cumulatively. -/
theorem constFormation {Γ : Ctx Head n} {name : DeclName} {type : Tm Head n}
    (typing : Typing R Γ (.const name) type) :
    ∃ declaredType u,
      R.constantType name = some declaredType ∧
      Typing R .nil declaredType (.head u) ∧ R.isUniverse u :=
  constFormationAux typing rfl

private theorem piFormationAux {Γ : Ctx Head n} {term type : Tm Head n}
    (typing : Typing R Γ term type) :
    ∀ {A : Tm Head n} {B : Tm Head (n + 1)}, term = .pi A B →
      ∃ u v w,
        Typing R Γ A (.head u) ∧ R.isUniverse u ∧
        Typing R (.snoc Γ A) B (.head v) ∧ R.isUniverse v ∧
        R.join u v w := by
  induction typing with
  | piForm formedA universeA formedB universeB join _ _ =>
      intro A B equality
      cases equality
      exact ⟨_, _, _, formedA, universeA, formedB, universeB, join⟩
  | cumul _ _ ih =>
      intro A B equality
      exact ih equality
  | conv _ _ _ _ ih _ =>
      intro A B equality
      exact ih equality
  | _ =>
      intro A B equality
      cases equality

/-- Formation of a displayed Pi exposes formation of both components. The
result type may have undergone conversion or cumulative adjustment. -/
theorem piFormation {Γ : Ctx Head n} {A type : Tm Head n}
    {B : Tm Head (n + 1)} (typing : Typing R Γ (.pi A B) type) :
    ∃ u v w,
      Typing R Γ A (.head u) ∧ R.isUniverse u ∧
      Typing R (.snoc Γ A) B (.head v) ∧ R.isUniverse v ∧
      R.join u v w :=
  piFormationAux typing rfl

private theorem sigmaFormationAux {Γ : Ctx Head n} {term type : Tm Head n}
    (typing : Typing R Γ term type) :
    ∀ {A : Tm Head n} {B : Tm Head (n + 1)}, term = .sigma A B →
      ∃ u v w,
        Typing R Γ A (.head u) ∧ R.isUniverse u ∧
        Typing R (.snoc Γ A) B (.head v) ∧ R.isUniverse v ∧
        R.join u v w := by
  induction typing with
  | sigmaForm formedA universeA formedB universeB join _ _ =>
      intro A B equality
      cases equality
      exact ⟨_, _, _, formedA, universeA, formedB, universeB, join⟩
  | cumul _ _ ih =>
      intro A B equality
      exact ih equality
  | conv _ _ _ _ ih _ =>
      intro A B equality
      exact ih equality
  | _ =>
      intro A B equality
      cases equality

/-- Formation of a displayed Sigma exposes formation of both components. -/
theorem sigmaFormation {Γ : Ctx Head n} {A type : Tm Head n}
    {B : Tm Head (n + 1)} (typing : Typing R Γ (.sigma A B) type) :
    ∃ u v w,
      Typing R Γ A (.head u) ∧ R.isUniverse u ∧
      Typing R (.snoc Γ A) B (.head v) ∧ R.isUniverse v ∧
      R.join u v w :=
  sigmaFormationAux typing rfl

/-- Every displayed result type is itself formed in some universe. This
uses neither normalization nor a boundary on the admitted conversion paths. -/
theorem regularity {Γ : Ctx Head n} {term type : Tm Head n}
    (typing : Typing R Γ term type) (universes : UniverseRegularity R)
    (context : ContextFormation R Γ) :
    ∃ u, R.isUniverse u ∧ Typing R Γ type (.head u) := by
  induction typing with
  | headType head =>
      obtain ⟨v, typedUniverse, isUniverse⟩ :=
        universes.universe_typed (universes.head_target head)
      exact ⟨v, isUniverse, .headType typedUniverse⟩
  | var index => exact context.lookup_formed index
  | const known formed universeWitness _ =>
      exact ⟨_, universeWitness, by
        simpa only [liftClosed, rename] using
          (formed.renameTyping (Δ := _) (ρ := Fin.elim0)
            (fun index => Fin.elim0 index))⟩
  | piForm _ _ _ _ join _ _ =>
      obtain ⟨v, typedUniverse, isUniverse⟩ :=
        universes.universe_typed (universes.join_target join)
      exact ⟨v, isUniverse, .headType typedUniverse⟩
  | sigmaForm _ _ _ _ join _ _ =>
      obtain ⟨v, typedUniverse, isUniverse⟩ :=
        universes.universe_typed (universes.join_target join)
      exact ⟨v, isUniverse, .headType typedUniverse⟩
  | lamIntro formed universeWitness _ _ _ =>
      exact ⟨_, universeWitness, formed⟩
  | appElim function argument ihFunction _ =>
      obtain ⟨_, _, formedPi⟩ := ihFunction context
      obtain ⟨_, v, _, _, _, formedB, universeB, _⟩ := formedPi.piFormation
      exact ⟨v, universeB, by
        simpa only [inst0, subst] using formedB.instantiate argument⟩
  | pairIntro formed universeWitness _ _ _ _ _ =>
      exact ⟨_, universeWitness, formed⟩
  | fstElim pair ihPair =>
      obtain ⟨_, _, formedSigma⟩ := ihPair context
      obtain ⟨u, _, _, formedA, universeA, _, _, _⟩ := formedSigma.sigmaFormation
      exact ⟨u, universeA, formedA⟩
  | sndElim pair ihPair =>
      obtain ⟨_, _, formedSigma⟩ := ihPair context
      obtain ⟨_, v, _, _, _, formedB, universeB, _⟩ := formedSigma.sigmaFormation
      exact ⟨v, universeB, by
        simpa only [inst0, subst] using formedB.instantiate (Typing.fstElim pair)⟩
  | idForm _ universeWitness _ _ _ _ _ =>
      obtain ⟨v, typedUniverse, isUniverse⟩ := universes.universe_typed universeWitness
      exact ⟨v, isUniverse, .headType typedUniverse⟩
  | reflIntro term ihTerm =>
      obtain ⟨u, universeWitness, formed⟩ := ihTerm context
      exact ⟨u, universeWitness, .idForm formed universeWitness term term⟩
  | cumul _ order _ =>
      obtain ⟨v, typedUniverse, isUniverse⟩ :=
        universes.universe_typed (universes.cumulative_target order)
      exact ⟨v, isUniverse, .headType typedUniverse⟩
  | conv _ formed universeWitness _ _ _ =>
      exact ⟨_, universeWitness, formed⟩

end Typing

/-- The complete candidate judgment includes its formed ambient telescope. -/
structure Judgment (R : Rules Head) (Γ : Ctx Head n)
    (term type : Tm Head n) : Prop where
  context : ContextFormation R Γ
  typing : Typing R Γ term type

theorem Judgment.toRaw {Γ : Ctx Head n} {term type : Tm Head n}
    (judgment : Judgment R Γ term type) : HasType R Γ term type :=
  judgment.typing.toRaw

theorem Judgment.regularity {Γ : Ctx Head n} {term type : Tm Head n}
    (judgment : Judgment R Γ term type) (universes : UniverseRegularity R) :
    ∃ u, R.isUniverse u ∧ Judgment R Γ type (.head u) := by
  obtain ⟨u, universeWitness, formed⟩ :=
    judgment.typing.regularity universes judgment.context
  exact ⟨u, universeWitness, judgment.context, formed⟩

/-- Substitution preserves the complete judgment when its target telescope
is formed. The substitution's component evidence uses refined typing. -/
theorem Judgment.substitute {Γ : Ctx Head n} {Δ : Ctx Head m}
    {term type : Tm Head n} {σ : Sub Head n m}
    (judgment : Judgment R Γ term type) (target : ContextFormation R Δ)
    (typed : CtxMor R Γ Δ σ) :
    Judgment R Δ (subst σ term) (subst σ type) :=
  ⟨target, judgment.typing.substitute typed⟩

/-! ## Declaration-formation controls -/

namespace Examples

def declaredName : DeclName := `FormationSensitiveExample.declared

def missingName : DeclName := `FormationSensitiveExample.missing

/-- One opaque declaration with the already formed cumulative ground type. -/
def formedDeclarationRules : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = declaredName then some (.head .legacyGround) else none }

/-- Positive: the declaration's actual type-formation proof licenses its use
in the complete candidate judgment. -/
theorem formed_declaration_judgment :
    Judgment formedDeclarationRules (.nil : Tower.Ctx 0)
      (.const declaredName) (.head .legacyGround) := by
  refine ⟨.nil, ?_⟩
  exact Typing.const (R := formedDeclarationRules) (Γ := .nil)
    (name := declaredName) (type := .head .legacyGround) (u := .sort Tower.zero) rfl
    (.headType Tower.HeadTyping.legacyGround) (Tower.IsUniverse.sort Tower.zero)

/-- The contrasting raw signature names an absent constant as the declared
type. Its universe rules and computation are otherwise unchanged. -/
def danglingDeclarationRules : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = declaredName then some (.const missingName) else none }

/-- Raw constant typing consults only the declared type lookup. -/
theorem raw_accepts_dangling_declaration :
    HasType danglingDeclarationRules (.nil : Tower.Ctx 0)
      (.const declaredName) (.const missingName) := by
  exact HasType.const (R := danglingDeclarationRules) (Γ := .nil)
    (name := declaredName) (type := .const missingName) rfl

/-- No conversion or cumulative tail can repair the missing closed
declaration-type formation needed by the refined constant rule. -/
theorem rejects_dangling_declaration {Γ : Tower.Ctx n} {type : Tower.Tm n} :
    ¬ Typing danglingDeclarationRules Γ (.const declaredName) type := by
  intro typing
  obtain ⟨declaredType, u, lookup, formed, _⟩ := typing.constFormation
  have typeEquality : declaredType = .const missingName := by
    change some (.const missingName) = some declaredType at lookup
    exact Option.some.inj lookup.symm
  subst declaredType
  obtain ⟨_, _, missingLookup, _, _⟩ := formed.constFormation
  change (none : Option (Tower.Tm 0)) = some _ at missingLookup
  cases missingLookup

end Examples

#print axioms ContextFormation.lookup_formed
#print axioms Typing.constFormation
#print axioms Typing.piFormation
#print axioms Typing.sigmaFormation
#print axioms Typing.regularity
#print axioms Judgment.regularity
#print axioms Judgment.substitute
#print axioms Examples.formed_declaration_judgment
#print axioms Examples.raw_accepts_dangling_declaration
#print axioms Examples.rejects_dangling_declaration

end FormationSensitive
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
