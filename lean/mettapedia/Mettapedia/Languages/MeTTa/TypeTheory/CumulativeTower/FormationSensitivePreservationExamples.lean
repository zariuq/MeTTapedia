import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitivePreservationInstances
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DefinitionalExpansionExamples

/-!
# Contextual preservation with real dependent consumers

The actual transparent signature satisfies the primitive body obligations;
its arbitrary finite runs preserve refined judgments. Consumers reduce a
dependent pair's type component, project its value, and compute in a binder
domain. A negative signature preserves conversion classes but supplies a body
of the wrong declared type, refuting preservation without body checking.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive.PreservationExamples

open Declaration
open ConstantExpansion.Examples
open Dependencies.Examples (aliasName valueName extraName ground extraBody)

variable {n : Nat}

/-- Every transparent body is checked against the actual declaration type,
including the body of the second alias. The opaque value supplies no delta. -/
theorem actual_bodies_checked (name : DeclName) (body : Tower.Tm 0)
    (lookup : signature.valueOf? name = some body) :
    ∃ declared, rules.constantType name = some declared ∧ Typing rules .nil body declared := by
  simp only [signature, Signature.ofList, List.foldr, Signature.insert,
    Signature.empty, Signature.valueOf?] at lookup
  split at lookup
  · next same =>
      subst name
      cases lookup
      exact ⟨sortTm Tower.zero, by decide, .headType .legacyGround⟩
  · next first =>
      split at lookup
      · next same =>
          subst name
          cases lookup
          have known : rules.constantType aliasName = some (sortTm Tower.zero) := by decide
          exact ⟨sortTm Tower.zero, by decide,
            .const known (.headType (Tower.HeadTyping.sort Tower.zero)) (Tower.IsUniverse.sort _)⟩
      · next second =>
          split at lookup
          · simp at lookup
          · split at lookup
            · next same =>
                subst name
                cases lookup
                exact ⟨Examples.polymorphicIdentityType Tower.zero, by decide, identity_body_typed .nil⟩
            · simp at lookup

/-- Full contextual preservation for this nonempty signature. No root
preservation or constructor-boundary hypothesis remains. -/
theorem actual_runs_preserve {Γ : Tower.Ctx n} {source target type : Tower.Tm n}
    (judgment : Judgment rules Γ source type)
    (steps : ConversionCoherence.StepStar rules source target) : Judgment rules Γ target type :=
  judgment.steps_preserve_definitions rfl rfl towerUniverseRegularity towerHeadPreservation
    Tower.headEq_symmetric qualification actual_bodies_checked steps

def packedType : Tower.Tm n := .sigma (sortTm Tower.zero) (.var 0)
def packedValue : Tower.Tm n := .pair (.const secondAliasName) (.const valueName)

theorem packedType_formed (Γ : Tower.Ctx n) :
    Typing rules Γ packedType (sortTm (.max (.succ Tower.zero) Tower.zero)) :=
  .sigmaForm (.headType (.sort _)) (.sort _) (.var 0) (.sort _) (.sorts _ _)

theorem packedValue_typed (Γ : Tower.Ctx n) : Typing rules Γ packedValue packedType :=
  .pairIntro (packedType_formed Γ) (.sort _) (alias_formed Γ) (value_at_alias Γ)

/-- Reducing the pair's first component changes the type demanded of its
second component. The preservation theorem transports that demand. -/
theorem packed_first_reduction :
    Step rules.headEq (packedValue : Tower.Tm 0)
      (.pair (.const aliasName) (.const valueName)) rules.computation ∧
    Judgment rules .nil (.pair (.const aliasName) (.const valueName)) packedType := by
  have lookup : signature.valueOf? secondAliasName = some (.const aliasName) := by decide
  have step : Step rules.headEq (packedValue : Tower.Tm 0)
      (.pair (.const aliasName) (.const valueName)) rules.computation :=
    .congPairFst (.root (.delta lookup))
  exact ⟨step, actual_runs_preserve ⟨.nil, packedValue_typed .nil⟩ (.tail .refl step)⟩

/-- The second projection's displayed type is itself a computation, the
first projection of the dependent pair; it is retained exactly. -/
theorem packed_second_projection :
    Judgment rules .nil (.const valueName : Tower.Tm 0) (.fst packedValue) := by
  have source : Judgment rules (.nil : Tower.Ctx 0) (.snd packedValue) (.fst packedValue) :=
    ⟨.nil, .sndElim (packedValue_typed .nil)⟩
  exact actual_runs_preserve source
    (.tail .refl (.betaSigmaSnd (.const secondAliasName) (.const valueName)))

def domainRedex : Tower.Tm n := .app (.lam (.var 0)) (sortTm Tower.zero)

theorem domainRedex_typed (Γ : Tower.Ctx n) :
    Typing Tower.rules Γ domainRedex (sortTm (.succ Tower.zero)) := by
  have formed : Typing Tower.rules Γ
      (.pi (sortTm (.succ Tower.zero)) (sortTm (.succ Tower.zero)))
      (sortTm (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))) :=
    .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)
  have identity : Typing Tower.rules Γ (.lam (.var 0))
      (.pi (sortTm (.succ Tower.zero)) (sortTm (.succ Tower.zero))) :=
    .lamIntro formed (.sort _) (.var 0)
  exact .appElim identity (.headType (.sort _))

/-- Computing in the binder domain of Pi X : (id U0). X preserves
the formation derivation, including the body's dependent variable. -/
theorem binder_domain_reduction :
    Judgment Tower.rules (.nil : Tower.Ctx 0) (.pi (sortTm Tower.zero) (.var 0))
      (sortTm (.max (.succ Tower.zero) Tower.zero)) := by
  have conversion : Conv Tower.HeadEq (domainRedex : Tower.Tm 0) (sortTm Tower.zero) :=
    .rel _ _ (.betaPi (.var 0) (sortTm Tower.zero))
  have body : Typing Tower.rules (.snoc .nil (domainRedex : Tower.Tm 0))
      (.var 0) (sortTm Tower.zero) :=
    .conv (.var 0) (.headType (.sort _)) (.sort _) (conversion.renameTerms wk)
  have source : Judgment Tower.rules (.nil : Tower.Ctx 0) (.pi domainRedex (.var 0))
      (sortTm (.max (.succ Tower.zero) Tower.zero)) :=
    ⟨.nil, .piForm (domainRedex_typed .nil) (.sort _) body (.sort _) (.sorts _ _)⟩
  exact source.steps_preserve_tower
    (.tail .refl (.congPiDom (.betaPi (.var 0) (sortTm Tower.zero))))

namespace WrongBody

def name : DeclName := `PreservationExample.wrongBody
def body : Tower.Tm n := .lam (.var 0)
def signature : Signature Tower.Head :=
  Signature.ofList [(name, ⟨ground, some body⟩)]
def rules : Rules Tower.Head := extendRules Tower.rules signature
def bodies : ConstantExpansion.Bodies Tower.Head :=
  fun c => if c = name then body else .const c

private theorem lookup : signature.valueOf? name = some (body : Tower.Tm 0) := by decide

/-- Conversion qualification alone does not check the type of a body. -/
def qualification : ConstantExpansion.Qualification rules :=
  ConstantExpansion.Qualification.ofSignature Tower.rules signature rfl bodies
    (by
      intro c
      by_cases same : c = name
      · subst c
        change Conv Tower.HeadEq (.const name) (body : Tower.Tm 0) rules.computation
        exact .rel _ _ (.root (RootStep.delta (base := Tower.rules) (n := 0) lookup))
      · simp only [bodies, if_neg same]
        exact .refl _)
    (by
      intro c value known
      by_cases same : c = name
      · subst c
        rw [lookup] at known
        cases known
        change Conv Tower.HeadEq (body : Tower.Tm 0) body
        exact .refl _
      · simp [signature, Signature.ofList, Signature.valueOf?, Signature.insert,
          Signature.empty, same] at known)
    (by intro k left right impossible; exact impossible.elim)

theorem source_typed : Judgment rules (.nil : Tower.Ctx 0) (.const name) ground := by
  have known : rules.constantType name = some (ground : Tower.Tm 0) := by decide
  exact ⟨.nil, .const known (.headType .legacyGround) (.sort _)⟩

theorem body_not_typed {Γ : Tower.Ctx n} : ¬ Typing rules Γ body ground := by
  intro typing
  obtain ⟨A, B, u, formed, universeWitness, inner, adjustment⟩ := typing.lamGeneration
  have boundary := qualification.piConversionBoundary Tower.headEq_symmetric
  exact boundary.headDisjoint
    (adjustment.toConvOfSourceDisjointHeads (fun _ => boundary.headDisjoint))

/-- The actual delta step violates typing preservation, despite a formed
declared type and a conversion qualification for the whole signature. -/
theorem no_root_preservation : ¬ RootPreservation rules := by
  intro preserves
  exact body_not_typed (preserves .nil source_typed.typing
    (RootStep.delta (base := Tower.rules) (n := 0) lookup))

end WrongBody

#print axioms actual_bodies_checked
#print axioms actual_runs_preserve
#print axioms packedType_formed
#print axioms packedValue_typed
#print axioms packed_first_reduction
#print axioms packed_second_projection
#print axioms domainRedex_typed
#print axioms binder_domain_reduction
#print axioms WrongBody.qualification
#print axioms WrongBody.source_typed
#print axioms WrongBody.body_not_typed
#print axioms WrongBody.no_root_preservation

end FormationSensitive.PreservationExamples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
