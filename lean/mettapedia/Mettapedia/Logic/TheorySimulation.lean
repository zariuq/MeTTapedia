import Mettapedia.CategoryTheory.MorphismReachability
import Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory

/-!
# Simulation orders for semantic theory objects

`TheoryTranslation` is deliberately permissive: it records maps of kinds,
signatures, and claims that preserve theorem scope and meaning.  It does not by
itself assert preservation of the additional syntax needed by a particular
logical interpretation.

Accordingly, comparison is indexed by a multiplicative morphism property.  The
unqualified semantic-simulation order admits every `TheoryTranslation`; the
conservative-simulation order additionally requires reflection of theorem
scope and meaning.  Arithmetic interpretations, logical embeddings, and other
structured comparisons can later supply stricter morphism properties without
changing the order construction.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheorySimulation

open Mettapedia.MorphismReachability
open Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe uKind uSignature uClaim

abbrev Object := TheoryObject.{uKind, uSignature, uClaim}

/-- The class of semantic theory translations that also reflect theorem scope
and independently supplied meaning. -/
def conservativeTranslations : _root_.CategoryTheory.MorphismProperty Object :=
  fun _source _target translation => translation.Conservative

instance conservativeTranslations_isMultiplicative :
    conservativeTranslations.IsMultiplicative where
  id_mem object := by
    constructor <;> intro kind claim assumption <;> exact assumption
  comp_mem earlier later earlierConservative laterConservative := by
    change (TheoryTranslation.comp earlier later).Conservative
    exact TheoryTranslation.Conservative.comp earlier later
      earlierConservative laterConservative

/-- `host` semantically simulates `guest` when some semantic theory
translation maps the guest into the host. -/
def SemanticallySimulates (host guest : Object) : Prop :=
  Reaches (⊤ : _root_.CategoryTheory.MorphismProperty Object) guest host

/-- `host` conservatively simulates `guest` when a scope- and
meaning-reflecting semantic translation maps the guest into the host. -/
def ConservativelySimulates (host guest : Object) : Prop :=
  Reaches conservativeTranslations guest host

/-- Semantic simulation is reflexive. -/
theorem semanticallySimulates_refl (theory : Object) :
    SemanticallySimulates theory theory :=
  reaches_refl (⊤ : _root_.CategoryTheory.MorphismProperty Object) theory

/-- Semantic simulations compose. -/
theorem semanticallySimulates_trans {first second third : Object}
    (secondSimulatesFirst : SemanticallySimulates second first)
    (thirdSimulatesSecond : SemanticallySimulates third second) :
    SemanticallySimulates third first :=
  reaches_trans (⊤ : _root_.CategoryTheory.MorphismProperty Object)
    secondSimulatesFirst thirdSimulatesSecond

/-- Conservative simulation is reflexive. -/
theorem conservativelySimulates_refl (theory : Object) :
    ConservativelySimulates theory theory :=
  reaches_refl conservativeTranslations theory

/-- Conservative simulations compose. -/
theorem conservativelySimulates_trans {first second third : Object}
    (secondSimulatesFirst : ConservativelySimulates second first)
    (thirdSimulatesSecond : ConservativelySimulates third second) :
    ConservativelySimulates third first :=
  reaches_trans conservativeTranslations
    secondSimulatesFirst thirdSimulatesSecond

/-- Every conservative simulation is a semantic simulation after forgetting
reflection. -/
theorem ConservativelySimulates.toSemanticallySimulates
    {host guest : Object} :
    ConservativelySimulates host guest → SemanticallySimulates host guest := by
  rintro ⟨translation, _conservative⟩
  exact ⟨translation, trivial⟩

/-- The explicit preorder obtained when all semantic translations are
admissible. -/
abbrev SemanticOrder :=
  Mettapedia.MorphismReachability.Order
    (⊤ : _root_.CategoryTheory.MorphismProperty Object)

/-- The explicit preorder obtained from conservative semantic translations. -/
abbrev ConservativeOrder :=
  Mettapedia.MorphismReachability.Order
    (conservativeTranslations : _root_.CategoryTheory.MorphismProperty Object)

/-- Mutual conservative simulation is equivalence in the induced preorder;
it is weaker than a specified categorical isomorphism. -/
def MutuallyConservativelySimulates (left right : Object) : Prop :=
  ConservativelySimulates left right ∧ ConservativelySimulates right left

theorem mutuallyConservativelySimulates_refl (theory : Object) :
    MutuallyConservativelySimulates theory theory :=
  ⟨conservativelySimulates_refl theory,
    conservativelySimulates_refl theory⟩

theorem MutuallyConservativelySimulates.symm {left right : Object}
    (bothDirections : MutuallyConservativelySimulates left right) :
    MutuallyConservativelySimulates right left :=
  ⟨bothDirections.2, bothDirections.1⟩

theorem MutuallyConservativelySimulates.trans
    {first second third : Object}
    (firstSecond : MutuallyConservativelySimulates first second)
    (secondThird : MutuallyConservativelySimulates second third) :
    MutuallyConservativelySimulates first third :=
  ⟨conservativelySimulates_trans secondThird.1 firstSecond.1,
    conservativelySimulates_trans firstSecond.2 secondThird.2⟩

/-! ## The morphism class matters -/

namespace Canary

/-- A base theory in which only `true` is in theorem scope and meaning. -/
def baseTheory : TheoryFamily Unit where
  Signature := Unit
  signatureOf := fun _kind => ()
  Claim := fun _kind => Bool
  Scope := fun _kind claim => claim = true
  Meaning := fun _kind claim => claim = true
  scope_sound := by intro _kind _claim inScope; exact inScope

/-- An extension in which both Boolean claims are in theorem scope and
meaning. -/
def extensionTheory : TheoryFamily Unit where
  Signature := Unit
  signatureOf := fun _kind => ()
  Claim := fun _kind => Bool
  Scope := fun _kind _claim => True
  Meaning := fun _kind _claim => True
  scope_sound := by intro _kind _claim _inScope; trivial

def baseObject : Object := ⟨Unit, baseTheory⟩
def extensionObject : Object := ⟨Unit, extensionTheory⟩

/-- The identity claim map embeds the base theorem scope into the extension. -/
def inclusion : baseObject ⟶ extensionObject where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro _kind; rfl
  mapClaim := fun _kind claim => claim
  scope_preserved := by intro _kind _claim _inScope; trivial
  meaning_preserved := by intro _kind _claim _meaningful; trivial

/-- Positive control: the extension semantically simulates the base. -/
theorem extension_semanticallySimulates_base :
    SemanticallySimulates extensionObject baseObject :=
  ⟨inclusion, trivial⟩

/-- The displayed inclusion is not conservative because the extension proves
the image of the base's false claim. -/
theorem inclusion_not_conservative :
    ¬ conservativeTranslations inclusion := by
  intro conservative
  have falseInBase := conservative.scope_reflecting () false (by trivial)
  change false = true at falseInBase
  exact Bool.noConfusion falseInBase

/-- Negative control: no alternative claim map can make the all-claims
extension a conservative simulator of the base theory. -/
theorem extension_not_conservativelySimulates_base :
    ¬ ConservativelySimulates extensionObject baseObject := by
  rintro ⟨translation, conservative⟩
  have falseInBase := conservative.scope_reflecting () false (by trivial)
  change false = true at falseInBase
  exact Bool.noConfusion falseInBase

end Canary

end Mettapedia.Logic.TheorySimulation
