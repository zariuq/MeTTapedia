import Mettapedia.Cybernetics.ObservedVariety
import Mettapedia.Enactive.Finite
import Mettapedia.Order.PrincipalCompletion

/-!
# Typed completion fibres

The completion of an aspect is retained as a dependent type before it is read
as a set or counted.  This is the informative form needed by open-ended Prime
relations: finite Bennett weakness is recovered as the cardinality of a finite
completion fibre, while proof-relevant answer occurrences remain a separate,
strictly finer layer.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive

universe uWorld uWorld'

namespace Completion

variable {World : Type uWorld} {layer : AbstractionLayer World}

/-- The dependent family of targets completing `source`. -/
abbrev Fibre (source : Aspect layer) : Type uWorld :=
  Mettapedia.Order.PrincipalCompletion.Fibre source

namespace Fibre

/-- Forget the completion witness while retaining its target. -/
def target {source : Aspect layer} (completion : Fibre source) : Aspect layer :=
  Mettapedia.Order.PrincipalCompletion.Fibre.target completion

/-- The typed completion fibre is exactly the subtype of the existing
set-valued principal completion cone. -/
def equivExtension (source : Aspect layer) :
    Fibre source ≃ ↥(extension source) where
  toFun completion :=
    ⟨completion.1, mem_extension.mpr completion.2⟩
  invFun completion :=
    ⟨completion.1, mem_extension.mp completion.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Refining a source can only remove completions.  The antitone law is kept
as an embedding of informative fibres rather than merely an inequality of
their cardinalities. -/
def contravariantEmbedding {left right : Aspect layer}
    (refines : left ≤ right) :
    Fibre right ↪ Fibre left :=
  Mettapedia.Order.PrincipalCompletion.Fibre.contravariantEmbedding refines

/-- An order isomorphism of aspect presentations transports the whole
completion fibre. -/
def congr {World' : Type uWorld'} {layer' : AbstractionLayer World'}
    (presentation : Aspect layer ≃o Aspect layer')
    (source : Aspect layer) :
    Fibre source ≃ Fibre (presentation source) :=
  Mettapedia.Order.PrincipalCompletion.Fibre.congr presentation source

/-- The exact change of presentation also preserves completion variety as an
observer-indexed family. -/
def exactPresentation {World' : Type uWorld'}
    {layer' : AbstractionLayer World'}
    (presentation : Aspect layer ≃o Aspect layer')
    (source : Aspect layer) :
    Mettapedia.Cybernetics.Observer.ExactPresentation
      (Mettapedia.Cybernetics.Observer.identity (Fibre source))
      (Mettapedia.Cybernetics.Observer.identity
        (Fibre (presentation source))) where
  stateEquiv := congr presentation source
  viewEquiv := congr presentation source
  observe_commutes := fun _ => rfl

end Fibre

end Completion

/-! ## Finite counting projection -/

namespace Finite.Completion

variable {World : Type uWorld} [Fintype World] [DecidableEq World]
  {layer : Finite.Layer World}

/-- The finite completion family.  Coercion to the extension finset is
deliberate: no additional completion relation is introduced. -/
abbrev Fibre (source : layer.Statement) : Type uWorld :=
  ↥(layer.extension source)

/-- Bennett weakness is exactly the cardinality readout of the finite typed
completion fibre. -/
theorem natCard_fibre (source : layer.Statement) :
    Nat.card (Fibre source) = layer.weakness source := by
  change Nat.card (↥(layer.extension source)) =
    (layer.extension source).card
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_coe (layer.extension source)

/-- The finite weakness antitone law is the cardinal readout of the structural
completion-fibre embedding. -/
def contravariantEmbedding {left right : layer.Statement}
    (refines : left.val ⊆ right.val) :
    Fibre right ↪ Fibre left where
  toFun completion :=
    ⟨completion.1, (Finite.Layer.mem_extension layer).mpr
      (refines.trans ((Finite.Layer.mem_extension layer).mp completion.2))⟩
  inj' := by
    intro first second equal
    exact Subtype.ext
      (congrArg (fun completion : Fibre left => completion.1) equal)

theorem natCard_fibre_antitone {left right : layer.Statement}
    (refines : left.val ⊆ right.val) :
    Nat.card (Fibre right) ≤ Nat.card (Fibre left) := by
  rw [natCard_fibre, natCard_fibre]
  exact Finite.Layer.weakness_antitone layer refines

/-- The finite-to-abstract aspect embedding is injective. -/
theorem statementToAbstract_injective :
    Function.Injective (Finite.Layer.Statement.toAbstract (layer := layer)) := by
  intro left right equal
  apply Subtype.ext
  apply Finset.Subset.antisymm
  · exact Finite.Layer.Statement.toAbstract_reflects layer (by rw [equal])
  · exact Finite.Layer.Statement.toAbstract_reflects layer (by rw [← equal])

/-- Embed a finite completion in the finiteness-free typed completion fibre. -/
def toAbstract (source : layer.Statement) :
    Fibre source →
      Mettapedia.Enactive.Completion.Fibre source.toAbstract :=
  fun completion =>
    ⟨completion.1.toAbstract,
      Finite.Layer.Statement.toAbstract_mono layer
        ((Finite.Layer.mem_extension layer).mp completion.2)⟩

/-- Finite completion embedding loses no completion identity. -/
theorem toAbstract_injective (source : layer.Statement) :
    Function.Injective (toAbstract source) := by
  intro left right equal
  apply Subtype.ext
  exact statementToAbstract_injective (congrArg Subtype.val equal)

end Finite.Completion

end Mettapedia.Enactive

#print axioms Mettapedia.Enactive.Completion.Fibre.exactPresentation
#print axioms Mettapedia.Enactive.Finite.Completion.natCard_fibre
#print axioms Mettapedia.Enactive.Finite.Completion.toAbstract_injective
