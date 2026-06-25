import Mettapedia.Logic.Metaphysics.UltrainfinitismCore
import Mettapedia.Logic.Metaphysics.UltrainfinitismTwoSemantics
import Mettapedia.Logic.Metaphysics.SiderNihilism
import Mettapedia.KR.ConceptOntology.ConstructionBase
import Mettapedia.KR.ConceptGeometry.AbstractInheritance

/-!
# The dial weld: one dial across the ultrafilter, concept, and world layers

The open/closed-world dial appears in three vocabularies across the library. This file
proves they are the **same dial**:

* **Concept layer = ultrafilter layer.** A concept is open-world in the credal sense
  (`openWorldConcept`, membership in the scrutability gap) **iff** its gate-verdict
  family is `OpenFamily` (`openWorldConcept_iff_openFamily`); it is That's-All **iff**
  the family is `PreciseFamily` (`thatsAllConcept_iff_preciseFamily`) — Codex's
  concept-state dial and the ultrainfinitist perspectival dial are provably one.
* **Finite evidence = principal shadows.** Over a finite index every ultrafilter is
  principal (`Ultrafilter.eq_pure_of_finite`), so every perspective on a finite gate
  family is some gate's own verdict (`ultraTrue_of_finite`). Together with the
  finite-stage atomicity of frontiers
  (`Mettapedia.Foundations.Gunk.not_isGunky_of_finite`), this is the theorem-pair form
  of "the finite is the principal shadow": **finite frontier ⟹ atomic; finite
  perspectives ⟹ all principal**. Gunk and free perspectives both live only in the
  limit.
* **World layer.** Every nontrivial Boolean world is a mereology
  (`BAWorld.toMereology`), and gunkiness transports definitionally, so the Cantor
  witness serves the Sider argument and the two-semantics theorem at once.
-/

namespace Mettapedia.Logic.Metaphysics

open Mettapedia.Foundations.Gunk Mettapedia.KR.ConceptOntology
open Mettapedia.KR.ConceptGeometry

universe u v

/-! ## Finite evidence: only principal perspectives -/

/-- Over a finite index, every perspective is a coordinate's own verdict: the finite
has only principal shadows. (Companion to `Gunk.not_isGunky_of_finite`: finite
frontiers are atomic, finite perspective-spaces are principal — gunk and freedom both
need the limit.) -/
theorem ultraTrue_of_finite {I : Type u} [Finite I] (𝓤 : Ultrafilter I) (P : I → Prop) :
    ∃ i, (UltraTrue 𝓤 P ↔ P i) := by
  obtain ⟨i, hi⟩ := 𝓤.eq_pure_of_finite
  exact ⟨i, by rw [hi, ultraTrue_pure]⟩

/-! ## The concept-layer weld -/

section ConceptWeld

variable {Obj : Type u} {Attr : Type v} {Q : Type} {Gate : Type}
variable [Preorder Q] [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr]

/-- The gate-verdict family of a concept: which admissible gates form it. -/
def gateVerdict (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) : Gate → Prop :=
  fun g => A ∈ AbstractInheritance.finiteConceptFamily (Γ g) M

omit [Fintype Gate] [Nonempty Gate] in
/-- **The weld, open side.** A concept is credally open-world iff its gate-verdict
family is `OpenFamily`: some perspective forms it and some refuses — the concept-state
dial and the ultrafilter dial coincide. -/
theorem openWorldConcept_iff_openFamily
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) :
    openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A ↔
      OpenFamily (gateVerdict Γ M A) := by
  rw [openFamily_iff]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    by_contra hc
    push_neg at hc
    exact h.2 hc
  · intro h
    exact ⟨h.1, fun hall => by
      obtain ⟨g, hg⟩ := h.2
      exact hg (hall g)⟩

omit [Fintype Gate] [Nonempty Gate] in
/-- **The weld, That's-All side.** A concept is credally That's-All iff its
gate-verdict family is `PreciseFamily`: all perspectives agree — through the dial
dichotomy, in one step. -/
theorem thatsAllConcept_iff_preciseFamily
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) :
    thatsAllConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A ↔
      PreciseFamily (gateVerdict Γ M A) := by
  have h : thatsAllConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A ↔
      ¬ openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A :=
    Iff.rfl
  rw [h, openWorldConcept_iff_openFamily, openFamily_iff_not_precise, not_not]

omit [Nonempty Gate] in
/-- On a finite gate family every perspective on a concept's formation is a gate's own
verdict — the inference-layer principal-shadow theorem, at the concept interface. -/
theorem conceptVerdict_principal_of_finite
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) (𝓤 : Ultrafilter Gate) :
    ∃ g, (UltraTrue 𝓤 (gateVerdict Γ M A) ↔ gateVerdict Γ M A g) :=
  ultraTrue_of_finite 𝓤 (gateVerdict Γ M A)

end ConceptWeld

/-! ## The world-layer weld -/

/-- Every nontrivial Boolean world is a mereology. -/
def BAWorld.toMereology (W : BAWorld) (h : Nontrivial W.carrier) : Mereology :=
  letI := h
  { carrier := W.carrier }

/-- Gunkiness transports definitionally between the two world presentations. -/
theorem gunky_toMereology_iff (W : BAWorld) (h : Nontrivial W.carrier) :
    Gunky (W.toMereology h) ↔ IsGunky W.carrier :=
  Iff.rfl

/-- The Cantor witness, read as a mereology: one gunky world serving the
two-semantics theorem and the Sider argument at once. -/
theorem cantorWorld_toMereology_gunky :
    Gunky (cantorWorld.toMereology (nontrivial_of_ne ⊥ ⊤ cantorWorld_bot_ne_top)) :=
  isGunky_clopens_cantor

/-- Hence the Cantor world also refutes Sider's nihilism directly. -/
theorem cantorWorld_not_siderNihilism :
    ¬ SiderNihilism (cantorWorld.toMereology
      (nontrivial_of_ne ⊥ ⊤ cantorWorld_bot_ne_top)) :=
  gunky_not_siderNihilism cantorWorld_toMereology_gunky

end Mettapedia.Logic.Metaphysics
