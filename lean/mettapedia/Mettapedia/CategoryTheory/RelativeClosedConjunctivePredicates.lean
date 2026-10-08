import Mettapedia.CategoryTheory.RelativeClosedConjunctivePresentation
import Mathlib.Order.Lattice

/-!
# Generated conjunctive predicates and satisfying contexts

Predicates are complete arrows into the authored proposition object, modulo
the generated equations. The four local declarations earn their actual
meet-semilattice order and truth. Substitution preserves both operations.
The satisfying context of a predicate is its genuine equalizer with truth,
with monic inclusion and the full guarded-arrow factorization bijection.

These predicates are the definable fragment. No assertion identifies them
with every subobject of the generated category.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctive.Predicates

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory

universe k

variable {C : Type k} [Category.{k} C]

def propositionObject : Object (lawfulSignature (C := C)) :=
  (equationInclusion (C := C)).object omega

def conjunction : product (propositionObject (C := C)) propositionObject ⟶ propositionObject :=
  (equationInclusion (C := C)).functor.map (classOf conjunctionRaw)

def truth : terminal (lawfulSignature (C := C)) ⟶ propositionObject :=
  (equationInclusion (C := C)).functor.map (classOf truthRaw)

theorem commutative_diagram :
    pairing (second (propositionObject (C := C)) propositionObject) (first propositionObject propositionObject) ≫
      conjunction = conjunction := declared_law (C := C) (ULift.up .commutativity)

theorem associative_diagram :
    pairing (first (product (propositionObject (C := C)) propositionObject) propositionObject ≫ conjunction)
        (second (product propositionObject propositionObject) propositionObject) ≫ conjunction =
      pairing (first (product propositionObject propositionObject) propositionObject ≫
          first propositionObject propositionObject)
        (pairing (first (product propositionObject propositionObject) propositionObject ≫
            second propositionObject propositionObject)
          (second (product propositionObject propositionObject) propositionObject) ≫ conjunction) ≫ conjunction :=
  declared_law (C := C) (ULift.up .associativity)

theorem idempotent_diagram :
    pairing (𝟙 (propositionObject (C := C))) (𝟙 propositionObject) ≫ conjunction = 𝟙 propositionObject :=
  declared_law (C := C) (ULift.up .idempotence)

theorem truth_unit_diagram :
    pairing (𝟙 (propositionObject (C := C))) (toTerminal propositionObject ≫ truth) ≫ conjunction =
      𝟙 propositionObject := declared_law (C := C) (ULift.up .truthUnit)

def Fiber (context : Object (lawfulSignature (C := C))) := context ⟶ propositionObject

def meet {context : Object (lawfulSignature (C := C))} (before after : Fiber context) : Fiber context :=
  pairing before after ≫ conjunction

def top (context : Object (lawfulSignature (C := C))) : Fiber context := toTerminal context ≫ truth

theorem meet_comm {context : Object (lawfulSignature (C := C))} (before after : Fiber context) :
    meet before after = meet after before := by
  have same := congrArg (fun arrow => pairing before after ≫ arrow) (commutative_diagram (C := C))
  simpa only [← Category.assoc, pairing_precompose, pairing_first, pairing_second, meet] using same.symm

theorem meet_assoc {context : Object (lawfulSignature (C := C))} (first second third : Fiber context) :
    meet (meet first second) third = meet first (meet second third) := by
  have same := congrArg (fun arrow => pairing (pairing first second) third ≫ arrow)
    (associative_diagram (C := C))
  simpa only [← Category.assoc, pairing_precompose, pairing_first, pairing_second, meet] using same

theorem meet_idem {context : Object (lawfulSignature (C := C))} (predicate : Fiber context) :
    meet predicate predicate = predicate := by
  have same := congrArg (fun arrow => predicate ≫ arrow) (idempotent_diagram (C := C))
  simpa only [← Category.assoc, pairing_precompose, Category.comp_id, meet] using same

theorem terminal_naturality {context before : Object (lawfulSignature (C := C))} (mapping : context ⟶ before) :
    mapping ≫ toTerminal before = toTerminal context := toTerminal_unique _

theorem meet_top {context : Object (lawfulSignature (C := C))} (predicate : Fiber context) :
    meet predicate (top context) = predicate := by
  have same := congrArg (fun arrow => predicate ≫ arrow) (truth_unit_diagram (C := C))
  simpa only [← Category.assoc, pairing_precompose, Category.comp_id, terminal_naturality, meet, top] using same

instance fiberMin (context : Object (lawfulSignature (C := C))) : Min (Fiber context) := ⟨meet⟩

instance fiberSemilattice (context : Object (lawfulSignature (C := C))) : SemilatticeInf (Fiber context) :=
  SemilatticeInf.mk' meet_comm meet_assoc meet_idem

instance fiberTop (context : Object (lawfulSignature (C := C))) : OrderTop (Fiber context) where
  top := top context
  le_top predicate := (meet_comm _ _).trans (meet_top predicate)

theorem entails_iff_eq_top {context : Object (lawfulSignature (C := C))} (predicate : Fiber context) :
    ⊤ ≤ predicate ↔ predicate = ⊤ := ⟨fun evidence => le_antisymm le_top evidence, fun same => by rw [same]⟩

def reindex {context before : Object (lawfulSignature (C := C))} (mapping : context ⟶ before) :
    Fiber before → Fiber context := fun predicate => mapping ≫ predicate

theorem reindex_identity (context : Object (lawfulSignature (C := C))) (predicate : Fiber context) :
    reindex (𝟙 context) predicate = predicate := Category.id_comp predicate

theorem reindex_comp {context before after : Object (lawfulSignature (C := C))}
    (first : context ⟶ before) (second : before ⟶ after) (predicate : Fiber after) :
    reindex (first ≫ second) predicate = reindex first (reindex second predicate) := Category.assoc _ _ _

theorem reindex_top {context before : Object (lawfulSignature (C := C))} (mapping : context ⟶ before) :
    reindex mapping ⊤ = ⊤ := by
  change mapping ≫ (toTerminal before ≫ truth) = toTerminal context ≫ truth
  rw [← Category.assoc, terminal_naturality]

theorem reindex_meet {context before : Object (lawfulSignature (C := C))}
    (mapping : context ⟶ before) (first second : Fiber before) :
    reindex mapping (first ⊓ second) = reindex mapping first ⊓ reindex mapping second := by
  change mapping ≫ (pairing first second ≫ conjunction) =
    pairing (mapping ≫ first) (mapping ≫ second) ≫ conjunction
  rw [← Category.assoc, pairing_precompose]

theorem reindex_mono {context before : Object (lawfulSignature (C := C))}
    (mapping : context ⟶ before) : Monotone (reindex mapping) := by
  intro first second ordered
  change reindex mapping second ⊓ reindex mapping first = reindex mapping first
  rw [← reindex_meet, ordered]

def satisfying {context : Object (lawfulSignature (C := C))} (predicate : Fiber context) :
    Object (lawfulSignature (C := C)) := equalizerObject predicate (top context)

def inclusion {context : Object (lawfulSignature (C := C))} (predicate : Fiber context) :
    satisfying predicate ⟶ context := equalizerInclusion predicate (top context)

instance inclusion_mono {context : Object (lawfulSignature (C := C))} (predicate : Fiber context) :
    Mono (inclusion predicate) := equalizerInclusion_mono _ _

theorem inclusion_satisfies {context : Object (lawfulSignature (C := C))} (predicate : Fiber context) :
    reindex (inclusion predicate) predicate = ⊤ :=
  (equalizer_condition predicate (top context)).trans (reindex_top (inclusion predicate))

def factor {context before : Object (lawfulSignature (C := C))} (predicate : Fiber before)
    (mapping : context ⟶ before) (evidence : reindex mapping predicate = ⊤) : context ⟶ satisfying predicate :=
  equalizerLift predicate (top before) mapping (evidence.trans (reindex_top mapping).symm)

theorem factor_inclusion {context before : Object (lawfulSignature (C := C))} (predicate : Fiber before)
    (mapping : context ⟶ before) (evidence : reindex mapping predicate = ⊤) :
    factor predicate mapping evidence ≫ inclusion predicate = mapping := equalizerLift_inclusion _ _ _ _

def factorization {context before : Object (lawfulSignature (C := C))} (predicate : Fiber before) :
    (context ⟶ satisfying predicate) ≃ {mapping : context ⟶ before // reindex mapping predicate = ⊤} where
  toFun mapping := ⟨mapping ≫ inclusion predicate, by
    rw [reindex_comp, inclusion_satisfies, reindex_top]⟩
  invFun mapping := factor predicate mapping.val mapping.property
  left_inv mapping := (cancel_mono (inclusion predicate)).mp (factor_inclusion _ _ _)
  right_inv mapping := Subtype.ext (factor_inclusion _ _ _)

end Mettapedia.CategoryTheory.RelativeClosedConjunctive.Predicates
