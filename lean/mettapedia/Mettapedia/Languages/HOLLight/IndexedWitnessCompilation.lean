import Mettapedia.Logic.HOL.IndexedWitnessProofs
import Mettapedia.Languages.HOLLight.InterpretedCompilation

/-!
# Shared native compilation of indexed witness consumption

The family, root, motive and witness-scoped evidence are parameters. The
three original premises stay explicit and all logical inferences are retained.
No index-selection or functionality rule is added to the checking kernel.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.IndexedWitnessCompilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v} {Γ : HOL.Ctx Base}
    {space index : HOL.Ty Base}
    (family : HOL.Term Const Γ (space ⇒ .prop))
    (root property : HOL.Term Const Γ (space ⇒ index ⇒ .prop))
    (point : HOL.Term Const Γ space) (evidence : HOL.Formula Const (index :: Γ))

def assumptions : List (HOL.Formula Const Γ) :=
  [.app family point, .app (IndexedPredicateInduction.lift root property) point,
    IndexedWitnessProofs.rootWitness root point evidence]

def conclusion : HOL.Formula Const Γ :=
  IndexedWitnessProofs.indexedWitness family root property point evidence

def proof : HOL.ProofSyntax Const (assumptions family root property point evidence)
    (conclusion family root property point evidence) :=
  IndexedWitnessProofs.consume family root property point evidence
    (.hyp (Δ := assumptions family root property point evidence) ⟨0, by simp [assumptions]⟩)
    (.hyp (Δ := assumptions family root property point evidence) ⟨1, by simp [assumptions]⟩)
    (.hyp (Δ := assumptions family root property point evidence) ⟨2, by simp [assumptions]⟩)

theorem proof_free : (proof family root property point evidence).FunctionExtensionalityFree := by
  unfold proof
  apply IndexedWitnessProofs.consume_free <;> trivial

variable (interpretation : HOL.TermInterpretation Base Const AtomicTy Symbol)

@[irreducible, noinline] def compile
    (names : ReverseTranslation.Naming (Γ.map (HOL.Ty.substitute interpretation.types))) :
    RetainedCompilation.Compiled emptyAxiomPolicy names
      (((assumptions family root property point evidence).map interpretation.term).map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand (interpretation.term (conclusion family root property point evidence))) :=
  InterpretedCompilation.compile interpretation (proof family root property point evidence)
    (proof_free family root property point evidence) names ("indexed-witness-consumption", 0)

#print axioms proof_free
#print axioms compile

end Mettapedia.Languages.HOLLight.IndexedWitnessCompilation
