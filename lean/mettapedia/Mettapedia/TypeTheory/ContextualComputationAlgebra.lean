import Mettapedia.TypeTheory.ContextualKleisliAdjunction

/-!
# Contextual computation algebras and the free-computation embedding

The computation objects here are Mathlib's Eilenberg--Moore algebras for the
monad already induced by the contextual Kleisli adjunction. Mathlib supplies
their free/forgetful adjunction. The comparison functor embeds the existing
Kleisli category as free algebras; its arrows act by the existing `Program.bind`.

Evaluating an algebra homomorphism at pure inputs recovers its Kleisli arrow.
The converse uses the algebra homomorphism law, so arbitrary carrier functions
are not mistaken for computation morphisms. Full faithfulness retains the
literal programs, including choice occurrences and intents; there is no effect
quotient or replacement evaluator. This is a candidate semantic interface, not
adoption of a full dependent CBPV calculus or an implementation of Need sharing.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualComputationAlgebra

open CategoryTheory
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open ContextualComputationKleisli (Object)
open ContextualKleisliAdjunction (inducedMonad)

universe u

/-- Existing contextual monad algebras, with no additional representation. -/
abbrev Algebra (State Intent : Type u) := (inducedMonad State Intent).Algebra

def free (State Intent : Type u) : Type u ⥤ Algebra State Intent :=
  (inducedMonad State Intent).free

def forget (State Intent : Type u) : Algebra State Intent ⥤ Type u :=
  (inducedMonad State Intent).forget

/-- The standard Eilenberg--Moore adjunction for the actual contextual monad. -/
def adjunction (State Intent : Type u) : free State Intent ⊣ forget State Intent :=
  (inducedMonad State Intent).adj

/-- Mathlib's comparison functor, specialized to the existing Kleisli adjunction. -/
def embedding (State Intent : Type u) : Object State Intent ⥤ Algebra State Intent :=
  Monad.comparison (ContextualKleisliAdjunction.adjunction State Intent)

variable {State Intent : Type u}

theorem embedding_obj (object : Object State Intent) :
    (embedding State Intent).obj object = (free State Intent).obj object.Carrier :=
  rfl

/-- The action of a free algebra is precisely flattening with actual bind. -/
theorem free_action {Answer : Type u}
    (program : Program State (Program State Answer Intent) Intent) :
    ((free State Intent).obj Answer).a program = Program.bind program (fun next => next) :=
  rfl

theorem free_map {Answer OtherAnswer : Type u} (function : Answer → OtherAnswer)
    (program : Program State Answer Intent) :
    ((free State Intent).map (TypeCat.ofHom function)).f program =
      Program.map function program :=
  rfl

/-- The original arrow encoded as a homomorphism between free algebras. -/
def encode {source target : Object State Intent} (arrow : source ⟶ target) :
    (embedding State Intent).obj source ⟶ (embedding State Intent).obj target :=
  (embedding State Intent).map arrow

@[simp] theorem encode_apply {source target : Object State Intent} (arrow : source ⟶ target)
    (program : Program State source.Carrier Intent) :
    (encode arrow).f program = Program.bind program arrow.toFun :=
  rfl

/-- A free-algebra homomorphism is determined by its action on pure inputs. -/
def decode {source target : Object State Intent}
    (arrow : (embedding State Intent).obj source ⟶ (embedding State Intent).obj target) :
    source ⟶ target :=
  ⟨fun value => arrow.f (.pure value)⟩

@[simp] theorem decode_apply {source target : Object State Intent}
    (arrow : (embedding State Intent).obj source ⟶ (embedding State Intent).obj target)
    (value : source.Carrier) :
    (decode arrow).toFun value = arrow.f (.pure value) :=
  rfl

@[simp] theorem decode_encode {source target : Object State Intent} (arrow : source ⟶ target) :
    decode (encode arrow) = arrow := by
  apply Object.Hom.ext
  rfl

@[simp] theorem encode_decode {source target : Object State Intent}
    (arrow : (embedding State Intent).obj source ⟶ (embedding State Intent).obj target) :
    encode (decode arrow) = arrow := by
  apply Monad.Algebra.Hom.ext
  ext program
  have recovered := congrArg (fun current => current (Program.map Program.pure program)) arrow.h
  change Program.bind (Program.map arrow.f (Program.map Program.pure program))
      (fun next => next) =
    arrow.f (Program.bind (Program.map Program.pure program) (fun next => next)) at recovered
  change Program.bind program (fun value => arrow.f (.pure value)) = arrow.f program
  simpa only [Program.map, ContextualComputationKleisli.Program.bind_assoc,
    Program.pure_bind, ContextualComputationKleisli.Program.bind_pure] using recovered

/-- Explicit inverse data; fullness does not require choosing arrow preimages. -/
def fullyFaithful (State Intent : Type u) : (embedding State Intent).FullyFaithful where
  preimage := decode
  map_preimage := encode_decode
  preimage_map := decode_encode

instance (State Intent : Type u) : (embedding State Intent).Full :=
  (fullyFaithful State Intent).full

instance (State Intent : Type u) : (embedding State Intent).Faithful :=
  (fullyFaithful State Intent).faithful

def arrowEquiv (source target : Object State Intent) :
    (source ⟶ target) ≃
      ((embedding State Intent).obj source ⟶ (embedding State Intent).obj target) :=
  (fullyFaithful State Intent).homEquiv

theorem encode_injective (source target : Object State Intent) :
    Function.Injective (encode (source := source) (target := target)) :=
  (arrowEquiv source target).injective

@[simp] theorem encode_id (object : Object State Intent) :
    encode (𝟙 object) = 𝟙 ((embedding State Intent).obj object) :=
  (embedding State Intent).map_id object

theorem encode_comp {first middle last : Object State Intent}
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    encode (earlier ≫ later) = encode earlier ≫ encode later :=
  (embedding State Intent).map_comp earlier later

theorem decode_id (object : Object State Intent) :
    decode (𝟙 ((embedding State Intent).obj object)) = 𝟙 object :=
  (fullyFaithful State Intent).preimage_id

theorem decode_comp {first middle last : Object State Intent}
    (earlier : (embedding State Intent).obj first ⟶ (embedding State Intent).obj middle)
    (later : (embedding State Intent).obj middle ⟶ (embedding State Intent).obj last) :
    decode (earlier ≫ later) = decode earlier ≫ decode later :=
  (fullyFaithful State Intent).preimage_comp earlier later

/-- Algebraic composition retains the actual sequencing of contextual programs. -/
theorem encoded_sequencing {first middle last : Object State Intent}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (program : Program State first.Carrier Intent) :
    (encode earlier ≫ encode later).f program =
      Program.bind program (fun value => Program.bind (earlier.toFun value) later.toFun) :=
  ContextualComputationKleisli.Program.bind_assoc program earlier.toFun later.toFun

/-- The free/forgetful algebra adjunction recovers the existing contextual monad. -/
def inducedMonadIso (State Intent : Type u) :
    (adjunction State Intent).toMonad ≅ inducedMonad State Intent :=
  Adjunction.adjToMonadIso (inducedMonad State Intent)

theorem induced_sequencing {Answer OtherAnswer : Type u}
    (program : Program State Answer Intent)
    (next : Answer → Program State OtherAnswer Intent) :
    (adjunction State Intent).toMonad.μ.app OtherAnswer
      ((adjunction State Intent).toMonad.map (TypeCat.ofHom next) program) =
        Program.bind program next := by
  have multiplication := (inducedMonadIso State Intent).hom.app_μ OtherAnswer
  change (adjunction State Intent).toMonad.μ.app OtherAnswer ≫ 𝟙 _ =
    ((adjunction State Intent).toMonad.map (𝟙 _) ≫ 𝟙 _) ≫
      (inducedMonad State Intent).μ.app OtherAnswer at multiplication
  rw [(adjunction State Intent).toMonad.map_id] at multiplication
  simp only [Category.id_comp, Category.comp_id] at multiplication
  rw [multiplication]
  exact ContextualKleisliAdjunction.inducedMonad_bind State Intent program next

section Controls

abbrev UnitValue : Object Bool Nat := ⟨Unit⟩
abbrev BoolValue : Object Bool Nat := ⟨Bool⟩

/-- Both alternatives and their individual intents are retained by the embedding. -/
def choiceIntent : UnitValue ⟶ BoolValue :=
  ⟨fun _ => .choose (.intent 10 (.pure false)) (.intent 20 (.pure true))⟩

def pureFalse : UnitValue ⟶ BoolValue :=
  Object.Hom.ofFunction (fun _ => false)

theorem choiceIntent_encoded_observations :
    (runWorldsAt ((encode choiceIntent).f (.intent 7 (.pure ()))) false []).map
      (fun result => (result.branch, result.answer, result.state, result.intents)) =
        [([false], false, false, [7, 10]), ([true], true, false, [7, 20])] :=
  rfl

theorem choiceIntent_not_pure : encode choiceIntent ≠ encode pureFalse := by
  intro equal
  have arrowsEqual := encode_injective UnitValue BoolValue equal
  have programsEqual := congrArg (fun arrow => arrow.toFun ()) arrowsEqual
  cases programsEqual

theorem choiceIntent_roundtrip : decode (encode choiceIntent) = choiceIntent :=
  decode_encode choiceIntent

end Controls

#print axioms adjunction
#print axioms encode_decode
#print axioms fullyFaithful
#print axioms encoded_sequencing
#print axioms inducedMonadIso
#print axioms induced_sequencing
#print axioms choiceIntent_encoded_observations
#print axioms choiceIntent_not_pure

end Mettapedia.TypeTheory.ContextualComputationAlgebra
