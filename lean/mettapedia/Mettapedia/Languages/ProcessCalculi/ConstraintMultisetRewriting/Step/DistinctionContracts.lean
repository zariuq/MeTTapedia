import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionObserver
import Mettapedia.GSLT.Logic.ObserverRefinement
import Mettapedia.Cybernetics.DistinctionCalculus.GradedCongruence

/-!
# Scoped, context-indexed observation contracts

Protected readings expose predicate tests. This lets a coarse test translate
to a predicate of a finer reading even when it merges several fine values.
The existing observer-refinement category then transports exact certificates.
Certificates are indexed by the actual scoped system, not a free-standing
status or numeric grade.

Context saturation retains every declared contextual reading and is closed
under the existing monoid of contexts. No finite carrier or test family is
required. Exact compression of every possible state predicate is injective;
lost readings cannot be reconstructed from their codes alone.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionObserver
open Interface
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.Cybernetics.DistinctionCalculus

universe uOb uT uH uO uS uF uL uV uQ uW uC
variable {Obj : Type uOb} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uO} [DecidableEq O] {State : Type uS}
  {Fir : State → Type uF} {L : Type uL} {V : Type uV} {Q : Type uQ} {W : Type uW}
  (P : Interface.Step X O State Fir) (offers : L → (s : State) → Fir s → Prop)

/-- Tests are predicates of the protected reading; they need not be decidable. -/
def tests (read : State → V) : System (Race.Generic.gslt P offers) where
  Atom := V → Prop
  observes predicate s := predicate (read s)
  observes_resp := by intro predicate s t equal; cases equal; rfl
  Label := L
  act a s t := Race.Generic.Moves P offers s a t
  act_resp_left := (Race.Generic.system P offers).act_resp_left
  act_resp_right := (Race.Generic.system P offers).act_resp_right

/-- Predicate tests and literal value readings induce the same bisimulation contract. -/
theorem tests_bisimulation_iff (read : State → V) (R : State → State → Prop) :
    (tests P offers read).IsBisimulation R ↔ (observed P offers read).IsBisimulation R := by
  constructor
  · rintro ⟨forth, back, agrees⟩
    exact ⟨forth, back, fun s t related value => agrees related (· = value)⟩
  · rintro ⟨forth, back, agrees⟩
    refine ⟨forth, back, ?_⟩
    intro s t related predicate
    have equal : read s = read t := (agrees related (read t)).mpr rfl
    change predicate (read s) ↔ predicate (read t)
    rw [equal]

/-- Coarsening a reading is a genuine refinement of predicate-test systems. -/
def readingRefinement (read : State → V) (summarize : V → W) :
    ObserverRefinement (tests P offers (summarize ∘ read)) (tests P offers read) where
  mapAtom predicate := predicate ∘ summarize
  mapLabel := id
  observes_iff _ _ := Iff.rfl
  act_iff _ _ _ := Iff.rfl

section Scopes
universe uScope uAtom uLabel
variable {S : GSLT} {Scope : Type uScope}
  (views : Scope → System.{uAtom, uLabel} S)

/-- The scope selects the actual tests and dynamics whose kernel is certified. -/
def Certificate (scope : Scope) {Code : Type*} (encode : S.Term → Code) : Prop :=
  (views scope).IsBisimulation (fun s t => encode s = encode t)

/-- A proved observer comparison transports a certificate; a matching status cannot do so. -/
theorem certificate_forget {old fresh : Scope}
    (refinement : ObserverRefinement (views old) (views fresh)) {Code : Type*}
    {encode : S.Term → Code} (certified : Certificate views fresh encode) :
    Certificate views old encode := by
  obtain ⟨forth, back, observations⟩ := certified
  refine ⟨?_, ?_, ?_⟩
  · intro s t same label s' moved
    obtain ⟨t', moved', related⟩ := forth same (refinement.mapLabel label)
      ((refinement.act_iff label s s').mp moved)
    exact ⟨t', (refinement.act_iff label t t').mpr moved', related⟩
  · intro s t same label t' moved
    obtain ⟨s', moved', related⟩ := back same (refinement.mapLabel label)
      ((refinement.act_iff label t t').mp moved)
    exact ⟨s', (refinement.act_iff label s s').mpr moved', related⟩
  · intro s t same atom
    exact (refinement.observes_iff atom s).trans
      ((observations same (refinement.mapAtom atom)).trans (refinement.observes_iff atom t).symm)

end Scopes

/-- Exactness at a finer reading licenses every postcomposed reading. -/
theorem exact_postcompose (encode : State → Q) (read : State → V) (summarize : V → W)
    (certified : Stable P offers encode ∧ Reads encode read) :
    Stable P offers encode ∧ Reads encode (summarize ∘ read) :=
  ⟨certified.1, fun s t same => congrArg summarize (certified.2 s t same)⟩

section Contexts
variable {C : Type uC} (contexts : ContextMonoid C State)

def contextRead (read : State → V) (s : State) : C → V := fun c => read (contexts.act c s)

/-- The identity context recovers the ordinary reading. -/
theorem contextRead_unit (read : State → V) (s : State) :
    contextRead contexts read s contexts.unit = read s := by
  simp [contextRead, contexts.act_unit]

/-- Saturating a reading under contexts makes its kernel context-closed. -/
theorem contextRead_closed (read : State → V) {s t : State}
    (same : contextRead contexts read s = contextRead contexts read t) (c : C) :
    contextRead contexts read (contexts.act c s) = contextRead contexts read (contexts.act c t) := by
  funext d
  have h := congrFun same (contexts.mul d c)
  simpa only [contextRead, contexts.act_mul] using h

/-- The saturated reading is the coarsest kernel closed under these contexts that protects read. -/
theorem contextRead_universal (read : State → V) (R : State → State → Prop)
    (protects : ∀ s t, R s t → read s = read t)
    (closed : ∀ c s t, R s t → R (contexts.act c s) (contexts.act c t))
    {s t : State} (related : R s t) : contextRead contexts read s = contextRead contexts read t :=
  funext fun c => protects _ _ (closed c s t related)

/-- Context compatibility upgrades the old exact certificate to all declared contextual tests. -/
theorem exact_contextRead (encode : State → Q) (read : State → V)
    (certified : Stable P offers encode ∧ Reads encode read)
    (closed : ∀ c s t, encode s = encode t → encode (contexts.act c s) = encode (contexts.act c t)) :
    Stable P offers encode ∧ Reads encode (contextRead contexts read) := by
  refine ⟨certified.1, ?_⟩
  intro s t same
  exact funext fun c => certified.2 _ _ (closed c s t same)

end Contexts

omit [DecidableEq O] in
theorem all_predicates_iff_injective {S Q : Type*} (encode : S → Q) :
    (∀ p : S → Prop, ∀ s t, encode s = encode t → (p s ↔ p t)) ↔
      Function.Injective encode := by
  constructor
  · intro protects s t same
    exact ((protects (fun x => x = s) s t same).mp rfl).symm
  · intro injective p s t same
    cases injective same
    rfl

omit [DecidableEq O] in
theorem lost_reading_has_no_decoder {S Q V : Type*} (encode : S → Q) (read : S → V)
    {s t : S} (same : encode s = encode t) (different : read s ≠ read t) :
    ¬ ∃ decode : Q → V, ∀ x, decode (encode x) = read x := by
  rintro ⟨decode, exactRead⟩
  apply different
  calc
    read s = decode (encode s) := (exactRead s).symm
    _ = decode (encode t) := congrArg decode same
    _ = read t := exactRead t

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionObserver
