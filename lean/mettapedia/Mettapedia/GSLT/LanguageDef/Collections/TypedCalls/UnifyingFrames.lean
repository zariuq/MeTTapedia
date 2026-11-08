import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UnifyingRegions
import Mettapedia.Logic.LP.UnificationReadSupport

/-!
# Support-indexed frames across two-way binding

An unrelated frame may contain typed or declared values. It need not satisfy
a global uninterpreted-substitution invariant. A binding step affects only
variables in its two currently instantiated operands; observations whose
current supports avoid those variables remain exactly unchanged. Arbitrary
predicates, including closed type facts, therefore survive on those frames.

Supports are measured after applying the current substitution. Distinct
source names can point to the same logical variable, so source-name disjointness
alone is not an admission rule. These are model-level support laws; no claim is
made that a native contract scanner already records these dependencies.

The encoded first-order support treats grounded values as leaves. A native
closure, seal or resource may carry additional captured ports, even when its
visible syntax is ground. Native admission must exclude such values or expose
those ports through its codec/support relation; `Machines.CapturedBindingProjection`
formalizes why visible groundness alone is insufficient.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UnifyingFrames

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open UnifyingRegions

abbrev support (value : Atom) : Finset String := (UnifyAtoms.encode value).freeVars

def observedSupport (σ : Substitution) (recipe : Atom) : Finset String := support (substA σ recipe)

def bindSupport (σ : Substitution) (pattern : Pat) (value : Atom) : Finset String :=
  observedSupport σ pattern.toAtom ∪ observedSupport σ value

/-- The computed MGU fixes every observation outside its actual operands'
support. This does not require either operand to be uninterpreted. -/
theorem unify_preserves_frame {pattern value frame : Atom}
    {theta : Mettapedia.Logic.LP.Subst UnifyAtoms.sig}
    (unified : UnifyAtoms.unify pattern value = some theta)
    (separate : Disjoint (support frame) (support pattern ∪ support value)) :
    substA (UnifyAtoms.readBack theta) frame = frame := by
  have relevant := Mettapedia.Logic.LP.unifyTotal_relevantIdempotent
    [(UnifyAtoms.encode pattern, UnifyAtoms.encode value)] theta unified
  have fixed : theta.applyTerm (UnifyAtoms.encode frame) = UnifyAtoms.encode frame := by
    apply Mettapedia.Logic.LP.Subst.applyTerm_eq_self
    intro x occurs
    apply relevant.fixes x
    have notOccurs : x ∉ support pattern ∪ support value :=
      fun member => Finset.disjoint_left.mp separate occurs member
    simpa [Mettapedia.Logic.LP.eqVars, support] using notOccurs
  have decoded := congrArg UnifyAtoms.decode fixed
  rw [UnifyAtoms.decode_applyTerm, UnifyAtoms.decode_encode] at decoded
  exact decoded

/-- A binding preserves a framed observation precisely under an explicit
disjoint-support sufficient condition. -/
theorem bindPattern_preserves_frame {σ τ : Substitution} {pattern : Pat} {value frame : Atom}
    (bound : bindPattern σ pattern value = some τ)
    (separate : Disjoint (observedSupport σ frame) (bindSupport σ pattern value)) :
    substA τ frame = substA σ frame := by
  unfold bindPattern at bound
  cases unified : UnifyAtoms.unify (substA σ pattern.toAtom) (substA σ value) with
  | none => simp [unified] at bound
  | some theta =>
      have eq : compose (UnifyAtoms.readBack theta) σ = τ := by simpa [unified] using bound
      subst τ
      rw [← substA_compose]
      exact unify_preserves_frame unified separate

/-- Clean operands, not a globally clean frame, justify the clean MGU rule. -/
theorem bindPattern_clean_operands {Γ : Decls} {σ τ : Substitution}
    {pattern : Pat} {value : Atom}
    (patternClean : Uninterp Γ (substA σ pattern.toAtom))
    (valueClean : Uninterp Γ (substA σ value))
    (bound : bindPattern σ pattern value = some τ) :
    Extends Γ σ τ ∧ substA τ pattern.toAtom = substA τ value := by
  unfold bindPattern at bound
  cases unified : UnifyAtoms.unify (substA σ pattern.toAtom) (substA σ value) with
  | none => simp [unified] at bound
  | some theta =>
      have eq : compose (UnifyAtoms.readBack theta) σ = τ := by simpa [unified] using bound
      subst τ
      have clean : Clean Γ (UnifyAtoms.readBack theta) :=
        UnifyAtoms.unify_uninterp unified patternClean valueClean
      refine ⟨⟨_, clean, rfl⟩, ?_⟩
      rw [← substA_compose, ← substA_compose]
      exact UnifyAtoms.unify_instance unified

/-- Every predicate on an unchanged observation is preserved. This includes
typing and ownership predicates without requiring a special transport axiom. -/
theorem bindPattern_preserves_predicate {σ τ : Substitution} {pattern : Pat} {value frame : Atom}
    (bound : bindPattern σ pattern value = some τ)
    (separate : Disjoint (observedSupport σ frame) (bindSupport σ pattern value))
    (predicate : Atom → Prop) (before : predicate (substA σ frame)) :
    predicate (substA τ frame) := by
  rw [bindPattern_preserves_frame bound separate]
  exact before

/-- A frame may be indexed by any type; only each observation's footprint
is relevant, not the size or the other contents of the frame. -/
theorem bindPattern_preserves_family {Index : Type} {σ τ : Substitution}
    {pattern : Pat} {value : Atom} (frame : Index → Atom) (predicate : Index → Atom → Prop)
    (bound : bindPattern σ pattern value = some τ)
    (separate : ∀ i, Disjoint (observedSupport σ (frame i)) (bindSupport σ pattern value))
    (before : ∀ i, predicate i (substA σ (frame i))) :
    ∀ i, predicate i (substA τ (frame i)) :=
  fun i => bindPattern_preserves_predicate bound (separate i) (predicate i) (before i)

theorem bindPattern_preserves_list {σ τ : Substitution} {pattern : Pat} {value : Atom}
    (frames : List Atom) (bound : bindPattern σ pattern value = some τ)
    (separate : ∀ frame ∈ frames, Disjoint (observedSupport σ frame) (bindSupport σ pattern value)) :
    frames.map (substA τ) = frames.map (substA σ) :=
  List.map_congr_left fun frame member => bindPattern_preserves_frame bound (separate frame member)

/-- Arbitrarily many closed formal types retain their actual entry facts.
The values may be open or contain declared constructors. -/
theorem bindPattern_preserves_entryFacts {Γ : Decls} {grounded : String → Bool}
    {σ τ : Substitution} {pattern : Pat} {value : Atom} (types : List (Ty Empty))
    (frames : List Atom) (bound : bindPattern σ pattern value = some τ)
    (separate : ∀ frame ∈ frames, Disjoint (observedSupport σ frame) (bindSupport σ pattern value))
    (before : EntryFacts Γ grounded types (frames.map (substA σ))) :
    EntryFacts Γ grounded types (frames.map (substA τ)) := by
  rw [bindPattern_preserves_list frames bound separate]
  exact before

/-- Ground frames are a consequence of the support law, not the frame
definition. They can contain arbitrary declared symbols. -/
theorem bindPattern_preserves_ground_frame {σ τ : Substitution} {pattern : Pat} {value frame : Atom}
    (bound : bindPattern σ pattern value = some τ)
    (ground : observedSupport σ frame = ∅) : substA τ frame = substA σ frame := by
  apply bindPattern_preserves_frame bound
  rw [ground]
  exact Finset.disjoint_empty_left _

structure Claim where
  recipe : Atom
  predicate : Atom → Prop

def Claim.Holds (σ : Substitution) (claim : Claim) : Prop := claim.predicate (substA σ claim.recipe)

/-- Invalidate only facts whose current observations may be changed by this
binding. This is a conservative executable dependency test. -/
def retained (σ : Substitution) (pattern : Pat) (value : Atom) (claims : List Claim) : List Claim :=
  claims.filter fun claim => decide
    (Disjoint (observedSupport σ claim.recipe) (bindSupport σ pattern value))

theorem retained_holds {σ τ : Substitution} {pattern : Pat} {value : Atom} {claims : List Claim}
    (bound : bindPattern σ pattern value = some τ)
    (before : ∀ claim ∈ claims, claim.Holds σ) :
    ∀ claim ∈ retained σ pattern value claims, claim.Holds τ := by
  intro claim member
  have parts := List.mem_filter.mp member
  have separate : Disjoint (observedSupport σ claim.recipe) (bindSupport σ pattern value) :=
    of_decide_eq_true parts.2
  exact bindPattern_preserves_predicate bound separate claim.predicate (before claim parts.1)

/-- A genuinely fresh logical binder and a ground value cannot change a
frame that does not mention that binder. Source spelling alone is not this
freshness condition: the current substitution and observed support matter. -/
theorem fresh_ground_binding_preserves {σ τ : Substitution} {name : String} {value frame : Atom}
    (fresh : σ name = .var name) (ground : support (substA σ value) = ∅)
    (absent : name ∉ observedSupport σ frame)
    (bound : bindPattern σ (.var name) value = some τ) : substA τ frame = substA σ frame := by
  apply bindPattern_preserves_frame bound
  change Disjoint (observedSupport σ frame)
    (support (substA σ (Atom.var name)) ∪ support (substA σ value))
  rw [substA, fresh, ground]
  simpa [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] using absent

namespace Controls

def declarations : Decls := fun name => if name = "Known" then [.sym "Tagged"] else []

def aliases : Substitution := fun name =>
  if name = "source-a" then .var "shared"
  else if name = "source-b" then .var "shared"
  else if name = "unrelated" then .symbol "Known"
  else .var name

def frame : Atom := .var "source-a"
def pattern : Pat := .var "source-b"
def value : Atom := .grounded (.int 7)
def openFrame : Atom := .expression [.symbol "Known", .var "outside"]

/-- Unrelated declared data makes global Clean false. -/
theorem global_clean_is_unnecessary : ¬ Clean declarations aliases := by
  intro clean
  have atKnown := clean "unrelated"
  simp [aliases, declarations, Uninterp, Safe] at atKnown

theorem operands_are_clean :
    Uninterp declarations (substA aliases pattern.toAtom) ∧
      Uninterp declarations (substA aliases value) := by
  constructor <;> trivial

/-- Distinct source names do not imply distinct current logical support. -/
theorem indirect_alias_not_separate :
    Disjoint (support frame) (support pattern.toAtom) ∧
      ¬ Disjoint (observedSupport aliases frame) (bindSupport aliases pattern value) := by
  decide +kernel

/-- The actual two-way update changes the indirectly aliased observation. -/
theorem indirect_alias_changes_frame :
    ((bindPattern aliases pattern value).map fun next => substA next frame) = some value ∧
      substA aliases frame = .var "shared" := by cbv

/-- An open frame with declared data but disjoint current support is kept. -/
theorem open_declared_frame_is_preserved :
    Disjoint (observedSupport aliases openFrame) (bindSupport aliases pattern value) ∧
      ((bindPattern aliases pattern value).map fun next => substA next openFrame) = some openFrame := by
  constructor
  · decide +kernel
  · cbv

def claims : List Claim :=
  [⟨frame, fun observed => observed = .var "shared"⟩,
   ⟨openFrame, fun observed => observed = openFrame⟩]

theorem only_affected_claim_is_invalidated :
    (retained aliases pattern value claims).map Claim.recipe = [openFrame] := by cbv

theorem fresh_ground_interpreted_value_preserves_frame :
    ((bindPattern Atom.var (.var "fresh") (.symbol "Known")).map
      fun next => substA next openFrame) = some openFrame := by cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UnifyingFrames
