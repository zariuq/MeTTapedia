import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Signature
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Contextual
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCanonicalCommutation

/-!
# The knowledge: name equivalence at closed names, nothing else

The frame action is the tree's contextual frames of the twin-binder signature: declaration
frames, contextual assignments, and their instantiation (`Interface.Frames.contextual`). Only the
equality of the knowledge is coarser than syntax.

* `Similar` (ground terms): the same term, except that a closed name (one whose read-back mentions
  no bound index from outside it and seals its quotes) may be replaced by a closed name structurally
  congruent to it (`StructuralCongruence` of the read-backs: the tree's equations of the calculus,
  among them quote-drop and the bag laws under a quote, which is the paper's name equivalence).
  Variables are compared as written, and so is the process structure of a row (its bags): the bag
  laws are not in the knowledge.
* `knowledge`: two terms at a frame are equal when every grounding of the frame makes them
  `Similar`. Instantiation preserves this by composition of groundings, so it is a frame action.
* `similar_sound`: `Similar` terms read back to structurally congruent patterns.
* `solvable_iff`: a store is solvable exactly when some grounding solves it.

Why exactly this equality, and not syntax or the whole equations, is stated in `ReactComparison`: syntactic
knowledge misses a communication through a received name, and the bag laws in the knowledge make
heating ambiguous (`Mechanisms.bag_laws_split_two_ways` of the `react` placement).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Interface.Frames (Frame)

/-- Ground terms. -/
abbrev G (Γ : Ctx sig) (s : Srt) : Type := Term (signature sig noUnknowns) Γ s

/-! ## Congruence of the source equations under the formers -/

theorem sc_apply_one (f : String) {a a' : Pattern} (same : StructuralCongruence a a') :
    StructuralCongruence (.apply f [a]) (.apply f [a']) := by
  refine StructuralCongruence.apply_cong f [a] [a'] rfl ?_
  intro i first _
  have zero : i = 0 := by simpa using first
  subst zero
  simpa using same

theorem sc_apply_two (f : String) {a a' b b' : Pattern} (first : StructuralCongruence a a')
    (second : StructuralCongruence b b') :
    StructuralCongruence (.apply f [a, b]) (.apply f [a', b']) := by
  refine StructuralCongruence.apply_cong f [a, b] [a', b'] rfl ?_
  intro i bound _
  have small : i < 2 := by simpa using bound
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simpa using first
  · simpa using second

theorem sc_pair (a a' b b' : Pattern) (first : StructuralCongruence a a')
    (second : StructuralCongruence b b') :
    StructuralCongruence (.collection .hashBag [a, b] none) (.collection .hashBag [a', b'] none) := by
  refine StructuralCongruence.par_cong [a, b] [a', b'] rfl ?_
  intro i bound _
  have small : i < 2 := by simpa using bound
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simpa using first
  · simpa using second

/-- A component before a bag, congruently: through `[p, bag]`, flattened. -/
theorem sc_cons {p p' : Pattern} {elements elements' : List Pattern}
    (head : StructuralCongruence p p')
    (tail : StructuralCongruence (.collection .hashBag elements none)
      (.collection .hashBag elements' none)) :
    StructuralCongruence (.collection .hashBag (p :: elements) none)
      (.collection .hashBag (p' :: elements') none) := by
  have unflatten : StructuralCongruence (.collection .hashBag (p :: elements) none)
      (.collection .hashBag [p, .collection .hashBag elements none] none) :=
    StructuralCongruence.symm _ _ (StructuralCongruence.par_flatten [p] elements)
  have flatten : StructuralCongruence (.collection .hashBag [p', .collection .hashBag elements' none] none)
      (.collection .hashBag (p' :: elements') none) :=
    StructuralCongruence.par_flatten [p'] elements'
  exact StructuralCongruence.trans _ _ _ unflatten
    (StructuralCongruence.trans _ _ _ (sc_pair _ _ _ _ head tail) flatten)

/-! ## Similar ground terms -/

/-- A ground term is **closed** when its read-back mentions no bound index from outside it and
seals its quotes. -/
abbrev Closed {Γ : Ctx sig} {s : Srt} (t : G Γ s) : Prop := binderSafeAt "NQuote" 0 (read t) = true

/-- **Similar ground terms**: the same term, except that a closed name may be replaced by a closed
name whose read-back is structurally congruent. Variables, and the process structure, are compared
as written. -/
inductive Similar : {Γ : Ctx sig} → {s : Srt} → G Γ s → G Γ s → Prop
  | var {Γ : Ctx sig} {s : Srt} (v : Var Γ s) : Similar (.var v) (.var v)
  | name {Γ : Ctx sig} {n m : G Γ .nm} : Closed n → Closed m →
      StructuralCongruence (read n) (read m) → Similar n m
  | zero {Γ : Ctx sig} : Similar (zeroT (Γ := Γ)) zeroT
  | bag {Γ : Ctx sig} {l l' : G Γ .ps} : Similar l l' → Similar (bagT l) (bagT l')
  | pnil {Γ : Ctx sig} : Similar (pnilT (Γ := Γ)) pnilT
  | pcons {Γ : Ctx sig} {p p' : G Γ .pr} {l l' : G Γ .ps} :
      Similar p p' → Similar l l' → Similar (pconsT p l) (pconsT p' l')
  | input {Γ : Ctx sig} {c c' : G Γ .nm} {b b' : G (.nm :: .pr :: Γ) .pr} :
      Similar c c' → Similar b b' → Similar (inputT c b) (inputT c' b')
  | output {Γ : Ctx sig} {c c' : G Γ .nm} {p p' : G Γ .pr} :
      Similar c c' → Similar p p' → Similar (outputT c p) (outputT c' p')
  | dropq {Γ : Ctx sig} {p p' : G Γ .pr} : Similar p p' → Similar (dropqT p) (dropqT p')
  | quote {Γ : Ctx sig} {p p' : G Γ .pr} : Similar p p' → Similar (quoteT p) (quoteT p')

theorem similar_refl : ∀ {Γ : Ctx sig} {s : Srt} (t : G Γ s), Similar t t
  | _, _, .var v => .var v
  | _, _, .op (.inl .zero) .nil => .zero
  | _, _, .op (.inl .bag) (.cons l .nil) => .bag (similar_refl l)
  | _, _, .op (.inl .pnil) .nil => .pnil
  | _, _, .op (.inl .pcons) (.cons p (.cons l .nil)) => .pcons (similar_refl p) (similar_refl l)
  | _, _, .op (.inl .input) (.cons c (.cons b .nil)) => .input (similar_refl c) (similar_refl b)
  | _, _, .op (.inl .output) (.cons c (.cons p .nil)) => .output (similar_refl c) (similar_refl p)
  | _, _, .op (.inl .dropq) (.cons p .nil) => .dropq (similar_refl p)
  | _, _, .op (.inl .quote) (.cons p .nil) => .quote (similar_refl p)
  | _, _, .op (.inr o) _ => o.key.elim

/-- **Similar terms read back to structurally congruent patterns.** -/
theorem similar_sound {Γ : Ctx sig} {s : Srt} {t t' : G Γ s} (similar : Similar t t') :
    StructuralCongruence (read t) (read t') := by
  induction similar with
  | var => exact StructuralCongruence.refl _
  | name _ _ same => exact same
  | zero => exact StructuralCongruence.refl _
  | bag _ inner => exact inner
  | pnil => exact StructuralCongruence.refl _
  | @pcons Γ p p' l l' _ _ head tail =>
      obtain ⟨elements, shape⟩ := read_ps_ground l
      obtain ⟨elements', shape'⟩ := read_ps_ground l'
      rw [shape, shape'] at tail
      rw [read_pcons, read_pcons, shape, shape']
      exact sc_cons head tail
  | input _ _ channel body =>
      rw [read_input, read_input]
      exact sc_apply_two _ channel (StructuralCongruence.lambda_cong _ _ _ body)
  | output _ _ channel payload =>
      rw [read_output, read_output]
      exact sc_apply_two _ channel payload
  | dropq _ inner =>
      rw [read_dropq, read_dropq]
      exact sc_apply_one _ (sc_apply_one _ inner)
  | quote _ inner =>
      rw [read_quote, read_quote]
      exact sc_apply_one _ inner

theorem similar_symm {Γ : Ctx sig} {s : Srt} {t t' : G Γ s} (similar : Similar t t') :
    Similar t' t := by
  induction similar with
  | var v => exact .var v
  | name closedN closedM same => exact .name closedM closedN (StructuralCongruence.symm _ _ same)
  | zero => exact .zero
  | bag _ inner => exact .bag inner
  | pnil => exact .pnil
  | pcons _ _ head tail => exact .pcons head tail
  | input _ _ channel body => exact .input channel body
  | output _ _ channel payload => exact .output channel payload
  | dropq _ inner => exact .dropq inner
  | quote _ inner => exact .quote inner

/-- **Similar terms are equally safe**, at every depth. -/
theorem similar_safe {Γ : Ctx sig} {s : Srt} {t t' : G Γ s} (similar : Similar t t') :
    ∀ depth, binderSafeAt "NQuote" depth (read t) = true →
      binderSafeAt "NQuote" depth (read t') = true := by
  induction similar with
  | var => exact fun _ safe => safe
  | name _ closedM _ => exact fun depth _ => binderSafeAt_mono "NQuote" closedM (Nat.zero_le depth)
  | zero => exact fun _ safe => safe
  | bag _ inner => exact inner
  | pnil => exact fun _ safe => safe
  | @pcons Γ p p' l l' _ _ head tail =>
      intro depth safe
      obtain ⟨elements, shape⟩ := read_ps_ground l
      obtain ⟨elements', shape'⟩ := read_ps_ground l'
      have unfolded : binderSafeAt "NQuote" depth (consBag (read p) (read l)) = true := safe
      rw [shape] at unfolded
      have parts : binderSafeAt "NQuote" depth (read p) = true ∧
          binderSafeListAt "NQuote" depth elements = true := by
        simpa [consBag, bagElements, binderSafeAt, binderSafeListAt] using unfolded
      have tailSafe := tail depth (by rw [shape]; simpa [binderSafeAt] using parts.2)
      rw [shape'] at tailSafe
      have tailList : binderSafeListAt "NQuote" depth elements' = true := by
        simpa [binderSafeAt] using tailSafe
      show binderSafeAt "NQuote" depth (consBag (read p') (read l')) = true
      rw [shape']
      simp [consBag, bagElements, binderSafeAt, binderSafeListAt, head depth parts.1, tailList]
  | @input Γ c c' b b' _ _ channel body =>
      intro depth safe
      have parts : binderSafeAt "NQuote" depth (read c) = true ∧
          binderSafeAt "NQuote" (depth + 1) (read b) = true := by
        rw [read_input] at safe
        simpa [binderSafeAt, binderSafeListAt] using safe
      rw [read_input]
      simp [binderSafeAt, binderSafeListAt, channel depth parts.1, body _ parts.2]
  | @output Γ c c' p p' _ _ channel payload =>
      intro depth safe
      have parts : binderSafeAt "NQuote" depth (read c) = true ∧
          binderSafeAt "NQuote" depth (read p) = true := by
        rw [read_output] at safe
        simpa [binderSafeAt, binderSafeListAt] using safe
      rw [read_output]
      simp [binderSafeAt, binderSafeListAt, channel depth parts.1, payload depth parts.2]
  | @dropq Γ p p' _ inner =>
      intro depth safe
      have part : binderSafeAt "NQuote" 0 (read p) = true := by
        rw [read_dropq] at safe
        simpa [binderSafeAt, binderSafeListAt] using safe
      rw [read_dropq]
      simp [binderSafeAt, binderSafeListAt, inner 0 part]
  | @quote Γ p p' _ inner =>
      intro depth safe
      have part : binderSafeAt "NQuote" 0 (read p) = true := by
        rw [read_quote] at safe
        simpa [binderSafeAt] using safe
      rw [read_quote]
      simp [binderSafeAt, inner 0 part]

theorem similar_trans {Γ : Ctx sig} {s : Srt} {t t' t'' : G Γ s} (first : Similar t t')
    (second : Similar t' t'') : Similar t t'' := by
  induction first with
  | var v =>
      cases second with
      | var => exact .var v
      | name closedV _ _ =>
          simp [Closed, read, readVar, binderSafeAt] at closedV
  | @name Γ n m closedN closedM same =>
      exact .name closedN (similar_safe second 0 closedM)
        (StructuralCongruence.trans _ _ _ same (similar_sound second))
  | zero => exact second
  | bag _ inner =>
      cases second with
      | bag next => exact .bag (inner next)
  | pnil => exact second
  | pcons _ _ head tail =>
      cases second with
      | pcons nextHead nextTail => exact .pcons (head nextHead) (tail nextTail)
  | input _ _ channel body =>
      cases second with
      | input nextChannel nextBody => exact .input (channel nextChannel) (body nextBody)
  | output _ _ channel payload =>
      cases second with
      | output nextChannel nextPayload => exact .output (channel nextChannel) (payload nextPayload)
  | dropq _ inner =>
      cases second with
      | dropq next => exact .dropq (inner next)
  | @quote Γ p p' related inner =>
      cases second with
      | name closedQuote closedM same =>
          exact .name (similar_safe (.quote (similar_symm related)) 0 closedQuote) closedM
            (StructuralCongruence.trans _ _ _ (similar_sound (.quote related)) same)
      | quote next => exact .quote (inner next)

/-! ## Observations and the frame action -/

/-- Similar observations: the same context and sort, and similar terms. -/
inductive ObsSimilar : Observation sig noUnknowns → Observation sig noUnknowns → Prop
  | mk {Γ : Ctx sig} {s : Srt} {t t' : G Γ s} : Similar t t' → ObsSimilar ⟨Γ, s, t⟩ ⟨Γ, s, t'⟩

theorem obsSimilar_refl (o : Observation sig noUnknowns) : ObsSimilar o o := by
  rcases o with ⟨Γ, s, t⟩
  exact .mk (similar_refl t)

theorem obsSimilar_symm {o o' : Observation sig noUnknowns} (similar : ObsSimilar o o') :
    ObsSimilar o' o := by
  cases similar with
  | mk inner => exact .mk (similar_symm inner)

theorem obsSimilar_trans {o o' o'' : Observation sig noUnknowns} (first : ObsSimilar o o')
    (second : ObsSimilar o' o'') : ObsSimilar o o'' := by
  cases first with
  | mk inner =>
      cases second with
      | mk inner' => exact .mk (similar_trans inner inner')

/-- An observation of a closed process: its term. -/
theorem obsSimilar_closed {t t' : G [] .pr} :
    ObsSimilar ⟨[], .pr, t⟩ ⟨[], .pr, t'⟩ ↔ Similar t t' := by
  constructor
  · intro similar
    cases similar with
    | mk inner => exact inner
  · exact .mk

/-- Groundings of a frame: every unknown gets a ground term. -/
abbrev Grounding (F : Frame sig) : Type := Assignment F.arity noUnknowns

/-- **Equality in the knowledge**: every grounding makes the two terms similar. -/
def Equal {F : Frame sig} (s t : Observation sig F.arity) : Prop :=
  ∀ g : Grounding F, ObsSimilar (instantiateObservation g s) (instantiateObservation g t)

/-- **The frame action**: the contextual frames of the twin-binder signature, with equality in the
knowledge `Equal`. Objects, morphisms, identities, composition and the action are those of
`Interface.Frames.contextual`. -/
def knowledge : Interface.Frames (fun F : Frame sig => Observation sig F.arity)
    (fun F G : Frame sig => Assignment F.arity G.arity) where
  E := fun s t => Equal s t
  equivalence _ := ⟨fun _ _ => obsSimilar_refl _, fun same g => obsSimilar_symm (same g),
    fun one two g => obsSimilar_trans (one g) (two g)⟩
  act := fun f t => instantiateObservation f t
  id F := generator F.arity
  comp := fun g f => Assignment.compose g f
  act_id := instantiateObservation_identity
  act_comp := fun g f t => (instantiateObservation_comp f g t).symm
  preserves := fun {_ _} f {s t} same g => by
    show ObsSimilar (instantiateObservation g (instantiateObservation f s))
      (instantiateObservation g (instantiateObservation f t))
    rw [instantiateObservation_comp, instantiateObservation_comp]
    exact same (Assignment.compose g f)

/-- The action, the identity and the composition are those of the contextual frames. -/
theorem knowledge_act {F G' : Frame sig} (f : Assignment F.arity G'.arity)
    (t : Observation sig F.arity) :
    knowledge.act f t = (Interface.Frames.contextual sig).act f t := rfl

/-! ## Solutions are groundings -/

/-- A grounding solves a store. -/
def GroundSolves {F : Frame sig} (g : Grounding F) (store : EquationStore (Observation sig F.arity)) :
    Prop :=
  ∀ e ∈ store, ObsSimilar (instantiateObservation g e.1) (instantiateObservation g e.2)

/-- The frame with no unknowns. -/
abbrev groundFrame : Frame sig := ⟨Empty, noUnknowns⟩

/-- Instantiation fixes ground terms. -/
theorem instantiate_ground (h : Assignment noUnknowns noUnknowns) {Γ : Ctx sig} {s : Srt}
    (t : G Γ s) : instantiate h t = t := by
  have only : h = generator noUnknowns := funext fun e => nomatch e
  rw [only]
  exact instantiate_identity t

theorem instantiateObservation_ground (h : Assignment noUnknowns noUnknowns)
    (o : Observation sig noUnknowns) : instantiateObservation h o = o := by
  rcases o with ⟨Γ, s, t⟩
  show (⟨Γ, s, instantiate h t⟩ : Observation sig noUnknowns) = ⟨Γ, s, t⟩
  rw [instantiate_ground]

/-- A ground term of each sort. -/
def groundTerm : (Γ : Ctx sig) → (s : Srt) → G Γ s
  | _, .nm => quoteT zeroT
  | _, .pr => zeroT
  | _, .ps => pnilT

/-- Every frame has a grounding. -/
def someGrounding (F : Frame sig) : Grounding F := fun i => groundTerm (F.arity i).1 (F.arity i).2

theorem groundSolves_of_models {F B : Frame sig} {σ : Assignment F.arity B.arity}
    {store : EquationStore (Observation sig F.arity)} (solved : knowledge.Models σ store)
    (h : Grounding B) : GroundSolves (Assignment.compose h σ) store := by
  intro e member
  have similar : ObsSimilar (instantiateObservation h (instantiateObservation σ e.1))
      (instantiateObservation h (instantiateObservation σ e.2)) := solved e member h
  rwa [instantiateObservation_comp, instantiateObservation_comp] at similar

theorem models_of_groundSolves {F : Frame sig} {g : Grounding F}
    {store : EquationStore (Observation sig F.arity)} (solved : GroundSolves g store) :
    knowledge.Models (a := F) (b := groundFrame) g store := by
  intro e member h
  show ObsSimilar (instantiateObservation h (instantiateObservation g e.1))
    (instantiateObservation h (instantiateObservation g e.2))
  rw [instantiateObservation_ground, instantiateObservation_ground]
  exact solved e member

/-- **Solvability is grounding.** -/
theorem solvable_iff {F : Frame sig} (store : EquationStore (Observation sig F.arity)) :
    knowledge.Solvable store ↔ ∃ g : Grounding F, GroundSolves g store := by
  constructor
  · rintro ⟨B, σ, solved⟩
    exact ⟨_, groundSolves_of_models solved (someGrounding B)⟩
  · rintro ⟨g, solved⟩
    exact ⟨groundFrame, g, models_of_groundSolves solved⟩

/-- Syntactic solutions of the contextual frames are solutions here. -/
theorem models_of_contextual {F B : Frame sig} {σ : Assignment F.arity B.arity}
    {store : EquationStore (Observation sig F.arity)}
    (solved : (Interface.Frames.contextual sig).Models σ store) : knowledge.Models σ store := by
  intro e member h
  have same : instantiateObservation σ e.1 = instantiateObservation σ e.2 := solved e member
  show ObsSimilar (instantiateObservation h (instantiateObservation σ e.1))
    (instantiateObservation h (instantiateObservation σ e.2))
  rw [same]
  exact obsSimilar_refl _

#print axioms similar_sound
#print axioms similar_trans
#print axioms solvable_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation
