import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachSyntax

/-!+# Knowledge transfer through equations on prepared schema views

Models may use any later contextual declaration family. A port has its own
opened view; knowledge transfer therefore concerns the actual sides of the
added equations, rather than a single label attached to a physical row.
Reach closes over accessible views while physical selection remains separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {point : S.Srt} {Name V : Type} [DecidableEq Name]
  {decl : V → MetaArity (base S point Name)}

abbrev Closed (decl : V → MetaArity (base S point Name)) :=
  Term (signature (base S point Name) decl) [] point

def ResolvesTo (store : EquationStore (Closed decl)) (term : Closed decl) (value : Name) : Prop :=
  ∀ {Future : Type} (future : Future → MetaArity (base S point Name))
    (candidate : Assignment decl future), ContextualFrameUnifier.Models candidate store →
      instantiate candidate term = name value

def Indistinguishable (store : EquationStore (Closed decl)) (known : Set (Closed decl))
    (a b : Name) : Prop :=
  ∀ {Future : Type} (future : Future → MetaArity (base S point Name))
    (candidate : Assignment decl future), ContextualFrameUnifier.Models candidate store →
      ∃ other : Assignment decl future, ContextualFrameUnifier.Models other store ∧
        ∀ term ∈ known,
          instantiate other term = mapNames (Equiv.swap a b) (instantiate candidate term)

def Possesses (store : EquationStore (Closed decl)) (known : Set (Closed decl)) (value : Name) : Prop :=
  ¬ ∃ other, other ≠ value ∧ Indistinguishable store known value other

theorem Indistinguishable.mono {store : EquationStore (Closed decl)}
    {known fewer : Set (Closed decl)} {a b : Name} (subset : fewer ⊆ known)
    (same : Indistinguishable store known a b) : Indistinguishable store fewer a b := by
  intro Future future candidate solved
  obtain ⟨other, model, values⟩ := same future candidate solved
  exact ⟨other, model, fun term member => values term (subset member)⟩

theorem Possesses.mono {store : EquationStore (Closed decl)}
    {known more : Set (Closed decl)} {value : Name} (possessed : Possesses store known value)
    (subset : known ⊆ more) : Possesses store more value := by
  rintro ⟨other, different, same⟩
  exact possessed ⟨other, different, same.mono subset⟩

omit [DecidableEq Name] in
theorem resolves_name (store : EquationStore (Closed decl)) (value : Name) :
    ResolvesTo store (name value) value := by
  intro Future future candidate _
  rfl

theorem resolved_name_possessed {store : EquationStore (Closed decl)}
    (consistent : ContextualFrameUnifier.Solvable store) {known : Set (Closed decl)}
    {term : Closed decl} (member : term ∈ known) {value : Name}
    (resolved : ResolvesTo store term value) : Possesses store known value := by
  rintro ⟨otherName, different, same⟩
  obtain ⟨Future, future, candidate, model⟩ := consistent
  obtain ⟨other, otherModel, values⟩ := same future candidate model
  have moved := values term member
  rw [resolved future candidate model, resolved future other otherModel] at moved
  change name (decl := future) value = name (Equiv.swap value otherName value) at moved
  rw [Equiv.swap_apply_left] at moved
  exact different (name_injective moved).symm

theorem written_name_possessed {store : EquationStore (Closed decl)}
    (consistent : ContextualFrameUnifier.Solvable store) {known : Set (Closed decl)}
    {value : Name} (member : name value ∈ known) : Possesses store known value :=
  resolved_name_possessed consistent member (resolves_name store value)

omit [DecidableEq Name] in
theorem ResolvesTo.unique {store : EquationStore (Closed decl)}
    (consistent : ContextualFrameUnifier.Solvable store) {term : Closed decl} {a b : Name}
    (first : ResolvesTo store term a) (second : ResolvesTo store term b) : a = b := by
  obtain ⟨Future,future,candidate,model⟩ := consistent
  exact name_injective ((first future candidate model).symm.trans (second future candidate model))

omit [DecidableEq Name] in
theorem ResolvesTo.append {store extra : EquationStore (Closed decl)} {term : Closed decl} {n : Name}
    (resolved : ResolvesTo store term n) : ResolvesTo (store ++ extra) term n := by
  intro Future future candidate model
  exact resolved future candidate ((ContextualFrameUnifier.models_append candidate store extra).mp model).1

/-- The known terms contain both sides of each new equation. -/
def KnowsEquations (known : Set (Closed decl)) (extra : EquationStore (Closed decl)) : Prop :=
  ∀ equation ∈ extra, equation.1 ∈ known ∧ equation.2 ∈ known

theorem indistinguishable_append {store extra : EquationStore (Closed decl)}
    {known : Set (Closed decl)} (knows : KnowsEquations known extra) {a b : Name}
    (same : Indistinguishable store known a b) : Indistinguishable (store ++ extra) known a b := by
  intro Future future candidate model
  obtain ⟨oldModel, extraModel⟩ := (ContextualFrameUnifier.models_append candidate store extra).mp model
  obtain ⟨other, otherModel, values⟩ := same future candidate oldModel
  refine ⟨other, (ContextualFrameUnifier.models_append other store extra).mpr ⟨otherModel, ?_⟩, values⟩
  intro equation member
  rw [values equation.1 (knows equation member).1, values equation.2 (knows equation member).2,
    extraModel equation member]

theorem possession_append {store extra : EquationStore (Closed decl)}
    {known : Set (Closed decl)} (knows : KnowsEquations known extra) {value : Name}
    (after : Possesses (store ++ extra) known value) : Possesses store known value := by
  rintro ⟨other, different, same⟩
  exact after ⟨other, different, indistinguishable_append knows same⟩

theorem indistinguishable_of_invariant {store : EquationStore (Closed decl)}
    {known : Set (Closed decl)} {a b : Name}
    (fixesKnown : ∀ term ∈ known, mapNames (Equiv.swap a b) term = term)
    (fixesStore : ∀ equation ∈ store,
      mapNames (Equiv.swap a b) equation.1 = equation.1 ∧
        mapNames (Equiv.swap a b) equation.2 = equation.2) :
    Indistinguishable store known a b := by
  intro Future future candidate model
  refine ⟨fun identity => mapNames (Equiv.swap a b) (candidate identity), ?_, ?_⟩
  · intro equation member
    have same := congrArg (mapNames (Equiv.swap a b)) (model equation member)
    simpa only [mapNames_instantiate, (fixesStore equation member).1,
      (fixesStore equation member).2] using same
  · intro term member
    simpa only [fixesKnown term member] using
      (mapNames_instantiate (Equiv.swap a b) candidate term).symm

def Knowledge (known : Set (Closed decl)) (views : Name → Set (Closed decl))
    (reached : Name → Prop) : Set (Closed decl) :=
  {term | term ∈ known ∨ ∃ value, reached value ∧ term ∈ views value}

def Reach (store : EquationStore (Closed decl)) (known : Set (Closed decl))
    (views : Name → Set (Closed decl)) (value : Name) : Prop :=
  ∀ closed : Name → Prop,
    (∀ n, Possesses store (Knowledge known views closed) n → closed n) → closed value

theorem Reach.closed {store : EquationStore (Closed decl)} {known : Set (Closed decl)}
    {views : Name → Set (Closed decl)} {value : Name}
    (possessed : Possesses store (Knowledge known views (Reach store known views)) value) :
    Reach store known views value := by
  intro closed closure
  apply closure value
  apply possessed.mono
  rintro term (member | ⟨n, reached, visible⟩)
  · exact Or.inl member
  · exact Or.inr ⟨n, reached closed closure, visible⟩

theorem Reach.of_possesses {store : EquationStore (Closed decl)} {known : Set (Closed decl)}
    {views : Name → Set (Closed decl)} {value : Name} (possessed : Possesses store known value) :
    Reach store known views value :=
  fun _ closure => closure value (possessed.mono fun _ member => Or.inl member)

theorem full_owner_reaches_every_name {store : EquationStore (Closed decl)}
    (consistent : ContextualFrameUnifier.Solvable store) (views : Name → Set (Closed decl)) (value : Name) :
    Reach store Set.univ views value :=
  Reach.of_possesses (written_name_possessed consistent (Set.mem_univ _))

/-- Per-use views may differ, but every added side must already be readable
at a reached space or be a term held by this actor. -/
theorem resolved_in_firing_reached {store extra : EquationStore (Closed decl)}
    {known : Set (Closed decl)} {views : Name → Set (Closed decl)}
    (consistent : ContextualFrameUnifier.Solvable (store ++ extra))
    (knows : KnowsEquations (Knowledge known views (Reach store known views)) extra)
    {term : Closed decl} (member : term ∈ known) {value : Name}
    (resolved : ResolvesTo (store ++ extra) term value) : Reach store known views value :=
  Reach.closed (possession_append knows (resolved_name_possessed consistent (Or.inl member) resolved))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach
