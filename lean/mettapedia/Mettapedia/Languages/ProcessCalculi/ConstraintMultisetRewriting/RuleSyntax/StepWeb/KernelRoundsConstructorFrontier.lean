import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRoundsSemiNaive

/-!
# Constructor summaries preserve the actual dependency frontier

Known outer constructors survive substitution. A source rule whose read
constructors are disjoint from the new rows therefore contributes no hot
instance. Unknown constructors and empty-premise rules remain candidates.
The resulting filter is independent of the precise hot-instance filter and
is proved to preserve its heads and rounds on actual ground matches.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds.ConstructorFrontier

open Mettapedia.Logic.LP
open SetStoreSyntax

variable {signature : LPSignature} {Label : Type}
  (constant : signature.constants → Option Label)
  (function : signature.functionSymbols → Option Label)

def head : Term signature → Option Label
  | .var _ => none
  | .const c => constant c
  | .app f _ => function f

theorem substitute_head (assignment : Subst signature) (pattern : Term signature)
    {label : Label} (known : head constant function pattern = some label) :
    head constant function (assignment.applyTerm pattern) = some label := by
  cases pattern with
  | var v => cases known
  | const c => exact known
  | app f args => exact known

def Candidate (patterns : List (Term signature)) (delta : Set (Term signature)) : Prop :=
  patterns = [] ∨ ∃ pattern ∈ patterns,
    head constant function pattern = none ∨
      ∃ value ∈ delta, head constant function value = head constant function pattern

theorem candidate_of_new_read (assignment : Subst signature)
    {patterns : List (Term signature)} {delta : Set (Term signature)}
    {pattern : Term signature} (inside : pattern ∈ patterns)
    (fresh : assignment.applyTerm pattern ∈ delta) :
    Candidate constant function patterns delta := by
  refine Or.inr ⟨pattern, inside, ?_⟩
  cases known : head constant function pattern with
  | none => exact Or.inl rfl
  | some label =>
    exact Or.inr ⟨assignment.applyTerm pattern, fresh, substitute_head constant function assignment pattern known⟩

variable [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols]
  {P : Program (OneFrame.Terms (Term signature))}

theorem candidate_of_hot (instance_ : GroundMatch P) (delta : Set (Term signature))
    (hot : SemiNaive.Hot (consequence instance_) delta) :
    Candidate constant function instance_.rule.body.read delta := by
  rcases hot with empty | ⟨value, member, fresh⟩
  · left
    have mapped : instance_.rule.body.read.map instance_.assignment.applyTerm = [] := by
      simpa only [consequence, List.toFinset_eq_empty_iff] using empty
    exact List.map_eq_nil_iff.mp mapped
  · obtain ⟨pattern, inside, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    exact candidate_of_new_read constant function instance_.assignment inside fresh

def heads (state : SemiNaive.Frontier (Term signature)) : Set (Term signature) :=
  {value | ∃ instance_ : GroundMatch P,
    (∀ premise ∈ (consequence instance_).read, premise ∈ state.known) ∧
    Candidate constant function instance_.rule.body.read state.delta ∧
    SemiNaive.Hot (consequence instance_) state.delta ∧ value ∈ (consequence instance_).made}

theorem heads_eq (state : SemiNaive.Frontier (Term signature)) :
    heads constant function (P := P) state = SemiNaive.heads (consequence (P := P)) state := by
  ext value
  constructor
  · rintro ⟨instance_, enabled, _, hot, made⟩
    exact ⟨instance_, enabled, hot, made⟩
  · rintro ⟨instance_, enabled, hot, made⟩
    exact ⟨instance_, enabled, candidate_of_hot constant function instance_ state.delta hot, hot, made⟩

def round (state : SemiNaive.Frontier (Term signature)) : SemiNaive.Frontier (Term signature) :=
  let fresh := heads constant function (P := P) state \ state.known
  ⟨state.known ∪ fresh, fresh⟩

theorem round_eq (state : SemiNaive.Frontier (Term signature)) :
    round constant function (P := P) state = SemiNaive.round (consequence (P := P)) state := by
  unfold round SemiNaive.round
  rw [heads_eq]

theorem round_known (state : SemiNaive.Frontier (Term signature))
    (valid : SemiNaive.Invariant (consequence (P := P)) state) :
    (round constant function (P := P) state).known = immediate (consequence (P := P)) state.known := by
  rw [round_eq]
  exact SemiNaive.round_known _ _ valid

theorem cold_not_hot (instance_ : GroundMatch P) (delta : Set (Term signature))
    (cold : ¬ Candidate constant function instance_.rule.body.read delta) :
    ¬ SemiNaive.Hot (consequence instance_) delta := by
  exact fun hot => cold (candidate_of_hot constant function instance_ delta hot)

namespace Controls

abbrev sampleSignature : LPSignature := ⟨Bool, ℕ, Empty, Empty.elim, Bool, fun _ => 1⟩
def constantLabel : sampleSignature.constants → Option Bool := some
def functionLabel : sampleSignature.functionSymbols → Option Bool := some
def node (constructor : Bool) (child : Term sampleSignature) : Term sampleSignature :=
  .app constructor (fun _ => child)

theorem empty_kept : Candidate constantLabel functionLabel [] ∅ := by
  exact Or.inl rfl

theorem unknown_kept : Candidate constantLabel functionLabel [.var 0] ∅ := by
  exact Or.inr ⟨.var 0, List.mem_singleton_self _, Or.inl rfl⟩

theorem same_constructor_kept :
    Candidate constantLabel functionLabel [node true (.var 0)] {node true (.const false)} := by
  exact Or.inr ⟨_, List.mem_singleton_self _, Or.inr ⟨_, rfl, rfl⟩⟩

theorem different_constructor_cold :
    ¬ Candidate constantLabel functionLabel [node true (.var 0)] {node false (.const true)} := by
  rintro (empty | ⟨pattern, inside, unknown | ⟨value, fresh, same⟩⟩)
  · cases empty
  · obtain rfl := List.mem_singleton.mp inside
    cases unknown
  · obtain rfl := List.mem_singleton.mp inside
    obtain rfl := Set.mem_singleton_iff.mp fresh
    cases same

theorem changed_subtree_keeps_constructor :
    head constantLabel functionLabel
      (Subst.applyTerm (fun _ => node false (.const true)) (node true (.var 0))) = some true := by
  exact substitute_head constantLabel functionLabel (fun _ => node false (.const true))
    (node true (.var 0)) rfl

end Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds.ConstructorFrontier
