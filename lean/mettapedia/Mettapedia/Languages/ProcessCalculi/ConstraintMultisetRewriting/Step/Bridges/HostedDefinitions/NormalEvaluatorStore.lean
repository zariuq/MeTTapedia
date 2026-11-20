import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# Actual source children extend their mover's constraint store

The law covers every source construct. Calls retain the caller's store and
append their copied match; queries and removals append the actual row use.
Other moves either keep the store or append their explicit bind equation.
Determined data therefore remain determined in live children. This concerns
the same datum, not an arbitrary new focus or commuting program effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorStore

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  (D : Discipline S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)
  (supply : Nat → Term S Γ star)
  {world nextWorld : World κ Γ star} {before : Branch κ Γ star D.Ty}
  {children : Multiset (Branch κ Γ star D.Ty)}

theorem move_store (moved : Move D P supply world before nextWorld children) :
    ∀ child ∈ children, ∃ extra, child.store = before.store ++ extra := by
  intro child member
  cases moved with
  | apply K term frames pending _ =>
      obtain ⟨clause, _, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
      exact ⟨[(instantiate (copyAt κ world.scope) clause.lhs, term)], rfl⟩
  | query K space pattern body frames pending handle _ =>
      obtain ⟨row, _, rfl⟩ := Multiset.mem_map.mp member
      exact ⟨rowUse world.scope row pattern, rfl⟩
  | choice =>
      rcases Multiset.mem_cons.mp member with rfl | later
      · exact ⟨[], (List.append_nil _).symm⟩
      · rw [Multiset.mem_singleton.mp later]
        exact ⟨[], (List.append_nil _).symm⟩
  | fail => cases member
  | letBind | remove | new | memo =>
      rw [Multiset.mem_singleton.mp member]
      exact ⟨_, rfl⟩
  | ret | unmatched | run | letStart | add | removeMissing | checkStart | admitted | refused |
      delay | forcePending | forceDone =>
      rw [Multiset.mem_singleton.mp member]
      exact ⟨[], (List.append_nil _).symm⟩

theorem determines_child {datum : Data κ Γ star} {code : Term S Γ star}
    (moved : Move D P supply world before nextWorld children)
    (known : Determines before.store datum code) {child : Branch κ Γ star D.Ty}
    (member : child ∈ children) (live : Solvable child.store) : Determines child.store datum code := by
  obtain ⟨extra, store⟩ := move_store D P supply moved child member
  rw [store] at live ⊢
  exact ⟨live, fun target assignment solved =>
    known.2 target assignment ((models_append assignment _ _).mp solved).1⟩

theorem reads_before {datum : Data κ Γ star} {code : Term S Γ star}
    (moved : Move D P supply world before nextWorld children) {child : Branch κ Γ star D.Ty}
    (member : child ∈ children) (read : Reads child.store datum code) : Reads before.store datum code := by
  obtain ⟨extra, store⟩ := move_store D P supply moved child member
  rw [store] at read
  exact reads_of_append read

theorem solvable_before (moved : Move D P supply world before nextWorld children)
    {child : Branch κ Γ star D.Ty} (member : child ∈ children) (live : Solvable child.store) :
    Solvable before.store := by
  obtain ⟨extra, store⟩ := move_store D P supply moved child member
  rw [store] at live
  exact solvable_of_append live

section Controls

theorem ret_move_store (world : World κ Γ star) (K : List (Constraint κ Γ star))
    (datum : Data κ Γ star) (frames : List (Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty))
    (moved : Move D P supply world ⟨K, .eval (.ret datum), frames, pending⟩ nextWorld children) :
    ∀ child ∈ children, child.store = K := by
  cases moved with
  | ret =>
      intro child member
      rw [Multiset.mem_singleton.mp member]

theorem selected_call_store (world : World κ Γ star) (K : List (Constraint κ Γ star))
    (datum : Data κ Γ star) (frames : List (Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty))
    (clause : SourceLanguage.Equation κ Γ star D.Ty) (inside : clause ∈ P.equations)
    (matched : Solvable (K ++ [(instantiate (copyAt κ world.scope) clause.lhs, datum)])) :
    ∃ children, Move D P supply world ⟨K, .eval (.apply datum), frames, pending⟩ world.fresh children ∧
      callBranch D world.scope K datum frames pending clause ∈ children ∧
      (callBranch D world.scope K datum frames pending clause).store =
        K ++ [(instantiate (copyAt κ world.scope) clause.lhs, datum)] := by
  refine ⟨_, .apply world K datum frames pending ⟨clause, inside, matched⟩, ?_, rfl⟩
  exact Multiset.mem_coe.mpr (List.mem_map.mpr ⟨clause, inside, rfl⟩)

theorem letBind_store (world : World κ Γ star) (K : List (Constraint κ Γ star))
    (site : κ.Site) (pattern value : Data κ Γ star) (body : Comp κ Γ star D.Ty)
    (frames : List (Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty)) :
    ∃ children, Move D P supply world ⟨K, .value value, .bindTo site pattern body :: frames, pending⟩
        world.fresh children ∧
      ∀ child ∈ children, child.store = K ++ [(instantiate (openAt κ site world.scope) pattern, value)] := by
  refine ⟨_, .letBind world K value site pattern body frames pending, ?_⟩
  intro child member
  rw [Multiset.mem_singleton.mp member]

theorem query_row_store (world : World κ Γ star) (K : List (Constraint κ Γ star))
    (space pattern : Data κ Γ star) (body : Comp κ Γ star D.Ty)
    (frames : List (Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty))
    (handle : Term S Γ star) (addressed : Determines K space handle)
    (row : Row κ Γ star) (inside : row ∈ world.spaces handle) :
    ∃ children, Move D P supply world ⟨K, .eval (.query space pattern body), frames, pending⟩
        world.fresh children ∧
      (⟨K ++ rowUse world.scope row pattern, .eval body, frames, pending⟩ : Branch κ Γ star D.Ty) ∈ children := by
  exact ⟨_, .query world K space pattern body frames pending handle addressed,
    Multiset.mem_map.mpr ⟨row, inside, rfl⟩⟩

end Controls

section DeadBinding

open SourceLanguage.Elaboration SourceLanguage.Toolkit

variable {κ₀ : Keys MSig} (D₀ : Discipline MSig [] ())
  (P₀ : SourceLanguage.Program κ₀ [] () D₀.Ty) (supply₀ : Nat → MClosed)

theorem live_child_is_required (world : World κ₀ [] ()) (site : κ₀.Site) :
    let a : Data κ₀ [] () := symAt "a"
    let b : Data κ₀ [] () := symAt "b"
    let before : Branch κ₀ [] () D₀.Ty := ⟨[], .value b, [.bindTo site a (.ret a)], []⟩
    let after : Branch κ₀ [] () D₀.Ty := ⟨[(a, b)], .eval (.ret a), [], []⟩
    Move D₀ P₀ supply₀ world before world.fresh {after} ∧
      Determines before.store a (csym "a") ∧ ¬ Determines after.store a (csym "a") := by
  dsimp only
  have live : Solvable ([] : List (Constraint κ₀ [] ())) :=
    ⟨SourceLanguage.Name κ₀, fam κ₀, generator (fam κ₀), fun _ inside => by cases inside⟩
  refine ⟨.letBind world [] (symAt "b") site (symAt "a") (.ret (symAt "a")) [] [],
    ⟨live, fun _ _ _ => rfl⟩, ?_⟩
  intro determined
  obtain ⟨X, target, assignment, solved⟩ := determined.1
  have same := (models_singleton assignment _).mp solved
  change (symAt "a" : Term (signature MSig target) [] ()) = symAt "b" at same
  have tags := congrArg (fun term : Term (signature MSig target) [] () =>
    match term with
    | .op (.inl (.sym name)) _ => name
    | _ => "") same
  exact (by decide : ("a" : String) ≠ "b") tags

end DeadBinding

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorStore

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorStore.move_store
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorStore.determines_child
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorStore.live_child_is_required
