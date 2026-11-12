import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataCheckpoint

/-!
# Compound recipes at actual fresh clause entry

The same renamer acts on the clause's pattern and body. Its successful
refinement links a compound formal pattern to the delivered argument. The
resulting data region earns an alias checkpoint without introducing a ghost
variable, replacing the binding record or assuming a successful body result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open DestinationDataRecipe DestinationDataDebt
open HE.Spec.Type.RuntimeRefinement (renameTypeVars)

theorem lexical_rename (rename : String → String) (expression : Atom) :
    Source.lexicalForm (renameTypeVars rename expression) = Source.lexicalForm expression := by
  cases expression with
  | var => simp [renameTypeVars, Source.lexicalForm]
  | symbol | grounded => simp only [renameTypeVars]
  | expression fields =>
      cases fields with
      | nil => simp only [renameTypeVars, List.map_nil]
      | cons first rest =>
          cases first with
          | var | grounded | expression => simp only [renameTypeVars, List.map_cons]; rfl
          | symbol head =>
              cases rest with
              | nil => simp only [renameTypeVars, List.map_cons, List.map_nil]
              | cons a rest =>
                  cases rest with
                  | nil =>
                      simp [renameTypeVars, Source.lexicalForm]
                      all_goals split <;> simp_all
                  | cons b rest =>
                      cases rest with
                      | nil =>
                          simp [renameTypeVars, Source.lexicalForm]
                          all_goals split <;> simp_all
                      | cons c rest =>
                          cases rest <;> simp [renameTypeVars, Source.lexicalForm]
                          all_goals split <;> simp_all
                          all_goals split <;> simp_all

theorem scoped_rename (rename : String → String) (expression : Atom) :
    Source.scopedForm (renameTypeVars rename expression) = Source.scopedForm expression := by
  cases expression with
  | var => simp [renameTypeVars, Source.scopedForm]
  | symbol | grounded => simp only [renameTypeVars]
  | expression fields =>
      cases fields with
      | nil => simp only [renameTypeVars, List.map_nil]
      | cons first rest =>
          cases first with
          | var | grounded | expression => simp only [renameTypeVars, List.map_cons]; rfl
          | symbol head =>
              cases rest with
              | nil => simp only [renameTypeVars, List.map_cons, List.map_nil]
              | cons a rest =>
                  cases rest with
                  | nil =>
                      cases a <;> simp [renameTypeVars, Source.scopedForm]
                      all_goals split <;> simp_all
                  | cons b rest => simp [renameTypeVars, Source.scopedForm]

theorem no_head_rename (rename : String → String) (children : List Atom)
    (noHead : ∀ head arguments, children ≠ .symbol head :: arguments) :
    ∀ head arguments, children.map (renameTypeVars rename) ≠ .symbol head :: arguments := by
  intro head arguments same
  cases children with
  | nil => cases same
  | cons first rest =>
      cases first with
      | var | grounded | expression =>
          simp only [List.map_cons, renameTypeVars] at same
          cases same
      | symbol name => exact (noHead name rest rfl).elim

theorem rename_recipe {program : SpaceSemantics.Program} {expression : Atom}
    (data : Recipe program expression) (rename : String → String) : Recipe program (renameTypeVars rename expression) := by
  induction data with
  | variableValue name => simpa only [renameTypeVars] using (Recipe.variableValue (program := program) (rename name))
  | symbol name => simpa only [renameTypeVars] using (Recipe.symbol (program := program) name)
  | grounded value => simpa only [renameTypeVars] using (Recipe.grounded (program := program) value)
  | named head arguments ordinary localForm inert surface children ih =>
      simp only [renameTypeVars, List.map_cons]
      have ordinaryRenamed : Source.lexicalForm (.expression (.symbol head :: arguments.map (renameTypeVars rename))) = false := by
        simpa only [renameTypeVars, List.map_cons] using (lexical_rename rename _).trans ordinary
      have scopedRenamed : Source.scopedForm (.expression (.symbol head :: arguments.map (renameTypeVars rename))) = false := by
        simpa only [renameTypeVars, List.map_cons] using (scoped_rename rename _).trans localForm
      refine Recipe.named head _ ordinaryRenamed scopedRenamed inert surface ?_
      intro child member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact ih original present
  | tuple children noHead parts ih =>
      simp only [renameTypeVars]
      apply Recipe.tuple _ (no_head_rename rename children noHead)
      intro child member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact ih original present

/-- This is the native return recognizer's compound-pattern leaf case.
The equality is syntax of the authored equation, not an output oracle. -/
theorem selected_data_entry {Context : Type} (program : SpaceSemantics.Program)
    (control : Control) (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (occurrence : Nat) (equation : SpaceSemantics.Equation) (next : Control)
    (index : Nat) (argument recipe : Atom) (world : EagerDFS.World) (context : Context)
    (selected : ClauseChoice.attempt control head arguments destination older occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe)
    (body : equation.body = recipe) (data : Recipe program recipe) :
    Invariant program older destination argument (⟨world, next, context⟩ : Cursor Context) := by
  let rename := ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation)
  let fresh := renameTypeVars rename recipe
  refine ⟨[.evaluate fresh destination], ?_, ?_, ?_⟩
  · have fields := (ClauseChoice.attempt_preserves_caller control head arguments destination older occurrence
      equation next selected).2.2.1
    simpa only [fresh, rename, ClauseChoice.freshBody, body, List.singleton_append] using fields
  · intro goal member
    cases List.mem_singleton.mp member
    exact .evaluate (rename_recipe data rename)
  · exact DestinationDataDebt.clause_entry control head arguments destination older occurrence equation next index
      argument recipe selected actual formal

theorem selected_checkpoint_alias {Context : Type} (program : SpaceSemantics.Program)
    (control : Control) (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (occurrence : Nat) (equation : SpaceSemantics.Equation) (next : Control)
    (index : Nat) (argument recipe : Atom) (world : EagerDFS.World) (context : Context)
    (selected : ClauseChoice.attempt control head arguments destination older occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe)
    (body : equation.body = recipe) (data : Recipe program recipe)
    (fuel : Nat) (after : Cursor Context)
    (reached : ((DestinationDataCheckpoint.regionMachine program older).run fuel ⟨world, next, context⟩).2 =
      .suspended (.inl ()) after) (name : String)
    (root : control.destination = destination) (slot : destination = .var name) :
    ScopedReturnLocal.AliasHolds argument after.control := by
  have entered := selected_data_entry program control head arguments destination older occurrence equation next index
    argument recipe world context selected actual formal body data
  have target := (ClauseChoice.attempt_preserves_caller control head arguments destination older occurrence
    equation next selected).1
  exact DestinationDataCheckpoint.checkpoint_alias fuel entered reached name (target.trans root) slot

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataEntry
