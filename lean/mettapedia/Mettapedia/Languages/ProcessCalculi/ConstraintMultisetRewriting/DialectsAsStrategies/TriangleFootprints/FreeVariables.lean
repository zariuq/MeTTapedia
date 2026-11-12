import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.BoundVariables

/-!
# A body variable its left side does not bind: how each dialect renames it

`BoundVariables` asks every body variable to occur in the row's left side (`BoundRow`). Here is what
happens without that condition, on the smallest programs.

* **HE** renames each row's variables apart once per row and per run (`AlphaVariantRel`: any
  injective renaming whose new names avoid the names visible to the query), and an unbound
  variable stays a variable through the read, the evaluation (a variable is delivered) and the
  publication. So the published name is whatever fresh name the run chose.
* **PeTTa** renames a row for its use number, `$y` to `$y#use` (`Unifying.rename`), deterministically.

## Results

* `nullary_complete`: on a program of rows `(= (h) $y)`, for every name `z`, HE's machine has a
  complete run from the entry of `(h)` that publishes one `$z` per row.
* `Controls.fresh_two_runs`: on `{(= (fresh) $y)}`, HE has a complete run publishing `$u` and another
  publishing `$v`, so **no answer list is published by every complete run** (`fresh_not_determined`);
  PeTTa answers `$y#1`.
* `Controls.shared_fresh_name`: on `{(= (two) $y), (= (two) $y)}`, HE has a complete run publishing
  `$z`, `$z`: both rows' variables renamed to one name; PeTTa answers `$y#1`, `$y#2`. No renaming
  of variables maps one answer list to the other (`no_renaming_maps`): the two rows share a
  binding in HE's answer and not in PeTTa's.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace FreeVariables

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationRowResultsRel
  EquationWork AlphaVariantRel atomOccurs_mem_typeVars)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel equalityGroundedSemantic
  semanticLoopFree_empty constraints)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags
open AnswerBags.Controls (sym app rule)
open WholeRunWords.Double (noHost)

/-! ## HE's renaming of a row -/

/-- A head applied to nothing matches itself with no bindings. -/
theorem nullary_matches (h : String) :
    MatchRel equalityGroundedSemantic (app h []) (app h []) Bindings.empty :=
  .expression (.cons (.symSym h semanticLoopFree_empty)
    (.mk (by simp [constraints, Bindings.empty]) .nil) .nil) semanticLoopFree_empty

/-- **Any name is a legal fresh name for `$y`** in the row `(= (h) $y)` against the query `(h)`:
the swap of `y` and `z` is an injective renaming, and `z` is not visible to the query. -/
theorem alpha_to (h z : String) :
    AlphaVariantRel [Atom.undefinedType] (app h []) Bindings.empty (app h []) (.var "y") (app h [])
      (.var z) := by
  refine ⟨Equiv.swap "y" z, (Equiv.swap "y" z).injective, .expression (.cons (.symbol h) .nil), ?_, ?_⟩
  · have renamed := Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.AlphaRenameAtomRel.«variable»
      (rename := Equiv.swap "y" z) "y"
    rwa [Equiv.swap_apply_left] at renamed
  · intro name occurs
    rcases occurs with left | right
    · have used := atomOccurs_mem_typeVars left
      simp [TypeSubst.typeVars, TypeSubst.typeVarsList] at used
    · cases right
      rw [Equiv.swap_apply_left]
      intro visible
      unfold Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.QueryVisibleName at visible
      rcases visible with inQuery | ⟨atom, member, inAtom⟩ | ⟨value, assigned⟩ |
          ⟨key, value, assigned, _⟩ | ⟨left, right, equal, _⟩
      · have used := atomOccurs_mem_typeVars inQuery
        simp [TypeSubst.typeVars, TypeSubst.typeVarsList] at used
      · simp only [List.mem_singleton] at member
        subst member
        have used := atomOccurs_mem_typeVars inAtom
        simp [Atom.undefinedType, TypeSubst.typeVars] at used
      · simp [Bindings.empty] at assigned
      · simp [Bindings.empty] at assigned
      · simp [Bindings.empty] at equal

/-- The work of the row `(= (h) $y)` at a position, its variable renamed to `z`. -/
def work (h z : String) (position : Nat) : EquationWork :=
  ⟨position, app h [], .var "y", app h [], .var z, Bindings.empty⟩

theorem row_hit (h z : String) (position : Nat) :
    EquationRowResultsRel [Atom.undefinedType] (app h []) Bindings.empty position
      (rule (app h []) (.var "y")) [work h z position] :=
  .hit position (app h []) (.var "y") (app h []) (.var z) Bindings.empty Bindings.empty
    (alpha_to h z) (nullary_matches h) Controls.mergeEmpty

/-! ## An unbound variable through HE's machine -/

/-- **An unbound variable reads as itself** under every frame whose record is empty. -/
theorem read_var (policy : Policy) (output : Frame) (unbound : output.bindings = Bindings.empty)
    (z : String) : output.read policy (.var z) = .var z := by
  have certified := output.certified
  rw [unbound] at certified
  have none := certified.lookup_none_of_outside (name := z)
    (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.specBindingVars,
      Bindings.empty])
  have erased := Entry.Value.erase_resolve output.environment z
  rw [none] at erased
  unfold Completed.Frame.read
  simp only [Entry.Value.substitute]
  generalize Entry.Value.resolve output.environment z = value at erased ⊢
  cases value <;> simp_all [Entry.Value.erase]

theorem erase_var (z : String) : (Entry.Value.var z).erase = .var z := by
  simp [Entry.Value.erase]

theorem ofAtom_var (z : String) : Entry.Value.ofAtom (.var z) = .var z := by
  simp [Entry.Value.ofAtom]

theorem var_not_stopped (z : String) : ¬ IsEmptyOrErrorRel (Entry.Value.var z).erase := by
  rw [erase_var]
  rintro (same | ⟨tail, same⟩) <;> simp [Atom.empty] at same

theorem var_not_function (policy : Policy) (z : String) :
    ¬ Completed.FunctionPending policy (.var z) := by
  rintro ⟨⟨body, same⟩, _⟩
  simp [Entry.Value.erase] at same

/-- **A variable is delivered as itself.** -/
theorem var_entry (policy : Policy) (z : String) :
    Entry.Rel policy.reentry (Entry.Value.var z).status (Entry.Value.var z).erase Atom.undefinedType
      .deliver := by
  rw [erase_var]
  exact .pass (by simpa [erase_var] using var_not_stopped z) (.variable z) (Or.inr (Or.inr rfl))

/-- **The equation loop on works whose bodies are the unbound variable `$z`**: each body is read,
returned, delivered as `$z`, and the batches are concatenated. -/
theorem var_equations_steps {lookup : CastLookup} {policy : Policy} {atoms : List Atom}
    {live : List Atom} {scope : List String} {original : Entry.Value} {activation : Frame}
    (z : String) :
    ∀ (works : List EquationWork),
      (∀ w ∈ works, w.body = .var z ∧ w.bindings = Bindings.empty ∧
        ∃ output : Frame, output.bindings = w.bindings ∧
          Entry.Value.UnifyRel policy.rebuilding activation.environment original
            (Entry.Value.ofAtom w.pattern) output.environment) →
      ∀ (stack : List Continuation) (emitted : List Result),
        ∃ results : List Result, results.length = works.length ∧
          (∀ r ∈ results, r.1 = .var z ∧ r.2.bindings = Bindings.empty) ∧
          HERuns.HESteps noHost lookup policy
            ⟨Space.ofList atoms, .work (.equations live scope original Atom.undefinedType activation
              works), stack, emitted⟩
            ⟨Space.ofList atoms, .returning results, stack, emitted⟩
  | [], _, stack, emitted => ⟨[], rfl, (fun _ member => by cases member),
      Relation.ReflTransGen.single (.internal .equationsNil)⟩
  | w :: ws, each, stack, emitted => by
      obtain ⟨body, empty, output, sameBindings, unified⟩ := each w List.mem_cons_self
      have outputEmpty : output.bindings = Bindings.empty := sameBindings.trans empty
      obtain ⟨R, lengthR, shapeR, path⟩ := var_equations_steps z ws
        (fun w' member => each w' (List.mem_cons_of_mem _ member))
        (.prepend ([(.var z, output)] ++ []) :: stack) emitted
      refine ⟨([(.var z, output)] ++ []) ++ R, by simp [lengthR], fun r member => ?_, ?_⟩
      · simp only [List.append_nil, List.mem_append, List.mem_singleton] at member
        rcases member with rfl | inR
        · exact ⟨rfl, outputEmpty⟩
        · exact shapeR r inR
      · refine .head (.internal (.equationsCons sameBindings unified)) ?_
        rw [body, ofAtom_var, read_var policy output outputEmpty z]
        refine .head (.internal (.boundaryProducerRaw (var_not_function policy z))) ?_
        refine .head (.internal .boundaryBatch) ?_
        refine .head (.internal .boundaryBatchCons) ?_
        refine .head (.internal .boundaryReturned) ?_
        refine .head (.internal (.returnEvaluate (by rw [erase_var]; simp [Atom.notReducible])
          (var_not_stopped z))) ?_
        have delivered := LocalStepWith.delivered (admission := .historical)
          (space := Space.ofList atoms) (dispatch := noHost) (lookup := lookup) (policy := policy)
          (live := live) (scope := scope) (value := .var z) (expected := Atom.undefinedType)
          (activation := output)
          (stack := .append (.boundaryBatch live scope none
            (.returned original Atom.undefinedType) []) ::
              .append (.equations live scope original Atom.undefinedType activation ws) :: stack)
          (by
            have same : output.read policy (.var z) = .var z := read_var policy output outputEmpty z
            rw [same]
            exact var_entry policy z)
        have same : output.read policy (.var z) = .var z := read_var policy output outputEmpty z
        rw [same] at delivered
        refine .head (.internal delivered) ?_
        refine .head (.internal .append) ?_
        refine .head (.internal .boundaryBatchNil) ?_
        refine .head (.internal .prepend) ?_
        refine .head (.internal .append) ?_
        refine .trans path ?_
        exact .single (.internal .prepend)

/-- **A complete run of HE publishing one `$z` per row**, on a program of rows `(= (h) $y)`. -/
theorem nullary_complete (policy : Policy) {atoms : List Atom} {h : String} (z : String)
    {works : List EquationWork} (head : DataAtom (.symbol h))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol h)) = [])
    (notInstruction : Minimal.embeddedInstruction (app h []) = false)
    (frontier : EquationFrontierRel (Space.ofList atoms) [Atom.undefinedType] (app h [])
      Bindings.empty works)
    (shape : ∀ w ∈ works, w.body = .var z ∧ w.bindings = Bindings.empty) (nonempty : works ≠ []) :
    ∃ emitted : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList atoms) (app h []) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], emitted⟩ ∧
        emitted.map (fun r => r.1.erase) = works.map (fun _ => .var z) := by
  have data : ∀ a ∈ Atom.symbol h :: [], DataAtom a := by
    intro a member
    simp only [List.mem_singleton] at member
    subst member
    exact head
  have frontier' : EquationFrontierRel (Space.ofList atoms) [Atom.undefinedType]
      (callValue h []).erase Completed.Frame.empty.bindings works := by
    rw [callValue_erase]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) Completed.Frame.empty.certified frontier'
  have each : ∀ w ∈ works, w.body = .var z ∧ w.bindings = Bindings.empty ∧
      ∃ output : Frame, output.bindings = w.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding Completed.Frame.empty.environment (callValue h [])
          (Entry.Value.ofAtom w.pattern) output.environment := by
    intro w member
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w member
    exact ⟨(shape w member).1, (shape w member).2, ⟨w.bindings, after, certificate⟩, rfl, unified⟩
  obtain ⟨R, lengthR, shapeR, loop⟩ := var_equations_steps (lookup := Completed.rawLookup)
    (policy := policy) (atoms := atoms) (live := []) (scope := []) z works each
    (.append (.calls [] [] Atom.undefinedType []) :: .publish (app h []) :: []) []
  have unchanged : (R ++ []).map (Completed.readResult policy) = R := by
    rw [List.append_nil]
    apply map_fixed
    intro r member
    obtain ⟨isVar, empty⟩ := shapeR r member
    obtain ⟨value, frame⟩ := r
    simp only at isVar empty
    subst isVar
    simp only [Completed.readResult]
    rw [read_var policy frame empty z]
  have selected : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      ((R ++ []).map (Completed.readResult policy)) R := by
    rw [unchanged]
    exact HERuns.success_all R fun r member => by
      rw [(shapeR r member).1, erase_var]
      rfl
  refine ⟨R.map (Completed.publishResult policy (app h [])), ?_, ?_⟩
  · refine .trans (HERuns.call_entry_steps raw_answers data untyped [] [] Completed.Frame.empty [] [])
      ?_
    refine .head (.internal (.callEquations
      (HERuns.value_not_error head (callValue_erase h []))
      (HERuns.value_nonGrounded (fun impossible => impossible) notInstruction (callValue_erase h []))
      frontier' nonempty)) ?_
    refine .trans loop ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .callsNil) ?_
    refine .head (.internal .prepend) ?_
    refine .head (.internal (.publish selected)) ?_
    exact HERuns.publish_all _ _ []
  · have lengths : R.map (fun r : Result => r.1.erase) = works.map (fun _ => Atom.var z) := by
      have each : R.map (fun r : Result => r.1.erase) = R.map (fun _ => Atom.var z) :=
        List.map_congr_left fun r member => by rw [(shapeR r member).1, erase_var]
      rw [each, List.map_const', List.map_const', lengthR]
    rw [List.map_map]
    have publishErase : ((fun r : Result => r.1.erase) ∘ Completed.publishResult policy (app h [])) =
        fun r : Result => r.1.erase := by
      funext r
      exact Completed.publishResult_erase policy (app h []) r
    rw [publishErase]
    exact lengths

namespace Controls

/-- `{(= (fresh) $y)}`. -/
def freshRows : List Atom := [rule (app "fresh" []) (.var "y")]

/-- `{(= (two) $y), (= (two) $y)}`. -/
def twoRows : List Atom := [rule (app "two" []) (.var "y"), rule (app "two" []) (.var "y")]

theorem fresh_frontier (z : String) :
    EquationFrontierRel (Space.ofList freshRows) [Atom.undefinedType] (app "fresh" []) Bindings.empty
      [work "fresh" z 0] := by
  have rows : (Space.ofList freshRows).atoms.zipIdx = [(rule (app "fresh" []) (.var "y"), 0)] := rfl
  have covered : List.Forall₂ (fun row block =>
      EquationRowResultsRel [Atom.undefinedType] (app "fresh" []) Bindings.empty row.2 row.1 block)
      (Space.ofList freshRows).atoms.zipIdx [[work "fresh" z 0]] := by
    rw [rows]
    exact .cons (row_hit "fresh" z 0) .nil
  exact .completed covered

theorem two_frontier (z : String) :
    EquationFrontierRel (Space.ofList twoRows) [Atom.undefinedType] (app "two" []) Bindings.empty
      [work "two" z 0, work "two" z 1] := by
  have rows : (Space.ofList twoRows).atoms.zipIdx =
      [(rule (app "two" []) (.var "y"), 0), (rule (app "two" []) (.var "y"), 1)] := rfl
  have covered : List.Forall₂ (fun row block =>
      EquationRowResultsRel [Atom.undefinedType] (app "two" []) Bindings.empty row.2 row.1 block)
      (Space.ofList twoRows).atoms.zipIdx [[work "two" z 0], [work "two" z 1]] := by
    rw [rows]
    exact .cons (row_hit "two" z 0) (.cons (row_hit "two" z 1) .nil)
  exact .completed covered

theorem fresh_run (policy : Policy) (z : String) :
    ∃ emitted : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList freshRows) (app "fresh" []) Atom.undefinedType)
          ⟨Space.ofList freshRows, .returning [], [], emitted⟩ ∧
        emitted.map (fun r => r.1.erase) = [.var z] :=
  nullary_complete policy z (.symbol (by decide) (by decide)) (by decide +kernel) (by decide +kernel)
    (fresh_frontier z) (fun w member => by
      simp only [List.mem_singleton] at member
      subst member
      exact ⟨rfl, rfl⟩) (by simp)

/-- **HE's answer to `(fresh)` depends on the run; PeTTa's does not.** On `{(= (fresh) $y)}`, HE has a
complete run publishing `$u` and one publishing `$v`; PeTTa's run gives `$y#1`. -/
theorem fresh_two_runs (policy : Policy) :
    (∃ emitted : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList freshRows) (app "fresh" []) Atom.undefinedType)
          ⟨Space.ofList freshRows, .returning [], [], emitted⟩ ∧
        emitted.map (fun r => r.1.erase) = [.var "u"]) ∧
      (∃ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
            (load (Space.ofList freshRows) (app "fresh" []) Atom.undefinedType)
            ⟨Space.ofList freshRows, .returning [], [], emitted⟩ ∧
          emitted.map (fun r => r.1.erase) = [.var "v"]) ∧
      Streaming.values (Streaming.advance (translate freshRows) 30
        (Streaming.enter { state := store freshRows } (app "fresh" []))) = [.var "y#1"] :=
  ⟨fresh_run policy "u", fresh_run policy "v", by decide +kernel⟩

/-- **Every-run determinacy fails without `BoundRow`**: no answer list is published by every
complete run of HE on `(fresh)`. -/
theorem fresh_not_determined (policy : Policy) :
    ¬ ∃ L : List Atom, ∀ emitted : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList freshRows) (app "fresh" []) Atom.undefinedType)
          ⟨Space.ofList freshRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = L := by
  rintro ⟨L, every⟩
  obtain ⟨⟨first, runU, publishedU⟩, ⟨second, runV, publishedV⟩, _⟩ := fresh_two_runs policy
  have same := (publishedU.symm.trans (every first runU)).trans (every second runV).symm
  rw [publishedV] at same
  simp at same

/-- **Two rows, one fresh name in HE; two names in PeTTa.** On `{(= (two) $y), (= (two) $y)}`, HE has
a complete run publishing `$z`, `$z`; PeTTa's run gives `$y#1`, `$y#2`. -/
theorem shared_fresh_name (policy : Policy) :
    (∃ emitted : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList twoRows) (app "two" []) Atom.undefinedType)
          ⟨Space.ofList twoRows, .returning [], [], emitted⟩ ∧
        emitted.map (fun r => r.1.erase) = [.var "z", .var "z"]) ∧
      Streaming.values (Streaming.advance (translate twoRows) 40
        (Streaming.enter { state := store twoRows } (app "two" []))) = [.var "y#1", .var "y#2"] :=
  ⟨nullary_complete policy "z" (.symbol (by decide) (by decide)) (by decide +kernel)
    (by decide +kernel) (two_frontier "z") (fun w member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact ⟨rfl, rfl⟩) (by simp), by decide +kernel⟩

/-- **No renaming of variables maps HE's answer list to PeTTa's**: `$z, $z` shares one variable and
`$y#1, $y#2` does not. -/
theorem no_renaming_maps (rename : String → String) :
    [Atom.var "z", Atom.var "z"].map (Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars
      rename) ≠ [.var "y#1", .var "y#2"] := by
  intro same
  simp only [List.map_cons, List.map_nil, List.cons.injEq,
    Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars, Atom.var.injEq] at same
  obtain ⟨first, second, _⟩ := same
  rw [first] at second
  simp at second

end Controls

#print axioms alpha_to
#print axioms read_var
#print axioms var_equations_steps
#print axioms nullary_complete
#print axioms Controls.fresh_two_runs
#print axioms Controls.fresh_not_determined
#print axioms Controls.shared_fresh_name
#print axioms Controls.no_renaming_maps

end FreeVariables

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
