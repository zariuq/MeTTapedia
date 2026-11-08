import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceCallAliasTransport

/-!
# Ground entry facts from actual source head unification

The native ground-version entry marks every variable of its protected head
pattern ground and uninterpreted. These statements derive those claims from
the existing source unifier, including the source list-pattern view. They do
not identify the native fact table with the source substitution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceGroundEntryFacts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi
open UnifyingFrames OpenFrameEffects SourceCallAliasTransport

def GroundData (decls : Decls) (value : Atom) : Prop := support value = ∅ ∧ Uninterp decls value

theorem resolve_ground (bindings : MORK.Subst) (value : Atom) (ground : support value = ∅) :
    Unifying.resolve bindings value = value := by
  rw [resolve_eq_subst]
  exact CapturedUninterpretedRegions.subst_ground ground _

theorem GroundData.keep {decls : Decls} {before after : MORK.Subst}
    (refines : Unifying.Refines before after) (value : Atom)
    (good : GroundData decls (Unifying.resolve before value)) :
    GroundData decls (Unifying.resolve after value) := by
  rw [refined_ground_observation refines value good.1]
  exact good

theorem groundData_variable {decls : Decls} (bindings : MORK.Subst) (pattern : Atom)
    (good : GroundData decls (Unifying.resolve bindings pattern)) (name : String)
    (occurs : name ∈ support pattern) : GroundData decls (Unifying.resolve bindings (.var name)) := by
  refine ⟨?_, ?_⟩
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro other present
    have escapes := (support_subst (readBindings bindings) pattern other).mpr
      ⟨name, occurs, present⟩
    rw [← resolve_eq_subst, good.1] at escapes
    exact Finset.notMem_empty _ escapes
  · apply ContractBindingFacts.uninterpreted_substituted_variable (readBindings bindings) pattern
    · simpa only [← resolve_eq_subst] using good.2
    · exact occurs

theorem groundData_member {decls : Decls} {values : List Atom}
    (good : GroundData decls (.expression values)) (value : Atom) (member : value ∈ values) :
    GroundData decls value := by
  refine ⟨?_, ContractBindingFacts.uninterpreted_member values (UnifyAtoms.safeAll_of_uninterp good.2) value member⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro name occurs
  have escapes := (support_expression values name).mpr ⟨value, member, occurs⟩
  rw [good.1] at escapes
  exact Finset.notMem_empty _ escapes

theorem groundData_tail {decls : Decls} {first : Atom} {rest : List Atom}
    (good : GroundData decls (.expression (first :: rest))) : GroundData decls (.expression rest) := by
  refine ⟨?_, UnifyAtoms.uninterp_of_all ?_⟩
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro name occurs
    obtain ⟨value, member, present⟩ := (support_expression rest name).mp occurs
    have escapes := (support_expression (first :: rest) name).mpr ⟨value, by simp [member], present⟩
    rw [good.1] at escapes
    exact Finset.notMem_empty _ escapes
  · intro value member
    exact (groundData_member good value (by simp [member])).2

theorem unifyTerms_ground_marks {decls : Decls} (fuel : Nat)
    (bindings bound : MORK.Subst) (pattern value : Atom) (valid : Unifying.Idempotent bindings)
    (good : GroundData decls value) (unified : Unifying.unifyTerms fuel bindings pattern value = .ok bound) :
    ∀ name ∈ support pattern, GroundData decls (Unifying.resolve bound (.var name)) := by
  have same := (Unifying.unifyTerms_sound fuel bindings bound pattern value valid unified).2.2
  rw [resolve_ground bound value good.1] at same
  exact groundData_variable bound pattern (same ▸ good)

theorem unifyLists_ground_marks {decls : Decls}
    (unifier : MORK.Subst → Atom → Atom → Unifying.Unified)
    (sound : ∀ bindings bound pattern value, Unifying.Idempotent bindings →
      unifier bindings pattern value = .ok bound → Unifying.Idempotent bound ∧ Unifying.Refines bindings bound)
    (marks : ∀ bindings bound pattern value, Unifying.Idempotent bindings → GroundData decls value →
      unifier bindings pattern value = .ok bound →
        ∀ name ∈ support pattern, GroundData decls (Unifying.resolve bound (.var name))) :
    ∀ patterns values bindings bound, Unifying.Idempotent bindings →
      (∀ value ∈ values, GroundData decls value) →
      Unifying.unifyLists unifier bindings patterns values = .ok bound →
        ∀ pattern ∈ patterns, ∀ name ∈ support pattern, GroundData decls (Unifying.resolve bound (.var name)) := by
  intro patterns
  induction patterns with
  | nil => intro values bindings bound valid good unified pattern member; cases member
  | cons first rest ih =>
      intro values bindings bound valid good unified pattern member name occurs
      cases values with
      | nil => cases unified
      | cons value values =>
          simp only [Unifying.unifyLists] at unified
          cases firstRun : unifier bindings first value with
          | clash => simp [firstRun] at unified
          | exhausted => simp [firstRun] at unified
          | ok middle =>
              rw [firstRun, Unifying.Unified.ok_andThen] at unified
              obtain ⟨middleValid, _⟩ := sound bindings middle first value valid firstRun
              rcases List.mem_cons.mp member with rfl | present
              · have headGood := marks bindings middle pattern value valid (good value (by simp)) firstRun name occurs
                have restRefines := (Unifying.unifyLists_refines unifier sound rest values middle bound middleValid unified).2
                exact GroundData.keep restRefines (.var name) headGood
              · exact ih values middle bound middleValid (fun value present => good value (by simp [present]))
                  unified pattern present name occurs

theorem cons_pattern_support (first rest : Atom) :
    support (.expression [.symbol "cons", first, rest]) = support first ∪ support rest := by
  ext name
  simp only [support_expression, List.mem_cons, List.not_mem_nil, or_false, Finset.mem_union]
  simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]

/-- Actual source pattern unification, including the cons view, makes every
pattern variable a ground uninterpreted part of the admitted argument. -/
theorem unifyPattern_ground_marks {decls : Decls} (fuel : Nat) :
    ∀ bindings bound pattern value, Unifying.Idempotent bindings → GroundData decls value →
      Unifying.unifyPattern fuel bindings pattern value = .ok bound →
        ∀ name ∈ support pattern, GroundData decls (Unifying.resolve bound (.var name)) := by
  induction fuel with
  | zero => intro bindings bound pattern value valid good unified; cases unified
  | succ fuel ih =>
      intro bindings bound pattern value valid good unified
      simp only [Unifying.unifyPattern, resolve_ground bindings value good.1] at unified
      split at unified
      all_goals try solve | cases unified
      all_goals try exact unifyTerms_ground_marks fuel bindings bound _ _ valid good unified
      · rename_i _ _ first rest head tail
        cases firstRun : Unifying.unifyPattern fuel bindings first head with
        | clash => simp [firstRun] at unified
        | exhausted => simp [firstRun] at unified
        | ok middle =>
            rw [firstRun, Unifying.Unified.ok_andThen] at unified
            obtain ⟨middleValid, _⟩ := Unifying.unifyPattern_refines fuel bindings middle first head valid firstRun
            have headMarks := ih bindings middle first head valid (groundData_member good head (by simp)) firstRun
            have tailMarks := ih middle bound rest (.expression tail) middleValid (groundData_tail good) unified
            have tailRefines := (Unifying.unifyPattern_refines fuel middle bound rest (.expression tail) middleValid unified).2
            intro name occurs
            rw [cons_pattern_support] at occurs
            rcases Finset.mem_union.mp occurs with inHead | inTail
            · exact GroundData.keep tailRefines (.var name) (headMarks name inHead)
            · exact tailMarks name inTail
      · rename_i _ _ patterns values _ _
        have all := unifyLists_ground_marks (Unifying.unifyPattern fuel) (Unifying.unifyPattern_refines fuel)
          ih patterns values bindings bound valid (fun value member => groundData_member good value member) unified
        intro name occurs
        obtain ⟨pattern, member, present⟩ := (support_expression patterns name).mp occurs
        exact all pattern member name present

theorem source_refinement_keeps_ground {before after : MORK.Subst}
    (refines : Unifying.Refines before after) :
    GroundUninterpretedVersions.KeepsGround (readBindings before) (readBindings after) :=
  fun name ground => refined_ground_observation refines (.var name) ground

theorem source_mark_active {decls : Decls} {facts : ContractBindingFacts.Facts}
    {bindings bound : MORK.Subst} (pattern : Pat) (value : Atom) (fuel : Nat)
    (valid : Unifying.Idempotent bindings)
    (sound : GroundUninterpretedVersions.GroundSound decls (readBindings bindings) facts)
    (good : GroundData decls value)
    (unified : Unifying.unifyPattern fuel bindings pattern.toAtom value = .ok bound) :
    GroundUninterpretedVersions.GroundSound decls (readBindings bound)
      (GroundUninterpretedVersions.markPat facts pattern ⟨true, true⟩) := by
  have refinement := (Unifying.unifyPattern_refines fuel bindings bound pattern.toAtom value valid unified).2
  have old := sound.keep (source_refinement_keeps_ground refinement)
  intro name flags found isGround
  rw [GroundUninterpretedVersions.lookup_markPat] at found
  split at found
  · next occurs =>
      have marked := unifyPattern_ground_marks fuel bindings bound pattern.toAtom value valid good unified name occurs
      exact ⟨marked.1, fun _ => marked.2⟩
  · exact old name flags found isGround

theorem source_mark_any {decls : Decls} {facts : ContractBindingFacts.Facts}
    {bindings bound : MORK.Subst} (pattern : Pat) (value : Atom) (fuel : Nat)
    (valid : Unifying.Idempotent bindings)
    (sound : GroundUninterpretedVersions.GroundSound decls (readBindings bindings) facts)
    (unified : Unifying.unifyPattern fuel bindings pattern.toAtom value = .ok bound) :
    GroundUninterpretedVersions.GroundSound decls (readBindings bound)
      (GroundUninterpretedVersions.markPat facts pattern ⟨false, false⟩) := by
  have refinement := (Unifying.unifyPattern_refines fuel bindings bound pattern.toAtom value valid unified).2
  have old := sound.keep (source_refinement_keeps_ground refinement)
  intro name flags found isGround
  rw [GroundUninterpretedVersions.lookup_markPat] at found
  split at found
  · cases oldFound : facts.lookup name with
    | none =>
        simp only [oldFound, GroundUninterpretedVersions.mergeInto, Option.some.injEq] at found
        subst flags
        cases isGround
    | some previous =>
        simp only [oldFound, GroundUninterpretedVersions.mergeInto, Option.some.injEq] at found
        subst flags
        have same : ContractBindingFacts.mergeFlags previous ⟨false, false⟩ = previous := by
          cases previous; simp [ContractBindingFacts.mergeFlags]
        rw [same] at isGround ⊢
        exact old name previous oldFound isGround
  · exact old name flags found isGround

/-- The C's ANY/UNINTERPRETED entry metadata is justified by the actual
ordered source head unifier. ANY parameters may hold arbitrary open data. -/
theorem source_entry_facts {decls : Decls} (fuel : Nat) :
    ∀ (positions : List GroundUninterpretedVersions.Position) (patterns : List Pat)
      (values : List Atom) (facts : ContractBindingFacts.Facts) (bindings bound : MORK.Subst),
      positions.length = patterns.length → GroundUninterpretedVersions.Admitted decls positions values →
      Unifying.Idempotent bindings → GroundUninterpretedVersions.GroundSound decls (readBindings bindings) facts →
      Unifying.unifyLists (Unifying.unifyPattern fuel) bindings (patterns.map Pat.toAtom) values = .ok bound →
        GroundUninterpretedVersions.GroundSound decls (readBindings bound)
          (GroundUninterpretedVersions.entryFacts .ground positions patterns facts) := by
  intro positions
  induction positions with
  | nil =>
      intro patterns values facts bindings bound len admitted valid sound unified
      cases patterns with
      | cons => simp at len
      | nil =>
          cases admitted
          cases unified
          exact sound
  | cons position positions ih =>
      intro patterns values facts bindings bound len admitted valid sound unified
      cases patterns with
      | nil => simp at len
      | cons pattern patterns =>
          cases admitted with
          | cons here later =>
              rename_i value values
              simp only [List.map_cons, Unifying.unifyLists] at unified
              cases firstRun : Unifying.unifyPattern fuel bindings pattern.toAtom value with
              | clash => simp [firstRun] at unified
              | exhausted => simp [firstRun] at unified
              | ok middle =>
                  rw [firstRun, Unifying.Unified.ok_andThen] at unified
                  have middleValid := (Unifying.unifyPattern_refines fuel bindings middle pattern.toAtom value valid firstRun).1
                  cases position with
                  | any =>
                      exact ih patterns values _ middle bound (by simpa using len) later middleValid
                        (source_mark_any pattern value fuel valid sound firstRun) unified
                  | uninterpreted =>
                      exact ih patterns values _ middle bound (by simpa using len) later middleValid
                        (source_mark_active pattern value fuel valid sound (here rfl) firstRun) unified

theorem source_arguments_entry_facts {decls : Decls}
    (positions : List GroundUninterpretedVersions.Position) (patterns : List Pat)
    (values : List Atom) (facts : ContractBindingFacts.Facts) (bindings bound : MORK.Subst)
    (len : positions.length = patterns.length) (admitted : GroundUninterpretedVersions.Admitted decls positions values)
    (valid : Unifying.Idempotent bindings) (sound : GroundUninterpretedVersions.GroundSound decls (readBindings bindings) facts)
    (unified : Unifying.unifyArguments bindings (patterns.map Pat.toAtom) values = .ok bound) :
    GroundUninterpretedVersions.GroundSound decls (readBindings bound)
      (GroundUninterpretedVersions.entryFacts .ground positions patterns facts) :=
  source_entry_facts _ positions patterns values facts bindings bound len admitted valid sound unified

/-- Entry metadata survives actual recursive calls, not only a value-only
oracle. This is the ground subset of the native fact table's claims. -/
theorem reached_ground_metadata {registry : SpaceSemantics.Program} {initial : MORK.Subst}
    {source target : Unifying.Configuration} {decls : Decls}
    (steps : Relation.ReflTransGen (Unifying.Transition registry) source target)
    (good : Unifying.ConfigurationRefines initial source) (answers : List Unifying.Answer)
    (returned : target.control = .returned answers) (facts : ContractBindingFacts.Facts)
    (sound : GroundUninterpretedVersions.GroundSound decls (readBindings initial) facts) :
    ∀ answer ∈ answers, GroundUninterpretedVersions.GroundSound decls (readBindings answer.bindings) facts := by
  intro answer present
  exact sound.keep (source_refinement_keeps_ground
    (Unifying.reached_answers_refine steps good answers returned answer present).2)

/-- Metadata for already delivered atom recipes. This is not an admission
claim for arbitrary evaluation of a compound source expression. -/
def deliveredFlags (decls : Decls) (facts : ContractBindingFacts.Facts) (recipes : List Atom) :
    List ContractBindingFacts.ValueFlags :=
  recipes.map fun recipe => ⟨GroundUninterpretedVersions.atomFlags decls facts recipe, false⟩

theorem delivered_meets_ground {decls : Decls} {facts : ContractBindingFacts.Facts}
    (bindings : MORK.Subst) (recipes : List Atom) (positions : List GroundUninterpretedVersions.Position)
    (sound : GroundUninterpretedVersions.GroundSound decls (readBindings bindings) facts)
    (checked : GroundUninterpretedVersions.meets .ground positions (deliveredFlags decls facts recipes) = true) :
    GroundUninterpretedVersions.Admitted decls positions (recipes.map (Unifying.resolve bindings)) := by
  have faithful : GroundUninterpretedVersions.ArgsFaithful decls (readBindings bindings) recipes
      (deliveredFlags decls facts recipes) := by
    clear checked
    induction recipes with
    | nil => exact .nil
    | cons first rest ih =>
        exact .cons (GroundUninterpretedVersions.const_faithful sound first) ih
  have admitted := GroundUninterpretedVersions.admitted_of_meets
    ((GroundUninterpretedVersions.meets_iff .ground positions _).mp checked) faithful
  have same : recipes.map (Unifying.resolve bindings) = recipes.map (substA (readBindings bindings)) :=
    List.map_congr_left fun recipe _ => resolve_eq_subst bindings recipe
  rwa [same]

/-- A candidate's real renamed head is the metadata pattern. Using a
constant wrapper here retains the entire atom pattern, including its logic
variables; `Pat.toAtom` is exactly that original renamed source term. -/
def renamedPatterns (use : Nat) (equation : SpaceSemantics.Equation) : List Pat :=
  equation.arguments.map fun argument => .const (Unifying.rename use argument)

theorem renamedPatterns_toAtoms (use : Nat) (equation : SpaceSemantics.Equation) :
    (renamedPatterns use equation).map Pat.toAtom = equation.arguments.map (Unifying.rename use) := by
  simp [renamedPatterns, List.map_map, Pat.toAtom]

/-- The exact head-selection step and its ground metadata agree at the
same renamed candidate and returned substitution. The remaining alternatives
retain their own order, freshness counters and possible exhaustion. -/
theorem selected_head_and_facts {decls : Decls}
    (positions : List GroundUninterpretedVersions.Position) (equation : SpaceSemantics.Equation)
    (rest : List SpaceSemantics.Equation) (use : Nat) (values : List Atom)
    (facts : ContractBindingFacts.Facts) (bindings bound : MORK.Subst)
    (len : positions.length = equation.arguments.length)
    (admitted : GroundUninterpretedVersions.Admitted decls positions values)
    (valid : Unifying.Idempotent bindings)
    (sound : GroundUninterpretedVersions.GroundSound decls (readBindings bindings) facts)
    (unified : Unifying.unifyArguments bindings (equation.arguments.map (Unifying.rename use)) values = .ok bound) :
    Unifying.selections bindings values use (equation :: rest) =
      (Unifying.selections bindings values (use + 1) rest).map
        (fun others => .evaluate bound (Unifying.rename use equation.body) :: others) ∧
    GroundUninterpretedVersions.GroundSound decls (readBindings bound)
      (GroundUninterpretedVersions.entryFacts .ground positions (renamedPatterns use equation) facts) := by
  constructor
  · cases remaining : Unifying.selections bindings values (use + 1) rest <;>
      simp [Unifying.selections, unified, remaining]
  · apply source_arguments_entry_facts positions (renamedPatterns use equation) values facts bindings bound
      (by simpa [renamedPatterns] using len) admitted valid sound
    rwa [renamedPatterns_toAtoms]

namespace Controls

def decls : Decls := fun name => if name = "Known" ∨ name = "cons" then [.sym "Tag"] else []
def headPattern : Pat := .ctor "cons" [.var "head", .var "tail"]
def patterns : List Pat := [headPattern, .var "ignored"]
def positions : List GroundUninterpretedVersions.Position := [.uninterpreted, .any]
def values : List Atom := [.expression [.symbol "free", .grounded (.int 2)], .symbol "Known"]
def bound : MORK.Subst := [
  ("ignored", .symbol "Known"), ("tail", .expression [.grounded (.int 2)]), ("head", .symbol "free")]
def facts : ContractBindingFacts.Facts := GroundUninterpretedVersions.entryFacts .ground positions patterns []

theorem source_list_view_unifies :
    Unifying.unifyArguments [] (patterns.map Pat.toAtom) values = .ok bound := by decide +kernel

theorem ground_entry_admitted : GroundUninterpretedVersions.Admitted decls positions values := by
  refine .cons (fun _ => ?_) (.cons (fun never => by cases never) .nil)
  constructor
  · decide +kernel
  · simp [Uninterp, Safe, SafeAll, HeadFree, substA, decls]

theorem real_entry_metadata_sound : GroundUninterpretedVersions.GroundSound decls (readBindings bound) facts := by
  apply source_arguments_entry_facts positions patterns values [] [] bound rfl ground_entry_admitted
  · intro name value found; cases found
  · exact GroundUninterpretedVersions.GroundSound.nil _ _
  · exact source_list_view_unifies

theorem marked_list_variables :
    facts.lookup "head" = some ⟨true, true⟩ ∧ facts.lookup "tail" = some ⟨true, true⟩ ∧
      facts.lookup "ignored" = some ⟨false, false⟩ := by decide +kernel

theorem interpreted_cons_pattern_does_not_invalidate_marks :
    ¬ Uninterp decls headPattern.toAtom ∧
      GroundUninterpretedVersions.GroundSound decls (readBindings bound) facts := by
  refine ⟨?_, real_entry_metadata_sound⟩
  simp [headPattern, Pat.toAtom, Pat.toAtoms, Uninterp, Safe, HeadFree, substA, decls]

theorem interpreted_any_is_not_claimed_clean :
    Unifying.resolve bound (.var "ignored") = .symbol "Known" ∧ ¬ Uninterp decls (.symbol "Known") := by
  constructor
  · rfl
  · simp [Uninterp, Safe, decls]

theorem protected_field_is_admissible_at_next_call :
    GroundUninterpretedVersions.Admitted decls positions
      ([.var "head", .var "ignored"].map (Unifying.resolve bound)) :=
  delivered_meets_ground bound _ positions real_entry_metadata_sound (by decide +kernel)

theorem unknown_any_cannot_be_promoted_to_protected :
    GroundUninterpretedVersions.meets .ground [.uninterpreted]
      (deliveredFlags decls facts [.var "ignored"]) = false := by decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceGroundEntryFacts
