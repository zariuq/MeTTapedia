import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceGroundEntryFacts

/-!
# Bind-any metadata at the source binding operation

The existing native-analysis `BindAny` rules are interpreted over the actual
source `unifyBinding`, including quoted patterns and list views. Fuel is kept
at the source operation's original budget; normalizing an operand here does
not silently replace that budget or assume unification completion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceGroundBindFacts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi
open UnifyingFrames SourceCallAliasTransport SourceGroundEntryFacts

theorem terms_resolve_right (fuel : Nat) (bindings : MORK.Subst) (pattern value : Atom)
    (valid : Unifying.Idempotent bindings) :
    Unifying.unifyTerms fuel bindings pattern (Unifying.resolve bindings value) =
      Unifying.unifyTerms fuel bindings pattern value := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [Unifying.unifyTerms, Unifying.resolve_idem valid]

theorem pattern_resolve_right (fuel : Nat) (bindings : MORK.Subst) (pattern value : Atom)
    (valid : Unifying.Idempotent bindings) :
    Unifying.unifyPattern fuel bindings pattern (Unifying.resolve bindings value) =
      Unifying.unifyPattern fuel bindings pattern value := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [Unifying.unifyPattern, Unifying.resolve_idem valid, terms_resolve_right fuel bindings _ value valid]

theorem terms_delivered_ground_marks {decls : Decls} (fuel : Nat)
    (bindings bound : MORK.Subst) (pattern value : Atom) (valid : Unifying.Idempotent bindings)
    (good : GroundData decls (Unifying.resolve bindings value))
    (unified : Unifying.unifyTerms fuel bindings pattern value = .ok bound) :
    ∀ name ∈ support pattern, GroundData decls (Unifying.resolve bound (.var name)) := by
  apply unifyTerms_ground_marks fuel bindings bound pattern (Unifying.resolve bindings value) valid good
  rwa [terms_resolve_right fuel bindings pattern value valid]

theorem pattern_delivered_ground_marks {decls : Decls} (fuel : Nat)
    (bindings bound : MORK.Subst) (pattern value : Atom) (valid : Unifying.Idempotent bindings)
    (good : GroundData decls (Unifying.resolve bindings value))
    (unified : Unifying.unifyPattern fuel bindings pattern value = .ok bound) :
    ∀ name ∈ support pattern, GroundData decls (Unifying.resolve bound (.var name)) := by
  apply unifyPattern_ground_marks fuel bindings bound pattern (Unifying.resolve bindings value) valid good
  rwa [pattern_resolve_right fuel bindings pattern value valid]

theorem quote_pattern_support (literal : Atom) :
    support (.expression [.symbol "quote", literal]) = support literal := by
  ext name
  simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]

theorem binding_delivered_ground_marks {decls : Decls}
    (bindings bound : MORK.Subst) (pattern value : Atom) (valid : Unifying.Idempotent bindings)
    (good : GroundData decls (Unifying.resolve bindings value))
    (unified : Unifying.unifyBinding bindings pattern value = .ok bound) :
    ∀ name ∈ support pattern, GroundData decls (Unifying.resolve bound (.var name)) := by
  unfold Unifying.unifyBinding at unified
  split at unified
  · have marks := terms_delivered_ground_marks _ bindings bound _ value valid good unified
    intro name occurs
    apply marks name
    simpa only [quote_pattern_support] using occurs
  · exact pattern_delivered_ground_marks _ bindings bound _ value valid good unified

open GroundUninterpretedVersions ContractBindingFacts

/-- Existing bind-any metadata is sound for an actual source binding. The
ground facts are preserved by source refinement; new marks are derived from
the matched value's real resolved components, including quote/list views. -/
theorem source_bindAny_sound {decls : Decls} {facts afterFacts : Facts} {pattern : Pat} {flags : ValueFlags}
    {bindings bound : MORK.Subst} {value : Atom}
    (admitted : BindAny decls facts pattern flags afterFacts)
    (valid : Unifying.Idempotent bindings)
    (sound : GroundSound decls (readBindings bindings) facts)
    (faithful : Faithful decls (value, readBindings bindings) flags)
    (unified : Unifying.unifyBinding bindings pattern.toAtom value = .ok bound) :
    GroundSound decls (readBindings bound) afterFacts := by
  have refinement := (Unifying.unifyBinding_refines bindings bound pattern.toAtom value valid unified).2
  have old := sound.keep (source_refinement_keeps_ground refinement)
  have parts : flags.ground = true → ∀ name ∈ support pattern.toAtom,
      support (readBindings bound name) = ∅ ∧
        (flags.uninterpreted = true → Uninterp decls (readBindings bound name)) := by
    intro ground name occurs
    obtain ⟨isGround, clean⟩ := faithful.2 ground
    have actualGround : support (Unifying.resolve bindings value) = ∅ := by
      simpa only [resolve_eq_subst] using isGround
    have structural := binding_delivered_ground_marks
      (decls := UninterpretedLocalMultiplicity.emptyDecls) bindings bound pattern.toAtom value valid
      ⟨actualGround, UninterpretedLocalMultiplicity.empty_safe Atom.var _⟩ unified name occurs
    refine ⟨structural.1, fun uninterpreted => ?_⟩
    exact (binding_delivered_ground_marks bindings bound pattern.toAtom value valid
      ⟨actualGround, by simpa only [resolve_eq_subst] using clean uninterpreted⟩ unified name occurs).2
  cases admitted with
  | clean uninterpreted patternClean =>
      intro name resultFlags found ground
      rw [lookup_markPat] at found
      split at found
      · next occurs =>
          cases flags with
          | mk base bottom =>
          cases base with
          | mk vg vu =>
          cases vg with
          | true => exact (parts rfl name occurs).imp_right fun c _ => c uninterpreted
          | false =>
              cases oldFound : facts.lookup name with
              | none => simp [oldFound, mergeInto] at found; subst found; simp at ground
              | some previous =>
                  simp only [oldFound, mergeInto, Option.some.injEq] at found
                  subst found
                  have wasGround : previous.ground = true := by simpa [mergeFlags] using ground
                  have wasClean := patternUninterpreted_names _ patternClean name occurs previous oldFound
                  obtain ⟨isGround, clean⟩ := old name previous oldFound wasGround
                  exact ⟨isGround, fun _ => clean wasClean⟩
      · exact old name resultFlags found ground
  | keeps closedOrGround keepsClaims =>
      intro name resultFlags found ground
      rw [lookup_markPat] at found
      split at found
      · next occurs =>
          cases oldFound : facts.lookup name with
          | none =>
              simp only [oldFound, mergeInto, Option.some.injEq] at found
              subst found
              have valueGround : flags.ground = true := (Bool.and_eq_true_iff.mp ground).1
              exact ⟨(parts valueGround name occurs).1, fun clean => by cases clean⟩
          | some previous =>
              simp only [oldFound, mergeInto, Option.some.injEq] at found
              subst found
              simp only [mergeFlags, Bool.or_eq_true, Bool.or_false] at ground ⊢
              by_cases wasGround : previous.ground = true
              · obtain ⟨isGround, clean⟩ := old name previous oldFound wasGround
                exact ⟨isGround, clean⟩
              · have valueGround : flags.ground = true := by
                  rcases ground with oldGround | newGround
                  · exact absurd oldGround wasGround
                  · exact (Bool.and_eq_true_iff.mp newGround).1
                refine ⟨(parts valueGround name occurs).1, fun clean => ?_⟩
                have promised := patternKeepsClaims_names _ keepsClaims name occurs previous oldFound clean
                exact absurd promised wasGround
      · exact old name resultFlags found ground

/-- The actual ordered call answers feed the source binding continuation.
Inherited facts and idempotence come from the earned source path, not from
an assumed invariant of an external callee. Result-value metadata remains
the local expression-analysis obligation. -/
theorem returned_bind_metadata {registry : SpaceSemantics.Program} {initial : MORK.Subst}
    {source target : Unifying.Configuration} {decls : Decls}
    (steps : Relation.ReflTransGen (Unifying.Transition registry) source target)
    (good : Unifying.ConfigurationRefines initial source) (answers : List Unifying.Answer)
    (returned : target.control = .returned answers) (facts afterFacts : Facts)
    (sound : GroundSound decls (readBindings initial) facts)
    (pattern : Pat) (body : Atom) (flags : ValueFlags)
    (admitted : BindAny decls facts pattern flags afterFacts)
    (bound : Unifying.Answer → MORK.Subst)
    (faithful : ∀ answer ∈ answers, Faithful decls (answer.value, readBindings answer.bindings) flags)
    (unified : ∀ answer ∈ answers, Unifying.unifyBinding answer.bindings pattern.toAtom answer.value = .ok (bound answer)) :
    Unifying.bindAnswers pattern.toAtom body answers =
      some (answers.map fun answer => .evaluate (bound answer) body) ∧
    ∀ answer ∈ answers, GroundSound decls (readBindings (bound answer)) afterFacts := by
  refine ⟨bindAnswers_exact pattern.toAtom body answers bound unified, ?_⟩
  intro answer present
  exact source_bindAny_sound admitted
    (Unifying.reached_answers_refine steps good answers returned answer present).1
    (reached_ground_metadata steps good answers returned facts sound answer present)
    (faithful answer present) (unified answer present)

namespace Controls

def declarations : Decls := SourceGroundEntryFacts.Controls.decls
def before : MORK.Subst := SourceGroundEntryFacts.Controls.bound
def facts : Facts := SourceGroundEntryFacts.Controls.facts
def pattern : Pat := .var "new"
def known : Atom := .symbol "Known"
def flags : ValueFlags := ⟨⟨true, false⟩, false⟩
def after : MORK.Subst := Unifying.bindVar before "new" known
def afterFacts : Facts := markPat facts pattern ⟨true, false⟩

theorem initial_idempotent : Unifying.Idempotent before := by
  have emptyValid : Unifying.Idempotent [] := by intro name value found; cases found
  exact (Unifying.unifyLists_refines _ (Unifying.unifyPattern_refines _)
    _ _ [] before emptyValid SourceGroundEntryFacts.Controls.source_list_view_unifies).1

theorem interpreted_bind_admitted : BindAny declarations facts pattern flags afterFacts :=
  .keeps (fun _ => rfl) (by decide +kernel)

theorem actual_interpreted_bind : Unifying.unifyBinding before pattern.toAtom known = .ok after := by
  decide +kernel

theorem interpreted_value_metadata : Faithful declarations (known, readBindings before) flags := by
  refine ⟨rfl, fun _ => ⟨?_, fun impossible => by cases impossible⟩⟩
  decide +kernel

theorem interpreted_bind_preserves_ground_metadata :
    GroundSound declarations (readBindings after) afterFacts :=
  source_bindAny_sound interpreted_bind_admitted initial_idempotent
    SourceGroundEntryFacts.Controls.real_entry_metadata_sound interpreted_value_metadata actual_interpreted_bind

theorem resulting_flags_do_not_invent_cleanliness :
    afterFacts.lookup "head" = some ⟨true, true⟩ ∧ afterFacts.lookup "new" = some ⟨true, false⟩ := by
  decide +kernel

theorem falsely_claimed_uninterpreted_value_is_rejected :
    ¬ Faithful declarations (known, readBindings before) ⟨⟨true, true⟩, false⟩ := by
  intro promise
  have bad := (promise.2 rfl).2 rfl
  simp [known, declarations, SourceGroundEntryFacts.Controls.decls, Uninterp, Safe, substA] at bad

def literalCons : Atom := .expression [.symbol "cons", .symbol "free", .symbol "Nil"]
def consPattern : Atom := .expression [.symbol "cons", .var "head", .var "tail"]
def quotedPattern : Pat := .const (.expression [.symbol "quote", consPattern])
def quotedAfter : MORK.Subst := [("tail", .symbol "Nil"), ("head", .symbol "free")]
def listViewAfter : MORK.Subst := [
  ("tail", .expression [.symbol "free", .symbol "Nil"]), ("head", .symbol "cons")]

theorem quoted_and_list_view_bindings_differ :
    Unifying.unifyBinding [] quotedPattern.toAtom literalCons = .ok quotedAfter ∧
      Unifying.unifyBinding [] consPattern literalCons = .ok listViewAfter ∧ quotedAfter ≠ listViewAfter := by
  decide +kernel

theorem quoted_binding_metadata_sound :
    GroundSound declarations (readBindings quotedAfter) (markPat [] quotedPattern ⟨true, false⟩) := by
  apply source_bindAny_sound (flags := flags) (bindings := []) (value := literalCons)
  · exact .keeps (fun _ => rfl) (by decide +kernel)
  · intro name value found; cases found
  · exact GroundSound.nil _ _
  · refine ⟨rfl, fun _ => ⟨?_, fun impossible => by cases impossible⟩⟩
    decide +kernel
  · exact quoted_and_list_view_bindings_differ.1

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceGroundBindFacts
