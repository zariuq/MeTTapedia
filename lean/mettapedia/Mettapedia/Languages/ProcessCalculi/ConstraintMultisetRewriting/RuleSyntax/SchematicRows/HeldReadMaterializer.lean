import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadConsumer

/-!
# Fresh activation of a persistent schematic row

The materializer is the existing held-rule step, opened above the whole
source support. A closure reading derives its admission; neither a solver
answer nor admission is a hypothesis. The resource and label laws retain
every source term needed by the subsequent private consumer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMaterializer

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open Presentation.Schematic (Tm rowSig)
open RuleOccurrences HeldCopyConsumer

universe uOcc uR uC uZ
variable {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}

noncomputable def materializer (codes : Codes RowTerms C Z)
    (s : RState RowTerms O R C Z) (held : R) (temporary : O) : RFiring O R E codes s where
  use := .held held
  ext := PUnit.unit
  opening := FreshNamespaces.opening (Equiv.refl Nat) (HeldFreshNamespaces.bound (Equiv.refl Nat) s) 0
  selection := ⟨[], [], [temporary]⟩
  seen := []
  madeRules := []
  installed := []
  removedRules := []
  published := []

variable (codes : Codes RowTerms C Z) (s : RState RowTerms O R C Z)
  (held : R) (temporary : O) (schema : Schema RowTerms)

theorem specification
    (declared : codes.unfold (s.held held).code = schema.toSpec) :
    (materializer codes s held temporary).spec = schema.toSpec := declared

theorem represents_closure
    (declared : codes.unfold (s.held held).code = schema.toSpec) :
    Opening.rowClosure (materializer codes s held temporary) schema.value =
      (⟨schema, (s.held held).args⟩ : Closure RowTerms s.frame) := by
  unfold Opening.rowClosure
  rw [specification codes s held temporary schema declared]
  rfl

theorem fresh : (materializer codes s held temporary).Fresh X :=
  HeldFreshNamespaces.firing_fresh (Equiv.refl Nat) (materializer codes s held temporary) 0 rfl

theorem shapes (ambient : Set C)
    (declared : codes.unfold (s.held held).code = schema.toSpec)
    (present : held ∈ s.rules) (lengths : schema.params.length = (s.held held).args.length) :
    (materializer codes s held temporary).Shapes X ambient := by
  refine ⟨fresh codes s held temporary, ?_, ?_⟩
  · unfold RFiring.RowShapes
    rw [specification codes s held temporary schema declared]
    exact ⟨List.nodup_nil, List.nodup_singleton temporary, rfl, rfl, rfl, rfl⟩
  · refine {
      available := present
      arguments := ?_
      installed := ?_
      madeNodup := List.nodup_nil
      madeLength := ?_
      madeNew := ?_
      removed := ?_
      removedNodup := List.nodup_nil
      removedHeld := ?_
      published := ?_ }
    · rw [specification codes s held temporary schema declared]
      exact lengths
    · rw [specification codes s held temporary schema declared]
      rfl
    · rw [specification codes s held temporary schema declared]
      rfl
    · intro occurrence member
      cases member
    · rw [specification codes s held temporary schema declared]
      rfl
    · intro pair member
      rw [specification codes s held temporary schema declared] at member
      cases member
    · rw [specification codes s held temporary schema declared]
      rfl

variable [DecidableEq O]

theorem admitted (ambient : Set C)
    (declared : codes.unfold (s.held held).code = schema.toSpec)
    (present : held ∈ s.rules) (temporaryFresh : temporary ∉ s.present)
    (caller : Subst rowSig)
    (known : X.Models (a := s.frame) (b := PUnit.unit) caller s.knowledge) (value : Tm)
    (reading : (⟨schema, (s.held held).args⟩ : Closure RowTerms s.frame).ReadsAt X (b := PUnit.unit) caller value) :
    (materializer codes s held temporary).Admits X ambient := by
  have same := specification codes s held temporary schema declared
  have lengths := Closure.wellFormed_of_readsAt (b := PUnit.unit) X _ caller reading
  have enabled : MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ()) s.present
      ((materializer codes s held temporary).selection.commit (T := Unit)) := by
    apply enabled_of
    · intro occurrence member
      cases member
    · intro occurrence member
      cases member
    · intro occurrence member
      cases member
    · intro occurrence member
      obtain rfl := List.mem_singleton.mp member
      exact temporaryFresh
  exact Materialization.admits_of_reading (b := PUnit.unit) X (materializer codes s held temporary) ambient
    (shapes codes s held temporary schema ambient declared present lengths) enabled
    (by rw [same]; rfl) (by rw [same]; rfl) (by rw [same]; rfl)
    (by rw [same]; rfl) (by rw [same]; rfl) (by rw [same]; rfl)
    (by rw [same]; rfl) (by rw [same]; rfl) schema.value
    (by rw [same]; exact List.mem_singleton_self schema.value)
    caller known value (by rw [represents_closure codes s held temporary schema declared]; exact reading)

variable [DecidableEq R]

theorem reading_iff_models (ambient : Set C)
    (declared : codes.unfold (s.held held).code = schema.toSpec)
    (present : held ∈ s.rules) (lengths : schema.params.length = (s.held held).args.length)
    (caller : Subst rowSig)
    (known : X.Models (a := s.frame) (b := PUnit.unit) caller s.knowledge) (value : Tm) :
    (⟨schema, (s.held held).args⟩ : Closure RowTerms s.frame).ReadsAt X (b := PUnit.unit) caller value ↔
      ∃ point : Subst rowSig,
        X.Models (a := s.frame) (b := PUnit.unit) point
          ((materializer codes s held temporary).result X).knowledge ∧
        (∀ term, s.Mentions term → point.applyTerm term = caller.applyTerm term) ∧
        point.applyTerm (((materializer codes s held temporary).result X).label temporary) = value := by
  have same := specification codes s held temporary schema declared
  have law := Materialization.materialized_reading (b := PUnit.unit) X (materializer codes s held temporary)
    ambient present (fresh codes s held temporary) (by rw [same]; rfl) (by rw [same]; rfl)
    (by rw [same]; exact lengths) schema.value temporary rfl (by rw [same]; rfl)
    caller known value
  rw [represents_closure codes s held temporary schema declared] at law
  change ((⟨schema, (s.held held).args⟩ : Closure RowTerms s.frame).ReadsAt X (b := PUnit.unit) caller value ↔
    ∃ point : Subst rowSig, X.Models (a := s.frame) (b := PUnit.unit) point
      ((materializer codes s held temporary).result X).knowledge ∧
      (∀ term : Tm, s.Mentions term →
        point.applyTerm ((Subst.id rowSig).applyTerm term) = caller.applyTerm term) ∧
      point.applyTerm (((materializer codes s held temporary).result X).label temporary) = value) at law
  simpa only [Subst.applyTerm_id] using law

theorem result_present :
    ((materializer codes s held temporary).result X).present = s.present ∪ {temporary} :=
  Materialization.result_present_single X (materializer codes s held temporary) temporary rfl rfl

theorem result_rules (persistent : (s.held held).mode = .persistent) :
    ((materializer codes s held temporary).result X).rules = s.rules :=
  (Materialization.persistent_source_retained X (materializer codes s held temporary)
    held rfl persistent rfl rfl).1

theorem result_held (occurrence : R) :
    ((materializer codes s held temporary).result X).held occurrence = s.held occurrence := by
  rw [(materializer codes s held temporary).result_held_other (by simp [materializer])]
  cases s.held occurrence with
  | mk heldCode arguments mode zone =>
    change (⟨heldCode, arguments.map (Subst.id rowSig).applyTerm, mode, zone⟩ :
      Held RowTerms C Z s.frame) = ⟨heldCode, arguments, mode, zone⟩
    have unchanged : arguments.map (Subst.id rowSig).applyTerm = arguments := by
      induction arguments with
      | nil => rfl
      | cons term rest ih => simp only [List.map_cons, Subst.applyTerm_id, ih]
    rw [unchanged]

theorem source_equation_retained (ambient : Set C)
    (equation : Equation Tm) (member : equation ∈ s.knowledge) :
    equation ∈ ((materializer codes s held temporary).result X).knowledge := by
  rcases equation with ⟨left, right⟩
  have transported := (rstep X O R E codes ambient).transported
    (materializer codes s held temporary) (left, right) member
  change ((Subst.id rowSig).applyTerm left, (Subst.id rowSig).applyTerm right) ∈
    (materializer codes s held temporary).information X at transported
  change (left, right) ∈ (materializer codes s held temporary).information X
  simpa only [Subst.applyTerm_id] using transported

theorem result_label_other
    (declared : codes.unfold (s.held held).code = schema.toSpec)
    (occurrence : O) (different : occurrence ≠ temporary) :
    ((materializer codes s held temporary).result X).label occurrence = s.label occurrence := by
  have production : (materializer codes s held temporary).spec.body.produce = [schema.value] := by
    rw [specification codes s held temporary schema declared]
    rfl
  have opened := congrArg (fun terms : List Tm =>
    terms.map (materializer codes s held temporary).opening.applyTerm) production
  change ((materializer codes s held temporary).base.opened X).produce =
    [(materializer codes s held temporary).opening.applyTerm schema.value] at opened
  change RuleSyntax.relabel (Tm := RowTerms) (a := s.frame)
    ((materializer codes s held temporary).base.row X s.toState) [temporary]
    ((materializer codes s held temporary).base.opened X).produce occurrence = s.label occurrence
  rw [opened]
  simp only [relabel, if_neg different]
  exact Subst.applyTerm_id (s.label occurrence)

theorem source_mentions_retained (ambient : Set C)
    (declared : codes.unfold (s.held held).code = schema.toSpec)
    (persistent : (s.held held).mode = .persistent) (temporaryFresh : temporary ∉ s.present)
    (term : Tm) (mentioned : s.Mentions term) :
    ((materializer codes s held temporary).result X).Mentions term := by
  rcases mentioned with (left | right | ⟨occurrence, present, labelled⟩) |
      ⟨occurrence, present, argument⟩
  · obtain ⟨equation, member, rfl⟩ := List.mem_map.mp left
    exact Or.inl (Or.inl (List.mem_map_of_mem
      (source_equation_retained codes s held temporary ambient equation member)))
  · obtain ⟨equation, member, rfl⟩ := List.mem_map.mp right
    exact Or.inl (Or.inr (Or.inl (List.mem_map_of_mem
      (source_equation_retained codes s held temporary ambient equation member))))
  · have different : occurrence ≠ temporary := fun same => temporaryFresh (same ▸ present)
    refine Or.inl (Or.inr (Or.inr ⟨occurrence, ?_, ?_⟩))
    · rw [result_present]
      exact Finset.mem_union_left _ present
    · rw [result_label_other codes s held temporary schema declared occurrence different]
      exact labelled
  · refine Or.inr ⟨occurrence, ?_, ?_⟩
    · rw [result_rules codes s held temporary persistent]
      exact present
    · rw [result_held codes s held temporary occurrence]
      exact argument

#print axioms represents_closure
#print axioms fresh
#print axioms shapes
#print axioms admitted
#print axioms reading_iff_models
#print axioms result_present
#print axioms result_rules
#print axioms result_held
#print axioms source_mentions_retained

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMaterializer
