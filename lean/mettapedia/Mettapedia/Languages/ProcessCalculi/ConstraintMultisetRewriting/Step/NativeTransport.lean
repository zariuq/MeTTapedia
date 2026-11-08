import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeInstance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Transport

/-!
# Renaming the occurrences of a native state

A **renaming** of a native state (`NativeState.rename`) applies a bijection `π` of occurrence
identities: the present occurrences are carried along `π` and the rows are reindexed, so the
occurrence `π o` of the renamed state holds the row of `o`. The frame, the private row family, the
scope ledger and the knowledge are unchanged. A native firing is renamed with it
(`NativeFiring.rename`): its selection, outputs, reuse flags and publication recipes are carried
along `π`, and so are its predicate queries, whose regions read the renamed identity (native labels
carry occurrence identities) and whose sightings are renamed (`renameQuery`). Rules and the solver
budget are unchanged.

## The solver does not see occurrence identities

The information problem of a renamed firing at the renamed state **is** the information problem of
the firing (`information_renamed`, `NativeFiring.information_rename`): scopes are allocated by port
position, and each port reads the row of the occurrence it selects. So the native solver runs on the
same problem with the same budget, and its return is the same.

## Transport laws

* **Admission is preserved** (`NativeFiring.realized_rename_iff`): shapes, physical enabling (as
  for the first-order step, `AnnotatedRuns.enabled_rename`), solvability, guards
  (`guardHolds_renamed`) and predicate queries (`renameQuery_holds_iff`).
* **Published results are transported** (`native_result_rename`): the result of the renamed firing
  is the renamed result. It is computed through the explicit form of a published state
  (`publishedOf`), which renaming commutes with (`publishedOf_rename`), and through the solver's
  determinacy on equal problems (`publishedOf_congr`).
* **The state isomorphism** (`renameStateIso`): a renaming is an isomorphism of states as the
  interface sees them, with the identity of frames and the renaming of occurrences.
* **Functoriality**: `NativeState.rename_refl`, `NativeState.rename_trans`; on events, a firing with
  its state, `NativeFiring.sigma_rename_refl` and `NativeFiring.sigma_rename_trans`; renaming a
  firing is inverted by `NativeFiring.unrename` (`rename_unrename`, `unrename_rename`).

The renamings are not yet the step's `Transport`: that also asks for a residual of a firing after
another firing, which the native data do not determine (`Step/NativeDiamond`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire regionOf mem_regionOf)
open ContextualPredicateQueryAdmission (WithQueries DataQuery nativeLabels)
open AnnotatedRuns (renameSelection)

/-! ## Port views under a renaming -/

/-- A list built port by port from renamed identities, each read back through the inverse, is the
list built from the identities. -/
theorem ofFn_renamed {α β : Type*} (l : List α) (π : α ≃ α) (G H : ℕ → α → β)
    (same : ∀ n a, G n a = H n a) :
    (List.ofFn fun p : Fin (l.map π).length => G p.val (π.symm ((l.map π).get p))) =
      List.ofFn fun p : Fin l.length => H p.val (l.get p) := by
  apply List.ext_getElem (by simp)
  intro n first second
  simp [same]

theorem mem_renameSelection_made {O : Type} (π : O ≃ O) (selection : Selection O) (o : O) :
    o ∈ (renameSelection π selection).made ↔ π.symm o ∈ selection.made := by
  constructor
  · intro member
    obtain ⟨a, inMade, rfl⟩ := List.mem_map.mp member
    simpa using inMade
  · intro member
    exact List.mem_map.mpr ⟨_, member, π.apply_symm_apply o⟩

/-- Renaming keeps the scope ledger a selection reserves: it depends on the port counts only. -/
theorem after_renamed {O : Type} (π : O ≃ O) (occupied : Finset ℕ) (selection : Selection O) :
    ContextualActivationScopes.after occupied (renameSelection π selection) =
      ContextualActivationScopes.after occupied selection := by
  simp [ContextualActivationScopes.after, ContextualActivationScopes.reserved,
    ContextualActivationScopes.count, renameSelection]

section Information

variable {S : Signature} {Local Shared O : Type} (locals : Local → MetaArity S)
  (captures : Shared → MetaArity S) {Γ : Ctx S} {sort : S.Srt} (π : O ≃ O)

/-- The take views of a renamed selection over reindexed rows are the take views. -/
theorem prepare_taken_renamed (occupied : Finset ℕ) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (label : O → Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort) :
    List.ofFn (ContextualSelectionViews.prepare locals captures occupied (renameSelection π selection) rule
        (fun o => label (π.symm o))).taken =
      List.ofFn (ContextualSelectionViews.prepare locals captures occupied selection rule label).taken :=
  ofFn_renamed selection.taken π
    (fun n o => ContextualFreshening.termAt locals captures (ContextualActivationScopes.start occupied + (1 + n))
      (label o))
    (fun n o => ContextualFreshening.termAt locals captures (ContextualActivationScopes.start occupied + (1 + n))
      (label o))
    fun _ _ => rfl

/-- The read views of a renamed selection over reindexed rows are the read views. -/
theorem prepare_read_renamed (occupied : Finset ℕ) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (label : O → Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort) :
    List.ofFn (ContextualSelectionViews.prepare locals captures occupied (renameSelection π selection) rule
        (fun o => label (π.symm o))).read =
      List.ofFn (ContextualSelectionViews.prepare locals captures occupied selection rule label).read :=
  ofFn_renamed selection.read π
    (fun n o => ContextualFreshening.termAt locals captures
      (ContextualActivationScopes.start occupied + (1 + (selection.taken.map π).length + n)) (label o))
    (fun n o => ContextualFreshening.termAt locals captures
      (ContextualActivationScopes.start occupied + (1 + selection.taken.length + n)) (label o))
    fun _ _ => by rw [List.length_map]

/-- **The equations a renamed selection adds are the equations the selection adds.** -/
theorem addedEquations_renamed (occupied : Finset ℕ) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    ContextualActivatedStep.addedEquations locals captures occupied (renameSelection π selection) rule
        (fun o => rows (π.symm o)) =
      ContextualActivatedStep.addedEquations locals captures occupied selection rule rows := by
  have taken := prepare_taken_renamed locals captures π occupied selection rule
    (fun o => ContextualStoredRows.asTemplate locals captures (rows o))
  have read := prepare_read_renamed locals captures π occupied selection rule
    (fun o => ContextualStoredRows.asTemplate locals captures (rows o))
  exact congrArg₂ (fun first second =>
    ContextualActivatedStep.useEquations
        (ContextualActivatedStep.prepared locals captures occupied selection rule rows).rule.take first ++
      ContextualActivatedStep.useEquations
        (ContextualActivatedStep.prepared locals captures occupied selection rule rows).rule.read second ++
      (ContextualActivatedStep.prepared locals captures occupied selection rule rows).rule.tell) taken read

/-- The latent equations of the rows a renamed selection reads are those the selection reads. -/
theorem latent_renamed (occupied : Finset ℕ) (selection : Selection O)
    (rows : O → ContextualConditionalRows.Row locals captures Γ sort) :
    ContextualConditionalExecution.latent locals captures occupied (renameSelection π selection)
        (fun o => rows (π.symm o)) =
      ContextualConditionalExecution.latent locals captures occupied selection rows := by
  have taken := ofFn_renamed selection.taken π
    (fun n o => (rows o).obligationsAt locals captures (ContextualActivationScopes.start occupied + (1 + n)))
    (fun n o => (rows o).obligationsAt locals captures (ContextualActivationScopes.start occupied + (1 + n)))
    fun _ _ => rfl
  have read := ofFn_renamed selection.read π
    (fun n o => (rows o).obligationsAt locals captures
      (ContextualActivationScopes.start occupied + (1 + (selection.taken.map π).length + n)))
    (fun n o => (rows o).obligationsAt locals captures
      (ContextualActivationScopes.start occupied + (1 + selection.taken.length + n)))
    fun _ _ => by rw [List.length_map]
  exact congrArg₂ (fun first second : List (ContextualResidual.Problem (ContextualActivatedStep.target locals captures)) =>
    first.flatten ++ second.flatten) taken read

/-- **The solver's problem does not see occurrence identities**: the information of a renamed
selection over reindexed rows is the information of the selection. -/
theorem information_renamed (occupied : Finset ℕ) (selection : Selection O)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualConditionalRows.Row locals captures Γ sort)
    (before : ContextualResidual.Problem captures) :
    ContextualConditionalExecution.information locals captures occupied (renameSelection π selection) rule
        (fun o => rows (π.symm o)) before =
      ContextualConditionalExecution.information locals captures occupied selection rule rows before := by
  have added := addedEquations_renamed locals captures π occupied selection rule (fun o => (rows o).value)
  have latent := latent_renamed locals captures π occupied selection rows
  exact congrArg₂ (fun added latent =>
    ContextualResidual.mapProblem (ContextualSelectionViews.capturedTarget locals captures) before ++
      ContextualResidual.observeProblem added ++ latent) added latent

/-- **Guards do not see occurrence identities**: a guard holds of reindexed rows over the renamed
world exactly when it holds of the rows over the world. -/
theorem guardHolds_renamed [DecidableEq O] {Next : Type} {next : Next → MetaArity S}
    (candidate : Assignment captures next) (rows : O → ContextualConditionalRows.Row locals captures Γ sort)
    (world : Finset O) (check : Check (Term (signature S captures) Γ sort)) :
    ContextualConditionalGuards.Holds locals candidate (fun o => rows (π.symm o)) (world.map π.toEmbedding) check ↔
      ContextualConditionalGuards.Holds locals candidate rows world check := by
  cases check with
  | equal _ _ => exact Iff.rfl
  | absent pattern =>
      simp only [ContextualConditionalGuards.Holds, Finset.forall_mem_map, Equiv.coe_toEmbedding,
        Equiv.symm_apply_apply]
  | count pattern cardinality =>
      have region : ContextualConditionalGuards.region locals candidate (fun o => rows (π.symm o))
          (world.map π.toEmbedding) pattern =
          (ContextualConditionalGuards.region locals candidate rows world pattern).map π.toEmbedding := by
        ext o
        simp only [ContextualConditionalGuards.mem_region, Finset.mem_map_equiv]
      simp only [ContextualConditionalGuards.Holds, region, Finset.card_map]

end Information

/-! ## Predicate queries under a renaming -/

section Queries

variable {O Label Candidate : Type*} (π : O ≃ O)

/-- **Rename a native predicate query**: its region reads the renamed identity, and its sightings
are renamed. Native labels carry occurrence identities, so the region must be renamed too. -/
def renameQuery (query : PredicateQueryAdmission.Query (O × Label) Candidate O) :
    PredicateQueryAdmission.Query (O × Label) Candidate O :=
  ⟨fun candidate label => query.region candidate (π.symm label.1, label.2), query.seen.map π.toEmbedding⟩

/-- A renamed query holds of reindexed labels over the renamed world exactly when the query holds. -/
theorem renameQuery_holds_iff (query : PredicateQueryAdmission.Query (O × Label) Candidate O)
    (candidate : Candidate) (label : O → Label) (world : Finset O) :
    ((renameQuery π query).atSolution candidate).Holds (fun o => (o, label (π.symm o)))
        (world.map π.toEmbedding) ↔
      (query.atSolution candidate).Holds (fun o => (o, label o)) world := by
  have region : regionOf (fun o => (o, label (π.symm o))) (world.map π.toEmbedding)
      ((renameQuery π query).atSolution candidate).region =
      (regionOf (fun o => (o, label o)) world (query.atSolution candidate).region).map π.toEmbedding := by
    ext o
    simp only [mem_regionOf, Finset.mem_map_equiv, renameQuery,
      PredicateQueryAdmission.Query.atSolution]
  change regionOf _ _ _ = query.seen.map π.toEmbedding ↔ regionOf _ _ _ = query.seen
  rw [region, Finset.map_inj]

theorem renameQuery_symm (query : PredicateQueryAdmission.Query (O × Label) Candidate O) :
    renameQuery π (renameQuery π.symm query) = query := by
  obtain ⟨region, seen⟩ := query
  have seenSame : (seen.map π.symm.toEmbedding).map π.toEmbedding = seen := by
    rw [Finset.map_map, ← Equiv.trans_toEmbedding, Equiv.symm_trans_self, Equiv.refl_toEmbedding,
      Finset.map_refl]
  simp only [renameQuery, Equiv.symm_symm, Equiv.apply_symm_apply, seenSame]

theorem renameQuery_symm' (query : PredicateQueryAdmission.Query (O × Label) Candidate O) :
    renameQuery π.symm (renameQuery π query) = query := by
  have := renameQuery_symm π.symm query
  rwa [Equiv.symm_symm] at this

theorem renameQuery_trans (ρ : O ≃ O) (query : PredicateQueryAdmission.Query (O × Label) Candidate O) :
    renameQuery ρ (renameQuery π query) = renameQuery (π.trans ρ) query := by
  obtain ⟨region, seen⟩ := query
  have seenSame : (seen.map π.toEmbedding).map ρ.toEmbedding = seen.map (π.trans ρ).toEmbedding := by
    rw [Finset.map_map, Equiv.trans_toEmbedding]
  simp only [renameQuery, seenSame]
  rfl

theorem renameQuery_refl (query : PredicateQueryAdmission.Query (O × Label) Candidate O) :
    renameQuery (Equiv.refl O) query = query := by
  obtain ⟨region, seen⟩ := query
  have seenSame : seen.map (Equiv.refl O).toEmbedding = seen := by
    rw [Equiv.refl_toEmbedding, Finset.map_refl]
  simp only [renameQuery, seenSame]
  rfl
end Queries

theorem renameSelection_symm {O : Type} (π : O ≃ O) (selection : Selection O) :
    renameSelection π (renameSelection π.symm selection) = selection := by
  obtain ⟨taken, read, made⟩ := selection
  simp [renameSelection]

theorem renameSelection_symm' {O : Type} (π : O ≃ O) (selection : Selection O) :
    renameSelection π.symm (renameSelection π selection) = selection := by
  have := renameSelection_symm π.symm selection
  rwa [Equiv.symm_symm] at this

theorem renameSelection_trans {O : Type} (π ρ : O ≃ O) (selection : Selection O) :
    renameSelection ρ (renameSelection π selection) = renameSelection (π.trans ρ) selection := by
  obtain ⟨taken, read, made⟩ := selection
  simp only [renameSelection, List.map_map, Equiv.coe_trans]

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt}

/-! ## Renaming native states -/

namespace NativeState

/-- **Rename the occurrences of a native state**: present occurrences are carried along `π`, and the
occurrence `π o` holds the row of `o`. Frame, private rows, scopes and knowledge are unchanged. -/
def rename (π : O ≃ O) (s : NativeState S O Γ sort) : NativeState S O Γ sort :=
  ⟨s.Local, s.localEquality, s.locals,
    { s.state with present := s.state.present.map π.toEmbedding, rows := fun o => s.state.rows (π.symm o) }⟩

theorem rename_refl (s : NativeState S O Γ sort) : s.rename (Equiv.refl O) = s := by
  obtain ⟨Local, localEquality, locals, ⟨Names, equality, declarations, occupied, equations, present, rows⟩⟩ := s
  have same : present.map (Equiv.refl O).toEmbedding = present := by
    rw [Equiv.refl_toEmbedding, Finset.map_refl]
  simp only [rename, same]
  rfl

theorem rename_trans (π ρ : O ≃ O) (s : NativeState S O Γ sort) :
    (s.rename π).rename ρ = s.rename (π.trans ρ) := by
  obtain ⟨Local, localEquality, locals, ⟨Names, equality, declarations, occupied, equations, present, rows⟩⟩ := s
  have same : (present.map π.toEmbedding).map ρ.toEmbedding = present.map (π.trans ρ).toEmbedding := by
    rw [Finset.map_map, Equiv.trans_toEmbedding]
  simp only [rename, same]
  rfl

theorem rename_symm (π : O ≃ O) (s : NativeState S O Γ sort) : (s.rename π).rename π.symm = s := by
  rw [rename_trans, Equiv.self_trans_symm, rename_refl]

end NativeState

/-! ## Renaming native firings -/

namespace NativeFiring

variable {s : NativeState S O Γ sort}

/-- Native firings with the same data are equal. -/
theorem ext' {f g : NativeFiring s} (rule : f.rule = g.rule) (selection : f.selection = g.selection)
    (outputs : f.outputs = g.outputs) (reusable : f.reusable = g.reusable) (queries : f.queries = g.queries)
    (fuel : f.fuel = g.fuel) (recipes : f.recipes = g.recipes) : f = g := by
  obtain ⟨rule₁, selection₁, outputs₁, reusable₁, queries₁, fuel₁, recipes₁, made₁⟩ := f
  obtain ⟨rule₂, selection₂, outputs₂, reusable₂, queries₂, fuel₂, recipes₂, made₂⟩ := g
  dsimp only at rule selection outputs reusable queries fuel recipes
  subst rule selection outputs reusable queries fuel recipes
  rfl

/-- **Rename a native firing** with its state: selection, outputs, reuse flags, recipes and
predicate queries are carried along `π`; the rule and the solver budget are unchanged. -/
def rename (π : O ≃ O) (f : NativeFiring s) : NativeFiring (s.rename π) where
  rule := f.rule
  selection := renameSelection π f.selection
  outputs o := f.outputs (π.symm o)
  reusable o := f.reusable (π.symm o)
  queries := f.queries.map (renameQuery π)
  fuel := f.fuel
  recipes o := f.recipes (π.symm o)
  recipes_made o notMade := f.recipes_made (π.symm o) fun made =>
    notMade ((mem_renameSelection_made π f.selection o).mpr made)

/-- **Carry a firing of the renamed state back**: the inverse of `rename`. -/
def unrename (π : O ≃ O) (g : NativeFiring (s.rename π)) : NativeFiring s where
  rule := g.rule
  selection := renameSelection π.symm g.selection
  outputs o := g.outputs (π o)
  reusable o := g.reusable (π o)
  queries := g.queries.map (renameQuery π.symm)
  fuel := g.fuel
  recipes o := g.recipes (π o)
  recipes_made o notMade := g.recipes_made (π o) fun made =>
    notMade ((mem_renameSelection_made π.symm g.selection o).mpr (by simpa using made))

theorem rename_unrename (π : O ≃ O) (g : NativeFiring (s.rename π)) : (unrename π g).rename π = g :=
  ext' rfl (renameSelection_symm π g.selection) (funext fun o => congrArg g.outputs (π.apply_symm_apply o))
    (funext fun o => congrArg g.reusable (π.apply_symm_apply o))
    ((List.map_map ..).trans ((List.map_congr_left fun query _ => renameQuery_symm π query).trans
      (List.map_id g.queries)))
    rfl (funext fun o => congrArg g.recipes (π.apply_symm_apply o))

theorem unrename_rename (π : O ≃ O) (f : NativeFiring s) : unrename π (f.rename π) = f :=
  ext' rfl (renameSelection_symm' π f.selection) (funext fun o => congrArg f.outputs (π.symm_apply_apply o))
    (funext fun o => congrArg f.reusable (π.symm_apply_apply o))
    ((List.map_map ..).trans ((List.map_congr_left fun query _ => renameQuery_symm' π query).trans
      (List.map_id f.queries)))
    rfl (funext fun o => congrArg f.recipes (π.symm_apply_apply o))

/-- **The information of a renamed firing is the firing's information**, so the solver runs on the
same problem. -/
theorem information_rename (π : O ≃ O) (f : NativeFiring s) : (f.rename π).information = f.information :=
  information_renamed s.locals s.state.declarations π s.state.occupied f.selection f.rule s.state.rows
    s.state.equations


/-- Firings at two states that differ only in their present occurrences are one event when their
data agree. -/
theorem sigma_eq_of_present {Local : Type} {localEquality : DecidableEq Local} {locals : Local → MetaArity S}
    {Names : Type} {equality : DecidableEq Names} {declarations : Names → MetaArity S} {occupied : Finset ℕ}
    {equations : ContextualResidual.Problem declarations}
    {rows : O → ContextualConditionalRows.Row locals declarations Γ sort} {first second : Finset O}
    (same : first = second)
    (f : NativeFiring (⟨Local, localEquality, locals,
      ⟨Names, equality, declarations, occupied, equations, first, rows⟩⟩ : NativeState S O Γ sort))
    (g : NativeFiring (⟨Local, localEquality, locals,
      ⟨Names, equality, declarations, occupied, equations, second, rows⟩⟩ : NativeState S O Γ sort))
    (rule : f.rule = g.rule) (selection : f.selection = g.selection) (outputs : f.outputs = g.outputs)
    (reusable : f.reusable = g.reusable) (queries : f.queries = g.queries) (fuel : f.fuel = g.fuel)
    (recipes : f.recipes = g.recipes) :
    (⟨_, f⟩ : (t : NativeState S O Γ sort) × NativeFiring t) = ⟨_, g⟩ := by
  subst same
  rw [ext' rule selection outputs reusable queries fuel recipes]

/-- **Renaming events is functorial**: renaming by `π` then `ρ` is renaming by `π.trans ρ`. -/
theorem sigma_rename_trans (π ρ : O ≃ O) (s : NativeState S O Γ sort) (f : NativeFiring s) :
    (⟨(s.rename π).rename ρ, (f.rename π).rename ρ⟩ : (t : NativeState S O Γ sort) × NativeFiring t) =
      ⟨s.rename (π.trans ρ), f.rename (π.trans ρ)⟩ := by
  obtain ⟨Local, localEquality, locals, ⟨Names, equality, declarations, occupied, equations, present, rows⟩⟩ := s
  refine sigma_eq_of_present ?_ _ _ rfl (renameSelection_trans π ρ f.selection) rfl rfl ?_ rfl rfl
  · exact (Finset.map_map _ _ _).trans (by rw [Equiv.trans_toEmbedding])
  · exact (List.map_map ..).trans (List.map_congr_left fun query _ => renameQuery_trans π ρ query)

/-- **Renaming events by the identity changes nothing.** -/
theorem sigma_rename_refl (s : NativeState S O Γ sort) (f : NativeFiring s) :
    (⟨s.rename (Equiv.refl O), f.rename (Equiv.refl O)⟩ : (t : NativeState S O Γ sort) × NativeFiring t) =
      ⟨s, f⟩ := by
  obtain ⟨Local, localEquality, locals, ⟨Names, equality, declarations, occupied, equations, present, rows⟩⟩ := s
  refine sigma_eq_of_present ?_ _ _ rfl (renameSelection_refl f.selection) rfl rfl ?_ rfl rfl
  · exact (by rw [Equiv.refl_toEmbedding, Finset.map_refl])
  · exact (List.map_congr_left fun query _ => renameQuery_refl query).trans (List.map_id _)

end NativeFiring

variable [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **A renaming is an isomorphism of states as the interface sees it**: the identity of frames, the
same knowledge, and the renaming of present occurrences. -/
noncomputable def renameStateIso (π : O ≃ O) (s : NativeState S O Γ sort) :
    (native (S := S) (O := O) (Γ := Γ) (sort := sort)).StateIso s (s.rename π) :=
  ⟨Frames.Iso.refl _, Frames.Iso.equivalent_refl _, π, rfl⟩

namespace NativeFiring

variable {s : NativeState S O Γ sort}

theorem shapes_rename (π : O ≃ O) (f : NativeFiring s) :
    (native (S := S) (O := O) (Γ := Γ) (sort := sort)).Shapes (f.rename π) ↔ native.Shapes f := by
  show (f.selection.taken.map π).Nodup ∧ (f.selection.made.map π).Nodup ∧
      f.rule.take.length = (f.selection.taken.map π).length ∧
      f.rule.read.length = (f.selection.read.map π).length ∧
      (f.selection.made.map π).map (fun o => f.outputs (π.symm o)) = (f.rename π).prepared.rule.produce ↔ _
  have outputs : (f.selection.made.map π).map (fun o => f.outputs (π.symm o)) = f.selection.made.map f.outputs := by
    rw [List.map_map]
    exact List.map_congr_left fun o _ => by simp
  rw [List.nodup_map_iff π.injective, List.nodup_map_iff π.injective, List.length_map, List.length_map, outputs]
  exact Iff.rfl

theorem holds_rename (π : O ≃ O) (f : NativeFiring s) (b : Frames.Frame S)
    (σ : Assignment s.infoFrame.arity b.arity) :
    (native (S := S) (O := O) (Γ := Γ) (sort := sort)).Holds (f.rename π) b σ ↔ native.Holds f b σ := by
  refine and_congr (forall₂_congr fun check _ =>
    guardHolds_renamed s.locals _ π σ
      (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present check) ?_
  show (∀ query ∈ f.queries.map (renameQuery π), _) ↔ _
  rw [List.forall_mem_map]
  exact forall₂_congr fun query _ => renameQuery_holds_iff π query _
    (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present

/-- **Admission is preserved by renaming**, with predicate queries and recipes. -/
theorem realized_rename_iff (π : O ≃ O) (f : NativeFiring s) : (f.rename π).Realized ↔ f.Realized := by
  rw [native_admits_iff, native_admits_iff]
  refine and_congr (shapes_rename π f) (and_congr ?_ (and_congr ?_ ?_))
  · exact AnnotatedRuns.enabled_rename (π := π) (label := fun _ : O => ()) s.state.present f.selection
  · rw [information_rename]
    exact Iff.rfl
  · rw [information_rename]
    exact forall_congr' fun b => forall_congr' fun σ => imp_congr_right fun _ => holds_rename π f b σ

theorem realized_unrename_iff (π : O ≃ O) (g : NativeFiring (s.rename π)) :
    (unrename π g).Realized ↔ g.Realized := by
  rw [← realized_rename_iff π (unrename π g), rename_unrename]

end NativeFiring

/-! ## Published results under a renaming -/

/-- **The published state of a solver return**, written out: the state's frame extended by the
return, its information carried along it, the physical result of the selection, and the rows
published through the recipes. -/
def publishedOf (s : NativeState S O Γ sort)
    (problem : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations))
    (update : ContextualFrameUpdate.Update problem) (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)
    (reusable : O → Bool) (recipes : Recipes s) : NativeState S O Γ sort :=
  ⟨s.Local ⊕ update.Variables, by letI := update.equality; exact inferInstance,
    ContextualPublication.privateFamily s.locals update.declaration,
    { Names := (Mettapedia.Logic.LP.ScopedVar s.Local ⊕ s.state.Names) ⊕ (update.Variables ⊕ Empty)
      equality := by let _ := s.state.equality; let _ := update.equality; infer_instance
      declarations := ContextualComputedFreshFrame.active
        (ContextualActivatedStep.target s.locals s.state.declarations) update.declaration
      occupied := ContextualFreshFrameScopeLedger.helperLedger
        (ContextualActivationScopes.after s.state.occupied selection)
      equations := ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource update) problem
      present := fire s.state.present (selection.commit (T := Unit))
      rows := fun occurrence =>
        match recipes occurrence with
        | some recipe => ContextualConditionalPublication.extendPrivate s.locals update.declaration _
            (recipe.publish (ContextualComputedFreshFrame.includeSource update) (outputs occurrence))
        | none =>
            if occurrence ∈ selection.made then
              if reusable occurrence then
                ContextualConditionalPublication.ordinary s.locals update.declaration _
                  (ContextualConditionalAnswers.ofUpdate update (outputs occurrence))
              else ContextualConditionalRows.ofStored _ _
                (.shared (instantiate (ContextualComputedFreshFrame.includeSource update) (outputs occurrence)))
            else ContextualConditionalPublication.extendPrivate s.locals update.declaration _
              ((s.state.rows occurrence).map s.locals s.state.declarations
                (Assignment.compose (ContextualComputedFreshFrame.includeSource update)
                  (ContextualSelectionViews.capturedTarget s.locals s.state.declarations))) }⟩

theorem publishedState_eq_publishedOf {s : NativeState S O Γ sort} (recipes : Recipes s)
    (firing : ContextualConditionalExecution.Firing s.locals s.state) :
    publishedState recipes firing =
      publishedOf s _ firing.update firing.selection firing.outputs firing.reusable recipes :=
  rfl

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Renaming commutes with publication.** -/
theorem publishedOf_rename (π : O ≃ O) (s : NativeState S O Γ sort)
    (problem : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations))
    (update : ContextualFrameUpdate.Update problem) (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)
    (reusable : O → Bool) (recipes : Recipes s) :
    (publishedOf s problem update selection outputs reusable recipes).rename π =
      publishedOf (s.rename π) problem update (renameSelection π selection) (fun o => outputs (π.symm o))
        (fun o => reusable (π.symm o)) (fun o => recipes (π.symm o)) := by
  have occupied := after_renamed π s.state.occupied selection
  have present := AnnotatedRuns.fire_rename (T := Unit) (π := π) s.state.present selection
  have made := mem_renameSelection_made π selection
  simp only [publishedOf, NativeState.rename, occupied, present]
  congr 2
  funext o
  cases recipes (π.symm o) with
  | some recipe => rfl
  | none =>
      by_cases inMade : π.symm o ∈ selection.made
      · rw [if_pos inMade, if_pos ((made o).mpr inMade)]
      · rw [if_neg inMade, if_neg fun member => inMade ((made o).mp member)]

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **The solver is determinate**: equal problems at one budget give the same published state. -/
theorem publishedOf_congr (s : NativeState S O Γ sort)
    (run : (problem : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations)) →
      ContextualFrameWorklist.Result problem)
    {first second : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations)}
    (same : first = second) {u : ContextualFrameUpdate.Update first} {v : ContextualFrameUpdate.Update second}
    (returnedFirst : run first = .residual u) (returnedSecond : run second = .residual v)
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)
    (reusable : O → Bool) (recipes : Recipes s) :
    publishedOf s first u selection outputs reusable recipes = publishedOf s second v selection outputs reusable recipes := by
  subst same
  cases returnedFirst.symm.trans returnedSecond
  rfl

/-- **Executions with renamed data publish the renamed state.** -/
theorem publishedState_rename (π : O ≃ O) {s : NativeState S O Γ sort} (recipes : Recipes s)
    (firing : ContextualConditionalExecution.Firing s.locals s.state)
    (renamed : ContextualConditionalExecution.Firing (s.rename π).locals (s.rename π).state)
    (rule : renamed.rule = firing.rule) (selection : renamed.selection = renameSelection π firing.selection)
    (outputs : renamed.outputs = fun o => firing.outputs (π.symm o))
    (reusable : renamed.reusable = fun o => firing.reusable (π.symm o)) (fuel : renamed.fuel = firing.fuel) :
    publishedState (s := s.rename π) (fun o => recipes (π.symm o)) renamed = (publishedState recipes firing).rename π := by
  obtain ⟨rule', selection', outputs', reusable', admitted', fuel', update', computed'⟩ := renamed
  dsimp only at rule selection outputs reusable fuel
  subst rule selection outputs reusable fuel
  refine (publishedState_eq_publishedOf (s := s.rename π) _ _).trans (Eq.trans ?_
    (publishedOf_rename π s _ firing.update firing.selection firing.outputs firing.reusable recipes).symm)
  exact publishedOf_congr (s.rename π)
    (fun problem => letI := s.state.equality
      ContextualFrameWorklist.run firing.fuel (ContextualActivatedStep.target s.locals s.state.declarations) problem)
    (information_renamed s.locals s.state.declarations π s.state.occupied firing.selection firing.rule s.state.rows
      s.state.equations) computed' firing.computed _ _ _ _

/-- **The result of a renamed native firing is the renamed result**: the solver returns the same
answer, and publication commutes with the renaming. -/
theorem native_result_rename (π : O ≃ O) {s : NativeState S O Γ sort} (f : NativeFiring s)
    (realized : f.Realized) (realized' : (f.rename π).Realized) :
    native.result (f.rename π) realized' = (native.result f realized).rename π := by
  change publishedState (s := s.rename π) (fun o => f.recipes (π.symm o)) ((f.rename π).pinned realized').firing =
    (publishedState f.recipes (f.pinned realized).firing).rename π
  have reusableOne : ((f.rename π).pinned realized').firing.reusable = (f.rename π).reusable :=
    ((f.rename π).pinned realized').intents
  have reusableTwo : (f.pinned realized).firing.reusable = f.reusable := (f.pinned realized).intents
  exact publishedState_rename π f.recipes _ _
    (((f.rename π).pinned realized').authored.trans (f.pinned realized).authored.symm)
    (((f.rename π).pinned realized').selected.trans
      (congrArg (renameSelection π) (f.pinned realized).selected.symm))
    (((f.rename π).pinned realized').values.trans
      (congrArg (fun outputs => fun o => outputs (π.symm o)) (f.pinned realized).values.symm))
    (reusableOne.trans (congrArg (fun reusable => fun o => reusable (π.symm o)) reusableTwo.symm))
    ((NativeFiring.pinned_fuel _ realized').trans (NativeFiring.pinned_fuel f realized).symm)

/-- Results depend on a firing, not on the proof of its admission. -/
theorem native_result_congr {s : NativeState S O Γ sort} {f g : NativeFiring s} (same : f = g)
    (first : f.Realized) (second : g.Realized) :
    native.result f first = native.result g second := by
  subst same
  rfl

/-- **The result of a carried-back firing, renamed, is the result of the firing.** -/
theorem native_result_unrename (π : O ≃ O) {s : NativeState S O Γ sort} (g : NativeFiring (s.rename π))
    (realized : (NativeFiring.unrename π g).Realized) (realized' : g.Realized) :
    (native.result (NativeFiring.unrename π g) realized).rename π = native.result g realized' := by
  rw [← native_result_rename π _ realized ((NativeFiring.realized_rename_iff π _).mpr realized)]
  exact native_result_congr (NativeFiring.rename_unrename π g) _ _

#print axioms ofFn_renamed
#print axioms after_renamed
#print axioms information_renamed
#print axioms guardHolds_renamed
#print axioms renameQuery_holds_iff
#print axioms NativeState.rename_refl
#print axioms NativeState.rename_trans
#print axioms NativeState.rename_symm
#print axioms NativeFiring.rename_unrename
#print axioms NativeFiring.unrename_rename
#print axioms NativeFiring.sigma_rename_trans
#print axioms NativeFiring.sigma_rename_refl
#print axioms NativeFiring.information_rename
#print axioms NativeFiring.realized_rename_iff
#print axioms NativeFiring.realized_unrename_iff
#print axioms publishedOf_rename
#print axioms publishedOf_congr
#print axioms publishedState_rename
#print axioms native_result_rename
#print axioms native_result_unrename

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
