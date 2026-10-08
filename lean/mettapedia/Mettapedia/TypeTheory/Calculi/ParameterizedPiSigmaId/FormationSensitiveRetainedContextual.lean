import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRuleSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveCwf

/-!
# Contextual structure with supplied formation and typing trees

A formed telescope contains a Type-valued spine of the actual supplied
formation trees. Types, terms and substitution components retain their own
trees. Substitution acts on those trees directly, including under binders;
erasure only reads their existing soundness theorem.

This construction concerns substitution and context comprehension. It does
not impose semantic computation equations on the retained histories or
assert arbitrary-model interpretation or classifying initiality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveRetainedContextual

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open FormationSensitiveRuleSignature

variable {Head : Type} {rules : Rules Head}

/-- Each telescope entry retains its independently supplied formation tree. -/
inductive Spine (rules : Rules Head) : {n : Nat} → Ctx Head n → Type where
  | nil : Spine rules .nil
  | snoc {n : Nat} {Γ : Ctx Head n} {A : Presentation.Tm Head n} {level : Head}
      (prior : Spine rules Γ) (universeWitness : rules.isUniverse level)
      (formation : Tree rules (judgment Γ A (.head level))) :
      Spine rules (.snoc Γ A)

namespace Spine

theorem sound {n : Nat} {Γ : Ctx Head n} (spine : Spine rules Γ) :
    FormationSensitive.ContextFormation rules Γ := by
  induction spine with
  | nil => exact .nil
  | snoc _ witness formation prior =>
      exact .snoc prior (FormationSensitiveRuleSignature.sound formation) witness

end Spine

structure Context (rules : Rules Head) where
  arity : Nat
  raw : Ctx Head arity
  spine : Spine rules raw

def Context.erase (context : Context rules) : FormationSensitiveContextual.Context rules :=
  ⟨context.arity, context.raw, context.spine.sound⟩

structure Hom (source target : Context rules) where
  substitution : Sub Head target.arity source.arity
  components : TreeSubstitution (R := rules) target.raw source.raw substitution

@[ext] theorem Hom.ext {source target : Context rules} {first second : Hom source target}
    (same : first.substitution = second.substitution)
    (evidence : HEq first.components second.components) : first = second := by
  cases first
  cases second
  cases same
  cases eq_of_heq evidence
  rfl

noncomputable def identity (context : Context rules) : Hom context context :=
  ⟨ids, TreeSubstitution.identity context.raw⟩

/-- Composition traverses the actual later components with the earlier
supplied component trees. -/
noncomputable def compose {source middle target : Context rules}
    (earlier : Hom source middle) (later : Hom middle target) : Hom source target :=
  ⟨subComp earlier.substitution later.substitution, later.components.comp earlier.components⟩

theorem identity_compose {source target : Context rules} (morphism : Hom source target) :
    compose (identity source) morphism = morphism :=
  Hom.ext (subComp_ids_left morphism.substitution)
    (TreeSubstitution.comp_identity_right morphism.components)

theorem compose_identity {source target : Context rules} (morphism : Hom source target) :
    compose morphism (identity target) = morphism :=
  Hom.ext (subComp_ids_right morphism.substitution)
    (TreeSubstitution.comp_identity_left morphism.components)

theorem compose_assoc {first second third fourth : Context rules}
    (earlier : Hom first second) (middle : Hom second third) (later : Hom third fourth) :
    compose (compose earlier middle) later = compose earlier (compose middle later) :=
  Hom.ext (subComp_assoc earlier.substitution middle.substitution later.substitution).symm
    (TreeSubstitution.comp_associativity later.components middle.components earlier.components).symm

noncomputable instance contextCategory (rules : Rules Head) : Category (Context rules) where
  Hom := Hom
  id := identity
  comp := compose
  id_comp := identity_compose
  comp_id := compose_identity
  assoc := compose_assoc

def Hom.erase {source target : Context rules} (morphism : Hom source target) :
    source.erase ⟶ target.erase :=
  ⟨morphism.substitution, fun index => FormationSensitiveRuleSignature.sound (morphism.components index)⟩

noncomputable def eraseBase (rules : Rules Head) :
    Context rules ⥤ FormationSensitiveContextual.Context rules where
  obj := Context.erase
  map := Hom.erase
  map_id _ := FormationSensitiveContextual.Hom.ext rfl
  map_comp _ _ := FormationSensitiveContextual.Hom.ext rfl

def empty (rules : Rules Head) : Context rules := ⟨0, .nil, .nil⟩

def toEmpty (source : Context rules) : source ⟶ empty rules :=
  ⟨Fin.elim0, fun index => Fin.elim0 index⟩

theorem toEmpty_unique (source : Context rules) (morphism : source ⟶ empty rules) :
    morphism = toEmpty source := by
  apply Hom.ext
  · funext index; exact Fin.elim0 index
  · apply Function.hfunext rfl
    intro index _ _
    exact Fin.elim0 index

/-- Formation evidence remains part of the type object, independently from
the telescope spine. -/
structure TypeOver (context : Context rules) where
  code : Presentation.Tm Head context.arity
  level : Head
  universeWitness : rules.isUniverse level
  formation : Tree rules (judgment context.raw code (.head level))

@[ext] theorem TypeOver.ext {context : Context rules} {first second : TypeOver context}
    (codes : first.code = second.code) (levels : first.level = second.level)
    (evidence : HEq first.formation second.formation) : first = second := by
  cases first
  cases second
  cases codes
  cases levels
  cases eq_of_heq evidence
  rfl

def TypeOver.erase {context : Context rules} (type : TypeOver context) :
    FormationSensitiveContextual.TypeOver context.erase :=
  ⟨type.code, type.level, type.universeWitness, FormationSensitiveRuleSignature.sound type.formation⟩

noncomputable def TypeOver.reindex {source target : Context rules} (type : TypeOver target)
    (morphism : source ⟶ target) : TypeOver source :=
  ⟨subst morphism.substitution type.code, type.level, type.universeWitness,
    type.formation.substitute morphism.components⟩

theorem TypeOver.reindex_id {context : Context rules} (type : TypeOver context) :
    type.reindex (𝟙 context) = type :=
  TypeOver.ext (subst_ids type.code) rfl (Tree.substitute_identity type.formation)

theorem TypeOver.reindex_comp {source middle target : Context rules} (type : TypeOver target)
    (earlier : source ⟶ middle) (later : middle ⟶ target) :
    type.reindex (earlier ≫ later) = (type.reindex later).reindex earlier :=
  TypeOver.ext (subst_subComp earlier.substitution later.substitution type.code).symm rfl
    (Tree.substitute_composition type.formation later.components earlier.components).symm

@[simp] theorem TypeOver.erase_reindex {source target : Context rules}
    (type : TypeOver target) (morphism : source ⟶ target) :
    (type.reindex morphism).erase = type.erase.reindex morphism.erase :=
  FormationSensitiveContextual.TypeOver.ext rfl rfl

structure Term (context : Context rules) (type : TypeOver context) where
  code : Presentation.Tm Head context.arity
  evidence : Tree rules (judgment context.raw code type.code)

@[ext] theorem Term.ext {context : Context rules} {type : TypeOver context}
    {first second : Term context type} (codes : first.code = second.code)
    (evidence : HEq first.evidence second.evidence) : first = second := by
  cases first
  cases second
  cases codes
  cases eq_of_heq evidence
  rfl

def Term.erase {context : Context rules} {type : TypeOver context} (term : Term context type) :
    FormationSensitiveContextual.Term context.erase type.erase :=
  ⟨term.code, FormationSensitiveRuleSignature.sound term.evidence⟩

noncomputable def Term.reindex {source target : Context rules} {type : TypeOver target}
    (term : Term target type) (morphism : source ⟶ target) :
    Term source (type.reindex morphism) :=
  ⟨subst morphism.substitution term.code, term.evidence.substitute morphism.components⟩

def Term.cast {context : Context rules} {first second : TypeOver context}
    (same : first = second) (term : Term context first) : Term context second := same ▸ term

@[simp] theorem Term.cast_code {context : Context rules} {first second : TypeOver context}
    (same : first = second) (term : Term context first) : (term.cast same).code = term.code := by
  cases same
  rfl

theorem Term.cast_evidence {context : Context rules} {first second : TypeOver context}
    (same : first = second) (term : Term context first) :
    HEq (term.cast same).evidence term.evidence := by
  cases same
  rfl

@[simp] theorem Term.castCongrArg_code {context : Context rules}
    {first second : TypeOver context} (same : first = second) (term : Term context first) :
    (_root_.cast (congrArg (Term context) same) term).code = term.code := by
  cases same
  rfl

theorem Term.castCongrArg_evidence {context : Context rules}
    {first second : TypeOver context} (same : first = second) (term : Term context first) :
    HEq (_root_.cast (congrArg (Term context) same) term).evidence term.evidence := by
  cases same
  rfl

theorem Term.cast_eq_castCongrArg {context : Context rules}
    {first second : TypeOver context} (same : first = second) (term : Term context first) :
    term.cast same = _root_.cast (congrArg (Term context) same) term := by
  cases same
  rfl

theorem Term.reindex_id {context : Context rules} {type : TypeOver context}
    (term : Term context type) : (term.reindex (𝟙 context)).cast type.reindex_id = term := by
  apply Term.ext
  · rw [Term.cast_code]; exact subst_ids term.code
  · exact (Term.cast_evidence type.reindex_id _).trans (Tree.substitute_identity term.evidence)

theorem Term.reindex_comp {source middle target : Context rules} {type : TypeOver target}
    (term : Term target type) (earlier : source ⟶ middle) (later : middle ⟶ target) :
    (term.reindex (earlier ≫ later)).cast (type.reindex_comp earlier later) =
      (term.reindex later).reindex earlier := by
  apply Term.ext
  · rw [Term.cast_code]
    exact (subst_subComp earlier.substitution later.substitution term.code).symm
  · exact (Term.cast_evidence (type.reindex_comp earlier later) _).trans
      (Tree.substitute_composition term.evidence later.components earlier.components).symm

/-! ## Comprehension preserves the supplied trees -/

def treeCast {n : Nat} {Γ : Ctx Head n} {subject first second : Presentation.Tm Head n}
    (same : first = second) (tree : Tree rules (judgment Γ subject first)) :
    Tree rules (judgment Γ subject second) :=
  _root_.cast (congrArg (fun type => Tree rules (judgment Γ subject type)) same) tree

theorem treeCast_heq {n : Nat} {Γ : Ctx Head n} {subject first second : Presentation.Tm Head n}
    (same : first = second) (tree : Tree rules (judgment Γ subject first)) :
    HEq (treeCast same tree) tree := cast_heq _ _

abbrev extend (context : Context rules) (type : TypeOver context) : Context rules :=
  ⟨context.arity + 1, .snoc context.raw type.code,
    .snoc context.spine type.universeWitness type.formation⟩

noncomputable def projectionHom (context : Context rules) (type : TypeOver context) :
    extend context type ⟶ context where
  substitution := projection
  components := by
    intro index
    change Tree rules (judgment (.snoc context.raw type.code) (.var index.succ)
      (subst projection (Ctx.lookup context.raw index)))
    exact treeCast (by rw [Ctx.lookup_snoc_succ, subst_projection])
      (Tree.variableLeaf (R := rules) (.snoc context.raw type.code) index.succ)

theorem projection_component (context : Context rules) (type : TypeOver context)
    (index : Fin context.arity) :
    HEq ((projectionHom context type).components index)
      (Tree.variableLeaf (R := rules) (.snoc context.raw type.code) index.succ) := by
  exact treeCast_heq (by rw [Ctx.lookup_snoc_succ, subst_projection])
    (Tree.variableLeaf (R := rules) (.snoc context.raw type.code) index.succ)

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing by the retained projection equals actual weakening on every
supplied tree, including its binding children. -/
theorem projection_substitute {context : Context rules} (type : TypeOver context)
    {subject annotation : Presentation.Tm Head context.arity}
    (tree : Tree rules (judgment context.raw subject annotation)) :
    HEq (tree.substitute (projectionHom context type).components)
      (Tree.weaken (extension := type.code) tree) := by
  let compatible : CtxRen context.raw (.snoc context.raw type.code) wk := fun _ => rfl
  let identityTrees := TreeSubstitution.identity (R := rules) context.raw
  have componentComparison :
      HEq (identityTrees.postcompose compatible) (projectionHom context type).components := by
    apply Function.hfunext rfl
    intro index other same
    cases same
    refine (TreeSubstitution.postcompose_component identityTrees compatible index).trans ?_
    refine (Tree.rename_heq ?_ (TreeSubstitution.identity_component context.raw index)
      compatible compatible rfl (HEq.refl _)).trans ?_
    · simp only [judgment, ids, subst_ids]
    · exact (Tree.rename_variableLeaf compatible index).trans
        (projection_component context type index).symm
  have renamedIdentity :
      HEq ((tree.substitute identityTrees).rename compatible)
        (Tree.weaken (extension := type.code) tree) :=
    Tree.rename_heq (by simp only [judgment, subst_ids]) (Tree.substitute_identity tree)
      compatible compatible rfl (HEq.refl _)
  exact (renamedIdentity.symm.trans (Tree.rename_substitute tree identityTrees compatible) |>.trans
    (Tree.substitute_congr tree (identityTrees.postcompose compatible)
      (projectionHom context type).components rfl rfl componentComparison)).symm

noncomputable def newest (context : Context rules) (type : TypeOver context) :
    Term (extend context type) (type.reindex (projectionHom context type)) where
  code := .var 0
  evidence := by
    change Tree rules (judgment (.snoc context.raw type.code) (.var 0)
      (subst projection type.code))
    exact treeCast (by rw [Ctx.lookup_snoc_zero, subst_projection])
      (Tree.variableLeaf (R := rules) (.snoc context.raw type.code) (0 : Fin (context.arity + 1)))

theorem newest_evidence (context : Context rules) (type : TypeOver context) :
    HEq (newest context type).evidence
      (Tree.variableLeaf (R := rules) (.snoc context.raw type.code) (0 : Fin (context.arity + 1))) := by
  exact treeCast_heq (by rw [Ctx.lookup_snoc_zero, subst_projection])
    (Tree.variableLeaf (R := rules) (.snoc context.raw type.code) (0 : Fin (context.arity + 1)))

/-- Pairing uses the supplied newest term and the supplied older component
trees, rather than rebuilding them from their typing propositions. -/
noncomputable def pair {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ target) (term : Term source (type.reindex morphism)) :
    source ⟶ extend target type where
  substitution := consSub term.code morphism.substitution
  components := by
    intro index
    refine Fin.cases ?_ (fun prior => ?_) index
    · exact treeCast (by
        dsimp only [TypeOver.reindex]
        rw [Ctx.lookup_snoc_zero, subst_consSub_rename_wk]) term.evidence
    · exact treeCast (by rw [Ctx.lookup_snoc_succ, subst_consSub_rename_wk])
        (morphism.components prior)

theorem pair_component_zero {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ target) (term : Term source (type.reindex morphism)) :
    HEq ((pair morphism term).components 0) term.evidence := by
  simp only [pair, Fin.cases_zero]
  exact treeCast_heq _ _

theorem pair_component_succ {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ target) (term : Term source (type.reindex morphism))
    (index : Fin target.arity) :
    HEq ((pair morphism term).components index.succ) (morphism.components index) := by
  simp only [pair, Fin.cases_succ]
  exact treeCast_heq _ _

set_option backward.isDefEq.respectTransparency false in
theorem pair_projection {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ target) (term : Term source (type.reindex morphism)) :
    pair morphism term ≫ projectionHom target type = morphism := by
  apply Hom.ext
  · exact subComp_consSub_projection term.code morphism.substitution
  · apply Function.hfunext rfl
    intro index other same
    cases same
    refine (TreeSubstitution.comp_component (projectionHom target type).components
      (pair morphism term).components index).trans ?_
    refine (Tree.substitute_heq ?_ (projection_component target type index)
      (pair morphism term).components (pair morphism term).components
      rfl (HEq.refl _) (HEq.refl _)).trans ?_
    · change judgment (.snoc target.raw type.code) (.var index.succ)
        (subst projection (Ctx.lookup target.raw index)) =
        judgment (.snoc target.raw type.code) (.var index.succ)
          (Ctx.lookup (.snoc target.raw type.code) index.succ)
      simp only [subst_projection, Ctx.lookup_snoc_succ]
    · rw [Tree.substitute_variableLeaf]
      exact pair_component_succ morphism term index

set_option backward.isDefEq.respectTransparency false in
theorem newest_pair_evidence {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ target) (term : Term source (type.reindex morphism)) :
    HEq ((newest target type).reindex (pair morphism term)).evidence term.evidence := by
  refine (Tree.substitute_heq ?_ (newest_evidence target type)
    (pair morphism term).components (pair morphism term).components
    rfl (HEq.refl _) (HEq.refl _)).trans ?_
  · change judgment (.snoc target.raw type.code) (.var 0) (subst projection type.code) =
      judgment (.snoc target.raw type.code) (.var 0)
        (Ctx.lookup (.snoc target.raw type.code) 0)
    simp only [subst_projection, Ctx.lookup_snoc_zero]
  · rw [Tree.substitute_variableLeaf]
    exact pair_component_zero morphism term

noncomputable def pulledNewest {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ extend target type) :
    Term source (type.reindex (morphism ≫ projectionHom target type)) :=
  ((newest target type).reindex morphism).cast
    (type.reindex_comp morphism (projectionHom target type)).symm

@[simp] theorem pulledNewest_code {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ extend target type) :
    (pulledNewest morphism).code = morphism.substitution 0 := by
  rw [pulledNewest, Term.cast_code]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pulledNewest_evidence {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ extend target type) :
    HEq (pulledNewest morphism).evidence (morphism.components 0) := by
  refine (Term.cast_evidence _ _).trans ?_
  refine (Tree.substitute_heq ?_ (newest_evidence target type)
    morphism.components morphism.components rfl (HEq.refl _) (HEq.refl _)).trans ?_
  · change judgment (.snoc target.raw type.code) (.var 0) (subst projection type.code) =
      judgment (.snoc target.raw type.code) (.var 0)
        (Ctx.lookup (.snoc target.raw type.code) 0)
    simp only [subst_projection, Ctx.lookup_snoc_zero]
  · exact heq_of_eq (Tree.substitute_variableLeaf morphism.components 0)

set_option backward.isDefEq.respectTransparency false in
theorem pair_eta {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ extend target type) :
    pair (morphism ≫ projectionHom target type) (pulledNewest morphism) = morphism := by
  apply Hom.ext
  · change consSub (pulledNewest morphism).code
      (subComp morphism.substitution projection) = morphism.substitution
    rw [pulledNewest_code]
    exact consSub_eta morphism.substitution
  · apply Function.hfunext rfl
    intro index other same
    cases same
    refine Fin.cases ?_ (fun prior => ?_) index
    · exact (pair_component_zero _ _).trans (pulledNewest_evidence morphism)
    · refine (pair_component_succ _ _ prior).trans ?_
      refine (TreeSubstitution.comp_component (projectionHom target type).components
        morphism.components prior).trans ?_
      refine (Tree.substitute_heq ?_ (projection_component target type prior)
        morphism.components morphism.components rfl (HEq.refl _) (HEq.refl _)).trans ?_
      · change judgment (.snoc target.raw type.code) (.var prior.succ)
          (subst projection (Ctx.lookup target.raw prior)) =
          judgment (.snoc target.raw type.code) (.var prior.succ)
            (Ctx.lookup (.snoc target.raw type.code) prior.succ)
        simp only [subst_projection, Ctx.lookup_snoc_succ]
      · exact heq_of_eq (Tree.substitute_variableLeaf morphism.components prior.succ)

/-- The newest-variable beta law identifies the entire supplied term tree. -/
theorem newest_pair {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ target) (term : Term source (type.reindex morphism)) :
    ((newest target type).reindex (pair morphism term)).cast
      (by rw [← type.reindex_comp, pair_projection]) = term := by
  apply Term.ext
  · rw [Term.cast_code]
    rfl
  · exact (Term.cast_evidence _ _).trans (newest_pair_evidence morphism term)

/-- Lifting a contextual substitution protects the newly bound variable and
weakens each actual supplied older component. The domain being extended may
itself depend on any earlier variables. -/
noncomputable def liftHom {source target : Context rules} (morphism : source ⟶ target)
    (type : TypeOver target) : extend source (type.reindex morphism) ⟶ extend target type :=
  ⟨liftSub morphism.substitution, morphism.components.lift type.code⟩

theorem lift_component_zero {source target : Context rules} (morphism : source ⟶ target)
    (type : TypeOver target) :
    HEq ((liftHom morphism type).components 0)
      (Tree.variableLeaf (R := rules) (extend source (type.reindex morphism)).raw
        (0 : Fin (source.arity + 1))) :=
  TreeSubstitution.lift_zero morphism.components type.code

theorem lift_component_succ {source target : Context rules} (morphism : source ⟶ target)
    (type : TypeOver target) (index : Fin target.arity) :
    HEq ((liftHom morphism type).components index.succ)
      (Tree.weaken (extension := (type.reindex morphism).code) (morphism.components index)) :=
  TreeSubstitution.lift_succ morphism.components type.code index

set_option backward.isDefEq.respectTransparency false in
/-- The direct lifted component action is precisely the structural
comprehension arrow assembled from projection and the newest term. -/
theorem lift_as_pair {source target : Context rules} (morphism : source ⟶ target)
    (type : TypeOver target) :
    liftHom morphism type =
      pair (projectionHom source (type.reindex morphism) ≫ morphism)
        ((newest source (type.reindex morphism)).cast
          (type.reindex_comp (projectionHom source (type.reindex morphism)) morphism).symm) := by
  apply Hom.ext
  · change liftSub morphism.substitution =
      consSub ((newest source (type.reindex morphism)).cast
        (type.reindex_comp (projectionHom source (type.reindex morphism)) morphism).symm).code
        (subComp projection morphism.substitution)
    rw [Term.cast_code]
    funext index
    refine Fin.cases rfl (fun prior => ?_) index
    exact (subst_projection (morphism.substitution prior)).symm
  · apply Function.hfunext rfl
    intro index other same
    cases same
    refine Fin.cases ?_ (fun prior => ?_) index
    · exact (lift_component_zero morphism type).trans
        ((newest_evidence source (type.reindex morphism)).symm.trans
          ((Term.cast_evidence _ _).symm.trans (pair_component_zero _ _).symm))
    · exact (lift_component_succ morphism type prior).trans
        ((projection_substitute (type.reindex morphism) (morphism.components prior)).symm.trans
          ((TreeSubstitution.comp_component morphism.components
            (projectionHom source (type.reindex morphism)).components prior).symm.trans
              (pair_component_succ
                (projectionHom source (type.reindex morphism) ≫ morphism)
                ((newest source (type.reindex morphism)).cast
                  (type.reindex_comp (projectionHom source (type.reindex morphism)) morphism).symm)
                prior).symm))

/-- The substitution lift gives the actual naturality square of dependent
context extension, with equality of all retained component trees. -/
theorem lift_projection {source target : Context rules} (morphism : source ⟶ target)
    (type : TypeOver target) :
    liftHom morphism type ≫ projectionHom target type =
      projectionHom source (type.reindex morphism) ≫ morphism := by
  rw [lift_as_pair]
  exact pair_projection _ _

structure Element (source target : Context rules) (type : TypeOver target) where
  base : source ⟶ target
  term : Term source (type.reindex base)

@[ext] theorem Element.ext {source target : Context rules} {type : TypeOver target}
    {first second : Element source target type} (bases : first.base = second.base)
    (codes : first.term.code = second.term.code)
    (evidence : HEq first.term.evidence second.term.evidence) : first = second := by
  cases first
  cases second
  cases bases
  cases Term.ext codes evidence
  rfl

noncomputable def toComprehension {source target : Context rules} {type : TypeOver target}
    (element : Element source target type) : source ⟶ extend target type :=
  pair element.base element.term

noncomputable def fromComprehension {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ extend target type) : Element source target type :=
  ⟨morphism ≫ projectionHom target type, pulledNewest morphism⟩

theorem from_to {source target : Context rules} {type : TypeOver target}
    (element : Element source target type) :
    fromComprehension (toComprehension element) = element := by
  apply Element.ext
  · exact pair_projection element.base element.term
  · exact pulledNewest_code (pair element.base element.term)
  · exact (pulledNewest_evidence (pair element.base element.term)).trans
      (pair_component_zero element.base element.term)

theorem to_from {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ extend target type) :
    toComprehension (fromComprehension morphism) = morphism := pair_eta morphism

/-- Both sides of representable comprehension retain the full component and
newest-term certificates, rather than only their erased raw codes. -/
noncomputable def comprehensionEquiv (source target : Context rules) (type : TypeOver target) :
    Element source target type ≃ (source ⟶ extend target type) where
  toFun := toComprehension
  invFun := fromComprehension
  left_inv := from_to
  right_inv := to_from

noncomputable def Element.precompose {first source target : Context rules} {type : TypeOver target}
    (element : Element source target type) (earlier : first ⟶ source) : Element first target type :=
  ⟨earlier ≫ element.base,
    (element.term.reindex earlier).cast (type.reindex_comp earlier element.base).symm⟩

set_option backward.isDefEq.respectTransparency false in
theorem comprehension_natural {first source target : Context rules} {type : TypeOver target}
    (element : Element source target type) (earlier : first ⟶ source) :
    earlier ≫ toComprehension element = toComprehension (element.precompose earlier) := by
  apply Hom.ext
  · change subComp earlier.substitution (consSub element.term.code element.base.substitution) =
      consSub (element.precompose earlier).term.code
        (subComp earlier.substitution element.base.substitution)
    rw [show (element.precompose earlier).term.code =
        subst earlier.substitution element.term.code from Term.cast_code _ _]
    exact subComp_consSub earlier.substitution element.term.code element.base.substitution
  · apply Function.hfunext rfl
    intro index other same
    cases same
    refine Fin.cases ?_ (fun prior => ?_) index
    · refine (TreeSubstitution.comp_component (pair element.base element.term).components
        earlier.components 0).trans ?_
      refine (Tree.substitute_heq ?_ (pair_component_zero element.base element.term)
        earlier.components earlier.components rfl (HEq.refl _) (HEq.refl _)).trans ?_
      · dsimp only [pair, TypeOver.reindex]
        simp only [consSub_zero, Ctx.lookup_snoc_zero, subst_consSub_rename_wk]
      · exact (Term.cast_evidence _ _).symm.trans
          (pair_component_zero (element.precompose earlier).base
            (element.precompose earlier).term).symm
    · refine (TreeSubstitution.comp_component (pair element.base element.term).components
        earlier.components prior.succ).trans ?_
      refine (Tree.substitute_heq ?_ (pair_component_succ element.base element.term prior)
        earlier.components earlier.components rfl (HEq.refl _) (HEq.refl _)).trans ?_
      · dsimp only [pair]
        simp only [consSub_succ, Ctx.lookup_snoc_succ, subst_consSub_rename_wk]
      · exact (TreeSubstitution.comp_component element.base.components earlier.components prior).symm.trans
          (pair_component_succ (element.precompose earlier).base
            (element.precompose earlier).term prior).symm

@[simp] theorem erase_projection (context : Context rules) (type : TypeOver context) :
    (projectionHom context type).erase =
      FormationSensitiveContextual.projectionHom context.erase type.erase :=
  FormationSensitiveContextual.Hom.ext rfl

@[simp] theorem erase_pair {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ target) (term : Term source (type.reindex morphism)) :
    (pair morphism term).erase =
      FormationSensitiveContextual.pair (type := type.erase) morphism.erase term.erase :=
  FormationSensitiveContextual.Hom.ext rfl

/-! ## The shared structural CwF and its erasure morphism -/

/-- The contextual structure keeps the exact supplied evidence in its type,
term and substitution carriers. The structural equations are obtained from
the direct all-tree action and the actual variable leaves. -/
noncomputable def cwf (rules : Rules Head) : Cwf where
  Ctx := Context rules
  Sub := fun source target => source ⟶ target
  idS := fun context => 𝟙 context
  compS := fun later earlier => earlier ≫ later
  id_comp := Category.comp_id
  comp_id := Category.id_comp
  comp_assoc := fun later middle earlier => (Category.assoc earlier middle later).symm
  Ty := TypeOver
  tySub := TypeOver.reindex
  tySub_id := TypeOver.reindex_id
  tySub_comp := fun type later earlier => type.reindex_comp earlier later
  Tm := Term
  tmSub := Term.reindex
  tmSub_id := by
    intro context type term
    apply Term.ext
    · rw [Term.castCongrArg_code type.reindex_id.symm]
      exact subst_ids term.code
    · exact (Tree.substitute_identity term.evidence).trans
        (Term.castCongrArg_evidence type.reindex_id.symm term).symm
  tmSub_comp := by
    intro source middle target type term later earlier
    apply Term.ext
    · rw [Term.castCongrArg_code (type.reindex_comp earlier later).symm]
      exact (subst_subComp earlier.substitution later.substitution term.code).symm
    · exact (Tree.substitute_composition term.evidence later.components earlier.components).symm.trans
        (Term.castCongrArg_evidence (type.reindex_comp earlier later).symm
          ((term.reindex later).reindex earlier)).symm
  ext := extend
  wk := fun type => projectionHom _ type
  vz := fun type => newest _ type
  pair := fun morphism _ term => pair morphism term
  wk_pair := fun morphism _ term => pair_projection morphism term
  vz_pair := by
    intro source target morphism type term
    have same : type.reindex morphism =
        (type.reindex (projectionHom target type)).reindex (pair morphism term) := by
      rw [← type.reindex_comp, pair_projection]
    apply Term.ext
    · rw [Term.castCongrArg_code same]
      rfl
    · exact (newest_pair_evidence morphism term).trans
        (Term.castCongrArg_evidence same term).symm
  pair_eta := by
    intro source target type morphism
    rw [← Term.cast_eq_castCongrArg (type.reindex_comp morphism (projectionHom target type)).symm]
    exact pair_eta morphism

noncomputable def withTerminal (rules : Rules Head) : CwfWithTerminal where
  toCwf := cwf rules
  empty := empty rules
  toEmpty := toEmpty
  toEmpty_unique := toEmpty_unique

noncomputable def eraseCwfBase (rules : Rules Head) :
    (cwf rules).base.Context ⥤ (FormationSensitiveContextual.asCwf rules).base.Context where
  obj context := ⟨context.val.erase⟩
  map morphism := morphism.erase
  map_id _ := FormationSensitiveContextual.Hom.ext rfl
  map_comp _ _ := FormationSensitiveContextual.Hom.ext rfl

/-- Erasure preserves joint type-and-term substitution naturally. Its fibre
maps discard histories only at this explicitly named comparison. -/
noncomputable def eraseFamily (rules : Rules Head) :
    CwfFamilyMorphism (cwf rules) (FormationSensitiveContextual.asCwf rules) where
  base := eraseCwfBase rules
  family := {
    app := fun _ => { onIndex := TypeOver.erase, onFibre := fun _ => Term.erase }
    naturality := by
      intro source target morphism
      apply IndexedFamily.Hom.ext
      · rfl
      · intro type term
        rfl }

/-- The erasure interpretation preserves the actual empty telescope,
extension, projection and newest variable on the nose. -/
noncomputable def eraseStrict (rules : Rules Head) :
    StrictCwfMorphism (withTerminal rules)
      (FormationSensitiveContextual.asCwfWithTerminal rules) where
  toFamilyMorphism := eraseFamily rules
  empty_preserved := rfl
  extension_preserved _ _ := rfl
  projection_preserved context type := by
    apply FormationSensitiveContextual.Hom.ext
    exact (subComp_ids_left projection).symm
  variable_preserved context type := by
    apply FormationSensitiveContextual.Term.heq_of_type_eq_of_code_eq
    · apply FormationSensitiveContextual.TypeOver.ext
      · exact (subst_ids _).symm
      · rfl
    · rfl

end FormationSensitiveRetainedContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
