import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Represents

/-!
# How each rule transforms the readings of an alternative

For each rule and each alternative of the shape the rule's take pattern describes, the readings of
the rule's made row, over the instantiations of the rule's unknowns that send its take pattern to a
reading of the alternative, are the readings of the alternative the source's move makes
(`transfer_ret`, `transfer_unmatched`, `transfer_choiceLeft`, `transfer_choiceRight`,
`transfer_schema`). These are the only rule-specific facts the correspondence needs.

The schema's transfer is where two-way unification is compared: a reading of the call by the store
and an instance of the equation's left side that agrees with it combine, by `graft`, into a solution
of the store extended with the source's copy of the equation (`solvable_copy_iff`).

The shape lemmas (`shape_*`) read the alternative back from one reading: if a rule's take pattern
reads as a reading of an alternative, the alternative has the rule's shape.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S} {Ty : Type}

/-! ## Instantiating named nodes -/

section NodeLemmas

variable {V W : Type} {D : V → MetaArity S} {E : W → MetaArity S} (σ : Assignment D E)

theorem instantiate_altN (x y : Term (signature S D) Γ star) :
    instantiate σ (altN N x y) = altN N (instantiate σ x) (instantiate σ y) := by
  show instantiate σ (N.node .alt ![x, y]) = _
  rw [N.instantiate_node]; exact congrArg _ (map_vec2 _ _ _)

theorem instantiate_evalN (x : Term (signature S D) Γ star) :
    instantiate σ (evalN N x) = evalN N (instantiate σ x) := by
  show instantiate σ (N.node .eval ![x]) = _
  rw [N.instantiate_node]; exact congrArg _ (map_vec1 _ _)

theorem instantiate_valueN (x : Term (signature S D) Γ star) :
    instantiate σ (valueN N x) = valueN N (instantiate σ x) := by
  show instantiate σ (N.node .value ![x]) = _
  rw [N.instantiate_node]; exact congrArg _ (map_vec1 _ _)

theorem instantiate_retN (x : Term (signature S D) Γ star) :
    instantiate σ (retN N x) = retN N (instantiate σ x) := by
  show instantiate σ (N.node .ret ![x]) = _
  rw [N.instantiate_node]; exact congrArg _ (map_vec1 _ _)

theorem instantiate_applyN (x : Term (signature S D) Γ star) :
    instantiate σ (applyN N x) = applyN N (instantiate σ x) := by
  show instantiate σ (N.node .apply ![x]) = _
  rw [N.instantiate_node]; exact congrArg _ (map_vec1 _ _)

theorem instantiate_choiceN (x y : Term (signature S D) Γ star) :
    instantiate σ (choiceN N x y) = choiceN N (instantiate σ x) (instantiate σ y) := by
  show instantiate σ (N.node .choice ![x, y]) = _
  rw [N.instantiate_node]; exact congrArg _ (map_vec2 _ _ _)

theorem instantiate_bindN (x y z : Term (signature S D) Γ star) :
    instantiate σ (bindN N x y z) = bindN N (instantiate σ x) (instantiate σ y) (instantiate σ z) := by
  show instantiate σ (N.node .bind ![x, y, z]) = _
  rw [N.instantiate_node]; exact congrArg _ (map_vec3 _ _ _ _)

theorem instantiate_pushN (x y z : Term (signature S D) Γ star) :
    instantiate σ (pushN N x y z) = pushN N (instantiate σ x) (instantiate σ y) (instantiate σ z) := by
  show instantiate σ (N.node .push ![x, y, z]) = _
  rw [N.instantiate_node]; exact congrArg _ (map_vec3 _ _ _ _)

end NodeLemmas

/-! ## Readings through an observation -/

theorem branchReads_observe {b : Branch κ Γ star Ty} {B : Interface.Frames.Frame S}
    {x : Term (signature S B.arity) Γ star} :
    branchReads N b B (observe x) ↔ ∃ σ : Assignment (fam κ) B.arity, Models σ b.store ∧
      encBranch N (instantiate σ) b = x := by
  constructor
  · rintro ⟨σ, solved, same⟩
    exact ⟨σ, solved, observe_injective same⟩
  · rintro ⟨σ, solved, rfl⟩
    exact ⟨σ, solved, rfl⟩

/-- Fill a control rule's unknowns. -/
def fill {B : Interface.Frames.Frame S} (d p c e st : Term (signature S B.arity) Γ star) :
    Assignment (unknownArity Γ star) B.arity
  | .datum => d
  | .pattern => p
  | .first => c
  | .second => e
  | .stack => st

theorem instantiate_unk {B : Interface.Frames.Frame S} (h : Assignment (unknownArity Γ star) B.arity)
    (x : Unknown) : instantiate h (unk x) = h x :=
  instantiate_generator h x

theorem models_nil_tells {F B : Interface.Frames.Frame S} (h : Assignment F.arity B.arity) :
    (Interface.Frames.contextual S).Models h [] :=
  fun _ member => by cases member

/-! ## The control rules -/

section Control

variable {b : Branch κ Γ star Ty} {B : Interface.Frames.Frame S}

/-- `ret` returns its datum. -/
theorem transfer_ret {t : Data κ Γ star} (focus : b.focus = .eval (.ret t)) (q : Observation S B.arity) :
    (∃ h : Assignment (unknownArity Γ star) B.arity,
      branchReads N b B (instantiateObservation h (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack)))) ∧
      (Interface.Frames.contextual S).Models (a := controlFrame Γ star) (b := B) h [] ∧
      instantiateObservation h (observe (altN N (valueN N (unk .datum)) (unk .stack))) = q) ↔
      branchReads N ⟨b.store, .value t, b.frames, b.pending⟩ B q := by
  constructor
  · rintro ⟨h, reads, _, rfl⟩
    change branchReads N b B (observe (instantiate h _)) at reads
    rw [instantiate_altN, instantiate_evalN, instantiate_retN, instantiate_unk, instantiate_unk] at reads
    obtain ⟨σ, solved, same⟩ := (branchReads_observe N).mp reads
    rw [encBranch, encAlt, focus] at same
    obtain ⟨onFocus, onStack⟩ := vec2_inj (N.args_eq same)
    have onDatum := vec1_inj (N.args_eq (vec1_inj (N.args_eq onFocus)))
    refine ⟨σ, solved, ?_⟩
    change observe _ = observe (instantiate h _)
    rw [instantiate_altN, instantiate_valueN, instantiate_unk, instantiate_unk]
    exact congrArg observe (congrArg₂ (altN N) (congrArg (valueN N) onDatum) onStack)
  · rintro ⟨σ, solved, rfl⟩
    refine ⟨fill (instantiate σ t) (instantiate σ t) (instantiate σ t) (instantiate σ t)
      (encStack N (instantiate σ) b.frames), ?_, models_nil_tells _, ?_⟩
    · refine ⟨σ, solved, ?_⟩
      change observe _ = observe (instantiate _ _)
      rw [instantiate_altN, instantiate_evalN, instantiate_retN, instantiate_unk, instantiate_unk]
      simp only [encBranch, encAlt, focus, encFocus, encComp, fill]
    · change observe (instantiate _ _) = _
      rw [instantiate_altN, instantiate_valueN, instantiate_unk, instantiate_unk]
      rfl

/-- An unmatched call returns the call. -/
theorem transfer_unmatched {t : Data κ Γ star} (focus : b.focus = .eval (.apply t))
    (q : Observation S B.arity) :
    (∃ h : Assignment (unknownArity Γ star) B.arity,
      branchReads N b B (instantiateObservation h (observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack)))) ∧
      (Interface.Frames.contextual S).Models (a := controlFrame Γ star) (b := B) h [] ∧
      instantiateObservation h (observe (altN N (valueN N (unk .datum)) (unk .stack))) = q) ↔
      branchReads N ⟨b.store, .value t, b.frames, b.pending⟩ B q := by
  constructor
  · rintro ⟨h, reads, _, rfl⟩
    change branchReads N b B (observe (instantiate h _)) at reads
    rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_unk, instantiate_unk] at reads
    obtain ⟨σ, solved, same⟩ := (branchReads_observe N).mp reads
    rw [encBranch, encAlt, focus] at same
    obtain ⟨onFocus, onStack⟩ := vec2_inj (N.args_eq same)
    have onDatum := vec1_inj (N.args_eq (vec1_inj (N.args_eq onFocus)))
    refine ⟨σ, solved, ?_⟩
    change observe _ = observe (instantiate h _)
    rw [instantiate_altN, instantiate_valueN, instantiate_unk, instantiate_unk]
    exact congrArg observe (congrArg₂ (altN N) (congrArg (valueN N) onDatum) onStack)
  · rintro ⟨σ, solved, rfl⟩
    refine ⟨fill (instantiate σ t) (instantiate σ t) (instantiate σ t) (instantiate σ t)
      (encStack N (instantiate σ) b.frames), ?_, models_nil_tells _, ?_⟩
    · refine ⟨σ, solved, ?_⟩
      change observe _ = observe (instantiate _ _)
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_unk, instantiate_unk]
      simp only [encBranch, encAlt, focus, encFocus, encComp, fill]
    · change observe (instantiate _ _) = _
      rw [instantiate_altN, instantiate_valueN, instantiate_unk, instantiate_unk]
      rfl

/-- The left alternative of a choice. -/
theorem transfer_choiceLeft {c d : Comp κ Γ star Ty} (focus : b.focus = .eval (.choice c d))
    (q : Observation S B.arity) :
    (∃ h : Assignment (unknownArity Γ star) B.arity,
      branchReads N b B (instantiateObservation h
        (observe (altN N (evalN N (choiceN N (unk .first) (unk .second))) (unk .stack)))) ∧
      (Interface.Frames.contextual S).Models (a := controlFrame Γ star) (b := B) h [] ∧
      instantiateObservation h (observe (altN N (evalN N (unk .first)) (unk .stack))) = q) ↔
      branchReads N ⟨b.store, .eval c, b.frames, b.pending⟩ B q := by
  constructor
  · rintro ⟨h, reads, _, rfl⟩
    change branchReads N b B (observe (instantiate h _)) at reads
    rw [instantiate_altN, instantiate_evalN, instantiate_choiceN, instantiate_unk, instantiate_unk,
      instantiate_unk] at reads
    obtain ⟨σ, solved, same⟩ := (branchReads_observe N).mp reads
    rw [encBranch, encAlt, focus] at same
    obtain ⟨onFocus, onStack⟩ := vec2_inj (N.args_eq same)
    obtain ⟨onFirst, _⟩ := vec2_inj (N.args_eq (vec1_inj (N.args_eq onFocus)))
    refine ⟨σ, solved, ?_⟩
    change observe _ = observe (instantiate h _)
    rw [instantiate_altN, instantiate_evalN, instantiate_unk, instantiate_unk]
    exact congrArg observe (congrArg₂ (altN N) (congrArg (evalN N) onFirst) onStack)
  · rintro ⟨σ, solved, rfl⟩
    refine ⟨fill (encComp N (instantiate σ) c) (encComp N (instantiate σ) c) (encComp N (instantiate σ) c)
      (encComp N (instantiate σ) d) (encStack N (instantiate σ) b.frames), ?_, models_nil_tells _, ?_⟩
    · refine ⟨σ, solved, ?_⟩
      change observe _ = observe (instantiate _ _)
      rw [instantiate_altN, instantiate_evalN, instantiate_choiceN, instantiate_unk, instantiate_unk,
        instantiate_unk]
      simp only [encBranch, encAlt, focus, encFocus, encComp, fill]
    · change observe (instantiate _ _) = _
      rw [instantiate_altN, instantiate_evalN, instantiate_unk, instantiate_unk]
      rfl

/-- The right alternative of a choice. -/
theorem transfer_choiceRight {c d : Comp κ Γ star Ty} (focus : b.focus = .eval (.choice c d))
    (q : Observation S B.arity) :
    (∃ h : Assignment (unknownArity Γ star) B.arity,
      branchReads N b B (instantiateObservation h
        (observe (altN N (evalN N (choiceN N (unk .first) (unk .second))) (unk .stack)))) ∧
      (Interface.Frames.contextual S).Models (a := controlFrame Γ star) (b := B) h [] ∧
      instantiateObservation h (observe (altN N (evalN N (unk .second)) (unk .stack))) = q) ↔
      branchReads N ⟨b.store, .eval d, b.frames, b.pending⟩ B q := by
  constructor
  · rintro ⟨h, reads, _, rfl⟩
    change branchReads N b B (observe (instantiate h _)) at reads
    rw [instantiate_altN, instantiate_evalN, instantiate_choiceN, instantiate_unk, instantiate_unk,
      instantiate_unk] at reads
    obtain ⟨σ, solved, same⟩ := (branchReads_observe N).mp reads
    rw [encBranch, encAlt, focus] at same
    obtain ⟨onFocus, onStack⟩ := vec2_inj (N.args_eq same)
    obtain ⟨_, onSecond⟩ := vec2_inj (N.args_eq (vec1_inj (N.args_eq onFocus)))
    refine ⟨σ, solved, ?_⟩
    change observe _ = observe (instantiate h _)
    rw [instantiate_altN, instantiate_evalN, instantiate_unk, instantiate_unk]
    exact congrArg observe (congrArg₂ (altN N) (congrArg (evalN N) onSecond) onStack)
  · rintro ⟨σ, solved, rfl⟩
    refine ⟨fill (encComp N (instantiate σ) c) (encComp N (instantiate σ) c) (encComp N (instantiate σ) c)
      (encComp N (instantiate σ) d) (encStack N (instantiate σ) b.frames), ?_, models_nil_tells _, ?_⟩
    · refine ⟨σ, solved, ?_⟩
      change observe _ = observe (instantiate _ _)
      rw [instantiate_altN, instantiate_evalN, instantiate_choiceN, instantiate_unk, instantiate_unk,
        instantiate_unk]
      simp only [encBranch, encAlt, focus, encFocus, encComp, fill]
    · change observe (instantiate _ _) = _
      rw [instantiate_altN, instantiate_evalN, instantiate_unk, instantiate_unk]
      rfl

end Control

/-! ## The schema of an equation -/

section SchemaTransfer

variable {b : Branch κ Γ star Ty} {B : Interface.Frames.Frame S}

/-- Fill a schema's unknowns: the source's names by `θ`, the stack by `st`. -/
def schemaFill (θ : Assignment (fam κ) B.arity) (st : Term (signature S B.arity) Γ star) :
    Assignment (schemaArity Γ star κ) B.arity
  | .inl x => θ x
  | .inr () => st

theorem instantiate_asUnknowns (h : Assignment (schemaArity Γ star κ) B.arity) {Δ : Ctx S} {sort : S.Srt}
    (x : Term (signature S (fam κ)) Δ sort) :
    instantiate h (instantiate asUnknowns x) = instantiate (fun y => h (.inl y)) x := by
  rw [instantiate_comp]
  apply congrArg (fun ρ => instantiate ρ x)
  funext y
  exact instantiate_generator h (.inl y)

theorem instantiate_schemaStack (h : Assignment (schemaArity Γ star κ) B.arity) :
    instantiate h (schemaStack (Γ := Γ) (star := star) (κ := κ)) = h (.inr ()) :=
  instantiate_generator h (.inr ())

theorem instantiate_encComp_asUnknowns (h : Assignment (schemaArity Γ star κ) B.arity)
    (c : Comp κ Γ star Ty) :
    instantiate h (encComp N (instantiate asUnknowns) c) = encComp N (instantiate (fun y => h (.inl y))) c := by
  rw [instantiate_encComp]
  apply encComp_congr
  intro t _
  exact instantiate_asUnknowns h t

/-- **An equation used at a call**: the readings of the schema's made row, over the instantiations
whose left side agrees with a reading of the call, are the readings of the alternative that the
source makes from a copy of the equation at a fresh scope. -/
theorem transfer_schema {n : ℕ} {t : Data κ Γ star} (e : SourceLanguage.Equation κ Γ star Ty)
    (focus : b.focus = .eval (.apply t)) (fresh : BranchBelow n b) (q : Observation S B.arity) :
    (∃ h : Assignment (schemaArity Γ star κ) B.arity,
      branchReads N b B (instantiateObservation h
        (observe (altN N (evalN N (applyN N (instantiate asUnknowns e.lhs))) schemaStack))) ∧
      (Interface.Frames.contextual S).Models (a := schemaFrame Γ star κ) (b := B) h [] ∧
      instantiateObservation h (observe (altN N (evalN N (encComp N (instantiate asUnknowns) e.rhs))
        schemaStack)) = q) ↔
      branchReads N ⟨b.store ++ [(instantiate (copyAt κ n) e.lhs, t)], .eval (e.rhs.inst (copyAt κ n)),
        b.frames, b.pending⟩ B q := by
  have callBelow : DependsBelow n t := fresh.2.1 t (by rw [focus]; simp [focusData, Comp.data])
  have stackBelow : ∀ {W : Type} {target : W → MetaArity S} (σ θ : Assignment (fam κ) target),
      encStack N (instantiate (graft n σ θ)) b.frames = encStack N (instantiate σ) b.frames := by
    intro W target σ θ
    apply encStack_congr
    intro fr member t' inside
    exact instantiate_graft_below σ θ (fresh.2.2 fr member t' inside)
  constructor
  · rintro ⟨h, reads, _, rfl⟩
    change branchReads N b B (observe (instantiate h _)) at reads
    rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_asUnknowns,
      instantiate_schemaStack] at reads
    obtain ⟨σ, solved, same⟩ := (branchReads_observe N).mp reads
    rw [encBranch, encAlt, focus] at same
    obtain ⟨onFocus, onStack⟩ := vec2_inj (N.args_eq same)
    have onCall := vec1_inj (N.args_eq (vec1_inj (N.args_eq onFocus)))
    -- `onCall : instantiate σ t = instantiate (h ∘ inl) e.lhs`, `onStack : encStack σ = h (inr ())`
    refine ⟨graft n σ (fun y => h (.inl y)), (models_append _ _ _).mpr
      ⟨(models_graft _ _ fresh.1).mpr solved, ?_⟩, ?_⟩
    · apply (models_singleton _ _).mpr
      rw [graft_copy, instantiate_graft_below _ _ callBelow]
      exact onCall.symm
    · change observe _ = observe (instantiate h _)
      rw [instantiate_altN, instantiate_evalN, instantiate_encComp_asUnknowns, instantiate_schemaStack]
      apply congrArg observe
      have maps : (fun t' : Data κ Γ star =>
          instantiate (graft n σ (fun y => h (.inl y))) (instantiate (copyAt κ n) t')) =
          fun t' : Data κ Γ star => instantiate (fun y => h (.inl y)) t' :=
        funext fun t' => graft_copy n σ _ t'
      simp only [encBranch, encAlt, encFocus]
      rw [encComp_mapData, stackBelow, onStack, maps]
  · rintro ⟨σ', solved', rfl⟩
    obtain ⟨old, new⟩ := (models_append σ' _ _).mp solved'
    have matched := (models_singleton σ' _).mp new
    refine ⟨schemaFill (fun y => instantiate σ' (copyAt κ n y)) (encStack N (instantiate σ') b.frames),
      ?_, models_nil_tells _, ?_⟩
    · refine ⟨σ', old, ?_⟩
      change observe _ = observe (instantiate _ _)
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_asUnknowns,
        instantiate_schemaStack]
      simp only [encBranch, encAlt, focus, encFocus, encComp, schemaFill]
      rw [← instantiate_copy, matched]
    · change observe (instantiate _ _) = _
      rw [instantiate_altN, instantiate_evalN, instantiate_encComp_asUnknowns, instantiate_schemaStack]
      apply congrArg observe
      have maps : (fun t' : Data κ Γ star => instantiate σ' (instantiate (copyAt κ n) t')) =
          fun t' : Data κ Γ star => instantiate (fun y => instantiate σ' (copyAt κ n y)) t' :=
        funext fun t' => instantiate_copy σ' t'
      simp only [encBranch, encAlt, encFocus, schemaFill]
      rw [encComp_mapData, maps]
      rfl

end SchemaTransfer

#print axioms transfer_ret
#print axioms transfer_unmatched
#print axioms transfer_choiceLeft
#print axioms transfer_choiceRight
#print axioms transfer_schema

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
