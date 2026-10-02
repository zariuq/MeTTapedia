import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchJRelation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.HeadSteps
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.SchemaDeterminism

/-!
# The weak-head reduction of the object package's annotated terms

* **The annotated root steps are deterministic** (`objectChurch_root_deterministic`).
  The schemas of the object package are determined by their left sides
  (`objectSchemas_determinate`): every metavariable occurs in its left side, the
  left sides of the declared computations are pairwise apart
  (`specLeftSides_allApart`), each of them is apart from every decoding redex
  (`specLeftSides_apart_holds`), and two decoding redexes with a common instance
  have one left side.
* **The weak-head reduction** (`objectHeadReduction`): the annotated weak-head
  steps `CWhStepR objectChurch objectRoles`, with every field the witness-indexed
  relation reads: β, the projections, the root steps, the function position of an
  application, the scrutinees of the projections, the code argument of the decoder,
  determinism, and the canonical forms as normal forms. Determinism is the generic
  determinism of the steps under the object package's root shape.
* **Scrutinee congruences** of the computing constants that inspect an argument:
  the path of the identity eliminator (`objectHeadReduction_jPath`), the numeral of
  `num-rec` (`objectHeadReduction_numRec`), of addition, of the iterated power set
  and of the iterator (`objectHeadReduction_add`, `_pow`, `_iter`); the decoder's
  code is the reduction's `holdsArg`.
* **The eliminator's case of the fundamental lemma** at this reduction
  (`Adequate.objectJ_head`): the path congruence discharged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open AlgebraicSchema (SchemaFamily variableMultiplicity)
open Package (jName numRecName iterName)

namespace CodeModel

/-! ## The schemas are determined by their left sides -/

/-- The left sides of the object package's declared computations. -/
def specLeftSides : List (Σ k : Nat, Tm Tower.Head k) :=
  computationSpecs.flatMap fun p => p.2.leftSides

/-- The left sides of the declared computations are pairwise apart. -/
theorem specLeftSides_allApart : AllApart specLeftSides = true := by
  decide

/-- Every metavariable of a declared computation's schema occurs in its left side. -/
theorem computationSpecs_checkCovers : (computationSpecs.all fun p => p.2.checkCovers) = true := by
  decide

/-- The left sides of the declared computations are apart from the decoding redex
`holds x`. -/
theorem specLeftSides_apart_holds :
    (specLeftSides.all fun L => Apart L.2 (.app (.const holdsN) (.var 0) : Tm Tower.Head 1)) =
      true := by
  decide

theorem mem_specLeftSides {p : DeclName × DeclaredComputation Tower.Head}
    (mem : p ∈ computationSpecs) {k : Nat} {L R : Tm Tower.Head k} (rule : p.2.schemas L R) :
    (⟨k, L⟩ : Σ k : Nat, Tm Tower.Head k) ∈ specLeftSides :=
  List.mem_flatMap.2 ⟨p, mem, p.2.mem_leftSides rule⟩

/-- A decoding schema's left side is the decoder applied to a code. -/
theorem decoderSchema_left {D : Decoders Tower.Head} {k : Nat} {L R : Tm Tower.Head k}
    (rule : decoderSchema D L R) : ∃ X, L = .app (.const D.holds) X := by
  rcases rule with rule | ⟨a, A, _, rule⟩ | ⟨e, A, _, rule⟩ <;> cases rule
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- A spec left side has no common instance with a decoding redex. -/
theorem spec_decoder_apart {k₁ k₂ n : Nat} {L₁ R₁ : Tm Tower.Head k₁} {L₂ R₂ : Tm Tower.Head k₂}
    (rule₁ : schemaUnionAll (computationSpecs.map fun p => (p.1, p.2.schemas)) L₁ R₁)
    (rule₂ : decoderSchema programCodes.decoders L₂ R₂) (τ₁ : Sub Tower.Head k₁ n)
    (τ₂ : Sub Tower.Head k₂ n) : Presentation.subst τ₁ L₁ ≠ Presentation.subst τ₂ L₂ := by
  obtain ⟨p, mem, rule₁⟩ := DeclaredComputation.mem_of_schemaUnionAll rule₁
  obtain ⟨X, rfl⟩ := decoderSchema_left rule₂
  have hA : Apart L₁ (.app (.const holdsN) (.var 0) : Tm Tower.Head 1) = true :=
    List.all_eq_true.1 specLeftSides_apart_holds _ (mem_specLeftSides mem rule₁)
  have hA' := Apart.subst_right L₁ _ (fun _ => X) hA
  exact Apart.subst_ne L₁ _ hA' τ₁ τ₂

/-- Two decoding schemas whose left sides have a common instance have one left side. -/
theorem decoder_leftUnique {k₁ k₂ n : Nat} {L₁ R₁ : Tm Tower.Head k₁} {L₂ R₂ : Tm Tower.Head k₂}
    (rule₁ : decoderSchema programCodes.decoders L₁ R₁)
    (rule₂ : decoderSchema programCodes.decoders L₂ R₂) (τ₁ : Sub Tower.Head k₁ n)
    (τ₂ : Sub Tower.Head k₂ n) (e : Presentation.subst τ₁ L₁ = Presentation.subst τ₂ L₂) :
    (⟨k₁, L₁⟩ : Σ k : Nat, Tm Tower.Head k) = ⟨k₂, L₂⟩ := by
  have impNe : ∀ {e₀ : DeclName} {A : Tm Tower.Head 0},
      programCodes.decoders.eqCarrier e₀ = some A → decide (programCodes.decoders.imp = e₀) =
        false := by
    intro e₀ A carrier
    refine decide_eq_false fun h => ?_
    rw [← h, programCodes_impNotEquation] at carrier
    cases carrier
  rcases rule₁ with rule₁ | ⟨a₁, A₁, c₁, rule₁⟩ | ⟨e₁, A₁, c₁, rule₁⟩ <;> cases rule₁ <;>
    rcases rule₂ with rule₂ | ⟨a₂, A₂, c₂, rule₂⟩ | ⟨e₂, A₂, c₂, rule₂⟩ <;> cases rule₂
  · rfl
  · exact absurd e (Apart.subst_ne _ _ rfl τ₁ τ₂)
  · have h : Apart (.app (.const programCodes.decoders.holds)
        (.app (.app (.const programCodes.decoders.imp) (.var 1)) (.var 0)) : Tm Tower.Head 2)
        (.app (.const programCodes.decoders.holds) (.app (.app (.const e₂) (.var 1)) (.var 0)) :
          Tm Tower.Head 2) = !decide (programCodes.decoders.imp = e₂) := by
      show (!decide (programCodes.decoders.holds = programCodes.decoders.holds) ||
        ((!decide (programCodes.decoders.imp = e₂) || false) || false)) = _
      rw [decide_eq_true rfl, Bool.or_false, Bool.or_false]
      rfl
    rw [impNe c₂] at h
    exact absurd e (Apart.subst_ne _ _ h τ₁ τ₂)
  · exact absurd e (Apart.subst_ne _ _ rfl τ₁ τ₂)
  · cases hd : decide (a₁ = a₂) with
    | true =>
        obtain rfl := of_decide_eq_true hd
        rfl
    | false =>
        have h : Apart (.app (.const programCodes.decoders.holds) (.app (.const a₁) (.var 0)) :
            Tm Tower.Head 1) (.app (.const programCodes.decoders.holds) (.app (.const a₂) (.var 0)) :
            Tm Tower.Head 1) = !decide (a₁ = a₂) := by
          show (!decide (programCodes.decoders.holds = programCodes.decoders.holds) ||
            (!decide (a₁ = a₂) || false)) = _
          rw [decide_eq_true rfl, Bool.or_false]
          rfl
        rw [hd] at h
        exact absurd e (Apart.subst_ne _ _ h τ₁ τ₂)
  · exact absurd e (Apart.subst_ne _ _ rfl τ₁ τ₂)
  · have h : Apart (.app (.const programCodes.decoders.holds)
        (.app (.app (.const e₁) (.var 1)) (.var 0)) : Tm Tower.Head 2)
        (.app (.const programCodes.decoders.holds)
          (.app (.app (.const programCodes.decoders.imp) (.var 1)) (.var 0)) : Tm Tower.Head 2) =
        !decide (e₁ = programCodes.decoders.imp) := by
      show (!decide (programCodes.decoders.holds = programCodes.decoders.holds) ||
        ((!decide (e₁ = programCodes.decoders.imp) || false) || false)) = _
      rw [decide_eq_true rfl, Bool.or_false, Bool.or_false]
      rfl
    have hne : decide (e₁ = programCodes.decoders.imp) = false :=
      decide_eq_false fun h' => of_decide_eq_false (impNe c₁) h'.symm
    rw [hne] at h
    exact absurd e (Apart.subst_ne _ _ h τ₁ τ₂)
  · exact absurd e (Apart.subst_ne _ _ rfl τ₁ τ₂)
  · cases hd : decide (e₁ = e₂) with
    | true =>
        obtain rfl := of_decide_eq_true hd
        rfl
    | false =>
        have h : Apart (.app (.const programCodes.decoders.holds)
            (.app (.app (.const e₁) (.var 1)) (.var 0)) : Tm Tower.Head 2)
            (.app (.const programCodes.decoders.holds)
              (.app (.app (.const e₂) (.var 1)) (.var 0)) : Tm Tower.Head 2) =
              !decide (e₁ = e₂) := by
          show (!decide (programCodes.decoders.holds = programCodes.decoders.holds) ||
            ((!decide (e₁ = e₂) || false) || false)) = _
          rw [decide_eq_true rfl, Bool.or_false, Bool.or_false]
          rfl
        rw [hd] at h
        exact absurd e (Apart.subst_ne _ _ h τ₁ τ₂)

/-- **The schemas of the object package are determined by their left sides.** -/
theorem objectSchemas_determinate : SchemaDeterminate objectSchemas where
  covers := by
    intro k L R rule
    rcases rule with rule | rule
    · obtain ⟨p, mem, rule⟩ := DeclaredComputation.mem_of_schemaUnionAll rule
      exact p.2.covers_of_checkCovers (List.all_eq_true.1 computationSpecs_checkCovers p mem) rule
    · rcases rule with rule | ⟨a, A, _, rule⟩ | ⟨e, A, _, rule⟩ <;> cases rule
      · exact coversAll_spec rfl
      · exact coversAll_spec rfl
      · exact coversAll_spec rfl
  leftUnique := by
    intro k₁ k₂ n L₁ R₁ L₂ R₂ rule₁ rule₂ τ₁ τ₂ e
    rcases rule₁ with rule₁ | rule₁ <;> rcases rule₂ with rule₂ | rule₂
    · obtain ⟨p₁, mem₁, r₁⟩ := DeclaredComputation.mem_of_schemaUnionAll rule₁
      obtain ⟨p₂, mem₂, r₂⟩ := DeclaredComputation.mem_of_schemaUnionAll rule₂
      rcases AllApart.eq_or_apart specLeftSides_allApart (mem_specLeftSides mem₁ r₁)
          (mem_specLeftSides mem₂ r₂) with h | h | h
      · exact h
      · exact absurd e (Apart.subst_ne _ _ h τ₁ τ₂)
      · exact absurd e.symm (Apart.subst_ne _ _ h τ₂ τ₁)
    · exact absurd e (spec_decoder_apart rule₁ rule₂ τ₁ τ₂)
    · exact absurd e.symm (spec_decoder_apart rule₂ rule₁ τ₂ τ₁)
    · exact decoder_leftUnique rule₁ rule₂ τ₁ τ₂ e

/-- **The annotated root steps of the object package are deterministic.** -/
theorem objectChurch_root_deterministic {n : Nat} {t u u' : CTm Tower.Head n}
    (first : objectChurch.computation.step t u) (second : objectChurch.computation.step t u') :
    u = u' :=
  ChurchRules.ofSchemas_deterministic objectSchemas objectRules_presents objectSchemas_firstOrder
    objectSchemas_determinate objectShape.deterministic first second

/-! ## The weak-head reduction -/

theorem objectRoles_propRigid : objectRoles propN = .rigid :=
  (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans
    (roles_of_not_mem (by decide))

theorem objectRoles_setRigid : objectRoles setN = .rigid :=
  (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_set

/-- A rigid constant takes no weak-head step. -/
theorem rigid_whnf {n : Nat} {c : DeclName} (role : objectRoles c = .rigid) :
    Whnf objectRules objectRoles (.const c : Tower.Tm n) :=
  constSpine_whnf objectShape (args := []) fun _ _ h => nomatch role.symm.trans h

/-- **The weak-head reduction of the object package's annotated terms**, with the
fields the witness-indexed relation reads. -/
def objectHeadReduction : HeadReduction objectChurch objectRigid where
  step := CWhStepR objectChurch objectRoles
  beta := .beta
  appFun := fun _ s => .appFun s
  root := .root
  holdsArg := fun s => CWhStepR.scrutinee (before := []) (after := []) objectRoles_holds rfl s
  deterministic := fun s s' =>
    (CWhStepR.deterministic objectShape objectChurch_root_deterministic s s').symm
  head_normal := fun h u => CWhStepR.not_of_whnf (head_whnf objectShape h) u
  pi_normal := fun A B u => CWhStepR.not_of_whnf (pi_whnf objectShape A.erase B.erase) u
  id_normal := fun A a b u => CWhStepR.not_of_whnf (id_whnf objectShape A.erase a.erase b.erase) u
  refl_normal := fun a u => CWhStepR.not_of_whnf (refl_whnf objectShape a.erase) u
  prop_normal := fun u => CWhStepR.not_of_whnf (rigid_whnf objectRoles_propRigid) u
  num_normal := fun u => CWhStepR.not_of_whnf (inductive_whnf objectShape objectRoles_num) u
  zero_normal := fun u => CWhStepR.not_of_whnf
    (canonical_whnf objectShape (.inr ⟨zeroN, 0, [], objectRoles_zero, rfl⟩)) u
  suc_normal := fun m u => CWhStepR.not_of_whnf
    (canonical_whnf objectShape (.inr ⟨sucN, 1, [m.erase], objectRoles_suc, rfl⟩)) u
  fstPair := .fstPair
  sndPair := .sndPair
  fst := .fst
  snd := .snd
  sigma_normal := fun A B u => CWhStepR.not_of_whnf (sigma_whnf objectShape A.erase B.erase) u
  ground_normal := fun u hg => by
    rcases hg with rfl | rfl
    · exact CWhStepR.not_of_whnf (rigid_whnf objectRoles_setRigid) u
    · exact CWhStepR.not_of_whnf (head_whnf objectShape _) u

theorem objectHeadReduction_step {n : Nat} {t u : CTm Tower.Head n} :
    objectHeadReduction.step t u ↔ CWhStepR objectChurch objectRoles t u :=
  Iff.rfl

/-! ## Scrutinee congruences -/

section Scrutinees

variable {n : Nat}

/-- **The path of the identity eliminator**: `J A x M d y q ⟶ J A x M d y q'` when
`q ⟶ q'`. -/
theorem objectHeadReduction_jPath {A x M d y q q' : CTm Tower.Head n}
    (s : objectHeadReduction.step q q') :
    objectHeadReduction.step (.app (CTm.appSpine (.const jName) [A, x, M, d, y]) q)
      (.app (CTm.appSpine (.const jName) [A, x, M, d, y]) q') := by
  have h := CWhStepR.scrutinee (before := [A, x, M, d, y]) (after := [])
    (objectRoles_of_roles roles_j nofun) rfl s
  rw [CTm.appSpine_concat, CTm.appSpine_concat] at h
  exact h

/-- **The numeral of `num-rec`**: `num-rec P z s q ⟶ num-rec P z s q'`. -/
theorem objectHeadReduction_numRec {P z s q q' : CTm Tower.Head n}
    (step : objectHeadReduction.step q q') :
    objectHeadReduction.step (.app (CTm.appSpine (.const numRecName) [P, z, s]) q)
      (.app (CTm.appSpine (.const numRecName) [P, z, s]) q') := by
  have h := CWhStepR.scrutinee (before := [P, z, s]) (after := [])
    (objectRoles_of_roles roles_numRec nofun) rfl step
  rw [CTm.appSpine_concat, CTm.appSpine_concat] at h
  exact h

/-- **The numeral of addition**, its second argument: `add m q ⟶ add m q'`. -/
theorem objectHeadReduction_add {m q q' : CTm Tower.Head n}
    (step : objectHeadReduction.step q q') :
    objectHeadReduction.step (.app (.app (.const addN) m) q) (.app (.app (.const addN) m) q') :=
  CWhStepR.scrutinee (before := [m]) (after := []) objectRoles_add rfl step

/-- **The numeral of the iterated power set**, its first argument:
`pow q X ⟶ pow q' X`. -/
theorem objectHeadReduction_pow {q q' X : CTm Tower.Head n}
    (step : objectHeadReduction.step q q') :
    objectHeadReduction.step (.app (.app (.const powN) q) X) (.app (.app (.const powN) q') X) :=
  CWhStepR.scrutinee (before := []) (after := [X]) objectRoles_pow rfl step

/-- **The numeral of the iterator**, its first argument. -/
theorem objectHeadReduction_iter {q q' A P st x h : CTm Tower.Head n}
    (step : objectHeadReduction.step q q') :
    objectHeadReduction.step (CTm.appSpine (.const iterName) [q, A, P, st, x, h])
      (CTm.appSpine (.const iterName) [q', A, P, st, x, h]) :=
  CWhStepR.scrutinee (before := []) (after := [A, P, st, x, h])
    (objectRoles_of_roles roles_iter nofun) rfl step

/-- **The code of the decoder**: `holds c ⟶ holds c'`. -/
theorem objectHeadReduction_holds {c c' : CTm Tower.Head n}
    (step : objectHeadReduction.step c c') :
    objectHeadReduction.step (.app (.const holdsN) c) (.app (.const holdsN) c') :=
  objectHeadReduction.holdsArg step

end Scrutinees

/-! ## The eliminator's case of the fundamental lemma -/

/-- **The eliminator's case of the fundamental lemma at the object package's
weak-head reduction**: for an adequate carrier, motive, method and path, the
eliminator's spine `J A x M d y p` is adequate at `M y p`. -/
theorem Adequate.objectJ_head {L : Type} [LevelOrder L] (levels : LevelModel objectRules L)
    {n : Nat} {Γ : CCtx Tower.Head n} {A x M d y p : CTm Tower.Head n}
    (J : JCase objectHeadReduction Γ A x M d y p) :
    Adequate objectChurchReading objectHeadReduction Γ
      (CTm.appSpine (.const jName) [A, x, M, d, y, p]) (.app (.app M y) p) :=
  Adequate.objectJ levels (fun s => objectHeadReduction_jPath s) J

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
