import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchJRelation
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
* **The object package is an extension of itself** (`objectExtension`): its reading, roles,
  root shape, determinism and its one declared datatype, the numbers, which its roles make the
  inductive type with constructors `zero` and `suc` and its reading reads with the tag of
  numbers.
* **The weak-head reduction** (`objectHeadReduction`): the reduction of that extension, the
  annotated weak-head steps `CWhStepR objectChurch objectRoles`, with every field the
  witness-indexed relation reads: β, the projections, the root steps, the function position
  of an application, the scrutinees of the projections, the code argument of the decoder,
  determinism, and the canonical forms as normal forms. The scrutinee congruences of the
  computing constants are those of every extension (`ObjectExtension.head_numRec`, ...).

Positive example: `num-rec P z s 0` takes the zero rule's root step. Negative example: a
constructor applied to its fields takes no step (`HeadReduction.ctor_normal`).
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

/-! ## The object package as an extension of itself -/

/-- **Head equality is trivial on the heads that are not universes** at the object
package: the legacy ground head is equal only to itself. -/
theorem objectRules_groundHeadEq : GroundHeadEq objectRules := by
  intro h h' same
  cases h <;> cases h'
  · exact .inr rfl
  · exact same.elim
  · exact same.elim
  · exact .inl (.sort _)

/-- **The object package is an extension of itself**: its reading, its roles, its root shape
and determinism, and its one declared datatype, the numbers, read with the tag of numbers. -/
def objectExtension : ObjectExtension where
  rules := objectRules
  church := objectChurch
  sub := ChurchRulesSub.refl _
  within := objectChurch_within rfl
  levels := ConvRules.objectLevels
  headTyping := id
  groundHeadEq := objectRules_groundHeadEq
  reading := objectChurchReading
  valid := objectChurchReading_valid
  reading_head := rfl
  reading_const := fun _ => rfl
  roles := objectRoles
  roles_object := fun _ => rfl
  shape := objectShape
  deterministic := objectChurch_root_deterministic
  data := objectData
  params := objectParams
  ctor := objectCtor
  ctor_data := fun h => h.1
  zero_ctor := ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  suc_ctor := ⟨rfl, .inr ⟨rfl, rfl⟩⟩
  data_role := fun {d} hd => by
    obtain rfl : d = numN := hd
    exact ⟨ctors, objectRoles_num⟩
  ctor_role := fun hc => by
    rcases hc with ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact objectRoles_zero
    · exact objectRoles_suc
  inductivesRead := fun role => by
    obtain ⟨rfl, -⟩ := objectRoles_inductive role
    refine .inl ⟨rfl, ?_⟩
    rw [objectChurchReading_num]
    exact Ideal.mem_principal_tag.2 rfl

/-! ## The weak-head reduction -/

/-- **The weak-head reduction of the object package's annotated terms**: the weak-head
reduction of the object package as an extension of itself, the annotated weak-head steps
`CWhStepR objectChurch objectRoles`. -/
def objectHeadReduction : HeadReduction objectChurch objectRigid :=
  objectExtension.head

theorem objectHeadReduction_step {n : Nat} {t u : CTm Tower.Head n} :
    objectHeadReduction.step t u ↔ CWhStepR objectChurch objectRoles t u :=
  Iff.rfl

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
