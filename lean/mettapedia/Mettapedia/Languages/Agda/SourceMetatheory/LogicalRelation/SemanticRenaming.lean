import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.RenamingClauses

/-!
Renaming closure is proved for the actual relation by finite level induction.
The universe case recursively transports its lower-level codes; the Pi case
composes the real formed worlds already quantified by its Kripke clauses.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

theorem LogRel.renaming {bound : Nat} {Γ : RawContext n} {A : Ty n} {P : Pack n}
    (related : LogRel bound Γ A P) {Δ : RawContext m} {ρ : Renaming n m}
    (world : World Γ Δ ρ) : ∃ Q, LogRel bound Δ (A.rename ρ) Q ∧ RenamePack ρ P Q := by
  induction bound using Nat.strong_induction_on generalizing n Γ A P m with
  | h bound ih =>
      cases related with
      | «universe» less red =>
          rename_i k
          obtain ⟨red⟩ := red
          refine ⟨universePack (below bound) Δ k, ?_, ?_⟩
          · exact .universe less ⟨by simpa only [Ty.universe_rename] using red.rename world⟩
          refine ⟨?_, ?_, ?_⟩
          · rintro B ⟨path⟩
            exact ⟨by simpa only [Ty.universe_rename] using path.rename world⟩
          · rintro t ⟨nf, ⟨path⟩, ⟨normal⟩, R, relatedR⟩
            obtain ⟨Q, renamed, _⟩ := ih k less ((below_iff less).mp relatedR) world
            refine ⟨nf.rename ρ, ?_, ⟨normal.rename ρ⟩, Q, ?_⟩
            · exact ⟨by simpa only [Ty.universe_rename] using world.reduction path⟩
            · exact (below_iff less).mpr (by simpa only [Ty.rename] using renamed)
          · rintro t u ⟨nf, ng, ⟨left⟩, ⟨right⟩, ⟨leftNormal⟩, ⟨rightNormal⟩, ⟨comparison⟩,
              ⟨R, rightType⟩, L, leftType, typeEqual⟩
            obtain ⟨R', rightRenamed, _⟩ := ih k less ((below_iff less).mp rightType) world
            obtain ⟨L', leftRenamed, leftAction⟩ := ih k less ((below_iff less).mp leftType) world
            refine ⟨nf.rename ρ, ng.rename ρ, ?_, ?_, ⟨leftNormal.rename ρ⟩,
              ⟨rightNormal.rename ρ⟩, ?_, ?_, L', ?_, ?_⟩
            · exact ⟨by simpa only [Ty.universe_rename] using world.reduction left⟩
            · exact ⟨by simpa only [Ty.universe_rename] using world.reduction right⟩
            · exact ⟨by simpa only [Ty.universe_rename] using world.termEquality comparison⟩
            · exact ⟨R', (below_iff less).mpr (by simpa only [Ty.rename] using rightRenamed)⟩
            · exact (below_iff less).mpr (by simpa only [Ty.rename] using leftRenamed)
            · simpa only [Ty.rename] using leftAction.types typeEqual
      | neutral red normal =>
          obtain ⟨red⟩ := red
          obtain ⟨normal⟩ := normal
          exact ⟨_, .neutral ⟨red.rename world⟩
            ⟨by simpa only [typeTerm_rename] using normal.rename ρ⟩, neutralPack_rename world⟩
      | pi red domain codomain family domains codomains =>
          obtain ⟨red⟩ := red
          obtain ⟨domain⟩ := domain
          obtain ⟨codomain⟩ := codomain
          let lifted := world.lift domain
          refine ⟨_, ?_, piPack_rename world⟩
          refine LR.pi ?_ ⟨domain.rename ρ world.respects world.targetFormed⟩ ?_ (family.after world) ?_ ?_
          · exact ⟨by simpa only [Ty.pi_rename] using red.rename world⟩
          · exact ⟨by simpa only [TyAbs.open_rename] using
              codomain.rename (Renaming.lift ρ) lifted.respects lifted.targetFormed⟩
          · intro k Θ τ future
            simpa only [PiFamily.after, Ty.rename_comp] using domains (world.comp future)
          · intro k Θ τ future a argument
            simpa only [PiFamily.after, TyAbs.rename_comp] using codomains (world.comp future) argument

/-- A canonical target eliminates the existential pack without selecting data. -/
theorem LogRel.renameCanonical {bound : Nat} {Γ : RawContext n} {A : Ty n} {P : Pack n}
    (related : LogRel bound Γ A P) {Δ : RawContext m} {ρ : Renaming n m}
    (world : World Γ Δ ρ) :
    LogRel (A.rename ρ).level Δ (A.rename ρ) (annotatedPack Δ (A.rename ρ)) ∧
      RenamePack ρ P (annotatedPack Δ (A.rename ρ)) := by
  obtain ⟨Q, renamed, action⟩ := related.renaming world
  exact ⟨renamed.annotated, renamed.annotatedPack_eq.symm ▸ action⟩

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
