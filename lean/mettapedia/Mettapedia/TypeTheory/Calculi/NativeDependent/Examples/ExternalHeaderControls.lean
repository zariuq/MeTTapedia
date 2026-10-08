import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalJudgmentControls

/-!
# Actual ordered formation certificates for dependent primitive headers

The supplied function-valued parameter telescope and complete-pair motive
headers are formed by the generated rules. Bounds cover every node of their
actual formation trees, including the argument-substitution witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Controls

theorem scalar_before {bound : Nat} (positive : 0 < bound) (n : Nat) :
    (scalar n).before signature.typeRank signature.termRank bound :=
  ⟨positive, fun position => Fin.elim0 position⟩

theorem domain_before {bound : Nat} (positive : 0 < bound) (n : Nat) :
    (domain n).before signature.typeRank signature.termRank bound :=
  ⟨scalar_before positive n, scalar_before positive (n + 1)⟩

theorem body_before {bound : Nat} (earlier : 2 < bound) (n : Nat) :
    (body n).before signature.typeRank signature.termRank bound := ⟨earlier, fun _ => trivial⟩

theorem sum_before {bound : Nat} (earlier : 2 < bound) (n : Nat) :
    (sum n).before signature.typeRank signature.termRank bound :=
  ⟨domain_before (Nat.lt_trans (by decide) earlier) n, body_before earlier n⟩

theorem emptyContext_before (bound : Nat) : emptyContext.before bound :=
  (deriveList_before_iff bound .contextNil .nil).mpr ⟨trivial, trivial⟩

theorem emptySubstitution_before {n bound : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) (ordered : formed.before bound) :
    (emptySubstitution formed).before bound := by
  unfold emptySubstitution
  apply (deriveList_before_iff bound _ _).mpr
  exact ⟨⟨formed.before_judgment ordered, trivial, fun position => Fin.elim0 position⟩,
    ordered, trivial⟩

theorem extendContext_before {n bound : Nat} {context : ContextExpr symbols n} {type : TypeExpr symbols n}
    (formed : Derivation signature (.context context)) (typed : Derivation signature (.type context type))
    (contextBound : formed.before bound) (typeBound : typed.before bound) :
    (extendContext formed typed).before bound := by
  unfold extendContext
  apply (deriveList_before_iff bound _ _).mpr
  exact ⟨⟨formed.before_judgment contextBound, (typed.before_judgment typeBound).2⟩,
    contextBound, typeBound, trivial⟩

theorem scalarFormed_before {n bound : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) (positive : 0 < bound)
    (ordered : formed.before bound) : (scalarFormed formed).before bound := by
  unfold scalarFormed
  apply (deriveList_before_iff bound _ _).mpr
  exact ⟨⟨formed.before_judgment ordered, scalar_before positive n⟩,
    ordered, emptyContext_before bound, emptySubstitution_before formed ordered, trivial⟩

theorem domainFormed_before {n bound : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) (positive : 0 < bound)
    (ordered : formed.before bound) : (domainFormed formed).before bound := by
  unfold domainFormed
  apply (deriveList_before_iff bound _ _).mpr
  have scalarBound := scalarFormed_before formed positive ordered
  exact ⟨⟨formed.before_judgment ordered, domain_before positive n⟩,
    scalarBound, scalarFormed_before (extendContext formed (scalarFormed formed)) positive
      (extendContext_before formed (scalarFormed formed) ordered scalarBound), trivial⟩

theorem functionHeader_before {bound : Nat} (positive : 0 < bound) : functionHeader.before bound :=
  extendContext_before emptyContext (domainFormed emptyContext) (emptyContext_before bound)
    (domainFormed_before emptyContext positive (emptyContext_before bound))

theorem lookupVariable_before {n bound : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) (position : Fin n)
    (ordered : formed.before bound) : (lookupVariable formed position).before bound := by
  unfold lookupVariable
  apply (deriveList_before_iff bound _ _).mpr
  exact ⟨⟨formed.before_judgment ordered, trivial,
    context.lookup_before signature.typeRank signature.termRank bound (formed.before_judgment ordered) position⟩,
    ordered, trivial⟩

theorem extendSubstitutionProof_before {n m bound : Nat}
    {source : ContextExpr symbols n} {target : ContextExpr symbols m} {type : TypeExpr symbols m}
    {substitution : Substitution symbols m n} {term : TermExpr symbols n}
    (previous : Derivation signature (.substitution source target substitution))
    (formed : Derivation signature (.type target type))
    (typed : Derivation signature (.term source term (type.substitute substitution)))
    (previousBound : previous.before bound) (formationBound : formed.before bound)
    (termBound : typed.before bound) : (extendSubstitutionProof previous formed typed).before bound := by
  unfold extendSubstitutionProof
  apply (deriveList_before_iff bound _ _).mpr
  have old := previous.before_judgment previousBound
  have formation := formed.before_judgment formationBound
  have value := typed.before_judgment termBound
  refine ⟨⟨old.1, ⟨old.2.1, formation.2⟩, ?_⟩,
    previousBound, formationBound, termBound, trivial⟩
  intro position
  cases position using Fin.cases with
  | zero => exact value.2.1
  | succ prior => exact old.2.2 prior

theorem fibreFormed_before {n bound : Nat} {context : ContextExpr symbols n} {term : TermExpr symbols n}
    (formed : Derivation signature (.context context))
    (typed : Derivation signature (.term context term (domain n)))
    (earlier : 2 < bound) (contextBound : formed.before bound) (termBound : typed.before bound) :
    (fibreFormed formed typed).before bound := by
  unfold fibreFormed
  apply (deriveList_before_iff bound _ _).mpr
  have positive : 0 < bound := Nat.lt_trans (by decide) earlier
  have value := typed.before_judgment termBound
  constructor
  · exact ⟨formed.before_judgment contextBound, earlier, fun _ => value.2.1⟩
  · simp only [PremiseEvidence.before]
    refine ⟨contextBound, functionHeader_before positive, ?_, trivial⟩
    apply (Derivation.before_reindex _ _).mpr
    exact extendSubstitutionProof_before _ _ _ (emptySubstitution_before formed contextBound)
      (domainFormed_before emptyContext positive (emptyContext_before bound))
      ((Derivation.before_reindex _ _).mpr termBound)

theorem bodyFormed_before {n bound : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) (earlier : 2 < bound)
    (ordered : formed.before bound) : (bodyFormed formed).before bound := by
  unfold bodyFormed
  apply fibreFormed_before _ _ earlier
  · exact extendContext_before formed (domainFormed formed) ordered
      (domainFormed_before formed (Nat.lt_trans (by decide) earlier) ordered)
  · apply (Derivation.before_reindex _ _).mpr
    exact lookupVariable_before _ 0
      (extendContext_before formed (domainFormed formed) ordered
        (domainFormed_before formed (Nat.lt_trans (by decide) earlier) ordered))

theorem sumFormed_before {n bound : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) (earlier : 2 < bound)
    (ordered : formed.before bound) : (sumFormed formed).before bound := by
  unfold sumFormed
  apply (deriveList_before_iff bound _ _).mpr
  exact ⟨⟨formed.before_judgment ordered, sum_before earlier n⟩,
    domainFormed_before formed (Nat.lt_trans (by decide) earlier) ordered,
    bodyFormed_before formed earlier ordered, trivial⟩

theorem pairHeader_before {bound : Nat} (earlier : 2 < bound) : pairHeader.before bound :=
  extendContext_before emptyContext (sumFormed emptyContext) (emptyContext_before bound)
    (sumFormed_before emptyContext earlier (emptyContext_before bound))

theorem componentContextFormed_before {n bound : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) (earlier : 2 < bound)
    (ordered : formed.before bound) : (componentContextFormed formed).before bound := by
  unfold componentContextFormed
  exact extendContext_before _ _
    (extendContext_before formed (domainFormed formed) ordered
      (domainFormed_before formed (Nat.lt_trans (by decide) earlier) ordered))
    (bodyFormed_before formed earlier ordered)

theorem genericPairTyped_before {n bound : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) (earlier : 2 < bound)
    (ordered : formed.before bound) : (genericPairTyped formed).before bound := by
  unfold genericPairTyped
  apply (Derivation.before_reindex _ _).mpr
  apply (deriveList_before_iff bound _ _).mpr
  have extendedBound := componentContextFormed_before formed earlier ordered
  let extended := componentContextFormed formed
  constructor
  · exact ⟨extended.before_judgment extendedBound,
      ⟨domain_before (Nat.lt_trans (by decide) earlier) _, body_before earlier _, trivial, trivial⟩,
      sum_before earlier _⟩
  · simp only [PremiseEvidence.before]
    refine ⟨domainFormed_before extended (Nat.lt_trans (by decide) earlier) extendedBound,
      bodyFormed_before extended earlier extendedBound, ?_,
      lookupVariable_before extended _ extendedBound, trivial⟩
    apply (Derivation.before_reindex _ _).mpr
    exact lookupVariable_before extended _ extendedBound

theorem motiveFormed_before {n bound : Nat} {context : ContextExpr symbols n} {term : TermExpr symbols n}
    (formed : Derivation signature (.context context))
    (typed : Derivation signature (.term context term (sum n)))
    (earlier : 4 < bound) (contextBound : formed.before bound) (termBound : typed.before bound) :
    (motiveFormed formed typed).before bound := by
  unfold motiveFormed
  apply (deriveList_before_iff bound _ _).mpr
  have twoEarlier : 2 < bound := Nat.lt_trans (by decide) earlier
  have value := typed.before_judgment termBound
  constructor
  · exact ⟨formed.before_judgment contextBound, earlier, fun _ => value.2.1⟩
  · simp only [PremiseEvidence.before]
    refine ⟨contextBound, pairHeader_before twoEarlier, ?_, trivial⟩
    apply (Derivation.before_reindex _ _).mpr
    exact extendSubstitutionProof_before _ _ _ (emptySubstitution_before formed contextBound)
      (sumFormed_before emptyContext twoEarlier (emptyContext_before bound))
      ((Derivation.before_reindex _ _).mpr termBound)

/-- The exact supplied header certificates respect the earlier-rank condition
at every premise occurrence. -/
def headers : HeaderFormation signature where
  typeHeader
    | .scalar => emptyContext
    | .fibre => functionHeader
    | .pairMotive => pairHeader
  typeHeader_before := by
    intro symbol
    cases symbol with
    | scalar => exact emptyContext_before 0
    | fibre => exact functionHeader_before (by decide)
    | pairMotive => exact pairHeader_before (by decide)
  termHeader := fun _ => branchHeader
  termHeader_before := by
    intro symbol
    cases symbol
    exact componentContextFormed_before emptyContext (by decide) (emptyContext_before 5)
  termResult := fun _ => branchResultFormed
  termResult_before := by
    intro symbol
    cases symbol
    exact motiveFormed_before branchHeader (genericPairTyped emptyContext) (by decide)
      (componentContextFormed_before emptyContext (by decide) (emptyContext_before 5))
      (genericPairTyped_before emptyContext (by decide) (emptyContext_before 5))

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Controls
