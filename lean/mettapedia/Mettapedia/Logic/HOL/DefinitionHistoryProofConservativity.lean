import Mettapedia.Logic.HOL.DefinitionHistorySemantics
import Mettapedia.Logic.HOL.ProofSyntaxHypothesisSubstitution

/-!
# Discharging the equations of checked definition histories

The newest definition has a body over its preceding signature. Its equation
and every older equation are carried into the final signature. Expanding a
history gives actual reflexivity proofs for all of those equations. Replacing
each equation occurrence by its supplied proof removes the extra assumptions
through all 29 retained HOL rules, including object binders and extensionality.

The construction keeps actual input proofs. General hypothesis substitution
can add or duplicate branches. The defining equations constructed here expand
to reflexivity leaves; their proof sizes do not certify independent evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.DefinitionHistory

universe u v

variable {Base : Type u} {source target : Ty Base → Type (max u v)}

def equations {source target : Ty Base → Type (max u v)} :
    DefinitionHistory source target → List (ClosedFormula target)
  | .nil => []
  | .add prior _ body =>
      .eq (.const DefinedConst.defined) (DefinedConst.embed body) ::
        prior.equations.map DefinedConst.embed

theorem erase_add_embed {prior : Ty Base → Type (max u v)}
    (history : DefinitionHistory source prior) (type : Ty Base) (body : ClosedTerm prior type)
    {context : Ctx Base} {result : Ty Base} (term : Term prior context result) :
    (DefinitionHistory.add history type body).erase (DefinedConst.embed term) =
      history.erase term := by
  rw [erase, DefinedConst.embed, substConst_mapConst]
  exact substConst_ext (fun _ => rfl) term

/-- Each equation has its own constructed proof after expansion. -/
def erasedEquationProof {source target : Ty Base → Type (max u v)} :
    (history : DefinitionHistory source target) →
    (occurrence : Fin history.equations.length) →
    ProofSyntax source [] (history.erase (history.equations.get occurrence))
  | .nil, occurrence => Fin.elim0 occurrence
  | .add prior type body, occurrence =>
      Fin.cases
        (ProofSyntax.castIndices rfl (by
          change Term.eq (prior.erase body) (prior.erase body) = _
          change Term.eq (prior.erase body) (prior.erase body) =
            Term.eq (prior.erase body)
              ((DefinitionHistory.add prior type body).erase (DefinedConst.embed body))
          rw [erase_add_embed]) (ProofSyntax.eqRefl (prior.erase body)))
        (fun index =>
          let original : Fin prior.equations.length :=
            index.cast (by simp only [List.length_map])
          ProofSyntax.castIndices rfl (by
            change prior.erase prior.equations[original.val] =
              (DefinitionHistory.add prior type body).erase
                (prior.equations.map DefinedConst.embed)[index.val]
            simp only [List.getElem_map, original, Fin.val_cast]
            exact (erase_add_embed prior type body _).symm)
            (erasedEquationProof prior original)) occurrence

set_option backward.isDefEq.respectTransparency false in
theorem erasedEquationProof_nodeCount (history : DefinitionHistory source target)
    (occurrence : Fin history.equations.length) :
    (history.erasedEquationProof occurrence).nodeCount = 1 := by
  induction history with
  | nil => exact Fin.elim0 occurrence
  | add prior type body ih =>
      refine Fin.cases ?_ (fun index => ?_) occurrence
      · simp only [erasedEquationProof, Fin.cases_zero, ProofSyntax.nodeCount_castIndices]
        rfl
      · simp only [erasedEquationProof, Fin.cases_succ, ProofSyntax.nodeCount_castIndices]
        exact ih _

def equationsIn (history : DefinitionHistory source target) (context : Ctx Base) :
    List (Formula target context) := history.equations.map (HOL.weakenCtx context)

def erasedEquationsInProof (history : DefinitionHistory source target)
    (context : Ctx Base) (occurrence : Fin (history.equationsIn context).length) :
    ProofSyntax source [] (history.erase ((history.equationsIn context).get occurrence)) :=
  let original : Fin history.equations.length :=
    occurrence.cast (by simp only [equationsIn, List.length_map])
  ProofSyntax.castIndices rfl (by
    change HOL.weakenCtx context (history.erase history.equations[original.val]) =
      history.erase (history.equations.map (HOL.weakenCtx context))[occurrence.val]
    simp only [List.getElem_map, original, Fin.val_cast]
    exact (substConst_weakenCtx history.images context _).symm)
    (ProofSyntax.weakenContext context (history.erasedEquationProof original))

theorem erasedEquationsInProof_nodeCount (history : DefinitionHistory source target)
    (context : Ctx Base) (occurrence : Fin (history.equationsIn context).length) :
    (history.erasedEquationsInProof context occurrence).nodeCount = 1 := by
  dsimp only [erasedEquationsInProof]
  rw [ProofSyntax.nodeCount_castIndices, ProofSyntax.weakenContext_nodeCount]
  exact history.erasedEquationProof_nodeCount _

/-- Remove definition equations by the actual expanded proofs, without
choosing receipts from proposition-valued derivability. -/
def dischargeEquations (history : DefinitionHistory source target)
    {context : Ctx Base} {assumptions : List (Formula target context)}
    {conclusion : Formula target context}
    (proof : ProofSyntax target (assumptions ++ history.equationsIn context) conclusion) :
    ProofSyntax source (assumptions.map history.erase) (history.erase conclusion) := by
  let targetAssumptions := assumptions.map history.erase
  let equationAssumptions := (history.equationsIn context).map history.erase
  let equationProofs : ProofSyntax.HypothesisSubstitution equationAssumptions targetAssumptions :=
    fun occurrence =>
      let original : Fin (history.equationsIn context).length :=
        occurrence.cast (by simp only [equationAssumptions, List.length_map])
      ProofSyntax.castIndices rfl (by
        change history.erase (history.equationsIn context)[original.val] =
          ((history.equationsIn context).map history.erase)[occurrence.val]
        simp only [List.getElem_map, original, Fin.val_cast])
        (ProofSyntax.mono (ProofSyntax.emptyOccurrenceMap targetAssumptions)
          (history.erasedEquationsInProof context original))
  let expanded := history.eraseProof proof
  let separated := ProofSyntax.castIndices (List.map_append ..) rfl expanded
  exact ProofSyntax.substituteHypotheses
    (ProofSyntax.HypothesisSubstitution.append targetAssumptions equationAssumptions
      targetAssumptions (ProofSyntax.HypothesisSubstitution.identity _) equationProofs)
    separated

theorem dischargeEquations_erasure (history : DefinitionHistory source target)
    {context : Ctx Base} {assumptions : List (Formula target context)}
    {conclusion : Formula target context}
    (proof : ProofSyntax target (assumptions ++ history.equationsIn context) conclusion) :
    ExtDerivation source (assumptions.map history.erase) (history.erase conclusion) :=
  (history.dischargeEquations proof).erase

theorem erase_embedded_assumptions (history : DefinitionHistory source target)
    {context : Ctx Base} (assumptions : List (Formula source context)) :
    (assumptions.map history.embed).map history.erase = assumptions := by
  induction assumptions with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, history.erase_embed, ih]

/-- A proof of an old sequent using any checked definition equations gives
an actual proof over the original signature. -/
def oldProof (history : DefinitionHistory source target)
    {context : Ctx Base} {assumptions : List (Formula source context)}
    {conclusion : Formula source context}
    (proof : ProofSyntax target
      (assumptions.map history.embed ++ history.equationsIn context) (history.embed conclusion)) :
    ProofSyntax source assumptions conclusion :=
  ProofSyntax.castIndices (history.erase_embedded_assumptions assumptions)
    (history.erase_embed conclusion) (history.dischargeEquations proof)

def extendProof (history : DefinitionHistory source target)
    {context : Ctx Base} {assumptions : List (Formula source context)}
    {conclusion : Formula source context} (proof : ProofSyntax source assumptions conclusion) :
    ProofSyntax target (assumptions.map history.embed ++ history.equationsIn context)
      (history.embed conclusion) :=
  ProofSyntax.mono (ProofSyntax.OccurrenceMap.appendRight _ _)
    (ProofSyntax.mapConst history.embedding proof)

theorem old_sequent_conservative (history : DefinitionHistory source target)
    {context : Ctx Base} (assumptions : List (Formula source context))
    (conclusion : Formula source context) :
    Nonempty (ProofSyntax target
      (assumptions.map history.embed ++ history.equationsIn context) (history.embed conclusion)) ↔
      Nonempty (ProofSyntax source assumptions conclusion) := by
  constructor
  · rintro ⟨proof⟩
    exact ⟨history.oldProof proof⟩
  · rintro ⟨proof⟩
    exact ⟨history.extendProof proof⟩

theorem old_derivation_conservative (history : DefinitionHistory source target)
    {context : Ctx Base} (assumptions : List (Formula source context))
    (conclusion : Formula source context) :
    ExtDerivation target
      (assumptions.map history.embed ++ history.equationsIn context) (history.embed conclusion) ↔
      ExtDerivation source assumptions conclusion := by
  constructor
  · intro derivation
    obtain ⟨proof⟩ := ProofSyntax.nonempty_of_derivation derivation
    exact (history.oldProof proof).erase
  · intro derivation
    obtain ⟨proof⟩ := ProofSyntax.nonempty_of_derivation derivation
    exact (history.extendProof proof).erase

end Mettapedia.Logic.HOL.DefinitionHistory
