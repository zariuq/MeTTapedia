import Mettapedia.Logic.HOL.IndexedConstructorInduction
import Mettapedia.Logic.HOL.UniversalArgumentProofs

/-!
# Explicit original-field clauses for indexed constructor methods

Each row universally binds its original fields and retains both its field
guard and supplied child condition. These clauses generate the existing
indexed-case interface. The motive and child condition remain parameters;
the clauses must be proved before the resulting method can be published.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms

open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    (inventory : ConstructorPrograms Const Γ) {space : Ty Base}
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (children : Term Const Γ (inventory.number ⇒ space))
    (condition : Term Const Γ (payloadType inventory.fields ⇒ .prop))
    (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))

def rowBody (occurrence : Fin inventory.fields.length) :
    ArgumentBody Const Γ (inventory.fields.get occurrence) :=
  fun images arguments =>
    .imp (applyArguments _ (HOL.subst images (inventory.allowed occurrence)) arguments)
      (.imp (.app (HOL.subst images condition) (encode inventory.fields occurrence arguments))
        (.app (.app (HOL.subst images property)
          ((inventory.subst images).constructorValue (HOL.subst images construct) occurrence arguments
            (HOL.subst images children)))
          (applyFields _ (HOL.subst images (inventory.result occurrence)) arguments)))

theorem rowBody_natural (occurrence : Fin inventory.fields.length) :
    NaturalBody (inventory.rowBody construct children condition property occurrence) := by
  intro Δ Ξ earlier later arguments
  simp only [rowBody, constructorValue, HOL.subst, ConstructorPrograms.subst,
    applyArguments_subst, applyFields_subst, encode_subst, HOL.subst_comp]
  rfl

def rowClause (occurrence : Fin inventory.fields.length) : Formula Const Γ :=
  forallArguments (inventory.fields.get occurrence)
    (inventory.rowBody construct children condition property occurrence)

theorem rowClause_subst (images : Subst Const Γ Ξ) (occurrence : Fin inventory.fields.length) :
    HOL.subst images (inventory.rowClause construct children condition property occurrence) =
      (inventory.subst images).rowClause (HOL.subst images construct) (HOL.subst images children)
        (HOL.subst images condition) (HOL.subst images property) occurrence := by
  unfold rowClause
  rw [forallArguments_subst _ _ _ (inventory.rowBody_natural construct children condition property occurrence)]
  apply congrArg (forallArguments (inventory.fields.get occurrence))
  funext laterContext later arguments
  simp only [rowBody, constructorValue, ConstructorPrograms.subst, HOL.subst_comp]
  rfl

def rowGoal (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence)) : Formula Const Γ :=
  .imp (applyArguments _ (inventory.allowed occurrence) arguments)
    (.imp (.app condition (encode inventory.fields occurrence arguments))
      (.app (.app property (inventory.constructorValue construct occurrence arguments children))
        (applyFields _ (inventory.result occurrence) arguments)))

theorem rowBody_identity (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence)) :
    inventory.rowBody construct children condition property occurrence Subst.id arguments =
      inventory.rowGoal construct children condition property occurrence arguments := by
  simp only [rowBody, rowGoal, HOL.subst_id, constructorValue, ConstructorPrograms.subst]

def eliminateRow {assumptions : List (Formula Const Γ)} (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (clause : ProofSyntax Const assumptions (inventory.rowClause construct children condition property occurrence)) :
    ProofSyntax Const assumptions (inventory.rowGoal construct children condition property occurrence arguments) :=
  ProofSyntax.castIndices rfl (inventory.rowBody_identity construct children condition property occurrence arguments)
    (forallArguments_elim _ _ (inventory.rowBody_natural construct children condition property occurrence) arguments clause)

theorem eliminateRow_free {assumptions : List (Formula Const Γ)} (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (clause : ProofSyntax Const assumptions (inventory.rowClause construct children condition property occurrence))
    (free : clause.FunctionExtensionalityFree) :
    (inventory.eliminateRow construct children condition property occurrence arguments clause).FunctionExtensionalityFree := by
  unfold eliminateRow
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact forallArguments_elim_free _ _ _ arguments clause free

def casesOfClauses {assumptions : List (Formula Const Γ)}
    (clauses : ∀ occurrence, ProofSyntax Const assumptions
      (inventory.rowClause construct children condition property occurrence)) :
    inventory.IndexedCases construct children condition property assumptions := by
  intro Ξ images occurrence arguments
  let shifted := inventory.subst images
  let row : ProofSyntax Const (assumptions.map (HOL.subst images))
      (shifted.rowClause (HOL.subst images construct) (HOL.subst images children)
        (HOL.subst images condition) (HOL.subst images property) occurrence) :=
    ProofSyntax.castIndices rfl (inventory.rowClause_subst construct children condition property images occurrence)
      (ProofSyntax.subst images (clauses occurrence))
  let localProof := ((shifted.eliminateRow (HOL.subst images construct) (HOL.subst images children)
      (HOL.subst images condition) (HOL.subst images property) occurrence arguments row).prepend
        (.app (HOL.subst images condition) (encode inventory.fields occurrence arguments))).prepend
          (applyArguments _ (shifted.allowed occurrence) arguments)
  exact .impE (.impE localProof (.hyp 0)) (.hyp 1)

theorem casesOfClauses_free {assumptions : List (Formula Const Γ)}
    (clauses : ∀ occurrence, ProofSyntax Const assumptions
      (inventory.rowClause construct children condition property occurrence))
    (free : ∀ occurrence, (clauses occurrence).FunctionExtensionalityFree) :
    ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) occurrence arguments,
      (inventory.casesOfClauses construct children condition property clauses images occurrence arguments).FunctionExtensionalityFree := by
  intro Ξ images occurrence arguments
  unfold casesOfClauses
  refine ⟨⟨?_, trivial⟩, trivial⟩
  apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
  apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
  apply eliminateRow_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr (free occurrence)

private def exchangeTwo {assumptions : List (Formula Const Γ)} {first second : Formula Const Γ} :
    ProofSyntax.OccurrenceMap (first :: second :: assumptions) (second :: first :: assumptions) where
  index := Fin.cases 1 (Fin.cases 0 (fun prior => prior.succ.succ))
  get_eq occurrence := by
    refine Fin.cases ?_ (fun occurrence => ?_) occurrence
    · rfl
    · refine Fin.cases ?_ (fun _ => ?_) occurrence <;> rfl

def clausesOfCases {assumptions : List (Formula Const Γ)}
    (cases : inventory.IndexedCases construct children condition property assumptions)
    (occurrence : Fin inventory.fields.length) :
    ProofSyntax Const assumptions (inventory.rowClause construct children condition property occurrence) :=
  forallArguments_intro _ _ (fun images arguments =>
    .impI (.impI (ProofSyntax.mono exchangeTwo (cases images occurrence arguments))))

theorem clausesOfCases_free {assumptions : List (Formula Const Γ)}
    (cases : inventory.IndexedCases construct children condition property assumptions)
    (free : ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) occurrence arguments,
      (cases images occurrence arguments).FunctionExtensionalityFree)
    (occurrence : Fin inventory.fields.length) :
    (inventory.clausesOfCases construct children condition property cases occurrence).FunctionExtensionalityFree := by
  apply forallArguments_intro_free
  intro Ξ images arguments
  exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (free images occurrence arguments)

theorem rowClauses_iff_cases {assumptions : List (Formula Const Γ)} :
    Nonempty (∀ occurrence, ProofSyntax Const assumptions
      (inventory.rowClause construct children condition property occurrence)) ↔
      Nonempty (inventory.IndexedCases construct children condition property assumptions) :=
  ⟨fun ⟨clauses⟩ => ⟨inventory.casesOfClauses construct children condition property clauses⟩,
    fun ⟨cases⟩ => ⟨inventory.clausesOfCases construct children condition property cases⟩⟩

def fromClauses {assumptions : List (Formula Const Γ)}
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (clauses : ∀ occurrence, ProofSyntax Const assumptions
      (inventory.rowClause construct children condition property occurrence))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (shape : ProofSyntax Const assumptions (.app (.app inventory.shapeProgram tag) payload))
    (child : ProofSyntax Const assumptions (.app condition payload)) :
    ProofSyntax Const assumptions
      (.app (IndexedPredicateInduction.lift (inventory.rootProgram construct) property)
        (.app (.app (.app construct tag) payload) children)) :=
  inventory.constructorCases_lift construct tag payload children condition property
    (inventory.casesOfClauses construct children condition property clauses) injectivity shape child

theorem fromClauses_free {assumptions : List (Formula Const Γ)}
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (clauses : ∀ occurrence, ProofSyntax Const assumptions
      (inventory.rowClause construct children condition property occurrence))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (shape : ProofSyntax Const assumptions (.app (.app inventory.shapeProgram tag) payload))
    (child : ProofSyntax Const assumptions (.app condition payload))
    (clausesFree : ∀ occurrence, (clauses occurrence).FunctionExtensionalityFree)
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (shapeFree : shape.FunctionExtensionalityFree) (childFree : child.FunctionExtensionalityFree) :
    (inventory.fromClauses construct children condition property tag payload clauses injectivity shape child).FunctionExtensionalityFree :=
  inventory.constructorCases_lift_free construct tag payload children condition property _ injectivity shape child
    (inventory.casesOfClauses_free construct children condition property clauses clausesFree)
    injectivityFree shapeFree childFree

def spineAssumptions (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields)) : List (Formula Const Γ) :=
  ConstructorInjectivity.statement construct :: .app (.app inventory.shapeProgram tag) payload ::
    .app condition payload :: List.ofFn (inventory.rowClause construct children condition property)

def rowHypothesis (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields)) (occurrence : Fin inventory.fields.length) :
    ProofSyntax Const (inventory.spineAssumptions construct children condition property tag payload)
      (inventory.rowClause construct children condition property occurrence) := by
  let position : Fin (inventory.spineAssumptions construct children condition property tag payload).length :=
    ⟨occurrence.val + 3, by simp only [spineAssumptions, List.length_cons, List.length_ofFn]; omega⟩
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp (Const := Const) position)
  simp [position, spineAssumptions, List.get_eq_getElem]

theorem rowHypothesis_free (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields)) (occurrence : Fin inventory.fields.length) :
    (inventory.rowHypothesis construct children condition property tag payload occurrence).FunctionExtensionalityFree := by
  unfold rowHypothesis
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def spineProof (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields)) :
    ProofSyntax Const (inventory.spineAssumptions construct children condition property tag payload)
      (.app (IndexedPredicateInduction.lift (inventory.rootProgram construct) property)
        (.app (.app (.app construct tag) payload) children)) :=
  inventory.fromClauses construct children condition property tag payload
    (assumptions := inventory.spineAssumptions construct children condition property tag payload)
    (inventory.rowHypothesis construct children condition property tag payload)
    (.hyp (Δ := inventory.spineAssumptions construct children condition property tag payload) ⟨0, by simp [spineAssumptions]⟩)
    (.hyp (Δ := inventory.spineAssumptions construct children condition property tag payload) ⟨1, by simp [spineAssumptions]⟩)
    (.hyp (Δ := inventory.spineAssumptions construct children condition property tag payload) ⟨2, by simp [spineAssumptions]⟩)

theorem spineProof_free (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields)) :
    (inventory.spineProof construct children condition property tag payload).FunctionExtensionalityFree := by
  unfold spineProof
  apply fromClauses_free
  · exact inventory.rowHypothesis_free construct children condition property tag payload
  · trivial
  · trivial
  · trivial

#print axioms rowBody_natural
#print axioms rowClause_subst
#print axioms eliminateRow_free
#print axioms casesOfClauses_free
#print axioms clausesOfCases_free
#print axioms rowClauses_iff_cases
#print axioms fromClauses_free
#print axioms spineProof_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms
