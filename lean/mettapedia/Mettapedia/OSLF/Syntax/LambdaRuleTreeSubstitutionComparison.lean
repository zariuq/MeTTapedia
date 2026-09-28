import Mettapedia.OSLF.Syntax.LambdaRuleTreeSubstitution

/-!
# Comparing indexed-tree substitution with retained-event substitution

The four-rule polynomial has a directly recursive substitution action.
The equivalent event graph also has an action. The comparison is stated on
the total space of endpoint-indexed trees, so both endpoints and the entire
chosen firing occurrence must agree.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaDerivationGraph
open Mettapedia.TypeTheory


private theorem packed_eq_of_components {Γ : Ctx sig}
    {firstSource secondSource firstTarget secondTarget : Term sig Γ .term}
    (sourceEq : firstSource = secondSource)
    (targetEq : firstTarget = secondTarget)
    {first : Derivation firstSource firstTarget}
    {second : Derivation secondSource secondTarget}
    (treeEq : HEq first second) :
    (⟨firstSource, firstTarget, first⟩ : PackedTree Γ) =
      ⟨secondSource, secondTarget, second⟩ := by
  cases sourceEq
  cases targetEq
  exact congrArg
    (fun tree : Derivation firstSource firstTarget =>
      (⟨firstSource, firstTarget, tree⟩ : PackedTree Γ))
    (eq_of_heq treeEq)

/-- The earlier direct substitution on the indexed polynomial, packed with
its exact substituted endpoints. -/
noncomputable def packedDirectSubstitute {Γ Δ : Ctx sig}
    (σ : Sub sig Γ Δ) (packed : PackedTree Γ) : PackedTree Δ :=
  ⟨bind σ packed.1, bind σ packed.2.1,
    substituteTree (judgment packed.1 packed.2.1) packed.2.2 σ⟩

/-- The direct indexed substitution and event substitution agree on a beta
firing, before transporting their endpoint indices. -/
private theorem beta_tree_compare {Γ Δ : Ctx sig}
    (body : Term sig (.term :: Γ) .term) (arg : Term sig Γ .term)
    (σ : Sub sig Γ Δ) :
    HEq
    (substituteTree
      (judgment (appT (lamT body) arg) (inst body arg))
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.beta body arg) (fun impossible => impossible.elim)) σ)
    (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
      (RuleShape.beta (bind (liftSub σ [.term]) body) (bind σ arg))
      (fun impossible => impossible.elim)) := by
  unfold substituteTree
  dsimp only [IndexedPolynomial.Fix.eliminate]
  dsimp only [id]
  exact cast_heq _ _

private theorem appCongL_tree_compare {Γ Δ : Ctx sig}
    (arg : Term sig Γ .term) (premise : Event Γ)
    (σ : Sub sig Γ Δ)
    (childEq : HEq
      (substituteTree (judgment (source premise) (target premise))
        (treeOfEvent premise) σ)
      (treeOfEvent (LambdaDerivationGraph.map σ premise))) :
    HEq
      (substituteTree
        (judgment (source (Event.appCongL arg premise))
          (target (Event.appCongL arg premise)))
        (treeOfEvent (Event.appCongL arg premise)) σ)
      (treeOfEvent (LambdaDerivationGraph.map σ
        (Event.appCongL arg premise))) := by
  change HEq
    (substituteTree
      (judgment (appT (source premise) arg)
        (appT (target premise) arg))
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.appCongL (source premise) (target premise) arg)
        (fun _ => treeOfEvent premise)) σ)
    (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
      (RuleShape.appCongL
        (source (LambdaDerivationGraph.map σ premise))
        (target (LambdaDerivationGraph.map σ premise))
        (bind σ arg))
      (fun _ => treeOfEvent (LambdaDerivationGraph.map σ premise)))
  unfold substituteTree
  dsimp only [IndexedPolynomial.Fix.eliminate, id]
  apply HEq.trans
    (b := IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
      (RuleShape.appCongL
        (bind σ (source premise)) (bind σ (target premise))
        (bind σ arg))
      (fun _ => substituteTree (judgment (source premise) (target premise))
        (treeOfEvent premise) σ))
  · unfold substituteTree
    dsimp only [IndexedPolynomial.Fix.eliminate]
    simp only [eq_mpr_eq_cast]
    exact (cast_heq _ _).trans (cast_heq _ _)
  · exact appCongL_heq (bind σ arg)
      (LambdaDerivationGraph.source_map σ premise).symm
      (LambdaDerivationGraph.target_map σ premise).symm
      (substituteTree (judgment (source premise) (target premise))
        (treeOfEvent premise) σ)
      (treeOfEvent (LambdaDerivationGraph.map σ premise)) childEq

private theorem appCongR_tree_compare {Γ Δ : Ctx sig}
    (funTerm : Term sig Γ .term) (premise : Event Γ)
    (σ : Sub sig Γ Δ)
    (childEq : HEq
      (substituteTree (judgment (source premise) (target premise))
        (treeOfEvent premise) σ)
      (treeOfEvent (LambdaDerivationGraph.map σ premise))) :
    HEq
      (substituteTree
        (judgment (source (Event.appCongR funTerm premise))
          (target (Event.appCongR funTerm premise)))
        (treeOfEvent (Event.appCongR funTerm premise)) σ)
      (treeOfEvent (LambdaDerivationGraph.map σ
        (Event.appCongR funTerm premise))) := by
  change HEq
    (substituteTree
      (judgment (appT funTerm (source premise))
        (appT funTerm (target premise)))
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.appCongR funTerm (source premise) (target premise))
        (fun _ => treeOfEvent premise)) σ)
    (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
      (RuleShape.appCongR
        (bind σ funTerm)
        (source (LambdaDerivationGraph.map σ premise))
        (target (LambdaDerivationGraph.map σ premise)))
      (fun _ => treeOfEvent (LambdaDerivationGraph.map σ premise)))
  unfold substituteTree
  dsimp only [IndexedPolynomial.Fix.eliminate, id]
  apply HEq.trans
    (b := IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
      (RuleShape.appCongR
        (bind σ funTerm) (bind σ (source premise))
        (bind σ (target premise)))
      (fun _ => substituteTree (judgment (source premise) (target premise))
        (treeOfEvent premise) σ))
  · unfold substituteTree
    dsimp only [IndexedPolynomial.Fix.eliminate]
    simp only [eq_mpr_eq_cast]
    exact (cast_heq _ _).trans (cast_heq _ _)
  · exact appCongR_heq (bind σ funTerm)
      (LambdaDerivationGraph.source_map σ premise).symm
      (LambdaDerivationGraph.target_map σ premise).symm
      (substituteTree (judgment (source premise) (target premise))
        (treeOfEvent premise) σ)
      (treeOfEvent (LambdaDerivationGraph.map σ premise)) childEq

private theorem lamCong_tree_compare {Γ Δ : Ctx sig}
    (premise : Event (.term :: Γ)) (σ : Sub sig Γ Δ)
    (childEq : HEq
      (substituteTree (judgment (source premise) (target premise))
        (treeOfEvent premise) (liftSub σ [.term]))
      (treeOfEvent (LambdaDerivationGraph.map (liftSub σ [.term]) premise))) :
    HEq
      (substituteTree
        (judgment (source (Event.lamCong premise))
          (target (Event.lamCong premise)))
        (treeOfEvent (Event.lamCong premise)) σ)
      (treeOfEvent (LambdaDerivationGraph.map σ
        (Event.lamCong premise))) := by
  change HEq
    (substituteTree
      (judgment (lamT (source premise)) (lamT (target premise)))
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.lamCong (source premise) (target premise))
        (fun _ => treeOfEvent premise)) σ)
    (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
      (RuleShape.lamCong
        (source (LambdaDerivationGraph.map (liftSub σ [.term]) premise))
        (target (LambdaDerivationGraph.map (liftSub σ [.term]) premise)))
      (fun _ => treeOfEvent (LambdaDerivationGraph.map
        (liftSub σ [.term]) premise)))
  unfold substituteTree
  dsimp only [IndexedPolynomial.Fix.eliminate, id]
  apply HEq.trans
    (b := IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
      (RuleShape.lamCong
        (bind (liftSub σ [.term]) (source premise))
        (bind (liftSub σ [.term]) (target premise)))
      (fun _ => substituteTree (judgment (source premise) (target premise))
        (treeOfEvent premise) (liftSub σ [.term])))
  · unfold substituteTree
    dsimp only [IndexedPolynomial.Fix.eliminate]
    simp only [eq_mpr_eq_cast]
    exact (cast_heq _ _).trans (cast_heq _ _)
  · exact lamCong_heq
      (LambdaDerivationGraph.source_map (liftSub σ [.term]) premise).symm
      (LambdaDerivationGraph.target_map (liftSub σ [.term]) premise).symm
      (substituteTree (judgment (source premise) (target premise))
        (treeOfEvent premise) (liftSub σ [.term]))
      (treeOfEvent (LambdaDerivationGraph.map (liftSub σ [.term]) premise)) childEq

/-- Recursive substitution on the four-rule polynomial agrees with
substitution of retained firing events, for every constructor and premise
depth. The heterogeneous comparison records the endpoint-index transport. -/
theorem substituteTree_treeOfEvent :
    ∀ {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ) (event : Event Γ),
      HEq
        (substituteTree (judgment (source event) (target event))
          (treeOfEvent event) σ)
        (treeOfEvent (LambdaDerivationGraph.map σ event))
  | _, _, σ, .beta body arg => beta_tree_compare body arg σ
  | _, _, σ, .appCongL arg premise =>
      appCongL_tree_compare arg premise σ (substituteTree_treeOfEvent σ premise)
  | _, _, σ, .appCongR funTerm premise =>
      appCongR_tree_compare funTerm premise σ (substituteTree_treeOfEvent σ premise)
  | _, _, σ, .lamCong premise =>
      lamCong_tree_compare premise σ
        (substituteTree_treeOfEvent (liftSub σ [.term]) premise)

/-- Both substitutions agree on a complete firing represented by an event.
The endpoint equalities and tree comparison are proved independently. -/
theorem packedDirectSubstitute_packTree {Γ Δ : Ctx sig}
    (σ : Sub sig Γ Δ) (event : Event Γ) :
    packedDirectSubstitute σ (packTree event) =
      packedMap σ (packTree event) := by
  rw [packedMap, unpack_pack]
  change (⟨bind σ (source event), bind σ (target event),
      substituteTree (judgment (source event) (target event))
        (treeOfEvent event) σ⟩ : PackedTree Δ) =
    ⟨source (LambdaDerivationGraph.map σ event),
      target (LambdaDerivationGraph.map σ event),
      treeOfEvent (LambdaDerivationGraph.map σ event)⟩
  exact packed_eq_of_components
    (LambdaDerivationGraph.source_map σ event).symm
    (LambdaDerivationGraph.target_map σ event).symm
    (substituteTree_treeOfEvent σ event)

/-- The pre-existing recursive polynomial substitution is exactly the
functorial action transported from retained firing events. This comparison
also applies to arbitrarily deep trees, not only to their four roots. -/
theorem packedDirectSubstitute_eq_packedMap {Γ Δ : Ctx sig}
    (σ : Sub sig Γ Δ) (packed : PackedTree Γ) :
    packedDirectSubstitute σ packed = packedMap σ packed := by
  calc
    packedDirectSubstitute σ packed =
        packedDirectSubstitute σ (packTree (unpackTree packed)) := by
          rw [pack_unpack]
    _ = packedMap σ (packTree (unpackTree packed)) :=
      packedDirectSubstitute_packTree σ (unpackTree packed)
    _ = packedMap σ packed := by rw [pack_unpack]

/-- The direct recursive action respects identity substitutions. -/
theorem packedDirectSubstitute_id {Γ : Ctx sig}
    (packed : PackedTree Γ) :
    packedDirectSubstitute (fun _ v => Term.var v) packed = packed := by
  rw [packedDirectSubstitute_eq_packedMap, packedMap_id]

/-- The direct recursive action respects substitution composition. -/
theorem packedDirectSubstitute_comp {Γ Δ Θ : Ctx sig}
    (σ : Sub sig Γ Δ) (τ : Sub sig Δ Θ) (packed : PackedTree Γ) :
    packedDirectSubstitute τ (packedDirectSubstitute σ packed) =
      packedDirectSubstitute (fun sort v => bind τ (σ sort v)) packed := by
  rw [packedDirectSubstitute_eq_packedMap,
    packedDirectSubstitute_eq_packedMap,
    packedDirectSubstitute_eq_packedMap, packedMap_comp]

/-- Direct substitution retains the complete ordered firing history. -/
theorem history_packedDirectSubstitute {Γ Δ : Ctx sig}
    (σ : Sub sig Γ Δ) (packed : PackedTree Γ) :
    history (packedDirectSubstitute σ packed).2.2 =
      history packed.2.2 := by
  rw [packedDirectSubstitute_eq_packedMap, history_packedMap]

/-- The authored closed lambda congruence has a beta premise below its
binder; the direct operation retains both constructor choices. -/
theorem closedLam_direct_history (σ : Sub sig [] []) :
    history (packedDirectSubstitute σ
      (packTree LambdaDerivationGraph.closedLamEvent)).2.2 =
      [.lamCong, .beta] := by
  rw [history_packedDirectSubstitute]
  exact closed_history

/-- Even after substitution, two different congruence choices with the
same original endpoints remain different retained firing occurrences. -/
theorem omega_direct_distinct {Δ : Ctx sig} (σ : Sub sig [] Δ) :
    packedDirectSubstitute σ (packTree LambdaDerivationGraph.leftOmegaEvent) ≠
      packedDirectSubstitute σ (packTree LambdaDerivationGraph.rightOmegaEvent) := by
  rw [packedDirectSubstitute_eq_packedMap,
    packedDirectSubstitute_eq_packedMap]
  intro equality
  have eventEq := congrArg unpackTree equality
  simp only [packedMap, unpack_pack] at eventEq
  change LambdaDerivationGraph.map σ LambdaDerivationGraph.leftOmegaEvent =
    LambdaDerivationGraph.map σ LambdaDerivationGraph.rightOmegaEvent at eventEq
  cases eventEq

#print axioms packedDirectSubstitute_eq_packedMap
#print axioms packedDirectSubstitute_id
#print axioms packedDirectSubstitute_comp
#print axioms history_packedDirectSubstitute
#print axioms closedLam_direct_history
#print axioms omega_direct_distinct
#print axioms substituteTree_treeOfEvent
#print axioms beta_tree_compare
#print axioms appCongL_tree_compare
#print axioms appCongR_tree_compare
#print axioms lamCong_tree_compare

end Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial
