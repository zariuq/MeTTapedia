import Mettapedia.OSLF.Syntax.LambdaRuleDerivationPolynomial
import Mettapedia.OSLF.Syntax.LambdaDerivationGraph

/-!
# Indexed lambda-rule derivations and retained events

The indexed rule polynomial and the event presheaf present the same four
firing constructors. This module compares their retained witnesses at exact
raw endpoints, before passing to an existence predicate or quotient state.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaCategoricalModel
open CategoryTheory

open Mettapedia.OSLF.Binding.LambdaDerivationGraph

/-- Read a retained event as a tree of the indexed four-rule polynomial.
The endpoint index is computed from the same event, so no proof erasure or
choice of a witness occurs. -/
def treeOfEvent : {Γ : Ctx sig} → (event : Event Γ) →
    Derivation (source event) (target event)
  | _, .beta body arg =>
      .roll (.beta body arg) (fun impossible => impossible.elim)
  | _, .appCongL arg premise =>
      .roll (.appCongL (source premise) (target premise) arg)
        (fun _ => treeOfEvent premise)
  | _, .appCongR funTerm premise =>
      .roll (.appCongR funTerm (source premise) (target premise))
        (fun _ => treeOfEvent premise)
  | _, .lamCong premise =>
      .roll (.lamCong (source premise) (target premise))
        (fun _ => treeOfEvent premise)

/-- Read an indexed tree as a retained event, together with exact proofs of
both endpoints. The recursive premise of LamCong is read in its extended
binder context. -/
noncomputable def eventOfTree :
    (j : Judgment) → rules.Fix () j →
      {event : Event j.1 // source event = j.2.1 ∧ target event = j.2.2} :=
  IndexedPolynomial.Fix.eliminate rules
    (fun _ j _ => {event : Event j.1 //
      source event = j.2.1 ∧ target event = j.2.2})
    (fun _ j shape _children ih => by
      cases shape with
      | beta body arg => exact ⟨.beta body arg, rfl, rfl⟩
      | appCongL left right arg =>
          exact ⟨.appCongL arg (ih ()).1,
            congrArg (fun term => appT term arg) (ih ()).2.1,
            congrArg (fun term => appT term arg) (ih ()).2.2⟩
      | appCongR funTerm left right =>
          exact ⟨.appCongR funTerm (ih ()).1,
            congrArg (appT funTerm) (ih ()).2.1,
            congrArg (appT funTerm) (ih ()).2.2⟩
      | lamCong left right =>
          exact ⟨.lamCong (ih ()).1,
            congrArg lamT (ih ()).2.1,
            congrArg lamT (ih ()).2.2⟩) ()

/-- Converting a retained event into the indexed presentation and back
recovers the entire constructor tree, not just its source and target. -/
theorem eventOfTree_treeOfEvent :
    ∀ {Γ : Ctx sig} (event : Event Γ),
      (eventOfTree _ (treeOfEvent event)).1 = event
  | _, .beta body arg => rfl
  | _, .appCongL arg premise => by
      change Event.appCongL arg (eventOfTree _ (treeOfEvent premise)).1 =
        Event.appCongL arg premise
      exact congrArg (Event.appCongL arg) (eventOfTree_treeOfEvent premise)
  | _, .appCongR funTerm premise => by
      change Event.appCongR funTerm (eventOfTree _ (treeOfEvent premise)).1 =
        Event.appCongR funTerm premise
      exact congrArg (Event.appCongR funTerm) (eventOfTree_treeOfEvent premise)
  | _, .lamCong premise => by
      change Event.lamCong (eventOfTree _ (treeOfEvent premise)).1 =
        Event.lamCong premise
      exact congrArg Event.lamCong (eventOfTree_treeOfEvent premise)

private theorem eventOfTree_appCongL
    {Γ : Ctx sig} (left right arg : Term sig Γ .term)
    (children : Unit → Derivation left right) :
    (eventOfTree _
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.appCongL left right arg) children)).1 =
      Event.appCongL arg (eventOfTree _ (children ())).1 := rfl

private theorem eventOfTree_appCongR
    {Γ : Ctx sig} (funTerm left right : Term sig Γ .term)
    (children : Unit → Derivation left right) :
    (eventOfTree _
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.appCongR funTerm left right) children)).1 =
      Event.appCongR funTerm (eventOfTree _ (children ())).1 := rfl

private theorem eventOfTree_lamCong
    {Γ : Ctx sig} (left right : Term sig (.term :: Γ) .term)
    (children : Unit → Derivation left right) :
    (eventOfTree _
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.lamCong left right) children)).1 =
      Event.lamCong (eventOfTree _ (children ())).1 := rfl

/-- Application-left congruence transports a premise comparison across
equal endpoint indices without identifying different firing constructors. -/
theorem appCongL_heq {Γ : Ctx sig}
    {firstSource firstTarget secondSource secondTarget : Term sig Γ .term}
    (arg : Term sig Γ .term)
    (sourceEq : firstSource = secondSource)
    (targetEq : firstTarget = secondTarget)
    (first : Derivation firstSource firstTarget)
    (second : Derivation secondSource secondTarget)
    (childEq : HEq first second) :
    HEq
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.appCongL firstSource firstTarget arg) (fun _ => first))
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.appCongL secondSource secondTarget arg) (fun _ => second)) := by
  cases sourceEq
  cases targetEq
  exact heq_of_eq (congrArg
    (fun child : Derivation firstSource firstTarget =>
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.appCongL firstSource firstTarget arg) (fun _ => child)))
    (eq_of_heq childEq))

/-- Application-right congruence transports a premise comparison across
equal endpoint indices. -/
theorem appCongR_heq {Γ : Ctx sig}
    {firstSource firstTarget secondSource secondTarget : Term sig Γ .term}
    (funTerm : Term sig Γ .term)
    (sourceEq : firstSource = secondSource)
    (targetEq : firstTarget = secondTarget)
    (first : Derivation firstSource firstTarget)
    (second : Derivation secondSource secondTarget)
    (childEq : HEq first second) :
    HEq
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.appCongR funTerm firstSource firstTarget) (fun _ => first))
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.appCongR funTerm secondSource secondTarget) (fun _ => second)) := by
  cases sourceEq
  cases targetEq
  exact heq_of_eq (congrArg
    (fun child : Derivation firstSource firstTarget =>
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.appCongR funTerm firstSource firstTarget) (fun _ => child)))
    (eq_of_heq childEq))

/-- Lambda congruence transports a premise comparison in the extended
binder context across equal endpoint indices. -/
theorem lamCong_heq {Γ : Ctx sig}
    {firstSource firstTarget secondSource secondTarget :
      Term sig (.term :: Γ) .term}
    (sourceEq : firstSource = secondSource)
    (targetEq : firstTarget = secondTarget)
    (first : Derivation firstSource firstTarget)
    (second : Derivation secondSource secondTarget)
    (childEq : HEq first second) :
    HEq
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.lamCong firstSource firstTarget) (fun _ => first))
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.lamCong secondSource secondTarget) (fun _ => second)) := by
  cases sourceEq
  cases targetEq
  exact heq_of_eq (congrArg
    (fun child : Derivation firstSource firstTarget =>
      (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
        (RuleShape.lamCong firstSource firstTarget) (fun _ => child)))
    (eq_of_heq childEq))

/-- Every indexed rule tree is the tree read from its retained event.
Heterogeneous equality states the comparison before transporting the two
endpoint equalities carried by `eventOfTree`. -/
theorem treeOfEvent_eventOfTree :
    ∀ (j : Judgment) (tree : rules.Fix () j),
      HEq (treeOfEvent (eventOfTree j tree).1) tree :=
  IndexedPolynomial.Fix.eliminate rules
    (fun _ j tree => HEq (treeOfEvent (eventOfTree j tree).1) tree)
    (fun base j shape children ih => by
      cases base
      cases shape with
      | beta body arg =>
          have childrenEq : children =
              (fun impossible => impossible.elim) := by
            funext impossible
            exact impossible.elim
          rw [childrenEq]
          rfl
      | appCongL left right arg =>
          let e := (eventOfTree _ (children ())).1
          have hs : source e = left := (eventOfTree _ (children ())).2.1
          have ht : target e = right := (eventOfTree _ (children ())).2.2
          have childEq : HEq (treeOfEvent e) (children ()) := ih ()
          have childrenEq : children = fun _ => children () := by
            funext position
            cases position
            rfl
          rw [childrenEq]
          change HEq
            (treeOfEvent (Event.appCongL arg e))
            (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
              (RuleShape.appCongL left right arg) (fun _ => children ()))
          change HEq
            (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
              (RuleShape.appCongL (source e) (target e) arg)
              (fun _ => treeOfEvent e))
            (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
              (RuleShape.appCongL left right arg) (fun _ => children ()))
          exact appCongL_heq arg hs ht (treeOfEvent e) (children ()) childEq
      | appCongR funTerm left right =>
          let e := (eventOfTree _ (children ())).1
          have hs : source e = left := (eventOfTree _ (children ())).2.1
          have ht : target e = right := (eventOfTree _ (children ())).2.2
          have childEq : HEq (treeOfEvent e) (children ()) := ih ()
          have childrenEq : children = fun _ => children () := by
            funext position
            cases position
            rfl
          rw [childrenEq]
          change HEq
            (treeOfEvent (Event.appCongR funTerm e))
            (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
              (RuleShape.appCongR funTerm left right) (fun _ => children ()))
          change HEq
            (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
              (RuleShape.appCongR funTerm (source e) (target e))
              (fun _ => treeOfEvent e))
            (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
              (RuleShape.appCongR funTerm left right) (fun _ => children ()))
          exact appCongR_heq funTerm hs ht (treeOfEvent e) (children ()) childEq
      | lamCong left right =>
          let e := (eventOfTree _ (children ())).1
          have hs : source e = left := (eventOfTree _ (children ())).2.1
          have ht : target e = right := (eventOfTree _ (children ())).2.2
          have childEq : HEq (treeOfEvent e) (children ()) := ih ()
          have childrenEq : children = fun _ => children () := by
            funext position
            cases position
            rfl
          rw [childrenEq]
          change HEq
            (treeOfEvent (Event.lamCong e))
            (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
              (RuleShape.lamCong left right) (fun _ => children ()))
          change HEq
            (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
              (RuleShape.lamCong (source e) (target e))
              (fun _ => treeOfEvent e))
            (IndexedPolynomial.Fix.roll (polynomial := rules) (base := ())
              (RuleShape.lamCong left right) (fun _ => children ()))
          exact lamCong_heq hs ht (treeOfEvent e) (children ()) childEq) ()

/-- All indexed rule trees in one context, with their exact endpoint
indices retained. -/
abbrev PackedTree (Γ : Ctx sig) :=
  Σ left : Term sig Γ .term,
    Σ right : Term sig Γ .term, Derivation left right

def packTree {Γ : Ctx sig} (event : Event Γ) : PackedTree Γ :=
  ⟨source event, target event, treeOfEvent event⟩

noncomputable def unpackTree {Γ : Ctx sig} (packed : PackedTree Γ) :
    Event Γ :=
  (eventOfTree (judgment packed.1 packed.2.1) packed.2.2).1

theorem unpack_pack {Γ : Ctx sig} (event : Event Γ) :
    unpackTree (packTree event) = event :=
  eventOfTree_treeOfEvent event

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

theorem pack_unpack {Γ : Ctx sig} (packed : PackedTree Γ) :
    packTree (unpackTree packed) = packed := by
  rcases packed with ⟨left, right, tree⟩
  let e := (eventOfTree (judgment left right) tree).1
  have hs : source e = left :=
    (eventOfTree (judgment left right) tree).2.1
  have ht : target e = right :=
    (eventOfTree (judgment left right) tree).2.2
  have htree : HEq (treeOfEvent e) tree :=
    treeOfEvent_eventOfTree (judgment left right) tree
  change (⟨source e, target e, treeOfEvent e⟩ : PackedTree Γ) =
    ⟨left, right, tree⟩
  exact packed_eq_of_components hs ht htree

/-- The presheaf's retained events are exactly the total space of the
indexed polynomial's rule trees at the same raw source and target terms. -/
noncomputable def eventTreeEquiv (Γ : Ctx sig) :
    Event Γ ≃ PackedTree Γ where
  toFun := packTree
  invFun := unpackTree
  left_inv := unpack_pack
  right_inv := pack_unpack

/-- Transport a complete indexed rule tree along a simultaneous
substitution through the proved event equivalence. This action retains the
chosen constructor and every recursive premise. -/
noncomputable def packedMap {Γ Δ : Ctx sig}
    (σ : Sub sig Γ Δ) (packed : PackedTree Γ) : PackedTree Δ :=
  packTree (LambdaDerivationGraph.map σ (unpackTree packed))

theorem packedMap_source {Γ Δ : Ctx sig}
    (σ : Sub sig Γ Δ) (packed : PackedTree Γ) :
    (packedMap σ packed).1 = bind σ packed.1 := by
  have hsource : source (unpackTree packed) = packed.1 :=
    congrArg Sigma.fst (pack_unpack packed)
  simp only [packedMap, packTree, LambdaDerivationGraph.source_map]
  rw [hsource]

theorem packedMap_target {Γ Δ : Ctx sig}
    (σ : Sub sig Γ Δ) (packed : PackedTree Γ) :
    (packedMap σ packed).2.1 = bind σ packed.2.1 := by
  have htarget : target (unpackTree packed) = packed.2.1 := by
    exact congrArg (fun tree : PackedTree Γ => tree.2.1)
      (pack_unpack packed)
  simp only [packedMap, packTree, LambdaDerivationGraph.target_map]
  rw [htarget]

theorem packedMap_id {Γ : Ctx sig} (packed : PackedTree Γ) :
    packedMap (fun _ v => Term.var v) packed = packed := by
  unfold packedMap
  rw [LambdaDerivationGraph.map_id]
  exact pack_unpack packed

theorem packedMap_comp {Γ Δ Θ : Ctx sig}
    (σ : Sub sig Γ Δ) (τ : Sub sig Δ Θ) (packed : PackedTree Γ) :
    packedMap τ (packedMap σ packed) =
      packedMap (fun sort v => bind τ (σ sort v)) packed := by
  unfold packedMap
  rw [unpack_pack]
  rw [LambdaDerivationGraph.map_comp]

/-- The total space of indexed rule trees varies functorially with ambient
substitution. -/
noncomputable def packedPresheaf : Base ⥤ Type where
  obj X := PackedTree X.unop.vars
  map f := TypeCat.ofHom (packedMap f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro packed
    exact packedMap_id packed
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro packed
    exact (packedMap_comp f.unop g.unop packed).symm

/-- Retained lambda events and the total space of indexed rule trees are
isomorphic as presheaves, so their complete firing evidence has the same
substitution behavior in every ambient context. -/
noncomputable def eventTreePresheafIso :
    LambdaDerivationGraph.eventPresheaf ≅ packedPresheaf where
  hom :=
    { app := fun _ => TypeCat.ofHom packTree
      naturality := by
        intro X Y f
        apply ConcreteCategory.hom_ext
        intro event
        change packTree (LambdaDerivationGraph.map f.unop event) =
          packedMap f.unop (packTree event)
        simp only [packedMap]
        rw [unpack_pack event] }
  inv :=
    { app := fun _ => TypeCat.ofHom unpackTree
      naturality := by
        intro X Y f
        apply ConcreteCategory.hom_ext
        intro packed
        change unpackTree (packedMap f.unop packed) =
          LambdaDerivationGraph.map f.unop (unpackTree packed)
        simp only [packedMap]
        exact unpack_pack _ }
  hom_inv_id := by
    ext X event
    exact unpack_pack event
  inv_hom_id := by
    ext X packed
    exact pack_unpack packed

/-- The indexed rule trees form an event graph over the original program
presheaf. Its endpoint maps are transported along the checked event-tree
isomorphism, rather than inferred from mere event existence. -/
noncomputable def packedGraph :
    FreePresheafEventExtension.Graph Programs where
  edge := packedPresheaf
  source := eventTreePresheafIso.inv ≫ LambdaDerivationGraph.sourceNatural
  target := eventTreePresheafIso.inv ≫ LambdaDerivationGraph.targetNatural

/-- The two Chapter 7 presentations are isomorphic as proof-relevant
graphs over programs, including both endpoint maps. -/
noncomputable def eventTreeGraphIso :
    LambdaDerivationGraph.graph ≅ packedGraph where
  hom :=
    { edgeMap := eventTreePresheafIso.hom
      source_comm := by
        dsimp [packedGraph, LambdaDerivationGraph.graph]
        simp
      target_comm := by
        dsimp [packedGraph, LambdaDerivationGraph.graph]
        simp }
  inv :=
    { edgeMap := eventTreePresheafIso.inv
      source_comm := rfl
      target_comm := rfl }
  hom_inv_id := by
    apply FreePresheafEventExtension.Hom.ext
    exact eventTreePresheafIso.hom_inv_id
  inv_hom_id := by
    apply FreePresheafEventExtension.Hom.ext
    exact eventTreePresheafIso.inv_hom_id

/-- Read the ordered constructor history directly from a retained event. -/
def eventHistory : {Γ : Ctx sig} → Event Γ → List RuleTag
  | _, .beta _ _ => [.beta]
  | _, .appCongL _ premise => .appCongL :: eventHistory premise
  | _, .appCongR _ premise => .appCongR :: eventHistory premise
  | _, .lamCong premise => .lamCong :: eventHistory premise

/-- The indexed polynomial's canonical history fold agrees with the direct
reading of the event, for every context and every derivation. -/
theorem history_treeOfEvent :
    ∀ {Γ : Ctx sig} (event : Event Γ),
      history (treeOfEvent event) = eventHistory event
  | _, .beta _ _ => rfl
  | _, .appCongL _ premise => by
      change RuleTag.appCongL :: history (treeOfEvent premise) =
        RuleTag.appCongL :: eventHistory premise
      rw [history_treeOfEvent premise]
  | _, .appCongR _ premise => by
      change RuleTag.appCongR :: history (treeOfEvent premise) =
        RuleTag.appCongR :: eventHistory premise
      rw [history_treeOfEvent premise]
  | _, .lamCong premise => by
      change RuleTag.lamCong :: history (treeOfEvent premise) =
        RuleTag.lamCong :: eventHistory premise
      rw [history_treeOfEvent premise]

theorem eventHistory_map :
    ∀ {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ) (event : Event Γ),
      eventHistory (LambdaDerivationGraph.map σ event) =
        eventHistory event
  | _, _, _, .beta _ _ => rfl
  | _, _, σ, .appCongL _ premise => by
      change RuleTag.appCongL ::
          eventHistory (LambdaDerivationGraph.map σ premise) =
        RuleTag.appCongL :: eventHistory premise
      rw [eventHistory_map σ premise]
  | _, _, σ, .appCongR _ premise => by
      change RuleTag.appCongR ::
          eventHistory (LambdaDerivationGraph.map σ premise) =
        RuleTag.appCongR :: eventHistory premise
      rw [eventHistory_map σ premise]
  | _, _, σ, .lamCong premise => by
      change RuleTag.lamCong ::
          eventHistory (LambdaDerivationGraph.map (liftSub σ [.term]) premise) =
        RuleTag.lamCong :: eventHistory premise
      rw [eventHistory_map (liftSub σ [.term]) premise]

/-- The substitution action on packed rule trees preserves the whole
ordered history, including firing information below binders. -/
theorem history_packedMap {Γ Δ : Ctx sig}
    (σ : Sub sig Γ Δ) (packed : PackedTree Γ) :
    history (packedMap σ packed).2.2 = history packed.2.2 := by
  have h := congrArg (fun tree : PackedTree Γ => history tree.2.2)
    (pack_unpack packed)
  change history
    (treeOfEvent (LambdaDerivationGraph.map σ (unpackTree packed))) =
      history packed.2.2
  rw [history_treeOfEvent, eventHistory_map]
  rw [← history_treeOfEvent (unpackTree packed)]
  exact h

/-- The named open beta and closed LamCong examples are the same firings
in both proof-relevant presentations. -/
theorem open_beta_comparison :
    treeOfEvent LambdaDerivationGraph.openBetaEvent = openBetaTree := rfl

theorem closed_lam_comparison :
    treeOfEvent LambdaDerivationGraph.closedLamEvent = closedLamTree := rfl

/-- Equal endpoints do not identify distinct indexed firing trees. -/
theorem omega_packed_trees_distinct :
    packTree LambdaDerivationGraph.leftOmegaEvent ≠
      packTree LambdaDerivationGraph.rightOmegaEvent := by
  intro equality
  have eventsEqual := congrArg unpackTree equality
  rw [unpack_pack, unpack_pack] at eventsEqual
  exact LambdaDerivationGraph.omega_events_distinct eventsEqual

#print axioms treeOfEvent
#print axioms eventOfTree
#print axioms eventOfTree_treeOfEvent
#print axioms treeOfEvent_eventOfTree
#print axioms eventTreeEquiv
#print axioms packedMap_id
#print axioms packedMap_comp
#print axioms eventTreePresheafIso
#print axioms eventTreeGraphIso
#print axioms history_treeOfEvent
#print axioms history_packedMap
#print axioms omega_packed_trees_distinct

end Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial
