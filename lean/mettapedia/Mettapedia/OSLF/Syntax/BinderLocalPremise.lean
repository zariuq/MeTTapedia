import Mettapedia.OSLF.Syntax.LambdaContextualRung

/-!
# Context-indexed premises for reductions below binders

A conditional operational rule may ask whether two terms step in a context
extended by binders introduced for that premise. The extension is part of the
premise data, not inferred from an occurrence's first location. Transport of
ambient variables lifts under precisely those binders. This is the semantic
carrier required by the lambda LamCong rule; compiling it from the canonical
authored `Premise` and executing it remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BinderLocalPremise

open CategoryTheory

variable {S : Signature}

/-- One premise whose two endpoints have the same sort and the same explicitly
opened binder context. -/
structure LocalStepPremise (S : Signature) (Γ : Ctx S) where
  binders : Ctx S
  sort : S.Srt
  source : Term S (binders ++ Γ) sort
  target : Term S (binders ++ Γ) sort

/-- The old, binder-free premise is the zero-extension case. -/
def LocalStepPremise.root {Γ : Ctx S} {sort : S.Srt}
    (source target : Term S Γ sort) : LocalStepPremise S Γ where
  binders := []
  sort := sort
  source := source
  target := target

/-- Transport an open premise along an ambient substitution, leaving its
locally bound variables fixed. -/
def LocalStepPremise.map {Γ Δ : Ctx S} (sigma : Sub S Γ Δ)
    (premise : LocalStepPremise S Γ) : LocalStepPremise S Δ where
  binders := premise.binders
  sort := premise.sort
  source := bind (liftSub sigma premise.binders) premise.source
  target := bind (liftSub sigma premise.binders) premise.target

private theorem liftSub_identity {Γ : Ctx S} :
    ∀ binders : Ctx S,
      liftSub (fun _ v => Term.var v : Sub S Γ Γ) binders =
        (fun _ v => Term.var v)
  | [] => rfl
  | _ :: binders => by
      funext sort v
      cases v with
      | zero => rfl
      | succ old =>
          simp only [liftSub, liftSub_identity binders, weaken, rename]

/-- The empty change of ambient context preserves the entire premise. -/
theorem LocalStepPremise.map_id {Γ : Ctx S}
    (premise : LocalStepPremise S Γ) :
    premise.map (fun _ v => Term.var v) = premise := by
  cases premise with
  | mk binders sort source target =>
      simp only [LocalStepPremise.map, liftSub_identity,
        bind_id]

/-- Premise transport composes, including both endpoints below its binders. -/
theorem LocalStepPremise.map_comp {Γ Δ Θ : Ctx S}
    (sigma : Sub S Γ Δ) (tau : Sub S Δ Θ)
    (premise : LocalStepPremise S Γ) :
    (premise.map sigma).map tau =
      premise.map (fun sort v => bind tau (sigma sort v)) := by
  cases premise with
  | mk binders sort source target =>
      simp only [LocalStepPremise.map, bind_comp,
        liftSub_comp sigma tau binders]

@[simp] theorem LocalStepPremise.map_binders {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) (premise : LocalStepPremise S Γ) :
    (premise.map sigma).binders = premise.binders := rfl

@[simp] theorem LocalStepPremise.map_sort {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) (premise : LocalStepPremise S Γ) :
    (premise.map sigma).sort = premise.sort := rfl

/-- A context-indexed relation is stable under every sorted substitution.
This is a genuine semantic property; the lambda instance is proved below. -/
def SubstitutionStable
    (R : (Γ : Ctx S) → (sort : S.Srt) →
      Term S Γ sort → Term S Γ sort → Prop) : Prop :=
  ∀ {Γ Δ : Ctx S} {sort : S.Srt}
    (sigma : Sub S Γ Δ) {source target : Term S Γ sort},
    R Γ sort source target →
      R Δ sort (bind sigma source) (bind sigma target)

/-- The premise reads the relation in its opened context. -/
def Holds
    (R : (Γ : Ctx S) → (sort : S.Srt) →
      Term S Γ sort → Term S Γ sort → Prop)
    {Γ : Ctx S} (premise : LocalStepPremise S Γ) : Prop :=
  R (premise.binders ++ Γ) premise.sort premise.source premise.target

/-- The root embedding preserves precisely the old relation judgment. -/
theorem holds_root_iff
    (R : (Γ : Ctx S) → (sort : S.Srt) →
      Term S Γ sort → Term S Γ sort → Prop)
    {Γ : Ctx S} {sort : S.Srt}
    (source target : Term S Γ sort) :
    Holds R (LocalStepPremise.root source target) ↔
      R Γ sort source target := Iff.rfl

/-- The root embedding commutes with ambient substitution. -/
theorem LocalStepPremise.root_map {Γ Δ : Ctx S} {sort : S.Srt}
    (sigma : Sub S Γ Δ) (source target : Term S Γ sort) :
    (LocalStepPremise.root source target).map sigma =
      LocalStepPremise.root (bind sigma source) (bind sigma target) := rfl

/-- Binder-local premise data form a presheaf on the syntactic context
category. Its action is the proved simultaneous-substitution action above. -/
def premisePresheaf (S : Signature) : (Syntactic.Ctxt S)ᵒᵖ ⥤ Type where
  obj X := LocalStepPremise S X.unop.vars
  map f := TypeCat.ofHom (LocalStepPremise.map f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro premise
    exact LocalStepPremise.map_id premise
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro premise
    exact (LocalStepPremise.map_comp f.unop g.unop premise).symm

/-- The ordinary relation's source/target pairs are the zero-binder fibre. -/
def rootPairs (S : Signature) (Γ : Ctx S) : Type :=
  Σ sort : S.Srt, Term S Γ sort × Term S Γ sort

/-- Root pairs reindex by simultaneous substitution. -/
def rootPairsMap {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) :
    rootPairs S Γ → rootPairs S Δ
  | ⟨sort, source, target⟩ =>
      ⟨sort, bind sigma source, bind sigma target⟩

theorem rootPairsMap_id {Γ : Ctx S} (pair : rootPairs S Γ) :
    rootPairsMap (fun _ v => Term.var v) pair = pair := by
  rcases pair with ⟨sort, ⟨source, target⟩⟩
  simp only [rootPairsMap, bind_id]
  rfl

theorem rootPairsMap_comp {Γ Δ Θ : Ctx S}
    (sigma : Sub S Γ Δ) (tau : Sub S Δ Θ)
    (pair : rootPairs S Γ) :
    rootPairsMap tau (rootPairsMap sigma pair) =
      rootPairsMap (fun sort v => bind tau (sigma sort v)) pair := by
  rcases pair with ⟨sort, ⟨source, target⟩⟩
  simp only [rootPairsMap, bind_comp]
  rfl

def rootPairsPresheaf (S : Signature) : (Syntactic.Ctxt S)ᵒᵖ ⥤ Type where
  obj X := rootPairs S X.unop.vars
  map f := TypeCat.ofHom (rootPairsMap f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro pair
    exact rootPairsMap_id pair
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro pair
    exact (rootPairsMap_comp f.unop g.unop pair).symm

/-- The old root-premise carrier embeds naturally in the binder-local one;
its zero-binder component is retained by every context substitution. -/
def rootInclusion (S : Signature) :
    rootPairsPresheaf S ⟶ premisePresheaf S where
  app X := TypeCat.ofHom (fun pair =>
    LocalStepPremise.root pair.2.1 pair.2.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro pair
    rcases pair with ⟨sort, ⟨source, target⟩⟩
    exact LocalStepPremise.root_map f.unop source target

/-- The zero-binder component retains its sort and both endpoints exactly. -/
theorem root_inclusion_injective {Γ : Ctx S} :
    Function.Injective
      (fun pair : rootPairs S Γ =>
        (LocalStepPremise.root pair.2.1 pair.2.2 : LocalStepPremise S Γ)) := by
  intro first second equality
  rcases first with ⟨firstSort, ⟨firstSource, firstTarget⟩⟩
  rcases second with ⟨secondSort, ⟨secondSource, secondTarget⟩⟩
  cases equality
  rfl

/-- Substitution-stable relations preserve binder-local premise evidence.
The extension context in the conclusion is exactly the one in the premise. -/
theorem holds_map
    {R : (Γ : Ctx S) → (sort : S.Srt) →
      Term S Γ sort → Term S Γ sort → Prop}
    (stable : SubstitutionStable R) {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) (premise : LocalStepPremise S Γ)
    (holds : Holds R premise) : Holds R (premise.map sigma) := by
  exact stable (liftSub sigma premise.binders) holds

namespace Lambda

open Mettapedia.OSLF.Binding.LambdaContextualRung

/-- The context-indexed, one-sorted lambda reduction as a sorted relation. -/
def relation (Γ : Ctx sig) (sort : Srt)
    (source target : Term sig Γ sort) : Prop :=
  match sort with
  | .term => LambdaContextualRung.Step Γ source target

/-- The proved lambda substitution theorem discharges the semantic premise
transport requirement, including the case under a newly opened binder. -/
theorem relation_stable : SubstitutionStable relation := by
  intro Γ Δ sort sigma source target reduction
  cases sort with
  | term => exact LambdaContextualRung.substitute sigma reduction

/-- The source LamCong premise has one local binder. -/
def lamCongPremise {Γ : Ctx sig}
    (source target : Term sig (Srt.term :: Γ) .term) :
    LocalStepPremise sig Γ where
  binders := [.term]
  sort := .term
  source := source
  target := target

/-- The open beta witness from the lambda rung is a genuine binder-local
premise, although its enclosing conclusion is closed. -/
theorem open_beta_holds :
    Holds relation
      (lamCongPremise (Γ := [])
        (appT (lamT (.var .zero)) (.var .zero))
        (.var .zero)) :=
  LambdaContextualRung.open_beta_uses_bound_variable

/-- The binder-local premise is genuinely new data, not an alias for an old
root pair: its extension context is nonempty. -/
theorem open_beta_not_root_premise :
    ¬ ∃ pair : rootPairs sig [],
      LocalStepPremise.root pair.2.1 pair.2.2 =
        lamCongPremise (Γ := [])
          (appT (lamT (.var .zero)) (.var .zero))
          (.var .zero) := by
  rintro ⟨pair, equality⟩
  have binders := congrArg LocalStepPremise.binders equality
  cases binders

/-- Every supplied binder-local lambda step supports the displayed LamCong
conclusion. This is the semantic rule to which authoring must compile. -/
theorem lamCong_of_holds {Γ : Ctx sig}
    {source target : Term sig (.term :: Γ) .term}
    (holds : Holds relation (lamCongPremise source target)) :
    LambdaContextualRung.Step Γ (lamT source) (lamT target) :=
  LambdaContextualRung.Step.lamCong holds

end Lambda

end Mettapedia.OSLF.Binding.BinderLocalPremise
