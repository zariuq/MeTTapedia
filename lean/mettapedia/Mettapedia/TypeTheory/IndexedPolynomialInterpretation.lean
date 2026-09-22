import Mettapedia.TypeTheory.IndexedPolynomialFree

/-!
# Substitution-compatible interpretations of indexed plans

A source constructor can be implemented by an entire target plan. Its operation
must commute with filling target holes. This contract extends uniquely to all
source plans, preserves substitution, and composes. A separate algebra law
establishes preservation of reconstructed results.

The polynomials and indexed families here inhabit one universe, so target free
plans remain admissible families for the same interface. Source and target share
their base and goal indices; changes of goal indices require a separate
reindexing construction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial

universe u
variable {Base : Type u} {Index : Base → Type u}
variable (P Q R S : IndexedPolynomial.{u,u,u,u} Base Index)

/-- An operation on target plans that is natural under typed hole substitution.
The law is an implementation obligation, independent of semantic correctness. -/
structure PlanInterpretation where
  act : {H : (b : Base) → Index b → Type u} →
    ∀ b i, P.Extension (Q.Free H) b i → Q.Free H b i
  bind_act : ∀ {H K : (b : Base) → Index b → Type u}
    (fill : ∀ b i, H b i → Q.Free K b i) b i
    (input : P.Extension (Q.Free H) b i),
    Free.bind Q fill b i (act b i input) =
      act b i (Extension.map P (Free.bind Q fill) input)

namespace PlanInterpretation

variable {P Q R S}

def algebra (F : PlanInterpretation P Q)
    (H : (b : Base) → Index b → Type u) : P.Algebra (Q.Free H) where
  act := F.act

/-- Extend constructor implementations to arbitrary source plans. -/
noncomputable def run (F : PlanInterpretation P Q)
    {H : (b : Base) → Index b → Type u} :
    ∀ b i, P.Free H b i → Q.Free H b i :=
  Free.fold P (fun _ _ h => Free.pure Q h) (F.algebra H)

@[simp] theorem run_pure (F : PlanInterpretation P Q)
    {H : (b : Base) → Index b → Type u} {b : Base} {i : Index b} (h : H b i) :
    F.run b i (Free.pure P h) = Free.pure Q h := rfl

@[simp] theorem run_node (F : PlanInterpretation P Q)
    {H : (b : Base) → Index b → Type u} {b : Base} {i : Index b}
    (s : P.Shape b i) (children : ∀ p, P.Free H b (P.next s p)) :
    F.run b i (Free.node P s children) =
      F.act b i ⟨s, fun p => F.run b _ (children p)⟩ := rfl

/-- The extension is uniquely determined by its leaves and method expansions. -/
theorem run_unique (F : PlanInterpretation P Q)
    {H : (b : Base) → Index b → Type u}
    (candidate : ∀ b i, P.Free H b i → Q.Free H b i)
    (leaves : ∀ b i (h : H b i), candidate b i (Free.pure P h) = Free.pure Q h)
    (nodes : ∀ b i (s : P.Shape b i) (c : ∀ p, P.Free H b (P.next s p)),
      candidate b i (Free.node P s c) = F.act b i ⟨s, fun p => candidate b _ (c p)⟩) :
    ∀ b i (t : P.Free H b i), candidate b i t = F.run b i t :=
  Free.fold_unique P _ _ candidate leaves nodes

/-- Interpret a filled proof/work plan, or fill its interpreted holes: same tree. -/
theorem run_bind (F : PlanInterpretation P Q)
    {H K : (b : Base) → Index b → Type u}
    (fill : ∀ b i, H b i → P.Free K b i)
    {b : Base} {i : Index b} (t : P.Free H b i) :
    F.run b i (Free.bind P fill b i t) =
      Free.bind Q (fun b i h => F.run b i (fill b i h)) b i (F.run b i t) := by
  have left := Free.fold_unique P (fun b i h => F.run b i (fill b i h))
    (F.algebra K) (fun b i t => F.run b i (Free.bind P fill b i t))
    (by intros; rfl) (by intros; rfl) b i t
  have right := Free.fold_unique P (fun b i h => F.run b i (fill b i h))
    (F.algebra K) (fun b i t => Free.bind Q
      (fun b i h => F.run b i (fill b i h)) b i (F.run b i t))
    (by intros; rfl) (by
      intro b i s c
      exact F.bind_act _ b i ⟨s, fun p => F.run b _ (c p)⟩) b i t
  exact left.trans right.symm

/-- The extension is natural in the family of outstanding obligations. -/
theorem run_map (F : PlanInterpretation P Q)
    {H K : (b : Base) → Index b → Type u}
    (mapping : ∀ b i, H b i → K b i)
    {b : Base} {i : Index b} (t : P.Free H b i) :
    F.run b i (Free.map P mapping b i t) =
      Free.map Q mapping b i (F.run b i t) := by
  unfold Free.map
  rw [run_bind]
  rfl

/-- The extension preserves flattening: it is a morphism of the free-plan
substitution structures, including plans whose holes already contain plans. -/
theorem run_join (F : PlanInterpretation P Q)
    {H : (b : Base) → Index b → Type u}
    {b : Base} {i : Index b} (t : P.Free (P.Free H) b i) :
    F.run b i (Free.join P t) =
      Free.join Q (Free.map Q F.run b i (F.run b i t)) := by
  unfold Free.join Free.map
  rw [run_bind, Free.bind_assoc]
  rfl

def identity : PlanInterpretation P P where
  act := fun _ _ input => Free.node P input.1 input.2
  bind_act := by intros; rfl

@[simp] theorem run_identity {H : (b : Base) → Index b → Type u}
    {b : Base} {i : Index b} (t : P.Free H b i) :
    (identity (P := P)).run b i t = t := by
  exact (run_unique identity (fun _ _ t => t)
    (by intros; rfl) (by intros; rfl) b i t).symm

/-- Compose expansions, retaining intermediate target nodes through the next map. -/
noncomputable def comp (F : PlanInterpretation P Q) (G : PlanInterpretation Q R) :
    PlanInterpretation P R where
  act := fun b i input => Free.bind R (fun _ _ t => t) b i
    (G.run b i (F.act b i (Extension.map P (fun _ _ t => Free.pure Q t) input)))
  bind_act := by
    intro H K fill b i input
    cases input with
    | mk s c =>
      dsimp only [Extension.map]
      rw [Free.bind_assoc]
      -- Transfer substitution through the first implementation and then G.
      have h := G.run_bind (fun b i (t : R.Free H b i) =>
        Free.pure Q (Free.bind R fill b i t))
        (F.act b i ⟨s, fun p => Free.pure Q (c p)⟩)
      erw [F.bind_act] at h
      simp only [Extension.map, Free.bind_pure] at h
      have h' := congrArg (Free.bind R (fun _ _ t => t) b i) h
      rw [Free.bind_assoc] at h'
      simp only [run_pure, Free.bind_pure] at h'
      exact h'.symm

theorem run_comp (F : PlanInterpretation P Q) (G : PlanInterpretation Q R)
    {H : (b : Base) → Index b → Type u} {b : Base} {i : Index b}
    (t : P.Free H b i) : (F.comp G).run b i t = G.run b i (F.run b i t) := by
  apply Eq.symm
  refine run_unique (F.comp G) (fun b i t => G.run b i (F.run b i t)) ?_ ?_ b i t
  · intros; rfl
  · intro b i s c
    rw [run_node]
    have h := G.run_bind (fun _ _ t => t)
      (F.act b i ⟨s, fun p => Free.pure Q (F.run b _ (c p))⟩)
    erw [F.bind_act] at h
    simp only [Extension.map, Free.bind_pure] at h
    rw [h]
    change _ = Free.bind R (fun _ _ t => t) b i
      (G.run b i (F.act b i ⟨s, fun p => Free.pure Q (G.run b _ (F.run b _ (c p)))⟩))
    have k := G.run_bind (fun b i t => Free.pure Q (G.run b i t))
      (F.act b i ⟨s, fun p => Free.pure Q (F.run b _ (c p))⟩)
    erw [F.bind_act] at k
    simp only [Extension.map, Free.bind_pure] at k
    rw [k, Free.bind_assoc]
    simp only [run_pure, Free.bind_pure]

/-- Proof irrelevance leaves the constructor operation as the extensional data. -/
theorem ext_act (F G : PlanInterpretation P Q) (same : @F.act = @G.act) : F = G := by
  cases F
  cases G
  cases same
  rfl

/-- Equality is determined by the extension on plans, since single-node plans
with plan-valued holes recover every constructor implementation. -/
theorem ext_run (F G : PlanInterpretation P Q)
    (same : ∀ (H : (b : Base) → Index b → Type u) b i (t : P.Free H b i),
      F.run b i t = G.run b i t) : F = G := by
  have acts : @F.act = @G.act := by
    funext H b i input
    cases input with
    | mk s c =>
      have h := same (Q.Free H) b i (Free.node P s (fun p => Free.pure P (c p)))
      have k := congrArg (Free.bind Q (fun _ _ t => t) b i) h
      simp only [run_node, run_pure] at k
      erw [F.bind_act, G.bind_act] at k
      simpa only [Extension.map, Free.bind_pure] using k
  cases F
  cases G
  cases acts
  rfl

@[simp] theorem identity_comp (F : PlanInterpretation P Q) : identity.comp F = F := by
  apply ext_run
  intro H b i t
  rw [run_comp, run_identity]

@[simp] theorem comp_identity (F : PlanInterpretation P Q) : F.comp identity = F := by
  apply ext_run
  intro H b i t
  rw [run_comp, run_identity]

theorem comp_assoc (F : PlanInterpretation P Q) (G : PlanInterpretation Q R)
    (J : PlanInterpretation R S) : (F.comp G).comp J = F.comp (G.comp J) := by
  apply ext_run
  intro H b i t
  simp only [run_comp]

/-- Local preservation at each expanded method suffices for reconstruction of
the whole interpreted plan. The source and target result families may differ. -/
theorem reconstruct
    (F : PlanInterpretation P Q)
    {H A B : (b : Base) → Index b → Type u}
    (source : P.Algebra A) (target : Q.Algebra B)
    (resultMap : ∀ b i, A b i → B b i)
    (sourceHole : ∀ b i, H b i → A b i)
    (targetHole : ∀ b i, H b i → B b i)
    (holesAgree : ∀ b i h, targetHole b i h = resultMap b i (sourceHole b i h))
    (methodsAgree : ∀ b i (s : P.Shape b i)
      (values : ∀ p, A b (P.next s p))
      (plans : ∀ p, Q.Free H b (P.next s p)),
      (∀ p, Free.fold Q targetHole target b _ (plans p) = resultMap b _ (values p)) →
      Free.fold Q targetHole target b i (F.act b i ⟨s, plans⟩) =
        resultMap b i (source.act b i ⟨s, values⟩))
    {b : Base} {i : Index b} (t : P.Free H b i) :
    Free.fold Q targetHole target b i (F.run b i t) =
      resultMap b i (Free.fold P sourceHole source b i t) := by
  induction t with
  | roll shape children ih =>
      cases shape with
      | inl hole => exact holesAgree b _ hole
      | inr shape =>
          dsimp only [withHoles] at children ih
          exact methodsAgree b _ shape
            (fun p => Free.fold P sourceHole source b _ (children p))
            (fun p => F.run b _ (children p)) ih

#print axioms run_bind
#print axioms run_join
#print axioms run_comp
#print axioms comp_assoc
#print axioms reconstruct

end PlanInterpretation

/-- Typed names for exactly the source constructor's recursive positions. A
position may be used only at its original base and child index. -/
def MethodHoles {b : Base} {i : Index b} (s : P.Shape b i)
    (b' : Base) (i' : Index b') : Type u :=
  {p : P.Position s // (⟨b', i'⟩ : Sigma Index) = ⟨b, P.next s p⟩}

/-- A concrete target plan whose holes name source children. Such a template
may contain several target methods rather than only one target constructor. -/
abbrev MethodTemplates := ∀ b i (s : P.Shape b i), Q.Free (MethodHoles P s) b i

namespace MethodTemplates

variable {P Q}

def fillPositions {H : (b : Base) → Index b → Type u}
    {b : Base} {i : Index b} {s : P.Shape b i}
    (children : ∀ p, Q.Free H b (P.next s p)) :
    ∀ b' i', MethodHoles P s b' i' → Q.Free H b' i' :=
  fun _ _ hole => cast
    (congrArg (fun x : Sigma Index => Q.Free H x.1 x.2) hole.2.symm)
    (children hole.1)

theorem fillPositions_bind {H K : (b : Base) → Index b → Type u}
    (fill : ∀ b i, H b i → Q.Free K b i)
    {b : Base} {i : Index b} {s : P.Shape b i}
    (children : ∀ p, Q.Free H b (P.next s p))
    (b' : Base) (i' : Index b') (hole : MethodHoles P s b' i') :
    Free.bind Q fill b' i' (fillPositions children b' i' hole) =
      fillPositions (fun p => Free.bind Q fill b _ (children p)) b' i' hole := by
  rcases hole with ⟨p, e⟩
  cases e
  rfl

/-- Template expansion satisfies substitution from the free-plan monad laws;
no substitution-preservation proof is demanded from a template author. -/
noncomputable def interpretation (templates : MethodTemplates P Q) :
    PlanInterpretation P Q where
  act := fun b i input => Free.bind Q (fillPositions input.2) b i
    (templates b i input.1)
  bind_act := by
    intro H K fill b i input
    rcases input with ⟨s, children⟩
    rw [Free.bind_assoc]
    congr 1
    funext b' i' hole
    exact fillPositions_bind fill children b' i' hole

/-- Recover the explicit method template of every lawful interpretation. -/
def ofInterpretation (F : PlanInterpretation P Q) : MethodTemplates P Q :=
  fun b i s => F.act b i ⟨s, fun p => Free.pure Q ⟨p, rfl⟩⟩

/-- The template construction covers every substitution-compatible operation. -/
@[simp] theorem interpretation_ofInterpretation (F : PlanInterpretation P Q) :
    interpretation (ofInterpretation F) = F := by
  have h : @(interpretation (ofInterpretation F)).act = @F.act := by
    funext H b i input
    rcases input with ⟨s, children⟩
    change Free.bind Q (fillPositions children) b i
      (F.act b i ⟨s, fun p => Free.pure Q ⟨p, rfl⟩⟩) = F.act b i ⟨s, children⟩
    erw [F.bind_act]
    rfl
  exact PlanInterpretation.ext_act _ _ h

@[simp] theorem ofInterpretation_interpretation (templates : MethodTemplates P Q) :
    ofInterpretation (interpretation templates) = templates := by
  funext b i s
  change Free.bind Q
    (fillPositions (fun p => Free.pure Q (⟨p, rfl⟩ : MethodHoles P s b (P.next s p))))
    b i (templates b i s) = templates b i s
  have h : fillPositions (Q := Q)
      (fun p => Free.pure Q (⟨p, rfl⟩ : MethodHoles P s b (P.next s p))) =
      (fun b' i' (hole : MethodHoles P s b' i') => Free.pure Q hole) := by
    funext b' i' hole
    rcases hole with ⟨p, e⟩
    cases e
    rfl
  rw [h, Free.bind_pure_right]

/-- Explicit composite templates are exactly the substitution-compatible
constructor operations, rather than a merely sufficient implementation trick. -/
noncomputable def equivInterpretation : MethodTemplates P Q ≃ PlanInterpretation P Q where
  toFun := interpretation
  invFun := ofInterpretation
  left_inv := ofInterpretation_interpretation
  right_inv := interpretation_ofInterpretation

end MethodTemplates

#print axioms MethodTemplates.interpretation_ofInterpretation
#print axioms MethodTemplates.equivInterpretation
end Mettapedia.TypeTheory.IndexedPolynomial
