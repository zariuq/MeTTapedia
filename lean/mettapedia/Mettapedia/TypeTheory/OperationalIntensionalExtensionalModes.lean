import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Logic.Relation

/-!
# A mode theory for the operational / intensional / extensional triangle

Multimodal type theory is parametrized by a *mode theory*: a 2-category of
modes, modalities, and transformations.  This module builds the mode theory
of the operational/intensional/extensional triangle **semantically**, as
three concrete categories with the connecting functors and the laws that the
modalities must satisfy — a non-degenerate model in `Cat` of the mode
2-category, which is exactly the input the syntactic type theory consumes.
No modal syntax (context locks, modal types) is claimed here; that is a
separate, later obligation.

The three modes and six generating modalities:

* **operational** — `DynSys`: types with a raw step relation (no reflexivity
  assumed);
* **intensional** — `RouteType`: types with a reflexive *route* relation
  (evidence structure retained);
* **extensional** — `ExtType`: bare carriers, the readout pole (trivially
  the category of types).

```
      DynSys  ── evidenceCompletion ──►  RouteType ── routeQuotient ──► ExtType
        ▲  ◄──── forgetReflexivity ────     ▲ │ ▲
        │                                   │ │ └── discreteOn ◄── ExtType
   dynQuotient ─────────────────────────────┼─┼──────────────────► ExtType
                                            │ └──── pointsOf ────► ExtType
```

The proved mode-theory laws:

* `operationalEvidence : evidenceCompletion ⊣ forgetReflexivity` — the
  intensional mode is the *free* evidence completion of raw dynamics;
* `extensionalReadout : routeQuotient ⊣ discreteOn` — the extensional mode
  is the *free* quotient (readout) of the intensional mode;
* `discretePoints : discreteOn ⊣ pointsOf` — with `discreteHomEquiv` and
  `pointsOf_discreteOn` witnessing that the discrete embedding is fully
  faithful: extensional types are the constant-route full subcategory of
  the intensional mode;
* `observationFactors : evidenceCompletion ⋙ routeQuotient ≅ dynQuotient`
  — the commuting triangle: observing dynamics directly agrees with reading
  out its evidence completion.

The non-collapse canaries (the adjunctions are *not* equivalences — which
is the content):

* `shadow_collapses_routes` / `shadow_not_invertible`: the discrete shadow
  of a route-rich object forgets its routes;
* `quotient_not_faithful`: distinct intensional maps become equal after
  extensional readout;
* `cycle_observation_collapses` beside `cycle_evidence_retains_states`:
  a two-state mutual cycle is a single extensional point, while its
  evidence completion keeps both states.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes

open CategoryTheory Relation

universe u

/-! ## The operational mode: raw dynamics -/

/-- An operational object: a carrier with a raw step relation. -/
structure DynSys : Type (u + 1) where
  carrier : Type u
  Step : carrier → carrier → Prop

/-- Step-preserving maps of dynamics. -/
structure DynHom (X Y : DynSys.{u}) : Type u where
  toFun : X.carrier → Y.carrier
  map_step : ∀ {a b}, X.Step a b → Y.Step (toFun a) (toFun b)

theorem DynHom.ext {X Y : DynSys.{u}} {f g : DynHom X Y}
    (h : ∀ a, f.toFun a = g.toFun a) : f = g := by
  obtain ⟨tf, hf⟩ := f
  obtain ⟨tg, hg⟩ := g
  have ht : tf = tg := funext h
  subst ht
  rfl

instance : Category DynSys.{u} where
  Hom := DynHom
  id _ := ⟨id, fun h => h⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun h => g.map_step (f.map_step h)⟩
  id_comp _ := DynHom.ext fun _ => rfl
  comp_id _ := DynHom.ext fun _ => rfl
  assoc _ _ _ := DynHom.ext fun _ => rfl

/-! ## The intensional mode: reflexive routes -/

/-- An intensional object: a carrier with a reflexive route relation —
the evidence structure that survives before any extensional quotient. -/
structure RouteType : Type (u + 1) where
  carrier : Type u
  Route : carrier → carrier → Prop
  route_refl : ∀ a, Route a a

/-- Route-preserving maps. -/
structure RouteHom (X Y : RouteType.{u}) : Type u where
  toFun : X.carrier → Y.carrier
  map_route : ∀ {a b}, X.Route a b → Y.Route (toFun a) (toFun b)

theorem RouteHom.ext {X Y : RouteType.{u}} {f g : RouteHom X Y}
    (h : ∀ a, f.toFun a = g.toFun a) : f = g := by
  obtain ⟨tf, hf⟩ := f
  obtain ⟨tg, hg⟩ := g
  have ht : tf = tg := funext h
  subst ht
  rfl

instance : Category RouteType.{u} where
  Hom := RouteHom
  id _ := ⟨id, fun h => h⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun h => g.map_route (f.map_route h)⟩
  id_comp _ := RouteHom.ext fun _ => rfl
  comp_id _ := RouteHom.ext fun _ => rfl
  assoc _ _ _ := RouteHom.ext fun _ => rfl

/-! ## The extensional mode: bare carriers -/

/-- An extensional object: a bare carrier — the readout pole.  (Trivially
equivalent to the category of types; kept as a wrapper so all three modes
share one hom discipline.) -/
structure ExtType : Type (u + 1) where
  carrier : Type u

/-- Plain functions. -/
structure ExtHom (X Y : ExtType.{u}) : Type u where
  toFun : X.carrier → Y.carrier

theorem ExtHom.ext {X Y : ExtType.{u}} {f g : ExtHom X Y}
    (h : ∀ a, f.toFun a = g.toFun a) : f = g := by
  obtain ⟨tf⟩ := f
  obtain ⟨tg⟩ := g
  have ht : tf = tg := funext h
  subst ht
  rfl

instance : Category ExtType.{u} where
  Hom := ExtHom
  id _ := ⟨id⟩
  comp f g := ⟨g.toFun ∘ f.toFun⟩
  id_comp _ := ExtHom.ext fun _ => rfl
  comp_id _ := ExtHom.ext fun _ => rfl
  assoc _ _ _ := ExtHom.ext fun _ => rfl

/-- Pointwise equality of functions off a quotient, from equality on
representatives.  (Stated with an explicit motive because `Quot.ind`'s
eliminator elaboration cannot infer it in the contexts below.) -/
private theorem quot_fun_ext {α : Type u} {r : α → α → Prop} {β : Type u}
    (f g : Quot r → β) (h : ∀ a, f (Quot.mk r a) = g (Quot.mk r a)) :
    ∀ q, f q = g q :=
  fun q => @Quot.ind α r (fun q => f q = g q) h q

/-! ## Modalities: operational ↔ intensional -/

/-- Free evidence completion: adjoin exactly the reflexive routes that raw
dynamics is missing. -/
def evidenceCompletion : DynSys.{u} ⥤ RouteType.{u} where
  obj X := ⟨X.carrier, ReflGen X.Step, fun _ => .refl⟩
  map f :=
    ⟨f.toFun, fun h =>
      match h with
      | .refl => .refl
      | .single h' => .single (f.map_step h')⟩
  map_id _ := RouteHom.ext fun _ => rfl
  map_comp _ _ := RouteHom.ext fun _ => rfl

/-- Forget which routes were reflexivity: every route structure is in
particular a dynamics. -/
def forgetReflexivity : RouteType.{u} ⥤ DynSys.{u} where
  obj X := ⟨X.carrier, X.Route⟩
  map f := ⟨f.toFun, f.map_route⟩
  map_id _ := DynHom.ext fun _ => rfl
  map_comp _ _ := DynHom.ext fun _ => rfl

/-- The intensional mode is the free evidence completion of the operational
mode. -/
def operationalEvidence : evidenceCompletion.{u} ⊣ forgetReflexivity.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _X Y =>
        { toFun := fun g => ⟨g.toFun, fun h => g.map_route (.single h)⟩
          invFun := fun f =>
            ⟨f.toFun, fun h =>
              match h with
              | .refl => Y.route_refl _
              | .single h' => f.map_step h'⟩
          left_inv := fun _ => RouteHom.ext fun _ => rfl
          right_inv := fun _ => DynHom.ext fun _ => rfl }
      homEquiv_naturality_left_symm := fun _ _ => RouteHom.ext fun _ => rfl
      homEquiv_naturality_right := fun _ _ => DynHom.ext fun _ => rfl }

/-! ## Modalities: intensional ↔ extensional -/

/-- The readout: quotient every intensional object by its routes. -/
def routeQuotient : RouteType.{u} ⥤ ExtType.{u} where
  obj X := ⟨Quot X.Route⟩
  map {X Y} f :=
    ⟨(Quot.map f.toFun (fun _ _ h => f.map_route h) :
        Quot X.Route → Quot Y.Route)⟩
  map_id _ := ExtHom.ext (quot_fun_ext _ _ fun _ => rfl)
  map_comp _ _ := ExtHom.ext (quot_fun_ext _ _ fun _ => rfl)

/-- The discrete embedding: a bare type with only identity routes. -/
def discreteOn : ExtType.{u} ⥤ RouteType.{u} where
  obj B := ⟨B.carrier, Eq, fun _ => rfl⟩
  map f := ⟨f.toFun, fun h => congrArg f.toFun h⟩
  map_id _ := RouteHom.ext fun _ => rfl
  map_comp _ _ := RouteHom.ext fun _ => rfl

/-- The points functor: forget the routes entirely. -/
def pointsOf : RouteType.{u} ⥤ ExtType.{u} where
  obj X := ⟨X.carrier⟩
  map f := ⟨f.toFun⟩
  map_id _ := ExtHom.ext fun _ => rfl
  map_comp _ _ := ExtHom.ext fun _ => rfl

/-- The extensional mode is the free quotient of the intensional mode:
readout is a left adjoint, hence lossy exactly where routes were real. -/
def extensionalReadout : routeQuotient.{u} ⊣ discreteOn.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X B =>
        { toFun := fun k =>
            ⟨k.toFun ∘ Quot.mk _, fun h => congrArg k.toFun (Quot.sound h)⟩
          invFun := fun g =>
            ⟨(Quot.lift g.toFun (fun _ _ h => g.map_route h) :
                Quot X.Route → B.carrier)⟩
          left_inv := fun _ => ExtHom.ext (quot_fun_ext _ _ fun _ => rfl)
          right_inv := fun _ => RouteHom.ext fun _ => rfl }
      homEquiv_naturality_left_symm := fun _ _ =>
        ExtHom.ext (quot_fun_ext _ _ fun _ => rfl)
      homEquiv_naturality_right := fun _ _ => RouteHom.ext fun _ => rfl }

/-- The discrete embedding is right adjoint to readout and left adjoint to
points: the extensional types sit *inside* the intensional mode. -/
def discretePoints : discreteOn.{u} ⊣ pointsOf.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _B Y =>
        { toFun := fun g => ⟨g.toFun⟩
          invFun := fun f =>
            ⟨f.toFun, fun {a _b} h => h ▸ Y.route_refl (f.toFun a)⟩
          left_inv := fun _ => RouteHom.ext fun _ => rfl
          right_inv := fun _ => ExtHom.ext fun _ => rfl }
      homEquiv_naturality_left_symm := fun _ _ => RouteHom.ext fun _ => rfl
      homEquiv_naturality_right := fun _ _ => ExtHom.ext fun _ => rfl }

/-- Full faithfulness of the discrete embedding, explicitly: maps between
discrete objects are exactly the underlying functions.  Extensional types
are the constant-route full subcategory of the intensional mode. -/
def discreteHomEquiv (B B' : ExtType.{u}) :
    (discreteOn.obj B ⟶ discreteOn.obj B') ≃ (B ⟶ B') where
  toFun g := ⟨g.toFun⟩
  invFun f := discreteOn.map f
  left_inv _ := RouteHom.ext fun _ => rfl
  right_inv _ := ExtHom.ext fun _ => rfl

/-- Points recover the discrete embedding on the nose. -/
theorem pointsOf_discreteOn (B : ExtType.{u}) :
    pointsOf.obj (discreteOn.obj B) = B := rfl

/-! ## The commuting triangle -/

/-- Observing dynamics directly: quotient by the raw steps. -/
def dynQuotient : DynSys.{u} ⥤ ExtType.{u} where
  obj X := ⟨Quot X.Step⟩
  map {X Y} f :=
    ⟨(Quot.map f.toFun (fun _ _ h => f.map_step h) :
        Quot X.Step → Quot Y.Step)⟩
  map_id _ := ExtHom.ext (quot_fun_ext _ _ fun _ => rfl)
  map_comp _ _ := ExtHom.ext (quot_fun_ext _ _ fun _ => rfl)

/-- At each dynamics, quotienting the evidence completion agrees with
quotienting the raw steps. -/
def quotEvidenceIso (X : DynSys.{u}) :
    routeQuotient.obj (evidenceCompletion.obj X) ≅ dynQuotient.obj X where
  hom :=
    ⟨(Quot.lift (Quot.mk X.Step)
        (fun a b (h : ReflGen X.Step a b) =>
          match h with
          | .refl => rfl
          | .single h' => Quot.sound h') :
        Quot (ReflGen X.Step) → Quot X.Step)⟩
  inv :=
    ⟨(Quot.map id (fun _ _ h => ReflGen.single h) :
        Quot X.Step → Quot (ReflGen X.Step))⟩
  hom_inv_id := ExtHom.ext (quot_fun_ext _ _ fun _ => rfl)
  inv_hom_id := ExtHom.ext (quot_fun_ext _ _ fun _ => rfl)

/-- The triangle commutes: extensional observation of dynamics factors
through the intensional evidence completion, naturally. -/
def observationFactors :
    evidenceCompletion.{u} ⋙ routeQuotient.{u} ≅ dynQuotient.{u} :=
  NatIso.ofComponents (fun X => quotEvidenceIso X) fun {_X} {_Y} _f =>
    ExtHom.ext (quot_fun_ext _ _ fun _ => rfl)

/-! ## Non-collapse canaries -/

/-- A route-rich object: two points, all routes present. -/
def codiscretePair : RouteType.{0} :=
  ⟨Bool, fun _ _ => True, fun _ => trivial⟩

/-- The extensional pair, as an object of the readout pole. -/
def extBool : ExtType.{0} := ⟨Bool⟩

/-- Any intensional map from the route-rich pair into a discrete object
collapses the two points: the discrete shadow forgets routes. -/
theorem shadow_collapses_routes
    (g : codiscretePair ⟶ discreteOn.obj extBool) :
    g.toFun true = g.toFun false :=
  g.map_route trivial

/-- Consequently the route-rich pair is not isomorphic to any discrete
picture of itself: the counit of `discretePoints` is not invertible. -/
theorem shadow_not_invertible :
    ¬ Nonempty (codiscretePair ≅ discreteOn.obj extBool) := by
  rintro ⟨e⟩
  have hcollapse : e.hom.toFun true = e.hom.toFun false :=
    shadow_collapses_routes e.hom
  have htrue : e.inv.toFun (e.hom.toFun true) = true :=
    congrArg (fun k : RouteHom codiscretePair codiscretePair => k.toFun true)
      e.hom_inv_id
  have hfalse : e.inv.toFun (e.hom.toFun false) = false :=
    congrArg (fun k : RouteHom codiscretePair codiscretePair => k.toFun false)
      e.hom_inv_id
  have : true = false := by rw [← htrue, ← hfalse, hcollapse]
  exact Bool.noConfusion this

/-- Two distinct intensional maps that the extensional readout cannot
distinguish: readout is not faithful. -/
theorem quotient_not_faithful :
    ∃ f g : codiscretePair ⟶ codiscretePair,
      f ≠ g ∧ routeQuotient.map f = routeQuotient.map g := by
  refine ⟨⟨id, fun _ => trivial⟩, ⟨Bool.not, fun _ => trivial⟩, ?_, ?_⟩
  · intro h
    have := congrArg (fun k => RouteHom.toFun k true) h
    exact Bool.noConfusion this
  · exact ExtHom.ext (quot_fun_ext _ _ fun _ => Quot.sound trivial)

/-- The two-state mutual cycle, operationally. -/
def mutualCycle : DynSys.{0} := ⟨Bool, fun a b => a ≠ b⟩

/-- Extensional observation collapses the cycle to a point. -/
theorem cycle_observation_collapses :
    (Quot.mk mutualCycle.Step true) = Quot.mk mutualCycle.Step false :=
  Quot.sound (by simp [mutualCycle])

/-- The evidence completion retains both states of the cycle: intensional
structure survives exactly where the readout collapses. -/
theorem cycle_evidence_retains_states :
    ∃ a b : (evidenceCompletion.obj mutualCycle).carrier, a ≠ b :=
  ⟨true, false, Bool.noConfusion⟩

/-! ## Axiom audit -/

#print axioms operationalEvidence
#print axioms extensionalReadout
#print axioms discretePoints
#print axioms observationFactors
#print axioms shadow_not_invertible
#print axioms quotient_not_faithful
#print axioms cycle_observation_collapses
#print axioms cycle_evidence_retains_states

end Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
