import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveRegularity

/-!
# Finite requirements of formation-sensitive derivations

Every finite derivation uses finitely many atomic obligations from its rule
package. These include the formation derivations of declarations and contexts,
and every root/head equation along conversion paths, not just names appearing
in the displayed term and type. Replaying these obligations reconstructs the
judgment in another package on the same syntax.

This theorem concerns the existing dependent calculus with varying rule
packages. It is not an STT inhabitation-reflection theorem, an executable
minimal-kernel finder, or qualification of arbitrary computation rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive.Dependencies

variable {Head : Type} {n : Nat}

/-- Atomic rule-package queries, with the exact queried data retained. -/
inductive Requirement (Head : Type) where
  | headTyping : Head → Head → Requirement Head
  | isUniverse : Head → Requirement Head
  | join : Head → Head → Head → Requirement Head
  | cumulative : Head → Head → Requirement Head
  | headEq : Head → Head → Requirement Head
  | constantType : DeclName → Tm Head 0 → Requirement Head
  | rootStep (n : Nat) : Tm Head n → Tm Head n → Requirement Head

def Requirement.Holds (R : Rules Head) : Requirement Head → Prop
  | .headTyping h u => R.headTyping h u
  | .isUniverse u => R.isUniverse u
  | .join u v w => R.join u v w
  | .cumulative u v => R.cumulative u v
  | .headEq h k => R.headEq h k
  | .constantType name type => R.constantType name = some type
  | .rootStep _ left right => R.computation.step left right

def HoldsAll (R : Rules Head) (requirements : List (Requirement Head)) : Prop :=
  ∀ requirement ∈ requirements, requirement.Holds R

@[simp] theorem holdsAll_nil (R : Rules Head) : HoldsAll R [] := by
  intro requirement impossible
  cases impossible

@[simp] theorem holdsAll_cons (R : Rules Head) (q : Requirement Head)
    (qs : List (Requirement Head)) :
    HoldsAll R (q :: qs) ↔ q.Holds R ∧ HoldsAll R qs := by
  simp only [HoldsAll, List.mem_cons, forall_eq_or_imp]

@[simp] theorem holdsAll_append (R : Rules Head) (left right : List (Requirement Head)) :
    HoldsAll R (left ++ right) ↔ HoldsAll R left ∧ HoldsAll R right := by
  constructor
  · intro valid
    exact ⟨fun q member => valid q (List.mem_append_left _ member),
      fun q member => valid q (List.mem_append_right _ member)⟩
  · rintro ⟨leftValid, rightValid⟩ q member
    rcases List.mem_append.mp member with member | member
    · exact leftValid q member
    · exact rightValid q member

/-- A finite list of primitive obligations suffices to reconstruct a claim
in every package satisfying that list. The claim is not itself a requirement. -/
def Supported (R : Rules Head) (claim : Rules Head → Prop) : Prop :=
  ∃ requirements : List (Requirement Head), HoldsAll R requirements ∧
    ∀ target : Rules Head, HoldsAll target requirements → claim target

namespace Supported

variable {R : Rules Head} {P Q : Rules Head → Prop}

theorem uniform (proved : ∀ target, P target) : Supported R P :=
  ⟨[], holdsAll_nil _, fun target _ => proved target⟩

theorem atom (requirement : Requirement Head) (valid : requirement.Holds R) :
    Supported R (fun target => requirement.Holds target) := by
  refine ⟨[requirement], ?_, ?_⟩
  · simpa only [holdsAll_cons, holdsAll_nil, and_true] using valid
  · intro target validated
    exact validated requirement (by simp)

theorem map (supported : Supported R P) (reconstruct : ∀ target, P target → Q target) :
    Supported R Q := by
  obtain ⟨requirements, valid, replay⟩ := supported
  exact ⟨requirements, valid, fun target checked => reconstruct target (replay target checked)⟩

theorem and (left : Supported R P) (right : Supported R Q) :
    Supported R (fun target => P target ∧ Q target) := by
  obtain ⟨leftRequirements, leftValid, replayLeft⟩ := left
  obtain ⟨rightRequirements, rightValid, replayRight⟩ := right
  refine ⟨leftRequirements ++ rightRequirements,
    (holdsAll_append _ _ _).mpr ⟨leftValid, rightValid⟩, ?_⟩
  intro target validated
  obtain ⟨leftChecked, rightChecked⟩ := (holdsAll_append _ _ _).mp validated
  exact ⟨replayLeft target leftChecked, replayRight target rightChecked⟩

end Supported

/-- Conversion support includes root steps beneath all binding constructors. -/
theorem step_supported {R : Rules Head} {left right : Tm Head n}
    (step : Step R.headEq left right R.computation) :
    Supported R (fun target => Step target.headEq left right target.computation) := by
  induction step with
  | betaPi body argument => exact .uniform fun _ => .betaPi body argument
  | betaSigmaFst first second => exact .uniform fun _ => .betaSigmaFst first second
  | betaSigmaSnd first second => exact .uniform fun _ => .betaSigmaSnd first second
  | @head n left right equal =>
      exact (Supported.atom (.headEq left right) equal).map fun _ h => .head h
  | @root n left right root =>
      exact (Supported.atom (.rootStep n left right) root).map fun _ h => .root h
  | congPiDom _ ih => exact ih.map fun _ h => .congPiDom h
  | congPiCod _ ih => exact ih.map fun _ h => .congPiCod h
  | congSigmaDom _ ih => exact ih.map fun _ h => .congSigmaDom h
  | congSigmaCod _ ih => exact ih.map fun _ h => .congSigmaCod h
  | congIdTy _ ih => exact ih.map fun _ h => .congIdTy h
  | congIdLeft _ ih => exact ih.map fun _ h => .congIdLeft h
  | congIdRight _ ih => exact ih.map fun _ h => .congIdRight h
  | congLam _ ih => exact ih.map fun _ h => .congLam h
  | congAppFun _ ih => exact ih.map fun _ h => .congAppFun h
  | congAppArg _ ih => exact ih.map fun _ h => .congAppArg h
  | congPairFst _ ih => exact ih.map fun _ h => .congPairFst h
  | congPairSnd _ ih => exact ih.map fun _ h => .congPairSnd h
  | congFst _ ih => exact ih.map fun _ h => .congFst h
  | congSnd _ ih => exact ih.map fun _ h => .congSnd h
  | congRefl _ ih => exact ih.map fun _ h => .congRefl h

theorem conversion_supported {R : Rules Head} {left right : Tm Head n}
    (conversion : Conv R.headEq left right R.computation) :
    Supported R (fun target => Conv target.headEq left right target.computation) := by
  induction conversion with
  | rel left right step =>
      exact (step_supported step).map fun _ h => .rel left right h
  | refl term => exact .uniform fun _ => .refl term
  | symm left right _ ih => exact ih.map fun _ h => .symm left right h
  | trans left middle right _ _ ihLeft ihRight =>
      exact (ihLeft.and ihRight).map fun _ ⟨hLeft, hRight⟩ =>
        .trans left middle right hLeft hRight

/-- All intermediate formation and conversion dependencies are retained. -/
theorem typing_supported {R : Rules Head} {Γ : Ctx Head n} {term type : Tm Head n}
    (typing : Typing R Γ term type) :
    Supported R (fun target => Typing target Γ term type) := by
  induction typing with
  | @headType n Γ h u typed =>
      exact (Supported.atom (.headTyping h u) typed).map fun _ h => .headType h
  | var index => exact .uniform fun _ => .var index
  | @const n Γ name type u known _ universeWitness ih =>
      exact (((Supported.atom (.constantType name type) known).and ih).and
        (Supported.atom (.isUniverse u) universeWitness)).map fun _ ⟨⟨hKnown, hFormed⟩, hUniverse⟩ =>
          .const hKnown hFormed hUniverse
  | @piForm n Γ A B u v w _ universeA _ universeB join ihA ihB =>
      exact (((ihA.and (Supported.atom (.isUniverse u) universeA)).and
        (ihB.and (Supported.atom (.isUniverse v) universeB))).and
        (Supported.atom (.join u v w) join)).map
          fun _ ⟨⟨⟨hA, hU⟩, ⟨hB, hV⟩⟩, hJoin⟩ => .piForm hA hU hB hV hJoin
  | @sigmaForm n Γ A B u v w _ universeA _ universeB join ihA ihB =>
      exact (((ihA.and (Supported.atom (.isUniverse u) universeA)).and
        (ihB.and (Supported.atom (.isUniverse v) universeB))).and
        (Supported.atom (.join u v w) join)).map
          fun _ ⟨⟨⟨hA, hU⟩, ⟨hB, hV⟩⟩, hJoin⟩ => .sigmaForm hA hU hB hV hJoin
  | @lamIntro n Γ A body B u _ universeWitness _ ihPi ihBody =>
      exact ((ihPi.and (Supported.atom (.isUniverse u) universeWitness)).and ihBody).map
        fun _ ⟨⟨hPi, hUniverse⟩, hBody⟩ => .lamIntro hPi hUniverse hBody
  | appElim _ _ ihFunction ihArgument =>
      exact (ihFunction.and ihArgument).map fun _ ⟨hFunction, hArgument⟩ =>
        .appElim hFunction hArgument
  | @pairIntro n Γ a b A B u _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      exact (((ihSigma.and (Supported.atom (.isUniverse u) universeWitness)).and ihFirst).and
        ihSecond).map fun _ ⟨⟨⟨hSigma, hUniverse⟩, hFirst⟩, hSecond⟩ =>
          .pairIntro hSigma hUniverse hFirst hSecond
  | fstElim _ ihPair => exact ihPair.map fun _ h => .fstElim h
  | sndElim _ ihPair => exact ihPair.map fun _ h => .sndElim h
  | @idForm n Γ A a b u _ universeWitness _ _ ihA ihLeft ihRight =>
      exact (((ihA.and (Supported.atom (.isUniverse u) universeWitness)).and ihLeft).and
        ihRight).map fun _ ⟨⟨⟨hA, hUniverse⟩, hLeft⟩, hRight⟩ =>
          .idForm hA hUniverse hLeft hRight
  | reflIntro _ ihTerm => exact ihTerm.map fun _ h => .reflIntro h
  | @cumul n Γ t u v _ order ihTerm =>
      exact (ihTerm.and (Supported.atom (.cumulative u v) order)).map
        fun _ ⟨hTerm, hOrder⟩ => .cumul hTerm hOrder
  | @conv n Γ t A B u _ _ universeWitness conversion ihTerm ihTarget =>
      exact (((ihTerm.and ihTarget).and (Supported.atom (.isUniverse u) universeWitness)).and
        (conversion_supported conversion)).map
          fun _ ⟨⟨⟨hTerm, hTarget⟩, hUniverse⟩, hConversion⟩ =>
            .conv hTerm hTarget hUniverse hConversion

theorem context_supported {R : Rules Head} {Γ : Ctx Head n}
    (context : ContextFormation R Γ) :
    Supported R (fun target => ContextFormation target Γ) := by
  induction context with
  | nil => exact .uniform fun _ => .nil
  | @snoc n Γ A u _ formed universeWitness ih =>
      exact ((ih.and (typing_supported formed)).and
        (Supported.atom (.isUniverse u) universeWitness)).map
          fun _ ⟨⟨hContext, hFormed⟩, hUniverse⟩ => .snoc hContext hFormed hUniverse

/-- A whole admitted judgment can be replayed using finitely many primitive
requirements, including dependencies in its ambient telescope. -/
theorem judgment_supported {R : Rules Head} {Γ : Ctx Head n} {term type : Tm Head n}
    (judgment : Judgment R Γ term type) :
    Supported R (fun target => Judgment target Γ term type) :=
  ((context_supported judgment.context).and (typing_supported judgment.typing)).map
    fun _ ⟨context, typing⟩ => ⟨context, typing⟩

theorem typing_transfer {source target : Rules Head}
    (preserves : ∀ requirement : Requirement Head,
      requirement.Holds source → requirement.Holds target)
    {Γ : Ctx Head n} {term type : Tm Head n} (typing : Typing source Γ term type) :
    Typing target Γ term type := by
  obtain ⟨requirements, valid, replay⟩ := typing_supported typing
  exact replay target (fun requirement member => preserves requirement (valid requirement member))

theorem judgment_transfer {source target : Rules Head}
    (preserves : ∀ requirement : Requirement Head,
      requirement.Holds source → requirement.Holds target)
    {Γ : Ctx Head n} {term type : Tm Head n} (judgment : Judgment source Γ term type) :
    Judgment target Γ term type := by
  obtain ⟨requirements, valid, replay⟩ := judgment_supported judgment
  exact replay target (fun requirement member => preserves requirement (valid requirement member))

#print axioms step_supported
#print axioms conversion_supported
#print axioms typing_supported
#print axioms context_supported
#print axioms judgment_supported
#print axioms typing_transfer
#print axioms judgment_transfer

end FormationSensitive.Dependencies
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
