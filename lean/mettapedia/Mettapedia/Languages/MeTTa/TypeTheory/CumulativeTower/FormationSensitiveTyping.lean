import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TypedSubstitution

/-!
# Formation-sensitive typing over the cumulative presentation

This candidate refinement reuses the existing terms, telescopes, universe
rules, declaration lookup and conversion. It adds formation premises at
constant use, lambda introduction, pair introduction and conversion. It does
not change the selected Prime typing relation or the sealed Pure fragment.

The structural laws below apply to arbitrary rule packages. They do not
qualify an arbitrary computation package as consistent or normalizing.
Universe regularity is an additional, independently checkable property of
the head rules; it is not implied by the `Rules` record itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive

variable {Head : Type}

/-- The universe obligations needed for every type to have a universe.
In particular, this interface has no untyped-top-sort exception. -/
structure UniverseRegularity (R : Rules Head) : Prop where
  head_target : ∀ {h u}, R.headTyping h u → R.isUniverse u
  join_target : ∀ {u v w}, R.join u v w → R.isUniverse w
  cumulative_target : ∀ {u v}, R.cumulative u v → R.isUniverse v
  universe_typed : ∀ {u}, R.isUniverse u →
    ∃ v, R.headTyping u v ∧ R.isUniverse v

/-- Formation-sensitive derivations on the existing raw syntax. The context
is left raw here so renaming and substitution can be proved before wrapping
the relation in a formed-context judgment. -/
inductive Typing (R : Rules Head) :
    {n : Nat} → Ctx Head n → Tm Head n → Tm Head n → Prop where
  | headType {n : Nat} {Γ : Ctx Head n} {h u : Head} :
      R.headTyping h u → Typing R Γ (.head h) (.head u)
  | var {n : Nat} {Γ : Ctx Head n} (i : Fin n) :
      Typing R Γ (.var i) (Ctx.lookup Γ i)
  | const {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0} {u : Head} :
      R.constantType name = some type →
      Typing R .nil type (.head u) → R.isUniverse u →
      Typing R Γ (.const name) (liftClosed type)
  | piForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {u v w : Head} :
      Typing R Γ A (.head u) → R.isUniverse u →
      Typing R (.snoc Γ A) B (.head v) → R.isUniverse v →
      R.join u v w → Typing R Γ (.pi A B) (.head w)
  | sigmaForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {u v w : Head} :
      Typing R Γ A (.head u) → R.isUniverse u →
      Typing R (.snoc Γ A) B (.head v) → R.isUniverse v →
      R.join u v w → Typing R Γ (.sigma A B) (.head w)
  | lamIntro {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
      {body B : Tm Head (n + 1)} {u : Head} :
      Typing R Γ (.pi A B) (.head u) → R.isUniverse u →
      Typing R (.snoc Γ A) body B →
      Typing R Γ (.lam body) (.pi A B)
  | appElim {n : Nat} {Γ : Ctx Head n} {g a A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Typing R Γ g (.pi A B) → Typing R Γ a A →
      Typing R Γ (.app g a) (inst0 a B)
  | pairIntro {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
      {B : Tm Head (n + 1)} {u : Head} :
      Typing R Γ (.sigma A B) (.head u) → R.isUniverse u →
      Typing R Γ a A → Typing R Γ b (inst0 a B) →
      Typing R Γ (.pair a b) (.sigma A B)
  | fstElim {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Typing R Γ p (.sigma A B) → Typing R Γ (.fst p) A
  | sndElim {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Typing R Γ p (.sigma A B) →
      Typing R Γ (.snd p) (inst0 (.fst p) B)
  | idForm {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {u : Head} :
      Typing R Γ A (.head u) → R.isUniverse u →
      Typing R Γ a A → Typing R Γ b A →
      Typing R Γ (.id A a b) (.head u)
  | reflIntro {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} :
      Typing R Γ a A → Typing R Γ (.refl a) (.id A a a)
  | cumul {n : Nat} {Γ : Ctx Head n} {t : Tm Head n} {u v : Head} :
      Typing R Γ t (.head u) → R.cumulative u v →
      Typing R Γ t (.head v)
  | conv {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n} {u : Head} :
      Typing R Γ t A → Typing R Γ B (.head u) → R.isUniverse u →
      Conv R.headEq A B R.computation → Typing R Γ t B

variable {n m k : Nat}

namespace Typing

/-- Erasing formation premises gives an actual raw derivation. -/
theorem toRaw {R : Rules Head} {Γ : Ctx Head n} {t A : Tm Head n}
    (typing : Typing R Γ t A) : HasType R Γ t A := by
  induction typing with
  | headType head => exact .headType head
  | var index => exact .var index
  | const known _ _ _ => exact .const known
  | piForm _ universeA _ universeB join ihA ihB =>
      exact .piForm ihA universeA ihB universeB join
  | sigmaForm _ universeA _ universeB join ihA ihB =>
      exact .sigmaForm ihA universeA ihB universeB join
  | lamIntro _ _ _ _ ihBody => exact .lamIntro ihBody
  | appElim _ _ ihFunction ihArgument => exact .appElim ihFunction ihArgument
  | pairIntro _ _ _ _ _ ihFirst ihSecond => exact .pairIntro ihFirst ihSecond
  | fstElim _ ihPair => exact .fstElim ihPair
  | sndElim _ ihPair => exact .sndElim ihPair
  | idForm _ universeWitness _ _ ihA ihLeft ihRight =>
      exact .idForm ihA universeWitness ihLeft ihRight
  | reflIntro _ ihTerm => exact .reflIntro ihTerm
  | cumul _ order ihTerm => exact .cumul ihTerm order
  | conv _ _ _ conversion ihTerm _ => exact .conv ihTerm conversion

/-- Renaming preserves all retained formation derivations, including under
binders. Closed declaration types remain closed. -/
theorem renameTyping {R : Rules Head} {Γ : Ctx Head n} {t A : Tm Head n}
    (typing : Typing R Γ t A) :
    ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}, CtxRen Γ Δ ρ →
      Typing R Δ (rename ρ t) (rename ρ A) := by
  induction typing with
  | headType head =>
      intro m Δ ρ compatible
      exact .headType head
  | var index =>
      intro m Δ ρ compatible
      simpa only [rename, compatible index] using
        (Typing.var (R := R) (Γ := Δ) (ρ index))
  | const known formed universeWitness _ =>
      intro m Δ ρ compatible
      simpa only [rename, rename_liftClosed] using
        (Typing.const (Γ := Δ) known formed universeWitness)
  | piForm _ universeA _ universeB join ihA ihB =>
      intro m Δ ρ compatible
      exact .piForm (ihA compatible) universeA
        (ihB (compatible.snoc _)) universeB join
  | sigmaForm _ universeA _ universeB join ihA ihB =>
      intro m Δ ρ compatible
      exact .sigmaForm (ihA compatible) universeA
        (ihB (compatible.snoc _)) universeB join
  | lamIntro _ universeWitness _ ihPi ihBody =>
      intro m Δ ρ compatible
      exact .lamIntro (ihPi compatible) universeWitness (ihBody (compatible.snoc _))
  | appElim _ _ ihFunction ihArgument =>
      intro m Δ ρ compatible
      simpa only [rename, rename_inst0] using
        (Typing.appElim (ihFunction compatible) (ihArgument compatible))
  | pairIntro _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      intro m Δ ρ compatible
      have second := ihSecond compatible
      rw [rename_inst0] at second
      exact .pairIntro (ihSigma compatible) universeWitness (ihFirst compatible) second
  | fstElim _ ihPair =>
      intro m Δ ρ compatible
      exact .fstElim (ihPair compatible)
  | sndElim _ ihPair =>
      intro m Δ ρ compatible
      simpa only [rename, rename_inst0] using (Typing.sndElim (ihPair compatible))
  | idForm _ universeWitness _ _ ihA ihLeft ihRight =>
      intro m Δ ρ compatible
      exact .idForm (ihA compatible) universeWitness (ihLeft compatible) (ihRight compatible)
  | reflIntro _ ihTerm =>
      intro m Δ ρ compatible
      exact .reflIntro (ihTerm compatible)
  | cumul _ order ihTerm =>
      intro m Δ ρ compatible
      exact .cumul (ihTerm compatible) order
  | conv _ _ universeWitness conversion ihTerm ihTarget =>
      intro m Δ ρ compatible
      exact .conv (ihTerm compatible) (ihTarget compatible) universeWitness
        (conversion.renameTerms ρ)

theorem weaken {R : Rules Head} {Γ : Ctx Head n} {t A extension : Tm Head n}
    (typing : Typing R Γ t A) :
    Typing R (.snoc Γ extension) (rename wk t) (rename wk A) :=
  typing.renameTyping (fun _ => rfl)

end Typing

/-- A simultaneous substitution admitted by the refined judgment itself. -/
def CtxMor (R : Rules Head) (Γ : Ctx Head n) (Δ : Ctx Head m)
    (σ : Sub Head n m) : Prop :=
  ∀ index, Typing R Δ (σ index) (subst σ (Ctx.lookup Γ index))

theorem CtxMor.toRaw {R : Rules Head} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ : Sub Head n m} (typed : CtxMor R Γ Δ σ) :
    Presentation.CtxMor R Γ Δ σ := fun index => (typed index).toRaw

theorem CtxMor.lift {R : Rules Head} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ : Sub Head n m} (typed : CtxMor R Γ Δ σ) (A : Tm Head n) :
    CtxMor R (.snoc Γ A) (.snoc Δ (subst σ A)) (liftSub σ) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · simpa only [liftSub_zero, Ctx.lookup_snoc_zero, subst_liftSub_wk] using
      (Typing.var (R := R) (Γ := .snoc Δ (subst σ A)) (0 : Fin (m + 1)))
  · intro prior
    simpa only [liftSub_succ, Ctx.lookup_snoc_succ, subst_liftSub_wk] using
      (Typing.weaken (extension := subst σ A) (typed prior))

/-- Substitution preserves the full derivation, not only raw typing or the
formation of its final type. -/
theorem Typing.substitute {R : Rules Head} {Γ : Ctx Head n} {t A : Tm Head n}
    (typing : Typing R Γ t A) :
    ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, CtxMor R Γ Δ σ →
      Typing R Δ (subst σ t) (subst σ A) := by
  induction typing with
  | headType head =>
      intro m Δ σ typed
      exact .headType head
  | var index =>
      intro m Δ σ typed
      exact typed index
  | const known formed universeWitness _ =>
      intro m Δ σ typed
      simpa only [subst, subst_liftClosed] using
        (Typing.const (Γ := Δ) known formed universeWitness)
  | piForm _ universeA _ universeB join ihA ihB =>
      intro m Δ σ typed
      exact .piForm (ihA typed) universeA (ihB (typed.lift _)) universeB join
  | sigmaForm _ universeA _ universeB join ihA ihB =>
      intro m Δ σ typed
      exact .sigmaForm (ihA typed) universeA (ihB (typed.lift _)) universeB join
  | lamIntro _ universeWitness _ ihPi ihBody =>
      intro m Δ σ typed
      exact .lamIntro (ihPi typed) universeWitness (ihBody (typed.lift _))
  | appElim _ _ ihFunction ihArgument =>
      intro m Δ σ typed
      simpa only [subst, subst_inst0] using
        (Typing.appElim (ihFunction typed) (ihArgument typed))
  | pairIntro _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      intro m Δ σ typed
      have second := ihSecond typed
      rw [subst_inst0] at second
      exact .pairIntro (ihSigma typed) universeWitness (ihFirst typed) second
  | fstElim _ ihPair =>
      intro m Δ σ typed
      exact .fstElim (ihPair typed)
  | sndElim _ ihPair =>
      intro m Δ σ typed
      simpa only [subst, subst_inst0] using (Typing.sndElim (ihPair typed))
  | idForm _ universeWitness _ _ ihA ihLeft ihRight =>
      intro m Δ σ typed
      exact .idForm (ihA typed) universeWitness (ihLeft typed) (ihRight typed)
  | reflIntro _ ihTerm =>
      intro m Δ σ typed
      exact .reflIntro (ihTerm typed)
  | cumul _ order ihTerm =>
      intro m Δ σ typed
      exact .cumul (ihTerm typed) order
  | conv _ _ universeWitness conversion ihTerm ihTarget =>
      intro m Δ σ typed
      exact .conv (ihTerm typed) (ihTarget typed) universeWitness (conversion.substitute σ)

/-- Opening a binder uses the existing capture-avoiding substitution. -/
theorem Typing.instantiate {R : Rules Head} {Γ : Ctx Head n}
    {A argument : Tm Head n} {body B : Tm Head (n + 1)}
    (bodyTyping : Typing R (.snoc Γ A) body B)
    (argumentTyping : Typing R Γ argument A) :
    Typing R Γ (inst0 argument body) (inst0 argument B) := by
  apply bodyTyping.substitute
  intro index
  refine Fin.cases ?_ ?_ index
  · change Typing R Γ argument (inst0 argument (rename wk A))
    rw [inst0_rename_wk]
    exact argumentTyping
  · intro prior
    change Typing R Γ (.var prior)
      (inst0 argument (rename wk (Ctx.lookup Γ prior)))
    rw [inst0_rename_wk]
    exact .var prior

/-- The existing cumulative head rules satisfy the separate universe
regularity obligations, with no new universe or logical axiom. -/
theorem towerUniverseRegularity : UniverseRegularity Tower.rules where
  head_target := by
    intro h u typing
    cases typing <;> exact .sort _
  join_target := by
    intro u v w join
    cases join
    exact .sort _
  cumulative_target := by
    intro u v order
    cases u <;> cases v <;> simp only [Tower.rules, Tower.Cumulative] at order
    exact .sort _
  universe_typed := by
    intro u universeWitness
    cases universeWitness with
    | sort level => exact ⟨_, .sort level, .sort _⟩

#print axioms Typing.toRaw
#print axioms Typing.renameTyping
#print axioms Typing.substitute
#print axioms Typing.instantiate
#print axioms towerUniverseRegularity

end FormationSensitive
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
