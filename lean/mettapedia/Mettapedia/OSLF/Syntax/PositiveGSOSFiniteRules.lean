import Mettapedia.OSLF.Syntax.PositiveGSOSPremises

/-!
# Positive selected clauses as actual finite-premise rules

The active/passive syntax embeds into ordinary finite-premise rules by
observing only its selected actions. All observed premises are positive;
passive arguments do not enter the observation set. Matching this finite
rule is exactly supplying the selected derivatives. Its target readout
agrees with the independent natural conclusion operation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.PositivePremises

open CategoryTheory Mettapedia.TypeTheory

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}
    {sort : S.Srt} {operator : S.Operator sort}

namespace Pattern

/-- Active argument occurrences, retaining their individual positions. -/
abbrev Active (pattern : Pattern (Actions := Actions) operator) :=
  {position : S.Position operator // pattern.active position = true}

/-- The actual selected transition address of one active occurrence. -/
def address (pattern : Pattern (Actions := Actions) operator) (position : pattern.Active) :
    Address Actions operator :=
  ⟨position.1, pattern.label position.1 position.2⟩

/-- Exactly the selected positive action addresses form the finite premise set. -/
noncomputable def observed (pattern : Pattern (Actions := Actions) operator) :
    Finset (Address Actions operator) := by
  classical
  let : Finite (S.Position operator) := S.finite operator
  let : Fintype pattern.Active := Fintype.ofFinite _
  exact Finset.univ.image pattern.address

theorem mem_observed (pattern : Pattern (Actions := Actions) operator)
    (candidate : Address Actions operator) :
    candidate ∈ pattern.observed ↔ ∃ position : pattern.Active, pattern.address position = candidate := by
  classical
  let : Finite (S.Position operator) := S.finite operator
  let : Fintype pattern.Active := Fintype.ofFinite _
  simp [observed]

theorem address_mem_observed (pattern : Pattern (Actions := Actions) operator)
    (position : pattern.Active) : pattern.address position ∈ pattern.observed :=
  (pattern.mem_observed _).mpr ⟨position, rfl⟩

/-- The minimal complete guard needed to interpret a positive target. -/
noncomputable abbrev selectedGuard (pattern : Pattern (Actions := Actions) operator) :
    Guard Actions operator :=
  observedGuard Actions pattern.observed (fun _ => true)

theorem selectedGuard_address (pattern : Pattern (Actions := Actions) operator)
    (position : pattern.Active) : pattern.selectedGuard (pattern.address position) = true := by
  classical
  simp [selectedGuard, observedGuard, pattern.address_mem_observed position]

/-- Include independent positive target names in the ordinary GSOS rule family. -/
noncomputable def nameInclusion (pattern : Pattern (Actions := Actions) operator) :
    variableFamily pattern ⟶ ruleVariables Actions operator pattern.selectedGuard :=
  fun _ _ => ↾(fun name => match name with
    | .original position => .original position
    | .derivative position active =>
        .derivative (pattern.address ⟨position, active⟩)
          (pattern.selectedGuard_address ⟨position, active⟩))

/-- Embed an authored positive conclusion into the actual finite GSOS format. -/
noncomputable abbrev finiteRule (pattern : Pattern (Actions := Actions) operator)
    (body : S.Term (variableFamily pattern) sort) : FiniteRule Actions operator where
  observed := pattern.observed
  pattern _ := true
  target := S.rename pattern.nameInclusion body

/-- A finite positive rule matches exactly when each selected action is enabled. -/
theorem finiteRule_matches (pattern : Pattern (Actions := Actions) operator)
    (body : S.Term (variableFamily pattern) sort) (guard : Guard Actions operator) :
    (pattern.finiteRule body).Matches guard ↔
      ∀ position : pattern.Active, guard (pattern.address position) = true := by
  constructor
  · intro firing position
    exact firing (pattern.address position) (pattern.address_mem_observed position)
  · intro enabled candidate present
    obtain ⟨position, equal⟩ := (pattern.mem_observed candidate).mp present
    subst candidate
    exact enabled position

/-- A supplied selected input proves every finite positive premise. -/
theorem realizes_matches (pattern : Pattern (Actions := Actions) operator)
    (body : S.Term (variableFamily pattern) sort) {X : S.Families}
    (arguments : BehaviourArguments S Actions X operator) (input : Input pattern X)
    (realizes : pattern.Realizes arguments input) :
    (pattern.finiteRule body).Matches (inputGuard Actions arguments) := by
  apply (pattern.finiteRule_matches body _).mpr
  intro position
  simp [inputGuard, address, realizes.2 position.1 position.2]

/-- Recover each actual selected derivative from the matching finite premises. -/
noncomputable def inputOfMatch (pattern : Pattern (Actions := Actions) operator)
    (body : S.Term (variableFamily pattern) sort) {X : S.Families}
    (arguments : BehaviourArguments S Actions X operator)
    (matching : (pattern.finiteRule body).Matches (inputGuard Actions arguments)) :
    Input pattern X where
  originals position := (arguments position).1
  derivatives position active := ((arguments position).2 (pattern.label position active)).get
    ((pattern.finiteRule_matches body _).mp matching ⟨position, active⟩)

theorem inputOfMatch_realizes (pattern : Pattern (Actions := Actions) operator)
    (body : S.Term (variableFamily pattern) sort) {X : S.Families}
    (arguments : BehaviourArguments S Actions X operator)
    (matching : (pattern.finiteRule body).Matches (inputGuard Actions arguments)) :
    pattern.Realizes arguments (pattern.inputOfMatch body arguments matching) := by
  constructor
  · intro position
    rfl
  · intro position active
    simp only [inputOfMatch]
    exact (Option.some_get _).symm

/-- Firing the finite rule is exactly inhabiting its selected premise domain. -/
theorem finiteRule_matches_iff_input (pattern : Pattern (Actions := Actions) operator)
    (body : S.Term (variableFamily pattern) sort) {X : S.Families}
    (arguments : BehaviourArguments S Actions X operator) :
    (pattern.finiteRule body).Matches (inputGuard Actions arguments) ↔
      ∃ input : Input pattern X, pattern.Realizes arguments input := by
  constructor
  · intro matching
    exact ⟨pattern.inputOfMatch body arguments matching,
      pattern.inputOfMatch_realizes body arguments matching⟩
  · rintro ⟨input, realizes⟩
    exact pattern.realizes_matches body arguments input realizes

/-- The finite-rule variable assignment recovers the exact selected input. -/
theorem matched_assignment (pattern : Pattern (Actions := Actions) operator)
    (body : S.Term (variableFamily pattern) sort) {X : S.Families}
    (arguments : BehaviourArguments S Actions X operator) (input : Input pattern X)
    (realizes : pattern.Realizes arguments input)
    (matching : (pattern.finiteRule body).Matches (inputGuard Actions arguments)) :
    pattern.nameInclusion ≫
        (pattern.finiteRule body).matchedInclusion (inputGuard Actions arguments) matching ≫
        assignment Actions arguments = input.assignment := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro name
  cases base
  cases name with
  | original position =>
      exact (realizes.1 position).symm
  | derivative position active =>
      change ((arguments position).2 (pattern.label position active)).get _ =
        input.derivatives position active
      simp [realizes.2 position active]

/-- The selected finite rule's actual target agrees with independent syntax evaluation. -/
theorem instantiate_finiteRule (pattern : Pattern (Actions := Actions) operator)
    (body : S.Term (variableFamily pattern) sort) {X : S.Families}
    (arguments : BehaviourArguments S Actions X operator) (input : Input pattern X)
    (realizes : pattern.Realizes arguments input)
    (matching : (pattern.finiteRule body).Matches (inputGuard Actions arguments)) :
    S.rename (assignment Actions arguments)
      (S.rename ((pattern.finiteRule body).matchedInclusion _ matching)
        (pattern.finiteRule body).target) =
      (NaturalConclusion.ofTarget pattern body).operation X input := by
  change S.rename (assignment Actions arguments)
    (S.rename ((pattern.finiteRule body).matchedInclusion _ matching)
      (S.rename pattern.nameInclusion body)) = S.rename input.assignment body
  have earlier := IndexedPolynomial.Free.map_comp S.polynomial
    (fun base index => pattern.nameInclusion base index)
    (fun base index => (pattern.finiteRule body).matchedInclusion _ matching base index) body
  have later := IndexedPolynomial.Free.map_comp S.polynomial
    (fun base index => (pattern.nameInclusion ≫
      (pattern.finiteRule body).matchedInclusion _ matching) base index)
    (fun base index => assignment Actions arguments base index) body
  exact (congrArg (S.rename (assignment Actions arguments)) earlier).trans
    (later.trans (congrArg (fun mapping => S.rename mapping body)
      (by simpa only [Category.assoc] using
        pattern.matched_assignment body arguments input realizes matching)))

end Pattern

end Mettapedia.OSLF.DeterministicGSOS.PositivePremises
