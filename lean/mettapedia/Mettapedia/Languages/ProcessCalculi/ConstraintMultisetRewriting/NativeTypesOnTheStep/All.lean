import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Comprehension
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.SyntacticShadow
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.SettlingStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.MatchAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.SchemaOpening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.CoerceSettled
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.CrossPostponed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.DecidedFragments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.DeclaredComputation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.VectorAppend
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.InterpreterDeclared
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.RhoNativeTypes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.AgreementCounterexample
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ConversionSettling
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ConversionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ComputableSettler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ComputableControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.DeclaredConfluence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateConversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateSettling
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.OlderUnknown
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.OlderUnknownControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateInference
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateInferenceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.MillerFamily
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.RankSettler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.RankSettlerControls

/-!
# The step's dependent fibre in native type theory

* `Comprehension`: a firing's information as a subobject of its frame's representable presheaf, the
  joint equalizer of its equations; typing after the match as factorization through the typed rows.
* `SyntacticShadow`: principal answers represent the comprehension up to agreement; settling along
  them is complete for the rule of every solution and sound for the rule up to agreement.
* `SettlingStep`: a step that settles lazily along a settler's initial solutions, conservative over
  the dependent full step, which is the settler that never settles.
* `MatchAdmission`: admission after the match, realized by the semantic settler.
* `SchemaOpening`: the comprehension read through the schema opening's typed arguments.
* `CoerceSettled`: the coerce firing typed after its match and admitted when settled.
* `CrossPostponed`: where no initial solution exists, every settler postpones: a third outcome, not
  a refusal.
* `DecidedFragments`: on stores with an initial solution or none, settled admission is admission
  after the match; the cross store is outside.
* `DeclaredComputation`: declared computing rules in conversion, and the coherence of telling them.
* `VectorAppend`: `vappend nil ys = ys` settled by the match and typed by declared addition; the
  controls for both, and for a declaration that is not confluent.
* `InterpreterDeclared`: the typed interpreter returns at its declared type once its value type is
  declared computing.
* `RhoNativeTypes`: rho's native types against the step's types, the generated logic agreeing with
  the past over the heating class, and where they diverge.
* `AgreementCounterexample`: raw typing is not closed under agreement: `h : Π (x : U₁). U₁` and its
  η-expansion agree, and only the η-expansion is typed at `Π (x : U₀). U₁`; a settler along the
  η-expansion makes the settling step admit a row not typed after the match.
* `ConversionSettling`: formed types are closed under agreement, so the conversion rule (the code typed
  in its frame at a type usable at the row's type after the solution) is decided exactly by settling;
  the converting settling step is fully sound for every settler.
* `ConversionControls`: the converting step admits the coerce firing and refuses the η firing for every
  settler.
* `ComputableSettler`: a computable settler from decided solver families, agreeing with the semantic
  settler on their union; the converting step does not depend on the representative; the tree's
  worklist driver as a family; conversion of variable codes.
* `ComputableControls`: decided admission in the tower, evaluated by the kernel, on a firing that
  learns a universe by matching; D2's coerce store is outside the families.
* `DeclaredConfluence`: addition declared computing is a constructor system, hence Church–Rosser with
  β; an overlapping declaration is not; with a normalizer, conversion is decided by normal forms.
* `TemplateConversion`: conversion moved to the variables: a template typed in its own frame, each
  template variable filled by a frame variable whose declared type converts; closed under agreement,
  decided by settling, fully sound; the templating step.
* `TemplateSettling`: the templating step does not depend on the representative, and on the decided
  fragments the computable settler's templating step admits what the semantic one's admits.
* `TemplateControls`: `f a` with `f : X` and `X ≐ Π (y : U₀). U₀` told: no typing in its frame, refused by
  conversion at the type for every settler, admitted by the templating step.
* `OlderUnknown`: a heterogeneous equation's type equation extracted into the store, at a common universe,
  with the same solutions; the older-unknown transition (the unknown solved at its own prefix, carried
  past the later declarations) is exact and carries initial solutions on its class; the tower's
  older-unknown family (extraction, then the in-place solver) joins the computable settler, which agrees
  with the semantic settler on the union of the decided fragments.
* `OlderUnknownControls`: D2's coerce firing admitted by the computable settler, evaluated by the kernel,
  where the present step refuses it; the same across universes; the tree's own stuck heterogeneous store
  settled; a refuted variant; a store whose type unknown is applied, declined; the cross store declined by
  every family.
* `TemplateInference`: the template of a neutral row inferred at a covered answer, principal by the
  principal types of synthesis; usability decided between simple types; the templating step decided on
  its fragment.
* `TemplateInferenceControls`: the gap firing admitted by the computable templating step, refused by the
  converting step for every settler; a function learned by matching admitted; a refused variant,
  independently not typed after the match; the η firing refused.
* `MillerFamily`: the unifier's Miller solver as a computable family, its answers trimmed computably to
  initial solutions; with it the computable settler settles a store pruned on both sides, which it
  declined before.
-/
