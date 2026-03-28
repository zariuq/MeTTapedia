import Mettapedia.Logic.HOL.IntuitionisticSoundness
import Mettapedia.Logic.HOL.IntuitionisticCompleteness
import Mettapedia.Logic.HOL.Semantics.Reduct

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-!
# Plain Intuitionistic HOL Mainline  [MAINLINE]

This module is the public entrypoint for the plain intuitionistic-extensional
HOL metatheory.

It intentionally stays on the direct mainline:

- intuitionistic soundness for the original signature,
- the internal cumulative-Henkin completeness milestone,
- and the canonical validity/provability interface used by the future direct
  original-signature completeness proof.

The final unconditional completeness theorem
`plain_intuitionistic_completeness` will be assembled here once the
growing-domain Kripke construction in `ParamWorld.lean` / `ParamCompleteness.lean`
is complete.

It intentionally does NOT import the original-reflection reduction / obstruction
files. Those files analyze an auxiliary constant-based bridge that is useful for
diagnostics and strengthened reflection theorems, but they are not the main
route to plain intuitionistic original-signature completeness.
-/
namespace PlainIntuitionistic

/--
Original-signature semantic validity from finite assumptions in all
intuitionistic/extensional Heyting-Henkin models.
-/
def OriginalValidFrom
    (Δ : List (ClosedFormula Const))
    (φ : ClosedFormula Const) : Prop :=
  ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
    HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)

/-- Plain intuitionistic soundness for closed theorems over the original signature. -/
theorem theorem_sound
    {φ : ClosedFormula Const}
    (d : ExtDerivation.Theorem Const φ)
    (M : HeytingHenkinModel.{u, v, w} Base Const) :
    HeytingHenkinModel.models M φ :=
  IntuitionisticSoundness.theorem_sound d M

/-- Ordinary derivability implies original-signature semantic validity. -/
theorem validFrom_of_provable
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hProv : ExtDerivation Const Δ φ) :
    OriginalValidFrom (Base := Base) (Const := Const) Δ φ := by
  intro M
  simpa [OriginalValidFrom] using
    (IntuitionisticSoundness.derivation_sound
      (Base := Base)
      (Const := Const)
      (d := hProv)
      (M := M)
      (ρ := fun v => nomatch v)
      (by intro τ v; nomatch v))

/--
Internal cumulative-Henkin completeness milestone:
canonical Henkin validity is equivalent to provability in the cumulative Henkin
language.
-/
theorem canonicalHenkinValidFrom_iff_provable
    {Δ : List (ClosedFormula (HenkinConstInfinity.HInf Base Const))}
    {φ : ClosedFormula (HenkinConstInfinity.HInf Base Const)} :
    HenkinConstInfinity.CanonicalHenkinValidFrom
        (Base := Base)
        (Const := Const)
        Δ
        φ ↔
      ClosedTheorySet.Provable
        (Const := HenkinConstInfinity.HInf Base Const)
        (fun ψ => ψ ∈ Δ ∨ ψ ∈ HenkinConstInfinity.HenkinAxioms (Base := Base) (Const := Const))
        φ :=
  HenkinConstInfinity.canonicalHenkinValidFrom_iff_provable
    (Base := Base)
    (Const := Const)

/--
If an original-signature derivation is already known, its cumulative-Henkin lift
is canonically valid.
-/
theorem liftBase_canonicalHenkinValidFrom_of_provable
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hProv : ExtDerivation Const Δ φ) :
    HenkinConstInfinity.CanonicalHenkinValidFrom
      (Base := Base)
      (Const := Const)
      (Δ.map (HenkinConstInfinity.liftBaseClosedFormula (Base := Base) (Const := Const)))
      (HenkinConstInfinity.liftBaseClosedFormula (Base := Base) (Const := Const) φ) :=
  HenkinConstInfinity.liftBase_canonicalHenkinValidFrom_of_provable
    (Base := Base)
    (Const := Const)
    hProv

/--
Original-signature semantic validity transports along the base-constant embedding
into the cumulative Henkin signature.
-/
theorem liftBase_validFrom_of_validFrom
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ∀ M : HeytingHenkinModel.{u, max u (v + 1), w}
        Base (HenkinConstInfinity.HInf Base Const),
      HeytingHenkinModel.modelsFrom M
        (Δ.map (HenkinConstInfinity.liftBaseClosedFormula (Base := Base) (Const := Const)))
        (HenkinConstInfinity.liftBaseClosedFormula (Base := Base) (Const := Const) φ)
        (fun v => nomatch v) := by
  intro M
  change
    HeytingHenkinModel.modelsFrom M
      (Δ.map (mapConst (fun {τ} c => HenkinConstInfinity.base c)))
      (mapConst (fun {τ} c => HenkinConstInfinity.base c) φ)
      (fun v => nomatch v)
  let Mred : HeytingHenkinModel.{u, v, w} Base Const :=
    HeytingHenkinModel.reduct
      (Base := Base)
      (Const := Const)
      (Const' := HenkinConstInfinity.HInf Base Const)
      (fun {τ} c => HenkinConstInfinity.base c)
      M
  have hBase := hValid Mred
  exact
    (HeytingHenkinModel.modelsFrom_mapConst_iff
      (Base := Base)
      (Const := Const)
      (Const' := HenkinConstInfinity.HInf Base Const)
      (fun {τ} c => HenkinConstInfinity.base c)
      M
      Δ
      φ
      (fun v => nomatch v)).mp hBase

/--
If a lifted canonical counterworld can always be turned into a standard
`HeytingHenkinModel` countermodel, then the remaining plain-completeness gap can
be stated entirely at the canonical-world layer.

Positive example:
the canonical-world counterexample theorem in
`CanonicalModel.lean` is enough once such a bridge is available.

Negative example:
without this bridge, the existing canonical counterworld machinery does not yet
directly discharge `OriginalValidFrom`.
-/
theorem liftBase_countermodel_of_canonical_counterworld
    (hBridge :
      ∀ {Δ : List (ClosedFormula (HenkinConstInfinity.HInf Base Const))}
        {φ : ClosedFormula (HenkinConstInfinity.HInf Base Const)},
        (∃ W : HenkinConstInfinity.World Base Const,
            W ∈ HenkinConstInfinity.contextDenote
                  (Base := Base)
                  (Const := Const)
                  Δ
                  (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
            ¬ HenkinConstInfinity.modelsFrom
                  (Base := Base)
                  (Const := Const)
                  Δ
                  φ
                  (HenkinConstInfinity.emptyClosedSubst Base Const)) →
          ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
              Base (HenkinConstInfinity.HInf Base Const),
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (hCanonicalCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
        ∃ W : HenkinConstInfinity.World Base Const,
          W ∈ HenkinConstInfinity.contextDenote
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
          ¬ HenkinConstInfinity.modelsFrom
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const) φ)
                (HenkinConstInfinity.emptyClosedSubst Base Const)) :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      ¬ ExtDerivation Const Δ φ →
      ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
          Base (HenkinConstInfinity.HInf Base Const),
        ¬ HeytingHenkinModel.modelsFrom M
            (Δ.map
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const)))
            (HenkinConstInfinity.liftBaseClosedFormula
              (Base := Base) (Const := Const) φ)
            (fun v => nomatch v) := by
  intro Δ φ hNot
  rcases hCanonicalCounter hNot with ⟨W, hWΔ, hWNot⟩
  exact hBridge ⟨W, hWΔ, hWNot⟩

/--
Stronger diagnostic reduction:
if original non-provability can be turned into non-provability of the lifted
cumulative-Henkin sequent, then the existing canonical countermodel theorem
already provides the lifted canonical counterworld.

Positive example:
this isolates one tempting proof-theoretic route very explicitly.

Negative example:
this is NOT the intended general mainline theorem boundary, because cumulative
Henkinization genuinely adds fresh witnesses; the empty-signature obstruction
shows that such a lifted non-provability principle is too strong in general.
-/
theorem liftBase_canonical_counterworld_of_liftBase_notProvable
    (hLiftNotProvable :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ¬ ClosedTheorySet.Provable
              (Const := HenkinConstInfinity.HInf Base Const)
              (fun ψ =>
                ψ ∈ Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)) ∨
                  ψ ∈ HenkinConstInfinity.HenkinAxioms
                    (Base := Base) (Const := Const))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ)) :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      ¬ ExtDerivation Const Δ φ →
        ∃ W : HenkinConstInfinity.World Base Const,
          W ∈ HenkinConstInfinity.contextDenote
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
          ¬ HenkinConstInfinity.modelsFrom
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const) φ)
                (HenkinConstInfinity.emptyClosedSubst Base Const) := by
  intro Δ φ hNot
  exact HenkinConstInfinity.exists_canonical_countermodel_of_list_notProvable
    (Base := Base)
    (Const := Const)
    (Δ := Δ.map
      (HenkinConstInfinity.liftBaseClosedFormula
        (Base := Base) (Const := Const)))
    (φ := HenkinConstInfinity.liftBaseClosedFormula
      (Base := Base) (Const := Const) φ)
    (hNot := hLiftNotProvable hNot)

/--
Route 1 endgame reduction:
if every non-derivable original sequent has a standard cumulative-Henkin
countermodel for its lifted form, then original-signature semantic validity
already implies derivability.

This is the direct Henkin path for plain intuitionistic completeness:
the remaining gap is a lifted countermodel theorem, not any reflection theorem.
-/
theorem provable_of_liftBase_countermodel
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
        ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
            Base (HenkinConstInfinity.HInf Base Const),
          ¬ HeytingHenkinModel.modelsFrom M
              (Δ.map
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const)))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ)
              (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  classical
  by_contra hNot
  rcases hCounter hNot with ⟨M, hM⟩
  have hLift :
      ∀ M : HeytingHenkinModel.{u, max u (v + 1), w}
          Base (HenkinConstInfinity.HInf Base Const),
        HeytingHenkinModel.modelsFrom M
          (Δ.map
            (HenkinConstInfinity.liftBaseClosedFormula
              (Base := Base) (Const := Const)))
          (HenkinConstInfinity.liftBaseClosedFormula
            (Base := Base) (Const := Const) φ)
          (fun v => nomatch v) :=
    liftBase_validFrom_of_validFrom (Base := Base) (Const := Const) hValid
  exact hM (hLift M)

/--
Plain completeness can also be reduced in two explicit Henkin-style steps:

1. produce a lifted canonical counterworld from original non-provability;
2. bridge that canonical counterworld to a standard `HeytingHenkinModel`.

This keeps the remaining endgame theorem boundary honest.
-/
theorem provable_of_liftBase_canonical_counterworld
    (hBridge :
      ∀ {Δ : List (ClosedFormula (HenkinConstInfinity.HInf Base Const))}
        {φ : ClosedFormula (HenkinConstInfinity.HInf Base Const)},
        (∃ W : HenkinConstInfinity.World Base Const,
            W ∈ HenkinConstInfinity.contextDenote
                  (Base := Base)
                  (Const := Const)
                  Δ
                  (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
            ¬ HenkinConstInfinity.modelsFrom
                  (Base := Base)
                  (Const := Const)
                  Δ
                  φ
                  (HenkinConstInfinity.emptyClosedSubst Base Const)) →
          ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
              Base (HenkinConstInfinity.HInf Base Const),
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (hCanonicalCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
        ∃ W : HenkinConstInfinity.World Base Const,
          W ∈ HenkinConstInfinity.contextDenote
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
          ¬ HenkinConstInfinity.modelsFrom
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const) φ)
                (HenkinConstInfinity.emptyClosedSubst Base Const))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  exact
    provable_of_liftBase_countermodel
      (Base := Base)
      (Const := Const)
      (liftBase_countermodel_of_canonical_counterworld
        (Base := Base)
        (Const := Const)
        hBridge
        hCanonicalCounter)
      hValid

/--
Mainline completeness reduction at the fully split Henkin boundary:

1. original non-provability implies lifted cumulative-Henkin non-provability;
2. lifted canonical counterworlds can be bridged to standard
   `HeytingHenkinModel`s.

This is the repo's current direct Route 1 endgame statement.
-/
theorem provable_of_liftBase_notProvable_and_canonical_counterworld
    (hBridge :
      ∀ {Δ : List (ClosedFormula (HenkinConstInfinity.HInf Base Const))}
        {φ : ClosedFormula (HenkinConstInfinity.HInf Base Const)},
        (∃ W : HenkinConstInfinity.World Base Const,
            W ∈ HenkinConstInfinity.contextDenote
                  (Base := Base)
                  (Const := Const)
                  Δ
                  (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
            ¬ HenkinConstInfinity.modelsFrom
                  (Base := Base)
                  (Const := Const)
                  Δ
                  φ
                  (HenkinConstInfinity.emptyClosedSubst Base Const)) →
          ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
              Base (HenkinConstInfinity.HInf Base Const),
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (hLiftNotProvable :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ¬ ClosedTheorySet.Provable
              (Const := HenkinConstInfinity.HInf Base Const)
              (fun ψ =>
                ψ ∈ Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)) ∨
                  ψ ∈ HenkinConstInfinity.HenkinAxioms
                    (Base := Base) (Const := Const))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  exact
    provable_of_liftBase_canonical_counterworld
      (Base := Base)
      (Const := Const)
      hBridge
      (liftBase_canonical_counterworld_of_liftBase_notProvable
        (Base := Base)
        (Const := Const)
        hLiftNotProvable)
      hValid

/--
Plain intuitionistic original-signature completeness follows from the lifted
cumulative-Henkin countermodel theorem supplied by the direct Henkin path.

This is stated in fully explicit `modelsFrom` form to keep the remaining gap
visible without relying on universe-polymorphic abbreviation inference.
-/
theorem validFrom_iff_provable_of_liftBase_countermodel
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
        ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
            Base (HenkinConstInfinity.HInf Base Const),
          ¬ HeytingHenkinModel.modelsFrom M
              (Δ.map
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const)))
              (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const) φ)
              (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  constructor
  · intro hValid
    exact
      provable_of_liftBase_countermodel
        (Base := Base)
        (Const := Const)
        hCounter
        hValid
  · exact validFrom_of_provable (Base := Base) (Const := Const)

/--
The same completeness reduction stated at the sharper canonical-world boundary.
-/
theorem validFrom_iff_provable_of_liftBase_canonical_counterworld
    (hBridge :
      ∀ {Δ : List (ClosedFormula (HenkinConstInfinity.HInf Base Const))}
        {φ : ClosedFormula (HenkinConstInfinity.HInf Base Const)},
        (∃ W : HenkinConstInfinity.World Base Const,
            W ∈ HenkinConstInfinity.contextDenote
                  (Base := Base)
                  (Const := Const)
                  Δ
                  (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
            ¬ HenkinConstInfinity.modelsFrom
                  (Base := Base)
                  (Const := Const)
                  Δ
                  φ
                  (HenkinConstInfinity.emptyClosedSubst Base Const)) →
          ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
              Base (HenkinConstInfinity.HInf Base Const),
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (hCanonicalCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
        ∃ W : HenkinConstInfinity.World Base Const,
          W ∈ HenkinConstInfinity.contextDenote
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
          ¬ HenkinConstInfinity.modelsFrom
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const) φ)
                (HenkinConstInfinity.emptyClosedSubst Base Const))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  constructor
  · intro hValid
    exact
      provable_of_liftBase_canonical_counterworld
        (Base := Base)
        (Const := Const)
        hBridge
        hCanonicalCounter
        hValid
  · exact validFrom_of_provable (Base := Base) (Const := Const)

end PlainIntuitionistic

end Mettapedia.Logic.HOL
