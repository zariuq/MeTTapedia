import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ExtendedSignatureBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Native parameterized extension of a constant signature by a local context.

This is the Codex-side replacement for the archived shim-backed parameter route:
original constants remain available through `Sum.inl`, and local world
parameters are carried by `Sum.inr`. -/
def ParamConst (Const : Ty Base → Type v) (Gamma : Ctx Base) (tau : Ty Base) :
    Type (max u v) :=
  Const tau ⊕ Var (Base := Base) Gamma tau

namespace CompletenessFrontier

/-- Embed the original constant signature into a native parameterized
signature. -/
abbrev paramEmbedding (Gamma : Ctx Base) :
    ∀ {tau : Ty Base}, Const tau -> ParamConst (Base := Base) Const Gamma tau :=
  fun {_} c => Sum.inl c

/-- Lift a closed frontier into the native parameterized signature over the
local context `Gamma`. -/
abbrev toParam (F : CompletenessFrontier Const []) (Gamma : Ctx Base) :
    CompletenessFrontier (ParamConst (Base := Base) Const Gamma) [] :=
  F.mapConstants (Const' := ParamConst (Base := Base) Const Gamma)
    (paramEmbedding (Base := Base) (Const := Const) Gamma)

/-- Retract the native empty-context parameterized signature back to the
original constant signature by eliminating the impossible variable summand. -/
abbrev emptyParamRetraction :
    ∀ {tau : Ty Base}, ParamConst (Base := Base) Const [] tau -> Const tau
  | _, Sum.inl c => c
  | _, Sum.inr v => nomatch v

/-- Closed theories over the native empty-context parameterized signature can
be built as preimages along `emptyParamRetraction`. -/
abbrev emptyParamTheorySet (U : ClosedTheorySet Const) :
    ClosedTheorySet (ParamConst (Base := Base) Const []) :=
  fun psi =>
    Mettapedia.Logic.HOL.mapClosedFormula
      (emptyParamRetraction (Base := Base) (Const := Const)) psi ∈ U

/-- Any original prime separating extension induces a genuine native
parameterized prime separating extension at empty context by pulling back along
`emptyParamRetraction`. -/
def toEmptyParamPrimeSeparatingExtension
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U) :
    PrimeSeparatingExtension
      (Const := ParamConst (Base := Base) Const [])
      (F.toParam [])
      (emptyParamTheorySet (Base := Base) (Const := Const) U) := by
  refine
    { contains_antecedents := ?_
      closed := ?_
      consistent := ?_
      prime_or := ?_
      omits_succedent := ?_ }
  · intro psi hpsi
    rcases List.mem_map.mp hpsi with ⟨chi, hchi, rfl⟩
    change
      Mettapedia.Logic.HOL.mapClosedFormula
        (emptyParamRetraction (Base := Base) (Const := Const))
        (Mettapedia.Logic.HOL.mapClosedFormula
          (paramEmbedding (Base := Base) (Const := Const) []) chi) ∈ U
    simpa [Mettapedia.Logic.HOL.mapClosedFormula,
      CompletenessFrontier.emptyParamRetraction,
      CompletenessFrontier.paramEmbedding] using hFU.contains_antecedents hchi
  · intro psi hpsi
    rcases hpsi with ⟨Gamma, hGamma, hDer⟩
    apply hFU.closed
    refine ClosedTheorySet.provable_of_closedTheory
      (Const := Const)
      (T := U)
      (Δ := Gamma.map (Mettapedia.Logic.HOL.mapClosedFormula
        (emptyParamRetraction (Base := Base) (Const := Const)))) ?_ ?_
    · intro chi hchi
      rcases List.mem_map.mp hchi with ⟨theta, htheta, rfl⟩
      exact hGamma theta htheta
    · simpa [Mettapedia.Logic.HOL.mapClosedFormula] using
        (ExtDerivation.closedTheory_mapConst
          (Base := Base)
          (Const := ParamConst (Base := Base) Const [])
          (Const' := Const)
          (f := emptyParamRetraction (Base := Base) (Const := Const))
          (Δ := Gamma)
          (φ := psi)
          hDer)
  · intro hInconsistent
    apply hFU.consistent
    rcases hInconsistent with ⟨Gamma, hGamma, hDer⟩
    refine ClosedTheorySet.provable_of_closedTheory
      (Const := Const)
      (T := U)
      (Δ := Gamma.map (Mettapedia.Logic.HOL.mapClosedFormula
        (emptyParamRetraction (Base := Base) (Const := Const)))) ?_ ?_
    · intro chi hchi
      rcases List.mem_map.mp hchi with ⟨theta, htheta, rfl⟩
      exact hGamma theta htheta
    · exact
        (ExtDerivation.closedTheory_mapConst
          (Base := Base)
          (Const := ParamConst (Base := Base) Const [])
          (Const' := Const)
          (f := emptyParamRetraction (Base := Base) (Const := Const))
          (Δ := Gamma)
          (φ := (.bot : ClosedFormula (ParamConst (Base := Base) Const [])))
          hDer)
  · intro phi psi hOr
    have hOr' :
        (.or
          (Mettapedia.Logic.HOL.mapClosedFormula
            (emptyParamRetraction (Base := Base) (Const := Const)) phi)
            (Mettapedia.Logic.HOL.mapClosedFormula
            (emptyParamRetraction (Base := Base) (Const := Const)) psi)
            : ClosedFormula Const) ∈ U := by
      exact hOr
    rcases hFU.prime_or hOr' with hphi | hpsi
    · left
      exact hphi
    · right
      exact hpsi
  · intro hSucc
    change
      Mettapedia.Logic.HOL.mapClosedFormula
        (emptyParamRetraction (Base := Base) (Const := Const))
        ((F.toParam []).succedent) ∈ U at hSucc
    exact hFU.omits_succedent <| by
      simpa [CompletenessFrontier.toParam,
        Mettapedia.Logic.HOL.mapClosedFormula,
        CompletenessFrontier.emptyParamRetraction,
        CompletenessFrontier.paramEmbedding] using hSucc

/-- The existential witness field transports directly along the native empty
parameter retraction. -/
theorem emptyParamTheorySet_existsWitness
    {U : ClosedTheorySet Const}
    (hExistsWitness :
      ∀ {sigma : Ty Base} {psi : Formula Const [sigma]},
        (.ex psi : ClosedFormula Const) ∈ U ->
          ∃ t : ClosedTerm Const sigma, instantiate (Base := Base) t psi ∈ U) :
    ∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const []) [sigma]},
      (.ex psi : ClosedFormula (ParamConst (Base := Base) Const [])) ∈
          emptyParamTheorySet (Base := Base) (Const := Const) U ->
        ∃ t : ClosedTerm (ParamConst (Base := Base) Const []) sigma,
          instantiate (Base := Base) t psi ∈
            emptyParamTheorySet (Base := Base) (Const := Const) U := by
  intro sigma psi hEx
  have hEx' :
      (.ex (Mettapedia.Logic.HOL.mapConst
        (emptyParamRetraction (Base := Base) (Const := Const)) psi)
          : ClosedFormula Const) ∈ U := by
    exact hEx
  rcases hExistsWitness hEx' with ⟨t, ht⟩
  refine ⟨Mettapedia.Logic.HOL.mapConst
    (paramEmbedding (Base := Base) (Const := Const) [])
    t, ?_⟩
  change
    Mettapedia.Logic.HOL.mapClosedFormula
      (emptyParamRetraction (Base := Base) (Const := Const))
      (instantiate (Base := Base)
        (Mettapedia.Logic.HOL.mapConst
          (paramEmbedding (Base := Base) (Const := Const) [])
          t)
        psi) ∈ U
  simpa [Mettapedia.Logic.HOL.mapClosedFormula,
    emptyParamRetraction,
    paramEmbedding] using ht

/-- The universal counterexample field transports directly along the native
empty parameter retraction. -/
theorem emptyParamTheorySet_allCounterexample
    {U : ClosedTheorySet Const}
    (hAllCounterexample :
      ∀ {sigma : Ty Base} {psi : Formula Const [sigma]},
        (.all psi : ClosedFormula Const) ∉ U ->
          ∃ t : ClosedTerm Const sigma, instantiate (Base := Base) t psi ∉ U) :
    ∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const []) [sigma]},
      (.all psi : ClosedFormula (ParamConst (Base := Base) Const [])) ∉
          emptyParamTheorySet (Base := Base) (Const := Const) U ->
        ∃ t : ClosedTerm (ParamConst (Base := Base) Const []) sigma,
          instantiate (Base := Base) t psi ∉
            emptyParamTheorySet (Base := Base) (Const := Const) U := by
  intro sigma psi hAll
  have hAll' :
      (.all (Mettapedia.Logic.HOL.mapConst
        (emptyParamRetraction (Base := Base) (Const := Const)) psi)
          : ClosedFormula Const) ∉ U := by
    intro hMem
    exact hAll hMem
  rcases hAllCounterexample hAll' with ⟨t, ht⟩
  refine ⟨Mettapedia.Logic.HOL.mapConst
    (paramEmbedding (Base := Base) (Const := Const) [])
    t, ?_⟩
  intro hMem
  change
    Mettapedia.Logic.HOL.mapClosedFormula
      (emptyParamRetraction (Base := Base) (Const := Const))
      (instantiate (Base := Base)
        (Mettapedia.Logic.HOL.mapConst
          (paramEmbedding (Base := Base) (Const := Const) [])
          t)
        psi) ∈ U at hMem
  exact ht <| by
    simpa [Mettapedia.Logic.HOL.mapClosedFormula,
      emptyParamRetraction,
      paramEmbedding] using hMem

theorem top_mem_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U) :
    (.top : ClosedFormula Const) ∈ U :=
  hFU.mem_of_setProvable
    (ClosedTheorySet.provable_top (Const := Const) F.antecedentTheorySet)

theorem bot_not_mem_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U) :
    (.bot : ClosedFormula Const) ∉ U := by
  intro hBot
  exact hFU.consistent (ClosedTheorySet.provable_of_mem (Const := Const) hBot)

end CompletenessFrontier

namespace HintikkaSet

/-- To prove a predicate on true formulas of the closed hull, it suffices to
prove it on the staged formulas and separately on `⊤`, which is the only new
true formula inserted by `close`. -/
theorem true_mem_close_of_true_mem
    {H : HintikkaSet Const []}
    {P : ClosedFormula Const → Prop}
    (hTop : P (.top : ClosedFormula Const))
    (hTrue : ∀ {phi : ClosedFormula Const}, (Sign.trueE, phi) ∈ H.formulas -> P phi)
    {phi : ClosedFormula Const}
    (hphi : (Sign.trueE, phi) ∈ H.close.formulas) :
    P phi := by
  have hphi' : phi = (.top : ClosedFormula Const) ∨ (Sign.trueE, phi) ∈ H.formulas := by
    rw [HintikkaSet.close] at hphi
    rcases List.mem_cons.mp hphi with hTop | hRest
    · cases hTop
      exact Or.inl rfl
    rcases List.mem_cons.mp hRest with hBot | hTail
    · cases hBot
    · exact Or.inr hTail
  rcases hphi' with rfl | hphi'
  · exact hTop
  · exact hTrue hphi'

/-- To prove a predicate on false formulas of the closed hull, it suffices to
prove it on the staged formulas and separately on `⊥`, which is the only new
false formula inserted by `close`. -/
theorem false_mem_close_of_false_mem
    {H : HintikkaSet Const []}
    {P : ClosedFormula Const → Prop}
    (hBot : P (.bot : ClosedFormula Const))
    (hFalse : ∀ {phi : ClosedFormula Const}, (Sign.falseE, phi) ∈ H.formulas -> P phi)
    {phi : ClosedFormula Const}
    (hphi : (Sign.falseE, phi) ∈ H.close.formulas) :
    P phi := by
  have hphi' : phi = (.bot : ClosedFormula Const) ∨ (Sign.falseE, phi) ∈ H.formulas := by
    rw [HintikkaSet.close] at hphi
    rcases List.mem_cons.mp hphi with hTop | hRest
    · cases hTop
    rcases List.mem_cons.mp hRest with hBot | hTail
    · cases hBot
      exact Or.inl rfl
    · exact Or.inr hTail
  rcases hphi' with rfl | hphi'
  · exact hBot
  · exact hFalse hphi'

end HintikkaSet

namespace CompletenessFrontier

/-- Native Codex-side parameterized root counterworld.

This is the chosen general-route object for the live branch: a world over a
parameterized signature together with containment of the lifted hypotheses and
omission of the lifted conclusion. No archived `ParamCompleteness` bridge is
imported or required here. -/
structure ParamRootCounterworld (F : CompletenessFrontier Const []) where
  Gamma : Ctx Base
  world : ClosedTheorySet.World (ParamConst (Base := Base) Const Gamma)
  hyps :
    ∀ {psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)},
      psi ∈ (F.toParam Gamma).antecedents -> psi ∈ world.carrier
  not_concl :
    (F.toParam Gamma).succedent ∉ world.carrier

/-- Proposition-level packaging of the native Codex-side parameterized root
counterworld boundary. -/
abbrev HasParamRootCounterworld
    (Base : Type u) (Const : Ty Base → Type v)
    (Delta : List (ClosedFormula Const)) (phi : ClosedFormula Const) : Prop :=
  Nonempty
    (ParamRootCounterworld (Base := Base) (Const := Const)
      { antecedents := Delta, succedent := phi })

/-- Native Codex-side parameterized counterworld bridge.

Any future general completeness construction should target this boundary rather
than the obstructed broad HInf reflection seam. -/
structure ParamRootCounterworldBridge (Base : Type u) (Const : Ty Base → Type v) where
  hasParamRootCounterworld_of_not_provable :
    ∀ {Delta : List (ClosedFormula Const)} {phi : ClosedFormula Const},
      ¬ ExtDerivation Const Delta phi ->
        HasParamRootCounterworld Base Const Delta phi

namespace ParamRootCounterworld

/-- A native parameterized root counterworld yields the mapped prime-separating
extension consumed by the generic extended-signature pullback layer. -/
def toMappedPrimeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : ParamRootCounterworld (Base := Base) (Const := Const) F) :
    PrimeSeparatingExtension
      (Const := ParamConst (Base := Base) Const C.Gamma)
      (F.toParam C.Gamma)
      C.world.carrier :=
  { contains_antecedents := C.hyps
    closed := C.world.closed
    consistent := C.world.consistent
    prime_or := C.world.prime_or
    omits_succedent := C.not_concl }

/-- If a mapped prime-separating extension over a native parameterized
signature already has the two quantifier fields needed by `toWorld`, it
upgrades directly to a native Codex-side parameterized root counterworld. -/
def ofPrimeSeparatingExtension
    {F : CompletenessFrontier Const []}
    {Gamma : Ctx Base}
    {U : ClosedTheorySet (ParamConst (Base := Base) Const Gamma)}
    (hFU :
      PrimeSeparatingExtension
        (Const := ParamConst (Base := Base) Const Gamma)
        (F.toParam Gamma)
        U)
    (hExistsWitness :
      ∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
        (.ex psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∈ U ->
          ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
            instantiate (Base := Base) t psi ∈ U)
    (hAllCounterexample :
      ∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
        (.all psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∉ U ->
          ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
            instantiate (Base := Base) t psi ∉ U) :
    ParamRootCounterworld (Base := Base) (Const := Const) F :=
  { Gamma := Gamma
    world := hFU.toWorld hExistsWitness hAllCounterexample
    hyps := hFU.contains_antecedents
    not_concl := hFU.omits_succedent }

/-- Any native parameterized root counterworld already refutes native
derivability of the original frontier. -/
theorem not_derivable
    {F : CompletenessFrontier Const []}
    (C : ParamRootCounterworld (Base := Base) (Const := Const) F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact F.not_derivable_of_mapped_world_counterexample
    (Const' := ParamConst (Base := Base) Const C.Gamma)
    (f := paramEmbedding (Base := Base) (Const := Const) C.Gamma)
    (W := C.world)
    (fun psi hpsi => C.hyps hpsi)
    C.not_concl

end ParamRootCounterworld

/-- Compatibility alias matching the older consumer theorem name while now
targeting the native Codex-side parameterized root counterworld object. -/
theorem mapped_primeSeparatingExtension_of_paramRootCounterworld
    {F : CompletenessFrontier Const []}
    (C : ParamRootCounterworld (Base := Base) (Const := Const) F) :
    PrimeSeparatingExtension
      (Const := ParamConst (Base := Base) Const C.Gamma)
      (F.toParam C.Gamma)
      C.world.carrier :=
  C.toMappedPrimeSeparatingExtension

/-- Once the native parameterized route produces a root counterworld, the
generic extended-signature pullback immediately refutes native derivability of
the original frontier. -/
theorem not_derivable_of_paramRootCounterworld
    {F : CompletenessFrontier Const []}
    (C : ParamRootCounterworld (Base := Base) (Const := Const) F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  C.not_derivable

/-- Under any direct native parameterized root-counterworld bridge, extensional
non-provability already refutes native derivability: the bridge produces the
counterworld, and the previous theorem consumes it honestly. -/
theorem not_derivable_of_not_extDerivation_of_paramRootCounterworldBridge
    {F : CompletenessFrontier Const []}
    (B : ParamRootCounterworldBridge Base Const)
    (hNot : ¬ ExtDerivation Const F.antecedents F.succedent) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  rcases B.hasParamRootCounterworld_of_not_provable hNot with ⟨C⟩
  exact C.not_derivable

end CompletenessFrontier

namespace CertifiedHeadPriorityCompletion

/-- The exact native canonical-route target above the certified completion
layer: a parameterized prime separating extension agreeing with the certified
closed Hintikka hull and already carrying the two quantifier fields needed to
upgrade to a world.

This deliberately stops one step before a full
`CandidateParamRootCounterworld`: it exposes the production-side data that the
native search/canonical route still needs to construct. -/
structure CandidateParamPrimeExtension
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F) where
  Gamma : Ctx Base
  carrier : ClosedTheorySet (ParamConst (Base := Base) Const Gamma)
  extension :
    CompletenessFrontier.PrimeSeparatingExtension
      (Const := ParamConst (Base := Base) Const Gamma)
      (F.toParam Gamma)
      carrier
  exists_witness :
    ∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
      (.ex psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∈ carrier ->
        ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
          instantiate (Base := Base) t psi ∈ carrier
  all_counterexample :
    ∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
      (.all psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∉ carrier ->
        ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
          instantiate (Base := Base) t psi ∉ carrier
  true_mem :
    ∀ {phi : ClosedFormula Const},
      (Sign.trueE, phi) ∈ C.closedHintikka.formulas ->
        Mettapedia.Logic.HOL.mapClosedFormula
          (CompletenessFrontier.paramEmbedding
            (Base := Base) (Const := Const) Gamma) phi ∈ carrier
  false_not_mem :
    ∀ {phi : ClosedFormula Const},
      (Sign.falseE, phi) ∈ C.closedHintikka.formulas ->
        Mettapedia.Logic.HOL.mapClosedFormula
          (CompletenessFrontier.paramEmbedding
            (Base := Base) (Const := Const) Gamma) phi ∉ carrier

namespace CandidateParamPrimeExtension

/-- Package raw parameterized prime-extension data together with certified
closed-hull agreement as the canonical production-side target for the native
parameterized route. -/
def ofPrimeExtensionAgreement
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    {Gamma : Ctx Base}
    (carrier : ClosedTheorySet (ParamConst (Base := Base) Const Gamma))
    (extension :
      CompletenessFrontier.PrimeSeparatingExtension
        (Const := ParamConst (Base := Base) Const Gamma)
        (F.toParam Gamma)
        carrier)
    (exists_witness :
      ∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
        (.ex psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∈ carrier ->
          ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
            instantiate (Base := Base) t psi ∈ carrier)
    (all_counterexample :
      ∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
        (.all psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∉ carrier ->
          ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
            instantiate (Base := Base) t psi ∉ carrier)
    (true_mem :
      ∀ {phi : ClosedFormula Const},
        (Sign.trueE, phi) ∈ C.closedHintikka.formulas ->
          Mettapedia.Logic.HOL.mapClosedFormula
            (CompletenessFrontier.paramEmbedding
              (Base := Base) (Const := Const) Gamma) phi ∈ carrier)
    (false_not_mem :
      ∀ {phi : ClosedFormula Const},
        (Sign.falseE, phi) ∈ C.closedHintikka.formulas ->
          Mettapedia.Logic.HOL.mapClosedFormula
            (CompletenessFrontier.paramEmbedding
              (Base := Base) (Const := Const) Gamma) phi ∉ carrier) :
    CandidateParamPrimeExtension (Base := Base) (Const := Const) C :=
  { Gamma := Gamma
    carrier := carrier
    extension := extension
    exists_witness := exists_witness
    all_counterexample := all_counterexample
    true_mem := true_mem
    false_not_mem := false_not_mem }

end CandidateParamPrimeExtension

/-- A native parameterized root world that already agrees with the closed
Hintikka hull of a certified completion.

This is the direct parameterized analogue of the existing
`CandidateClosedHintikkaSemantics` packaging: instead of semilocal truth values,
it records literal world membership/non-membership for the closed formulas
staged by the certified completion. -/
structure CandidateParamRootCounterworld
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F) where
  Gamma : Ctx Base
  world : ClosedTheorySet.World (ParamConst (Base := Base) Const Gamma)
  true_mem :
    ∀ {phi : ClosedFormula Const},
      (Sign.trueE, phi) ∈ C.closedHintikka.formulas ->
        Mettapedia.Logic.HOL.mapClosedFormula
          (CompletenessFrontier.paramEmbedding
            (Base := Base) (Const := Const) Gamma) phi ∈ world.carrier
  false_not_mem :
    ∀ {phi : ClosedFormula Const},
      (Sign.falseE, phi) ∈ C.closedHintikka.formulas ->
        Mettapedia.Logic.HOL.mapClosedFormula
          (CompletenessFrontier.paramEmbedding
            (Base := Base) (Const := Const) Gamma) phi ∉ world.carrier

namespace CandidateParamRootCounterworld

/-- Package a raw parameterized world together with agreement on the certified
closed Hintikka hull as a certified candidate parameterized root counterworld. -/
def ofWorldAgreement
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    {Gamma : Ctx Base}
    (world : ClosedTheorySet.World (ParamConst (Base := Base) Const Gamma))
    (true_mem :
      ∀ {phi : ClosedFormula Const},
        (Sign.trueE, phi) ∈ C.closedHintikka.formulas ->
          Mettapedia.Logic.HOL.mapClosedFormula
            (CompletenessFrontier.paramEmbedding
              (Base := Base) (Const := Const) Gamma) phi ∈ world.carrier)
    (false_not_mem :
      ∀ {phi : ClosedFormula Const},
        (Sign.falseE, phi) ∈ C.closedHintikka.formulas ->
          Mettapedia.Logic.HOL.mapClosedFormula
            (CompletenessFrontier.paramEmbedding
              (Base := Base) (Const := Const) Gamma) phi ∉ world.carrier) :
    CandidateParamRootCounterworld (Base := Base) (Const := Const) C :=
  { Gamma := Gamma
    world := world
    true_mem := true_mem
    false_not_mem := false_not_mem }

/-- Any certified parameterized candidate world already packages the native
root-counterworld object for the frontier. -/
def toParamRootCounterworld
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamRootCounterworld (Base := Base) (Const := Const) C) :
    CompletenessFrontier.ParamRootCounterworld (Base := Base) (Const := Const) F :=
  { Gamma := W.Gamma
    world := W.world
    hyps := by
      intro psi hpsi
      rcases List.mem_map.mp hpsi with ⟨chi, hchi, rfl⟩
      exact W.true_mem <| by
        simpa [CertifiedHeadPriorityCompletion.toClosedLocalHintikkaCertificate_formulas] using
          (C.toClosedLocalHintikkaCertificate.true_mem hchi)
    not_concl := by
      exact W.false_not_mem <| by
        simpa [CertifiedHeadPriorityCompletion.toClosedLocalHintikkaCertificate_formulas] using
          C.toClosedLocalHintikkaCertificate.false_mem }

/-- A certified parameterized candidate world therefore already refutes native
derivability of the original frontier. -/
theorem not_derivable
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamRootCounterworld (Base := Base) (Const := Const) C) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  W.toParamRootCounterworld.not_derivable

end CandidateParamRootCounterworld

namespace CandidateParamPrimeExtension

/-- A certified parameterized prime extension upgrades directly to the
certified parameterized root-counterworld package. -/
def toCandidateParamRootCounterworld
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeExtension (Base := Base) (Const := Const) C) :
    CandidateParamRootCounterworld (Base := Base) (Const := Const) C :=
  CandidateParamRootCounterworld.ofWorldAgreement
    (Base := Base) (Const := Const) C
    (W.extension.toWorld W.exists_witness W.all_counterexample)
    W.true_mem
    W.false_not_mem

/-- A certified parameterized prime extension therefore already packages the
native root-counterworld boundary. -/
def toParamRootCounterworld
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeExtension (Base := Base) (Const := Const) C) :
    CompletenessFrontier.ParamRootCounterworld (Base := Base) (Const := Const) F :=
  W.toCandidateParamRootCounterworld.toParamRootCounterworld

/-- A certified parameterized prime extension therefore already refutes native
derivability of the original frontier. -/
theorem not_derivable
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeExtension (Base := Base) (Const := Const) C) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  W.toParamRootCounterworld.not_derivable

end CandidateParamPrimeExtension

/-- A raw parameterized world that agrees with the certified closed Hintikka
hull can be consumed directly into the certified candidate-world package. -/
theorem exists_candidateParamRootCounterworld_of_exists_worldAgreement
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      ∃ (Gamma : Ctx Base) (world : ClosedTheorySet.World (ParamConst (Base := Base) Const Gamma)),
        (∀ {phi : ClosedFormula Const},
          (Sign.trueE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∈ world.carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.falseE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∉ world.carrier)) :
    Nonempty
      (CandidateParamRootCounterworld (Base := Base) (Const := Const) C) := by
  rcases hW with ⟨Gamma, world, hTrue, hFalse⟩
  exact ⟨CandidateParamRootCounterworld.ofWorldAgreement
    (Base := Base) (Const := Const) C world hTrue hFalse⟩

/-- Raw parameterized prime-extension data can be consumed directly into the
certified production-side package for the native route. -/
theorem exists_candidateParamPrimeExtension_of_exists_primeExtensionAgreement
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      ∃ (Gamma : Ctx Base)
        (carrier : ClosedTheorySet (ParamConst (Base := Base) Const Gamma)),
        CompletenessFrontier.PrimeSeparatingExtension
          (Const := ParamConst (Base := Base) Const Gamma)
          (F.toParam Gamma)
          carrier ∧
        (∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
          (.ex psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∈ carrier ->
            ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
              instantiate (Base := Base) t psi ∈ carrier) ∧
        (∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
          (.all psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∉ carrier ->
            ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
              instantiate (Base := Base) t psi ∉ carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.trueE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∈ carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.falseE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∉ carrier)) :
    Nonempty
      (CandidateParamPrimeExtension (Base := Base) (Const := Const) C) := by
  rcases hW with ⟨Gamma, carrier, hExt, hExists, hAll, hTrue, hFalse⟩
  exact ⟨CandidateParamPrimeExtension.ofPrimeExtensionAgreement
    (Base := Base) (Const := Const) C carrier hExt hExists hAll hTrue hFalse⟩

/-- Existence of a certified parameterized prime extension already yields the
certified parameterized root-counterworld package. -/
theorem exists_candidateParamRootCounterworld_of_exists_candidateParamPrimeExtension
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeExtension (Base := Base) (Const := Const) C)) :
    Nonempty
      (CandidateParamRootCounterworld (Base := Base) (Const := Const) C) := by
  rcases hW with ⟨W⟩
  exact ⟨W.toCandidateParamRootCounterworld⟩

/-- Existence of a certified parameterized candidate world already yields the
native root-counterworld boundary for the frontier. -/
theorem exists_paramRootCounterworld_of_exists_candidateParamRootCounterworld
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (CandidateParamRootCounterworld (Base := Base) (Const := Const) C)) :
    Nonempty (CompletenessFrontier.ParamRootCounterworld (Base := Base) (Const := Const) F) := by
  rcases hW with ⟨W⟩
  exact ⟨W.toParamRootCounterworld⟩

/-- Existence of a certified parameterized prime extension already yields the
native root-counterworld boundary for the frontier. -/
theorem exists_paramRootCounterworld_of_exists_candidateParamPrimeExtension
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeExtension (Base := Base) (Const := Const) C)) :
    Nonempty (CompletenessFrontier.ParamRootCounterworld (Base := Base) (Const := Const) F) := by
  rcases hW with ⟨W⟩
  exact ⟨W.toParamRootCounterworld⟩

/-- Existence of a certified parameterized candidate world already refutes
native derivability of the frontier. -/
theorem not_derivable_of_exists_candidateParamRootCounterworld
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (CandidateParamRootCounterworld (Base := Base) (Const := Const) C)) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  rcases hW with ⟨W⟩
  exact W.not_derivable

/-- Existence of a certified parameterized prime extension already refutes
native derivability of the frontier. -/
theorem not_derivable_of_exists_candidateParamPrimeExtension
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeExtension (Base := Base) (Const := Const) C)) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  rcases hW with ⟨W⟩
  exact W.not_derivable

/-- Raw parameterized prime-extension data therefore already refutes native
derivability of the frontier. -/
theorem not_derivable_of_exists_primeExtensionAgreement
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      ∃ (Gamma : Ctx Base)
        (carrier : ClosedTheorySet (ParamConst (Base := Base) Const Gamma)),
        CompletenessFrontier.PrimeSeparatingExtension
          (Const := ParamConst (Base := Base) Const Gamma)
          (F.toParam Gamma)
          carrier ∧
        (∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
          (.ex psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∈ carrier ->
            ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
              instantiate (Base := Base) t psi ∈ carrier) ∧
        (∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
          (.all psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∉ carrier ->
            ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
              instantiate (Base := Base) t psi ∉ carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.trueE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∈ carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.falseE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∉ carrier)) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  C.not_derivable_of_exists_candidateParamPrimeExtension <|
    C.exists_candidateParamPrimeExtension_of_exists_primeExtensionAgreement hW

/-- A raw agreeing parameterized world therefore already refutes native
derivability of the frontier. -/
theorem not_derivable_of_exists_worldAgreement
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      ∃ (Gamma : Ctx Base) (world : ClosedTheorySet.World (ParamConst (Base := Base) Const Gamma)),
        (∀ {phi : ClosedFormula Const},
          (Sign.trueE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∈ world.carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.falseE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∉ world.carrier)) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  rcases hW with ⟨Gamma, world, hTrue, hFalse⟩
  exact C.not_derivable_of_exists_mapped_worldAgreement
    (Const' := ParamConst (Base := Base) Const Gamma)
    (f := CompletenessFrontier.paramEmbedding
      (Base := Base) (Const := Const) Gamma)
    ⟨world, hTrue, hFalse⟩

end CertifiedHeadPriorityCompletion

namespace CertifiedCountermodelCandidate

/-- Candidate-level alias for the certified production-side parameterized prime
extension package. -/
abbrev CandidateParamPrimeExtension
    (C : CertifiedCountermodelCandidate Const []) :=
  CertifiedHeadPriorityCompletion.CandidateParamPrimeExtension
    (C := C.toCertifiedCompletion)

/-- Candidate-level alias for the certified parameterized root-counterworld
package. -/
abbrev CandidateParamRootCounterworld
    (C : CertifiedCountermodelCandidate Const []) :=
  CertifiedHeadPriorityCompletion.CandidateParamRootCounterworld
    (C := C.toCertifiedCompletion)

/-- Raw parameterized world agreement can be consumed directly at the certified
candidate layer. -/
theorem exists_candidateParamRootCounterworld_of_exists_worldAgreement
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      ∃ (Gamma : Ctx Base)
        (world : ClosedTheorySet.World (ParamConst (Base := Base) Const Gamma)),
        (∀ {phi : ClosedFormula Const},
          (Sign.trueE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∈ world.carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.falseE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∉ world.carrier)) :
    Nonempty (CandidateParamRootCounterworld (Base := Base) (Const := Const) C) := by
  exact
    CertifiedHeadPriorityCompletion.exists_candidateParamRootCounterworld_of_exists_worldAgreement
      (C := C.toCertifiedCompletion) hW

/-- Raw parameterized prime-extension agreement can be consumed directly at the
certified candidate layer. -/
theorem exists_candidateParamPrimeExtension_of_exists_primeExtensionAgreement
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      ∃ (Gamma : Ctx Base)
        (carrier : ClosedTheorySet (ParamConst (Base := Base) Const Gamma)),
        CompletenessFrontier.PrimeSeparatingExtension
          (Const := ParamConst (Base := Base) Const Gamma)
          (C.frontier.toParam Gamma)
          carrier ∧
        (∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
          (.ex psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∈ carrier ->
            ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
              instantiate (Base := Base) t psi ∈ carrier) ∧
        (∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
          (.all psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∉ carrier ->
            ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
              instantiate (Base := Base) t psi ∉ carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.trueE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∈ carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.falseE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∉ carrier)) :
    Nonempty (CandidateParamPrimeExtension (Base := Base) (Const := Const) C) := by
  exact
    CertifiedHeadPriorityCompletion.exists_candidateParamPrimeExtension_of_exists_primeExtensionAgreement
      (C := C.toCertifiedCompletion) hW

/-- A certified candidate parameterized world already yields the native
root-counterworld boundary for the frontier. -/
theorem exists_paramRootCounterworld_of_exists_candidateParamRootCounterworld
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty (CandidateParamRootCounterworld (Base := Base) (Const := Const) C)) :
    Nonempty
      (CompletenessFrontier.ParamRootCounterworld
        (Base := Base) (Const := Const) C.frontier) := by
  simpa [CertifiedCountermodelCandidate.toCertifiedCompletion] using
    (CertifiedHeadPriorityCompletion.exists_paramRootCounterworld_of_exists_candidateParamRootCounterworld
      (C := C.toCertifiedCompletion) hW)

/-- Existence of a certified candidate parameterized prime extension already
yields the certified candidate parameterized root-counterworld package. -/
theorem exists_candidateParamRootCounterworld_of_exists_candidateParamPrimeExtension
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty (CandidateParamPrimeExtension (Base := Base) (Const := Const) C)) :
    Nonempty (CandidateParamRootCounterworld (Base := Base) (Const := Const) C) := by
  exact
    CertifiedHeadPriorityCompletion.exists_candidateParamRootCounterworld_of_exists_candidateParamPrimeExtension
      (C := C.toCertifiedCompletion) hW

/-- A certified candidate parameterized prime extension already yields the
native root-counterworld boundary for the frontier. -/
theorem exists_paramRootCounterworld_of_exists_candidateParamPrimeExtension
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty (CandidateParamPrimeExtension (Base := Base) (Const := Const) C)) :
    Nonempty
      (CompletenessFrontier.ParamRootCounterworld
        (Base := Base) (Const := Const) C.frontier) := by
  simpa [CertifiedCountermodelCandidate.toCertifiedCompletion] using
    (CertifiedHeadPriorityCompletion.exists_paramRootCounterworld_of_exists_candidateParamPrimeExtension
      (C := C.toCertifiedCompletion) hW)

/-- Existence of a certified candidate parameterized world already refutes
native derivability of the frontier. -/
theorem not_derivable_of_exists_candidateParamRootCounterworld
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty (CandidateParamRootCounterworld (Base := Base) (Const := Const) C)) :
    ¬ Derivable (Base := Base) (Const := Const) C.frontier.antecedents C.frontier.succedent := by
  simpa [CertifiedCountermodelCandidate.toCertifiedCompletion] using
    (CertifiedHeadPriorityCompletion.not_derivable_of_exists_candidateParamRootCounterworld
      (C := C.toCertifiedCompletion) hW)

/-- Existence of a certified candidate parameterized prime extension already
refutes native derivability of the frontier. -/
theorem not_derivable_of_exists_candidateParamPrimeExtension
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty (CandidateParamPrimeExtension (Base := Base) (Const := Const) C)) :
    ¬ Derivable (Base := Base) (Const := Const) C.frontier.antecedents C.frontier.succedent := by
  simpa [CertifiedCountermodelCandidate.toCertifiedCompletion] using
    (CertifiedHeadPriorityCompletion.not_derivable_of_exists_candidateParamPrimeExtension
      (C := C.toCertifiedCompletion) hW)

/-- Raw parameterized prime-extension agreement therefore already refutes
native derivability at the certified candidate layer. -/
theorem not_derivable_of_exists_primeExtensionAgreement
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      ∃ (Gamma : Ctx Base)
        (carrier : ClosedTheorySet (ParamConst (Base := Base) Const Gamma)),
        CompletenessFrontier.PrimeSeparatingExtension
          (Const := ParamConst (Base := Base) Const Gamma)
          (C.frontier.toParam Gamma)
          carrier ∧
        (∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
          (.ex psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∈ carrier ->
            ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
              instantiate (Base := Base) t psi ∈ carrier) ∧
        (∀ {sigma : Ty Base} {psi : Formula (ParamConst (Base := Base) Const Gamma) [sigma]},
          (.all psi : ClosedFormula (ParamConst (Base := Base) Const Gamma)) ∉ carrier ->
            ∃ t : ClosedTerm (ParamConst (Base := Base) Const Gamma) sigma,
              instantiate (Base := Base) t psi ∉ carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.trueE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∈ carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.falseE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∉ carrier)) :
    ¬ Derivable (Base := Base) (Const := Const) C.frontier.antecedents C.frontier.succedent := by
  exact C.not_derivable_of_exists_candidateParamPrimeExtension <|
    C.exists_candidateParamPrimeExtension_of_exists_primeExtensionAgreement hW

/-- Raw agreeing parameterized world data therefore already refutes native
derivability at the certified candidate layer. -/
theorem not_derivable_of_exists_worldAgreement
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      ∃ (Gamma : Ctx Base)
        (world : ClosedTheorySet.World (ParamConst (Base := Base) Const Gamma)),
        (∀ {phi : ClosedFormula Const},
          (Sign.trueE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∈ world.carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.falseE, phi) ∈ C.closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∉ world.carrier)) :
    ¬ Derivable (Base := Base) (Const := Const) C.frontier.antecedents C.frontier.succedent := by
  rcases hW with ⟨Gamma, world, hTrue, hFalse⟩
  exact C.not_derivable_of_exists_mapped_worldAgreement
    (Const' := ParamConst (Base := Base) Const Gamma)
    (f := CompletenessFrontier.paramEmbedding
      (Base := Base) (Const := Const) Gamma)
    ⟨world, hTrue, hFalse⟩

end CertifiedCountermodelCandidate

namespace SignedFormula

/-- Agreement of a signed closed formula with a closed theory-set. -/
def AgreesWithTheorySet
    (U : ClosedTheorySet Const) :
    SignedFormula Const [] → Prop
  | (Sign.trueE, phi) => phi ∈ U
  | (Sign.falseE, phi) => phi ∉ U

end SignedFormula

namespace SaturationSearchState.LocalBranchResolution

/-- A chosen local branch agrees with a closed theory-set when each formula it
adds has the matching membership/non-membership relation with that theory-set. -/
def AgreesWithTheorySet
    (U : ClosedTheorySet Const)
    (r : LocalBranchResolution Const []) : Prop :=
  ∀ {sf : SignedFormula Const []},
    sf ∈ LocalSaturationStep.additions r.step ->
      SignedFormula.AgreesWithTheorySet U sf

end SaturationSearchState.LocalBranchResolution

namespace DeterministicLocalSaturationStep

/-- A deterministic local saturation step agrees with a closed theory-set when
each formula it adds has the matching membership/non-membership relation with
that theory-set. -/
def AgreesWithTheorySet
    (U : ClosedTheorySet Const)
    (s : DeterministicLocalSaturationStep Const []) : Prop :=
  ∀ {sf : SignedFormula Const []},
    sf ∈ DeterministicLocalSaturationStep.additions s ->
      SignedFormula.AgreesWithTheorySet U sf

end DeterministicLocalSaturationStep

namespace SaturationSearchState.HeadPrioritySearchDerivation

/-- The initial frontier formulas already agree with any prime separating
extension over that frontier. -/
theorem agreesWithTheorySet_of_mem_initial
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    {sf : SignedFormula Const []}
    (hsf : sf ∈ (SaturationSearchState.initial F).hintikka.formulas) :
    SignedFormula.AgreesWithTheorySet U sf := by
  rcases List.mem_append.mp hsf with hsf | hsf
  · rcases List.mem_map.mp hsf with ⟨phi, hphi, rfl⟩
    exact hFU.contains_antecedents hphi
  · rcases List.mem_singleton.mp hsf with rfl
    exact hFU.omits_succedent

/-- A head-priority derivation is theory-set-guided when every local step it
chooses adds formulas already agreeing with that target theory-set. -/
def GuidedByTheorySet
    {F : CompletenessFrontier Const []}
    (U : ClosedTheorySet Const) :
    {S : SaturationSearchState Const []} ->
      HeadPrioritySearchDerivation F S -> Prop
  | _, .initial => True
  | _, .saturate D _ t =>
      GuidedByTheorySet U D ∧
        DeterministicLocalSaturationStep.AgreesWithTheorySet U t.step
  | _, .resolveHead D r _ =>
      GuidedByTheorySet U D ∧
        SaturationSearchState.LocalBranchResolution.AgreesWithTheorySet U r

/-- Any formula visible at the end of a theory-set-guided derivation already
agrees with the target theory-set. -/
theorem agreesWithTheorySet_of_mem
    {F : CompletenessFrontier Const []}
    {S : SaturationSearchState Const []}
    (D : HeadPrioritySearchDerivation F S)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hGuide : GuidedByTheorySet U D)
    {sf : SignedFormula Const []}
    (hsf : sf ∈ S.hintikka.formulas) :
    SignedFormula.AgreesWithTheorySet U sf := by
  induction D generalizing U sf with
  | initial =>
      exact agreesWithTheorySet_of_mem_initial (Const := Const) hFU hsf
  | @saturate S D hIdle t ih =>
      rcases hGuide with ⟨hGuideD, hGuideStep⟩
      have hsf' :
          sf ∈ DeterministicLocalSaturationStep.additions t.step ∨
            sf ∈ S.hintikka.formulas := by
        simpa [SaturationSearchState.applyLocalStep, HintikkaSet.saturateWithStep,
          HintikkaSet.insertAll, DeterministicLocalSaturationStep.additions] using hsf
      rcases hsf' with hAdd | hOld
      · exact hGuideStep hAdd
      · exact ih hFU hGuideD hOld
  | @resolveHead S D r hhead ih =>
      rcases hGuide with ⟨hGuideD, hGuideStep⟩
      have hsf' :
          sf ∈ LocalSaturationStep.additions r.step ∨
            sf ∈ S.hintikka.formulas := by
        simpa [SaturationSearchState.resolveHead, HintikkaSet.saturateWithStep,
          HintikkaSet.insertAll] using hsf
      rcases hsf' with hAdd | hOld
      · exact hGuideStep hAdd
      · exact ih hFU hGuideD hOld

theorem true_mem_of_guidedByTheorySet
    {F : CompletenessFrontier Const []}
    {S : SaturationSearchState Const []}
    (D : HeadPrioritySearchDerivation F S)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hGuide : GuidedByTheorySet U D)
    {phi : ClosedFormula Const}
    (hphi : (Sign.trueE, phi) ∈ S.hintikka.formulas) :
    phi ∈ U :=
  agreesWithTheorySet_of_mem (Const := Const) D hFU hGuide hphi

theorem false_mem_of_guidedByTheorySet
    {F : CompletenessFrontier Const []}
    {S : SaturationSearchState Const []}
    (D : HeadPrioritySearchDerivation F S)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hGuide : GuidedByTheorySet U D)
    {phi : ClosedFormula Const}
    (hphi : (Sign.falseE, phi) ∈ S.hintikka.formulas) :
    phi ∉ U :=
  agreesWithTheorySet_of_mem (Const := Const) D hFU hGuide hphi

end SaturationSearchState.HeadPrioritySearchDerivation

namespace SaturationSearchState.HeadPriorityCompletion

/-- Production theorem for the native parameterized route at empty context.

Given a compatible head-priority completion, an original prime separating
extension, the two original quantifier fields, and direct agreement between the
completion's staged Hintikka formulas and that extension, we can construct the
certified native `CandidateParamPrimeExtension` object itself. -/
def toCandidateParamPrimeExtensionOfPrimeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hExistsWitness :
      ∀ {sigma : Ty Base} {psi : Formula Const [sigma]},
        (.ex psi : ClosedFormula Const) ∈ U ->
          ∃ t : ClosedTerm Const sigma, instantiate (Base := Base) t psi ∈ U)
    (hAllCounterexample :
      ∀ {sigma : Ty Base} {psi : Formula Const [sigma]},
        (.all psi : ClosedFormula Const) ∉ U ->
          ∃ t : ClosedTerm Const sigma, instantiate (Base := Base) t psi ∉ U)
    (hTrue :
      ∀ {phi : ClosedFormula Const},
        (Sign.trueE, phi) ∈ C.state.hintikka.formulas -> phi ∈ U)
    (hFalse :
      ∀ {phi : ClosedFormula Const},
        (Sign.falseE, phi) ∈ C.state.hintikka.formulas -> phi ∉ U) :
    CertifiedHeadPriorityCompletion.CandidateParamPrimeExtension
      (Base := Base)
      (Const := Const)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) := by
  refine
    CertifiedHeadPriorityCompletion.CandidateParamPrimeExtension.ofPrimeExtensionAgreement
      (Base := Base)
      (Const := Const)
      (C := C.toCertifiedOfPrimeSeparatingExtension hCompat hFU)
      (carrier := CompletenessFrontier.emptyParamTheorySet (Base := Base) (Const := Const) U)
      (extension := CompletenessFrontier.toEmptyParamPrimeSeparatingExtension
        (Base := Base) (Const := Const) (F := F) hFU)
      ?_ ?_ ?_ ?_
  · exact CompletenessFrontier.emptyParamTheorySet_existsWitness
      (Base := Base) (Const := Const) hExistsWitness
  · exact CompletenessFrontier.emptyParamTheorySet_allCounterexample
      (Base := Base) (Const := Const) hAllCounterexample
  · intro phi hphi
    have hphi' : phi ∈ U := HintikkaSet.true_mem_close_of_true_mem
      (H := C.state.hintikka)
      (P := fun psi : ClosedFormula Const => psi ∈ U)
      (CompletenessFrontier.top_mem_of_primeSeparatingExtension
        (Base := Base) (Const := Const) (F := F) hFU)
      (fun {psi} hpsi => hTrue hpsi)
      (by
        simpa [SaturationSearchState.HeadPriorityCompletion.toCertifiedOfPrimeSeparatingExtension,
          SaturationSearchState.HeadPriorityCompletion.toCertified,
          CertifiedHeadPriorityCompletion.state,
          CertifiedHeadPriorityCompletion.hintikka,
          CertifiedHeadPriorityCompletion.closedHintikka] using hphi)
    change
      Mettapedia.Logic.HOL.mapClosedFormula
        (CompletenessFrontier.emptyParamRetraction (Base := Base) (Const := Const))
        (Mettapedia.Logic.HOL.mapClosedFormula
          (CompletenessFrontier.paramEmbedding (Base := Base) (Const := Const) [])
          phi) ∈ U
    simpa [Mettapedia.Logic.HOL.mapClosedFormula,
      CompletenessFrontier.emptyParamRetraction,
      CompletenessFrontier.paramEmbedding] using hphi'
  · intro phi hphi
    have hphi' : phi ∉ U := HintikkaSet.false_mem_close_of_false_mem
      (H := C.state.hintikka)
      (P := fun psi : ClosedFormula Const => psi ∉ U)
      (CompletenessFrontier.bot_not_mem_of_primeSeparatingExtension
        (Base := Base) (Const := Const) (F := F) hFU)
      (fun {psi} hpsi => hFalse hpsi)
      (by
        simpa [SaturationSearchState.HeadPriorityCompletion.toCertifiedOfPrimeSeparatingExtension,
          SaturationSearchState.HeadPriorityCompletion.toCertified,
          CertifiedHeadPriorityCompletion.state,
          CertifiedHeadPriorityCompletion.hintikka,
          CertifiedHeadPriorityCompletion.closedHintikka] using hphi)
    change
      Mettapedia.Logic.HOL.mapClosedFormula
        (CompletenessFrontier.emptyParamRetraction (Base := Base) (Const := Const))
        (Mettapedia.Logic.HOL.mapClosedFormula
          (CompletenessFrontier.paramEmbedding (Base := Base) (Const := Const) [])
          phi) ∉ U
    simpa [Mettapedia.Logic.HOL.mapClosedFormula,
      CompletenessFrontier.emptyParamRetraction,
      CompletenessFrontier.paramEmbedding] using hphi'

/-- The same production theorem can be driven by a theory-set-guided search
derivation, replacing the ad hoc staged-formula agreement hypotheses with a
single structural invariant on the chosen search steps. -/
def toCandidateParamPrimeExtensionOfPrimeSeparatingExtensionOfGuidedByTheorySet
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := Const) U C.derivation)
    (hExistsWitness :
      ∀ {sigma : Ty Base} {psi : Formula Const [sigma]},
        (.ex psi : ClosedFormula Const) ∈ U ->
          ∃ t : ClosedTerm Const sigma, instantiate (Base := Base) t psi ∈ U)
    (hAllCounterexample :
      ∀ {sigma : Ty Base} {psi : Formula Const [sigma]},
        (.all psi : ClosedFormula Const) ∉ U ->
          ∃ t : ClosedTerm Const sigma, instantiate (Base := Base) t psi ∉ U) :
    CertifiedHeadPriorityCompletion.CandidateParamPrimeExtension
      (Base := Base)
      (Const := Const)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) :=
  C.toCandidateParamPrimeExtensionOfPrimeSeparatingExtension
    (hCompat := hCompat)
    (hFU := hFU)
    (hExistsWitness := hExistsWitness)
    (hAllCounterexample := hAllCounterexample)
    (hTrue := fun hphi =>
      SaturationSearchState.HeadPrioritySearchDerivation.true_mem_of_guidedByTheorySet
        (Const := Const) C.derivation hFU hGuide hphi)
    (hFalse := fun hphi =>
      SaturationSearchState.HeadPrioritySearchDerivation.false_mem_of_guidedByTheorySet
        (Const := Const) C.derivation hFU hGuide hphi)

/-- The extensional non-provability route can now target the native
parameterized-world endpoint directly, provided the certified completion has a
parameterized world agreeing with its closed Hintikka hull. -/
theorem exists_paramRootCounterworld_of_exists_candidateParamRootCounterworld_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent)
    (hW :
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateParamRootCounterworld
          (Base := Base)
          (Const := Const)
          (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot))) :
    Nonempty (CompletenessFrontier.ParamRootCounterworld (Base := Base) (Const := Const) F) :=
  CertifiedHeadPriorityCompletion.exists_paramRootCounterworld_of_exists_candidateParamRootCounterworld
    (C := C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot) hW

/-- The extensional non-provability route can also target the native
parameterized root-counterworld boundary through the more production-side
parameterized prime-extension package. -/
theorem exists_paramRootCounterworld_of_exists_candidateParamPrimeExtension_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent)
    (hW :
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateParamPrimeExtension
          (Base := Base)
          (Const := Const)
          (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot))) :
    Nonempty (CompletenessFrontier.ParamRootCounterworld (Base := Base) (Const := Const) F) :=
  CertifiedHeadPriorityCompletion.exists_paramRootCounterworld_of_exists_candidateParamPrimeExtension
    (C := C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot) hW

/-- The extensional non-provability route can also target the certified
parameterized candidate-world package through a raw parameterized world
agreement witness. -/
theorem exists_candidateParamRootCounterworld_of_exists_worldAgreement_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent)
    (hW :
      ∃ (Gamma : Ctx Base) (world : ClosedTheorySet.World (ParamConst (Base := Base) Const Gamma)),
        (∀ {phi : ClosedFormula Const},
          (Sign.trueE, phi) ∈ (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot).closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∈ world.carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.falseE, phi) ∈ (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot).closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∉ world.carrier)) :
    Nonempty
      (CertifiedHeadPriorityCompletion.CandidateParamRootCounterworld
        (Base := Base)
        (Const := Const)
        (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot)) :=
  CertifiedHeadPriorityCompletion.exists_candidateParamRootCounterworld_of_exists_worldAgreement
    (C := C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot) hW

/-- Prime separating extensions can likewise be paired with a certified
parameterized candidate world and consumed directly at the native
root-counterworld boundary. -/
theorem exists_paramRootCounterworld_of_exists_candidateParamRootCounterworld_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hW :
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateParamRootCounterworld
          (Base := Base)
          (Const := Const)
          (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU))) :
    Nonempty (CompletenessFrontier.ParamRootCounterworld (Base := Base) (Const := Const) F) :=
  CertifiedHeadPriorityCompletion.exists_paramRootCounterworld_of_exists_candidateParamRootCounterworld
    (C := C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) hW

/-- Prime separating extensions can likewise be paired with a certified
parameterized prime extension and consumed directly at the native
root-counterworld boundary. -/
theorem exists_paramRootCounterworld_of_exists_candidateParamPrimeExtension_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hW :
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateParamPrimeExtension
          (Base := Base)
          (Const := Const)
          (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU))) :
    Nonempty (CompletenessFrontier.ParamRootCounterworld (Base := Base) (Const := Const) F) :=
  CertifiedHeadPriorityCompletion.exists_paramRootCounterworld_of_exists_candidateParamPrimeExtension
    (C := C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) hW

/-- Prime separating extensions likewise admit the raw parameterized
world-agreement entry point into the certified candidate-world package. -/
theorem exists_candidateParamRootCounterworld_of_exists_worldAgreement_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hW :
      ∃ (Gamma : Ctx Base) (world : ClosedTheorySet.World (ParamConst (Base := Base) Const Gamma)),
        (∀ {phi : ClosedFormula Const},
          (Sign.trueE, phi) ∈ (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU).closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∈ world.carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.falseE, phi) ∈ (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU).closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∉ world.carrier)) :
    Nonempty
      (CertifiedHeadPriorityCompletion.CandidateParamRootCounterworld
        (Base := Base)
        (Const := Const)
        (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU)) :=
  CertifiedHeadPriorityCompletion.exists_candidateParamRootCounterworld_of_exists_worldAgreement
    (C := C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) hW

/-- The extensional non-provability route therefore refutes native
derivability from any certified parameterized candidate world for the closed
Hintikka hull. -/
theorem not_derivable_of_exists_candidateParamRootCounterworld_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent)
    (hW :
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateParamRootCounterworld
          (Base := Base)
          (Const := Const)
          (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot))) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_of_exists_candidateParamRootCounterworld
    (C := C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot) hW

/-- The extensional non-provability route therefore also refutes native
derivability from the more production-side certified parameterized
prime-extension package. -/
theorem not_derivable_of_exists_candidateParamPrimeExtension_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent)
    (hW :
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateParamPrimeExtension
          (Base := Base)
          (Const := Const)
          (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot))) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_of_exists_candidateParamPrimeExtension
    (C := C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot) hW

/-- The extensional non-provability route therefore also refutes native
derivability from a raw agreeing parameterized world for the closed Hintikka
hull. -/
theorem not_derivable_of_exists_worldAgreement_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent)
    (hW :
      ∃ (Gamma : Ctx Base) (world : ClosedTheorySet.World (ParamConst (Base := Base) Const Gamma)),
        (∀ {phi : ClosedFormula Const},
          (Sign.trueE, phi) ∈ (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot).closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∈ world.carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.falseE, phi) ∈ (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot).closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∉ world.carrier)) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_of_exists_worldAgreement
    (C := C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot) hW

/-- Prime separating extensions likewise refute native derivability once the
closed Hintikka hull is paired with a certified parameterized candidate world. -/
theorem not_derivable_of_exists_candidateParamRootCounterworld_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hW :
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateParamRootCounterworld
          (Base := Base)
          (Const := Const)
          (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU))) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_of_exists_candidateParamRootCounterworld
    (C := C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) hW

/-- Prime separating extensions likewise refute native derivability once the
closed Hintikka hull is paired with the more production-side certified
parameterized prime-extension package. -/
theorem not_derivable_of_exists_candidateParamPrimeExtension_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hW :
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateParamPrimeExtension
          (Base := Base)
          (Const := Const)
          (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU))) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_of_exists_candidateParamPrimeExtension
    (C := C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) hW

/-- Prime separating extensions likewise refute native derivability from a raw
agreeing parameterized world for the certified closed Hintikka hull. -/
theorem not_derivable_of_exists_worldAgreement_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hW :
      ∃ (Gamma : Ctx Base) (world : ClosedTheorySet.World (ParamConst (Base := Base) Const Gamma)),
        (∀ {phi : ClosedFormula Const},
          (Sign.trueE, phi) ∈ (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU).closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∈ world.carrier) ∧
        (∀ {phi : ClosedFormula Const},
          (Sign.falseE, phi) ∈ (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU).closedHintikka.formulas ->
            Mettapedia.Logic.HOL.mapClosedFormula
              (CompletenessFrontier.paramEmbedding
                (Base := Base) (Const := Const) Gamma) phi ∉ world.carrier)) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_of_exists_worldAgreement
    (C := C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) hW

end SaturationSearchState.HeadPriorityCompletion

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
