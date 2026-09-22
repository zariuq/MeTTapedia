import Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy

/-!
# Substitution coherence of decoded dependent families

An independently supplied code constructor and its decoding equivalence
induce contextual products and sums. Their substitution laws are consequences
of pointwise construction, not fields of the code interface. Domain,
codomain, and result levels are independent parameters.

The equivalences also transport arbitrary dependent motives over the full
comprehension, retaining their dependence on decoded values. No equality of
decoded types is inferred from an equivalence. The beta and eta laws below
are semantic equations; in particular, they add no native eta conversion.

The existing two-level hierarchy supplies examples, not an unbounded native
universe model. Universe formation, predicative rank separation, interpretation
of native declarations, and native typing soundness are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.TarskiDecodedFamilyCoherence

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.TarskiUniverseCapabilities
open Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison

universe uLevel uCode uEl uContext uSource uEarlier uOther uMotive u

/-! ## Equivalences over context comprehension -/

namespace Fibrewise

variable {Context : Type uContext} {Source : Type uSource}
variable {Earlier : Type uEarlier}
variable {A : Context → Type uEl} {B : Context → Type uOther}

/-- The existing dependent-sum congruence preserves the context coordinate. -/
def total (equivalence : ∀ point, A point ≃ B point) : Sigma A ≃ Sigma B :=
  Equiv.sigmaCongrRight equivalence

/-- The ordinary set-family comprehension action on a base substitution. -/
def extend (substitution : Source → Context) (A : Context → Type uEl) :
    (Σ point, A (substitution point)) → Sigma A :=
  fun point => ⟨substitution point.1, point.2⟩

@[simp] theorem total_base (equivalence : ∀ point, A point ≃ B point)
    (point : Sigma A) : (total equivalence point).1 = point.1 := rfl

@[simp] theorem extend_id (A : Context → Type uEl) : extend id A = id := rfl

theorem extend_comp (earlier : Earlier → Source) (later : Source → Context)
    (A : Context → Type uEl) :
    extend (later ∘ earlier) A = extend later A ∘ extend earlier (A ∘ later) := rfl

/-- The decoding comparison is cartesian over every base substitution. -/
theorem total_reindex (substitution : Source → Context)
    (equivalence : ∀ point, A point ≃ B point) :
    total equivalence ∘ extend substitution A =
      extend substitution B ∘ total (fun point => equivalence (substitution point)) := rfl

theorem total_symm_reindex (substitution : Source → Context)
    (equivalence : ∀ point, A point ≃ B point) :
    (total equivalence).symm ∘ extend substitution B =
      extend substitution A ∘
        (total (fun point => equivalence (substitution point))).symm := rfl

/-- All dependent sections over the decoded comprehension are transported,
not only constant motives or functions of the base context. -/
def motiveEquiv (equivalence : ∀ point, A point ≃ B point)
    (motive : Sigma B → Type uMotive) :
    ((point : Sigma A) → motive (total equivalence point)) ≃
      ((point : Sigma B) → motive point) :=
  Equiv.piCongrLeft motive (total equivalence)

/-- Motive transport and contextual substitution form the same square. -/
theorem motive_reindex (substitution : Source → Context)
    (equivalence : ∀ point, A point ≃ B point)
    (motive : Sigma B → Type uMotive) :
    (motive ∘ total equivalence) ∘ extend substitution A =
      (motive ∘ extend substitution B) ∘
        total (fun point => equivalence (substitution point)) := rfl

/-- Transporting a dependent section then substituting agrees exactly with
substitution followed by the reindexed transport. -/
theorem motiveEquiv_symm_reindex (substitution : Source → Context)
    (equivalence : ∀ point, A point ≃ B point)
    (motive : Sigma B → Type uMotive) (term : ∀ point, motive point) :
    (fun point => (motiveEquiv equivalence motive).symm term
        (extend substitution A point)) =
      (motiveEquiv (fun point => equivalence (substitution point))
        (motive ∘ extend substitution B)).symm
          (fun point => term (extend substitution B point)) := rfl

/-- The forward transport square retains the necessary dependent casts. -/
theorem motiveEquiv_reindex (substitution : Source → Context)
    (equivalence : ∀ point, A point ≃ B point)
    (motive : Sigma B → Type uMotive)
    (term : ∀ point, motive (total equivalence point)) :
    (fun point => motiveEquiv equivalence motive term
        (extend substitution B point)) =
      motiveEquiv (fun point => equivalence (substitution point))
        (motive ∘ extend substitution B)
          (fun point => term (extend substitution A point)) := by
  apply (motiveEquiv (fun point => equivalence (substitution point))
    (motive ∘ extend substitution B)).symm.injective
  funext point
  simp only [motiveEquiv, Equiv.piCongrLeft_symm_apply]
  change motiveEquiv equivalence motive term
      (total equivalence (extend substitution A point)) = _
  simp only [motiveEquiv, Equiv.piCongrLeft_apply_apply]
  exact (Equiv.piCongrLeft_apply_apply
    (motive ∘ extend substitution B)
    (total (fun point => equivalence (substitution point)))
    (fun point => term (extend substitution A point)) point).symm

@[simp] theorem motiveEquiv_id (motive : Sigma A → Type uMotive) :
    motiveEquiv (fun point => Equiv.refl (A point)) motive = Equiv.refl _ := by
  apply Equiv.symm_bijective.1
  apply Equiv.ext
  intro term
  funext point
  rfl

/-- Composition transports the entire motive along both fibre comparisons. -/
theorem motiveEquiv_comp {C : Context → Type u}
    (first : ∀ point, A point ≃ B point) (second : ∀ point, B point ≃ C point)
    (motive : Sigma C → Type uMotive) :
    (motiveEquiv first (motive ∘ total second)).trans (motiveEquiv second motive) =
      motiveEquiv (fun point => (first point).trans (second point)) motive := by
  apply Equiv.symm_bijective.1
  apply Equiv.ext
  intro term
  funext point
  rfl

/-- The naturality square is coherent with composite base substitutions. -/
theorem motiveEquiv_reindex_comp (earlier : Earlier → Source) (later : Source → Context)
    (equivalence : ∀ point, A point ≃ B point)
    (motive : Sigma B → Type uMotive)
    (term : ∀ point, motive (total equivalence point)) :
    (fun point => motiveEquiv equivalence motive term
        (extend later B (extend earlier (B ∘ later) point))) =
      motiveEquiv (fun point => equivalence (later (earlier point)))
        (motive ∘ extend later B ∘ extend earlier (B ∘ later))
          (fun point => term (extend later A (extend earlier (A ∘ later) point))) :=
  motiveEquiv_reindex (later ∘ earlier) equivalence motive term

end Fibrewise

/-! ## External code operations, with no assumed contextual laws -/

variable (family : TarskiCodeFamily.{uLevel, uCode, uEl})

/-- The domain, codomain, and result levels need not coincide. -/
structure PiCoding (domainLevel codomainLevel resultLevel : family.Level) where
  code : (domain : family.Code domainLevel) →
    (family.El domainLevel domain → family.Code codomainLevel) → family.Code resultLevel
  decode : ∀ domain codomain,
    family.El resultLevel (code domain codomain) ≃
      ((argument : family.El domainLevel domain) →
        family.El codomainLevel (codomain argument))

/-- Independent dependent-sum code data at the same three level positions. -/
structure SigmaCoding (domainLevel codomainLevel resultLevel : family.Level) where
  code : (domain : family.Code domainLevel) →
    (family.El domainLevel domain → family.Code codomainLevel) → family.Code resultLevel
  decode : ∀ domain codomain,
    family.El resultLevel (code domain codomain) ≃
      (Σ argument : family.El domainLevel domain,
        family.El codomainLevel (codomain argument))

/-- Contextualization of an external family in the existing set-family CwF. -/
def universeFamily (family : TarskiCodeFamily.{uLevel, u, u}) :
    TarskiUniverseFamily family.Level (familiesCwf.{u}) where
  univ _ level _ := family.Code level
  el code point := family.El _ (code point)

theorem universeSubstitutionStable (family : TarskiCodeFamily.{uLevel, u, u}) :
    (universeFamily family).SubstitutionStable where
  univ_sub _ _ := rfl
  el_sub _ _ := rfl

variable {family}
variable {i j k : family.Level}
variable {Context : Type uContext} {Source : Type uSource} {Earlier : Type uEarlier}

namespace PiCoding

variable (operation : PiCoding family i j k)
variable (domain : Context → family.Code i)
variable (codomain : (Σ point, family.El i (domain point)) → family.Code j)

def contextCode : Context → family.Code k :=
  fun point => operation.code (domain point) (fun argument => codomain ⟨point, argument⟩)

def fibreEquiv (point : Context) :
    family.El k (operation.contextCode domain codomain point) ≃
      ((argument : family.El i (domain point)) → family.El j (codomain ⟨point, argument⟩)) :=
  operation.decode (domain point) (fun argument => codomain ⟨point, argument⟩)

/-- The decoding equivalence acts on complete sections. -/
def sectionEquiv :
    ((point : Context) → family.El k (operation.contextCode domain codomain point)) ≃
      ((point : Context) → (argument : family.El i (domain point)) →
        family.El j (codomain ⟨point, argument⟩)) :=
  Equiv.piCongrRight (operation.fibreEquiv domain codomain)

def lam (body : ∀ point, family.El j (codomain point)) :
    (point : Context) → family.El k (operation.contextCode domain codomain point) :=
  fun point => (operation.fibreEquiv domain codomain point).symm
    (fun argument => body ⟨point, argument⟩)

def app
    (function : ∀ point, family.El k (operation.contextCode domain codomain point))
    (argument : ∀ point, family.El i (domain point)) :
    (point : Context) → family.El j (codomain ⟨point, argument point⟩) :=
  fun point => operation.fibreEquiv domain codomain point (function point) (argument point)

theorem beta (body : ∀ point, family.El j (codomain point))
    (argument : ∀ point, family.El i (domain point)) :
    operation.app domain codomain (operation.lam domain codomain body) argument =
      fun point => body ⟨point, argument point⟩ := by
  funext point
  exact congrFun ((operation.fibreEquiv domain codomain point).apply_symm_apply _) _

/-- Semantic eta does not add an object-language conversion. -/
theorem eta (function : ∀ point, family.El k (operation.contextCode domain codomain point)) :
    operation.lam domain codomain (fun point =>
        operation.fibreEquiv domain codomain point.1 (function point.1) point.2) = function := by
  funext point
  simpa only [lam] using
    (operation.fibreEquiv domain codomain point).symm_apply_apply (function point)

theorem contextCode_reindex (substitution : Source → Context) :
    operation.contextCode domain codomain ∘ substitution =
      operation.contextCode (domain ∘ substitution)
        (codomain ∘ Fibrewise.extend substitution (fun point => family.El i (domain point))) := rfl

theorem fibreEquiv_reindex (substitution : Source → Context) (point : Source) :
    operation.fibreEquiv (domain ∘ substitution)
        (codomain ∘ Fibrewise.extend substitution (fun point => family.El i (domain point))) point =
      operation.fibreEquiv domain codomain (substitution point) := rfl

theorem lam_reindex (substitution : Source → Context)
    (body : ∀ point, family.El j (codomain point)) :
    (fun point => operation.lam domain codomain body (substitution point)) =
      operation.lam (domain ∘ substitution)
        (codomain ∘ Fibrewise.extend substitution (fun point => family.El i (domain point)))
        (fun point => body (Fibrewise.extend substitution (fun point => family.El i (domain point)) point)) :=
  rfl

theorem app_reindex (substitution : Source → Context)
    (function : ∀ point, family.El k (operation.contextCode domain codomain point))
    (argument : ∀ point, family.El i (domain point)) :
    (fun point => operation.app domain codomain function argument (substitution point)) =
      operation.app (domain ∘ substitution)
        (codomain ∘ Fibrewise.extend substitution (fun point => family.El i (domain point)))
        (fun point => function (substitution point))
        (fun point => argument (substitution point)) := rfl

end PiCoding

namespace SigmaCoding

variable (operation : SigmaCoding family i j k)
variable (domain : Context → family.Code i)
variable (codomain : (Σ point, family.El i (domain point)) → family.Code j)

def contextCode : Context → family.Code k :=
  fun point => operation.code (domain point) (fun argument => codomain ⟨point, argument⟩)

def fibreEquiv (point : Context) :
    family.El k (operation.contextCode domain codomain point) ≃
      (Σ argument : family.El i (domain point), family.El j (codomain ⟨point, argument⟩)) :=
  operation.decode (domain point) (fun argument => codomain ⟨point, argument⟩)

def sectionEquiv :
    ((point : Context) → family.El k (operation.contextCode domain codomain point)) ≃
      ((point : Context) → Σ argument : family.El i (domain point),
        family.El j (codomain ⟨point, argument⟩)) :=
  Equiv.piCongrRight (operation.fibreEquiv domain codomain)

def pair (first : ∀ point, family.El i (domain point))
    (second : ∀ point, family.El j (codomain ⟨point, first point⟩)) :
    (point : Context) → family.El k (operation.contextCode domain codomain point) :=
  fun point => (operation.fibreEquiv domain codomain point).symm ⟨first point, second point⟩

def fst (value : ∀ point, family.El k (operation.contextCode domain codomain point)) :
    (point : Context) → family.El i (domain point) :=
  fun point => (operation.fibreEquiv domain codomain point (value point)).1

def snd (value : ∀ point, family.El k (operation.contextCode domain codomain point)) :
    (point : Context) → family.El j (codomain ⟨point, operation.fst domain codomain value point⟩) :=
  fun point => (operation.fibreEquiv domain codomain point (value point)).2

/-- Both dependent projections compute together, before any fibre cast. -/
theorem pair_decode (first : ∀ point, family.El i (domain point))
    (second : ∀ point, family.El j (codomain ⟨point, first point⟩)) (point : Context) :
    operation.fibreEquiv domain codomain point (operation.pair domain codomain first second point) =
      ⟨first point, second point⟩ :=
  (operation.fibreEquiv domain codomain point).apply_symm_apply _

theorem fst_pair (first : ∀ point, family.El i (domain point))
    (second : ∀ point, family.El j (codomain ⟨point, first point⟩)) :
    operation.fst domain codomain (operation.pair domain codomain first second) = first := by
  funext point
  exact congrArg Sigma.fst (operation.pair_decode domain codomain first second point)

theorem snd_pair (first : ∀ point, family.El i (domain point))
    (second : ∀ point, family.El j (codomain ⟨point, first point⟩)) (point : Context) :
    HEq (operation.snd domain codomain (operation.pair domain codomain first second) point)
      (second point) :=
  (Sigma.mk.inj_iff.mp (operation.pair_decode domain codomain first second point)).2

theorem eta (value : ∀ point, family.El k (operation.contextCode domain codomain point)) :
    operation.pair domain codomain (operation.fst domain codomain value)
      (operation.snd domain codomain value) = value := by
  funext point
  exact (operation.fibreEquiv domain codomain point).symm_apply_apply _

theorem contextCode_reindex (substitution : Source → Context) :
    operation.contextCode domain codomain ∘ substitution =
      operation.contextCode (domain ∘ substitution)
        (codomain ∘ Fibrewise.extend substitution (fun point => family.El i (domain point))) := rfl

theorem fibreEquiv_reindex (substitution : Source → Context) (point : Source) :
    operation.fibreEquiv (domain ∘ substitution)
        (codomain ∘ Fibrewise.extend substitution (fun point => family.El i (domain point))) point =
      operation.fibreEquiv domain codomain (substitution point) := rfl

theorem pair_reindex (substitution : Source → Context)
    (first : ∀ point, family.El i (domain point))
    (second : ∀ point, family.El j (codomain ⟨point, first point⟩)) :
    (fun point => operation.pair domain codomain first second (substitution point)) =
      operation.pair (domain ∘ substitution)
        (codomain ∘ Fibrewise.extend substitution (fun point => family.El i (domain point)))
        (fun point => first (substitution point))
        (fun point => second (substitution point)) := rfl

theorem fst_reindex (substitution : Source → Context)
    (value : ∀ point, family.El k (operation.contextCode domain codomain point)) :
    (fun point => operation.fst domain codomain value (substitution point)) =
      operation.fst (domain ∘ substitution)
        (codomain ∘ Fibrewise.extend substitution (fun point => family.El i (domain point)))
        (fun point => value (substitution point)) := rfl

theorem snd_reindex (substitution : Source → Context)
    (value : ∀ point, family.El k (operation.contextCode domain codomain point)) :
    (fun point => operation.snd domain codomain value (substitution point)) =
      operation.snd (domain ∘ substitution)
        (codomain ∘ Fibrewise.extend substitution (fun point => family.El i (domain point)))
        (fun point => value (substitution point)) := rfl

end SigmaCoding

/-! ## Mixed levels from independently given changes of codes -/

/-- Moving input codes also transports the dependent argument of the
codomain. Equivalences, rather than decoded-type equalities, suffice. -/
def PiCoding.mapInputs (operation : PiCoding family i j k)
    {newDomain newCodomain : family.Level}
    (mapDomain : family.Code newDomain → family.Code i)
    (decodeDomain : ∀ code, family.El i (mapDomain code) ≃ family.El newDomain code)
    (mapCodomain : family.Code newCodomain → family.Code j)
    (decodeCodomain : ∀ code, family.El j (mapCodomain code) ≃ family.El newCodomain code) :
    PiCoding family newDomain newCodomain k where
  code domain codomain := operation.code (mapDomain domain)
    (fun argument => mapCodomain (codomain (decodeDomain domain argument)))
  decode domain codomain :=
    (operation.decode (mapDomain domain)
      (fun argument => mapCodomain (codomain (decodeDomain domain argument)))).trans
        ((decodeDomain domain).piCongr
          (fun argument => decodeCodomain (codomain (decodeDomain domain argument))))

def SigmaCoding.mapInputs (operation : SigmaCoding family i j k)
    {newDomain newCodomain : family.Level}
    (mapDomain : family.Code newDomain → family.Code i)
    (decodeDomain : ∀ code, family.El i (mapDomain code) ≃ family.El newDomain code)
    (mapCodomain : family.Code newCodomain → family.Code j)
    (decodeCodomain : ∀ code, family.El j (mapCodomain code) ≃ family.El newCodomain code) :
    SigmaCoding family newDomain newCodomain k where
  code domain codomain := operation.code (mapDomain domain)
    (fun argument => mapCodomain (codomain (decodeDomain domain argument)))
  decode domain codomain :=
    (operation.decode (mapDomain domain)
      (fun argument => mapCodomain (codomain (decodeDomain domain argument)))).trans
        ((decodeDomain domain).sigmaCongr
          (fun argument => decodeCodomain (codomain (decodeDomain domain argument))))

/-! ## Exact connection to the existing CwF operations -/

section Cwf

variable {family : TarskiCodeFamily.{uLevel, u, u}}
variable {Context : Type u} {i j k : family.Level}
variable (domain : Context → family.Code i)
variable (codomain : (Σ point, family.El i (domain point)) → family.Code j)

/-- The base reindexing used above is the existing CwF comprehension map. -/
theorem Fibrewise.extend_cwf {Source Context : Type u}
    (substitution : Source → Context) (type : Context → Type u) :
    Fibrewise.extend substitution type =
      familiesCwf.pair
        (familiesCwf.compS substitution (familiesCwf.wk (familiesCwf.tySub type substitution)))
        type (familiesCwf.vz (familiesCwf.tySub type substitution)) := rfl

/-- Decoding identifies the constructed code with the existing full CwF
product fibre; it does not claim equality of those two types. -/
def PiCoding.cwfEquiv (operation : PiCoding family i j k) (point : Context) :
    (universeFamily family).el (operation.contextCode domain codomain) point ≃
      familiesProducts.pi ((universeFamily family).el domain)
        ((universeFamily family).el codomain) point :=
  operation.fibreEquiv domain codomain point

def SigmaCoding.cwfEquiv (operation : SigmaCoding family i j k) (point : Context) :
    (universeFamily family).el (operation.contextCode domain codomain) point ≃
      familiesSums.sigma ((universeFamily family).el domain)
        ((universeFamily family).el codomain) point :=
  operation.fibreEquiv domain codomain point

theorem PiCoding.lam_cwf (operation : PiCoding family i j k)
    (body : ∀ point, family.El j (codomain point)) :
    operation.sectionEquiv domain codomain (operation.lam domain codomain body) =
      familiesProducts.lam body := by
  funext point
  exact (operation.fibreEquiv domain codomain point).apply_symm_apply _

theorem PiCoding.app_cwf (operation : PiCoding family i j k)
    (function : ∀ point, family.El k (operation.contextCode domain codomain point))
    (argument : ∀ point, family.El i (domain point)) :
    operation.app domain codomain function argument =
      familiesProducts.app (domain := fun point => family.El i (domain point))
        (codomain := fun point => family.El j (codomain point))
        (operation.sectionEquiv domain codomain function) argument := rfl

theorem SigmaCoding.pair_cwf (operation : SigmaCoding family i j k)
    (first : ∀ point, family.El i (domain point))
    (second : ∀ point, family.El j (codomain ⟨point, first point⟩)) :
    operation.sectionEquiv domain codomain (operation.pair domain codomain first second) =
      familiesSums.pair (domain := fun point => family.El i (domain point))
        (codomain := fun point => family.El j (codomain point)) first second := by
  funext point
  exact operation.pair_decode domain codomain first second point

theorem SigmaCoding.fst_cwf (operation : SigmaCoding family i j k)
    (value : ∀ point, family.El k (operation.contextCode domain codomain point)) :
    operation.fst domain codomain value =
      familiesSums.fst (domain := fun point => family.El i (domain point))
        (codomain := fun point => family.El j (codomain point))
        (operation.sectionEquiv domain codomain value) := rfl

theorem SigmaCoding.snd_cwf (operation : SigmaCoding family i j k)
    (value : ∀ point, family.El k (operation.contextCode domain codomain point)) :
    operation.snd domain codomain value =
      familiesSums.snd (domain := fun point => family.El i (domain point))
        (codomain := fun point => family.El j (codomain point))
        (operation.sectionEquiv domain codomain value) := rfl

end Cwf

/-! ## Reusing the two-level hierarchy's actual closure witnesses -/

namespace TwoLevel

open TwoLevelSetFamilies

universe small

def pi (level : Bool) : PiCoding externalFamily.{small} level level level where
  code := piCode level
  decode := decodePiEquiv level

def sigma (level : Bool) : SigmaCoding externalFamily.{small} level level level where
  code := sigmaCode level
  decode := decodeSigmaEquiv level

theorem pi_contextCode {Context : Type (small + 2)} {level : Bool}
    (domain : Context → Code.{small} level)
    (codomain : (Σ point, decode.{small} level (domain point)) → Code.{small} level) :
    (pi level).contextCode domain codomain = piClosed.piCode domain codomain := rfl

theorem sigma_contextCode {Context : Type (small + 2)} {level : Bool}
    (domain : Context → Code.{small} level)
    (codomain : (Σ point, decode.{small} level (domain point)) → Code.{small} level) :
    (sigma level).contextCode domain codomain = sigmaClosed.sigmaCode domain codomain := rfl

theorem pi_fibreEquiv {Context : Type (small + 2)} {level : Bool}
    (domain : Context → Code.{small} level)
    (codomain : (Σ point, decode.{small} level (domain point)) → Code.{small} level)
    (point : Context) :
    (pi level).fibreEquiv domain codomain point = piClosed.el_piCode domain codomain point := rfl

theorem sigma_fibreEquiv {Context : Type (small + 2)} {level : Bool}
    (domain : Context → Code.{small} level)
    (codomain : (Σ point, decode.{small} level (domain point)) → Code.{small} level)
    (point : Context) :
    (sigma level).fibreEquiv domain codomain point = sigmaClosed.el_sigmaCode domain codomain point := rfl

/-- Actual lower-to-upper cumulative transport, followed by upper product
closure. The codomain remains independently upper-level. -/
def mixedPi : PiCoding externalFamily.{small} false true true :=
  (pi true).mapInputs
    (externalCumulative.lift (show Below false true from ⟨rfl, rfl⟩))
    (externalCumulative.decodeLift (show Below false true from ⟨rfl, rfl⟩))
    id (fun code => Equiv.refl (decode true code))

def mixedSigma : SigmaCoding externalFamily.{small} false true true :=
  (sigma true).mapInputs
    (externalCumulative.lift (show Below false true from ⟨rfl, rfl⟩))
    (externalCumulative.decodeLift (show Below false true from ⟨rfl, rfl⟩))
    id (fun code => Equiv.refl (decode true code))

end TwoLevel

/-! ## Varying mixed-level fibres and nontrivial decoding transport -/

namespace Controls

open TwoLevelSetFamilies

/-- The lower-level domain has two inhabitants in every base context. -/
def domain (_ : Nat) : Code.{0} false := ⟨Bool⟩

def domainValue {point : Nat} (value : decode.{0} false (domain point)) : Bool :=
  value.down.down

/-- The upper-level fibre depends on both the base and the decoded argument. -/
def codomain (point : Σ context, decode.{0} false (domain context)) : Code.{0} true :=
  ⟨ULift.{1, 0} (Fin (point.1 + if domainValue point.2 then 2 else 1))⟩

def body (point : Σ context, decode.{0} false (domain context)) :
    decode.{0} true (codomain point) :=
  ⟨⟨⟨point.1, by
    split <;> omega⟩⟩⟩

def argument (_ : Nat) : decode.{0} false (domain 0) := ⟨⟨true⟩⟩

def function : (point : Nat) →
    decode.{0} true (TwoLevel.mixedPi.contextCode domain codomain point) :=
  TwoLevel.mixedPi.lam domain codomain body

def pair : (point : Nat) →
    decode.{0} true (TwoLevel.mixedSigma.contextCode domain codomain point) :=
  TwoLevel.mixedSigma.pair domain codomain argument
    (fun point => body ⟨point, argument point⟩)

theorem mixed_application (point : Nat) :
    (TwoLevel.mixedPi.app domain codomain function argument point).down.down.val = point := by
  have computation := congrFun (TwoLevel.mixedPi.beta domain codomain body argument) point
  exact congrArg (fun value => value.down.down.val) computation

theorem mixed_pair (point : Nat) :
    (TwoLevel.mixedSigma.fibreEquiv domain codomain point (pair point)).2.down.down.val = point := by
  have computation := TwoLevel.mixedSigma.pair_decode domain codomain argument
    (fun point => body ⟨point, argument point⟩) point
  exact congrArg (fun value => value.2.down.down.val) computation

/-- A genuine dependent permutation of the same decoded upper fibres. -/
def reverseFibre (point : Σ context, decode.{0} false (domain context)) :
    decode.{0} true (codomain point) ≃ decode.{0} true (codomain point) :=
  let lower : decode.{0} true (codomain point) ≃
      Fin (point.1 + if domainValue point.2 then 2 else 1) :=
    Equiv.ulift.trans Equiv.ulift
  lower.trans (Fin.revPerm.trans lower.symm)

/-- The code is unchanged; the selected comparison is visibly different. -/
def comparison (point : Nat) :
    decode.{0} true (TwoLevel.mixedSigma.contextCode domain codomain point) ≃
      (Σ value : decode.{0} false (domain point), decode.{0} true (codomain ⟨point, value⟩)) :=
  (TwoLevel.mixedSigma.fibreEquiv domain codomain point).trans
    (Equiv.sigmaCongrRight (fun value => reverseFibre ⟨point, value⟩))

def motive (point : Σ context,
    Σ value : decode.{0} false (domain context), decode.{0} true (codomain ⟨context, value⟩)) : Type :=
  Fin (point.2.2.down.down.val + 1)

def motiveTerm (point : Σ context,
    Σ value : decode.{0} false (domain context), decode.{0} true (codomain ⟨context, value⟩)) :
    motive point := ⟨point.2.2.down.down.val, Nat.lt_succ_self _⟩

theorem comparison_changes_value :
    (comparison 3 (pair 3)).2.down.down.val = 1 ∧
      (TwoLevel.mixedSigma.fibreEquiv domain codomain 3 (pair 3)).2.down.down.val = 3 := by
  constructor
  · change ((reverseFibre
      ⟨3, (TwoLevel.mixedSigma.fibreEquiv domain codomain 3 (pair 3)).1⟩)
        (TwoLevel.mixedSigma.fibreEquiv domain codomain 3 (pair 3)).2).down.down.val = 1
    rw [show TwoLevel.mixedSigma.fibreEquiv domain codomain 3 (pair 3) =
      ⟨argument 3, body ⟨3, argument 3⟩⟩ from
      TwoLevel.mixedSigma.pair_decode domain codomain argument
        (fun point => body ⟨point, argument point⟩) 3]
    decide
  · exact mixed_pair 3

/-- Ignoring a selected decoding equivalence changes even a dependent
section's observable value, despite retaining exactly the same code. -/
theorem omitting_transport_changes_motive_value :
    ((Fibrewise.motiveEquiv comparison motive).symm motiveTerm ⟨3, pair 3⟩).val = 1 ∧
      (motiveTerm (Fibrewise.total
        (TwoLevel.mixedSigma.fibreEquiv domain codomain) ⟨3, pair 3⟩)).val = 3 :=
  comparison_changes_value

/-- The motive really sees the transported value: at the same base point,
its two resulting fibres have different finite cardinalities. -/
theorem transported_motive_fibres_not_equivalent :
    ¬ Nonempty (motive (Fibrewise.total comparison ⟨3, pair 3⟩) ≃
      motive (Fibrewise.total
        (TwoLevel.mixedSigma.fibreEquiv domain codomain) ⟨3, pair 3⟩)) := by
  change ¬ Nonempty
    (Fin ((comparison 3 (pair 3)).2.down.down.val + 1) ≃
      Fin ((TwoLevel.mixedSigma.fibreEquiv domain codomain 3 (pair 3)).2.down.down.val + 1))
  rw [comparison_changes_value.1, comparison_changes_value.2]
  rintro ⟨equivalence⟩
  have cardinality := Fintype.card_congr equivalence
  norm_num at cardinality

/-- The full dependent motive still reindexes under a noninjective context
map; its dependence on the transported value is not discarded. -/
theorem mixed_motive_reindex :
    (fun point => (Fibrewise.motiveEquiv comparison motive).symm motiveTerm
        (Fibrewise.extend (fun index => index % 2 + 3)
          (fun index => decode.{0} true (TwoLevel.mixedSigma.contextCode domain codomain index)) point)) =
      (Fibrewise.motiveEquiv (fun index => comparison (index % 2 + 3))
        (motive ∘ Fibrewise.extend (fun index => index % 2 + 3)
          (fun index => Σ value : decode.{0} false (domain index),
            decode.{0} true (codomain ⟨index, value⟩)))).symm
          (fun point => motiveTerm (Fibrewise.extend (fun index => index % 2 + 3)
            (fun index => Σ value : decode.{0} false (domain index),
              decode.{0} true (codomain ⟨index, value⟩)) point)) :=
  Fibrewise.motiveEquiv_symm_reindex _ comparison motive motiveTerm

end Controls

#print axioms universeSubstitutionStable
#print axioms Fibrewise.motiveEquiv_reindex
#print axioms Fibrewise.motiveEquiv_comp
#print axioms Fibrewise.motiveEquiv_reindex_comp
#print axioms PiCoding.beta
#print axioms PiCoding.eta
#print axioms PiCoding.mapInputs
#print axioms PiCoding.lam_cwf
#print axioms SigmaCoding.pair_decode
#print axioms SigmaCoding.snd_pair
#print axioms SigmaCoding.mapInputs
#print axioms SigmaCoding.pair_cwf
#print axioms TwoLevel.mixedPi
#print axioms TwoLevel.mixedSigma
#print axioms Controls.mixed_application
#print axioms Controls.mixed_pair
#print axioms Controls.omitting_transport_changes_motive_value
#print axioms Controls.transported_motive_fibres_not_equivalent
#print axioms Controls.mixed_motive_reindex

end Mettapedia.TypeTheory.TarskiDecodedFamilyCoherence
