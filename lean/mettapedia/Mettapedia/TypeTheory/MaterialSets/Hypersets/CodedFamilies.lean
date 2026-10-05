import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSetUniverses
import Mettapedia.TypeTheory.MaterialSets.Hypersets.DependentProduct
import Mettapedia.TypeTheory.DependentFamilySectionDescent
import Mathlib.Logic.Equiv.Basic

/-!
# Bounded codes of actual hyperset families

A hyperset at graph-size level `u` is coded by a well-founded set at level
`u + 1`. Valid codes, their interpreted members, and their dependent sections
are compared with the actual decoded hypersets and member types. The comparisons
retain values and have inverse and evaluation laws.

For a supplied closed host universe containing `carrierCode`, separation and
powerset closure put every valid code, the code carrier, and the codes of actual
material dependent sums and products in that universe. Existence of such a
universe is not assumed globally. The host's membership remains well-founded;
`codeMem` is a different, interpreted relation that can have self-members.

The existing graph coding, decoder, and theorems about them use
`Classical.choice`. This module inherits that host-level dependency; it does not
assert an object-language choice principle. Dependent replacement uses an
explicit graph `Presentation`. The bounds are specifically for `HSet.{u}`
families with propositional material membership, not evidence-sensitive graph
occurrence families or arbitrary families of higher host-universe levels.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilies

open HSet Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseLift

universe u

noncomputable section

/-- Valid codes at the next host universe level. -/
abbrev Code := {c : ZFSet.{u + 1} // c ∈ hsetCode.{u}}

/-- The actual code of a hyperset, together with its validity. -/
def encode (x : HSet.{u}) : Code.{u} :=
  ⟨code x, mem_hsetCode.mpr ⟨x, rfl⟩⟩

/-- Decode a valid code. Its validity excludes the decoder's default case. -/
def decode (c : Code.{u}) : HSet.{u} := decodeHSet c.1

@[simp] theorem decode_encode (x : HSet.{u}) : decode (encode x) = x :=
  decodeHSet_code x

@[simp] theorem encode_decode (c : Code.{u}) : encode (decode c) = c := by
  obtain ⟨x, hx⟩ := mem_hsetCode.mp c.2
  apply Subtype.ext
  change code (decodeHSet c.1) = c.1
  rw [← hx, decodeHSet_code]

/-- Valid codes and actual hypersets are equivalent, with the actual decoder. -/
def carrierEquiv : Code.{u} ≃ HSet.{u} where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

/-- Every code is bounded by the carrier of lifted lower-level host sets. -/
theorem encode_mem_of_carrier_mem {U : ZFSet.{u + 1}}
    (hU : ZFSetUniverseClosure.Closed U) (h : carrierCode.{u} ∈ U) (x : HSet.{u}) :
    (encode x).1 ∈ U :=
  hU.subset_mem h (code_subset_carrierCode x)

/-- Valid codes lying in the supplied enclosing host universe. -/
abbrev BoundedCode (U : ZFSet.{u + 1}) :=
  {c : ZFSet.{u + 1} // c ∈ hsetCode.{u} ∧ c ∈ U}

def boundedEncode {U : ZFSet.{u + 1}} (hU : ZFSetUniverseClosure.Closed U)
    (h : carrierCode.{u} ∈ U) (x : HSet.{u}) : BoundedCode U :=
  ⟨(encode x).1, (encode x).2, encode_mem_of_carrier_mem hU h x⟩

/-- Under the stated bound, restricting valid codes to `U` loses no hyperset. -/
def boundedCarrierEquiv {U : ZFSet.{u + 1}} (hU : ZFSetUniverseClosure.Closed U)
    (h : carrierCode.{u} ∈ U) : BoundedCode U ≃ HSet.{u} where
  toFun c := decode ⟨c.1, c.2.1⟩
  invFun := boundedEncode hU h
  left_inv c := by
    apply Subtype.ext
    change code (decode ⟨c.1, c.2.1⟩) = c.1
    exact congrArg (fun c : Code.{u} => c.1) (encode_decode ⟨c.1, c.2.1⟩)
  right_inv := decode_encode

/-- The same bound contains every valid code, independently of its presentation. -/
theorem validCode_mem {U : ZFSet.{u + 1}} (hU : ZFSetUniverseClosure.Closed U)
    (h : carrierCode.{u} ∈ U) (c : Code.{u}) : c.1 ∈ U := by
  have same := congrArg (fun c : Code.{u} => c.1) (encode_decode c)
  exact same ▸ encode_mem_of_carrier_mem hU h (decode c)

/-- Interpreted members whose codes also carry the enclosing-universe bound. -/
abbrev BoundedMembers {U : ZFSet.{u + 1}} (c : BoundedCode U) :=
  {a : BoundedCode U // codeMem c.1 a.1}

/-- Bounded interpreted members and actual decoded members have the same values. -/
def boundedMemberEquiv {U : ZFSet.{u + 1}} (hU : ZFSetUniverseClosure.Closed U)
    (h : carrierCode.{u} ∈ U) (c : BoundedCode U) :
    BoundedMembers c ≃ El (· ∈ ·) (decodeHSet c.1) where
  toFun a := ⟨decodeHSet a.1.1, a.2⟩
  invFun a := ⟨boundedEncode hU h a.1, by
    change decodeHSet (code a.1) ∈ decodeHSet c.1
    rw [decodeHSet_code]
    exact a.2⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : Code.{u} => c.1) (encode_decode ⟨a.1.1, a.1.2.1⟩)
  right_inv a := El.ext HSet.propositional (decodeHSet_code a.1)

theorem boundedMemberEquiv_value {U : ZFSet.{u + 1}}
    (hU : ZFSetUniverseClosure.Closed U) (h : carrierCode.{u} ∈ U)
    (c : BoundedCode U) (a : BoundedMembers c) :
    (boundedMemberEquiv hU h c a).1 = decodeHSet a.1.1 := rfl

/-- The whole valid-code carrier is itself a member of the supplied universe. -/
theorem codeCarrier_mem {U : ZFSet.{u + 1}} (hU : ZFSetUniverseClosure.Closed U)
    (h : carrierCode.{u} ∈ U) : hsetCode.{u} ∈ U :=
  hsetCode_mem_of_carrierCode_mem hU h

/-- Members with the interpreted relation, not host `ZFSet` membership. -/
abbrev Members (c : Code.{u}) := {a : Code.{u} // codeMem c.1 a.1}

/-- Reading an interpreted code member retains exactly its decoded value. -/
def memberEquiv (c : Code.{u}) : Members c ≃ El (· ∈ ·) (decode c) where
  toFun a := ⟨decode a.1, a.2⟩
  invFun a := ⟨encode a.1, by
    change decodeHSet (code a.1) ∈ decodeHSet c.1
    rw [decodeHSet_code]
    exact a.2⟩
  left_inv a := Subtype.ext (encode_decode a.1)
  right_inv a := El.ext HSet.propositional (decode_encode a.1)

@[simp] theorem memberEquiv_value (c : Code.{u}) (a : Members c) :
    (memberEquiv c a).1 = decode a.1 := rfl

@[simp] theorem memberEquiv_symm_value (c : Code.{u}) (a : El (· ∈ ·) (decode c)) :
    ((memberEquiv c).symm a).1 = encode a.1 := rfl

/-- A family of actual valid codes over interpreted code members. -/
abbrev Family (c : Code.{u}) := Members c → Code.{u}

/-- Decode the family using the actual inverse member comparison. -/
def decodedFamily {c : Code.{u}} (B : Family c) : El (· ∈ ·) (decode c) → HSet.{u} :=
  fun a => decode (B ((memberEquiv c).symm a))

theorem decodedFamily_at_member {c : Code.{u}} (B : Family c) (a : Members c) :
    decodedFamily B (memberEquiv c a) = decode (B a) :=
  congrArg (fun a => decode (B a)) ((memberEquiv c).symm_apply_apply a)

/-- Fibre comparison over the corresponding actual decoded domain member. -/
def fibreEquiv {c : Code.{u}} (B : Family c) (a : Members c) :
    Members (B a) ≃ El (· ∈ ·) (decodedFamily B (memberEquiv c a)) :=
  (memberEquiv (B a)).trans
    (Mettapedia.TypeTheory.DependentFamilySectionDescent.equalityEquiv
      (congrArg (El (· ∈ ·)) (decodedFamily_at_member B a).symm))

private theorem equalityEquiv_el_value {X Y : HSet.{u}} (same : X = Y)
    (a : El (· ∈ ·) X) :
    (Mettapedia.TypeTheory.DependentFamilySectionDescent.equalityEquiv
      (congrArg (El (· ∈ ·)) same) a).1 = a.1 := by
  cases same
  rfl

/-- Fibre comparison retains the actual decoded member through transport. -/
theorem fibreEquiv_value {c : Code.{u}} (B : Family c) (a : Members c)
    (b : Members (B a)) : (fibreEquiv B a b).1 = decode b.1 := by
  exact equalityEquiv_el_value (decodedFamily_at_member B a).symm (memberEquiv (B a) b)

abbrev Section {c : Code.{u}} (B : Family c) := ∀ a, Members (B a)

/-- Actual decoded sections, with inverse laws furnished by the member and
fibre comparisons rather than a representative-selection assumption. -/
def sectionEquiv {c : Code.{u}} (B : Family c) :
    Section B ≃ (∀ a, El (· ∈ ·) (decodedFamily B a)) :=
  Equiv.piCongr (memberEquiv c) (fibreEquiv B)

/-- Section decoding commutes with evaluation at a corresponding domain member. -/
theorem sectionEquiv_apply {c : Code.{u}} (B : Family c) (s : Section B)
    (a : Members c) : sectionEquiv B s (memberEquiv c a) = fibreEquiv B a (s a) :=
  Equiv.piCongr_apply_apply _ _ s a

/-- The evaluation comparison retains the actual decoded value. -/
theorem sectionEquiv_apply_value {c : Code.{u}} (B : Family c) (s : Section B)
    (a : Members c) : (sectionEquiv B s (memberEquiv c a)).1 = decode (s a).1 := by
  rw [sectionEquiv_apply]
  exact fibreEquiv_value B a (s a)

/-- Interpreted members of an actual set's code are its actual material members. -/
def encodedMemberEquiv (X : HSet.{u}) : Members (encode X) ≃ El (· ∈ ·) X :=
  (memberEquiv (encode X)).trans
    (Mettapedia.TypeTheory.DependentFamilySectionDescent.equalityEquiv
      (congrArg (El (· ∈ ·)) (decode_encode X)))

theorem encodedMemberEquiv_value (X : HSet.{u}) (a : Members (encode X)) :
    (encodedMemberEquiv X a).1 = decode a.1 :=
  equalityEquiv_el_value (decode_encode X) (memberEquiv (encode X) a)

theorem encodedMemberEquiv_symm_value (X : HSet.{u}) (a : El (· ∈ ·) X) :
    decode ((encodedMemberEquiv X).symm a).1 = a.1 := by
  rw [← encodedMemberEquiv_value, Equiv.apply_symm_apply]

abbrev Pairs {c : Code.{u}} (B : Family c) := Σ' a : Members c, Members (B a)

/-- Code-member dependent pairs and actual decoded dependent pairs. -/
def pairEquiv {c : Code.{u}} (B : Family c) :
    Pairs B ≃ (Σ' a : El (· ∈ ·) (decode c), El (· ∈ ·) (decodedFamily B a)) :=
  (Equiv.psigmaEquivSigma _).trans
    ((Equiv.sigmaCongr (memberEquiv c) (fibreEquiv B)).trans
      (Equiv.psigmaEquivSigma _).symm)

theorem pairEquiv_first_value {c : Code.{u}} (B : Family c) (ab : Pairs B) :
    (pairEquiv B ab).1.1 = decode ab.1.1 := rfl

theorem pairEquiv_second_value {c : Code.{u}} (B : Family c) (ab : Pairs B) :
    (pairEquiv B ab).2.1 = decode ab.2.1 :=
  fibreEquiv_value B ab.1 ab.2

/-- The actual material dependent-pair set, over the decoded family. -/
def materialSigma (p : Presentation.{u}) {c : Code.{u}} (B : Family c) : HSet.{u} :=
  sigmaSet (dependentReplacement p) HSet.union kuratowski (decode c) (decodedFamily B)

/-- The actual material set of total single-valued dependent graphs. -/
def materialPi (p : Presentation.{u}) {c : Code.{u}} (B : Family c) : HSet.{u} :=
  dependentProduct p (decode c) (decodedFamily B)

def sigmaCode (p : Presentation.{u}) {c : Code.{u}} (B : Family c) : Code.{u} :=
  encode (materialSigma p B)

def piCode (p : Presentation.{u}) {c : Code.{u}} (B : Family c) : Code.{u} :=
  encode (materialPi p B)

/-- Bounded closure for the code of the actual material dependent sum. -/
theorem sigmaCode_mem {U : ZFSet.{u + 1}} (hU : ZFSetUniverseClosure.Closed U)
    (h : carrierCode.{u} ∈ U) (p : Presentation.{u}) {c : Code.{u}} (B : Family c) :
    (sigmaCode p B).1 ∈ U :=
  hU.subset_mem h (code_subset_carrierCode (materialSigma p B))

/-- Bounded closure for the code of the actual material dependent product. -/
theorem piCode_mem {U : ZFSet.{u + 1}} (hU : ZFSetUniverseClosure.Closed U)
    (h : carrierCode.{u} ∈ U) (p : Presentation.{u}) {c : Code.{u}} (B : Family c) :
    (piCode p B).1 ∈ U :=
  hU.subset_mem h (code_subset_carrierCode (materialPi p B))

def boundedSigmaCode {U : ZFSet.{u + 1}} (hU : ZFSetUniverseClosure.Closed U)
    (h : carrierCode.{u} ∈ U) (p : Presentation.{u}) {c : Code.{u}} (B : Family c) :
    BoundedCode U := ⟨(sigmaCode p B).1, (sigmaCode p B).2, sigmaCode_mem hU h p B⟩

def boundedPiCode {U : ZFSet.{u + 1}} (hU : ZFSetUniverseClosure.Closed U)
    (h : carrierCode.{u} ∈ U) (p : Presentation.{u}) {c : Code.{u}} (B : Family c) :
    BoundedCode U := ⟨(piCode p B).1, (piCode p B).2, piCode_mem hU h p B⟩

/-- Actual members of the material sum's code are actual dependent code pairs. -/
def sigmaMembersEquiv (p : Presentation.{u}) {c : Code.{u}} (B : Family c) :
    Members (sigmaCode p B) ≃ Pairs B :=
  (encodedMemberEquiv (materialSigma p B)).trans
    ((HSet.sigmaSetEquiv p (decode c) (decodedFamily B)).trans (pairEquiv B).symm)

/-- Actual members of the material product's code are actual dependent sections. -/
def piMembersEquiv (p : Presentation.{u}) {c : Code.{u}} (B : Family c) :
    Members (piCode p B) ≃ Section B :=
  (encodedMemberEquiv (materialPi p B)).trans
    ((HSet.piSetEquiv p (decode c) (decodedFamily B)).trans (sectionEquiv B).symm)

/-- Encode a dependent pair using the actual material sum comparison. -/
def pairCode (p : Presentation.{u}) {c : Code.{u}} (B : Family c) (ab : Pairs B) :
    Members (sigmaCode p B) := (sigmaMembersEquiv p B).symm ab

/-- Pair coding retains both actual decoded values in its Kuratowski pair. -/
theorem pairCode_value (p : Presentation.{u}) {c : Code.{u}} (B : Family c)
    (ab : Pairs B) : decode (pairCode p B ab).1 = kpair (decode ab.1.1) (decode ab.2.1) := by
  change decode ((encodedMemberEquiv (materialSigma p B)).symm
    ((HSet.sigmaSetEquiv p (decode c) (decodedFamily B)).symm (pairEquiv B ab))).1 = _
  calc
    _ = ((HSet.sigmaSetEquiv p (decode c) (decodedFamily B)).symm (pairEquiv B ab)).1 :=
      encodedMemberEquiv_symm_value _ _
    _ = kpair (decode ab.1.1) (decode ab.2.1) := by
      change kpair (pairEquiv B ab).1.1 (pairEquiv B ab).2.1 = _
      rw [pairEquiv_first_value, pairEquiv_second_value]

/-- Abstract an actual section as a member of the actual material product code. -/
def abstractPi (p : Presentation.{u}) {c : Code.{u}} (B : Family c) (s : Section B) :
    Members (piCode p B) := (piMembersEquiv p B).symm s

/-- Apply a coded material graph, retaining the result code and fibre membership. -/
def applyPi (p : Presentation.{u}) {c : Code.{u}} (B : Family c)
    (g : Members (piCode p B)) (a : Members c) : Members (B a) :=
  piMembersEquiv p B g a

@[simp] theorem applyPi_abstract (p : Presentation.{u}) {c : Code.{u}} (B : Family c)
    (s : Section B) (a : Members c) : applyPi p B (abstractPi p B s) a = s a := by
  exact congrFun ((piMembersEquiv p B).apply_symm_apply s) a

@[simp] theorem abstractPi_apply (p : Presentation.{u}) {c : Code.{u}} (B : Family c)
    (g : Members (piCode p B)) : abstractPi p B (applyPi p B g) = g :=
  (piMembersEquiv p B).symm_apply_apply g

/-- Decoding abstraction gives the actual graph of the actual decoded section. -/
theorem abstractPi_value (p : Presentation.{u}) {c : Code.{u}} (B : Family c)
    (s : Section B) : decode (abstractPi p B s).1 =
      functionGraph (dependentReplacement p) kuratowski (sectionEquiv B s) := by
  change decode ((encodedMemberEquiv (materialPi p B)).symm
    ((HSet.piSetEquiv p (decode c) (decodedFamily B)).symm (sectionEquiv B s))).1 = _
  exact encodedMemberEquiv_symm_value _ _

/-- Coded graph application agrees with actual material graph evaluation. -/
theorem applyPi_value (p : Presentation.{u}) {c : Code.{u}} (B : Family c)
    (g : Members (piCode p B)) (a : Members c) : decode (applyPi p B g a).1 =
      (HSet.piSetEquiv p (decode c) (decodedFamily B)
        (encodedMemberEquiv (materialPi p B) g) (memberEquiv c a)).1 := by
  have same := (sectionEquiv B).apply_symm_apply
    (HSet.piSetEquiv p (decode c) (decodedFamily B)
      (encodedMemberEquiv (materialPi p B) g))
  have values := congrArg (fun s => (s (memberEquiv c a)).1) same
  exact (sectionEquiv_apply_value B (piMembersEquiv p B g) a).symm.trans values

/-- Reindex a code family along an actual map of interpreted domain members. -/
def reindexFamily {c d : Code.{u}} (σ : Members c → Members d) (B : Family d) : Family c :=
  B ∘ σ

/-- The corresponding map of actual decoded domain members. -/
def decodedSub {c d : Code.{u}} (σ : Members c → Members d) :
    El (· ∈ ·) (decode c) → El (· ∈ ·) (decode d) :=
  fun a => memberEquiv d (σ ((memberEquiv c).symm a))

@[simp] theorem decodedSub_at_member {c d : Code.{u}} (σ : Members c → Members d)
    (a : Members c) : decodedSub σ (memberEquiv c a) = memberEquiv d (σ a) := by
  simp only [decodedSub, Equiv.symm_apply_apply]

@[simp] theorem decodedSub_id (c : Code.{u}) : decodedSub (id : Members c → Members c) = id := by
  funext a
  exact (memberEquiv c).apply_symm_apply a

theorem decodedSub_comp {c d e : Code.{u}} (σ : Members c → Members d)
    (τ : Members d → Members e) : decodedSub (τ ∘ σ) = decodedSub τ ∘ decodedSub σ := by
  funext a
  simp only [decodedSub, Function.comp_apply, Equiv.symm_apply_apply]

/-- Actual family substitution agrees after decoding. -/
theorem decodedFamily_reindex {c d : Code.{u}} (σ : Members c → Members d)
    (B : Family d) (a : El (· ∈ ·) (decode c)) :
    decodedFamily (reindexFamily σ B) a = decodedFamily B (decodedSub σ a) := by
  simp only [decodedFamily, reindexFamily, decodedSub, Function.comp_apply,
    Equiv.symm_apply_apply]

def restrictSection {c d : Code.{u}} (σ : Members c → Members d) (B : Family d)
    (s : Section B) : Section (reindexFamily σ B) := fun a => s (σ a)

/-- Section substitution commutes with the actual decoded member and fibre
comparisons, including transport along the family comparison. -/
theorem sectionEquiv_reindex {c d : Code.{u}} (σ : Members c → Members d)
    (B : Family d) (s : Section B) (a : El (· ∈ ·) (decode c)) :
    transport (decodedFamily_reindex σ B a)
      (sectionEquiv (reindexFamily σ B) (restrictSection σ B s) a) =
        sectionEquiv B s (decodedSub σ a) := by
  obtain ⟨a, rfl⟩ := (memberEquiv c).surjective a
  apply El.ext HSet.propositional
  calc
    _ = decode (s (σ a)).1 :=
      (transport_fst _ _).trans
        (sectionEquiv_apply_value (reindexFamily σ B) (restrictSection σ B s) a)
    _ = (sectionEquiv B s (decodedSub σ (memberEquiv c a))).1 := by
      rw [decodedSub_at_member]
      exact (sectionEquiv_apply_value B s (σ a)).symm

/-- Sums map covariantly: retain the dependent value and map its domain member. -/
def mapSigma (p : Presentation.{u}) {c d : Code.{u}} (σ : Members c → Members d)
    (B : Family d) (x : Members (sigmaCode p (reindexFamily σ B))) :
    Members (sigmaCode p B) :=
  pairCode p B ⟨σ (sigmaMembersEquiv p (reindexFamily σ B) x).1,
    (sigmaMembersEquiv p (reindexFamily σ B) x).2⟩

theorem sigmaMembersEquiv_map (p : Presentation.{u}) {c d : Code.{u}}
    (σ : Members c → Members d) (B : Family d)
    (x : Members (sigmaCode p (reindexFamily σ B))) :
    sigmaMembersEquiv p B (mapSigma p σ B x) =
      ⟨σ (sigmaMembersEquiv p (reindexFamily σ B) x).1,
        (sigmaMembersEquiv p (reindexFamily σ B) x).2⟩ :=
  (sigmaMembersEquiv p B).apply_symm_apply _

theorem mapSigma_pair (p : Presentation.{u}) {c d : Code.{u}}
    (σ : Members c → Members d) (B : Family d) (ab : Pairs (reindexFamily σ B)) :
    mapSigma p σ B (pairCode p (reindexFamily σ B) ab) = pairCode p B ⟨σ ab.1, ab.2⟩ := by
  unfold mapSigma pairCode
  rw [Equiv.apply_symm_apply]

@[simp] theorem mapSigma_id (p : Presentation.{u}) {c : Code.{u}} (B : Family c)
    (x : Members (sigmaCode p B)) : mapSigma p id B x = x := by
  exact (sigmaMembersEquiv p B).symm_apply_apply x

theorem mapSigma_comp (p : Presentation.{u}) {c d e : Code.{u}}
    (σ : Members c → Members d) (τ : Members d → Members e) (B : Family e)
    (x : Members (sigmaCode p (reindexFamily (τ ∘ σ) B))) :
    mapSigma p (τ ∘ σ) B x = mapSigma p τ B (mapSigma p σ (reindexFamily τ B) x) := by
  have same := congrArg
    (fun ab : Pairs (reindexFamily τ B) => pairCode p B ⟨τ ab.1, ab.2⟩)
    (sigmaMembersEquiv_map p σ (reindexFamily τ B) x)
  exact same.symm

/-- Products restrict contravariantly along the domain map. No equality between
the source and target material product sets is asserted. -/
def restrictPi (p : Presentation.{u}) {c d : Code.{u}} (σ : Members c → Members d)
    (B : Family d) (g : Members (piCode p B)) :
    Members (piCode p (reindexFamily σ B)) :=
  abstractPi p (reindexFamily σ B) (restrictSection σ B (applyPi p B g))

@[simp] theorem restrictPi_apply (p : Presentation.{u}) {c d : Code.{u}}
    (σ : Members c → Members d) (B : Family d) (g : Members (piCode p B)) (a : Members c) :
    applyPi p (reindexFamily σ B) (restrictPi p σ B g) a = applyPi p B g (σ a) :=
  applyPi_abstract p (reindexFamily σ B) _ a

@[simp] theorem restrictPi_id (p : Presentation.{u}) {c : Code.{u}} (B : Family c)
    (g : Members (piCode p B)) : restrictPi p id B g = g := by
  apply (piMembersEquiv p B).injective
  funext a
  exact restrictPi_apply p id B g a

theorem restrictPi_comp (p : Presentation.{u}) {c d e : Code.{u}}
    (σ : Members c → Members d) (τ : Members d → Members e) (B : Family e)
    (g : Members (piCode p B)) :
    restrictPi p (τ ∘ σ) B g = restrictPi p σ (reindexFamily τ B) (restrictPi p τ B g) := by
  apply (piMembersEquiv p (reindexFamily (τ ∘ σ) B)).injective
  funext a
  change applyPi p (reindexFamily (τ ∘ σ) B) _ a =
    applyPi p (reindexFamily σ (reindexFamily τ B)) _ a
  rw [restrictPi_apply, restrictPi_apply, restrictPi_apply]
  rfl

/-- Restriction of actual material graphs commutes with abstraction. -/
theorem restrictPi_abstract (p : Presentation.{u}) {c d : Code.{u}}
    (σ : Members c → Members d) (B : Family d) (s : Section B) :
    restrictPi p σ B (abstractPi p B s) =
      abstractPi p (reindexFamily σ B) (restrictSection σ B s) := by
  apply (piMembersEquiv p (reindexFamily σ B)).injective
  funext a
  change applyPi p (reindexFamily σ B) _ a = applyPi p (reindexFamily σ B) _ a
  rw [restrictPi_apply, applyPi_abstract, applyPi_abstract]
  rfl

/-- Inhabitation of the actual product code is equivalent to a supplied actual
section. No inference from mere fibrewise nonemptiness is made. -/
theorem nonempty_piMembers_iff (p : Presentation.{u}) {c : Code.{u}} (B : Family c) :
    Nonempty (Members (piCode p B)) ↔ Nonempty (Section B) :=
  ⟨fun ⟨g⟩ => ⟨piMembersEquiv p B g⟩,
    fun ⟨s⟩ => ⟨abstractPi p B s⟩⟩

/-- A real empty fibre over a real domain member prevents any product member. -/
theorem no_piCode_of_empty_fibre (p : Presentation.{u}) {c : Code.{u}} (B : Family c)
    (a : Members c) (empty : decode (B a) = ∅) : ¬ Nonempty (Members (piCode p B)) := by
  rintro ⟨g⟩
  have b := memberEquiv (B a) (applyPi p B g a)
  exact notMem_empty b.1 (empty ▸ b.2)

/-! ## A non-well-founded family inside the interpreted code carrier -/

def quineDomain : Code.{u} := encode {quineAtom.{u}}

def quineArgument : Members quineDomain.{u} :=
  (encodedMemberEquiv {quineAtom.{u}}).symm ⟨quineAtom, mem_singleton_self _⟩

theorem quineArgument_value : decode quineArgument.{u}.1 = quineAtom.{u} :=
  encodedMemberEquiv_symm_value _ _

def quineFamily : Family quineDomain.{u} := fun _ => encode {quineAtom.{u}}

def quineSection : Section quineFamily.{u} := fun _ => quineArgument

def quineGraph (p : Presentation.{u}) : Members (piCode p quineFamily.{u}) :=
  abstractPi p quineFamily quineSection

/-- The Quine-containing family has an actual material function graph. -/
theorem quinePi_inhabited (p : Presentation.{u}) :
    Nonempty (Members (piCode p quineFamily.{u})) := ⟨quineGraph p⟩

/-- Application of that graph returns the non-well-founded Quine atom. -/
theorem quineGraph_apply_value (p : Presentation.{u}) :
    decode (applyPi p quineFamily (quineGraph p) quineArgument).1 = quineAtom.{u} := by
  rw [quineGraph, applyPi_abstract]
  exact quineArgument_value

/-- The actual decoded family contains a non-well-founded member. -/
theorem quineFamily_not_wf (a : Members quineDomain.{u}) : ¬ (decode (quineFamily a)).WF := by
  change ¬ (decode (encode {quineAtom.{u}})).WF
  rw [decode_encode]
  exact not_wf_of_mem (mem_singleton_self _) not_wf_quineAtom

/-- The material product is exactly the singleton of the singleton Quine graph. -/
theorem quineMaterialPi (p : Presentation.{u}) :
    materialPi p quineFamily.{u} = {{kpair quineAtom quineAtom}} := by
  unfold materialPi decodedFamily quineFamily quineDomain
  simp only [decode_encode]
  exact (congrArg (fun X : HSet.{u} => dependentProduct p X (fun _ => {quineAtom}))
    (decode_encode {quineAtom})).trans (dependentProduct_quine_singleton p)

theorem quineGraph_value (p : Presentation.{u}) :
    decode (quineGraph p).1 = {kpair quineAtom.{u} quineAtom} := by
  have member : decode (quineGraph p).1 ∈ materialPi p quineFamily :=
    (encodedMemberEquiv_value _ _) ▸
      (encodedMemberEquiv (materialPi p quineFamily) (quineGraph p)).2
  exact mem_singleton.mp (quineMaterialPi p ▸ member)

/-- The graph itself retains non-well-founded values; it is not in the
well-founded hyperset fragment merely because its host code is well-founded. -/
theorem quineGraph_not_wf (p : Presentation.{u}) : ¬ (decode (quineGraph p).1).WF := by
  rw [quineGraph_value]
  apply not_wf_of_mem (mem_singleton_self _)
  intro hwf
  have first := hwf.fst
  rw [fst_kpair] at first
  exact not_wf_quineAtom first

/-- The actual product code lies in every supplied closed carrier bound. -/
theorem quinePiCode_mem {U : ZFSet.{u + 1}} (hU : ZFSetUniverseClosure.Closed U)
    (h : carrierCode.{u} ∈ U) (p : Presentation.{u}) :
    (piCode p quineFamily.{u}).1 ∈ U := piCode_mem hU h p _

/-- Its actual member graph's code also lies in that same bound. -/
theorem quineGraphCode_mem {U : ZFSet.{u + 1}} (hU : ZFSetUniverseClosure.Closed U)
    (h : carrierCode.{u} ∈ U) (p : Presentation.{u}) :
    (quineGraph p).1.1 ∈ U := validCode_mem hU h _

/-- Negative family control: the nonempty Quine-containing domain with an empty
fibre has no graph, even though its product code is bounded. -/
theorem quineEmptyFamily_no_product (p : Presentation.{u}) :
    ¬ Nonempty (Members (piCode p (fun _ : Members quineDomain.{u} => encode ∅))) :=
  no_piCode_of_empty_fibre p _ quineArgument (decode_encode ∅)

/-! ## Host membership and interpreted membership are different relations -/

/-- Interpreted membership of valid codes admits self-membership. -/
theorem quine_codeMem_self : codeMem (encode quineAtom.{u}).1 (encode quineAtom).1 :=
  codeMem_code.mpr quineAtom_mem_self

/-- Host membership of every code remains irreflexive. -/
theorem hostCode_not_mem_self (c : Code.{u}) : c.1 ∉ c.1 := ZFSet.mem_irrefl _

/-- In particular, the self-membered decoded atom is not a self-membered host code. -/
theorem quine_membership_boundary :
    codeMem (encode quineAtom.{u}).1 (encode quineAtom).1 ∧
      (encode quineAtom.{u}).1 ∉ (encode quineAtom).1 :=
  ⟨quine_codeMem_self, hostCode_not_mem_self _⟩

/-- Replacing the interpreted relation by host membership would invalidate the
member interpretation, already on the Quine atom. -/
theorem codeMem_not_host_membership :
    ¬ (∀ a b : Code.{u}, codeMem a.1 b.1 ↔ b.1 ∈ a.1) := by
  intro same
  exact hostCode_not_mem_self (encode quineAtom)
    ((same (encode quineAtom) (encode quineAtom)).mp quine_codeMem_self)

end

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilies
