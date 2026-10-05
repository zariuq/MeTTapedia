import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Judgment
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Structural
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Functionality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Algorithm
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Generation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Conservativity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHeadNormalization
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Decidability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.RigidHeads
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.NeutralHeads
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Renaming
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.NormalizingLift
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Synthesis
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.BelowDecidability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Checking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.WrittenDomains
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WrittenDomains
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Cumulative
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirst
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirstDefinition
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirstEquations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CheckingAlgorithm
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CallAbstraction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursiveCallAbstraction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RootReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CallReordering
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirstTelescope
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursorDerivation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTree
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTreeCompile
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTreeConfluence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTreeExtension
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTreeTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ConstantDeclarations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.PartialConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ConstantInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.HeadFormControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.NeutralSubstitutionControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.HeadMorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ElaborationHeadMap
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.PackageSum
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.DeclarationRewriting
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ParameterizedDatatypes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ParameterizedPackage
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ConstantRenaming
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.TheoremDefinitions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.TheoremStability

/-!
# Typed definitional equality

The declarative judgment `Γ ⊢ a ≡ b : A` with eta for functions and pairs,
its structural laws and presuppositions, the type-directed conversion
algorithm, and the normalization model: a logical relation over a generic
equality, validity, the fundamental lemma, and the facts about the weak-head
forms of types it supplies, over which the consequences are stated:
injectivity and discrimination of type formers, preservation, soundness of the
conversion algorithm and conservativity over untyped conversion; an algorithmic equality with weak-head
reduction, type-directed eta and spine comparison, stable under renaming, whose instance of the model
makes the conversion algorithm complete and decides the typed equality between
terms of a type; the kernel's bidirectional typing, whose synthesized types
are principal, which is sound, and complete on the bidirectional fragment, and
the refutations principal types justify; the declared identity eliminator is a
semantic constant whose linear rule preserves typing; declared simple
inductive types, their constructors and their recursors are semantic
constants, constructors are injective and distinct, and the recursor's
computation rules preserve typing; a datatype may carry a parameter telescope,
and the empty telescope is that simple inductive; definitions by one equation and by
structural recursion are semantic constants whose equations preserve typing;
a package extended by an admissible list of datatypes and definitions computes as the package
extended by one case tree for each declaration, its root steps start at the constants that
compute and never overlap, and over a definition by constructor patterns its rewriting is
Church–Rosser;
typed terms are weakly head normalizing; and the cumulative tower, alone, with
the eliminator, with the natural numbers, and with addition defined by
structural recursion, is an instance satisfying every hypothesis; the tower
alone decides its typed equality.

Terms whose λs may carry a written domain have their own typing judgment, in
which a written domain must be a type equal to the domain its λ is checked
at: it erases to typing, every typed term has a fully written twin, and it is
stable under renaming, substitution and conversion; steps on written terms
simulate the calculus's steps in both directions through erasure, preserve
the judgment and are typed equalities of the erasures; and equality of
written terms is equality of erasures between terms typed at a common type.
A λ is not typed at a function type whose domain differs from its written
domain by the outer type former or, among universes, by the level.

Cumulativity is a judgment of the calculus, `Γ ⊢ A ⊑ B`: a type is usable at
another. It is generated by type equality, the universe order, dependent
function types with equal domains and codomains below, and dependent pair types
with both components below, and a term of a type is a term of every type above
it. It inverts on every former, is stable under renaming, substitution and
changes of context along it, holds in the normalization model through the
inclusions of the dependent function and pair interpretations, and is decided
once the rule package decides its universe order. A family into one universe
is a family into every universe above it, together with its η-expansion. The
kernel's synthesized types are principal, reflexivity having a least type
exactly at rigid types; two terms whose synthesized types have no common upper
bound are equal at no type. In the tower, a pair of a small type and an
element is a pair at the next universe and not conversely; domains are
invariant in both directions; reflexivity proofs at a raised carrier, of a
type or of a family, have no least type, while at a rigid carrier they do; and
the kernel checks a family and its η-expansion at the raised codomain and
refuses the family over another domain. In a telescope of closed types,
moving one entry to the front or to the back is a renaming along which typing
and typed equality transport, adjacent independent entries exchange, a context
renaming lifts under further entries, and two functions of the telescope are
equal when their applications to its variables are. A definition by
structural recursion whose calls change an argument before the scrutinee is
admitted through its scrutinee-first form: the move of the field block is a
context renaming between the two equation contexts, the definition passing
its arguments to that form has, at a constructor pattern, the form's full
application with the pattern at its scrutinee on the right of its δ-step, and
the two matches assign the pattern variables the same arguments. The authored
definition's equation at a constructor pattern is a typed equality: its δ-step
followed by the scrutinee-first form's ι-step; and an authored recursive call is
equal to the scrutinee-first call. In the tower, `add-onto`, `rev-onto` and
`dfa-run`, whose recursive calls change their accumulators, satisfy their
authored equations with their authored right-hand sides.

The kernel's synthesis, checking and subtype test are relations over the rule
package's reduction and conversion algorithm, sound in every normalization
model whose declared constant types are types. A right-hand side of a
structural recursion checked by the kernel with the defined constant declared
and not computing is, with each recursive call replaced by its recursive
hypothesis, a right-hand side checked by the kernel in the hypothesis context
without the constant: reduction, conversion, the subtype test and checking all
reflect along the substitution of calls for hypotheses, a synthesized type up
to reduction. The kernel's check thus gives the premise of the recursion's
semantic theorem in every normalization model of the rule package without the
constant; a recursor's computation rules reflect along that substitution. In
the tower, `add-onto`'s scrutinee-first form is declared from the kernel's
check of its right-hand sides over the natural numbers with their recursor.

The kernel's rewriting of an authored right-hand side, each call of the
authored function turned into the scrutinee-first call on the moved
arguments, is a reduct of that right-hand side under the admitted definition,
so typed-equal to it; and the declared function satisfies every authored
equation with its authored right-hand side, an arbitrary term the rewriting is
applied to. These hold for dependent telescopes, where the entries before the
scrutinee depend on each other: moving a closed scrutinee type to the front of
such a telescope is a context renaming, so typing and typed equality transport
to the scrutinee-first telescope.

A definition by structural recursion is derivable from the recursor of its
inductive type. The recursor applied to the motive `λ t. Π ȳ. C` and to
methods built from the right-hand sides, each typed at its case type,
satisfies every equation of the definition, with its own recursive calls in
place of the definition's: one ι-step followed by β-steps. In the tower, the
scrutinee-first forms of `add-onto`, `rev-onto` and `dfa-run`, written with
the recursors of the numbers and of the lists, satisfy their equations with
the changing accumulator.

The cumulative tower's instances and controls described here ("in the tower")
are in the calculus's instance modules (`ParameterizedPiSigmaId.Instances`),
which import these results.
-/
