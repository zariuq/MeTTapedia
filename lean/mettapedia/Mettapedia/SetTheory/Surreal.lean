import Mettapedia.SetTheory.Surreal.SignExpansion
import Mettapedia.SetTheory.Surreal.Simplicity
import Mettapedia.SetTheory.Surreal.Birthday
import Mettapedia.SetTheory.Surreal.Cut
import Mettapedia.SetTheory.Surreal.BoundedBirthday
import Mettapedia.SetTheory.Surreal.CutConstruction
import Mettapedia.SetTheory.Surreal.OptionWitness
import Mettapedia.SetTheory.Surreal.Negation
import Mettapedia.SetTheory.Surreal.IntegerEmbedding
import Mettapedia.SetTheory.Surreal.Addition
import Mettapedia.SetTheory.Surreal.AdditionMeasure
import Mettapedia.SetTheory.Surreal.AdditionOrder
import Mettapedia.SetTheory.Surreal.AdditiveInverse
import Mettapedia.SetTheory.Surreal.Associativity
import Mettapedia.SetTheory.Surreal.AddGroup
import Mettapedia.SetTheory.Surreal.AdditionBirthday
import Mettapedia.SetTheory.Surreal.PositiveFloor
import Mettapedia.SetTheory.Surreal.HalvingLadder
import Mettapedia.SetTheory.Surreal.DyadicEmbedding
import Mettapedia.SetTheory.Surreal.IntegerArithmetic
import Mettapedia.SetTheory.Surreal.DyadicExamples
import Mettapedia.SetTheory.Surreal.FiniteDay
import Mettapedia.SetTheory.Surreal.OptionBounds
import Mettapedia.SetTheory.Surreal.Doubling
import Mettapedia.SetTheory.Surreal.FiniteBirthday

/-!
# Surreal numbers as sign expansions

The whole lane, in dependency order.

## The carrier

`SignExpansion` — `PreSurreal` is a length together with a sign at each
position below it; `Surreal` is the quotient by agreement, linearly ordered by
the first position where two expansions differ. `Simplicity` and `Birthday`
develop the length as the birthday, and `Cut` fixes the canonical option
families: *every* younger number on the correct side.

## The cut

`BoundedBirthday` shows those families are small, `CutConstruction` builds the
simplest number strictly between any separated pair and proves it unique, and
`OptionWitness` supplies the witnesses that keep the later inductions from
being vacuous.

## Arithmetic

`Negation` is definable outright, because reversing every sign is a closed form
on expansions. `Addition` defines Conway's sum by the cut recursion but can
only characterise it *conditionally*, on the sum's option families being
separated.

`AdditionMeasure` supplies the order that makes the mutual recursion terminate
— the multiset of birthdays under Dershowitz–Manna — and `AdditionOrder`
discharges the separation obligation and strict monotonicity together, so the
sum is Conway's cut unconditionally.

The rest follows: `AdditiveInverse`, `Associativity`, then `AddGroup`
assembles `AddCommGroup` and `IsOrderedCancelAddMonoid` over the existing
`LinearOrder`, and `AdditionBirthday` bounds a sum's birthday by the natural
sum of the summands'.

## The executable dyadics

`PositiveFloor` proves that `mk (dyadicPre k)` is the least positive number
born by day `k + 1`, which bounds the option families of the halving ladder
without enumerating them. `HalvingLadder` uses those bounds for the one
theorem the interpretation rests on, `ladder (k+1) + ladder (k+1) = ladder k`.

`DyadicEmbedding` then reads `m / 2^k` as `m • ladder k`, so additivity is
`add_zsmul` and order preservation *and reflection* are
`zsmul_lt_zsmul_iff_left`. `IntegerArithmetic` proves `ofNat n + 1 = ofNat (n+1)`
from the cut and so identifies the sign-expansion integer embedding with the
integer-multiple one — without it the lane would carry two unrelated integer
embeddings. `DyadicExamples` carries the computed checks and the rejection
controls.

## The characterisation

`FiniteDay` proves the numbers born by a finite day form a *finite* set — not
merely a small one — so the option families attain their bounds.
`OptionBounds` records what a bracket forces about the brackets of its own
members, and `Doubling` proves the theorem the converse rests on:

```
c + c = a + b        a greatest left option, b least right option
```

purely additively, with no birthday of a dyadic computed. `FiniteBirthday`
then runs the induction: every number born by day `n` is an integer multiple
of `ladder n`, so **finite-birthday surreals are precisely the represented
dyadics** (`birthday_lt_omega0_iff_exists_dyadic`).

## Not here

Multiplication, the comparison with level series, and adequacy against an
external `SNo` development are separate obligations and are not addressed by
any file in this directory.
-/
