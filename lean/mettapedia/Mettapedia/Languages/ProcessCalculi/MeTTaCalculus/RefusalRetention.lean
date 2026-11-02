import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RefusalRetention.PollLoop
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RefusalRetention.FairnessAndSearch

/-!
# A refused call retained and polled

A native reader that resumes a refused call with the same receiving context retains the task and
never observes it (`PollLoop`); that holds in every run, including runs strongly fair for every
step kind (`FairnessAndSearch`). The repair counts the refusal unless the call is registered on a
wake source; counting is exactly the refusal semantics of `Machines.RefusalObservation` on a
single call.

`PollLoop.PaidPrefixContinuation` also separates retrying a retained suffix
from restarting its source after a visible prefix. Two requesting contexts can
select different suffix values while sharing that prefix once; restarting after
a nonempty prefix is observably different because it duplicates the effects.
This is the checkpoint obligation at a first world-distinguishing read, not a
claim about the compiled runtime.
-/
