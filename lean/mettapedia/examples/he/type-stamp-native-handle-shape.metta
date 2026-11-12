; A literal kind tag can affect typing even when child kind/types agree.
(: NativeHandle H)
(: mork-space K)
(: other K)
!(let $state (new-state (NativeHandle mork-space 0))
   (let $_ (change-state! $state (NativeHandle other 0)) (get-state $state)))
