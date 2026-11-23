; Experimental local actor adapter over the emitted Erlang GSLT evaluator.
; Native rho transfers explicit state tasks. Actor effects and kernel epochs
; are recorded separately; effects are not represented as RuleJobReceipts.
; Load after gslt_erlang, gslt_erlang_rho and the generated mailbox kernel.

(: gslt:er-actor:undefined (-> %Undefined%))
(= (gslt:er-actor:undefined) (PApp "ErAtom" (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" (LCons (PApp "R16Nibble7" LNil) (LCons (PApp "R16Nibble5" LNil) (LCons (PApp "R16Nibble6" LNil) (LCons (PApp "R16Nibble14" LNil) (LCons (PApp "R16Nibble6" LNil) (LCons (PApp "R16Nibble4" LNil) (LCons (PApp "R16Nibble6" LNil) (LCons (PApp "R16Nibble5" LNil) (LCons (PApp "R16Nibble6" LNil) (LCons (PApp "R16Nibble6" LNil) (LCons (PApp "R16Nibble6" LNil) (LCons (PApp "R16Nibble9" LNil) (LCons (PApp "R16Nibble6" LNil) (LCons (PApp "R16Nibble14" LNil) (LCons (PApp "R16Nibble6" LNil) (LCons (PApp "R16Nibble5" LNil) (LCons (PApp "R16Nibble6" LNil) (LCons (PApp "R16Nibble4" LNil) LNil)))))))))))))))))) RNone) LNil)))

(: gslt:er-actor:empty-mailbox (-> %Undefined%))
(= (gslt:er-actor:empty-mailbox)
  (PApp "ErMailbox" (LCons (PApp "ErValuesNil" LNil)
    (LCons (PApp "ErValuesNil" LNil) (LCons (PApp "ErValuesNil" LNil) LNil)))))
(: gslt:er-actor:pid (-> Number %Undefined%))
(= (gslt:er-actor:pid $identity)
  (let* (($digits (gslt:word16:digits $identity))
         ($word (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $digits RNone)))
    (PApp "ErPid" (LCons $word LNil))))
(: gslt:er-actor:pid-value (-> Atom %Undefined%))
(= (gslt:er-actor:pid-value $value)
  (case $value (((PApp "ErPid" (LCons $word LNil)) (gslt:word16:vector-value $word)) ($bad None))))
(: gslt:er-actor:get (-> Number Atom %Undefined%))
(= (gslt:er-actor:get $pid $processes)
  (case $processes
    ((LNil None)
     ((LCons (ErLocal $identity $mailbox $machine) $rest)
      (if (== $pid $identity) (Some (ErLocal $identity $mailbox $machine))
        (gslt:er-actor:get $pid $rest))))))
(: gslt:er-actor:put (-> Number Atom Atom %Undefined%))
(= (gslt:er-actor:put $pid $replacement $processes)
  (case $processes
    ((LNil LNil)
     ((LCons (ErLocal $identity $mailbox $machine) $rest)
      (if (== $pid $identity) (LCons $replacement $rest)
        (let $tail (gslt:er-actor:put $pid $replacement $rest)
          (LCons (ErLocal $identity $mailbox $machine) $tail)))))))
(: gslt:er-actor:begin (-> Atom %Undefined%))
(= (gslt:er-actor:begin $machine)
  (let $mailbox (gslt:er-actor:empty-mailbox)
    (ErActorSystem (LCons (ErLocal 0 $mailbox $machine) LNil) LNil 1 LNil)))

(: gslt:er-actor:resume (-> Atom Atom %Undefined%))
(= (gslt:er-actor:resume $machine $source)
  (case $machine
    (((ErMachine $phase $plan $standard $runner $epochs)
      (let* (($next (gslt:runner:begin ClassSearch $plan $standard $source))
             ($history (LCons (ErEpoch $plan $runner) $epochs)))
        (ErMachine ErRunning $plan $standard $next $history))))))
(: gslt:er-actor:return (-> Atom Atom Atom %Undefined%))
(= (gslt:er-actor:return $machine $values $continuation)
  (let $source (gslt:er:pack2 "ErReturn" $values $continuation)
    (gslt:er-actor:resume $machine $source)))
(: gslt:er-actor:badarg (-> Atom Atom %Undefined%))
(= (gslt:er-actor:badarg $machine $continuation)
  (let $source (gslt:er:pack2 "ErRaise" (PApp "ErBadarg" LNil) $continuation)
    (gslt:er-actor:resume $machine $source)))
(: gslt:er-actor:store (-> Number Atom Atom Atom Atom %Undefined%))
(= (gslt:er-actor:store $pid $mailbox $machine $effect $system)
  (case $system
    (((ErActorSystem $processes $network $fresh $history)
      (let $updated (gslt:er-actor:put $pid (ErLocal $pid $mailbox $machine) $processes)
        (ErActorSystem $updated $network $fresh (LCons $effect $history)))))))

(: gslt:er-actor:execute (-> Number Number Number Atom %Undefined%))
(= (gslt:er-actor:execute $pid $ticks $quantum $system)
  (case $system
    (((ErActorSystem $processes $network $fresh $history)
      (case (gslt:er-actor:get $pid $processes)
        ((None $system)
         ((Some (ErLocal $identity $mailbox $machine))
          (let $advanced (gslt:er:advance $ticks $quantum $machine)
            (case $advanced
              (((ErMachine ErSuspended $plan $standard
                  (ClassMachine $status
                    (PApp "ErActorRequest" (LCons (PApp $operation LNil)
                      (LCons $arguments (LCons $continuation LNil))))
                    $query $states $receipts) $epochs)
                (gslt:er-actor:request $pid $mailbox $advanced $operation $arguments $continuation $system))
               ($other (gslt:er-actor:store $pid $mailbox $advanced (ErLocalWork $pid) $system)))))))))))

)
(: gslt:er-actor:request (-> Number Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:er-actor:request $pid $mailbox $machine $operation $arguments $continuation $system)
  (case $operation
    (("ErSelf"
      (case $arguments
        (((PApp "ErValuesNil" LNil)
          (let* (($value (gslt:er-actor:pid $pid)) ($values (gslt:er:pack2 "ErValuesCons" $value (PApp "ErValuesNil" LNil)))
                 ($resumed (gslt:er-actor:return $machine $values $continuation)))
            (gslt:er-actor:store $pid $mailbox $resumed (ErActorEffect $pid $operation) $system)))
         ($bad (gslt:er-actor:refuse $pid $mailbox $machine $continuation $system)))))
     ("ErSpawn" (gslt:er-actor:spawn $pid $mailbox $machine $arguments $continuation $system))
     ("ErSend" (gslt:er-actor:send $pid $mailbox $machine $arguments $continuation $system))
     ("ErPeekMessage" (gslt:er-actor:mailbox $pid $mailbox $machine $operation $arguments $continuation $system))
     ("ErNextMessage" (gslt:er-actor:mailbox $pid $mailbox $machine $operation $arguments $continuation $system))
     ("ErRemoveMessage" (gslt:er-actor:mailbox $pid $mailbox $machine $operation $arguments $continuation $system))
     ("ErWaitInfinity" (gslt:er-actor:mailbox $pid $mailbox $machine $operation $arguments $continuation $system))
     ($bad (ErActorDiagnostic UnknownOperation $system)))))
(: gslt:er-actor:refuse (-> Number Atom Atom Atom Atom %Undefined%))
(= (gslt:er-actor:refuse $pid $mailbox $machine $continuation $system)
  (let $resumed (gslt:er-actor:badarg $machine $continuation)
    (gslt:er-actor:store $pid $mailbox $resumed (ErActorFault $pid Badarg) $system)))

(: gslt:er-actor:spawn (-> Number Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:er-actor:spawn $pid $mailbox $machine $arguments $continuation $system)
  (case $arguments
    (((PApp "ErValuesCons" (LCons
        (PApp "ErClosure" (LCons (PApp "ErZero" LNil) (LCons $function (LCons $captured LNil))))
        (LCons (PApp "ErValuesNil" LNil) LNil)))
      (case $system
        (((ErActorSystem $processes $network $fresh $history)
          (case (gslt:er-actor:get $fresh $processes)
            (((Some $used) (ErActorDiagnostic PidCollision $system))
             (None
              (case $machine
                (((ErMachine $phase $plan $standard $runner $epochs)
                  (let* (($closure (PApp "ErClosure" (LCons (PApp "ErZero" LNil) (LCons $function (LCons $captured LNil)))))
                         ($source (gslt:er:pack3 "ErApply" $closure (PApp "ErValuesNil" LNil) (PApp "ErKDone" LNil)))
                         ($child (gslt:er:begin $plan $standard $source))
                         ($empty (gslt:er-actor:empty-mailbox))
                         ($value (gslt:er-actor:pid $fresh))
                         ($values (gslt:er:pack2 "ErValuesCons" $value (PApp "ErValuesNil" LNil)))
                         ($parent (gslt:er-actor:return $machine $values $continuation))
                         ($updated (gslt:er-actor:put $pid (ErLocal $pid $mailbox $parent) $processes))
                         ($all (gslt:automata:append $updated (LCons (ErLocal $fresh $empty $child) LNil)))
                         ($next (+ $fresh 1)))
                    (ErActorSystem $all $network $next (LCons (ErActorSpawn $pid $fresh) $history))))))))))))
)
     ($bad (gslt:er-actor:refuse $pid $mailbox $machine $continuation $system)))))


(: gslt:er-actor:send (-> Number Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:er-actor:send $pid $mailbox $machine $arguments $continuation $system)
  (case $arguments
    (((PApp "ErValuesCons" (LCons $receiver (LCons
        (PApp "ErValuesCons" (LCons $message (LCons (PApp "ErValuesNil" LNil) LNil))) LNil)))
      (case (gslt:er-actor:pid-value $receiver)
        ((None (gslt:er-actor:refuse $pid $mailbox $machine $continuation $system))
         ((Some $target)
          (case $system
            (((ErActorSystem $processes $network $fresh $history)
              (let* (($values (gslt:er:pack2 "ErValuesCons" $message (PApp "ErValuesNil" LNil)))
                     ($resumed (gslt:er-actor:return $machine $values $continuation))
                     ($updated (gslt:er-actor:put $pid (ErLocal $pid $mailbox $resumed) $processes))
                     ($pending (gslt:automata:append $network (LCons (ErEnvelope $pid $target $message) LNil))))
                (ErActorSystem $updated $pending $fresh (LCons (ErActorSend $pid $target $message) $history)))))))))
)
     ($bad (gslt:er-actor:refuse $pid $mailbox $machine $continuation $system)))))


(: gslt:er-actor:return-store (-> Number Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:er-actor:return-store $pid $mailbox $machine $values $continuation $effect $system)
  (let $resumed (gslt:er-actor:return $machine $values $continuation)
    (gslt:er-actor:store $pid $mailbox $resumed $effect $system)))
(: gslt:er-actor:one (-> Atom %Undefined%))
(= (gslt:er-actor:one $value) (gslt:er:pack2 "ErValuesCons" $value (PApp "ErValuesNil" LNil)))
(: gslt:er-actor:two (-> Atom Atom %Undefined%))
(= (gslt:er-actor:two $first $second)
  (let $tail (gslt:er-actor:one $second) (gslt:er:pack2 "ErValuesCons" $first $tail)))

(: gslt:er-actor:mailbox (-> Number Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:er-actor:mailbox $pid $mailbox $machine $operation $arguments $continuation $system)
  (case $arguments
    (((PApp "ErValuesNil" LNil)
      (case $operation
        (("ErPeekMessage" (gslt:er-actor:peek $pid $mailbox $machine $continuation $system))
         ("ErNextMessage" (gslt:er-actor:cursor $pid $mailbox $machine "ErNext" "ErAdvanced" $continuation $system))
         ("ErRemoveMessage" (gslt:er-actor:cursor $pid $mailbox $machine "ErRemove" "ErRemoved" $continuation $system))
         ("ErWaitInfinity" (gslt:er-actor:wait $pid $mailbox $machine $continuation $system)))))
     ($bad (gslt:er-actor:refuse $pid $mailbox $machine $continuation $system)))))
(: gslt:er-actor:peek (-> Number Atom Atom Atom Atom %Undefined%))
(= (gslt:er-actor:peek $pid $mailbox $machine $continuation $system)
  (let* (($source (gslt:er:pack1 "ErPeek" $mailbox)) ($result (gslt:er-rho:mailbox-kernel $source)))
    (gslt:er-actor:mailbox-result $pid ErPeek $mailbox $machine $continuation $result $system)))
(: gslt:er-actor:cursor (-> Number Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:er-actor:cursor $pid $mailbox $machine $operation $expected $continuation $system)
  (let* (($peekSource (gslt:er:pack1 "ErPeek" $mailbox)) ($peek (gslt:er-rho:mailbox-kernel $peekSource)))
    (gslt:er-actor:mailbox-result $pid (ErCursorPeek $operation $expected)
      $mailbox $machine $continuation $peek $system)))
(: gslt:er-actor:wait (-> Number Atom Atom Atom Atom %Undefined%))
(= (gslt:er-actor:wait $pid $mailbox $machine $continuation $system)
  (let* (($source (gslt:er:pack1 "ErWait" $mailbox)) ($result (gslt:er-rho:mailbox-kernel $source)))
    (gslt:er-actor:mailbox-result $pid ErWait $mailbox $machine $continuation $result $system)))

; Cursor operations retain the completed peek account while their second
; kernel run is pending. No effect is committed before its kernel completes.
(: gslt:er-actor:mailbox-result (-> Number Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:er-actor:mailbox-result $pid $action $mailbox $machine $continuation $result $system)
  (case $result
    (((ErRhoKernelPending $account)
      (ErActorMailboxPending $pid $action $mailbox $machine $continuation $result $system))
     ((ErRhoKernelDone $target $account)
      (gslt:er-actor:mailbox-done $pid $action $mailbox $machine $continuation $target $account $system))
     ($bad (ErActorDiagnostic MailboxProgress $bad $system)))))
(: gslt:er-actor:mailbox-done (-> Number Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:er-actor:mailbox-done $pid $action $mailbox $machine $continuation $target $account $system)
  (case $action
    ((ErPeek
      (case $target
        (((PApp "ErPeekValue" (LCons $message (LCons $box LNil)))
          (let* (($true (gslt:er:true)) ($values (gslt:er-actor:two $true $message)))
            (gslt:er-actor:return-store $pid $box $machine $values $continuation
              (ErActorMailbox $pid ErPeek $account) $system)))
         ((PApp "ErPeekEmpty" (LCons $box LNil))
          (let* (($false (gslt:er:false)) ($undefined (gslt:er-actor:undefined))
                 ($values (gslt:er-actor:two $false $undefined)))
            (gslt:er-actor:return-store $pid $box $machine $values $continuation
              (ErActorMailbox $pid ErPeekEmpty $account) $system)))
         ($bad (ErActorDiagnostic MailboxResultShape $target $system)))))
     ((ErCursorPeek $operation $expected)
      (case $target
        (((PApp "ErPeekValue" (LCons $message (LCons $normalized LNil)))
          (let* (($cursorSource (gslt:er:pack1 $operation $normalized))
                 ($cursorResult (gslt:er-rho:mailbox-kernel $cursorSource)))
            (gslt:er-actor:mailbox-result $pid (ErCursorApply $operation $expected $account)
              $normalized $machine $continuation $cursorResult $system)))
         ((PApp "ErPeekEmpty" $fields) (ErActorDiagnostic EmptyMailboxCursor $machine $system))
         ($bad (ErActorDiagnostic MailboxResultShape $target $system)))))
     ((ErCursorApply $operation $expected $peekAccount)
      (case $target
        (((PApp $tag (LCons $box LNil))
          (if (== $tag $expected)
            (let* (($true (gslt:er:true)) ($values (gslt:er-actor:one $true)))
              (gslt:er-actor:return-store $pid $box $machine $values $continuation
                (ErActorMailbox $pid $operation $peekAccount $account) $system))
            (ErActorDiagnostic MailboxResultShape $target $system)))
         ($bad (ErActorDiagnostic MailboxResultShape $target $system)))))
     (ErWait
      (case $target
        (((PApp "ErReady" (LCons $box LNil))
          (let* (($false (gslt:er:false)) ($values (gslt:er-actor:one $false)))
            (gslt:er-actor:return-store $pid $box $machine $values $continuation
              (ErActorMailbox $pid ErReady $account) $system)))
         ((PApp "ErWaiting" (LCons $box LNil))
          (gslt:er-actor:store $pid $box $machine (ErActorMailbox $pid ErWaiting $account) $system))
         ($bad (ErActorDiagnostic MailboxResultShape $target $system)))))
     ($bad (ErActorDiagnostic MailboxAction $action $system)))))

(: gslt:er-actor:has-pair (-> Number Number Atom Bool))
(= (gslt:er-actor:has-pair $sender $receiver $messages)
  (case $messages
    ((LNil False)
     ((LCons (ErEnvelope $from $to $message) $tail)
      (if (== $sender $from)
        (if (== $receiver $to) True (gslt:er-actor:has-pair $sender $receiver $tail))
        (gslt:er-actor:has-pair $sender $receiver $tail))))))
(: gslt:er-actor:take-delivery (-> Number Atom Atom %Undefined%))
(= (gslt:er-actor:take-delivery $index $before $messages)
  (case $messages
    ((LNil None)
     ((LCons (ErEnvelope $sender $receiver $message) $tail)
      (if (== $index 0)
        (if (gslt:er-actor:has-pair $sender $receiver $before) None
          (let $rest (gslt:automata:append $before $tail)
            (Some (ErDelivery $sender $receiver $message $rest))))
        (let* (($next (- $index 1))
               ($prefix (gslt:automata:append $before (LCons (ErEnvelope $sender $receiver $message) LNil))))
          (gslt:er-actor:take-delivery $next $prefix $tail)))))))
(: gslt:er-actor:deliver (-> Number Atom %Undefined%))
(= (gslt:er-actor:deliver $index $system)
  (case $system
    (((ErActorSystem $processes $network $fresh $history)
      (case (gslt:er-actor:take-delivery $index LNil $network)
        ((None $system)
         ((Some (ErDelivery $sender $receiver $message $rest))
          (case (gslt:er-actor:get $receiver $processes)
            ((None (ErActorSystem $processes $rest $fresh (LCons (ErActorDiscard $sender $receiver $message) $history)))
             ((Some (ErLocal $identity $mailbox (ErMachine ErComplete $plan $standard $runner $epochs)))
              (ErActorSystem $processes $rest $fresh (LCons (ErActorDiscard $sender $receiver $message) $history)))
             ((Some (ErLocal $identity $mailbox $machine))
              (let* (($source (gslt:er:pack2 "ErDeliver" $message $mailbox))
                     ($result (gslt:er-rho:mailbox-kernel $source)))
                (gslt:er-actor:delivery-result
                  (ErDelivery $sender $receiver $message $rest) $result $system)))))))))))

)
(: gslt:er-actor:delivery-result (-> Atom Atom Atom %Undefined%))
(= (gslt:er-actor:delivery-result $delivery $result $system)
  (case $result
    (((ErRhoKernelPending $account) (ErActorDeliveryPending $delivery $result $system))
     ((ErRhoKernelDone (PApp "ErDelivered" (LCons $box LNil)) $account)
      (case (ErDeliveryContext $delivery $system)
        (((ErDeliveryContext (ErDelivery $sender $receiver $message $rest)
             (ErActorSystem $processes $network $fresh $history))
          (case (gslt:er-actor:get $receiver $processes)
            (((Some (ErLocal $identity $mailbox $machine))
              (let $updated (gslt:er-actor:put $receiver (ErLocal $identity $box $machine) $processes)
                (ErActorSystem $updated $rest $fresh
                  (LCons (ErActorDelivery $sender $receiver $message $account) $history))))
             ($missing (ErActorDiagnostic DeliveryReceiver $delivery $system)))))
         ($bad (ErActorDiagnostic DeliveryContext $delivery $system)))))
     ($bad (ErActorDiagnostic DeliveryResultShape $result $system)))))

; Resume the saved search and action phase, rather than starting a new search.
; A suspended choice sequence retains its remaining choices in order.
(: gslt:er-actor:continue (-> Number Number Atom %Undefined%))
(= (gslt:er-actor:continue $ticks $quantum $pending)
  (case $pending
    (((ErActorMailboxPending $pid $action $mailbox $machine $continuation $progress $system)
      (let $result (gslt:er-rho:mailbox-resume $ticks $quantum $progress)
        (gslt:er-actor:mailbox-result $pid $action $mailbox $machine $continuation $result $system)))
     ((ErActorDeliveryPending $delivery $progress $system)
      (let $result (gslt:er-rho:mailbox-resume $ticks $quantum $progress)
        (gslt:er-actor:delivery-result $delivery $result $system)))
     ((ErActorChoicesPending $rest $action)
      (let $resumed (gslt:er-actor:continue $ticks $quantum $action)
        (case $resumed
          (((ErActorSystem $processes $network $fresh $history)
            (gslt:er-actor:choices $rest $resumed))
           ($waiting (ErActorChoicesPending $rest $resumed))))))
     ($stopped $stopped))))

; Native rho transfers the complete selected configuration to a local task.
; Choosing an action is explicit; this does not claim scheduler completeness.
(: gslt:er-actor:step (-> Atom Atom %Undefined%))
(= (gslt:er-actor:step $choice $system)
  (let* (($channel (rho:quote (rho:val erlang-system-state)))
         ($process (gslt:er-rho:mailbox-request $channel $choice $system))
         ($next (rhometta:transitions $process)) ($tasks (rhometta:values $next)))
    (case $tasks
      ((((ErRhoMailboxTask $action (rho:quote (rho:val $state))))
        (gslt:er-actor:dispatch $action $state))
       ($bad (ErActorDiagnostic StateTransfer $system))))))
(: gslt:er-actor:dispatch (-> Atom Atom %Undefined%))
(= (gslt:er-actor:dispatch $choice $system)
  (case $choice
    (((ErExecute $pid $ticks $quantum) (gslt:er-actor:execute $pid $ticks $quantum $system))
     ((ErDeliver $index) (gslt:er-actor:deliver $index $system))
     ($bad (ErActorDiagnostic UnknownChoice $system)))))
(: gslt:er-actor:choices (-> Atom Atom %Undefined%))
(= (gslt:er-actor:choices $choices $system)
  (case $choices
    ((LNil $system)
     ((LCons $choice $rest)
      (let $next (gslt:er-actor:step $choice $system)
        (case $next
          (((ErActorSystem $processes $network $fresh $history)
            (gslt:er-actor:choices $rest $next))
           ($pending (ErActorChoicesPending $rest $next)))))))))

(: gslt:er-actor:waiting (-> Atom Atom Bool))
(= (gslt:er-actor:waiting $mailbox $machine) (case $machine (((ErMachine ErComplete $plan $standard $runner $epochs) True) ((ErMachine ErSuspended $plan $standard (ClassMachine $status (PApp "ErActorRequest" (LCons (PApp "ErWaitInfinity" LNil) (LCons (PApp "ErValuesNil" LNil) (LCons $continuation LNil)))) $query $states $receipts) $epochs) (case $mailbox (((PApp "ErMailbox" (LCons $saved (LCons (PApp "ErValuesNil" LNil) (LCons (PApp "ErValuesNil" LNil) LNil)))) True) ($other False)))) ($other False))))
(: gslt:er-actor:all-waiting (-> Atom Bool))
(= (gslt:er-actor:all-waiting $processes)
  (case $processes
    ((LNil True)
     ((LCons (ErLocal $pid $mailbox $machine) $rest)
      (if (gslt:er-actor:waiting $mailbox $machine) (gslt:er-actor:all-waiting $rest) False)))))
(: gslt:er-actor:observe (-> Atom %Undefined%))
(= (gslt:er-actor:observe $system)
  (case $system
    (((ErActorSystem $processes $network $fresh $history)
      (case (gslt:er-actor:get 0 $processes)
        (((Some (ErLocal $pid $mailbox
            (ErMachine ErComplete $plan $standard
              (ClassMachine $status (PApp "ErDone" (LCons $values LNil)) $query $states $receipts) $epochs)))
          (ErActorValue $values))
         ((Some (ErLocal $pid $mailbox
            (ErMachine ErComplete $plan $standard
              (ClassMachine $status (PApp "ErFault" (LCons $fault LNil)) $query $states $receipts) $epochs)))
          (ErActorFaultResult $fault))
         ($other
          (if (== $network LNil)
            (if (gslt:er-actor:all-waiting $processes) ErActorBlocked ErActorPending)
            ErActorPending)))))
     ($pending (ErActorPendingState $pending)))))
