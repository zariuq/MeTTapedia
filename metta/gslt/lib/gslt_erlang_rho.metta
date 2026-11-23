; Native rho transfers an explicit mailbox token into a local task.
; Complete the task with the existing emitted GSLT mailbox kernel in PeTTa.
; The complete kernel account remains in results, including incomplete work.
; Load after a generated gslt:er-rho:mailbox-kernel definition.

!(import! &self rhometta)

(: gslt:er-rho:perform (-> Atom Atom %Undefined%))
(= (gslt:er-rho:perform $operation $token)
  (case $token
    (((rho:quote (rho:val $mailbox))
      (let* (($source (PApp $operation (LCons $mailbox LNil)))
             ($result (gslt:er-rho:mailbox-kernel $source)))
        (rho:val (ErRhoMailboxResult $operation $result))))
     ($bad (rho:val (ErRhoMailboxRefusal $bad))))))

(: gslt:er-rho:mailbox-request (-> Atom Atom Atom %Undefined%))
(= (gslt:er-rho:mailbox-request $stateChannel $operation $mailbox)
  (rho:par
    (rho:send $stateChannel (rho:val $mailbox))
    (rho:recv $stateChannel $token
      (rho:val (ErRhoMailboxTask $operation $token)))))

(: gslt:er-rho:complete-task (-> Atom %Undefined%))
(= (gslt:er-rho:complete-task $task)
  (case $task
    (((ErRhoMailboxTask $operation $token)
      (gslt:er-rho:perform $operation $token))
     ($bad (rho:val (ErRhoMailboxRefusal $bad))))))
