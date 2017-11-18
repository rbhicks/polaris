(deftemplate node
  (slot      identity)
  (multislot source-nodes)
  (multislot destination-nodes))

(deftemplate initial-node
  (slot      identity))

(deftemplate terminal-node
  (slot      identity))

(deftemplate traversal
  (slot      next-node)
  (multislot visited-nodes))

(deftemplate looped-traversal
  (multislot path))

(deftemplate loop
  (slot      identity)
  (multislot nodes))

(deftemplate loop-instruction
  (slot loop-identity)
  (slot index)
  (slot calculated (default FALSE))
  (slot mnemonic)
  (slot operand0)
  (slot operand1))

(deftemplate loop-metadata
  (slot loop-identity)
  (slot instruction-count)
  (slot instructions-calculated (default 0))
  (slot first-node)
  (slot last-node)
  (slot encryption/packing-potential))

(deftemplate potential-encryption/packing-loop
  (slot first-node)
  (slot last-node))

(defrule find-initial-node
  (node
   (identity     ?identity)
   (source-nodes $?source-nodes))
  (test (= (length$ $?source-nodes) 0))
  =>
  (assert (initial-node
           (identity ?identity))))

(defrule find-terminal-node
  (node
   (identity          ?identity)
   (destination-nodes $?destination-nodes))
  (test (= (length$ $?destination-nodes) 0))
  =>
  (assert (terminal-node
           (identity ?identity))))

(defrule visit-initial-node
  (initial-node
   (identity     ?initial-node-identity))
  (node
   (source-nodes $?source-nodes)
   (identity     ?target-node-identity))
  (test (member$ ?initial-node-identity
                 $?source-nodes))
  =>
  (assert (traversal
           (next-node ?target-node-identity)
           (visited-nodes (create$ ?initial-node-identity)))))

(defrule visit-node
 ?traversal <- (traversal
                (next-node           ?next-node)
                (visited-nodes       $?visited-nodes))
               (node
                (identity            ?next-node)
                (destination-nodes   $?destination-nodes))
               (not
                (test
                 (member$ ?next-node $?visited-nodes)))
               (not
                (exists
                 (terminal-node
                  (identity ?next-node))))
 =>
 (progn$ (?destination-node $?destination-nodes)
          (bind ?traversal-identity (gensym))
          (duplicate ?traversal
                      (next-node         ?destination-node)
                      (visited-nodes     (insert$
                                          $?visited-nodes
                                          (+ 1 (length$ $?visited-nodes))
                                          ?next-node))))
 (retract ?traversal))

(defrule visit-terminal-node
 ?traversal <- (traversal
                (next-node     ?next-node)
                (visited-nodes $?visited-nodes))
               (terminal-node
                (identity      ?next-node))
 =>
 (modify ?traversal
  (next-node     nil)
  (visited-nodes (insert$
                  $?visited-nodes
                  (+ 1 (length$ $?visited-nodes))
                  ?next-node))))

(defrule revisit-node
 ?traversal <- (traversal
                (next-node          ?next-node)
                (visited-nodes      $?visited-nodes))
               (node
                (identity           ?next-node))
               (test
                (member$ ?next-node $?visited-nodes))
               (not
                (exists
                 (terminal-node
                  (identity ?next-node))))
 =>
 (assert
  (looped-traversal
   (path (create$ $?visited-nodes ?next-node))))
 (retract ?traversal))

(defrule find-loop
 (looped-traversal
  (path $?path))
 =>
 (bind ?subsequent-loop-node-value (nth$ (length$ $?path) $?path))
 (bind ?initial-loop-node-occurence (member$ ?subsequent-loop-node-value $?path))
 (bind $?looped-nodes (subseq$ $?path ?initial-loop-node-occurence (length$ $?path)))
 (bind ?node-count (- (length$ $?looped-nodes) 1))
 (bind ?last-looped-node-value (nth$ ?node-count $?looped-nodes))
 (bind ?loop-identity (gensym))
 (assert
  (loop
   (identity ?loop-identity)

   (nodes $?looped-nodes)))
 (assert
  (loop-metadata
   (loop-identity ?loop-identity)
   (instruction-count ?node-count)
   (first-node ?subsequent-loop-node-value)
   (last-node ?last-looped-node-value)
   (encryption/packing-potential 0))))


(defrule process-loop
  (loop
   (identity   ?identity)
   (nodes      $?looped-nodes))
  =>
  (python-call process_loop_instructions ?identity $?looped-nodes))


(defrule find-arithmetic-mnemonics
 ?loop-instruction <- (loop-instruction
                       (loop-identity                ?loop-identity)
                       (mnemonic                     ?mnemonic&"rol"|"add"|"or"|"shl"|"xor"|"sub"|"adc"|"shr")
                       (calculated                   FALSE))
 ?loop-metadata    <- (loop-metadata
                       (loop-identity                ?loop-identity)
                       (instructions-calculated      ?instructions-calculated)
                       (encryption/packing-potential ?encryption/packing-potential))
 =>
 (modify ?loop-instruction (calculated TRUE))
 (modify ?loop-metadata
  (instructions-calculated (+ ?instructions-calculated 1))
  (encryption/packing-potential (+ ?encryption/packing-potential 1))))


(defrule find-data-manipulation-mnemonics
 ?loop-instruction <- (loop-instruction
                       (loop-identity                ?loop-identity)
                       (mnemonic                     ?mnemonic&"xchg"|"repne scasb"|"mov"|"lea")
                       (calculated                   FALSE))
 ?loop-metadata    <- (loop-metadata
                       (loop-identity                ?loop-identity)
                       (instructions-calculated      ?instructions-calculated)                       
                       (encryption/packing-potential ?encryption/packing-potential))
 =>
 (modify ?loop-instruction (calculated TRUE))
 (modify ?loop-metadata
  (instructions-calculated (+ ?instructions-calculated 1))
  (encryption/packing-potential (+ ?encryption/packing-potential 0))))


(defrule find-data-index-mnemonics
 ?loop-instruction <- (loop-instruction
                       (loop-identity                ?loop-identity)
                       (mnemonic                     ?mnemonic&"dec"|"inc")
                       (calculated                   FALSE))
 ?loop-metadata    <- (loop-metadata
                       (loop-identity                ?loop-identity)
                       (instructions-calculated      ?instructions-calculated)
                       (encryption/packing-potential ?encryption/packing-potential))
 =>
 (modify ?loop-instruction (calculated TRUE))
 (modify ?loop-metadata
  (instructions-calculated (+ ?instructions-calculated 1))
  (encryption/packing-potential (+ ?encryption/packing-potential 0.5))))


;; 'push' included here due to it's usual use in conjuction with 'call'
;; it is noted that this arrangement could be too simplistic for advanced
;; obfuscation or binaries that were not compiled from c or c++
(defrule find-data-function-call-mnemonics
 ?loop-instruction <- (loop-instruction
                       (loop-identity                ?loop-identity)
                       (mnemonic                     ?mnemonic&"loop"|"call"|"push"|"jmp")
                       (calculated                   FALSE))
 ?loop-metadata    <- (loop-metadata
                       (loop-identity                ?loop-identity)
                       (instructions-calculated      ?instructions-calculated)
                       (encryption/packing-potential ?encryption/packing-potential))
 =>
 (modify ?loop-instruction (calculated TRUE))
 (modify ?loop-metadata
  (instructions-calculated (+ ?instructions-calculated 1))
  (encryption/packing-potential (- ?encryption/packing-potential 3))))


(defrule find-data-unconditional-branch-mnemonics
 ?loop-instruction <- (loop-instruction
                       (loop-identity                ?loop-identity)
                       (mnemonic                     ?mnemonic&"jmp")
                       (calculated                   FALSE))
 ?loop-metadata    <- (loop-metadata
                       (loop-identity                ?loop-identity)
                       (instructions-calculated      ?instructions-calculated)
                       (encryption/packing-potential ?encryption/packing-potential))
 =>
 (modify ?loop-instruction (calculated TRUE))
 (modify ?loop-metadata
  (instructions-calculated (+ ?instructions-calculated 1))
  (encryption/packing-potential (+ ?encryption/packing-potential 1))))


;; 'cmp' is included here for it's common use in conjuction with the branching instructions
(defrule find-data-conditional-branch-mnemonics
 ?loop-instruction <- (loop-instruction
                       (loop-identity                ?loop-identity)
                       (mnemonic                     ?mnemonic&"cmp"|"loop"|"jbe"|"jnz"|"jnb"|"ja"|"jb"|"jz")
                       (calculated                   FALSE))
 ?loop-metadata    <- (loop-metadata
                       (loop-identity                ?loop-identity)
                       (instructions-calculated      ?instructions-calculated)
                       (encryption/packing-potential ?encryption/packing-potential))
 =>
 (modify ?loop-instruction (calculated TRUE))
 (modify ?loop-metadata
  (instructions-calculated (+ ?instructions-calculated 1))
  (encryption/packing-potential (+ ?encryption/packing-potential 1))))

(defrule identify-potential-encryption/packing-loop
  (loop-metadata
   (loop-identity                ?loop-identity)
   (instructions-calculated      ?instructions-calculated)
   (instruction-count            ?instruction-count&?instructions-calculated)
   (first-node                   ?first-node)
   (last-node                    ?last-node)
   (encryption/packing-potential ?encryption/packing-potential))
  (test
   (> 0.90
      (/ ?encryption/packing-potential ?instruction-count)))
  (not
   (exists
    (potential-encryption/packing-loop
     (first-node ?first-node)
     (last-node  ?last-node))))
  =>
  (assert
   (potential-encryption/packing-loop
    (first-node ?first-node)
    (last-node  ?last-node))))

(defrule output-potential-encryption/packing-loop
  (nope)
  (potential-encryption/packing-loop
    (first-node ?first-node)
    (last-node  ?last-node))
  =>
  (python-call print_line "potential encryption/packing loop")
  (python-call print_hex ?first-node)
  (python-call print_hex ?last-node)
  (python-call print_line "================================================================"))











