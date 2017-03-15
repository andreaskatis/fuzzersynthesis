; K = 0
; Transition relation
(define-fun T ((%init Bool) ($desiredSpeed$0 Real) ($OK$0 Bool) ($desiredSpeed$1 Real) ($OK$1 Bool)) Bool (= $OK$1 (and (>= $desiredSpeed$1 (/ 0 10)) (<= $desiredSpeed$1 (/ 1000 10)))))
; Universally quantified variables
(declare-fun %init () Bool)
(declare-fun $desiredSpeed$~1 () Real)
(declare-fun $OK$~1 () Bool)
(declare-fun $desiredSpeed$0 () Real)
(declare-fun $OK$0 () Bool)
(assert (T %init $desiredSpeed$~1 $OK$~1 $desiredSpeed$0 $OK$0))
