; K = 1
; Transition relation
(define-fun T ((%init Bool) ($carSpeed$0 Real) ($desiredSpeed$0 Real) ($OK$0 Bool) ($carSpeed$1 Real) ($desiredSpeed$1 Real) ($OK$1 Bool)) Bool (= $OK$1 (or (or (= $desiredSpeed$1 (ite %init (/ 0 10) $desiredSpeed$0)) (= $desiredSpeed$1 $carSpeed$1)) (= $desiredSpeed$1 (/ 0 10)))))
; Universally quantified variables
(declare-fun $carSpeed$~1 () Real)
(declare-fun $desiredSpeed$~1 () Real)
(declare-fun $OK$~1 () Bool)
(declare-fun $carSpeed$0 () Real)
(declare-fun $desiredSpeed$0 () Real)
(declare-fun $OK$0 () Bool)
(assert (T true $carSpeed$~1 $desiredSpeed$~1 $OK$~1 $carSpeed$0 $desiredSpeed$0 $OK$0))
