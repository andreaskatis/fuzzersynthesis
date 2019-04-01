; K = 1
; Transition relation
(define-fun T ((%init Bool) ($cruiseThrottle$0 Real) ($OK$0 Bool) ($cruiseThrottle$1 Real) ($OK$1 Bool)) Bool (= $OK$1 (and (>= $cruiseThrottle$1 (/ 0 10)) (<= $cruiseThrottle$1 (/ 1000 10)))))
; Universally quantified variables
(declare-fun $cruiseThrottle$~1 () Real)
(declare-fun $OK$~1 () Bool)
(declare-fun $cruiseThrottle$2 () Real)
(declare-fun $OK$2 () Bool)
(assert (and (T true $cruiseThrottle$~1 $OK$~1 $cruiseThrottle$2 $OK$2) $OK$2))
