; K = 1
; Transition relation
(define-fun T ((%init Bool) ($mode$0 Int) ($cruiseThrottle$0 Real) ($OK$0 Bool) ($mode$1 Int) ($cruiseThrottle$1 Real) ($OK$1 Bool)) Bool (= $OK$1 (or (or (or (= $mode$1 4) (= $mode$1 5)) (= $mode$1 6)) (= $cruiseThrottle$1 (/ 0 10)))))
; Universally quantified variables
(declare-fun $mode$~1 () Int)
(declare-fun $cruiseThrottle$~1 () Real)
(declare-fun $OK$~1 () Bool)
(declare-fun $mode$2 () Int)
(declare-fun $cruiseThrottle$2 () Real)
(declare-fun $OK$2 () Bool)
(assert (and (T true $mode$~1 $cruiseThrottle$~1 $OK$~1 $mode$2 $cruiseThrottle$2 $OK$2) $OK$2))
