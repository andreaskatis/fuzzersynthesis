; K = 2
; Transition relation
(define-fun T ((%init Bool) ($mode$0 Int) ($cruiseThrottle$0 Real) ($OK$0 Bool) ($mode$1 Int) ($cruiseThrottle$1 Real) ($OK$1 Bool)) Bool (= $OK$1 (or (not (= $mode$1 4)) (= $cruiseThrottle$1 (ite %init (/ 0 10) $cruiseThrottle$0)))))
; Universally quantified variables
(declare-fun $mode$~1 () Int)
(declare-fun $cruiseThrottle$~1 () Real)
(declare-fun $OK$~1 () Bool)
(declare-fun $mode$0 () Int)
(declare-fun $cruiseThrottle$0 () Real)
(declare-fun $OK$0 () Bool)
(declare-fun $mode$3 () Int)
(declare-fun $cruiseThrottle$3 () Real)
(declare-fun $OK$3 () Bool)
(assert (and (T false $mode$0 $cruiseThrottle$0 $OK$0 $mode$3 $cruiseThrottle$3 $OK$3) $OK$3))
