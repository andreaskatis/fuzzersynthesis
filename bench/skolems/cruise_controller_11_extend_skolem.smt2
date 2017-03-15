(declare-fun $cruiseThrottle$2 () Real)
(declare-fun $mode$2 () Int)
(declare-fun $OK$2 () Bool)

(assert (and (= $OK$2 true) (= $mode$2 4) (= $cruiseThrottle$2 0.0)))
(check-sat)
