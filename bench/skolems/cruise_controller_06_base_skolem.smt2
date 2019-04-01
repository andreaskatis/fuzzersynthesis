(declare-fun $cruiseThrottle$2 () Real)
(declare-fun $OK$2 () Bool)

(assert (and (= $OK$2 true) (= $cruiseThrottle$2 0.0)))
(check-sat)
