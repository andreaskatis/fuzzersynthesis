(declare-fun $desiredSpeed$2 () Real)
(declare-fun $carSpeed$0 () Real)
(declare-fun $desiredSpeed$~1 () Real)
(declare-fun $OK$2 () Bool)

(assert (let ((a!1 (= 0.0 (ite true (to_real (div 0 10)) $desiredSpeed$~1))))
(let ((a!2 (or a!1 (= 0.0 $carSpeed$0) (= 0.0 (to_real (div 0 10))))))
  (and (= $OK$2 a!2) (= $desiredSpeed$2 0.0)))))
(check-sat)
