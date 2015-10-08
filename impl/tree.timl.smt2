(define-fun max ((x Int) (y Int)) Int
  (ite (< x y) y x))
(define-fun mymin ((x Int) (y Int)) Int
  (ite (> x y) y x))
(declare-datatypes () ((Unit TT)))

(push)
(declare-const n2 Int)
(assert (<= 0 n2))
(declare-const n1 Int)
(assert (<= 0 n1))
(declare-const n Int)
(assert (<= 0 n))
(declare-const m Int)
(assert (<= 0 m))
(assert (= (+ (+ n1 1) n2) n))
(assert (not (<= (+ (+ (+ 1 m) (+ 1 (* (+ m 3) n1))) (+ 1 (* (+ m 3) n2))) (* (+ m 3) n))))
(check-sat)
(pop)
