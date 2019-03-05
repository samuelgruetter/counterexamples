(define-fun mysubset ((s1 set) (s2 set)) bool
  (forall ((k K)) (=> (= (select s1 k) true)
                      (= (select s2 k) true))))

(declare-const s1 set)
(declare-const s2 set)
(assert (not
         (iff (mysubset s1 s2) (subset s1 s2))))
