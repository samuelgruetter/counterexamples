; Each partial map m is encoded as an array m and a set m_p telling which
; keys are present in the map

(declare-sort K)
(declare-sort V)

(define-sort map () (Array K V))
(define-sort set () (Array K bool))

(define-fun extends ((s1 map) (s1_p set)
		     (s2 map) (s2_p set))
  bool
  (forall ((k K)) (=> (= (select s2_p k) true)
		      (and (= (select s1_p k) true)
			   (= (select s1 k) (select s2 k))))))

(define-fun undef_on ((m map) (m_p set) (s set)) bool
  (forall ((k K)) (=> (= (select s k) true)
		      (= (select m_p k) false))))


(define-fun maps_to ((k K) (v V) (m map) (m_p set)) bool
  (and (= (select m k) v)
       (= (select m_p k) true)))

(define-fun only_differ ((m1 map) (m1_p set) (ks set) (m2 map) (m2_p map)) bool
  (forall ((k K)) (or (select ks k)
		      (and (= (select m1 k) (select m2 k))
			   (= (select m1_p k) (select m2_p k))))))
