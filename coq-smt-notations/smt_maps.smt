(declare-datatypes (T) ((option None (Some (option-value T)))))
(define-sort map (K V) (Array K (option V)))

(declare-sort V)
(declare-sort K)

(define-const empty_map (map K V)
  ((as const (Array K (option V))) None))

(define-fun get ((m (map K V)) (k K)) (option V)
  (select m k))

(define-fun put ((m (map K V)) (k K) (v V)) (map K V)
  (store m k (Some v)))

(declare-fun update_map ((map K V) (map K V)) (map K V))

(assert (forall ((m1 (map K V)) (m2 (map K V)) (k K))
    (=> (= (get m2 k) None)
	(= (get (update_map m1 m2) k) (get m1 k)))))
(assert (forall ((m1 (map K V)) (m2 (map K V)) (k K) (v V))
    (=> (= (get m2 k) (Some v))
	(= (get (update_map m1 m2) k) (Some v)))))

(check-sat)

;; (get-model)
