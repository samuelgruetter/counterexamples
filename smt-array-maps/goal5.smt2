; Coq lemma:
;  forall (initialH initialL : t X) (fvngs : t X) (av vv : X) (v v0 : key)
;	   (prefinalL finalL : t X) (fvn fvngs' mvs mvs0 : t X),
;    extends initialL initialH ->
;    undef_on initialH fvngs ->
;    Disjoint (empty X) fvngs ->
;    get prefinalL v = Some av ->
;    get finalL v0 = Some vv ->
;    subset fvngs' fvn ->
;    subset fvn fvngs ->
;    only_differ initialL mvs prefinalL ->
;    only_differ prefinalL mvs0 finalL ->
;    v0 \in mvs0 ->
;    v \in mvs ->
;    subset mvs0 (diff fvn fvngs') -> subset mvs (diff fvngs fvn) -> get finalL v = Some av.


(declare-const initialH map)
(declare-const initialH_p set)
(declare-const initialL map)
(declare-const initialL_p set)
(declare-const fvngs set)
(declare-const prefinalL map)
(declare-const prefinalL_p set)
(declare-const finalL map)
(declare-const finalL_p set)
(declare-const fvn set)
(declare-const fvngsprime set)
(declare-const mvs set)
(declare-const mvs0 set)

(declare-const v K)
(declare-const v0 K)

(declare-const av V)
(declare-const vv V)

(assert (extends initialL initialL_p initialH initialH_p))
(assert (undef_on initialH initialH_p fvngs))
(assert (maps_to v av prefinalL prefinalL_p))
(assert (maps_to v0 vv finalL finalL_p))
(assert (subset fvngsprime fvn))
(assert (subset fvn fvngs))
(assert (only_differ initialL initialL_p mvs prefinalL prefinalL_p))
(assert (only_differ prefinalL prefinalL_p mvs0 finalL finalL_p))
(assert (select mvs0 v0))
(assert (select mvs v))
(assert (subset mvs0 (difference fvn fvngsprime)))
(assert (subset mvs (difference fvngs fvn)))

(assert (not (maps_to v av finalL finalL_p)))
