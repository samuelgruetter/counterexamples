function update_map<K(!new), V>(m1: map<K, V>, m2: map<K, V>): map<K, V>
ensures
  (forall k :: k in m1 || k in m2 ==> k in update_map(m1, m2)) &&
  (forall k :: k in m2 ==> update_map(m1, m2)[k] == m2[k]) &&
  (forall k :: !(k in m2) && k in m1 ==> update_map(m1, m2)[k] == m1[k]) &&
  (forall k :: !(k in m2) && !(k in m1) ==> !(k in update_map(m1, m2)))
{
  map k | k in (m1.Keys + m2.Keys) :: if k in m2 then m2[k] else m1[k]
}

predicate map_extends<K, V>(m1: map<K, V>, m2: map<K, V>) {
  forall k :: k in m2 ==> k in m1 && m1[k] == m2[k]
}

lemma update_map_extends<K, V>
  (m1: map<K, V>, m2: map<K, V>, m3: map<K, V>, m4: map<K, V>)
 requires map_extends(m1, m3)
 requires map_extends(m2, m4)
 requires m1.Keys !! m2.Keys
 ensures map_extends(update_map(m1, m2), update_map(m3, m4))
{}

lemma wrong_update_map_extends<K, V>
  (m1: map<K, V>, m2: map<K, V>, m3: map<K, V>, m4: map<K, V>)
 requires map_extends(m1, m3)
 requires map_extends(m2, m4)
 ensures map_extends(update_map(m1, m2), update_map(m3, m4))
{}
