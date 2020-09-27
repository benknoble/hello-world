(ns binary)

(defn bits [n]
  (->> n
       vec
       (map int)
       (map (partial + -48))
       (filter #{0 1})))

(defn powers2 [n]
  (->> n
       bits
       reverse
       (map-indexed (fn [i e] (if (zero? e) e i)))
       reverse))

; bug: incorrectly handles 0th bit set = 2^0 = 1
(defn pow2 [n]
  (->> n
       powers2
       (map (fn [e] (if-not (zero? e) (Math/pow 2 e) e)))
       (map int)))


(def sum (partial reduce +))

(defn un->ten [n]
  (->> n pow2 sum))

(defn tc->ten [n]
  (->> n
       pow2
       (map-indexed (fn [i e] (if (zero? i) (- e) e)))
       sum))

(->> [(assert (= -2 (tc->ten "1110")))
      (assert (= -10 (tc->ten "110110")))
      (assert (= 112 (tc->ten "01110000")))
      (assert (= -98 (tc->ten "10011111")))
      (assert (= -29 (tc->ten "100011")))]
     (every? nil?))
