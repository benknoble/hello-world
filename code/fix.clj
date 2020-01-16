(ns fix
  (:require [clojure.test :as t]))

(defn U
  "the U combinator; requires f to co-operate"
  [f]
  (f f))

(defn Y
  "pure lazy Y combinator => stack overflow"
  [f]
  (let [A (fn [x] (f (x x)))]
   (A A)))

(defn X
  "β-reduces into Y => stack overflow"
  [f]
  ((fn [x] (x x))
   (fn [x] (f (x x)))))

(defn Z
  "strict fixed-point combinator"
  [f]
  (let [A (fn [x] (f (fn [v] ((x x) v))))]
   (A A)))

(def theta
  "Turing fixed-point combinator"
  (let [A (fn [x] (fn [y] (y ((x x) y))))]
    (A A)))

(def theta-v
  "Turing fixed-point combinator by-value"
  (let [A (fn [x] (fn [y] (y (fn [z] (((x x) y) z)))))]
    (A A)))

(def fib'
  "un-fixed fibonacci sequence"
  (fn [f]
    (fn [n]
      (case n
        0 0
        1 1
        (+ (f (dec n))
           (f (dec (dec n))))))))

(def !'
  "un-fixed factorial function"
  (fn [f]
    (fn [n]
      (if (zero? n)
        1
        (* n (f (dec n)))))))

(defn fib
  "fibonacci"
  [n]
  (case n
    0 0
    1 1
    (+ (fib (dec n))
       (fib (dec (dec n))))))

(defn !
  "factorial"
  [n]
  (if (zero? n)
    1
    (apply * (map inc (range n)))))

(t/deftest test-Z
  (t/are [x y] (= x y)
         (fib 6) ((Z fib') 6)
         (! 5) ((Z !') 5)))

(t/deftest test-theta-v
  (t/are [x y] (= x y)
         (fib 6) ((theta-v fib') 6)
         (! 5) ((theta-v !') 5)))

(defn run-tests [] (t/run-tests 'fix))
