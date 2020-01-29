(ns hello.cruel-world)

(defn what-kind?
  []
  "Beautiful")

; (.log js/console (what-kind?))
(def app
  (.getElementById js/document "app"))

(set! (.-innerHTML app) (what-kind?))
