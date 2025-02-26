(declare-rel pu (Int Int))
(declare-rel po (Int Int))
(declare-rel inv1 (Int Int Int Int))
(declare-rel inv2 (Int Int Int Int))

(declare-var n Int)
(declare-var c Int)
(declare-var d Int)
(declare-var sl Int)
(declare-var n1 Int)
(declare-var c1 Int)
(declare-var d1 Int)
(declare-var sl1 Int)

(declare-rel fail ())

(rule (=> (and (= sl 1) (= sl1 0)) (po sl sl1)))
(rule (=> (and (= sl 2) (= sl1 1)) (po sl sl1)))
;; (rule (=> (and (= sl 3) (= sl1 2)) (po sl sl1)))
;; (rule (=> (and (= sl 4) (= sl1 3)) (po sl sl1)))
;; (rule (=> (and (= sl 5) (= sl1 4)) (po sl sl1)))
;; (rule (=> (and (= sl 6) (= sl1 5)) (po sl sl1)))
;; (rule (=> (and (= sl 7) (= sl1 6)) (po sl sl1)))
;; (rule (=> (and (= sl 8) (= sl1 7)) (pu sl sl1)))
;; (rule (=> (and (= sl 9) (= sl1 8)) (pu sl sl1)))5

(rule (=> (and (= sl 0) (= sl1 1)) (pu sl sl1)))
(rule (=> (and (= sl 1) (= sl1 2)) (pu sl sl1)))
(rule (=> (and (= sl 2) (= sl1 3)) (pu sl sl1)))
(rule (=> (and (= sl 3) (= sl1 4)) (pu sl sl1)))
;; (rule (=> (and (= sl 4) (= sl1 5)) (pu sl sl1)))
;; (rule (=> (and (= sl 5) (= sl1 6)) (pu sl sl1)))
;; (rule (=> (and (= sl 6) (= sl1 7)) (pu sl sl1)))
;; (rule (=> (and (= sl 7) (= sl1 8)) (pu sl sl1)))
;; (rule (=> (and (= sl 8) (= sl1 9)) (pu sl sl1)))

;; (rule (=> (and (= sl 4) (= sl1 5)) (pu sl sl1)))
;; (rule (=> (and (= sl 2) (= sl1 3) (po sl sl1)) fail))
;; (rule (=> (and (= sl 3) (= sl1 2) (pu sl sl1)) fail))
;; (rule (=> (and (= sl 0) (= sl1 1) (po sl sl1)) fail))
;; (rule (=> (and (= sl 1) (= sl1 2) (po sl sl1)) fail))
;; (rule (=> (and (= sl 1) (= sl1 0) (pu sl sl1)) fail))
;; (rule (=> (and (= sl 2) (= sl1 1) (pu sl sl1)) fail))
;; (rule (=> (and (= sl 2) (= sl1 4)) (po sl sl1)))
;; (rule (=> (and (= sl 2) (= sl1 2)) (po sl sl1)))
;; (rule (=> (and (= sl 2) (= sl1 2)) (pu sl sl1)))
;; (rule (=> (and (= sl 3) (= sl1 2)) (pu sl sl1)))
;; (rule (=> (and (= sl 4) (= sl1 2)) (pu sl sl1)))
;; (rule (=> (and (= sl 50) (= sl1 51)) (pu sl sl1)))		
;; (rule (=> (and (= sl 100) (= sl1 101)) (pu sl sl1)))
;; (rule (=> (and (= sl 101) (= sl1 102)) (pu sl sl1)))
;; (rule (=> (and (= sl 102) (= sl1 103)) (pu sl sl1)))
;; (rule (=> (and (= sl 104) (= sl1 105)) (pu sl sl1)))
;; (rule (=> (and (= sl 105) (= sl1 106)) (pu sl sl1)))
;; (rule (=> (and (= sl 101) (= sl1 100)) (po sl sl1)))
;; (rule (=> (and (= sl 100) (= sl1 99)) (po sl sl1)))
;; (rule (=> (and (= sl 99) (= sl1 98)) (po sl sl1)))
;; (rule (=> (and (= sl 98) (= sl1 97)) (po sl sl1)))
;; (rule (=> (and (= sl 97) (= sl1 96)) (po sl sl1)))
;; (rule (=> (and (>= sl 0)(= sl 97) (= sl1 96)) (po sl sl1)))

(rule (=> (and (> n 0) (= sl 0) (= c 0) (= d 0)) (inv1 c n d sl)))

(rule (=> (and (inv1 c n d sl) (< c n) (= c1 (+ c 1)) (pu sl sl1))
(inv1 c1 n d sl1)))

(rule (=> (and (inv1 c n d sl) (not (< c n))) (inv2 c n d sl)))

(rule (=> (and (inv2 c n d sl) (not (= sl 0)) (= d1 (+ d 1)) (po sl sl1)) (inv2 c n d1 sl1)))

(rule (=> (and (inv2 c n d sl) (= sl 0) (not (= d n))) fail))

(query fail :print-certificate true)
