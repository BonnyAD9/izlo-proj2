(set-logic NIA)

(set-option :produce-models true)
(set-option :incremental true)

; Deklarace promennych pro vstupy
; ===============================

; Ceny
(declare-fun c1 () Int)
(declare-fun c2 () Int)
(declare-fun c3 () Int)
(declare-fun c4 () Int)
(declare-fun c5 () Int)

; Kaloricke hodnoty
(declare-fun k1 () Int)
(declare-fun k2 () Int)
(declare-fun k3 () Int)
(declare-fun k4 () Int)
(declare-fun k5 () Int)

; Maximalni pocty porci
(declare-fun m1 () Int)
(declare-fun m2 () Int)
(declare-fun m3 () Int)
(declare-fun m4 () Int)
(declare-fun m5 () Int)

; Maximalni cena obedu
(declare-fun max_cena () Int)

; Deklarace promennych pro reseni
(declare-fun n1 () Int)
(declare-fun n2 () Int)
(declare-fun n3 () Int)
(declare-fun n4 () Int)
(declare-fun n5 () Int)
(declare-fun best () Int)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;; START OF SOLUTION ;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; counts must be positive
(assert (>= n1 0))
(assert (>= n2 0))
(assert (>= n3 0))
(assert (>= n4 0))
(assert (>= n5 0))

; counts must be less or equal to the available
(assert (<= n1 m1))
(assert (<= n2 m2))
(assert (<= n3 m3))
(assert (<= n4 m4))
(assert (<= n5 m5))

(assert
  ; the price is less then or equal to the maximum
  (<= (+ (* n1 c1) (* n2 c2) (* n3 c3) (* n4 c4) (* n5 c5)) max_cena)
)

(assert
  ; set the best calories
  (= best (+ (* n1 k1) (* n2 k2) (* n3 k3) (* n4 k4) (* n5 k5)))
)

(assert
  ; the calories ar the max possible
  (forall ((a Int) (b Int) (c Int) (d Int) (e Int))
    ; for all other solutions is true that:
    (or
      ; the count is negative
      (< a 0) (< b 0) (< c 0) (< d 0) (< e 0)
      ; or the price is too high
      (> (+ (* a c1) (* b c2) (* c c3) (* d c4) (* e c5)) max_cena)
      ; or you cannot buy as much
      (> a m1) (> b m2) (> c m3) (> d m4) (> e m4)
      ; or the calories are same or worse than the searched solution
      (<= (+ (* a  k1) (* b  k2) (* c  k3) (* d  k4) (* e  k5)) best)
    )
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;; END OF SOLUTION ;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Testovaci vstupy
; ================

(echo "Test 1.a - ocekavany vystup je sat, promenna best ma hodnotu 34")
(check-sat-assuming (
  (= c1 7) (= c2 3) (= c3 6) (= c4 10) (= c5 8)
  (= k1 5) (= k2 2) (= k3 4) (= k4 7)  (= k5 3)
  (= m1 3) (= m2 2) (= m3 4) (= m4 1)  (= m5 3)
  (= max_cena 50)
))
(get-value (best n1 n2 n3 n4 n5))

(echo "Test 1.b - neexistuje jine reseni nez 34, ocekavany vystup je unsat")
(check-sat-assuming (
  (= c1 7) (= c2 3) (= c3 6) (= c4 10) (= c5 8)
  (= k1 5) (= k2 2) (= k3 4) (= k4 7)  (= k5 3)
  (= m1 3) (= m2 2) (= m3 4) (= m4 1)  (= m5 3)
  (= max_cena 50)
  (not (= best 34))
))

; =========================================================


(echo "Test 2.a - ocekavany vystup je sat, promenna best ma hodnotu 0")
(check-sat-assuming (
  (= c1 7) (= c2 3) (= c3 6) (= c4 10) (= c5 8)
  (= k1 5) (= k2 2) (= k3 4) (= k4 7)  (= k5 3)
  (= m1 3) (= m2 2) (= m3 4) (= m4 1)  (= m5 3)
  (= max_cena 0)
))
(get-value (best n1 n2 n3 n4 n5))

(echo "Test 2.b - neexistuje jine reseni nez 0, ocekavany vystup je unsat")
(check-sat-assuming (
  (= c1 7) (= c2 3) (= c3 6) (= c4 10) (= c5 8)
  (= k1 5) (= k2 2) (= k3 4) (= k4 7)  (= k5 3)
  (= m1 3) (= m2 2) (= m3 4) (= m4 1)  (= m5 3)
  (= max_cena 0)
  (not (= best 0))
))
