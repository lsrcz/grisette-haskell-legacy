{-

; DEFINITIONS
(define (moveLeft coord)
  (match coord
    [(list x y) (list (- x 1) y)]))

(define (moveRight coord)
  (match coord
    [(list x y) (list (+ x 1) y)]))

(define (moveUp coord)
  (match coord
    [(list x y) (list x (- y 1))]))

(define (moveDown coord)
  (match coord
    [(list x y) (list x (+ y 1))]))

; GRAMMAR
(define-grammar (moving coord)
  [expr
   (choose coord
           (moveUp (expr))
           (moveLeft (expr))
           (moveDown (expr))
           (moveRight (expr)))])

gramar: moveUp e, moveLeft e, moveRight e, moveLeft e



exmaple

  var x = CoordLit a b
  return x

-}