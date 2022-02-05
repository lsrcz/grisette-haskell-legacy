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

instance SymGen SymBool MovingExprSpec MovingOpExpr where
  genSymIndexed _ = ...

instance SymGen SymBool MovingExprSpec MovingExpr where
  genSymIndexed _ = ...




instance SymGen SymBool (MovingExprSpec, MovingExpr) MovingOpExpr where
  genSymIndexed _ = ...

instance SymGen SymBool (MovingExprSpec, MovingExpr) MovingExpr where
  genSymIndexed _ = ...


instance SymGen SymBool () (CoordExpr -> SymInteger) where
  genSymIndexed v = genSymSimpleIndexed @SymBool v

instance SymGenSimple SymBool () (CoordExpr -> SymInteger) where
  genSymSimpleIndexed _ = do
    v <- genSymSimpleIndexed @SymBool ()
    return $ const v


instance SymGen SymBool MovingExprSpec (CoordExpr -> UnionM MovingOpExpr) where
  genSymIndexed spec = genSymSimpleIndexed @SymBool v

instance SymGenSimple SymBool MovingExprSpec (CoordExpr -> UnionM MovingOpExpr) where
  genSymSimpleIndexed spec = ...

instance SymGen SymBool MovingExprSpec (CoordExpr -> UnionM MovingExpr) where
  genSymIndexed spec = genSymSimpleIndexed @SymBool v

instance SymGenSimple SymBool MovingExprSpec (CoordExpr -> UnionM MovingExpr) where
  genSymSimpleIndexed spec = ...


genSymIndexed, genSymSimpleIndexed, genSym