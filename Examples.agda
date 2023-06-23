module Examples where

open import CLC

-----------
-- Examples
-----------

pattern Bool = Unit + Unit

-- a sample context
Gamma = [] `, Bool {- 2 -} `, String {- 1 -} `, String {- 0 -}

pattern x0 = zero
pattern x1 = succ x0
pattern x2 = succ x1
pattern x3 = succ x2
pattern x4 = succ x3

-- (λ. print x2) (print x0)
ex0 : Tm Gamma Unit
ex0 = app (lam (app print (var x2))) (app print (var x0))

-- λ. λ. λ. case x2 of { _ -> x1 ; _ -> x2 }
ifte : Tm Gamma (Bool ⇒ (a ⇒ (a ⇒ a)))
ifte = lam (lam (lam (case (var x2) (var x1) (var x2))))

-- let t in u
_︔_ : Tm Gamma a → Tm Gamma b → Tm Gamma b
t ︔ u = let-in t (wkTm freshWk u)

-- To understand the problem of "redundant case analysis", consider
-- the examples below:

-- (λ v1 v2. case x2 v1 v2) (print x0) (print x1)
red-case : Tm Gamma Unit
red-case = app (app (app ifte (var x2)) (app print (var x0))) (app print (var x1))

-- print x0 ; print x1
red-case' : Tm Gamma Unit
red-case' = app print (var x0) ︔ app print (var x1)

-- We would like for these examples to be equal when normalized, but
-- they currently aren't. This can be achieved by redefining normal
-- forms to avoid redundant branches and refining 𝒞. A tedious
-- endeavour in Agda, but achievable nevertheless.

-- Similarly, the problem of "repeated case analysis" is illustrated
-- below:

repeated-case : Tm Gamma Unit
repeated-case = case (var x2)
  (case (var x3)
    (app print (var x2))
    (app print (var x3))) -- never taken
  (case (var x3)
    (app print (var x2))  -- never taken
    (app print (var x3)))

repeated-case' : Tm Gamma Unit
repeated-case' = case (var x2)
  (app print (var x1))
  (app print (var x2))
