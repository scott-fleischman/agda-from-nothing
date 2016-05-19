module AgdaFromNothing1 where

-- \Gl λ
-- \to →

data Empty : Set where

-- ? is a hole
-- ^C ^L is load file
-- ^C ^, in hole you see the goal and premises
empty : Empty
empty = {!!}

data Singleton : Set where
  singleton : Singleton

-- ^C ^R refine
singleTerm : Singleton
singleTerm = singleton

data Boolean : Set where
  true false : Boolean

-- ^C ^(spacebar) fill hole and validate
b1 : Boolean
b1 = true

data Breakfast : Set where
  bacon eggs toast : Breakfast

identity : Boolean -> Boolean
--identity = λ x -> x
identity x = x

-- ^C ^N  normalize/reduce expression

id-false = identity false
--id-false = ( λ x -> x ) false
--id-false = false

-- 2 + 2 -> 4
-- 4/8 -> 1/2

-- in a hole, type name, then ^C ^C
not : Boolean -> Boolean
not true = false
not false = true
-- not = λ x -> ?

-- ^C ^= in a hole shows contraints
not-true : Boolean
not-true = not true

-- ^G exit
_and_ : Boolean -> Boolean -> Boolean
--and = λ x -> (λ y -> ...)
--and = λ x -> λ y -> ...
--and = λ x y -> ...
true and y = y
false and _ = false

a1 = true and false

if_then_else_ : Boolean -> Boolean -> Boolean -> Boolean
if true then x else _ = x
if false then _ else y = y

if1 = if true then false else true

data Number : Set where
  zero : Number
  suc_ : Number → Number
{-# BUILTIN NATURAL Number #-}

_+_ : Number -> Number -> Number
zero + y = y
(suc x) + y = suc (x + y) -- (1 + x) + y = 1 + (x + y)

data Equals : Number → Number → Set where
  refl : {x : Number} → Equals x x

simple : Equals (1 + 3) (2 + 2)
simple = refl
