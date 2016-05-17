module AgdaFromNothing2 where

-- \lambda  \Gl
-- \to \r

data Empty : Set where

data Unit : Set where
  unit : Unit

data Boolean : Set where
  true : Boolean
  false : Boolean

myUnit : Unit
myUnit = unit

myBool : Boolean
myBool = false

identity : Boolean → Boolean
--identity = λ x → x
identity x = x

-- ^C ^N : normalize
myBool2 : Boolean
myBool2 = identity myBool

-- ?  hole
-- ^C ^, inside of a hole, tells you the goal and premises
-- variable in a hole, ^C ^C -- case split
-- in a hole, ^C ^space fill in the hole
not : Boolean → Boolean
not true = false
not false = true

ex1 = not true
ex2 = not false
ex3 = not (not true)
ex4 = not (not (not false))

_and_ :   (Boolean → (Boolean → Boolean))
true and y = y
false and _ = false

ex5 = true and false
ex6 = true and true

_or_ : Boolean → Boolean → Boolean
true or _ = true
false or y = y

ex7 = true or false
ex8 = (true and false) or true
ex9 = (true and false) or (not (false and true))

if_then_else_ : Boolean → Boolean → Boolean → Boolean
if true then x else _ = x
if false then _ else y = y

ex10 = if ex9 then true else false

not' : Boolean → Boolean
not' x = if x then false else true

ex1' = not' true

_and'_ : Boolean → Boolean → Boolean
x and' y = if x then y else false

ex5' = true and' false
ex6' = true and' true

data Breakfast : Set where
  bacon eggs toast : Breakfast

if'_then_else_ : Boolean → Breakfast → Breakfast → Breakfast
if' true then x else _ = x
if' false then _ else y = y

bf1 : Boolean → Breakfast
bf1 x = if' x then bacon else toast

if''_then_else_ : {A : Set} → Boolean → A → A → A
if'' true then x else _ = x
if'' false then _ else y = y

bf2 : Boolean → Breakfast
bf2 x = if''_then_else_ {A = Breakfast} x bacon toast

ex11 = bf2 true
ex12 = bf2 false
ex13 = bf2 (true and (false or (not true)))


data Number : Set where
  zero : Number
  next : Number → Number
{-# BUILTIN NATURAL Number #-}

n0 = zero
n1 = next zero
n2 = next (next zero)
n3 = next n2
n4 = 12

_+_ : Number → Number → Number
zero     + y = y
(next x) + y = next (x + y)  --  (1 + x) + y  = 1 + (x + y)

ex-n1 = 3 + 7

open import Agda.Primitive

data Equals {level : Level} {A : Set level} (x : A) : A → Set level where
  refl : Equals x x
{-# BUILTIN EQUALITY Equals #-}
{-# BUILTIN REFL refl #-}

value : Equals 2 2
value = refl

proof : Equals (2 + 2) 4
proof = refl

-- 2 + 2
-- (next (next zero)) + (next (next zero))
-- next ( (next zero) + (next (next zero)) )
--        next ( zero + (next (next zero)))
--               (next (next zero))
-- next (next (next (next zero)))

proof1 : (x : Number) → Equals (zero + x) x
proof1 x = refl

proof2with : {x y : Number} → Equals x y → Equals (next x) (next y)
proof2with refl = refl

proof2 : (x : Number) → Equals (x + zero) x
proof2 zero = refl
proof2 (next x) = proof2with (proof2 x)

-- Equals (next (x + zero)) (next x)
--        x + zero = x
-- Equals (next x) (next x)
