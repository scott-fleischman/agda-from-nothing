{-# OPTIONS --exact-split #-}

module SimpleTypes where

data Empty : Set where
data Single : Set where
  single : Single
data Boolean : Set where
  true : Boolean
  false : Boolean

-- ?
-- 
-- ^C ^C
NOT : Boolean → Boolean
NOT true = false
NOT false = true

_AND_ : Boolean → Boolean → Boolean
true  AND y = y
false AND _ = false
-- AND _ _ = false
infixr 20 _AND_

-- ^C ^F / ^C ^B
_OR_ : Boolean → Boolean → Boolean
-- OR x y = {!x y!}
true  OR true  = true
true  OR false = true
false OR true  = true
false OR false = false
infixr 19 _OR_

-- ^C ^N
-- ^G
example-b1 : Boolean
example-b1 = NOT true

-- change to _AND_
example-b2 : Boolean
example-b2 = true AND false

-- infixr
example-b3 : Boolean
example-b3 = true AND true AND false

-- infixr 19
example-b4 : Boolean
example-b4 = true AND false OR true


if_then_else_ : Boolean → Boolean → Boolean → Boolean
if true then x else y = x
if false then x else y = y

example-b5 : Boolean
example-b5 = if true then (false AND true) else true


for_if_then_else_ : (A : Set) → Boolean → A → A → A
for A if true then x else y = x
for A if false then x else y = y

data Breakfast : Set where
  bacon eggs toast : Breakfast

this-morning : Boolean → Breakfast
this-morning b = for Breakfast if b then bacon else eggs

implied-if_then_else_ : {A : Set} → Boolean → A → A → A
implied-if true then x else y = x
implied-if false then x else y = y

this-morning' : Boolean → Breakfast -- Boolean → ?
this-morning' b = implied-if b then bacon else eggs


_equals?_ : Boolean → Boolean → Boolean
true equals? true = true
true equals? false = false
false equals? true = false
false equals? false = true


this-morning'' : Breakfast
this-morning'' = implied-if (true equals? true) then bacon else eggs


data Number : Set where
  zero : Number
  suc_ : Number → Number
{-# BUILTIN NATURAL Number #-}

one = suc zero
two = suc suc zero
-- three = suc (suc (suc zero))
three = suc suc suc zero

_+_ : Number → Number → Number
zero + y = y
(suc x) + y = suc (x + y)


_*_ : Number → Number → Number
zero * y = zero
(suc x) * y = y + (x * y)


_≤?_ : Number → Number → Boolean
zero ≤? _ = true
(suc x) ≤? zero = false
(suc x) ≤? (suc y) = x ≤? y

infix 10 _≤_ _≰_
data _≤_ : Number → Number → Set where
  zero≤ : (n : Number) → zero ≤ n
  suc≤ : (n m : Number) → n ≤ m → suc n ≤ suc m

data _≰_ : Number → Number → Set where
  zero≰ : (n : Number) → suc n ≰ zero
  suc≰ : (n m : Number) → n ≰ m → suc n ≰ suc m

flip≰ : (n m : Number) → n ≰ m → m ≤ n
flip≰ .(suc n) .0 (zero≰ n) = zero≤ (suc n)
flip≰ .(suc n) .(suc m) (suc≰ n m x) = suc≤ m n (flip≰ n m x)

data Decidable≤ : Number → Number → Set where
  yes : {n m : Number} → n ≤ m → Decidable≤ n m
  no : {n m : Number} → n ≰ m → Decidable≤ n m

numberDecidable≤ : (n m : Number) → Decidable≤ n m
numberDecidable≤ zero m = yes (zero≤ m)
numberDecidable≤ (suc n) zero = no (zero≰ n)
numberDecidable≤ (suc n) (suc m) with numberDecidable≤ n m
numberDecidable≤ (suc n) (suc m) | yes x = yes (suc≤ n m x)
numberDecidable≤ (suc n) (suc m) | no x = no (suc≰ n m x)


{-
data Number : Set where
  zero : Number
  suc_ : Number → Number
-}

open import Agda.Primitive

--infixr 20 _∷_
data List (la : Level) : Set (lsuc la) where
  end : List la
  add : (A : Set la) → A → List la → List la

mixed : List lzero
mixed = add Breakfast bacon (add Number 6 end)

nestedMixed : List (lsuc lzero)
nestedMixed = add (List lzero) mixed end


max : Number → Number → Number
max zero y = y
max (suc x) zero = suc x
max (suc x) (suc y) = suc (max x y)

data Max : Number → Number → Number → Set where
  zero : (m : Number) → Max m zero m
  suc-zero : (n : Number) → Max (suc n) (suc n) zero
  suc-suc : (x n m : Number) → (Max x n m) → Max (suc x) (suc n) (suc m)


data Ordered : Number → Set where
  start : (n : Number) → Ordered n
  next : (n : Number) → {m : Number} → (n ≤ m) → Ordered m → Ordered n

addInOrder : (n : Number) → {m : Number} → Ordered m → Ordered (max n m)
addInOrder n (start m) with numberDecidable≤ n m
addInOrder n (start m) | yes x = next n x (start (max n m))
addInOrder n (start m) | no x = {!next m (flip≰ n m x) (start n)!}
addInOrder n (next m x xs) = {!!}

{-
with numberDecidable≤ n m
addInOrder n xs | yes x = {!!}
addInOrder n xs | no x = {!!}
-}

data Drink : Set where
  coffee juice : Drink

data Emotion-Traditional : Set where
  happy sad angry afraid surprised digusted : Emotion-Traditional
data Emotion-Simplified : Set where
  happy sad angry afraid : Emotion-Simplified


open import Agda.Builtin.Equality

p1 : (x y z : Boolean) → x AND (y OR z) ≡ (x AND y) OR (x AND z)
p1 true true true = refl
p1 true true false = refl
p1 true false true = refl
p1 true false false = refl
p1 false true true = refl
p1 false true false = refl
p1 false false true = refl
p1 false false false = refl

