{-# OPTIONS --exact-split #-}

module Faithlife where

data Singleton : Set where
  singleton : Singleton

data Boolean : Set where
  true false : Boolean

data _≡_ {X : Set} (x : X) : X → Set where
  equal : x ≡ x

statement : true ≡ true
statement = equal

data Empty : Set where

not : Boolean → Boolean
not true = false
not false = true

not-true-false : (not true) ≡ false
not-true-false = equal

identity : Boolean → Boolean
identity x = x

and-false : Boolean → Boolean
and-false _ = false

and : Boolean → (Boolean → Boolean)
and true = identity
and false = and-false

and′ : Boolean → Boolean → Boolean
and′ true true = true
and′ true false = false
and′ false _ = false

and-false-false : (x : Boolean) → (and x false) ≡ false
and-false-false true = equal -- Equal (and true false) false
and-false-false false = equal --  Equal (and false false) false

data Number : Set where
  zero : Number
  suc : Number → Number
{-# BUILTIN NATURAL Number #-}

n0 = zero
n1 = suc zero
n2 = suc (suc zero)
n2' = suc n1

n2=n2' : n2 ≡ n2'
n2=n2' = equal

n2=n1 : n2 ≡ n1 → Empty
n2=n1 ()

if_then_else_ : Boolean → Boolean → Boolean → Boolean
if true then x else y = x
if false then x else y = y

not' : Boolean → Boolean
not' x = if x then false else true

not=not' : (x : Boolean) → (not x) ≡ (not' x)
not=not' true = equal
not=not' false = equal

_+_ : Number → Number → Number
zero + y = y
suc x + y = suc (x + y) -- (1 + x) + y == 1 + (x + y)
{-# BUILTIN NATPLUS _+_ #-}

2+2=4 : (2 + 2) ≡ 4
2+2=4 = equal

_*_ : Number → Number → Number
zero * y = zero
suc x * y = y + (x * y)
{-# BUILTIN NATTIMES _*_ #-}

2*3=6 : (2 * 3) ≡ 6
2*3=6 = equal

_^_ : Number → Number → Number
x ^ zero = 1
x ^ suc y = x * (x ^ y)

2^3=8 : (2 ^ 3) ≡ 8
2^3=8 = equal

2^16 : (2 ^ 16) ≡ 65536
2^16 = equal

2^32 : (2 ^ 17) ≡ (65536 * 2)
2^32 = equal

data Decidable (X : Set) : Set where
  is-true : (x : X) → Decidable X
  is-false : (x : X → Empty) → Decidable X

isLessThan : Number → Number → Boolean
isLessThan = {!!}

data _≤_ : Number → Number → Set where
  zero≤ : {n : Number} → zero ≤ n
  suc≤ : {n m : Number} → n ≤ m → suc n ≤ suc m

data _≰_ : Number → Number → Set where
  ≰zero : {n : Number} → suc n ≰ zero
  suc≰ : {n m : Number} → n ≰ m → suc n ≰ suc m

data Decidable≤ : Number → Number → Set where
  is-true : {n m : Number} → n ≤ m → Decidable≤ n m
  is-false : {n m : Number} → n ≰ m → Decidable≤ n m

_≤?_ : (x y : Number) → Decidable≤ x y
zero ≤? y = is-true zero≤
(suc x) ≤? zero = is-false ≰zero
(suc x) ≤? (suc y) with x ≤? y
(suc x) ≤? (suc y) | is-true p = is-true (suc≤ p)
(suc x) ≤? (suc y) | is-false p = is-false (suc≰ p)

open import Agda.Builtin.Unit

which : {x y : Number} → Decidable≤ x y → Set
which (is-true x) = ⊤
which (is-false x) = Empty

test1 : which (7 ≤? 6) → Empty
test1 ()

test2 : which (5 ≤? 6)
test2 = _
