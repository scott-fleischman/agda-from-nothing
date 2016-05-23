{-# OPTIONS --exact-split #-}

module 01-Boolean where

infixl 6 _or_ _xor_ _iff_
infixl 7 _and_
infixl 4 _≡_

data Boolean : Set where
  false : Boolean
  true : Boolean

data _≡_ (x : Boolean) : Boolean → Set where
  equal : x ≡ x

not : Boolean → Boolean
not false = true
not true = false

_and_ : Boolean → Boolean → Boolean
false and _ = false
true and y = y

_or_ : Boolean → Boolean → Boolean
false or y = y
true or _ = true

_nand_ : Boolean → Boolean → Boolean
false nand false = true
false nand true = true
true nand false = true
true nand true = false

_nor_ : Boolean → Boolean → Boolean
false nor false = true
false nor true = false
true nor false = false
true nor true = false

_iff_ : Boolean → Boolean → Boolean
false iff false = true
false iff true = false
true iff false = false
true iff true = true 

_xor_ : Boolean → Boolean → Boolean
false xor false = false
false xor true = true
true xor false = true
true xor true = false

if_then_else_ : {X : Set} → Boolean → X → X → X
if false then _ else y = y
if true then x else _ = x

not′ : Boolean → Boolean
not′ b = if b then false else true

not-true-eq-false : not true ≡ false
not-true-eq-false = equal

not-false-eq-true : not false ≡ true
not-false-eq-true = equal

true-and-true-eq-true : true and true ≡ true
true-and-true-eq-true = equal

not-eq-not′ : (x : Boolean) → not x ≡ not′ x
not-eq-not′ false = equal -- Goal: not false ≡ not′ false
not-eq-not′ true = equal -- Goal: not true ≡ not′ true

false-and-x-eq-false : (x : Boolean) → false and x ≡ false
false-and-x-eq-false x = equal

x-and-false-eq-false : (x : Boolean) → x and false ≡ false
x-and-false-eq-false false = equal -- Goal: false and false ≡ false
x-and-false-eq-false true = equal -- Goal: true and false ≡ false

false-or-false-eq-false : false or false ≡ false
false-or-false-eq-false = equal

true-or-x-eq-true : (x : Boolean) → true or x ≡ true
true-or-x-eq-true _ = equal

true-eq-true-or-x : (x : Boolean) → x or true ≡ true
true-eq-true-or-x false = equal -- Goal: false or true ≡ true
true-eq-true-or-x true = equal -- Goal: true or true ≡ true

if-true-then-false-eq-false : if true then false else true ≡ false
if-true-then-false-eq-false = equal

nand-eq-not-and : (x y : Boolean) → x nand y ≡ not (x and y)
nand-eq-not-and false false = equal
nand-eq-not-and false true = equal
nand-eq-not-and true false = equal
nand-eq-not-and true true = equal

nor-eq-not-or : (x y : Boolean) → x nor y ≡ not (x or y)
nor-eq-not-or false false = equal
nor-eq-not-or false true = equal
nor-eq-not-or true false = equal
nor-eq-not-or true true = equal

xor-eq-not-iff : (x y : Boolean) → x xor y ≡ not (x iff y)
xor-eq-not-iff false false = equal
xor-eq-not-iff false true = equal
xor-eq-not-iff true false = equal
xor-eq-not-iff true true = equal
