{-# OPTIONS --exact-split #-}

module 01-Boolean where

infixl 6 _or_
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

if_then_else_ : Boolean → Boolean → Boolean → Boolean
if false then _ else y = y
if true then x else _ = x

not′ : Boolean → Boolean
not′ b = if b then false else true

test-not-true : not true ≡ false
test-not-true = equal

test-not-false : not false ≡ true
test-not-false = equal

test-true-and-true : true and true ≡ true
test-true-and-true = equal

test-x-and-false : ∀ x → x and false ≡ false
test-x-and-false false = equal -- Goal: false and false ≡ false
test-x-and-false true = equal -- Goal: true and false ≡ false

test-false-and-x : ∀ x → false and x ≡ false
test-false-and-x x = equal

test-false-or-false : false or false ≡ false
test-false-or-false = equal

test-true-or-x : ∀ x → true or x ≡ true
test-true-or-x _ = equal

test-if : if true then false else true ≡ false
test-if = equal

test-not-not′ : ∀ x → not x ≡ not′ x
test-not-not′ false = equal -- Goal: not false ≡ not′ false
test-not-not′ true = equal -- Goal: not true ≡ not′ true
