{-# OPTIONS --exact-split #-}

module Boolean where

data Boolean : Set where
  false : Boolean
  true : Boolean

not : Boolean → Boolean
not false = true
not true = false

_and_ : Boolean → Boolean → Boolean
false and _ = false
true and y = y

_or_ : Boolean → Boolean → Boolean
x or y = {!!}

if_then_else_ : Boolean → Boolean → Boolean → Boolean
if false then _ else y = y
if true then x else _ = x

data _≡_  (x : Boolean) : Boolean → Set where
  equal : x ≡ x

test-not-true : (not true) ≡ false
test-not-true = equal

test-not-false : (not false) ≡ true
test-not-false = equal

test-true-and-true : (true and true) ≡ true
test-true-and-true = {!!}

test-x-and-false : (x : Boolean) → (x and false) ≡ false
test-x-and-false false = equal -- Goal: (false and false) ≡ false
test-x-and-false true = equal -- Goal: (true and false) ≡ false

test-false-and-x : (x : Boolean) → (false and x) ≡ false
test-false-and-x = {!!}

test-false-or-false : (false or false) ≡ false
test-false-or-false = {!!}

test-true-or-x : (x : _) → (true and x) ≡ true
test-true-or-x = {!!}

test-if : (if true then false else true) ≡ false
test-if = equal

not′ : Boolean → Boolean
not′ b = if b then false else true

test-not-not′ : ∀ b → not b ≡ not′ b
test-not-not′ false = equal -- Goal: not false ≡ not′ false
test-not-not′ true = equal -- Goal: not true ≡ not′ true
