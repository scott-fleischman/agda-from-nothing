module Script where

-- basic data types

data Singleton : Set where
  singleton : Singleton

data Unit : Set where
  tt : Unit

only-one-value : Singleton
only-one-value = singleton

-- ^C ^N - normalize

another-name : Singleton
another-name = singleton

-- ^C ^N - normalize

data Boolean : Set where
  false : Boolean
  true : Boolean

data Boolean' : Set where
  false true : Boolean'

-- slide 1

data Breakfast : Set where
  bacon : Breakfast
  eggs : Breakfast
  toast : Breakfast

data Breakfast' : Set where
  bacon eggs toast : Breakfast'

data Emotion : Set where
  happy sad angry frustrated surprised afraid : Emotion

data Empty : Set where

-- functions

-- → \r \to
boolean-identity : Boolean → Boolean
boolean-identity true = true
boolean-identity false = false

boolean-identity′ : Boolean → Boolean
boolean-identity′ x = x

-- case split: ^C ^C
-- hole: ?
-- fill a hole: ^C ^space
-- inspect goal, context ^C ^comma 
boolean-identity″ : Boolean → Boolean
boolean-identity″ x = {!!}

-- exercise
not′ : Boolean → Boolean
not′ x = {!!}

not : Boolean → Boolean
not false = true
not true = false

not-true = not true
not-false = not false

and-false : Boolean → Boolean
and-false false = false
and-false true = false

and-true : Boolean → Boolean
and-true false = false
and-true true = true

and′ : Boolean → (Boolean → Boolean)
and′ false = and-false
and′ true = and-true

and-false-false = (and′ false) false
and-true-true = (and′ true) true

and″ : Boolean → Boolean → Boolean
and″ false false = false
and″ false true = false
and″ true false = false
and″ true true = true

-- exercise?

and-false-true = and″ false true

and : Boolean → Boolean → Boolean
--and false y = false
and false _ = false
and true y = y

-- exercise: or

or′ : Boolean → Boolean → Boolean
or′ = {!!}

or″ : Boolean → Boolean → Boolean
or″ false false = false
or″ false true = true
or″ true false = true
or″ true true = true

or : Boolean → Boolean → Boolean
or false y = y
or true _ = true

or-true-false = or true false
or-false-false = or false false

if_then_else_ : Boolean → Boolean → Boolean → Boolean
--if b then x else y = ?
if false then _ else y = y
if true then x else _ = x

not-redux : Boolean → Boolean
not-redux b = if b then false else true

not-redux-false = not-redux false

-- ^C ^D  Boolean Breakfast Emotion : Set
-- if b then bacon else eggs
--if_then_else_ : (A : Set) → Boolean → A → A → A
-- Slide : Dependent function
for_if_then_else_ : (A : Set) → Boolean → A → A → A
-- for_if_then_else_ A b x y = ?
for _ if false then x else y = y
for _ if true then x else y = x

bacon-or-eggs : Boolean → Breakfast
bacon-or-eggs x = for Breakfast if x then bacon else eggs
