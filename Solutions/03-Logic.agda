module 03-Logic where

infixl 6 _or_
infixl 7 _and_

-- A → (B → A)
modus-ponens : {A B : Set} → (A → B) → A → B
modus-ponens f a = f a

data _and_ (A B : Set) : Set where
  both : (a : A) → (b : B) → A and B

data _or_ (A B : Set) : Set where
  first : (a : A) → A or B
  second : (b : B) → A or B

-- A and B → A
proj1 : {A B : Set} → A and B → A
proj1 (both a b) = a

-- A and B → B
proj2 : {A B : Set} → A and B → B
proj2 (both a b) = b

-- A → A or B
inj1 : {A B : Set} → A → A or B
inj1 = first

-- B → A or B
inj2 : {A B : Set} → B → A or B
inj2 = second

or-over-and
  : {A B C : Set}
  → (A and B) or C
  → (A or C) and (B or C)
or-over-and (first (both a b)) = both (first a) (first b)
or-over-and (second x) = both (second x) (second x)

and-over-or
  : {A B C : Set}
  → (A or B) and C
  → (A and C) or (B and C)
and-over-or (both (first a) c) = first (both a c)
and-over-or (both (second b) c) = second (both b c)

data Empty : Set where

not : (A : Set) → Set
not A = A → Empty

empty-to-anything : {A : Set} → Empty → A
empty-to-anything ()

-- (A and B) → not (not A or not B)
not-not-and : {A B : Set} → (A and B) → not (not A or not B)
not-not-and (both a b) (first ae) = ae a
not-not-and (both a b) (second be) = be b

-- (A or B) → not (not A and not B)
not-not-or : {A B : Set} → (A or B) → not (not A and not B)
not-not-or (first a) (both ae be) = ae a
not-not-or (second b) (both ae be) = be b

-- (not A or not B) → not (A and B)
not-from-or : {A B : Set} → (not A or not B) → not (A and B)
not-from-or (first ae) (both a b) = ae a
not-from-or (second be) (both a b) = be b

-- (not A and not B) → not (A or B)
not-from-and : {A B : Set} → (not A and not B) → not (A or B)
not-from-and (both ae be) (first a) = ae a
not-from-and (both ae be) (second b) = be b

-- not (A or B) → (not A and not B)
not-over-or : {A B : Set} → not (A or B) → (not A and not B)
not-over-or {A} {B} f = both notA notB
  where
  notA : A → Empty
  notA x = f (first x)

  notB : B → Empty
  notB x = f (second x)

-- (A and B) → not (A → not B)
and-not-arrow : {A B : Set} → (A and B) → not (A → not B)
and-not-arrow (both a b) anb = anb a b

-- (A → B) → not (A and not B)
arrow-not-and-not : {A B : Set} → (A → B) → not (A and not B)
arrow-not-and-not f (both a be) = be (f a)

-- (A and not B) → not (A → B)
and-not-not-arrow : {A B : Set} → (A and not B) → not (A → B)
and-not-not-arrow (both a be) ab = be (ab a)

-- (A → not B) → not (A and B)
arrow-not-and : {A B : Set} → (A → not B) → not (A and B)
arrow-not-and f (both a b) = f a b

-- not (A and B) → (A → not B)
not-and-arrow-not : {A B : Set} → not (A and B) → (A → not B)
not-and-arrow-not f a b = f (both a b)

-- (A or B) → (not A → B)
or-not-arrow : {A B : Set} → (A or B) → (not A → B)
or-not-arrow (first a) ae = empty-to-anything (ae a)
or-not-arrow (second b) ae = b

-- (not A or B) → (A → B)
not-or-arrow : {A B : Set} → (not A or B) → (A → B)
not-or-arrow (first ae) a = empty-to-anything (ae a)
not-or-arrow (second b) a = b

-- (A → B) → ((A → (B → C)) → (A → C))
arrow-trans : {A B C : Set} → (A → B) → ((A → (B → C)) → (A → C))
arrow-trans f g a = g a (f a)

-- A → (B → A and B)
uncurry : {A B : Set} → A → (B → A and B)
uncurry a b = both a b

-- (A → C) → ((B → C) → (A or B → C))
uncurry-domain : {A B C : Set} → (A → C) → ((B → C) → (A or B → C))
uncurry-domain f g (first a) = f a
uncurry-domain f g (second b) = g b

-- (A → B) → ((A → not B) → not A)
arrow-nots : {A B : Set} → (A → B) → ((A → not B) → not A)
arrow-nots f g a = g a (f a)

-- not A → (A → B)
not-arrow : {A B : Set} → not A → (A → B)
not-arrow f a = empty-to-anything (f a)

-- ∀xA(x) → A(t)
apply-example : {X : Set} → {A : X → Set} → ((x : X) → A x) → (t : X) → A t
apply-example f t = f t

module ApplyExample where
  data X : Set where
    -- constructors...
  data A : X → Set where -- note that (A : X → Set)
    given : (x : X) → A x

-- A(t) → ∃xA(x)
data Pair (X : Set) (A : X → Set) : Set where
  pair : (x : X) → (A x) → Pair X A

-- A(t) → ∃xA(x)
pair-example : {X : Set} → {A : X → Set} → (t : X) → (A t) → Pair X A
pair-example t v = pair t v


-- not (not (A or not A))
not-not-exclusive-middle : {A : Set} → not (not (A or not A))
not-not-exclusive-middle {A} f = f A-or-not-A 
  where
-- f  : A or (A → Empty) → Empty
  not-A : not A -- A → Empty
  not-A x = f (first x)

  A-or-not-A : A or not A -- A or (A → Empty)
  A-or-not-A = second not-A
