module 05-List where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data Boolean : Set where true false : Boolean

infixr 5 _∷_
data List {a : Level} (A : Set a) : Set a where
  [] : List A
  _∷_ : (x : A) → (xs : List A) → List A

length : {a : Level} → {A : Set a} → List A → Nat
length [] = 0
length (x ∷ xs) = 1 + length xs

length-empty-0 : {a : Level} → {A : Set a} → length ([] {A = A}) ≡ 0
length-empty-0 = refl

length-two : {a : Level} → {A : Set a} → {x : A} → length (x ∷ x ∷ []) ≡ 2
length-two = refl

replicate : {a : Level} → {A : Set a} → Nat → A → List A
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

length-replicate : {a : Level} → {A : Set a} → (n : Nat) → (x : A) → length (replicate n x) ≡ n
length-replicate zero x = refl
length-replicate (suc n) x rewrite length-replicate n x = refl

map : {a b : Level} → {A : Set a} → {B : Set b}
  → (f : A → B)
  → List A
  → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-preserves-length : {a b : Level} → {A : Set a} → {B : Set b}
  → (f : A → B)
  → (xs : List A)
  → length (map f xs) ≡ length xs
map-preserves-length f [] = refl
map-preserves-length f (x ∷ xs) rewrite map-preserves-length f xs = refl

apply : {a b : Level} → {A : Set a} → {B : Set b}
  → List (A → B)
  → List A
  → List B
apply [] [] = []
apply [] (x ∷ xs) = []
apply (f ∷ fs) [] = []
apply (f ∷ fs) (x ∷ xs) = f x ∷ apply fs xs

append : {a : Level} → {A : Set a} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

append-length : {a : Level} → {A : Set a}
  → (xs : List A)
  → (ys : List A)
  → length (append xs ys) ≡ length xs + length ys
append-length [] ys = refl
append-length (x ∷ xs) ys rewrite append-length xs ys = refl

data Vec {a : Level} (A : Set a) : Nat → Set a where
  [] : Vec A zero
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

vlength : {a : Level} → {A : Set a} → {n : Nat} → Vec A n → Nat
vlength {n = n} v = n

vreplicate : {a : Level} → {A : Set a} → (n : Nat) → A → Vec A n
vreplicate zero x = []
vreplicate (suc n) x = x ∷ vreplicate n x

vmap : {a b : Level} → {A : Set a} → {B : Set b} → {n : Nat}
  → (f : A → B)
  → Vec A n
  → Vec B n
vmap f [] = []
vmap f (x ∷ xs) = f x ∷ vmap f xs

vapply : {a b : Level} → {A : Set a} → {B : Set b} → {n : Nat}
  → Vec (A → B) n
  → Vec A n
  → Vec B n
vapply [] [] = []
vapply (f ∷ fs) (x ∷ xs) = f x ∷ vapply fs xs

vappend : {a : Level} → {A : Set a} → {n m : Nat}
  → Vec A n
  → Vec A m
  → Vec A (n + m)
vappend [] ys = ys
vappend (x ∷ xs) ys = x ∷ vappend xs ys
