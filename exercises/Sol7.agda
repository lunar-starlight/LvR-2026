{-# OPTIONS --prop #-}

---------------------------------------------------------------------------
-- Week 7 exercises for the Logika v računalništvu course at UL FMF      --
-- Lecturer: Alex Simpson                                                --
-- Teaching Assistant: Luna Strah                                        --
--                                                                       --
-- Adapted from Danel Ahmans's exercises from 2022 available at:         --
-- https://github.com/danelahman/lograc-2022/blob/main/exercises/        --
--                                                                       --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252 --
---------------------------------------------------------------------------

module Sol7 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; _≢_)
open import Relation.Nullary using (¬_)


-- data ℕ : Set where
--   zero : ℕ
--   suc  : ℕ → ℕ

-- infixl 6  _+_
-- infixl 7  _*_

-- _+_ : ℕ → ℕ → ℕ
-- zero    + n = n
-- (suc m) + n = suc (m + n)

-- _*_ : ℕ → ℕ → ℕ
-- zero * n = zero
-- suc m * n = n + m * n

-- {-# BUILTIN NATURAL ℕ #-}
-- {-# BUILTIN NATPLUS _+_ #-}
-- {-# BUILTIN NATTIMES _*_ #-}

-- infixr 5 _∷_

-- data List (A : Set) : Set where
--   []  : List A
--   _∷_ : A → List A → List A

-- {-# BUILTIN LIST List #-}

-- length : {A : Set} → List A → ℕ
-- length [] = zero
-- length (x ∷ xs) = suc (length xs)
-- map : {A B : Set} → (A → B) → List A → List B
-- map f [] = []
-- map f (x ∷ xs) = f x ∷ map f xs

-- data Vec (A : Set) : ℕ → Set where
--   []  : Vec A 0
--   _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- infix 4 _≡_

-- data _≡_ {A : Set} (x : A) : A → Set where
--   refl : x ≡ x

-- symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
-- symm refl = refl

-- trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- trans refl q = q

-- cong : {A B : Set} (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
-- cong f refl = refl

-- subst : {A : Set} {B : A → Set} {x y : A} → x ≡ y → B x → B y
-- subst refl a = a

-- data ⊥ : Set where

-- infix 3 ¬_
-- ¬_ : Set → Set
-- ¬ P = P → ⊥

-- infix 4 _≢_
-- _≢_ : {A : Set} → A → A → Set
-- x ≢ y = ¬ x ≡ y

{-
   We also postulate the principle of function extensionality so
   that you can use it if and when needed in the exercises below.
-}

postulate
  fun-ext : {A : Set} {B : A → Set} {f g : (x : A) → B x}
          → ((x : A) → f x ≡ g x)
          → f ≡ g




-------------------------------
-------------------------------
-- SIMPLER EXERCISES [START] --
-------------------------------
-------------------------------

----------------
-- Exercise 0 --
----------------

{-
   Start by proving the following simple equational properties about natural numbers and addition.
   Hint: Use induction. You might find it useful to recall the congruence principle `cong` from
   lecture.
-}

+-identityʳ : (n : ℕ) → n + zero ≡ n
+-identityʳ zero = refl
+-identityʳ (suc n) = cong suc (+-identityʳ n)

+-identityˡ : (n : ℕ) → zero + n ≡ n
+-identityˡ n = refl

+-suc : (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

suc-inj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl


----------------
-- Exercise 1 --
----------------

{- Define the function `lookup` that looks up the value in a given vector at a given natural number
   index.

   As the index below can be an arbitrary natural number, then we have to define `lookup` as a
   partial function. We do this by giving `lookup` the `Maybe` return type, which has two
   constructors: one for the value if the function is defined, and one to mark that that the
   functions is not defined. Set-theoretically, `Maybe A` should be read as the disjoint union of
   sets `A` and `{ nothing }`. -}

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

lookup : {A : Set} {n : ℕ} → Vec A n → ℕ → Maybe A
--lookup xs i = {!!}
lookup [] i = nothing
lookup (x ∷ xs) zero = just x
lookup (x ∷ xs) (suc i) = lookup xs i


----------------
-- Exercise 7 --
----------------

{-
   There are several ways of defining relations on types. For example, lets define the ≤ relation on
   natural numbers.
-}

module WithProp where
  data _≤_ : ℕ → ℕ → Prop where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

  infix 4 _≤_

module WithSet where
  data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

  infix 4 _≤_

module WithPropInd where
  open WithProp

  {-
    However trying to define a Type-elimination principle for `≤` with `Prop` fails. You can attempt
    to finish the definition below, but since you are unable to pattern-match on `p`.
  -}
  module _ (P : (m n : ℕ) → Set)
    (pzn : (n : ℕ) → P zero n)
    (pss : (m n : ℕ) → P m n → P (suc m) (suc n)) where

    -- ≤-ind : (m n : ℕ) → m ≤ n → P m n
    -- ≤-ind zero    n       p = pzn n
    -- ≤-ind (suc m) (suc n) p = {!!}
    --≤-ind (suc m) (suc n) p = pss m n (≤-ind m n p)


module WithSetInd where
  open WithSet

  module _ (P : (m n : ℕ) → Set)
    (pzn : (n : ℕ) → P zero n)
    (pss : (m n : ℕ) → P m n → P (suc m) (suc n)) where

    ≤-ind : (m n : ℕ) → m ≤ n → P m n
    ≤-ind m n z≤n = pzn n
    ≤-ind m n (s≤s p) = pss _ _ (≤-ind _ _ p)
    -- Here we must omit the arguments to `pss` and `≤-ind`, since they should be predecessors of
    -- `m` and n. Alternatively, we should pattern-match on `m` and `n` to extract their
    -- predecessors (we already know they are successors).


module WithPropButWithSetEliminationAsWell where

  data ⊥ᵖ : Prop where

  record ⊤ᵖ : Prop where
    constructor tt

  _≤_ : ℕ → ℕ → Prop
  zero  ≤ n     = ⊤ᵖ
  suc m ≤ zero  = ⊥ᵖ
  suc m ≤ suc n = m ≤ n

  infix 4 _≤_

module WithPropButWithSetEliminationAsWellInd where
  open WithPropButWithSetEliminationAsWell

  module _ {P : (m n : ℕ) → Set}
    (pzn : (n : ℕ) → P zero n)
    (pss : (m n : ℕ) → P m n → P (suc m) (suc n)) where

    ≤-ind : (m n : ℕ) → m ≤ n → P m n
    ≤-ind zero n p = pzn n
    ≤-ind (suc m) (suc n) p = pss m n (≤-ind m n p)

{-
   At various times we will be comparing the two definitions, so we import both. We shall try to
   work with the definition using `Prop` defined as a function, however that might change in the
   future. Feel free to comment out the modules `WithProp` and `WithPropInd` above, if you feel they
   pollute your workspace.
-}

open WithPropButWithSetEliminationAsWell
open WithSet using () renaming (_≤_ to _≤ˢ_; z≤n to z≤ˢn; s≤s to s≤ˢs)

≤-to-≤ˢ : (m n : ℕ) → m ≤ n → m ≤ˢ n
≤-to-≤ˢ zero _ _ = z≤ˢn
≤-to-≤ˢ (suc m) (suc n) p = s≤ˢs (≤-to-≤ˢ m n p)

≤ˢ-to-≤ : (m n : ℕ) → m ≤ˢ n → m ≤ n
≤ˢ-to-≤ m n z≤ˢn = tt
≤ˢ-to-≤ m n (s≤ˢs p) = ≤ˢ-to-≤ _ _ p


----------------
-- Exercise 7 --
----------------

{-
   Show that `≤` gives a partial order on ℕ.
-}

reflexive : (n : ℕ) → n ≤ n
reflexive zero = tt
reflexive (suc n) = reflexive n

transitive : (m n k : ℕ) → m ≤ n → n ≤ k → m ≤ k
transitive zero n k p q = tt
transitive (suc m) (suc n) (suc k) p q = transitive m n k p q


anti-symmetric : (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
anti-symmetric zero zero p q = refl
anti-symmetric (suc m) (suc n) p q = cong suc (anti-symmetric m n p q)



----------------
-- Exercise = --
----------------

{-
   Recall the "is even" predicate for unary numbers.
-}

data Even : ℕ → Set where
  even-z : Even zero
  even-ss : {n : ℕ} → Even n → Even (suc (suc n))


is-even : ℕ → Prop
is-even zero = ⊤ᵖ
is-even (suc zero) = ⊥ᵖ
is-even (suc (suc n)) = is-even n



-----------------
-- Exercise 12 --
-----------------

{-
   consider a strict comparison relation on the naturals.
-}

_<_ : ℕ → ℕ → Prop
n < m = suc n ≤ m

_>_ : ℕ → ℕ → Prop
n > m = m < n

infix 4 _<_
infix 4 _>_


{-
   This allows us to state (and prove) a correctness theorem for `lookup` from earlier. For
   simplicity we shall only consider vectors over the unit type `⊤`.
-}


open import Data.Unit
--data ⊤ : Set where
--  tt : ⊤

lookup-totalᵀ : {n : ℕ}
              → (xs : Vec ⊤ n)
              → (i : ℕ)
              → i < n
              → lookup xs i ≡ just tt
lookup-totalᵀ (x ∷ xs) zero p = refl
lookup-totalᵀ (x ∷ xs) (suc i) p = lookup-totalᵀ xs i p


----------------
-- Exercise 3 --
----------------

{-
   The `lookup-totalᵀ` lemma above is commonly called an "extrinsic" proof because we prove the
   correctness of `lookup` after the fact, externally to its (simply typed, regarding the index `i`)
   definition.

   In contrast, we could instead make use of the expressiveness of dependent types and define an
   alternative `safe-lookup` function that is total and guaranteed to always return a value of type
   `A`. In this case one will have to prove that the index is in the range in order to be able to
   call the `safe-lookup` function below.

   We do this by restricting the index argument of the function to be from the finite set of natural
   numbers `{ 0 , 1 , ... , n - 1 }` already in the type signature of the lookup function. For this
   we will use the dependent type `Fin` defined below. As this "correctness of the index argument"
   specification is now imposed in the types at definition time, this style of proof is commonly
   called "intrinsic".

   Intuitively, `Fin n` is the finite set `{ 0 , 1 , ... , n - 1 }`.
-}

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

safe-lookup : {A : Set} {n : ℕ} → Vec A n → Fin n → A
safe-lookup [] ()
safe-lookup (x ∷ xs) zero = x
safe-lookup (x ∷ xs) (suc i) = safe-lookup xs i


----------------
-- Exercise 4 --
----------------

{-
   Prove that the two lookup functions compute the same value if the given index is in an
   appropriate range.

   In order to pass the given natural number `i` as an argument to the `safe-lookup` function, you
   will have to convert it to an element of `Fin` with the `nat-to-fin` function. As a challenge,
   the type of `nat-to-fin` is left for you to complete (notice the hole in the type). Hint: You
   should be able to reverse-engineer it from its use in the type of `lookup-correct` below. If you
   fill the hole with the correct type, the yellow highlighting below will disappear. -}

nat-to-fin : {n : ℕ} (i : ℕ) → i < n → Fin n
nat-to-fin {suc n} zero p = zero
nat-to-fin {suc n} (suc i) p = suc (nat-to-fin i p)

lookup-correct : {A : Set} {n : ℕ}
               → (xs : Vec A n)
               → (i : ℕ)
               → (p : i < n)
               → lookup xs i ≡ just (safe-lookup xs (nat-to-fin i p))
lookup-correct (x ∷ xs) zero p = refl
lookup-correct (x ∷ xs) (suc i) p = lookup-correct xs i p


----------------
-- Exercise 7 --
----------------

{-
   Recall the conversion maps between vectors and lists.
-}

to-list : {A : Set} {n : ℕ} → Vec A n → List A
to-list [] = []
to-list (x ∷ xs) = x ∷ to-list xs

to-vec : {A : Set} (xs : List A) → Vec A (length xs)
to-vec [] = []
to-vec (x ∷ xs) = x ∷ to-vec xs

{-
   Prove that the `to-list` function produces a list with the same length as the given vector.
-}

to-list-length : {A : Set} {n : ℕ}
                → (xs : Vec A n)
                → n ≡ length (to-list xs)
to-list-length [] = refl
to-list-length (x ∷ xs) = cong suc (to-list-length xs)



-------------------------------------
-------------------------------------
-- MORE INVOLVED EXERCISES [START] --
-------------------------------------
-------------------------------------

open import Function using (id; _∘_)


-----------------
-- Exercise 10 --
-----------------

{-
   Prove that `to-list` is the left inverse of `to-vec`. Observe that you have to prove equality
   between functions.
-}

list-vec-list : {A : Set}
              → (to-list ∘ to-vec) ≡ id {A = List A}
list-vec-list {A} = fun-ext list-vec-list-aux
  where
    list-vec-list-aux : (xs : List A) → (to-list ∘ to-vec) xs ≡ xs
    list-vec-list-aux [] = refl
    list-vec-list-aux (x ∷ xs) = cong (x ∷_) (list-vec-list-aux xs)




-----------------
-- Exercise 12 --
-----------------

{-
   Show equality on the natural numbers is decidable.
-}

data _</≡/>_ (m n : ℕ) : Set where
  m<n : m < n → m </≡/> n
  m≡n : m ≡ n → m </≡/> n
  m>n : m > n → m </≡/> n

{-
   Define a function `test-</≡/>` that, given two natural numbers, returns the proof of either
   `n < m`, `n ≡ m`, or `n > m` depending on the relationship between the given two numbers.

   In its essence, the function `test-</≡/>` shows that the natural ordering relation on natural
   numbers is total and decidable---we can compute which of the three situations actually holds. See
   PLFA (https://plfa.inf.ed.ac.uk/Decidable/) for more details.
-}

test-</≡/> : (m n : ℕ) → m </≡/> n
test-</≡/> zero zero = m≡n refl
test-</≡/> zero (suc n) = m<n tt
test-</≡/> (suc m) zero = m>n tt
test-</≡/> (suc m) (suc n) with test-</≡/> m n
... | m<n x = m<n x
... | m≡n refl = m≡n refl
... | m>n x = m>n x


-----------------
-- Exercise 13 --
-----------------

{-
   Below is the inductive type `Tree A` of node-labelled binary trees
   holding data of type `A` in their nodes. Such a tree is either an
   `empty` tree (holding no data); or a root node built from a left
   subtree `t`, data `n`, and a right subtree `u`, written `node t n u`.

   For example, the binary tree

           42
           /\
          /  \
         22  52
          \
           \
           32

   would be represented in Agda as the expression

     `node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)`

   of type `Tree ℕ`.
-}

data Tree (A : Set) : Set where
  empty : Tree A
  node  : Tree A → A → Tree A → Tree A

{-
   For trees holding natural numbers, define a function that inserts a given natural number into a
   tree following the insertion strategy for binary search trees
   (https://en.wikipedia.org/wiki/Binary_search_tree).

   Namely, when inserting a number `n` into an `empty` tree, the function should create a new
   trivial tree containing just `n`; and when recursively inserting a number `n` into a tree of the
   form `node t m u`, the function should behave as one of the following three cases: - if n = m,
   then the function just returns the given tree, doing nothing; - if n < m, then the function
   recursively tries to add `n` into `t`; or - if n > m, then the function recursively tries to add
   `n` into `u`.

   Hint: When testing which of the three situations holds for a `node t m u` case, you might find it
   helpful to use Agda's `with` abstraction
   (https://agda.readthedocs.io/en/v2.6.2.1/language/with-abstraction.html) to do perform
   pattern-matching without having to define auxiliary functions.
-}

insert : Tree ℕ → ℕ → Tree ℕ
insert empty n = node empty n empty
insert (node t x u) n with test-</≡/> x n
... | m<n p = node t x (insert u n)
... | m≡n p = node t x u
... | m>n p = node (insert t n) x u

{-
   As a sanity check, prove that inserting 12, 27, and 52 into the above
   example tree correctly returns the expected trees.
-}

insert-12 : insert (node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)) 12
            ≡
            node (node (node empty 12 empty) 22 (node empty 32 empty)) 42 (node empty 52 empty)
insert-12 = refl

insert-27 : insert (node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)) 27
            ≡
            node (node empty 22 (node (node empty 27 empty) 32 empty)) 42 (node empty 52 empty)
insert-27 = refl

insert-52 : insert (node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)) 52
            ≡
            node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)
insert-52 = refl


-----------------
-- Exercise 14 --
-----------------

{-
   Define an inductive relation `∈` that specifies that a given natural
   number exists in the given tree.

   Hint: This relation should specify a path in a given tree from its
   root to the desired natural number whose existence we are specifying.
-}

data _∈_ (n : ℕ) : Tree ℕ → Set where
  ∈-here : {t u : Tree ℕ} → n ∈ node t n u
  ∈-left : {t u : Tree ℕ} {x : ℕ} → n ∈ t → n ∈ node t x u
  ∈-right : {t u : Tree ℕ} {x : ℕ} → n ∈ u → n ∈ node t x u


{-
   Prove that the tree returned by the `insert` function indeed
   contains the inserted natural number.

   Hint: If you used Agda's `with` abstraction for pattern-matching in
   the definition of `insert`, you will need to perform similar amount
   of pattern-matching also in this proof to make the type of the hole
   compute. You can tell when this is needed because the type of the
   hole will involve an expression of the form `f v | g w`, meaning
   that in order for `f v` to be computed and normalised further, you
   need to first pattern-match on the value of `g v` (using `with`).

   If you haven't spotted this already, then it is part of a general
   pattern---proofs often follow the same structure as the definitions.
-}

insert-∈ : (t : Tree ℕ) → (n : ℕ) → n ∈ (insert t n)
insert-∈ empty n = ∈-here
insert-∈ (node t x u) n with test-</≡/> x n
... | m<n p = ∈-right (insert-∈ u n)
... | m≡n refl = ∈-here
... | m>n p = ∈-left (insert-∈ t n)


-------------------------------------
-------------------------------------
-- MOST INVOLVED EXERCISES [START] --
-------------------------------------
-------------------------------------

-----------------
-- Exercise 15 --
-----------------

{-
   While above you were asked to define the `insert` function
   following the insertion strategy for binary search trees, then
   concretely the function is still working on arbitrary binary
   trees. Here we will define an inductive predicate to classify
   binary trees that are indeed binary search trees and prove that
   the `insert` function preserves this predicate.
-}

{-
   Before we define the binary search tree predicate, we extend
   the type of natural numbers with bottom and top elements,
   written `-∞` and `+∞` (for symmetry and their analogy with
   negative and positive infinities; also, `⊥` and `⊤` are already
   used in Agda for the empty and unit type). We then also extend the
   order `<` to take these new bottom and top elements into account.
-}

data ℕ∞ : Set where
  -∞  :     ℕ∞
  [_] : ℕ → ℕ∞
  +∞  :     ℕ∞

_<∞_ : ℕ∞ → ℕ∞ → Prop
-∞ <∞ -∞ = ⊥ᵖ
-∞ <∞ [ x ] = ⊤ᵖ
-∞ <∞ +∞ = ⊤ᵖ
[ m ] <∞ -∞ = ⊥ᵖ
[ m ] <∞ [ n ] = m < n
[ m ] <∞ +∞ = ⊤ᵖ
+∞ <∞ n = ⊥ᵖ

{-
   Using this extended definition of natural numbers, we next define
   an inductive predicate `IsBST` on binary trees that specifies when
   a given binary tree holding natural numbers is in fact a binary
   search tree (https://en.wikipedia.org/wiki/Binary_search_tree).

   Note that, concretely, the `IsBST` predicate consists of two definitions:
   - the `IsBST` predicate, which is the "top-level" predicate specifying
     that a given binary tree is in a binary search tree format; and
   - the recursively defined relation `IsBST-rec`, which does most of the
     work in imposing the binary search tree invariant on the given tree.

   The `IsBST-rec` relation carries two additional `ℕ∞`-arguments that
   specify the range of values a given binary search tree is allowed
   to hold, in particular, which values the left and right subtrees of
   a `node t n u` tree node are allowed to store. Further, note that the
   `empty` case holds a proof that `lower` is indeed less than `upper`.
-}

data IsBST-rec (lower upper : ℕ∞) : Tree ℕ → Set where
  empty-bst : {p : lower <∞ upper} → IsBST-rec lower upper empty
  node-bst  : {t u : Tree ℕ} {n : ℕ}
            → IsBST-rec lower [ n ] t
            → IsBST-rec [ n ] upper u
            → IsBST-rec lower upper (node t n u)

data IsBST : Tree ℕ → Set where
  empty-bst : IsBST empty
  node-bst  : {t u : Tree ℕ} {n : ℕ}
            → IsBST-rec -∞ [ n ] t
            → IsBST-rec [ n ] +∞ u
            → IsBST (node t n u)

{-
   Prove that having the `(p : lower <∞ upper)` proof witness in the
   `empty` cases of the `IsBST-rec` relation indeed forces the `<∞`
   relation to hold for the bound indices of `IsBST-rec` in general.

   Hint: You might find it helpful to prove the transitivity of `<∞`.
-}

trans-< : (m n l : ℕ) → m < n → n < l → m < l
trans-< zero (suc _) (suc _) _ _ = tt
trans-< (suc m) (suc _) (suc l) p q = trans-< m _ l p q
trans-<∞ : (m n l : ℕ∞) → m <∞ n → n <∞ l → m <∞ l
trans-<∞ -∞ [ _ ] [ _ ] _ _ = tt
trans-<∞ -∞ [ _ ] +∞ _ _ = tt
trans-<∞ [ m ] [ n ] [ l ] p q = trans-< m n l p q
trans-<∞ [ _ ] [ _ ] +∞ _ _ = tt

isbst-rec-<∞ : {lower upper : ℕ∞} {t : Tree ℕ}
             → IsBST-rec lower upper t
             → lower <∞ upper
isbst-rec-<∞ (empty-bst {p}) = p
isbst-rec-<∞ {lower} {upper} (node-bst p q) = trans-<∞ lower _ upper (isbst-rec-<∞ p) (isbst-rec-<∞ q)

{-
   Disclaimer: The `(p : lower <∞ upper)` proof witness in the `empty`
   case of the `IsBST-rec` relation means that every proof about a
   given tree being a binary search tree needs one to construct such
   proofs explicitly for all `empty` (sub)trees. For example, see below:
-}

{-
   In fact, defining `<∞` as we did above also makes the definition of transitivity worse. Try
   defining it as a datatype in `Set` and compare the proofs of transitivity.
-}

--_<ˢ_ : (m n : ℕ) → Set
--m <ˢ n = suc m ≤ˢ n

data _<ˢ_ : ℕ → ℕ → Set where
  z<ˢsn : {n : ℕ} → zero <ˢ suc n
  s<ˢs  : {m n : ℕ} → m <ˢ n → suc m <ˢ suc n

data _<ˢ∞_ : ℕ∞ → ℕ∞ → Set where
  -∞<ˢn  : {n   : ℕ∞}  →           -∞   <ˢ∞   n
  []<ˢ[] : {n m : ℕ}   → n <ˢ m → [ n ] <ˢ∞ [ m ]
  n<ˢ+∞  : {n   : ℕ∞}  →            n   <ˢ∞  +∞

trans-<ˢ : {n m k : ℕ} → n <ˢ m → m <ˢ k → n <ˢ k
trans-<ˢ z<ˢsn (s<ˢs q) = z<ˢsn
trans-<ˢ (s<ˢs p) (s<ˢs q) = s<ˢs (trans-<ˢ p q)

trans-<ˢ∞ : {n m k : ℕ∞} → n <ˢ∞ m → m <ˢ∞ k → n <ˢ∞ k
trans-<ˢ∞ -∞<ˢn _ = -∞<ˢn
trans-<ˢ∞ ([]<ˢ[] p) ([]<ˢ[] q) = []<ˢ[] (trans-<ˢ p q)
trans-<ˢ∞ ([]<ˢ[] p) n<ˢ+∞ = n<ˢ+∞
trans-<ˢ∞ n<ˢ+∞ n<ˢ+∞ = n<ˢ+∞

-----------------
-- Exercise 16 --
-----------------

{-
   Prove that being a binary search tree is invariant under `insert`.

   Hint: As the `IsBST` predicate is defined in two steps, then you
   might find it useful to prove an auxiliary lemma about `insert`
   preserving also the recursively defined `IsBST-rec` relation.
-}


insert-bst-rec : {lower upper : ℕ∞} (t : Tree ℕ) → (n : ℕ)
               → (p : lower <∞ [ n ])
               → (q : [ n ] <∞ upper)
               → IsBST-rec lower upper t
               → IsBST-rec lower upper (insert t n)
insert-bst-rec _ _ p q empty-bst = node-bst (empty-bst {p = p}) (empty-bst {p = q})
insert-bst-rec _ n p q (node-bst {t} {u} {m} r s) with test-</≡/> m n
... | m<n x = node-bst r (insert-bst-rec u n x q s)
... | m≡n refl = node-bst r s
... | m>n x = node-bst (insert-bst-rec t n p x r) s

insert-bst : (t : Tree ℕ) → (n : ℕ) → IsBST t → IsBST (insert t n)
insert-bst t n empty-bst = node-bst empty-bst empty-bst
insert-bst _ n (node-bst {t} {u} {n = m} p q) with test-</≡/> m n
... | m<n r = node-bst p (insert-bst-rec u n r tt q)
... | m≡n r = node-bst p q
... | m>n r = node-bst (insert-bst-rec t n tt r p) q

-----------------
-- Exercise 17 --
-----------------

{-
   Prove that `list-vec` is the left inverse of `vec-list`. Observe that you have to prove equality
   between functions.

   Note that if we simply wrote `id` as the right-hand side of the equational property below we
   would get a typing error about a mismatch in the natural number indices. Find a way to fix the
   type of a given vector to use it in the right-hand side of the equation.

   Hint 1: For a slightly unsatisfactory solution, think how you could convert a given vector to
   another of a given type using recursion.

   Hint 2: For a more complete solution, recall from the exercises how one change the type of a
   given value (e.g., a vector) using a previously proved equality proof, and then combine this with
   one of the equational lemmas we proved above.

   WARNING: The hint 2 solution of this exercise is probably the most complex on this exercise
   sheet, as it will require some careful thought when generalising the concrete statement you are
   trying to prove, relating element-wise equality of vectors to the `≡` relation on vectors, etc.
   So we suggest you leave this one for the very last. -}

vec-list-conv : {A : Set} {n : ℕ}
              → (xs : Vec A n)
              → Vec A (length (to-list xs))
vec-list-conv []       = []
vec-list-conv (x ∷ xs) = x ∷ vec-list-conv xs

vec-list-vec : {A : Set} {n : ℕ}
             → to-vec ∘ to-list ≡ vec-list-conv {A} {n}
vec-list-vec {A} {n} = fun-ext aux
  where
    aux : {n : ℕ} → (xs : Vec A n) → (to-vec ∘ to-list) xs ≡ vec-list-conv xs
    aux [] = refl
    aux (x ∷ xs) = cong (x ∷_) (aux xs)
