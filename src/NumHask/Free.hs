{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- | What is a Free Algebra?
--
-- An algebra is a collection of operations which combine values to produce other
-- values. Algebra is a posh way of saying "construction kit". The type of values
-- an algebra combines and produces is called the carrier of the algebra. The
-- collection of operations and specification of their arities is called the
-- signature of the algebra. ~ pigworker [reddit comment](https://www.reddit.com/r/haskell/comments/36y9jc/haskell_as_an_mvc_framework/)
--
-- Adding a law to an algebra can be thought of as partitioning the carrier of
-- the algebra into equivalence classes induced by that law, and regarding each
-- class as one element. ~ [The Boom Heirarchy](http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=601FB55680BBC2C1A14D136657E4A7ED?doi=10.1.1.49.3252&rep=rep1&type=pdf)
--
-- -- Free object definition
--
-- Less well known is the dual to this statement: that the best way to avoid the violation of a ... is to make it unrepresentable.
--
-- - a Free Field is a bag o' bags
--
-- Adherence to the moral implications of a law, the haskell culture would shift from author reponsibility for ensuring laws are adhered to, to making laws explicit by their inclusion in smart constructors (algebras) of free objects. In this way, the violation of laws becoming unrepresentable.

{- Note that we are not cleanly following wikipedia:

A free algebra is the noncommutative analogue of a polynomial ring since its elements may be described as "polynomials" with non-commuting variables." ~ <https://en.wikipedia.org/wiki/Free_algebra>

(For the more general free algebras in universal algebra, see free object.)

Informally, a free object over a set A can be thought of as being a "generic" algebraic structure over A: the only equations that hold between elements of the free object are those that follow from the defining axioms of the algebraic structure. ~ <https://en.wikipedia.org/wiki/Free_object>

A free object over a set forgets everything about that set except some universal properties, specified by the word following free. For example, the free monoid over Integers forgets unique factorization, unique representation in every base, the GCD function, and everything else about the Integers except: they are a set of objects, there is an associative (binary) operation on Integers, and there is a "neutral" Integer; precisely the universal properties of monoids. ~ <https://www.schoolofhaskell.com/user/bss/magma-tree>

this functor “forgets” the monoidal structure — once we are inside a plain set, we no longer distinguish the unit element or care about multiplication — it’s called a forgetful functor. Forgetful functors come up regularly in category theory. ~ https://bartoszmilewski.com/2015/07/21/free-monoids/

TODO:

https://hackage.haskell.org/package/free-algebras-0.1.0.0/docs/Data-Algebra-Free.html

TODO:

free object is defined as being the left-hand side of an adjunction.

https://stackoverflow.com/questions/40704181/how-are-free-objects-constructed


-}

module NumHask.Free
  ( -- * a free algebra
    FreeAlgebra (..),

    -- * the initial objects
    Tree (..),
    toTreeL,
    toTreeR,
    Exp (..),
    parseExp,
    freeExp,

    -- * single law free algebras
    NoLaws,
    MagmaOnly,
    UnitalOnly,
    TreeU,
    AssociativeOnly,
    TreeA,
    CommutativeOnly,
    InvertibleOnly,
    IdempotentOnly,
    AbsorbingOnly,

    -- * multi-law free algebras
    FreeMonoid (..),
    MultMonoid,
    AddCommGroup,
    Bag (..),
    mapBag,
    RingLaws,
    FreeRing (..),

    -- * example helpers
    (⊕),
    Example (..),
    InformalTests,
    calate,
  )
where

import qualified Data.Attoparsec.Text as A
import qualified Data.Map as Map hiding (fromList)
import qualified Data.Text as Text
import qualified Data.Sequence as Seq
import GHC.Exts (IsList (..), coerce, toList)
import qualified GHC.Show
import NumHask.Algebra.Abstract.Group ()
import NumHask.Prelude hiding (lift, reduce, toList)

-- $setup
--
-- >>> :set -XOverloadedStrings
-- >>> :set -XOverloadedLists
-- >>> :set -XNoImplicitPrelude
-- >>> import NumHask.Prelude hiding (toList, reduce, pure)

-- | A free algebra is a construction kit of operations and axioms that combine to produce values of a type.
class FreeAlgebra initial free a | free -> initial where
  -- | Convert from a structure (the initial type) to another structure, the free object, forgetting the algebraic laws encapsulated in the free object definition.
  forget :: initial a -> free a

  -- | Create a free object from a carrier type singleton.
  lift :: a -> free a

  -- | The algebra of the free object.
  --
  -- > lift . algebra == id
  algebra :: free a -> a

  -- | Pretty print the free object.
  printf :: free a -> Text

-- | A binary tree is a common initial structure when considering free algebras.
--
-- The initial object for a Magma algebra is typically a tree-like structure representing a computation or expression; a series of binary operations, such as:
--
-- (1 ⊕ 4) ⊕ ((7 ⊕ 12) ⊕ 0)
--
-- >>> let m1 = Branch (Branch (Leaf (Example 1)) (Leaf (Example 4))) (Branch (Branch (Leaf (Example 7)) (Leaf (Example 12))) (Leaf (Example 0))) :: Tree MagmaOnly Example
-- >>> putStrLn $ printf m1
-- ((1⊕4)⊕((7⊕12)⊕0))
--
data Tree laws a
  = Leaf a
  | Branch (Tree laws a) (Tree laws a)
  deriving (Eq, Ord, Show, Functor)

-- | Starting from a particular initial structure, different sets of algerbraic laws may lead to the same actual structure. A phantom type is included in Tree and in other structures to help distinguish these cases.
data NoLaws

-- | Convenience function to construct a Tree from a list with left bracket groupings.
--
-- >>> toTreeL [1,4,7,12,0]
-- Branch (Branch (Branch (Branch (Leaf 1) (Leaf 4)) (Leaf 7)) (Leaf 12)) (Leaf 0)
toTreeL :: NonEmpty a -> Tree NoLaws a
toTreeL (x :| xs) = foldl (\s a -> Branch s (Leaf a)) (Leaf x) xs

-- | Construct a Tree from a list with a right bracket groupings.
--
-- >>> toTreeR [1,4,7,12,0]
-- Branch (Leaf 1) (Branch (Leaf 4) (Branch (Leaf 7) (Branch (Leaf 12) (Leaf 0))))
toTreeR :: NonEmpty a -> Tree NoLaws a
toTreeR l =
  let (x :| xs) = (fromList . reverse . toList $ l)
   in foldl (\s a -> Branch (Leaf a) s) (Leaf x) xs

-- * Individual Magma Laws

-- | example magma
(⊕) :: (Magma a) => a -> a -> a
(⊕) = magma

-- | example type
newtype Example = Example Int deriving (Eq, Ord, Associative, Commutative, Idempotent)

instance Magma Example where
  magma (Example a) (Example b) = Example $ a + b

instance Unital Example where
  unit = Example zero

instance Absorbing Example where
  absorb = Example zero

instance Invertible Example where
  inv (Example a) = Example (negate a)

instance Show Example where
  show (Example a) = show a

-- | Free Algebra for a Magma
--
-- > a ⊕ b is closed
--
-- Given an initial binary Tree structure ie
--
-- > data Tree a = Leaf a | Branch (Tree a) (Tree a)
--
-- , a closed binary operation (a magma) and no other laws, the free algebra is also a Tree.
--
-- >>> let init = toTreeL $ Example <$> [1,4,7,12,0] :: Tree NoLaws Example
-- >>> let free = forget init :: Tree MagmaOnly Example
-- >>> putStrLn $ printf $ free
-- ((((1⊕4)⊕7)⊕12)⊕0)
--
-- >>> algebra free
-- 24
data MagmaOnly

instance
  (Show a, Magma a) =>
  FreeAlgebra (Tree NoLaws) (Tree MagmaOnly) a
  where
  forget = coerce

  lift = Leaf

  algebra (Leaf a) = a
  algebra (Branch a b) = algebra a ⊕ algebra b

  printf (Leaf a) = show a
  printf (Branch a b) = mconcat ["(", printf a, "⊕", printf b, ")"]

-- | Free Unital
--
-- > unit ⊕ a = a
-- > a ⊕ unit = a
data UnitalOnly

-- | The introduction of unital laws to the algebra changes what the free structure is. From the point of view of algebra as an instruction kit for constructing an object, the unital laws suggest that, where an element is combined with the unit element, this operation should be ignored or forgotten.
--
-- Starting with two different initial objects, ((0 ⊕ 4) ⊕ 0) ⊕ 12 and 4 ⊕ 12 (say) are equivalent. The initial structure (a Tree) can be divided into equivalence classes where trees are isomorphic (the same).
--
-- Unlike the MagmaOnly case, the forgetting of unit operations means that an empty tree can result from an initially non-empty initial structure. The easiest way to do this is simply to graft an Empty tag to a Tree.
--
-- >>> let init = toTreeL $ Example <$> [0,1,4,0,7,12,0] :: Tree NoLaws Example
-- >>> putStrLn $ printf $ (forget init :: TreeU UnitalOnly Example)
-- (((1⊕4)⊕7)⊕12)
--
-- In other words, a free algebra makes violation of the algerbraic laws non-representable in the free structure.
--
-- An Empty represents a collapse of an initial structure down to nothing, as a result of applying the unital laws eg
--
-- >>> let init = toTreeL $ Example <$> [0,0,0] :: Tree NoLaws Example
-- >>> forget init :: TreeU UnitalOnly Example
-- Empty
data TreeU laws a = Empty | NonEmpty (Tree MagmaOnly a)
  deriving (Eq, Ord, Show, Functor)

instance
  (Eq a, Show a, Unital a) =>
  FreeAlgebra (Tree NoLaws) (TreeU UnitalOnly) a
  where
  forget (Leaf a) = lift a
  forget (Branch a b) = opU (forget a) (forget b)
    where
      opU Empty t = t
      opU t Empty = t
      opU (NonEmpty t) (NonEmpty t') = NonEmpty (Branch t t')

  lift a = bool (NonEmpty (Leaf a)) Empty (a == unit)

  algebra Empty = unit
  algebra (NonEmpty t) = algebra t

  printf Empty = show @a (unit @a)
  printf (NonEmpty t) = printf t

-- | Free Associative
--
-- > (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
data AssociativeOnly

-- | Introduction of an associative law induces an equivalence class where, for example, (1 ⊕ 2) ⊕ 3 and 1 ⊕ (2 ⊕ 3) should be represented in the same way.
--
-- The free object constructor thus needs to forget about the tree shape (the brackets).
--
-- As an algebra proceeds one element at a time, branches (or "links") still exist from one element to the next. The free object is still a tree structure, but it is the same tree shape.
--
-- Forcing one side of the branch to be a value provides a tree structure that branch to the other side. Choosing the left branch as the value is arbitrary.
--
-- >>> let exl = toTreeL $ Example <$> [1,4,7,12,0]
-- >>> putStrLn $ printf (forget exl :: Tree MagmaOnly Example)
-- ((((1⊕4)⊕7)⊕12)⊕0)
--
-- >>> let exr = toTreeR $ Example <$> [1,4,7,12,0]
-- >>> putStrLn $ printf (forget exr :: Tree MagmaOnly Example)
-- (1⊕(4⊕(7⊕(12⊕0))))
--
-- >>> putStrLn $ printf (forget exl :: TreeA AssociativeOnly Example)
-- 1⊕4⊕7⊕12⊕0
--
-- >>> (\x -> (forget $ toTreeL x :: TreeA AssociativeOnly Example) == (forget $ toTreeR $ x :: TreeA AssociativeOnly Example)) (Example <$> [1,4,7,12,0])
-- True
data TreeA laws a = LeafA a | BranchA a (TreeA laws a) deriving (Eq, Show, Functor)

instance (Show a, Associative a) => FreeAlgebra (Tree NoLaws) (TreeA AssociativeOnly) a where
  forget (Leaf a) = LeafA a
  forget (Branch (Leaf a) b) = BranchA a (forget b)
  forget (Branch a b) = opA (forget a) (forget b)
    where
      opA :: TreeA AssociativeOnly a -> TreeA AssociativeOnly a -> TreeA AssociativeOnly a
      opA (LeafA a) b = BranchA a b
      opA (BranchA a b) c = BranchA a (opA b c)

  lift = LeafA

  algebra (LeafA a) = a
  algebra (BranchA a b) = a ⊕ algebra b

  printf (LeafA a) = show a
  printf (BranchA a b) = show a <> "⊕" <> printf b

-- | Free Commutative
--
-- > a ⊕ b == b ⊕ a
--
-- but non-associative, so
-- > (a ⊕ b) ⊕ c == (b ⊕ a) ⊕ c
-- > (a ⊕ b) ⊕ c /= a ⊕ (b ⊕ c)
--
-- Commutation requires a ⊕ b and b ⊕ a to be represented the same, and this induces a preordering: *some* form of (arbitrary) ordering is needed to consistently represent a ⊕ b and b ⊕ a as ~ab~ (say).
--
-- In structural terms, a commutative tree is a mobile; a tree that has lost it's left and rightedness. To implement this forgetting, the left element of BranchC is arbitrarily chosen as always being less than or equal to the right element.
--
-- c1: 3 ⊕ (2 ⊕ 1)
-- c2: 3 ⊕ (1 ⊕ 2)
-- c3: (1 ⊕ 2) ⊕ 3
--
-- >>> let c1 = forget $ Branch (Leaf (Example 3)) (Branch (Leaf (Example 2)) (Leaf (Example 1))) :: Tree CommutativeOnly Example
-- >>> let c2 = forget $ Branch (Leaf (Example 3)) (Branch (Leaf (Example 1)) (Leaf (Example 2))) :: Tree CommutativeOnly Example
-- >>> let c3 = forget $ Branch (Branch (Leaf (Example 1)) (Leaf (Example 2))) (Leaf (Example 3)) :: Tree CommutativeOnly Example
--
-- >>> c1 == c2
-- True
--
-- >>> c1 == c3
-- True
data CommutativeOnly

instance (Show a, Ord a, Commutative a) => FreeAlgebra (Tree NoLaws) (Tree CommutativeOnly) a where
  forget (Leaf a) = Leaf a
  forget (Branch a b) = op (forget a) (forget b)
    where
      -- The commutative binary operation "forgets" the original ordering, thus losing the left/right information contained in the original Tree.
      op a b = bool (Branch b a) (Branch a b) (a < b)

  lift = Leaf

  algebra (Leaf a) = a
  algebra (Branch a b) = algebra a ⊕ algebra b

  printf (Leaf a) = show a
  printf (Branch a b) = "(" <> printf a <> "⊕" <> printf b <> ")"

-- | Free Invertible
--
-- > inv a ⊕ (a ⊕ b) == b -- left cancellation
-- > (a ⊕ b) ⊕ inv b == a -- right cancellation
--
-- but inv a ⊕ a is not a thing yet without a unit to equal to.
--
-- The cancellation (or reversal) of a value and the value are both lost in forming the equivalence relationship. Editing and diffing are two obvious examples.
--
-- The data structure for the equivalence class is unchanged, so Tree can be reused.
--
-- inv1: -1 ⊕ (1 ⊕ 5) == 5
-- inv2: (1 ⊕ 5) ⊕ -5 == 1
-- inv3: (1 ⊕ 5) ⊕ -1 == (1 ⊕ 5) ⊕ -1
--
-- >>> let inv1 = Branch (Leaf (Example (-1))) (Branch (Leaf (Example 1)) (Leaf (Example 5)))
-- >>> let inv2 = Branch (Branch (Leaf (Example 1)) (Leaf (Example 5))) (Leaf (Example (-5)))
-- >>> let inv3 = Branch (Branch (Leaf (Example 1)) (Leaf (Example 5))) (Leaf ((Example (-1))))
-- >>> forget inv1 :: Tree InvertibleOnly Example
-- Leaf 5
--
-- >>> putStrLn $ printf $ (forget inv3 :: Tree InvertibleOnly Example)
-- ((1⊕5)⊕-1)
data InvertibleOnly

instance (Show a, Eq a, Invertible a) => FreeAlgebra (Tree NoLaws) (Tree InvertibleOnly) a where
  forget (Leaf a) = Leaf a
  forget (Branch a b) = op (forget a) (forget b)
    where
      op a@(Branch la (Leaf ra)) b@(Branch (Leaf lb) rb) =
        bool (Branch a b) (op la rb) (ra == inv lb)
      op l@(Leaf la) b@(Branch (Leaf lb) bb) =
        bool (Branch l b) bb (la == inv lb)
      op b@(Branch bb (Leaf lb)) l@(Leaf la) =
        bool (Branch b l) bb (lb == inv la)
      op l r = Branch l r

  lift = Leaf

  algebra (Leaf a) = a
  algebra (Branch a b) = algebra a ⊕ algebra b

  printf (Leaf a) = show a
  printf (Branch a b) = "(" <> printf a <> "⊕" <> printf b <> ")"

-- | Free Idempotent
--
-- > a ⊕ a = a
--
-- Repeated elements are forgotten in the equivalence class object.
--
-- idem1: (5 ⊕ 5) ⊕ 1 == 5 ⊕ 1
-- idem2: (1 ⊕ 5) ⊕ (1 ⊕ 5) == (1 ⊕ 5)
--
-- but
--
-- idem3: (1 ⊕ 5) ⊕ 5 == (1 ⊕ 5) ⊕ 5
--
-- because we don't yet have associativity.
--
--
-- >>> let idem1 = Branch (Branch (Leaf (Example 5)) (Leaf (Example 5))) (Leaf (Example 1))
-- >>> let idem2 = Branch (Branch (Leaf (Example 1)) (Leaf (Example 5))) (Branch (Leaf (Example 1)) (Leaf  (Example 5)))
-- >>> let idem3 = Branch (Branch (Leaf (Example 1)) (Leaf (Example 5))) (Leaf (Example 5))
-- >>> putStrLn $ printf (forget idem1 :: Tree IdempotentOnly Example)
-- (5 o 1)
--
-- >>> putStrLn $ printf (forget idem2 :: Tree IdempotentOnly Example)
-- (1 o 5)
--
-- >>> putStrLn $ printf (forget idem3 :: Tree IdempotentOnly Example)
-- ((1 o 5) o 5)
--
-- >>> algebra (forget idem3 :: Tree IdempotentOnly Example)
-- 5
data IdempotentOnly

instance (Show a, Ord a) => FreeAlgebra (Tree NoLaws) (Tree IdempotentOnly) a where
  forget (Leaf a) = Leaf a
  forget (Branch a b) = op (forget a) (forget b)
    where
      op a b = bool (Branch a b) a (a == b)

  lift = Leaf

  algebra (Leaf a) = a
  algebra (Branch a b) = algebra a `max` algebra b

  printf (Leaf a) = show a
  printf (Branch a b) =
    "(" <> printf a <> " o " <> printf b <> ")"

-- | Free Absorbing
--
-- > e ⊕ a == e  left absorbing
-- > a ⊕ e == e  right absorbing
--
-- The absorbed element is forgotten.
--
-- ab1: 0 * (2 * 5) == 0
-- ab2: (2 * 5) * 0 == 0
--
-- >>> let ab1 = Branch (Leaf (Example 0)) (Branch (Leaf (Example 2)) (Leaf (Example 5)))
-- >>> let ab2 = Branch (Branch (Leaf (Example 2)) (Leaf (Example 5))) (Leaf (Example 0))
-- >>> forget ab1 :: Tree AbsorbingOnly Example
-- Leaf 0
--
-- >>> forget ab2 :: Tree AbsorbingOnly Example
-- Leaf 0
data AbsorbingOnly

instance
  (Show a, Eq a, Absorbing a) =>
  FreeAlgebra (Tree NoLaws) (Tree AbsorbingOnly) a
  where
  forget (Leaf a) = Leaf a
  forget (Branch (Leaf a) (Leaf b)) =
    bool
      (Branch (Leaf a) (Leaf b))
      (Leaf absorb)
      (a == absorb || b == absorb)
  forget (Branch (Leaf a) r) =
    bool (Branch (Leaf a) (forget r)) (Leaf absorb) (a == absorb)
  forget (Branch l (Leaf a)) =
    bool (Branch (forget l) (Leaf a)) (Leaf absorb) (a == absorb)
  forget (Branch a b) = op (forget a) (forget b)
    where
      op l@(Leaf a) r =
        bool (Branch l r) (Leaf absorb) (a == absorb)
      op l r@(Leaf a) =
        bool (Branch l r) (Leaf absorb) (a == absorb)
      op a b = Branch a b

  lift = Leaf

  algebra (Leaf a) = a
  algebra (Branch a b) = algebra a ⊕ algebra b

  printf (Leaf a) = show a
  printf (Branch a b) = "(" <> printf a <> "*" <> printf b <> ")"

{- | The free monoid is a list.

Applying these laws in the context of converting an expression tree into the simplest structure possible, involves:

 - forgetting whenever an element in the initial structure in the unit (one in the case of multiplication).
 - forgetting the brackets.

 Starting with the initial tree:

 > data Tree a = Leaf a | Branch (Tree a) (Tree a)

 We graft on a sum tag to represent an empty structure:

 > data Tree a = Empty | Leaf a | Branch (Tree a) (Tree a)

 To "forget" the left/right structure of the tree we force the left side of the branch to be a value rather than another tree branch, so that the whole tree always branches to the right:

 > data Tree a = Empty | Leaf a | Branch a (Tree a)

 Leaf a can be represented as Branch a Empty, so we can simplify this to:

 > data Tree a = Empty | Branch a (Tree a)

 And this is the classical Haskell cons list with different names:

 > data [] a = [] | a : [a]

-}
newtype FreeMonoid laws a = FreeMonoid {leaves :: [a]} deriving (Eq, Ord, Foldable, Show)

-- | Multiplicative monoid laws
--
-- > a * b is closed
-- > one * a = a
-- > a * one = a
-- > (a * b) * c = a * (b * c)
--
-- >>> one :: FreeMonoid MultMonoid Example
-- FreeMonoid {leaves = []}
--
--  ex1: (1 * 2) * (4 * 5) * 1
--
-- >>> let ex1 = Branch (Branch (Branch (Leaf 1) (Leaf 2)) (Branch (Leaf 4) (Leaf 5))) (Leaf 1)
--
-- >>> printf (forget ex1 :: FreeMonoid MultMonoid Int)
-- "(2*4*5)"
--
-- >>> algebra (forget ex1 :: FreeMonoid MultMonoid Int)
-- 40
data MultMonoid

instance Multiplicative (FreeMonoid MultMonoid a) where
  one = FreeMonoid []

  -- times shuffles the ones out of the expression tree
  (*) (FreeMonoid as) (FreeMonoid bs) = FreeMonoid $ rz as bs
    where
      -- quotienting (???)
      rz [] a = a
      rz a [] = a
      rz (x : xs) ys = x : rz xs ys

instance (Show a, Eq a, Multiplicative a) => FreeAlgebra (Tree NoLaws) (FreeMonoid MultMonoid) a where
  forget (Leaf a) = lift a
  forget (Branch a b) = forget a * forget b

  lift a = bool (FreeMonoid [a]) one (a == one)

  algebra = foldr (*) one

  printf (FreeMonoid []) = show @a one
  printf (FreeMonoid ls) = calate "*" (show <$> ls)


{- | The Free Commutative Monoid is a Bag.

In addition to the forget function for a monoid, forgetting the addition of zero and brackets, a commutative monad introduces commutation as a new law.

Commutation means representing a+b and b+a as the same ~ab~ say. To do this, the representation has to forget the ordering of expressions. A list that has lost it's order is sometimes referred to as a bag. An efficient representation of a bag is a (key,value) pair where the key is elements in the initial expression and value is the number of times the element has occurred.

In a paradox typical of adjoint functors, the forgetting of the ordering of the initial structure induces a requirement that the carrier type be ordered.

-}
newtype Bag laws a = Bag {unbag :: Map.Map a Int} deriving (Eq, Ord, Show)

-- | This is a functor from Ord -> Ord but, sadly, not a functor from Hask -> Hask
mapBag :: (Ord b) => (a -> b) -> Bag laws a -> Bag laws b
mapBag f (Bag m) = Bag $ Map.mapKeysWith (+) f m

-- toList . fromList /= id due to forgetfulness
-- but the interface is too ubiquitous to give up.
instance (Ord a, Subtractive a) => IsList (Bag AddCommGroup a) where
  type Item (Bag AddCommGroup a) = a

  toList (Bag m) =
    mconcat $
      ( \(k, v) ->
          bool
            (replicate v k)
            (replicate (negate v) (negate k))
            (v < zero)
      )
        <$> Map.toAscList m

  fromList l =
    Bag
      $ snd
      $ Map.partition (== zero)
      $ Map.fromListWith (+)
      $ (\e -> bool (e, 1) (negate e, -1) (e < zero)) <$> l

{- | Additive Commutative Group Laws

> a + b is closed
> zero + a = a
> a + zero = a
> (a + b) + c = a + (b + c)
> a + b == b + a
> a + negate a = zero

Adding invertibility to the list of laws for a commutative monoid gets us to the definition of a Commutative (or Abelian) Group.

Invertible (in combination with commutation) means forgetting a value when the inversion of the value is contained somwhere within the expression. For example, arnmed with a definition of what a negative number is, integer addition such as:

> 1+2+3+-1+-4+2

Can be represented as a bag of 2 2's, one 3 and minus one 4's.

>>> let exbag = fromList [1,2,3,-1,-4,-2] :: Bag AddCommGroup Int
>>> exbag
Bag {unbag = fromList [(3,1),(4,-1)]}

>>> toList exbag
[3,-4]

>>> exAdd = toTreeL [0,1,2,3,0,-1,-4,-2,0]
>>> putStrLn $ printf (forget exAdd :: Bag AddCommGroup Int)
(3+-4)

-}
data AddCommGroup

instance (Ord a) => Additive (Bag AddCommGroup a) where
  zero = Bag Map.empty

  (+) (Bag a) (Bag b) =
    Bag
      $ snd
      $ Map.partition (== zero)
      $ Map.unionWith (+) a b

instance (Ord a) => Subtractive (Bag AddCommGroup a) where
  negate (Bag m) = Bag $ Map.map negate m

instance (Show a, Eq a, Ord a, Subtractive a) => FreeAlgebra (Tree NoLaws) (Bag AddCommGroup) a where
  forget (Leaf a) = lift a
  forget (Branch a b) = forget a + forget b

  lift a
    | a == zero = zero
    | a < zero = Bag (Map.singleton (negate a) (-1))
    | otherwise = Bag $ Map.singleton a 1

  algebra (Bag m) =
    Map.foldrWithKey
      ( \k v acc ->
          foldr ($) acc (replicate v (k +))
      )
      zero
      m

  printf b =
    bool
      (calate "+" (show <$> toList b))
      (show @a zero)
      (b == zero)

{- | Ring Laws

Addition
> a + b is closed
> zero + a = a
> a + zero = a
> (a + b) + c = a + (b + c)
> a + b == b + a
> a + negate a = zero

Multiplication
> a * b is closed
> one * a = a
> a * one = a
> (a * b) * c = a * (b * c)

Absorption
> a * zero = zero
> zero * a = zero

Distributive
> a * (b + c) = (a * b) + (a * c)
> (b + c) * a = (b * a) + (c * a)

-}
data RingLaws

{- | Where an algebra involves two (or more) operators, the initial structure (the expression) is arrived at by grafting new types of branches using sum types.

-}
data Exp a
  = Value a
  | Add (Exp a) (Exp a)
  | Mult (Exp a) (Exp a)
  deriving (Eq, Ord, Show, Functor)

instance (Show a, Eq a, Ring a, Magma a) => FreeAlgebra Exp Exp a where
  forget = id

  lift = Value

  algebra (Value a) = a
  algebra (Add a b) = algebra a + algebra b
  algebra (Mult a b) = algebra a * algebra b

  printf (Value a) = show a
  printf (Mult a b) = "(" <> printf a <> "*" <> printf b <> ")"
  printf (Add a b) = "(" <> printf a <> "+" <> printf b <> ")"

{- | The Free Ring is a recursive sequence of bags.

Given multiplication is monoidal (with the free object a list) and addition is a commutative group (with the free object a bag), it seems intuitively the case that the free object for a ring is a recursive list of bags. It is recursive because the ordering of +'s and *'s does not reduce, so that the tree-like nature of the expression is not forgotten.

Abstractly, the choice of what goes in what should be an arbitrary one; the free object could also be a (recursive) bag of lists. The addition collection structure feels like it should be within the multiplication structure, however, because of the distribution law equivalence that need to be honoured in the representation:

> a ⋅ (b + c) = (a · b) + (a · c)
> (b + c) · a = (b · a) + (c · a)

It is likely, in most endevours, that multiplication is more expensive than addition, and the left hand side of these equations have less multiplications.

The free ring is the same general shape as the free monad in the [free](https://hackage.haskell.org/package/free-5.1.4/docs/Control-Monad-Free.html) library

> data Free f a = Pure a | Free (f (Free f a))

which in turn is almost the same shape as Fix eg

> newtype Fix f = Fix (f (Fix f))

If Bag could form a Functor instance, then the Free Ring could be expressed as:

> data FreeRing a = Free (Compose Bag Seq) a

In a similar vein, a Free Field would be a recursive bag of bags, or

> data FreeField a = Free (Compose Bag Bag) a

which is a very clean result.

-}
data FreeRing laws a
  = FreeV a
  | FreeR [Bag AddCommGroup (FreeRing laws a)]
  deriving (Eq, Ord, Show)

data FreeRing' laws a
  = FreeV' a
  | FreeR' (Seq (Bag AddCommGroup (FreeRing laws a)))
  deriving (Eq, Ord, Show)

-- | Parse an Exp, convert to a free structure and print.
freeExp :: Text -> Text
freeExp t = printf (forget (parseExp t) :: FreeRing RingLaws Int)

-- | informal test suite
--
-- empty expression
--
-- >>> freeExp "0"
-- "0"
--
-- plain (with multiplicative precedence)
--
-- >>> forget $ parseExp "1+2*3" :: FreeRing RingLaws Int
-- FreeR [Bag {unbag = fromList [(FreeV 1,1),(FreeR [Bag {unbag = fromList [(FreeV 2,1)]},Bag {unbag = fromList [(FreeV 3,1)]}],1)]}]
--
-- >>> freeExp "1+2*3"
-- "(1+(2*3))"
--
-- Additive unital
--
-- >>> freeExp "0+(2+0)*3+0"
-- "(2*3)"
--
-- General additive associative and commutation
--
-- >>> freeExp "(1+2)*3+(4+5)+6*7"
-- "(4+5+((1+2)*3)+(6*7))"
--
-- Multiplicative unital
--
-- >>> freeExp "1*3+4*1+1*(5*6)"
-- "(3+4+(5*6))"
--
-- Multiplicative association (not commutative)
--
-- >>> freeExp "(2*6)*((4*5)*2)"
-- "(2*6*4*5*2)"
--
-- absorbative
--
-- >>> freeExp "0*1+3*(3+4)*0"
-- "0"
--
-- additive invertible
--
-- >>> freeExp "(1+2)+(-1+-2)"
-- "0"
--
-- distribution
--
-- > a ⋅ (b + c) = (a · b) + (a · c)
-- > (b + c) · a = (b · a) + (c · a)
--
-- left
--
-- >>> freeExp "2*(3+4)+2*5+2*6"
-- "(2*(3+4+5+6))"
--
-- right
--
-- >>> freeExp "(3+4)*2+5*2+6*2"
-- "((3+4+5+6)*2)"
--
-- mixed (left then right checks)
--
-- > freeExp "2*(3+4)*2+5*2+2*6*2"
-- "((5+(2*(3+4))+(2*6))*2)"
--
-- TODO: "(2*(3+4+6)*2+5*2)" is a valid alternative?
--
-- TODO: optional extras:
--
-- If +one is faster than +a
--
-- > (a . b) + a ==> a . (b + one)
--
-- If a is scalar ...
--
-- upcasing a bag
--
-- > 3+3+3+3 ==> 3*4
--
-- exp
--
-- > 3*3*3*3 ==> 3^4
data InformalTests

-- | Single bag a value
bagV :: (Ord a, Subtractive a) => a -> Bag AddCommGroup (FreeRing RingLaws a)
bagV a
  | a == zero = zero
  | a < zero = Bag (Map.singleton (FreeV $ negate a) (-1))
  | otherwise = Bag $ Map.singleton (FreeV a) 1

-- | Single bag a FreeRing
bagR :: (Ord a) => FreeRing RingLaws a -> Bag AddCommGroup (FreeRing RingLaws a)
bagR a
  | a == FreeR [] = zero
  | otherwise = Bag $ Map.singleton a 1

instance (Eq a, Ord a, Subtractive a, Multiplicative a) => Multiplicative (FreeRing RingLaws a) where
  one = FreeV one

  -- absorption law
  (*) _ (FreeR []) = FreeR []
  (*) (FreeR []) _ = FreeR []
  -- multiplicative unital
  (*) (FreeV vl) (FreeV vr)
    | vl == one = FreeV vr
    | vr == one = FreeV vl
    | otherwise = FreeR [bagV vl, bagV vr]
  -- multiplicative unital
  (*) (FreeV v) (FreeR bs) =
    FreeR $ bool [bagV v] [] (v == one) <> bs
  (*) (FreeR bs) (FreeV v) =
    FreeR $ bs <> bool [bagV v] [] (v == one)
  (*) (FreeR as) (FreeR bs) = FreeR $ as <> bs

instance forall (a :: Type). (Ord a, Ring a) => Additive (FreeRing RingLaws a) where
  zero = FreeR []

  -- additive unital guards
  (+) (FreeR []) a = a
  (+) a (FreeR []) = a
  -- invertible check
  (+) (FreeV vl) (FreeV vr) =
    bool
      (FreeR $ (: []) $ bagV vl + bagV vr)
      (FreeR [])
      (vl == negate vr)
  -- add another additive element to a (single-element list) bag
  (+) (FreeV v) (FreeR [b]) = FreeR $ (: []) $ bagV v + b
  (+) (FreeR [b]) (FreeV v) = FreeR $ (: []) $ bagV v + b
  -- multiplication expression being added to so
  -- create a new addition branch
  (+) (FreeV v) (FreeR bs) =
    FreeR $ (: []) $
      bagV v + bagR (FreeR bs)
  (+) (FreeR bs) (FreeV v) =
    FreeR $ (: []) $
      bagV v + bagR (FreeR bs)
  (+) (FreeR [a]) (FreeR [b]) =
    FreeR $ (: []) $ a + b
  (+) as (FreeR [b]) =
    FreeR $ (: []) $ bagR as + b
  (+) (FreeR [a]) bs =
    FreeR $ (: []) $ bagR bs + a
  -- distributive
  -- > (a · as') + (a · bs') ==> a ⋅ (as' + bs')
  -- > (ras' . ra) + (rbs' . ra) ==> (ras' + rbs') . ra
  (+) f@(FreeR as@(a : as')) f'@(FreeR bs@(b : bs')) =
    bool
      ( bool
          (FreeR $ (: []) $ bagR f + bagR f')
          ( (FreeR (reverse ras') + FreeR (reverse rbs'))
              * FreeR [ra]
          )
          (ra == rb)
      )
      (FreeR [a] * (FreeR as' + FreeR bs'))
      (a == b)
    where
      (ra : ras') = reverse as
      (rb : rbs') = reverse bs

instance (Show a, Ord a, Ring a) => Subtractive (FreeRing RingLaws a) where
  negate (FreeV a) = FreeV (negate a)
  negate (FreeR []) = FreeR []
  -- no multiply, negate everything in the bag
  negate (FreeR ((Bag m) : xs)) = FreeR $ [Bag $ Map.map negate m] <> xs

instance (Show a, Eq a, Ord a, Ring a) => FreeAlgebra Exp (FreeRing RingLaws) a where
  forget (Value a) = lift a
  forget (Add a b) = forget a + forget b
  forget (Mult a b) = forget a * forget b

  lift a = bool (FreeV a) (FreeR []) (a == zero)

  algebra (FreeV a) = a
  algebra (FreeR []) = zero
  algebra (FreeR xs) = foldr (*) one (algebra . algebra <$> xs)

  printf (FreeV v) = show v
  printf (FreeR []) = show @a (zero @a)
  printf (FreeR bs) = calate "*" (printBagFreeR <$> bs)
    where
      printBagFreeR b =
        bool
          (calate "+" (printf <$> toList b))
          (show @a zero)
          (b == zero)

-- expression parsing helpers
data BadExpParse = BadExpParse deriving (Show)

instance Exception BadExpParse

-- | Parser adds implicit parens
--
-- > let t1 = "(4*(1+3)+(3+1)+6*(4+5*(11+6)*(3+2)))+(7+3+11*2)"
-- > printf . parseExp $ t1
-- "((((4*(1+3))+(3+1))+(6*(4+((5*(11+6))*(3+2)))))+((7+3)+(11*2)))"
parseExp :: Text -> Exp Int
parseExp t = either (throw BadExpParse) id $ A.parseOnly expr t

-- | Exp parser
-- > second printf $ A.parseOnly expr " ((1 + 3) + (4 + 5)) * (7 + 3 + 11 * 2)x"
-- Right "(((1+3)+(4+5))*((7+3)+(11*2)))"
expr :: A.Parser (Exp Int)
expr = branch term add

factor :: A.Parser (Exp Int)
factor = val <|> paren expr

term :: A.Parser (Exp Int)
term = branch factor mult

-- signed integer
--
-- > A.parse val " 5 "
-- Done " " (Value 5)
val :: A.Parser (Exp Int)
val = A.skipSpace *> (Value <$> A.signed A.decimal)

add :: A.Parser (Exp a -> Exp a -> Exp a)
add = (A.skipSpace *> A.char '+') $> Add <* A.skipSpace

mult :: A.Parser (Exp a -> Exp a -> Exp a)
mult = (A.skipSpace *> A.char '*') $> Mult <* A.skipSpace

paren :: A.Parser a -> A.Parser a
paren p = do
  _ <- A.skipSpace
  _ <- A.char '('
  _ <- A.skipSpace
  r <- p
  _ <- A.skipSpace
  _ <- A.char ')'
  pure r <|> p

branch :: A.Parser a -> A.Parser (a -> a -> a) -> A.Parser a
branch p op = do
  a <- p
  more a
  where
    more a' = (more =<< (($) <$> op <*> pure a' <*> p)) <|> pure a'

-- | intercalate elements of an expression with an operator, and put brackets around this.
calate :: Text -> [Text] -> Text
calate _ [] = mempty
calate _ [x] = x
calate op xs = "(" <> Text.intercalate op xs <> ")"
