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
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- | __A 'Control.Monad.Free.Free' 'Num' is a 'Seq'uence of 'Bag's.__
--
-- One of the many things that sparks joy in Haskell is the density of expression that can be achieved. If it wasn't for a few quirks of the language, and if 'Ring' is substituted for 'Num', a free ring could be concretely defined as 'Control.Monad.Free.Free' ('Data.Functor.Compose.Compose' 'Bag' 'Seq') a.
--
-- As it stands, the library associates a free algebra with a forgetful functor representing what could be thought of as a robust set of polymorphic fusion rules. There are a lot of things that are number-like computations, and some of them need to go very fast and be very clean.
--
-- I had often heard about a free monoid and had always wondered what else, other than the iconic Haskell list, is a free thing. This library is a rough map of what has been a somewhat shambolic exploration of this notion. I hope you enjoy browsing the haddocks as much as I enjoyed crafting them. Before diving into the module proper,  there is a few landmarks worth noting:
--
-- - What, exactly, is a 'Num'?
--
-- - What is an algebra?
--
-- - The forgotten price that must be paid for an object to be free.
--
-- - The magic in category theory.
--
-- == What is a 'Num'?
--
-- /Can you truthfully say that you treasure something buried so deeply in a closet or drawer that you have forgotten its existence? If things had feelings, they would certainly not be happy. Free them from the prison to which you have relegated them. Help them leave that deserted isle to which you have exiled them./ ~ Marie Kondo
--
-- 'GHC.Num' is a dusty, old corner of our Haskell shelf-space. As is usually the case, the exact definition of what a 'Num' is is only ever a @λ> :i@ away.
--
-- >>> :i Num
-- type Num :: * -> Constraint
-- class Num a where
--   (GHC.Num.+) :: a -> a -> a
--   (GHC.Num.-) :: a -> a -> a
--   (GHC.Num.*) :: a -> a -> a
--   GHC.Num.negate :: a -> a
--   GHC.Num.abs :: a -> a
--   signum :: a -> a
--   GHC.Num.fromInteger :: Integer -> a
-- ...
--
-- So 'Num' is a Haskell class with an interface unchanged since it's specification in the [haskell98](https://www.haskell.org/onlinereport/standard-prelude.html) standard.
--
-- The other, obvious answer to the question is that a 'Num' is a number; it says so in the name, after all. But, by convention, a Haskell class is more than just the polymorphic type (the a) and the operators (the class interface). By convention, a Haskell class is also a set of laws that the class is expected to adhere to.
--
-- The commentary added since haskell98 mentions the mathematical concept of a ring but there are a few warts:
--
-- - 'zero' and 'one' are not included in the interface, but defined via 'fromInteger', a [special](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/rebindable_syntax.html) function baked into the Haskell language.
--
-- - abs and signum are not properties of a [ring](https://en.wikipedia.org/wiki/Ring_(mathematics\)), but of metric analytic branches of math.
--
-- The end result is that any notion of a free object applied to a 'Num' is difficult to imagine. If the interface is cleaned up, however, as in 'Ring' from the [numhask](https://hackage.haskell.org/package/numhask) library, with attention paid to each and every law, then resolution improves, and we are able to sharpen our tools.
--
-- A better definition of what our number systems are can lead to cleaner, faster coding patterns and design. In turn, this might eventually lead to ubiquitous usage of Haskell in numerical computing. As it stands right now, Haskell usage is restricted to only the most stubborn and dreamy of the numeric-analyst crew to which I claim membership of.
--
-- This article-module is, in part, a plea to release the Haskell numerical classes from their existing dusty drawers so we can begin to imagine some sort of future of numerical computation within the halls proper of Haskell. With apologies to Marie Kondo (and unsupported strikeout):
--
-- The __prelude__ (space) within which we __code__ (live) should be for the __language__ (person) we are becoming now, not for the __language__ (person) we were in the past.
--
-- and
--
-- Imagine what it would be like to have a __prelude__ (bookshelf) filled only with __functions__ (books) that you really love. Isn’t that image spellbinding? For someone who loves __functions__ (books), what greater happiness could there be?
--
-- == What is an algebra?
--
-- /Art is fire plus algebra./ ~ Jorge Luis Borges
--
-- or, less succinctly,
--
-- /An algebra is a collection of operations which combine values to produce other values. Algebra is a posh way of saying "construction kit". The type of values an algebra combines and produces is called the carrier of the algebra. The collection of operations and specification of their arities is called the signature of the algebra./ ~ [pigworker reddit comment](https://www.reddit.com/r/haskell/comments/36y9jc/haskell_as_an_mvc_framework/)
--
-- A free algebra then, is a set of instructions for creating a free object from some initial structure or expression. 'FreeAlgebra' can be thought of as a class for busting up a computation into two parts:
--
-- - 'forget': a function that transforms a structure into a Free Object representing an ideal given the (abstract) laws of the algebra being defined, and
--
-- - 'algebra': a (concrete) algebra from the Free Object to the carrier type (the type being produced).
--
-- == The price of a free object is forgetting.
--
-- /Maybe if I forgot things once in a while, we'd all be a little bit happier./ ~ Jay Asher, Thirteen Reasons Why
--
-- A free object is [neither](https://en.wikipedia.org/wiki/Gratis_versus_libre) "free as in beer" nor "free as in speech". It is free as in absent the algebraic laws that refer to how the object is constructed. At the heart of what is the free object, the @free@ part of the @FreeAlgebra initial free@ type, is a forgetting that throws away the structural details of the very laws the free object defines.
--
-- /A free object over a set forgets everything about that set except some universal properties, specified by the word following free. For example, the free monoid over Integers forgets unique factorization, unique representation in every base, the GCD function, and everything else about the Integers except: they are a set of objects, there is an associative (binary) operation on Integers, and there is a "neutral" Integer; precisely the universal properties of monoids./ ~ <https://www.schoolofhaskell.com/user/bss/magma-tree>
--
-- /... informally, a free object over a set A can be thought of as being a "generic" algebraic structure over A: the only equations that hold between elements of the free object are those that follow from the defining axioms of the algebraic structure./ ~ <https://en.wikipedia.org/wiki/Free_object>
--
-- /Adding a law to an algebra can be thought of as partitioning the carrier of the algebra into equivalence classes induced by that law, and regarding each class as one element./ ~ [The Boom Hierarchy](http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=601FB55680BBC2C1A14D136657E4A7ED?doi=10.1.1.49.3252&rep=rep1&type=pdf)
--
-- As is becoming well known, the easiest way to ensure that laws are never violated is by making their transgression non-representable. 'FreeAlgebra' represents a  technique for achieving this necessary step in constructing a free object from an initial representation.
--
-- == The magic in category theory
--
-- /Essentially everything that makes category theory nontrivial and interesting ... can be derived from the concept of adjoint functors./ ~ nLabs
--
-- What makes the above statement so interesting is when you combine it with their definition of adjunction (the noun to the "adjoint" adverb):
--
-- /adjunction : free functor ⊣ forgetful functor/ ~ [nLabs](https://ncatlab.org/nlab/show/free-forgetful+adjunction)
--
-- That's it! That's as far as they are prepared to discuss things, cascading definitions notwithstanding.
--
-- There's something very 17th century medicine about 21st century category theory. "An overabundance of the yellow humours can be fixed by an application of leeches" is how I hear much category theoretic prescription. We simply don't yet know enough about applied category theory for it to be distinguishable from magic.
--
-- Which leaves room for amateurs such as myself to do some hack-and-slash exploring. I can take a leap and see adjunctiveness (or is it adjointanality?) as yet another metaphor for this deep dual nature of programming. That is, for every way of considering a problem, you can "flip the switch" and think about it in an opposite, orthogonal, adjacent or flippin' arrow perspective or context.
--
-- With respect to a 'FreeAlgebra', the flipped switch is this:
--
-- __To arrive at a Free Object (where the only thing that is left are the laws under consideration), you need to forget the very laws encapsulated in the free structure and remember everything else.__
--
-- /this functor “forgets” the monoidal structure — once we are inside a plain set, we no longer distinguish the unit element or care about multiplication — it’s called a forgetful functor./ ~ https://bartoszmilewski.com/2015/07/21/free-monoids/
--
-- Future breakthroughs will not be found in quantum theory, mired in the 20th century slide-rules of physics.  They will not be gained by applying bio-logic-al constructs to computers with convoluted neural nets and tautological machine learnings. They will certainly never occur within a context of computer science as linguistic endeavour. The future can be seen now, however opaquely and paradoxical, and will be shaped by the binary oppositions and sheer post-modernist confusions of category theory.
--
module NumHask.FreeAlgebra
  ( -- * a free algebra class
    FreeAlgebra (..),

    -- * initial objects
    NoLaws,
    Tree (..),
    toTreeL,
    toTreeR,
    Exp (..),
    parseExp,
    freeExp,

    -- * single law free algebras
    MagmaOnly,
    UnitalOnly,
    TreeU (..),
    AssociativeOnly,
    TreeA (..),
    CommutativeOnly,
    InvertibleOnly,
    IdempotentOnly,
    AbsorbingOnly,

    -- * multi-law free algebras
    FreeMonoid (..),
    MultMonoid,
    Bag (..),
    mapBag,
    AddCommGroup,
    RingLaws,
    FreeRing (..),

    -- * example helpers
    Example (..),
    InformalTests,
    calate,
    action,

    -- * module tree
    freeExpM,
    parseExpM,
    exprM,
    termM,
    factorM,
    addM,
    multM,
    actionM,
  )
where

import qualified Data.Attoparsec.Text as A
import qualified Data.Map as Map hiding (fromList)
import qualified Data.Sequence as Seq
import Data.Sequence ((<|), Seq (..), (|>))
import qualified Data.Text as Text
import Data.Text (Text, pack)
import GHC.Exts (IsList (..), coerce, toList)
import NumHask.Algebra.Group ()
import NumHask.Prelude hiding (reduce, toList, putStrLn)
import Control.Exception
import Data.List.NonEmpty (NonEmpty (..))
import Data.Functor
import Control.Applicative

-- $setup
--
-- >>> :set -XOverloadedStrings
-- >>> :set -XOverloadedLists
-- >>> :set -XNoImplicitPrelude
-- >>> import NumHask.Prelude hiding (toList, reduce, pure, putStrLn)
-- >>> import Data.Text.IO (putStrLn)
-- >>> import Data.List.NonEmpty (toList)

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

-- | Starting from a particular initial structure, different sets of laws may lead to the same actual structure (or free object). Informal phantom type are included in most structures to help distinguish these cases and supply differing instances.
data NoLaws

-- | A binary tree is a common initial structure when considering free algebras.
--
-- The initial object for a Magma algebra is typically a tree-like structure representing a computation or expression; a series of binary operations, such as:
--
-- > (1 ⊕ 4) ⊕ ((7 ⊕ 12) ⊕ 0)
--
-- >>> let m1 = Branch (Branch (Leaf (Example 1)) (Leaf (Example 4))) (Branch (Branch (Leaf (Example 7)) (Leaf (Example 12))) (Leaf (Example 0))) :: Tree MagmaOnly Example
-- >>> putStrLn $ printf m1
-- ((1⊕4)⊕((7⊕12)⊕0))
data Tree laws a
  = Leaf a
  | Branch (Tree laws a) (Tree laws a)
  deriving (Eq, Ord, Show, Functor)

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

-- | example type
newtype Example = Example Int deriving (Eq, Ord, Associative, Commutative, Idempotent)

instance Magma Example where
  (Example a) ⊕ (Example b) = Example $ a + b

instance Unital Example where
  unit = Example zero

instance Additive Example where
   (+) = (⊕)
   zero = unit

instance Subtractive Example where
   negate = inv

instance Multiplicative Example where
   (*) (Example a) (Example b) = Example (a * b)
   one  = Example one

instance Absorbing Example where
  absorb = Example zero

instance Distributive Example

instance Invertible Example where
  inv (Example a) = Example (negate a)

instance Show Example where
  show (Example a) = show a

-- | Free Algebra for a Magma
--
-- > a ⊕ b is closed
--
-- Given an initial binary Tree structure:
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

  printf (Leaf a) = (pack . show) a
  printf (Branch a b) = mconcat ["(", printf a, "⊕", printf b, ")"]

-- |
--
-- > unit ⊕ a = a
-- > a ⊕ unit = a
data UnitalOnly

-- | The introduction of unital laws to the algebra changes what the free structure is, compared to the 'MagmaOnly' case. From this library's point of view, that an algebra is an instruction kit for constructing an object, the unital laws are an instruction to substitute "a" for whenever "unit ⊕ a" occurs. Where an element is combined with the unit element, this operation should be erased and forgotten.
--
-- For example, from the point of view of the free algebra, ((0 ⊕ 4) ⊕ 0) ⊕ 12 and 4 ⊕ 12 (say) are the same. The initial structure can be divided into equivalence classes where trees are isomorphic (the same).
--
-- In contrast to the MagmaOnly case, the forgetting of unit operations means that an empty tree can result from an initially non-empty initial structure. The easiest way to represent this potential free object is simply to graft an EmptyTree tag to a Tree with a sum type.
--
-- An EmptyTree represents a collapse of an initial structure down to nothing, as a result of applying the unital laws eg
--
-- >>> let init = toTreeL $ Example <$> [0,0,0] :: Tree NoLaws Example
-- >>> forget init :: TreeU UnitalOnly Example
-- EmptyTree
--
-- __/By forgetting instances of the unital laws in the original expression, the unital laws cannot be violated in the free object because they no longer exist./__
--
-- >>> let init = toTreeL $ Example <$> [0,1,4,0,7,12,0] :: Tree NoLaws Example
-- >>> putStrLn $ printf $ (forget init :: TreeU UnitalOnly Example)
-- (((1⊕4)⊕7)⊕12)
data TreeU laws a = EmptyTree | NonEmptyTree (Tree MagmaOnly a)
  deriving (Eq, Ord, Show, Functor)

instance
  (Eq a, Show a, Unital a) =>
  FreeAlgebra (Tree NoLaws) (TreeU UnitalOnly) a
  where
  forget (Leaf a) = lift a
  forget (Branch a b) = opU (forget a) (forget b)
    where
      opU EmptyTree t = t
      opU t EmptyTree = t
      opU (NonEmptyTree t) (NonEmptyTree t') = NonEmptyTree (Branch t t')

  lift a = bool (NonEmptyTree (Leaf a)) EmptyTree (a == unit)

  algebra EmptyTree = unit
  algebra (NonEmptyTree t) = algebra t

  printf EmptyTree = pack $ show @a (unit @a)
  printf (NonEmptyTree t) = printf t

-- |
--
-- > (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
data AssociativeOnly

-- | Introduction of an associative law induces an equivalence class where, for example, (1 ⊕ 2) ⊕ 3 and 1 ⊕ (2 ⊕ 3) should be represented in the same way.
--
-- 'forget', the free object constructor, thus needs to forget about the tree shape (the brackets or parentheses of the original expression).
--
-- As an algebra consumes an expression one element at a time, branches (or "links") still exist from one element to the next. The free object is still a tree structure, but it is the same tree shape.
--
-- Forcing one side of the branch to be a value provides a tree structure that branches to the other side. The left branch as the value has been chosen in this representation but this is arbitrary.
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

  printf (LeafA a) = (pack . show) a
  printf (BranchA a b) = (pack . show) a <> "⊕" <> printf b

-- |
--
-- > a ⊕ b == b ⊕ a
--
-- but non-associative, so
--
-- > (a ⊕ b) ⊕ c == (b ⊕ a) ⊕ c
--
-- but
--
-- > (a ⊕ b) ⊕ c /= a ⊕ (b ⊕ c)
--
-- Commutation requires a ⊕ b and b ⊕ a to be represented the same, and this induces a preordering: __/some/__ form of (arbitrary) ordering is needed to consistently and naturally represent a ⊕ b and b ⊕ a as "ab".
--
-- In structural terms, a commutative tree is a mobile; a tree that has lost it's left and rightedness. To implement this forgetting, the left element of BranchC is arbitrarily chosen as always being less than or equal to the right element.
--
-- c1: 3 ⊕ (2 ⊕ 1)
--
-- c2: 3 ⊕ (1 ⊕ 2)
--
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

  printf (Leaf a) = pack $ show a
  printf (Branch a b) = "(" <> printf a <> "⊕" <> printf b <> ")"

-- |
--
-- > inv a ⊕ (a ⊕ b) == b -- left cancellation
-- > (a ⊕ b) ⊕ inv b == a -- right cancellation
--
-- but
--
-- > inv a ⊕ a == unit
-- is not a thing yet without a unit to equal to.
--
-- The cancellation (or reversal or negation) of a value and the value are both lost in forming the equivalence relationship. Editing and diffing are two obvious examples.
--
-- The data structure for the equivalence class is unchanged, so Tree can be reused.
--
-- inv1: -1 ⊕ (1 ⊕ 5) == 5
--
-- inv2: (1 ⊕ 5) ⊕ -5 == 1
--
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

  printf (Leaf a) = pack $ show a
  printf (Branch a b) = "(" <> printf a <> "⊕" <> printf b <> ")"

-- |
--
-- > a ⊕ a = a
--
-- Immediately repeated elements are forgotten in the equivalence class object.
--
-- idem1: (5 ⊕ 5) ⊕ 1 == 5 ⊕ 1
--
-- idem2: (1 ⊕ 5) ⊕ (1 ⊕ 5) == (1 ⊕ 5)
--
-- but
--
-- idem3: (1 ⊕ 5) ⊕ 5 == (1 ⊕ 5) ⊕ 5
--
-- because we don't yet have associativity.
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

  printf (Leaf a) = pack $ show a
  printf (Branch a b) =
    "(" <> printf a <> " o " <> printf b <> ")"

-- |
--
-- > e ⊕ a == e  left absorbing
-- > a ⊕ e == e  right absorbing
--
-- The absorbed element is forgotten.
--
-- ab1: 0 * (2 * 5) == 0
--
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

  printf (Leaf a) = pack $ show a
  printf (Branch a b) = "(" <> printf a <> "*" <> printf b <> ")"

-- | The free monoid is a list.
--
-- Applying unital and associativity laws in the context of converting an expression tree into a free monoid, the simplest structure possible, involves:
--
-- - forgetting whenever an element in the initial structure in the unit (one, say, in the case of multiplication).
-- - forgetting the brackets.
--
-- So, starting with the initial tree:
--
-- > data Tree a = Leaf a | Branch (Tree a) (Tree a)
--
-- We graft on a sum tag to represent an empty structure:
--
-- > data Tree a = EmptyTree | Leaf a | Branch (Tree a) (Tree a)
--
-- To 'forget' the left/right structure of the tree we force the left side of the branch to be a value rather than another tree branch, so that the whole tree always branches to the right:
--
-- > data Tree a = EmptyTree | Leaf a | Branch a (Tree a)
--
-- Leaf a can be represented as Branch a EmptyTree, so we can simplify this to:
--
-- > data Tree a = EmptyTree | Branch a (Tree a)
--
-- And this is the classical Haskell cons list with different names:
--
-- > data [] a = [] | a : [a]
newtype FreeMonoid laws a = FreeMonoid {leaves :: [a]} deriving (Eq, Ord, Foldable, Show)

-- | Multiplicative monoid laws
--
-- > a * b is closed
-- > one * a = a
-- > a * one = a
-- > (a * b) * c = a * (b * c)
--
-- >>> one :: FreeMonoid MultMonoid Int
-- FreeMonoid {leaves = []}
--
--  ex1: (1 * 2) * (4 * 5) * 1
--
-- >>> let ex1 = Branch (Branch (Branch (Leaf 1) (Leaf 2)) (Branch (Leaf 4) (Leaf 5))) (Leaf 1)
--
-- >>> putStrLn $ printf (forget ex1 :: FreeMonoid MultMonoid Int)
-- (2*4*5)
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

  printf (FreeMonoid []) = pack $ show @a one
  printf (FreeMonoid ls) = calate "*" ((pack . show) <$> ls)

-- | The Free commutative monoid is a Bag.
--
-- In addition to the forgetting needed for the free monoid, forgetting additions of zero and forgetting brackets, a commutative law means forgetting the order of the original expression structure.
--
-- A list that has lost it's order is sometimes referred to as a bag. An efficient representation of a bag is a (key,value) pair where the keys are elements in the initial expression and values are the number of times the element has occurred.
--
-- In the usual surface-paradox typical of adjointness, the forgetting of the ordering of the initial structure induces a requirement that the carrier type be ordered.
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

-- | Additive Commutative Group Laws
--
-- > a + b is closed
-- > zero + a = a
-- > a + zero = a
-- > (a + b) + c = a + (b + c)
-- > a + b == b + a
-- > a + negate a = zero
--
-- Adding invertibility to the list of laws for a commutative monoid gets us to the definition of a Commutative (or Abelian) Group.
--
-- Invertible (in combination with commutation) means forgetting a value when the inversion of the value is contained somewhere within the expression. For example, armed with a definition of what a negative number is, integer addition such as:
--
-- > 1+2+3+-1+-4+2
--
-- Can be represented as a bag of 2 2's, one 3 and minus one 4's.
--
-- >>> let exbag = fromList [1,2,3,-1,-4,-2] :: Bag AddCommGroup Int
-- >>> exbag
-- Bag {unbag = fromList [(3,1),(4,-1)]}
--
-- >>> exAdd = toTreeL [0,1,2,3,0,-1,-4,-2,0]
-- >>> putStrLn $ printf (forget exAdd :: Bag AddCommGroup Int)
-- (3+-4)
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
      (calate "+" ((pack . show) <$> toList b))
      (pack $ show @a zero)
      (b == zero)

-- | Ring Laws
--
-- > a + b is closed
-- > zero + a = a
-- > a + zero = a
-- > (a + b) + c = a + (b + c)
-- > a + b == b + a
-- > a + negate a = zero
-- > a * b is closed
-- > one * a = a
-- > a * one = a
-- > (a * b) * c = a * (b * c)
-- > a * zero = zero
-- > zero * a = zero
-- > a * (b + c) = (a * b) + (a * c)
-- > (b + c) * a = (b * a) + (c * a)
data RingLaws

-- | Where an algebra involves two (or more) operators, the initial structure (the expression) is arrived at by grafting new types of branches using sum types.
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

  printf (Value a) = pack $ show a
  printf (Mult a b) = "(" <> printf a <> "*" <> printf b <> ")"
  printf (Add a b) = "(" <> printf a <> "+" <> printf b <> ")"

-- | The free ring is a recursive sequence of bags.
--
-- Given multiplication is monoidal (with the free object a list) and addition is a commutative group (with the free object a bag), it seems intuitively the case that the free object for a ring is a recursive list of bags. It is recursive because the ordering of +'s and *'s does not reduce, so that the tree-like nature of the expression is not forgotten.
--
-- Abstractly, the choice of what goes in what should be an arbitrary one; the free object could also be a (recursive) bag of lists. The addition collection structure feels like it should be within the multiplication structure, however, because of the distribution law equivalence that need to be honoured in the representation:
--
-- > a ⋅ (b + c) = (a · b) + (a · c)
-- > (b + c) · a = (b · a) + (c · a)
--
-- It is likely, in most endeavours, that multiplication is more expensive than addition, and the left hand side of these equations have less multiplications.
--
-- Because the distribution laws are substitutions to both the left and the right, use of 'Seq' is indicated instead of a list (which is isomorphic to a list and thus allowed as an alternative).
--
-- The free ring is the same general shape as the free monad in the [free](https://hackage.haskell.org/package/free-5.1.4/docs/Control-Monad-Free.html) library
--
-- > data Free f a = Pure a | Free (f (Free f a))
--
-- which in turn is almost the same shape as Fix eg
--
-- > newtype Fix f = Fix (f (Fix f))
--
-- If Bag could form a Functor instance, then the Free Ring could be expressed as @'Control.Monad.Free.Free' ('Data.Functor.Compose.Compose' 'Bag' 'Seq') a@
--
-- which is a very clean result.
data FreeRing laws a
  = FreeV a
  | FreeR (Seq (Bag AddCommGroup (FreeRing laws a)))
  deriving (Eq, Ord, Show)

-- | Parse an Exp, forget to the free object structure and print.
--
-- >>> let t1 = "(4*(1+3)+(3+1)+6*(4+5*(11+6)*(3+2)))+(7+3+11*2)"
-- >>> putStrLn $ freeExp t1
-- (1+3+3+7+(4*(1+3))+(6*(4+(5*(6+11)*(2+3))))+(11*2))
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
-- FreeR (fromList [Bag {unbag = fromList [(FreeV 1,1),(FreeR (fromList [Bag {unbag = fromList [(FreeV 2,1)]},Bag {unbag = fromList [(FreeV 3,1)]}]),1)]}])
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
-- absorptive
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
-- >>> freeExp "2*(3+4)*2+5*2+2*6*2"
-- "((5+(2*(3+4))+(2*6))*2)"
--
-- Note that @(2*(3+4+6)*2+5*2)@ is a valid alternative to what the current 'FreeRing' 'forget' function comes up with.
--
-- == TODO: optional extras:
--
-- - If +one is faster than +a
--
-- > (a . b) + a ==> a . (b + one)
--
-- - If a is scalar ...
--
-- lifting an (additive bag) to a multiplication sequence
--
-- > 3+3+3+3 ==> 3*4
--
-- - introducing exponents
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
  | a == FreeR Empty = zero
  | otherwise = Bag $ Map.singleton a 1

instance (Eq a, Ord a, Subtractive a, Multiplicative a) => Multiplicative (FreeRing RingLaws a) where
  one = FreeV one

  -- absorption law
  (*) _ (FreeR Empty) = FreeR Empty
  (*) (FreeR Empty) _ = FreeR Empty
  -- multiplicative unital
  (*) (FreeV vl) (FreeV vr)
    | vl == one = FreeV vr
    | vr == one = FreeV vl
    | otherwise = FreeR (bagV vl <| bagV vr <| Empty)
  -- multiplicative unital
  (*) (FreeV v) (FreeR bs) =
    FreeR $ bool (bagV v <|) id (v == one) bs
  (*) (FreeR bs) (FreeV v) =
    FreeR $ bool (|> bagV v) id (v == one) bs
  (*) (FreeR as) (FreeR bs) = FreeR $ as <> bs

instance forall (a :: Type). (Ord a, Ring a) => Additive (FreeRing RingLaws a) where
  zero = FreeR Empty

  -- additive unital guards
  (+) (FreeR Empty) a = a
  (+) a (FreeR Empty) = a
  -- invertible check
  (+) (FreeV vl) (FreeV vr) =
    bool
      (FreeR $ Seq.singleton $ bagV vl + bagV vr)
      (FreeR Empty)
      (vl == negate vr)
  -- add another additive element to a (single-element list) bag
  (+) (FreeV v) (FreeR (b :<| Empty)) = FreeR $ Seq.singleton $ bagV v + b
  (+) (FreeR (b :<| Empty)) (FreeV v) = FreeR $ Seq.singleton $ bagV v + b
  -- multiplication expression being added to so
  -- create a new addition branch
  (+) (FreeV v) (FreeR bs) =
    FreeR $ Seq.singleton $
      bagV v + bagR (FreeR bs)
  (+) (FreeR bs) (FreeV v) =
    FreeR $ Seq.singleton $
      bagV v + bagR (FreeR bs)
  (+) (FreeR (a :<| Empty)) (FreeR (b :<| Empty)) =
    FreeR $ Seq.singleton $ a + b
  (+) as (FreeR (b :<| Empty)) =
    FreeR $ Seq.singleton $ bagR as + b
  (+) (FreeR (a :<| Empty)) bs =
    FreeR $ Seq.singleton $ bagR bs + a
  -- distributive
  -- > (a · as') + (a · bs') ==> a ⋅ (as' + bs')
  -- > (ras' . ra) + (rbs' . ra) ==> (ras' + rbs') . ra
  -- left-biased checking
  (+) f@(FreeR ((al :<| as') :|> ar)) f'@(FreeR ((bl :<| bs') :|> br))
    | al == bl = FreeR (Seq.singleton al) * (FreeR (as' :|> ar) + FreeR (bs' :|> br))
    | ar == br = (FreeR (al :<| as') + FreeR (bl :<| bs')) * FreeR (Seq.singleton ar)
    | otherwise =
      FreeR $ Seq.singleton $ bagR f + bagR f'
  (+) a b = FreeR $ Seq.singleton $ bagR a + bagR b

instance (Show a, Ord a, Ring a) => Subtractive (FreeRing RingLaws a) where
  negate (FreeV a) = FreeV (negate a)
  negate (FreeR Empty) = FreeR Empty
  -- no multiply, negate everything in the bag
  negate (FreeR ((Bag m) :<| xs)) =
    FreeR $ Seq.singleton (Bag $ Map.map negate m) <> xs

instance (Show a, Eq a, Ord a, Ring a) => FreeAlgebra Exp (FreeRing RingLaws) a where
  forget (Value a) = lift a
  forget (Add a b) = forget a + forget b
  forget (Mult a b) = forget a * forget b

  lift a = bool (FreeV a) (FreeR Empty) (a == zero)

  algebra (FreeV a) = a
  algebra (FreeR Empty) = zero
  algebra (FreeR xs) = foldr (*) one (algebra . algebra <$> xs)

  printf (FreeV v) = pack $ show v
  printf (FreeR Empty) = pack $ show @a (zero @a)
  printf (FreeR bs) = calate "*" (toList $ printBagFreeR <$> bs)
    where
      printBagFreeR b =
        bool
          (calate "+" (printf <$> toList b))
          (pack $ show @a zero)
          (b == zero)

-- expression parsing helpers
data BadExpParse = BadExpParse deriving (Show)

instance Exception BadExpParse

-- | Text parser for an expression. Parenthesis is imputed assuming multiplicative precedence and left-to-right default association.
--
-- > let t1 = "(4*(1+3)+(3+1)+6*(4+5*(11+6)*(3+2)))+(7+3+11*2)"
-- > putStrLn . printf . parseExp $ t1
-- ((((4*(1+3))+(3+1))+(6*(4+((5*(11+6))*(3+2)))))+((7+3)+(11*2)))
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

action :: A.Parser (Exp a -> Exp a -> Exp a)
action = (A.skipSpace *> A.char '*') $> Mult <* A.skipSpace

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

-- | Module expression
data ExpM a
  = ValueM a
  | ActionM a (ExpM a)
  | AddM (ExpM a) (ExpM a)
  | MultM (ExpM a) (ExpM a)
  deriving (Eq, Ord, Show, Functor)

instance (Show a, Eq a, Ring a, Magma a) => FreeAlgebra ExpM ExpM a where
  forget = id

  lift = ValueM

  algebra (ValueM a) = a
  algebra (ActionM a  b) = a * algebra b
  algebra (AddM a b) = algebra a + algebra b
  algebra (MultM a b) = algebra a * algebra b

  printf (ValueM a) = (pack . show) a
  printf (ActionM a b) = "(" <> (pack . show) a <> ".*" <> printf b <> ")"
  printf (MultM a b) = "(" <> printf a <> "*" <> printf b <> ")"
  printf (AddM a b) = "(" <> printf a <> "+" <> printf b <> ")"

instance Magma Int where
  

freeExpM :: Text -> Text
freeExpM t = printf (forget (fmap Example (parseExpM t)) :: ExpM Example)

-- expression parsing helpers
data BadExpMParse = BadExpMParse deriving (Show)

instance Exception BadExpMParse

-- | Text parser for an expression. Parenthesis is imputed assuming multiplicative precedence and left-to-right default association.
--
-- > let t1 = "(4.*(1+3)+(3+1)+6*(4+5*(11+6).*(3+2)))+(7+3+11*2)"
-- > putStrLn . printf . parseExp $ t1
-- ((((4*(1+3))+(3+1))+(6*(4+((5*(11+6))*(3+2)))))+((7+3)+(11*2)))
parseExpM :: Text -> ExpM Int
parseExpM t = either (throw BadExpParse) id $ A.parseOnly exprM t

-- | Exp parser
-- > second printf $ A.parseOnly expr " ((1 + 3) + (4 + 5)) * (7 + 3 + 11 * 2)x"
-- Right "(((1+3)+(4+5))*((7+3)+(11*2)))"
exprM :: A.Parser (ExpM Int)
exprM = branch termM addM

factorM :: A.Parser (ExpM Int)
factorM = valM <|> paren exprM

termM :: A.Parser (ExpM Int)
termM = branch factorM multM

-- signed integer
--
-- > A.parse val " 5 "
-- Done " " (Value 5)
valM :: A.Parser (ExpM Int)
valM = A.skipSpace *> (ValueM <$> A.signed A.decimal)

addM :: A.Parser (ExpM a -> ExpM a -> ExpM a)
addM = (A.skipSpace *> A.char '+') $> AddM <* A.skipSpace

multM :: A.Parser (ExpM a -> ExpM a -> ExpM a)
multM = (A.skipSpace *> A.char '*') $> MultM <* A.skipSpace

actionM :: A.Parser (a -> ExpM a -> ExpM a)
actionM = (A.skipSpace *> A.string ".*") $> ActionM <* A.skipSpace

