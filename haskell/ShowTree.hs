-- | An ASCII art show function for binary trees.

module ShowTree where

import Data.List

data Tree a = Leaf | Node (Tree a) a (Tree a)

data WidthTree a = Leaf | Node (Tree a) a (Tree a)

showTree :: Int -> Tree a -> String
showTree pre (Leaf) = (replicate pre ' ') ++ "x"
showTree pre (Node l x r) = intercalate "\n" (map (replicate pre ' ' ++) ["x", " / \\ ", (showTree pre l ++ "   " ++ showTree pre r)])

instance Show a => Show (Tree a) where
  show = showTree 0
