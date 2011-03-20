-- | A binary tree whose type garauntees that it is balanced.
--
-- The type of the tree captures the rules of the Red-black tree:
-- * Each node is considered either Red or Black.
-- * All the paths from the root to leafs contain the same number of Black nodes.
-- * A path from the root to a leaf cannot contain two consecutive Red nodes.
--
-- These rules assure that the longest path is no more than twice as longer than the shorter one,
-- because it can only add one Red node after each Black node.

{-# OPTIONS -Wall #-}
{-# LANGUAGE EmptyDataDecls, GADTs #-}

module RedBlackTree
    ( Tree
    , empty, insert
    , fromList, toList
    ) where

import Data.List (foldl')

-- Type definition
data Zero
data Succ n

-- We use trees whose root is Black. Simply for implementation convinience.
data Red
data Black
data Tree a where
    Tree :: Node Black n a -> Tree a
-- Node types are tagged by their subtree's Black-degree (number of Black nodes per path).
data Node t n a where
    -- A degree 0 Black node must be an empty tree.
    Nil :: Node Black Zero a
    BlackNode :: Node t0 n a -> a -> Node t1 n a -> Node Black (Succ n) a
    RedNode :: Node Black n a -> a -> Node Black n a -> Node Red n a

-- An isValid function is unnecessary.
-- It's implementation would be:
-- > isValid = const True

-- Show instance
instance Show a => Show (Tree a) where
    show (Tree tree) = show tree
instance Show a => Show (Node t n a) where
    show Nil = ""
    show (BlackNode left mid right) = showNode "B" left mid right
    show (RedNode left mid right) = showNode "R" left mid right

showNode :: (Show a, Show b, Show c) => String -> a -> b -> c -> String
showNode color left mid right =
    indentSide (' ', '|') (show left) ++
    color ++ ":" ++ show mid ++ "\n" ++
    indentSide ('|', ' ') (show right)

indentSide :: (Char, Char) -> String -> String
indentSide _ "" = ""
indentSide (leftIndent, rightIndent) side =
    unlines $ map (leftIndent:) left ++ ['+':mid] ++ map (rightIndent:) right
    where
        (left, mid:right) = break ((`notElem` " |+") . head) $ lines side

-- Functions
toList :: Tree a -> [a]
toList (Tree node) = nodeToList node

nodeToList :: Node t n a -> [a]
nodeToList Nil = []
nodeToList (BlackNode left x right) =
    nodeToList left ++ [x] ++ nodeToList right
nodeToList (RedNode left x right) =
    nodeToList left ++ [x] ++ nodeToList right

empty :: Tree a
empty = Tree Nil

fromList :: Ord a => [a] -> Tree a
fromList = foldl' (flip insert) empty

-- Insert
insert :: Ord a => a -> Tree a -> Tree a
insert x (Tree tree) =
    case nodeInsert x tree of
    ValidTree (RedNode left mid right) -> Tree $ BlackNode left mid right
    ValidTree node@(BlackNode _ _ _) -> Tree node
    ValidTree Nil -> Tree Nil  -- this shouldnt happen

-- An intermediate results of insert.
-- These may be invalid trees in that the root is Red and one of its children is also Red.
-- This is a intermediate result, which will be fixed after being propagated to the parent.
data InsertResult t n a where
    ValidTree :: Node t0 n a -> InsertResult t1 n a
    RRB :: Node Red n a -> a -> Node Black n a -> InsertResult Red n a
    BRR :: Node Black n a -> a -> Node Red n a -> InsertResult Red n a

revInsertResult :: Bool -> InsertResult t n a -> InsertResult t n a
revInsertResult False x = x
revInsertResult True (ValidTree x) = ValidTree x
revInsertResult True (RRB left mid right) = BRR right mid left
revInsertResult True (BRR left mid right) = RRB right mid left

nodeInsert :: Ord a => a -> Node t n a -> InsertResult t n a
nodeInsert x Nil = nodeInsertH False x Nil
nodeInsert x node@(BlackNode left mid right)
    | x < mid = nodeInsertH False x node
    | otherwise = nodeInsertH True x $ BlackNode right mid left
nodeInsert x node@(RedNode left mid right)
    | x < mid = nodeInsertH False x node
    | otherwise = nodeInsertH True x $ RedNode right mid left

nodeInsertH :: Ord a => Bool -> a -> Node t n a -> InsertResult t n a
nodeInsertH _ x Nil = ValidTree $ RedNode Nil x Nil
nodeInsertH isRev x (BlackNode left mid right) =
    case nodeInsert x left of
    insRes ->
        case revInsertResult isRev insRes of
        ValidTree newLeft -> ValidTree . revNode isRev $ BlackNode newLeft mid right
        RRB ll lm lr -> h right ll lm lr mid
        BRR ll lm lr ->
            case revNode isRev lr
            of RedNode lrl lrm lrr ->
                h right (revNode isRev (RedNode ll lm lrl)) lrm lrr mid
    where
        h :: Node t n a -> Node Red n a -> a -> Node Black n a -> a -> InsertResult Black (Succ n) a
        h r@(RedNode _ _ _) = hr (revNode isRev r)
        h r@(BlackNode _ _ _) = hb r
        h r@Nil = hb r
        hr :: Node Red n a -> Node Red n a -> a -> Node Black n a -> a -> InsertResult Black (Succ n) a
        hr (RedNode rl rm rr) ll lm lr m =
            ValidTree . revNode isRev $ RedNode
                (revNode isRev (BlackNode ll lm lr))
                m
                (revNode isRev (BlackNode rl rm rr))
        hb r ll lm lr m = ValidTree . revNode isRev $ BlackNode ll lm (revNode isRev (RedNode lr m r))
nodeInsertH isRev x (RedNode left mid right) =
    case nodeInsert x left of
        ValidTree newLeft@(RedNode _ _ _) -> revInsertResult isRev $ RRB newLeft mid right
        ValidTree newLeft@(BlackNode _ _ _) -> ValidTree . revNode isRev $ RedNode newLeft mid right
        ValidTree Nil -> ValidTree . revNode isRev $ RedNode Nil mid right

revNode :: Bool -> Node t n a -> Node t n a
revNode False x = x
revNode True Nil = Nil
revNode True (BlackNode left mid right) = BlackNode right mid left
revNode True (RedNode left mid right) = RedNode right mid left
