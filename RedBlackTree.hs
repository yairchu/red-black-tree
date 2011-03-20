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
    BlackNode :: NodeH t0 t1 n a -> Node Black (Succ n) a
    RedNode :: NodeH Black Black n a -> Node Red n a
data NodeH l r n a = NodeH (Node l n a) a (Node r n a)

-- An isValid function is unnecessary.
-- It's implementation would be:
-- > isValid = const True

-- Show instance
instance Show a => Show (Tree a) where
    show (Tree tree) = show tree
instance Show a => Show (Node t n a) where
    show Nil = ""
    show (BlackNode node) = showNode "B" node
    show (RedNode node) = showNode "R" node

showNode :: (Show a) => String -> NodeH l r n a -> String
showNode color (NodeH left mid right) =
    indentSide (' ', '|') (show left) ++
    color ++ ":" ++ show mid ++ "\n" ++
    indentSide ('|', ' ') (show right)
    where
        indentSide _ "" = ""
        indentSide (leftIndent, rightIndent) side =
            unlines $ map (leftIndent:) l ++ ['+':m] ++ map (rightIndent:) r
            where
                (l, m:r) = break ((`notElem` " |+") . head) $ lines side

-- Functions
toList :: Tree a -> [a]
toList (Tree node) =
    nodeToList node
    where
        nodeToList :: Node t n a -> [a]
        nodeToList Nil = []
        nodeToList (BlackNode x) = nodeToListH x
        nodeToList (RedNode x) = nodeToListH x
        nodeToListH (NodeH left x right) = nodeToList left ++ [x] ++ nodeToList right

empty :: Tree a
empty = Tree Nil

fromList :: Ord a => [a] -> Tree a
fromList = foldl' (flip insert) empty

-- Insert
insert :: Ord a => a -> Tree a -> Tree a
insert x (Tree tree) =
    case nodeInsert x tree of
    ValidTree (RedNode node) -> Tree (BlackNode node)
    ValidTree node@(BlackNode _) -> Tree node
    ValidTree Nil -> Tree Nil  -- this shouldnt happen

-- An intermediate results of insert.
-- These may be invalid trees in that the root is Red and one of its children is also Red.
-- This is a intermediate result, which will be fixed after being propagated to the parent.
data InsertResult t n a where
    ValidTree :: Node t0 n a -> InsertResult t1 n a
    Invalid0 :: NodeH Red Black n a -> InsertResult Red n a
    Invalid1 :: NodeH Black Red n a -> InsertResult Red n a

revInsertResult :: Bool -> InsertResult t n a -> InsertResult t n a
revInsertResult False x = x
revInsertResult True (ValidTree x) = ValidTree x
revInsertResult True (Invalid0 node) = Invalid1 $ revNodeH node
revInsertResult True (Invalid1 node) = Invalid0 $ revNodeH node

nodeInsert :: Ord a => a -> Node t n a -> InsertResult t n a
nodeInsert x node =
    nodeInsertH isRev x $ revNode isRev node
    where
        isRev :: Bool
        isRev =
            case node of
            Nil -> False
            (BlackNode (NodeH _ mid _)) -> x >= mid
            (RedNode (NodeH _ mid _)) -> x >= mid

nodeInsertH :: Ord a => Bool -> a -> Node t n a -> InsertResult t n a
nodeInsertH _ x Nil = ValidTree . RedNode $ NodeH Nil x Nil
nodeInsertH isRev x (BlackNode (NodeH left mid right)) =
    case nodeInsert x left of
    insRes ->
        case revInsertResult isRev insRes of
        ValidTree newLeft -> ValidTree . revNode isRev . BlackNode $ NodeH newLeft mid right
        Invalid0 node -> h node mid right
        Invalid1 (NodeH ll lm lr) ->
            case revNode isRev lr
            of RedNode (NodeH lrl lrm lrr) ->
                h (NodeH (revNode isRev . RedNode $ NodeH ll lm lrl) lrm lrr) mid right
    where
        h :: NodeH Red Black n a -> a -> Node t n a -> InsertResult Black (Succ n) a
        h l m r@(RedNode _) = hr l m (revNode isRev r)
        h l m r@(BlackNode _) = hb l m r
        h l m Nil = hb l m Nil
        hr :: NodeH Red Black n a -> a -> Node Red n a -> InsertResult Black (Succ n) a
        hr (NodeH ll lm lr) m (RedNode (NodeH rl rm rr))=
            ValidTree . revNode isRev . RedNode $ NodeH
                (revNode isRev . BlackNode $ NodeH ll lm lr)
                m
                (revNode isRev . BlackNode $ NodeH rl rm rr)
        hb (NodeH ll lm lr) m r = ValidTree . revNode isRev . BlackNode $ NodeH ll lm (revNode isRev . RedNode $ NodeH lr m r)
nodeInsertH isRev x (RedNode (NodeH left mid right)) =
    case nodeInsert x left of
        ValidTree newLeft@(RedNode _) -> revInsertResult isRev . Invalid0 $ NodeH newLeft mid right
        ValidTree newLeft@(BlackNode _) -> ValidTree . revNode isRev . RedNode $ NodeH newLeft mid right
        ValidTree Nil -> ValidTree . revNode isRev . RedNode $ NodeH Nil mid right

revNode :: Bool -> Node t n a -> Node t n a
revNode False x = x
revNode True Nil = Nil
revNode True (BlackNode node) = BlackNode $ revNodeH node
revNode True (RedNode node) = RedNode $ revNodeH node

revNodeH :: NodeH l r n a -> NodeH r l n a
revNodeH (NodeH left mid right) = NodeH right mid left
