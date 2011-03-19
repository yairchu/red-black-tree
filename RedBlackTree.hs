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
    BlackNode :: RBNode n a -> a -> RBNode n a -> Node Black (Succ n) a
    RedNode :: Node Black n a -> a -> Node Black n a -> Node Red n a
data RBNode n a
    = ItsRed (Node Red n a)
    | ItsBlack (Node Black n a)

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
instance Show a => Show (RBNode n a) where
    show (ItsRed tree) = show tree
    show (ItsBlack tree) = show tree

showNode :: (Show a, Show b) => String -> a -> b -> a -> String
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
    rbNodeToList left ++ [x] ++ rbNodeToList right
nodeToList (RedNode left x right) =
    nodeToList left ++ [x] ++ nodeToList right

rbNodeToList :: RBNode n a -> [a]
rbNodeToList (ItsRed node) = nodeToList node
rbNodeToList (ItsBlack node) = nodeToList node

empty :: Tree a
empty = Tree Nil

fromList :: Ord a => [a] -> Tree a
fromList = foldl' (flip insert) empty

-- Insert
insert :: Ord a => a -> Tree a -> Tree a
insert x (Tree tree) =
    case nodeInsert x tree of
    ValidTree (ItsBlack newTree) -> Tree newTree
    ValidTree (ItsRed (RedNode left mid right)) -> Tree $ BlackNode (ItsBlack left) mid (ItsBlack right)

-- An intermediate results of insert.
-- These may be invalid trees in that the root is Red and one of its children is also Red.
-- This is a intermediate result, which will be fixed after being propagated to the parent.
data InsertResult t n a where
    ValidTree :: RBNode n a -> InsertResult t n a
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
nodeInsertH _ x Nil = ValidTree . ItsRed $ RedNode Nil x Nil
nodeInsertH isRev x (BlackNode left mid right) =
    case rbInsert x left of
    insRes ->
        case revInsertResult isRev insRes of
        ValidTree newLeft -> ValidTree . ItsBlack $ makeNode isRev BlackNode newLeft mid right
        RRB ll lm lr -> rrb ll lm lr mid right
        BRR ll lm lr ->
            case revNode isRev lr
            of RedNode lrl lrm lrr ->
                rrb (makeNode isRev RedNode ll lm lrl) lrm lrr mid right
    where
        rrb :: Node Red n a -> a -> Node Black n a -> a -> RBNode n a -> InsertResult Black (Succ n) a
        rrb ll lm lr m (ItsRed r) =
            case revNode isRev r of
            RedNode rl rm rr ->
                ValidTree . ItsRed $ makeNode isRev RedNode
                    (makeNode isRev BlackNode (ItsRed ll) lm (ItsBlack lr))
                    m
                    (makeNode isRev BlackNode (ItsBlack rl) rm (ItsBlack rr))
        rrb ll lm lr m (ItsBlack r) =
            ValidTree . ItsBlack $ makeNode isRev BlackNode
                (ItsRed ll)
                lm
                (ItsRed (makeNode isRev RedNode lr m r))
nodeInsertH isRev x (RedNode left mid right) =
    case nodeInsert x left of
        ValidTree (ItsBlack newLeft) -> ValidTree . ItsRed $ makeNode isRev RedNode newLeft mid right
        ValidTree (ItsRed newLeft) -> revInsertResult isRev $ RRB newLeft mid right

makeNode :: Bool -> (a -> b -> a -> c) -> a -> b -> a -> c
makeNode False func left mid right = func left mid right
makeNode True func left mid right = func right mid left

revNode :: Bool -> Node t n a -> Node t n a
revNode False x = x
revNode True Nil = Nil
revNode True (BlackNode left mid right) = BlackNode right mid left
revNode True (RedNode left mid right) = RedNode right mid left

rbInsert :: Ord a => a -> RBNode n a -> InsertResult Red n a
rbInsert x (ItsBlack node) =
    case nodeInsert x node of
    ValidTree r -> ValidTree r
rbInsert x (ItsRed node) = nodeInsert x node
