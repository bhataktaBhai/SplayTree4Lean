# SplayTree4Lean
Implementation of splay trees in Lean 4

The splay tree, developed by Sleator and Tarjan, is a balanced binary search
tree algorithm conjectured to be dynamically optimal.
This repository contains a library for splay trees in Lean 4.

## Plans
- Define the `splayTree` (as an inductive type)
- Provide functionality to build a `splayTree` from a `list`
- Allow insertion, deletion, and lookups
- Prove correctness of all above operations

## Ambitions
- Implement a computation monad to keep track of the number of "steps"
  (e.g. rotations and splays) used by each aforementioned operation
- Prove total access time bound of $O((m + n) log n + m)$ for a sequence of $m$
  access operations on a `splayTree` of size $n$ (without insertions or deletions)
