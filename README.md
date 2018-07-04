# Synquid Improvement

We are trying to figure out ways to optimize the performance of enumeration in Synquid.

We have tried:

- Extend the <code>succinct type system</code> to support datatypes and refinement measures
- Build finite <code>succinct type</code> graph for polymorphic types
- Search expressions by traversal in the weighted, directed graph with heuristic ranking function
- Wisely keep search state after branch abduction

We will try:

- Add symmetric reduction
