# A Logical Relation for MLTT using Indexed Inductive Types #

This is a tweak on a project by Joakim Öhman (@mr-ohman), Andreas Abel (@andreasabel) and
Andrea Vezzosi (@Saizan).

The original project formalizes a logical relation for a variant Martin-Löf Type Theory
inside Agda, and uses it to obtain meta-theoretical properties such as normalization,
consistency and decidability of type-checking.

Here, I tried to reduce the gap between the strength of the theory being studied and the
meta-theory. Most notably, I removed the use of induction-recursion, a strong induction
principle, by replacing its uses with functional relations described by indexed inductive
types.

I did my best to implement these relations in a way that allows for maximal reuse
of the existing code. I removed the decidability of type-checking, as I think having
normalization, canonicity and consistency is enough to show that the idea works.

The theory under study has:
- Dependent products
- One predicative universe level (plus large types)
- Natural numbers with large elimination

The meta-theory needs:
- Dependent products
- Five predicative universe levels (plus large types)
- Indexed inductive types with large elimination.

Furthermore, I conjecture that
- The theory under study can be extended to support booleans, dependent sums, the inductive 
equality, and W-types.
- The use of indexed inductive types in the meta-theory should be reducible to 
boolean, dependent sums, the inductive equality, and W-types.
- The theory under study can be extended to support a hierarchy of n universes, at the
expense of n+4 levels in the meta-theory.

If these conjectures turn out to be true, then the gap in strength between the theory and 
the meta-theory is precisely measured by the number of additional universes. 
It would be interesting to see how low we can bring this gap (of course, Gödel's theorem 
tells us that it will always be non-zero).

### How can I be sure you did not cheat? ###

Agda features Induction-Recursion and a lot more universes than just 5, and as far as I can tell 
there is no way to disable these. So how do we know I haven't used these features in a
hidden way?

I am afraid there is no other way than going through the code. At the very least, I have
ported the definition of reducibility to Coq (which does not feature induction-recursion)
and it works fine. Porting the entirety of the development would be a lot of work, though!

### Dependencies ###

This project is written in Agda. It has been tested to be working with Agda version 2.6.2.
