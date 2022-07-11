# The Topological Ontology project

This repository contains the Lean prover source code for the Topological Ontology,
a system of formal philosophy based on topological spaces, meant to serve as a foundation for metaphysics and other
related topics. 

One of the major contributions of the project so far has been to formalize a new theory of the distinction between substances and accidents and use it to analyze cosmological arguments for the existence of God in the Lean theorem prover. A paper will soon be published detailing our investigations, but the source code was made to be readable independently of the paper. For understanding the cosmological arguments we recommend reading in the following order:

[ontology.lean](src/ontology.lean) → [prime.lean](/src/prime.lean) → [substances.lean](/src/substances.lean) → 
[causality.lean](src/metaphysics/causality.lean) → [god.lean](src/theology/natural/god.lean) → [proofs.lean](src/theology/natural/proofs.lean)

There are parts of the project that are incomplete or a work in progress, but the aforementioned files currently have no unfinished proofs, and do not depend on any other file containing unfinished proofs.

If you have any suggestions or comments, feel free to use our Discussions section. We may generally accept pull requests proposing modifications of the source code which do not break or remove definitions and theorems, but for more involved philosophical additions, please start a discussion first.

If you want to suggest an aspect of philosophy to be formalized next, or propose that some philosophical theory you formalized be integrated into our project, start a discussion.

We notice that we are currently using Lean community version 3.8.0. We plan on updating to the latest version in the future, and eventually porting our project to Lean 4.