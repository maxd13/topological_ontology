<style>
    body{
        text-align: justify
    }
</style>

# Ontological Spaces

## Abstract

We provide a common topological foundation for the development of philosophical formal ontologies and, develop our own philosophical ontology, greatly inspired by Aristotle's Categories and E. J. Lowe's Four category ontology. We finish by discussing some applications, such as defining God in our ontological model.

- [Ontological Spaces](#ontological-spaces)
  - [Abstract](#abstract)
  - [Introduction](#introduction)
  - [Nothingness and *Impossibilia*.](#nothingness-and-impossibilia)
  - [Individuals and multiplicity.](#individuals-and-multiplicity)
  - [Intension and Extension.](#intension-and-extension)
    - [First and Second intentions.](#first-and-second-intentions)
  - [Order and perfection.](#order-and-perfection)
  - [Algebraic realisms.](#algebraic-realisms)
  - [The Topological nature of Reality.](#the-topological-nature-of-reality)
    - [Order-Theoretic arguments.](#order-theoretic-arguments)
      - [Parsimony](#parsimony)
      - [Explanatory power](#explanatory-power)
    - [Topological arguments.](#topological-arguments)
      - [Parsimony](#parsimony-1)
      - [Explanatory power](#explanatory-power-1)
    - [The argument from logic.](#the-argument-from-logic)
  - [Examples of ontologies.](#examples-of-ontologies)
  - [The use of Alexandroff spaces.](#the-use-of-alexandroff-spaces)
  - [Substances and accidents.](#substances-and-accidents)
  - [Universals and positive properties.](#universals-and-positive-properties)
  - [Intrinsic and extrinsic accidents.](#intrinsic-and-extrinsic-accidents)
  - [Defining God in topology.](#defining-god-in-topology)
  - [Conclusion.](#conclusion)

## Introduction

Topology is the study of geometric shapes equivalent up to a continuous deformation, such as stretching, twisting, crumpling and bending, but not tearing or gluing <!--[1](citation)-->. For instance any potato is topologically the same (*homeomorphic*) as a sphere. A topologist is a mathematician who cannot distinguish his donut from his coffee mug, as the saying goes: they both have a single hole.

<!-- Horrible paragraph! Refactor. -->
Topology has generalized much of geometry and analysis, this being the initial motivation of the field. It is however its capacity to generalize a good deal of logic and order theory, foundational mathematical disciplines for philosophy, which interests us the most. In fact Category Theory, a foundational discipline capable of massive generalizations and great philosophical applicability, grew out of algebraic topology and is currently used as an alternative foundation for mathematics than set theory.

Ontology is the study of being as such, and the fundamental a priori structure of reality. The connection between the two is very much indirect, as it follows from the more easilly seen connection between ontology and order theory, and the fact that any order theoretic structure is deep down just a kind of topological space, called an *Alexandroff space*.

This connection is given by the fact that the entities which ontology discusses are naturally ordered by a relation of *existential entailment*. Any ontological theory must admit that there is such a relation between possible entities $x$ and $y$ such that whenever $x$ exists $y$ must also necessarilly exist, even if different ontological theories might differ as to the nature of this relation, or about which entities in fact entail which other entities. As such, we can already associate to any possible ontological theory a kind of mathematical structure which we have taken to call a **formal ontology** or just **ontology**. This structure will give us a reasonable mathematical model to work with ontology.

Ontology studies “what there is” but also “what there could be”, and so the ontological structure will consist of a collection of possible entities which one postulates to be at least possible to exist, like unicorns; these entities can also be called by different names like, *individuals, things, objects,* etc… and also, if one is feeling particularly Augustinian: *goods*. The possible entities of the ontology will also have intrinsic and necessary interrelations and connections between them, the most fundamental one of which being that of existential entailment. Again, we will say that an entity $x$ **existentially entails** an entity $y$, and denote it by $x \to y$, if whenever $x$ exists, $y$ must also necessarily exist. The relation $\to$ is in fact a **preorder relation**, meaning it satisfies:

- For all $x, x \to x$.					**(Reflexivity)**
- For all $x, y, z,$ if $x \to y$ and $y \to z,$ then $x \to z.$		                            **(Transitivity)**

If the collection of all possible entities is taken to be a *set*, then a structure of this sort, consisting of a set equipped with a preorder relation, already exists in mathematics and is called simply a **preordered set**. For the sake of mathematical simplicity we will assume, without noticeable loss of generality, that the collection of objects is a set, rather than a *proper class*. Beyond simplicity, we could say that any cardinality based argument that could be proposed against the idea of there being a set of all possible entities must run against the fact that any language can only describe a countable number of different entities, and that at any rate the cardinality of continuum already appears to be more than enough to account for all quantitative aspects of reality that could be thought, except for the existence of abstract sets of arbitrarily high order. Later on we will argue that distinctions between high order sets can be taken to be distinctions of reason rather than distinctions in reality, as all of these sets could be ontologically founded upon a given set of objects.

Any preorder relation naturally induces two other relations. In our case, we could call one of them **existential equivalence** $\leftrightarrow$ and the other called **order of being** ≤, which are defined in the following manner:
- $x \leftrightarrow y \iff x \to y \ \land \ y \to x.$
- $[x] \le [y] \iff x \to y.$

The axioms read:

- For all $x$ and $y$, $x$ is existentially equivalent to $y$ *if and only if* $x$ existentially entails $y$ and $y$ existentially entails $x$.
- The equivalence class of $x$ is lesser in being than the equivalence class of $y$ *if and only if* $x$ existentially entails $y$.

As the name suggests, it can be proven from its definition that existential equivalence $\leftrightarrow$ is an **equivalence relation**, meaning that besides satisfying transitivity and reflexivity it also satisfies **symmetry**:

- For all $x, y,$ if $x \leftrightarrow y$ then $y \leftrightarrow x.$

Furthermore, the order of being is an order in the sense that it is a **partial order**, i.e. it is a preorder which also satisfies **anti-symmetry**:

- For all $x, y,$ if $x \le y$ and $y \le x$ then $x = y$.

The **equivalence class** of a given entity $x$ will be the set of all entities existentially equivalent to $x$. The order ≤ is defined only for equivalence classes, and we can also define the **meet** and the **join** of such equivalence classes as we can for any partial order. 

## Nothingness and *Impossibilia*.

**TODO:** Explain why it is ok to add a 0.

## Individuals and multiplicity.

## Intension and Extension.

### First and Second intentions.

## Order and perfection.
## Algebraic realisms.
## The Topological nature of Reality.

<!-- Talking points:
- What is a topological space?
- The world-entity duality as a special case of the space-quantity duality. -->


### Order-Theoretic arguments.
#### Parsimony
#### Explanatory power

### Topological arguments.
#### Parsimony
#### Explanatory power

### The argument from logic.

We can consider the question also from the point of view of logic, insofar as topological spaces can be used to give formal semantics to modal logics. The argument to be made here is that there is a distinct modality, which we will call the *truthmaker* modality, conforming to the axioms of $S4$ and whose topological semantics yields naturally the concept of open sets as entities.

If $\varphi$ is a proposition, we can construct another proposition of the form *"$\varphi$ has a truthmaker"* and denote this construction by $\square \varphi$. By $\square \varphi$ we mean that there exists some entity $x$ in reality such that in every possible world in which $x$ exists, $\varphi$ is true. So Socrates is a truthmaker for the sentence "Socrates exists" and the beard of Socrates is a truthmaker for "Socrates has a beard". 

Now, it may seem to some that all sentences would require truthmakers in this manner, and if that was the case there would be no need to introduce a modal operator $\square$ to qualify sentences, since then $\square \varphi$ would be true only when $\varphi$ itself were true. But we can certainly consider that some sentences need not necessarilly have truthmakers. For instance the sentence "unicorns do not exist" does not seem to require a truthmaker, for it is true not by virtue of there existing some entity in reality that makes it true, but rather by the *absence* of an entity, namely an unicorn. We can postulate that if a possible entity is absent from the actual world, this need not be due to the existence of another entity which necessitates its being absent; rather we could say its absence requires no explanation or grounding in the existence of something else.

In that case the truthmaker modality is certainly non-trivial, and we may expect it to conform to the following axioms of the modal system $S4$:

- $\bold{(K)} \ \square (\varphi \to \psi) \to (\square \varphi \to \square \psi).$
  
  Also known as the Distribution axiom of normal modal logics and named after Saul Kripke, this axiom can be read as saying that if there exists an entity $x$ in reality such that whenever $x$ exists and $\varphi$ is true $\psi$ is also true, and there exists an entity $y$ which makes $\varphi$ true, then there exists an entity $z$ which makes $\psi$ true. We can take $z = x \cap y.$

- $\bold{(T)} \ \square \varphi \to \varphi.$

  Obviously, if there is an entity in reality whose existence makes $\varphi$ true, then $\varphi$ is true. This is also called the Reflection axiom.

- $\bold{(4)} \ \square \varphi \to \square \square \varphi.$

  If an entity $x$ is a truthmaker for $\varphi$ then $x$ itself is trivially a truthmaker for the fact that a truthmaker for $\varphi$ exists.

Other than these axioms $S4$ also assumes the following inference rule:

- $\bold{(Necessitation)} \vdash \varphi \rArr \ \vdash \square \varphi.$ 

In our present context, this rule can be read as saying that if $\varphi$ is true in every possible world (because it is a tautology) then $\varphi$ has a truthmaker. One interpretation of this rule would be to say that it introduces the assumption that at least one possible entity exists, for any possible entity is a truthmaker of a necessarily true proposition. In fact the rule does more than that, as it is equivalent to the supposition of a Necessary Being in the topological semantics, and as such can be seen as stating the principle that necessary truths demand necessary truthmakers. 

The conception that the truth of propositions must be grounded in the existence of real things seems to underlie most of philosophy. It would seem very strange indeed that there was nothing in reality to ground the necessity of mathematical theorems, other than perhaps the human mind. We understand the mind to be contingent, so it would be hard for it to ground something necessary. Even if one attempts to ground necessary truths in the existence of multiple minds, if he won't admit the existence of a necessary mind, there wouldn't seem to be any reason to assume that it were necessary for some mind to exist at all, and as such it would seem to be possible for no mind to exist. Clearly however, if the collection of things on which a necessary sentence was grounded were itself contingent, the sentence itself would be either not necessary or not grounded.

Another more strictly Platonic interpretation of the rule would consist of in the exploration of 

## Examples of ontologies.
## The use of Alexandroff spaces.

We next consider some applications of the concepts developed so far to the formal definition of tradional concepts of Aristotelian metaphysics, such as the substance/accident distinction, the division of primary and secondary substances and God.

## Substances and accidents.
## Universals and positive properties.
## Intrinsic and extrinsic accidents.
## Defining God in topology.
## Conclusion.

It is not possible to develop the theory much further than what we have done in this current space, but we strongly believe that the system outlined here can serve as a foundation for the discussion of many other topics in metaphysics. The developments I have in mind already include the proper definition of the concept of essence, the Aristotelian distincion of matter and form, the Thomistic concepts of *actus essendi* and Divine simplicity, the formalization of a medieval theory of mereology, a theory of efficient causality and a few proofs of the existence of God.

<!-- For another paper: -->

<!--
Essence and accidents.
Matter and form.
Existence, essence, and the act of being.
The 10 Categories.
The 5 (post) Predicaments.
Mereology.
Efficient causality.
Teleology.
Proofs of the existence of God.
Platonism and angels. -->

