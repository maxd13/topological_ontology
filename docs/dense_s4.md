<style>
    body{
        text-align: justify;
        font-family: Times;
        /* font-size: 12pt; */
    }
</style>

# Substances, Truthmakers, and Natural Theology in $S4$

## **Abstract**
We consider the role the topological concept of density can play in the topological semantics of the logic $S4$. By means of this concept we mathematically define the Aristotelian notion of **substance**, i.e. a concrete particular object in the world, as a dense open set in the semantics of a specific modal operator which expresses that a proposition has a truthmaker. We begin first by giving an account of propositions, truthmakers, and how they are related by this modality before diving into the definition of substance. Based on these constructions, we provide an introduction to the general mathematical framework we use to formalize philosophical concepts, and later apply it to the particular question of mathematically defining God. Much more can be said about philosophy through this framework, but we leave that for a later article.

## **Introduction**

The topological semantics of the system $S4$ is known from the work of McKinsey and Tarski (1944). In this form of semantics we build upon the fact that the Lindenbaum-Tarski algebra construction of the propositional modal system $S4$ is an interior algebra. Every topological space can be seen as an interior algebra by means of its interior operator, which is defined in the powerset of the domain of the topological space, in such a way that every complete atomistic interior algebra is essentially a topological space. A topological interpretation of the $S4$ calculus is simply an interior algebra homomorphism from the Lindenbaum-Tarski algebra of $S4$ to some complete atomistic interior algebra (i.e. the powerset of some set, equipped with a Kuratowski interior operator). This is a particular case of the algebraic semantics of $S4$, in which the codomain algebra is allowed to be any interior algebra, but generalizes regular $S4$ semantics based on Kripke frames: a Kripke frame for $S4$ is just an Alexandroff topological space. 

<!-- We assume the reader to be acquainted with all of the relevant mathematics. -->

<!-- We do not assume the reader to be acquainted with all of the relevant mathematics in detail, but this is highly recommended, as we will not be explaining in this paper the basic notions of what topological spaces and interior algebras are. -->

<!-- In this paper we shall explain all these relevant mathematics in detail. -->

Considering the box operator of $S4$ to stand for a specific *truthmaker modality*, if points of a model topological space are considered to be possible worlds, the associated non-empty open sets of the space can naturally be taken to be possible entities, or *possibilia*, defined up to an equivalence relation which preserves their role as truthmakers for propositions. The dense open sets of the space can be interpreted as concrete possible objects, or substances in a basic Aristotelian sense, with non-dense non-empty open sets then taking the role of accidents. The empty set takes the role of *impossibilia* and the universe set of all points takes the role of a necessary being. Together with some philosophically relevant assumptions about the connectedness and compactness of the space, the necessary being could also be taken to be God. In what follows we give a summary of these ideas.

The reader need not be acquainted with all of the relevant mathematics to understand this paper, as many of the concepts are intuitive enough to be understood without a direct appeal to algebra, and some of them will be explained in the course of this article. A background in mathematics or logic is however desirable, and at least basic acquaintance with set theory must be assumed. Suffices to say, as an introduction to the layperson, that propositions in a logical language can be interpreted to be the sets of possible worlds in which the propositions are true, and this interpretation preserves the logical structure of the language. Furthermore, certain kinds of entities, called *truthmakers*, can also be represented as the sets of worlds in which these entities exist; this provides a simple way to analyze the grounding of propositions by truthmakers in terms of very well know mathematical structures. We shall explain these points in the course of this article.

## **Propositions and Truthmakers** [$^1$](footnote1)

**[footnote1]: For an introduction to truthmakers, refer to: MacBride, Fraser, "Truthmakers", The Stanford Encyclopedia of Philosophy (Spring 2019 Edition), Edward N. Zalta (ed.), URL = <https://plato.stanford.edu/archives/spr2019/entries/truthmakers/>.**

There is in philosophy an intuitive notion that the truth of propositions must be grounded in the existence of real things. We say that a possible entity $x$ is a *truthmaker* for a proposition $\varphi$ if and only if in every possible world in which $x$ exists, $\varphi$ is true. We assume that some propositions require truthmakers to exist in order to be true, as is clear from the example of purely existential propositions. For instance, the proposition "zebras exist" will be true if and only if there exists some zebra, so any zebra is a truthmaker for this proposition, just as Socrates is a truthmaker for "Socrates exists".

We assume also that not all propositions require a truthmaker in order to be true. The proposition "unicorns do not exist" is one such proposition: we need not assume that in every possible world in which unicorns fail to exist there exists some distinct entity whose very existence precludes the existence of any unicorn. Rather if in some possible world "unicorns do not exist" is true, this could simply be explained by the absence of unicorns.

If in a given possible world $w$ no entity exists that precludes unicorns from existing, we will say that unicorns are, in this sense, possible in $w$, while if some entity exists in $w$ which does precludes unicorns from existing in the same worlds as itself, we will naturally say unicorns are impossible in $w$; and of course, in any possible world in which unicorns do exist, they are in fact be possible. Because of this it seems natural to consider that the proposition "unicorns do not exist" does not require a truthmaker, as we do not expect that in the actual world there be any unicorn-precluding entity incompatible with the existence of unicorns and necessary to explain their absence.

We call this sort of propositions -- which demand truthmakers in order to be true -- **open** propositions. They depend on the existence of truthmakers in the sense that in any possible world in which truthmakers for these propositions do not exist, the propositions are false. On the other hand, a proposition like "unicorns do not exist", which is clearly just a negation of an open proposition, are called **closed** propositions. Some propositions are neither open nor closed, while some are both, as we will see shortly.

### **Mathematics and Necessity**

What kinds of proposition are open? Certainly the ones which talk explicitly about existence in a positive sense must be considered such, but it is less obvious whether, for instance, mathematical statements can be open propositions. It surely doesn't look like (unless one is committed to numbers being distinct self-subsistent entities) the statement $2 + 2 = 4$ is talking about or postulating the existence of anything, so one could perhaps be excused for thinking that no such statement can be open. 
It also doesn't look like it is denying that any class of entities exists either, so it doesn't appear to be closed. In fact, it would, perhaps, be shocking to many mathematicians to claim that statements of
pure mathematics could have any sort of existential content whatsoever, as it is believed by many that mathematics
does not talk about anything that goes on in reality, but only about ordering concepts in our mind.

Yet, if we consider the also generally accepted principle of propositional extensionality, the whole subject changes
picture. By propositional extensionality we mean the claim that propositions which are logically equivalent are in
fact equal. So because "$1 + 1 = 2$" is logically equivalent to "$2 + 2 = 4$", we have that in fact these formulas express one and the same proposition; or at least they do so with respect to a suitable theory of arithmetic, such as that of Peano. Now, even within Peano arithmetic, it is provable that "$2 + 2 = 4$" is logically equivalent to "$\exists x, x = x$" which expresses the informal claim that "something, whatsoever, exists". It looks clearly that, at least with respect to the theory of arithmetic, "$2 + 2 = 4$" in fact signifies an open proposition.

Of course it is very much possible for the anti-realist mathematician to object that the existential quantifier of
predicate logic does not really mean the same thing as "existence" in the metaphysical sense. That much might as well
be granted; but provided one does not deny that the principle "something, whatsoever, exists" is necessarily true, as a self-evident metaphysical principle, it should follow that, under a suitable theory of metaphysics and existence which also included arithmetic, "$2 + 2 = 4$" is also equivalent to this principle in a metaphysical sense of the word "exists". As such, once we consider metaphysical theories, and logical equivalence *modulo* (or relative to) metaphysical theories, we can conclude with absolute certainty that any and all statements of mathematics, and in fact any and all necessary statements whatsoever, must be open. They are all equivalent to this single, clearly existential, statement.

Are necessary statements also closed? For them to be closed, they have to be the denial of an existential, i.e. open,
statement. However the denial of a necessary proposition is either a logical or a metaphysical contradiction; they are what can be called *metaphysically impossible* propositions. The denial of any necessary formula is, as such, logically equivalent to the expression "There exists (in the "metaphysical" sense) a real physical object whose shape is both that of a sphere and that of a cube at the same time". Intuitively, the proposition signified by this expression could only be true if there were such a weirdly shaped object, but because no such object can exist, in any possible world, the proposition is absurd and impossible. Being absurd, however, does not mean it is not open, and as such we can conclude that, in effect, necessary propositions are also closed. 

We call propositions which are both open and closed **clopen** propositions. The existence of clopen propositions should otherwise have prompted us to abandon this sort of nomenclature if it were not for the fact it is standard in the field of topology; so the reader must bear this apparent contradiction in terms. Notice further that any metaphysically impossible propositions are also clopen, since we have shown them to be open, and since their negation is also open, they are both open and closed at the same time.

<!-- Now, there are theories which in fact do claim more than mere logic and arithmetic; in fact any true metaphysical theory must do such a thing. However,  -->

<!-- Of course there are many different true formulas of arithmetics, which are intensionally very different from each other, even though they do not differ with respect to logical equivalence. By saying that -->

### **Algebraic operations on open propositions**

There are also other propositions which are neither metaphysically necessary nor impossible. We have already given two examples of some such propositions above which illustrate other important facts
about open propositions. There are existential statements which postulate the existence of a single entity, such as "Socrates exists", and there are the ones which postulate the existence of an entity from among a class, such as
"Zebras exist". Any statement of the latter class can plausibly be seen as a disjunction of, perhaps infinitely many,
statements of the former, so that if $Z$ is the set of all possible zebras, and z is a zebra, there will be this proposition "z exists", and the proposition "zebras exist" can be looked at as being the logical disjunction of all propositions of this sort; i.e. this latter proposition is true if and only if at least one proposition of the form "z exists" is true. From this we can conclude that the class of open propositions is closed by disjunctions of any arbitrary size; so given any arbitrary set of open propositions, their "disjunction", in the sense outlined above, will be also an open proposition.

Another more controversial point to be made concerns whether the same is true for conjunctions of propositions. We would like it to be the case that whenever two propositions $\varphi$ and $\psi$ are open, then their conjunction $\varphi \land \psi$ be also open. Here the conjunction, denoted by the $\land$ symbol, is the proposition which states that "both $\varphi$ and $\psi$ are true at the same time". What does this requirement entail? It requires us to postulate that whenever both propositions are true, there is a distinct entity in reality which makes them both true. Someone might object that for both propositions to be true, if they are open, it suffices that both have distinct truthmakers, but not that there is a truthmaker which makes them both true. For example, the sentences "Socrates exists" and "Plato exists" are made true respectively by Socrates and by Plato, but the sentence "both Socrates and Plato exist" is not made true by either of them separately, since one could exist without the other. What we are claiming is that in this and any other similar cases there is some distinct entity, which is neither Socrates nor Plato, whose existence entails the existence of both Socrates and Plato.

What kind of entity would this be? I can only think that this entity would be some sort of mereological fusion of Socrates and Plato. Some sort of totality, collection, set, or whole which contains Socrates and Plato, and only Socrates and Plato, can be thought of as being a distinctly existing entity, and whose existence entails the existence of both of them. We can also postulate, along the same lines, that when we say that "Humanity exists"[$^2$](footnote3), for instance, we are really saying that there is this distinct entity in the world, or universal if you will, which corresponds to the class all humans, such that the existence of a human entails the existence of this universal entity. These universals need not be thought of as Platonic universals in any sense (though they might be) but could be taken to be just the spatio-temporal extensions of all members of the class (assuming they have spatio-temporal extensions), or some other such reductive paraphrasis as may suit any (naturalist) philosopher's fancy. This would then be a distinct sort of mereological fusion from the conjunctive one. 

**[footnote2]: Which we take here to be logically equivalent to "Humans exist".**

### **Alternatives to our algebraic realism**

If the reader is uncomfortable with this sort of realistic assumption, we will discuss below how he can avoid such postulates by taking truthmakers to be *facts* rather than entities. An ultra-realist, such as myself, is entirely comfortable with the assumption that there is no real distinction between facts and entities, but we leave room in the mathematical theory to accommodate less radical views. It may seem after all more plausible to some readers to say that there is a distinct *fact* that Socrates and Plato exist at the same time, which grounds the truth of the conjunctive proposition, than to say that there is a distinct, really existing, *entity* which does so. Similarly, he may admit that there is some distinctive *fact* that human beings exist, which is distinct from the existence of any particular human being, and which grounds the truth of the disjunctive proposition; instead of admitting that this fact is really the *entity* which we call "Humanity". We will discuss the costs that such a distinction incurs in the course of the paper.
<!-- 
To delve a little bit deeper, as a side note, on my own position about the issue, I defend the position that I call **algebraic realism**. There are  -->

Regardless of what one's position might be about the intrinsic nature of truthmakers, as to whether they are entities or facts, states of affairs, or something else entirely, what the theory does require is that if a pair of open propositions is conjunctively true, then there is a distinctive truthmaker which grounds the truth of the conjunction. What justifies us in accepting at least this much is really the mathematical beauty and simplicity of the theory that ensues. We will assume, in our following discussion, for simplicity's sake, and for consistency with our previous definition of truthmakers, that truthmakers are indeed entities; but the attentive reader can readily reconstruct our theory in terms of a framework of facts, if he so wishes. 

It is important to point out however that we need not assume that the "truthmaker" of a conjunction needs to be a real entity, at least in the case in which such conjunction is logically impossible. If a proposition $\varphi$ is clopen, the conjunction of $\varphi$ and $\lnot \varphi$ is inconsistent. It will still however be open, as we have shown above inconsistent propositions are open. In this particular case the openness of such propositions is not an extra assumption of the theory, but something that follows from what has been previously discussed. Furthermore, that there exists a truthmaker for the conjunction whenever there exist truthmakers for the individual propositions follows vacuously from the fact that it is impossible for these truthmakers to coexist in the same possible worlds. 

### **The Alexandroff hypothesis**

Are arbitrary conjunctions of open propositions also open, or just conjunctions of finitely many propositions? This will certainly be the case if the infinite conjunctions turns out to be metaphysically impossible propositions, as we have already discussed. I would believe also that, even outside this special case, once one admits that finite conjunctions are open, there is no reason not to grant that arbitrary conjunctions are open, for I see no reason to postulate any sort of asymmetry in completeness between conjunctions and disjunctions. However, we are not really constrained by the mathematical interpretation to admit this principle, for the whole theory could in principle be developed without it. It is quite possible that the assumption of this principle, which we call the *Alexandroff hypothesis*, would provide us with many metaphysically relevant consequences, and the whole range of these consequences remains yet to be explored. Nevertheless, in the present
article we will not rely on this assumption.

Without the Alexandroff hypothesis, our reflection about truthmakers and open propositions already demonstrates informally that the class of open propositions might be treated as the collection of open sets of some topological space[$^3$](footnote2). If the hypothesis holds, this topological space will also be Alexandroff-discrete. This is the basis for our mathematical treatment of the concept of truthmakers. 

To summarize the results of this section:

* Propositions can have **truthmakers**.
* Propositions that are only true when truthmakers exist for them are called **open**.
* Not all propositions are open.
* Propositions that are the negation of an open proposition are called **closed**.
* Metaphysically necessary and impossible propostions are both open and closed, i.e. **clopen**.
* The arbitrary disjunction of open propositions is open.
* The conjunction of pairs of open propositions is open.
* Treating truthmakers as facts rather than entities does not hurt our mathematical account of truthmakers (more on this later).
* It is perhaps acceptable also that arbitrary conjunctions of open propositions are open, which is called the **Alexandroff hypothesis**, but we shall not assume this.

**[footnote3]: Or, to be more accurate, it corresponds to a *frame* in the context of pointless topology, since we have not yet discussed how to represent propositions as sets of possible worlds, or points. But this distinction is irrelevant for our present purposes, as we will be discussing such representations shortly.**

## **The Truthmaker modality**

With the notion of "truthmaker" in place and an intuitive account of how open propositions form a topology, we begin the mathematical treatment of the problem. We see that for any proposition $\varphi$ there will be some other proposition "$\varphi$ has a truthmaker", which we can denote by $\square \varphi$. This latter proposition will be true in a possible world if and only if there exists an entity in that world which is a truthmaker for proposition $\varphi$. If $\square$ is taken to be a modal operator we should expect it to satisfy, by what has been discussed above, the axioms for $S4$. In which case, its associated diamond operator $\diamond$ will also model precisely the particular notion of possibility we have just outlined in paragraph **3** of the previous section. To see this we remind the reader here of the axioms of $S4$:

### **Axioms of $S4$:**

- $\bold{(K)} \ \square (\varphi \to \psi) \to (\square \varphi \to \square \psi).$
  
  Also known as the Distribution axiom of normal modal logics and named after Saul Kripke, this axiom can be read as saying that if there exists an entity $x$ in reality such that whenever $x$ exists and $\varphi$ is true then $\psi$ is also true, and there exists an entity $y$ which makes $\varphi$ true, then there exists an entity $z$ which makes $\psi$ true. To recap, we can always consider $z$ to be a mereological conjunction of $x$ and $y$; so we denote this by $z = x \cap y$ for reasons that will become obvious in the next section.
  
  <!-- , and if entities are identified with the sets of possible worlds in which they exist, as we shall explain below, we would have $z = x \cap y.$ The entity $z$ is then precisely the entity denoted by the expression "the fact that both $x$ and $y$ exist", and this can be taken to be some totality whose existence depends of both $x$ and $y$. Some sort of whole of which only $x$ and $y$ are parts. -->

- $\bold{(T)} \ \square \varphi \to \varphi.$

  Obviously, if there is an entity in reality whose existence makes $\varphi$ true, then $\varphi$ is true. This is also called the Reflection axiom.

- $\bold{(4)} \ \square \varphi \to \square \square \varphi.$

  If an entity $x$ is a truthmaker for $\varphi$, then $x$ itself is trivially a truthmaker for the fact $\square \varphi$ that a truthmaker for $\varphi$ exists.

Other than these axioms $S4$ also assumes the following inference rule:

- $\bold{(Necessitation)} \vdash \varphi \rArr \ \vdash \square \varphi.$ 

  In our present context, this rule can be read as saying that if $\varphi$ is true in every possible world (because it is a tautology) then $\varphi$ has a truthmaker. The interpretation that we have given for this rule is that it says that at least one possible entity must necessarily exist in any possible world, for any possible entity is a truthmaker of a necessarily true proposition.

### **Truthmakers for necessary truths**

There seems to have been some unease about the acceptance of our entailment-based definition of truthmakers in the literature on account precisely of the fact that it makes any entity a truthmaker for any necessary proposition. This implies that, for instance, whatever is in the back of my refrigerator is a truthmaker for "$2 + 2 = 4$", even though arithmetic has nothing to do with refrigerators. This is of course just a consequence of the fact that the entailment relation we have in mind in our definition is classical and not one, say, of a relevance logical calculus. 

Now, it is certainly outside the scope of this article to answer all possible objections to this simple and usual definition of truthmakers, but I must say at least that I do not see much bite in this sort of objection. I believe this unease may come from the fact that sometimes what philosophers mean by "the truthmaker of $\varphi$" is what in my theory I call would *the ontological counterpart* of $\varphi$. This concept, which we will properly define later, can be thought of as the "supremum" under a certain order of existential entailment, of all the truthmakers of a proposition. Any run of the mill truthmaker for "$2 + 2 = 4$" is indeed very much irrelevant for arithmetics, but the ontological counterpart of that proposition is a necessary being. It looks to me that a necessary being is much more relevant as the ground for the truths of arithmetic than what is in the back of my refrigerator. 

Nevertheless, we require this simpler concept of truthmaker first to later be able to define that of ontological counterpart. As such, from our point of view, it is better first to give a simple definition of what truthmakers are and then refine the definition for special classes of truthmakers later to account for other epistemic goals a theory of truthmakers is intended to satisfy, such as that of an account of relevance. It is also quite clear that if we do reject the simple definition we would have to reject the $S4$ axiomatization of the truthmaker modality. This would probably make the mathematical theory of this modality inconvenient. We want therefore to take this characterization of truthmakers to its ultimate consequences, and I do believe that doing so will provide an incredibly rich mathematical theory of ontology.

### **Some consequences of the axiomatization**

<!-- The usefulness of a redefinition of truthmakers that tries to account for a relevance relation between the truthmakers and the propositions can in the best case scenario only be akin to whatever usefulness relevance logic provides us beyond the usage of classical logic. It is quite clear that classical logic does not provide us with a good definition of the concepts of "deduction", "syllogism" and "proof". Even Aristotle already knew that something more is required for a proof to be epistemically relevant than the mere entailment of the conclusion from the premisses, which is why his logic was in effect paraconsistent. Nevertheless, what is also true is that no relevance logic can do a better job at defining the simple notion of logical entailment than classical logic does. In fact I would say that the   -->


<!-- In fact from this rule we will ultimately be able to infer that there is a necessary being (or fact) in the topological semantics, and as such it can be seen as stating the principle that necessary truths demand necessary truthmakers.  -->

<!-- The conception that the truth of propositions must be grounded in the existence of real things seems to underlie most of philosophy. It would seem very strange indeed that there was nothing in reality to ground the necessity of mathematical theorems, other than perhaps the human mind. We understand the mind to be contingent, so it would be hard for it to ground something necessary. Even if one attempts to ground necessary truths in the existence of multiple minds, if he won't admit the existence of a necessary mind, there wouldn't seem to be any reason to assume that it were necessary for some mind to exist at all, and as such it would seem to be possible for no mind to exist. Clearly however, if the collection of things on which a necessary proposition was grounded were itself contingent, the proposition itself would be contingent. As such it only makes sense to expect necessary truths to be grounded in a necessary being.

Furthermore, the assumption of a necessary being is a metaphysically parsimonious one, for even many skeptics of metaphysics have admitted that in the absence of a God, the universe itself, as well as its composing matter, would have to be taken to be necessarily existing entities. Bertrand Russell for instance, following J. S. Mill, appears to adopt this position **[TODO: add further citations]**.  Many arguments do in fact exist to show the existence of a necessary being in general, regardless of further controversy, and suffices at this point to admit simply that a necessary being exists, whatever its nature might be. -->

It is also a consequence of the axioms of $S4$ that $\square$ distributes over conjunctions, i.e. $\square\varphi \land \square\psi = \square (\varphi \land \psi)$ for any $\varphi, \psi$. This fact is
what commits us to the position that conjunctions of open propositions have distinct truthmakers because $\square\varphi \land \square\psi \to \square (\varphi \land \psi)$ literally means "if $\varphi$ has a truthmaker, and $\psi$ has a truthmaker, then the fact that both occur together has a truthmaker". In the special cases that $\varphi \to \psi$ or $\psi \to \varphi$ any truthmaker of the antecedent would be a truthmaker of the consequent, and as such no distinct truthmaker for the whole conjunction would be needed. But if these special cases do not hold, then at least in some possible world $w$ one proposition would be true while the other false, and in this world if one of them had a truthmaker (e.g. because it is open) this couldn't be a truthmaker for the conjunction.

It would be possible to assume that in the worlds in which the propositions are conjointly true, only the truthmaker for the conjunction exists, instead of a distinct truthmaker for each proposition, but it must be assumed that it is at least possible for a distinct truthmaker for each proposition to exist, since these truthmakers exist in other possible worlds. It might perhaps be much more simple to just assume that these conjoint truthmakers really are mereological totalities composed of truthmakers for each proposition; so whenever truthmakers were present for each proposition, some conjoint truthmaker would also be present. The way these assumptions are used in our theory will become clear shortly when we discuss the nature of truthmakers in the next section.

Furthermore the assumption is used the justify the validity of axiom $\bold{K}$. Since, under our definition of truthmakers, the other axioms and the necessitation rule should be uncontroversial, and the assumption of $\bold{K}$ together with these axioms is sufficient for $\square$ being distributive over conjunctions, $\bold{K}$ is certainly the strongest assumption in our theory of the truthmaker modality. Denial of it would leave us very much outside the realm of normal modal logics, which is to say, much farther away from a simple theory of this modality and of its semantics. By the end of this paper, we shall quickly glance at how the assumption of $S4$ gives the semantics of this modality strong connections with the semantics of intuitionistic logic, which further justifies its assumption via the analogy between truthmakers and proofs.

Naturally, with this notation we should also be able to express that a proposition $\varphi$ is open by the formula $\square \varphi = \varphi$, where, to recap, equality between propositions is defined to be logical equivalence. In fact, because of the axiom $\bold{T}$ above, it suffices that $\varphi \to \square \varphi$ be true for $\varphi$ to be open. This literally says that if $\varphi$ is true, then it has a truthmaker. Dually, to say that $\varphi$ is closed is to say $\diamond\varphi = \varphi$ which under $S4$ is equivalent to $\diamond\varphi \to \varphi$. Mathematically the equations define what are known as *fixed points*. We can equivalently say that $\varphi$ is open if it is a fixed point of the $\square$ operator, and closed if it is a fixed point of the $\diamond$ operator, they are called *fixed points* because when the operators are applied these propositions are in a sense "fixed in place".

### **Natural necessity and possibility**

It should also be noted that we can interpret the $\square$ operator as some kind of alethic necessity, which is perhaps a good representation of the notions of natural, or physical, necessity.
We can say that $\square \varphi$ expresses that the proposition $\varphi$ is "necessary" in the sense that the existence of something necessitates it, or determines it to happen, but not in the sense that it is true in every possible world.
Its dual operator $\diamond$, which is defined to be $\lnot \square \lnot$, then naturally corresponds to the dual notion of possibility. If we take $\square \lnot \varphi$ to mean that "something *precludes* $\varphi$ from being true", then naturally $\diamond \varphi$ says $\varphi$ is possible in the sense that there is nothing which precludes it from happening. It makes sense that negative existential statements satisfy $\diamond\varphi \to \varphi$ because the only thing that would preclude such a statement from being true is the exitence of the entity they deny, but if this entity does not exist they are true. In the absence of something to preclude unicorns from failling to exist (i.e. an unicorn), then unicorns do not exist.

Natural necessity is necessity that is due to the existence of things in the world, in particular the existence of contingent things. It is not necessary in an absolute sense, for instance, that plants always grow toward the sun (in the sense that this would happen in any possible world) because arguably there are worlds in which no plants exist at all. But this is in a sense necessary relative to the actual world because plants exist in it along with the conditions necessary for their growth. So if $\varphi$ is the proposition "plants grow toward the sun" then $\square \varphi$ could also be interpreted as saying that "it is by natural necessity that plants grow toward the sun", because whenever there is a truthmaker for $\varphi$, i.e. plants conjoined with the conditions for their growth, it follows necessarily (axiom $\bold{T}$) that $\varphi$ is true. So $\varphi$ is necessitated by the existence of contingent natural entities. Natural possibility $\diamond \varphi$ can then be interpreted as "it is not against the laws of nature that plants grow toward the sun". This interpretation may also lend further plausibility to our assumption of axiom $\bold{K}$.

<!-- ### **Diamond of possibility**

What axioms are valid for the dual operator $\diamond$? The following axioms are a consequence of the definition of $\diamond$ under $S4$, and they also provide an alternative axiomatization of the logic: -->

<!-- ### **Derived modalities**

From these 2 basic modalities we can also define others throught the combination of them. -->

### **Event-based Semantics**
In the topological semantics of $S4$, every proposition $\varphi$ is associated with a possible (or the single impossible) *event* in a topological space of possible worlds. As should perhaps be clear by now, a topological space is a mathematical structure which consists of:

* A set $W$ of points, which we call **possible worlds**.
* A set $\mathcal{O}$ of subsets of $W$, the elements of which we call **open sets**, such that $\mathcal{O}$:
  * Includes $W$: $W \in \mathcal{O}$.
  * Includes the empty set: $\empty \in \mathcal{O}$.
  * Is closed by arbitrary unions: $\bigcup\limits_{S \in X \subseteq \mathcal{O}}S \in \mathcal{O}$
  * Is closed by intersections: $\forall S_1,S_2 \in \mathcal{O}, S_1 \cap S_2 \in \mathcal{O}$

Axioms which we have already shown open propositions must satisfy, and which we now assume to be true for open events as well.

 An **event** is nothing but a set of possible worlds, so that $\varphi$ is associated with the set $[\varphi]$ of possible worlds in which $\varphi$ is true, i.e. the "event" of "$\varphi$ being true". The association is of course consistent with the rules of the propositional calculus, so, again, two logically equivalent propositions are considered to be equal, are associated with the same event, and:

- Necessarily true propositions $\top$ are associated with the set $[\top]$ of all possible worlds.
- Necessarily false propositions $\bot$ are associated with the empty set $[\bot] = \empty$.
- The negation $\lnot \varphi$ is associated with $[\varphi]^c$, the set complement of $[\varphi]$.
- The proposition $\varphi \land \psi$ is associated with the intersection $[\varphi] \cap [\psi]$.
- The proposition $\varphi \lor \psi$ is associated with the union $[\varphi] \cup [\psi]$.
- and so on...

In this manner the association is restricted to be what is called a *Boolean algebra homomorphism*. Moreover, the proposition $\square \varphi$ is associated with the topological interior of the set $[\varphi]$, i.e. the largest open subset of $[\varphi]$ in the topological space. In this manner, the association grows to be what is called an *Interior algebra homomorphism*.

It is then trivial to notice that, since $\square \varphi$ is taken to mean that "$\varphi$ has a truthmaker", $[\square \varphi]$ is the *event* of $\varphi$ having a truthmaker, i.e. the set of all possible worlds in which $\varphi$ has a truthmaker. This event corresponds to the union of all the open subsets of $[\varphi]$, i.e.:
 
 $$[\square \varphi] = I([\varphi]) = \bigcup_{S \in \mathcal{O}_{[\varphi]}}{S}.$$
 
Where $\mathcal{O}_{[\varphi]}$ is the set of all open subsets of $[\varphi]$ and $I$ denotes the interior of a set. Now, an event $e$ is said to **occur** at possible world $w$ if and only if $w \in e$. Considering this, we can conclude that the occurrence of any such open event $S$ will entail the existence of some truthmaker of $\varphi$, in the sense that in any possible world in which $S$ occurs $\varphi$ has a truthmaker. Furthermore, in any possible world in which $\varphi$ does in fact have a truthmaker at least one of these events $S$ from the set $\mathcal{O}_{[\varphi]}$ must necessarilly occur. The events of $\mathcal{O}_{[\varphi]}$ are then good candidates to be the events of particular truthmakers of $\varphi$ existing, since given any truthmaker $x$ of $\varphi$, the set of all possible worlds in which it exists must necessarily be a subset of $[\square\varphi]$, and it seems only natural to think that $[\square\varphi]$ is but the union of all such events for all truthmakers of $\varphi$.

Dually, $\diamond \varphi$ is associated with the topological closure of $[\varphi]$, i.e. the smallest closed superset of $[\varphi]$, denoted $C([\varphi])$. Since $\diamond \varphi$ is taken to mean "nothing precludes $\varphi$ from being the case", $[\diamond \varphi]$ is the *event* of no entity existing whose existence would entail $\varphi$ to be false. This event corresponds to the intersection of all closed supersets of $[\varphi]$:

$$[\diamond \varphi] = C([\varphi]) = \bigcap_{S \in \mathcal{C}_{[\varphi]}}{S}.$$

Where $\mathcal{C}_{[\varphi]}$ is the set of all closed supersets of $[\varphi]$. It is also a theorem of topology that arbitrary intersections of closed sets are closed, therefore $[\diamond \varphi]$ is a closed event. It should be interesting to mention the further dual theorem which says that (finite) ***unions of closed sets are also closed*** so that by means of this we have given a full characterization of the basic axioms of both open and closed sets.

To summarize this section: **TODO**

## **Truthmakers as open events**

After showing that open propositions can be represented by (open) events, we seek to show now, as we have hinted above, that truthmakers too can be so represented. In fact this will allow us to refer to open sets of a topological space synonymously as both open propositions and truthmakers. We make no assumption that the there is no real distinction between open propositions and truthmakers, but only that both can be *represented* by exactly the same sets; and by a representation of $A$ by $B$ we mean roughly that there is some injective function from $A$ to $B$ which in some sense preserves all relevant structure present in $A$ that would be relevant to preserve for the purpose of talking about, or paraphrasing, elements of $A$ by means of elements of $B$[$^4$](footnote4).

**[footnote4]: In algebra this would more accurately be called an *homomorphism*.**

### **Existential entailment**

What is the nature of truthmakers? If they are entities, what kinds of entities are them? It should be safe to assume that only those entities which stand in the relation of *truthmaking* to propositions qualify; and furthermore, we have already defined what this relation is via logical entailment. However from the point of view of our definition any entity $x$ would at the very least be a truthmaker for the proposition "$x$ exists", so it looks like there is no specific kind of truthmaker entities. Nevertheless, I believe we should look at the possibility of there being a distinct kind of such entities in more detail before dismissing it, and for this discussion we need to begin by introducing the simple concept of existential entailment.

<!-- It should however be expedient to generalize first the relation of truthmaking to the entities themselves before investigating what truthmakers are.  -->

We say that an entity $x$ **existentially entails** an entity $y$ if and only if in every possible world in which $x$ exists $y$ must also necessarily exist; which is to say that "$y$ exists" is entailed as a logical consequence by the proposition "$x$ exists".
 
**TODO** [existential entailment and equivalence]

<!-- We can speak of "entities" as being the truthmakers of propositions  -->

<!-- in the propositional calculus, and define them within the metalanguage of the model space by means of its events. Indeed, every abstract "entity" can be associated with the set of all possible worlds in which it is supposed to exist, and the association should be unique up to an existential equivalence. Namely, if two entities $x$ and $y$ exist in exactly the same possible worlds we shall say that they are **existentially equivalent** and denote this by $x \lrArr y$. -->

Are existentially equivalent entities equal? It might be difficult to tell whether equivalent entities are really distinct. For instance, we do not know whether Socrates is really distinct from "the humanity of Socrates", for it might be hard to find any non-trivial *real* predicate, whose semantics we can easily understand without mystery, that would distinguish Socrates from something as abstract and mysterious as his "humanity", and which would commit us to the real existence of this distinct object. Yet, if there is such a thing denoted by this expression we should expect it to be at least existentially equivalent to Socrates, for wherever you find Socrates (i.e. in any possible world), there is his humanity, and wherever you find his humanity, there must also be Socrates. There is in this example a doubt as to whether the distinction between Socrates and his "humanity" is one merely of reason or one of reality. We would perhaps have greater evidence for positing a real distinction between them were it not for the fact that both are existentially equivalent.

<!-- Two entities that are existentially equivalent cannot be distinguished in mathematical terms, nor, as I suspect, in any terms at all that are expressible in human language. For instance, we do not know whether Socrates is really distinct from "the rationality of Socrates", for we cannot find any non-trivial real predicate, whose semantics we can easily understand without mystery, that would distinguish Socrates from something as abstract and mysterious as his "rationality". Yet, if there is such a thing denoted by this expression we should expect it to be at least existentially equivalent to Socrates, for wherever you find Socrates (i.e. in any p. world), there is his rationality, and wherever you find his rationality, there must also be Socrates. There is in this example a doubt as to whether the distinction between Socrates and his "rationality" is one merely of reason or one of reality, and we would have greater evidence for positing a real distinction were it not for the fact that both are existentially equivalent.
-->

To refer quickly to a theological, and even more mysterious, example, in Christianity we cannot distinguish the Father from the Son by any specific property which natural reason can prove one to have and the other to lack. But by revelation we are told there is a real distinction between them, which otherwise we would not be able to know. This has to do, I would argue, with the fact that both are existentially equivalent in this sense, which makes the real distinctions between them fuzzy and mysterious to us.

### **Intensional and Extensional entities**

To clarify the issue while giving us a path to avoid any mysterious aspects which would be too hard to investigate in the present article, we may distinguish an extensional ontological theory from an intensional one. In an extensional ontological theory there is a clear identity criteria between the basic entities of the theory; just as in set theory there is a clear identity criteria between sets. In contrast, in an intensional theory identity between entities is taken to be a primitive relation which is essentially undefinable, except perhaps in a trivial or, perhaps circular, sense. In such a theory it is therefore much harder to prove that any two entities are equal; we can take as self-evident or axiomatic that two entities are equal, but it is next to impossible to prove this for any non-trivial case without previous assumptions about the identity of other entities. In contrast, in the extensional theory most identity statements are derived explicitly from the application of an extensionality axiom.

In set theory the extensionality axiom states that two sets are equal if and only if every element of one is an element of the other. To produce for our theory an equivalent axiom, it would suffice to define a truthmaker to be an equivalence class, of the "entities" of some intensional theory, with respect to the relation of existential equivalence. In this manner, since the truthmakers become essentially sets of intensional entities, we can define their equality as equality between sets, which doesn't depend for its definition on a notion of equality between the elements of the sets, but only on a primitive notion of set membership. Furthermore, this definition is applicable to any intensional theory of ontology which admits a relation of existential entailment, this in turn makes our extensional theory of truthmakers compatible with any background intensional theory one wants to adopt. 

From this characterization of truthmakers there naturally occur such questions as, first, what grounds do we have to say that truthmakers are purely extensional entities? Secondly, if they are taken to be so, are they a new *sui generis* kind of entity or can they be reduced simply to the equivalence classes of intensional entities? Thirdly, if truthmakers are so characterized will they stand in an 1-1 relation with respect to open propositions/events?

The first question can naturally be resolved by considering that, just as logically equivalent propositions have the same truthmakers, existentially equivalent entities are truthmakers for exactly the same propositions. If the existence of an entity $x$ entails the truth of a proposition $\varphi$ and entity $y$ is existentially equivalent to $x$, it is obvious that the existence of $y$ also entails $\varphi,$ therefore $y$ is also a truthmaker of $\varphi$. In this sense any entity in an existential equivalence class can be taken to be *a* or *the* truthmaker for $\varphi$, but it is really the whole class, regardless of the arbitrary choice of representative, which stands in the relation of being a truthmaker for the same propositions. Cast in another light, if we abstract away the differences between entities in the same class we can say they are the same *qua* truthmakers, i.e. they are the same in respect to how they stand in the truthmaking relation to propositions; the singular entity that is abstracted away by this procedure can be called *the* truthmaker, that unique position in the truthmaking relation in which all members of the class stand. It is quite clear that from this point of view it makes perfect sense to *define* truthmakers as equivalence classes of propositions; in this way we can see that the derived principle of extensionality for truthmakers, which is a consequence of their definitions as sets, is in a sense an ontological dual, or "counterpart", of the logical principle of propositional extensionality.

To be sure, some things might be lost by considering truthmakers to be purely extensional. As in the example above, someone may want to claim that there is something like "the humanity of Socrates" which is really distinct from him and which should be the only thing considered a true truthmaker for "Socrates is human". In our theory, Socrates himself suffices as a truthmaker for his being human just as well as his "humanity" might. In fact, for any essential predicate of Socrates just about anything that is existentially equivalent to him suffices as a truthmaker for the proposition formed from this predicate, and we might as well simply refrain from talking about the myriad of things that may fall into this category and talk rather about Socrates *qua* truthmaker as standing in the truthmaking relation to the proposition "Socrates is human". So from the point of view of our theory, we can neither affirm nor deny that "the humanity of Socrates" exists; we can not even express it within the confines of our mathematical theory.

<!-- Strangely enough, Socrates's "humanity" also suffices as a truthmaker for "Socrates exists". -->

The extensionality principle is a necessary consequence of our definition of truthmakers, if someone is not comfortable with it he must take issue with the simple definition that we have given. However, as pointed out before, our general approach is to give a simple definition of truthmakers and then refine it as needed for special cases, lest the notion of truthmaker is left undefined and a new primitive concept is introduced into our theory without a proper axiomatization. It is entirely possible to later introduce an intensional notion of truthmaking which is compatible with our extensional definition and which can help expand our theory into further directions. It is not a strict requirement of our philosophy that there be a single relation of "truthmaking", but only that this extensional relation we have described exists and that it can be used as a foundation for a lot of philosophy. It might however also turn out to be that most of philosophy can be made rigorous by considering it only from the extensional perspective and not feigning hypothesis about intensional matters.

### **Are Truthmakers special entities?**

With regards to the second question it must be said that it is indifferent to our theory whether or not truthmakers so considered form a distinct category of entity or not, and as such we do not assume it. This might be defended by postulating that among each equivalence class there is a canonical representative which in some sense or another best represents the whole class for purposes of truthmaking. If this is assumed we could define truthmakers precisely as being the class of entities whose identity conditions are given precisely by existential equivalence, even though in this case their extensionality principle would not be a corollary of the extensionality of sets. But the introduction of this assumption into the theory requires us to admit a new primitive category of truthmakers, which looks very much unwarranted.

But we should not conclude, from assuming truthmakers to be equivalence classes of entities, that we are somehow committed to the real existence of sets or classes of entities as being a real *sui generis* kind of entity either. We talk about sets and classes as concepts to represent and model reality, just as any mathematician would. We would rather conclude that truthmakers are just abstract concepts that we use to represent entities defined *up to* existential equivalence insofar as they are truthmakers of propositions. There are, in short, no real "truthmakers" but only entities which stand in the truthmaking relation to propositions; it is only that we also overload the term "truthmaker" to talk about classes of intensional entities as a naming convenience. We do so because we want to talk about these classes as if they "existed" in possible worlds without having to mention which particular elements of the class exist in those worlds (all of them). So language naturally induces us to think about these classes as entities themselves, even though I see no reason to deny that they are anything but mental concoctions.

### **Truthmaker representations**

We also need not be limited to an account of truthmakers as equivalence classes of entities. In fact ultimately in our theory we will want to *define* extensional entities as open events rather than to take the concept of entity as primitive, so it would also not be expedient to consider truthmakers merely as equivalence classes. As promised we want to show that they can be represented as the non-empty open sets of possible worlds of some topological space. We **TODO**

For all mathematical intents and purposes then, a truthmaker $x$ in our theory will be identified with the unique set of all possible worlds in which $x$ can be said to exist, i.e. the event of $x$ existing. Existential entailment between entities ($\rArr$) then reduces to set membership ($\sube$) between these events which are now identified with truthmakers, and equality of truthmakers reduces to equality between sets. 

<!-- Notice also that the association of truthmakers with events is injective. -->

Which events should be taken to represent truthmakers? As should perhaps be obvious by now, only the open sets of the space will suffice for this task, since the event $[\square \varphi]$ of a truthmaker for a proposition $\varphi$ existing is open, and this can naturally be regarded as the union of all existential events that are individual truthmakers of $\varphi$, just as the proposition $\square \varphi$ can naturally be regarded as a disjunction of propositions each of which expresses the existence of a specific truthmaker of $\varphi$. However we should not expect any of these events to be empty, for then the associated individual would not exist in any possible world, and hence we should expect that only non-empty open events are truthmakers.

To make a clearer argument as to why this interpretation must be accepted, consider a proposition $\varphi$; we want to decide whether $\varphi$ expresses the existence of an entity, either of a particular entity, like Socrates, or an entity from a certain class, like a zebra. It is clear in either case, as we have already argued, that if a proposition of this sort is true then it must always have a truthmaker, hence it must satisfy:

$$\varphi \to \square \varphi.$$

Where by "satisfy" we mean $[\varphi \to \square \varphi]$ is the set of all possible worlds, i.e. the necessary event. Adding the axiom $T$ into this yields:

$$\varphi \leftrightarrow \square \varphi.$$

And since logically equivalent propositions are equal, this implies:

$$\varphi = \square \varphi.$$

Hence $\varphi$ is a fixed point of the operator $\square$. We then have:

$$[\varphi] = [\square \varphi] = I([\varphi]).$$

As such $[\varphi]$ is also a fixed point of the interior operator, i.e. an open set. And this will be true not only for propositions expressing the existence of particular entities, but also the existence of entities of a class.

Notice however that $\bot$ also satisfies this axiom schema, for $\bot \to \square \bot$ is a tautology provable from the application of the *ex falso quodlibet* principle of logic. In one sense, $\bot$ may be taken also to be an example of existential proposition, for it may be paraphrased as "There exists a circle which is also a square". In another sense however we must be careful with this association, for the event $[\bot]$ is empty and as such can be associated to no real individual. But it might be taken to be associated with all the impossible non-entities that one could think of.

We have proven that any proposition $\varphi$ expressing an existential claim must satisfy the axiom $\varphi \to \square \varphi$ and as such be associated an open event $[\varphi]$. But arguably we have not yet proven the converse: that any proposition whatsoever, provided only it is not necessarily false, satisfying $\varphi \to \square \varphi$ must be existential. This remains to be proven because if a non-existential proposition which might be true were to also satisfy this, then some non-empty open events would be non-existential.

We consider then that any proposition for which $\varphi \to \square \varphi$ is necessarily true can be paraphrased as "There exists a truthmaker of $\varphi$" for $\varphi$ is true if and only if it has a truthmaker, as we argued above, and so it must be logically equivalent to this paraphrase; in which case as propositions they are also equal. We can then take $\varphi$ to be an existential proposition much in the same sense as we took "zebras exist" to be one, provided only that there is at least one possible truthmaker of $\varphi$, which is to say that $[\varphi] \neq \empty$, or that $\varphi$ is not necessarily false. In this case however, $\varphi$ affirms the existence of one entity in a class of entities (the truthmakers of $\varphi$) which is defined in terms of $\varphi$, so this might seem odd compared to the example of zebras. And yet nothing keeps us from defining a zebra, in the nominal sense, or for the purposes of mathematical argument, as a truthmaker of the proposition "zebras exist". There is no reason to suspect that the class of truthmakers of $\varphi$ could also not be defined in terms independent of $\varphi$; it is actually very much irrelevant either way, from a logical point of view, whether it can or cannot.

A minor issue remains to be resolved for our argument to be complete; namely, the argument intends to show that every non-empty open set in the image of the association [ ] is an existential event, but this is not enough to show that every non-empty open set is an existential event, for the association [ ] would perhaps not be surjective, and should not even be expected to be so if the number of possible worlds is infinite and the number of propositions in the calculus is countable, as is to be expected for a formal language. In that case it would be impossible for [ ] to be surjective.

But here we must say we are not really concerned with keeping our calculus countable, or even with investigating any logical property within the calculus itself. We began by considering the calculus because we deemed it to be the easiest way, among many other alternatives, to introduce the notion of modeling possible entities as non-empty open sets of a space of possible worlds. We could just as well have argued from a variety of purely topological approaches and never have bothered mentioning $S4$ at all. In one approach, we could simply argue that since any topology on a set is equivalent to a Kuratowski Interior operator defined on its Powerset, if we interpret the points in the space as worlds, the sets as propositions, and the interior operator as assigning to each proposition $\varphi$ the proposition $\square \varphi$ which states that "$\varphi$ has a truthmaker" then naturally the open sets would be precisely the existential propositions/events emerging as fixed points of the operator $\square$, and any nitpicky objection about logic wouldn't even make sense. We have chosen to start with $S4$ for the simplicity of the exposition of its axioms, and for the popularity of the system; but here onwards we might as well change our approach to a more semantic / model theoretic one.

In a nutshell our argument is:

- A proposition (modulo $\leftrightarrow$) expresses the existence of an entity if and only if it is a fixed point of the operator $\square$.
- Every event has an (unique) associated proposition.
- An event is open if and only if its associated proposition is a fixed point of the operator $\square$.
- A non-empty event is existential, i.e. associated with an individual, (and can for all intents and purposes be taken to *be* an individual) if and only if its associated proposition expresses the existence of an entity.

**Therefore** a non-empty event is open if and only if it is existential.

The first premiss we have proven, the second can always be assumed since we might for all intents and purposes define an event to be a proposition (the proposition that the event occurs) or define a proposition to be an event (the event that the proposition is true); and the third is a simple mathematical theorem about interior algebras. Namely, it might be taken to be this:

**Theorem:** If $f: A \to B$ is a bijective interior algebra homomorphism and $x \in B$, then $x$ is a fixed point of $\square_B$ if and ony if $f^{-1}(x)$ is a fixed point of $\square_A$. 

A generalization of the theorem works for any kind of algebraic structure and is ultimately a corollary of a simple theorem of universal algebra, so we leave as an exercise to the reader to prove this particular version, if he so desires.

With regards to the fourth, it comes from our general identification of individuals with the set of the possible worlds in which they exist. Just as we can identify propositions and events, and existential propositions to open events, we can also identify individuals with existential events, and we do so if and only if the associated proposition of the existential event is existential and not necessarily false.

## **Truthmakers as Facts**

The reader may be somewhat perplexed that we have taken up as being part of the same class of "existential" propositions, both the ones postulating the existence of a particular individual, as well as the ones claiming one in a broader class of individuals must exist. Indeed, according to the right-hand side ($\lArr$) of the implication of the fourth premiss of our argument, to the proposition "zebras exist" there must correspond some distinct individual which exists in every possible world in which there are zebras. This individual we may take to be the universal of "zebrality", or simply the set/totality of all zebras. This is necessary if we are to consider all possible open sets of possible worlds to be individuals. 

If however one is feeling particularly nominalistic and is unwilling to accept this, if he accepts at least that every proposition which expresses the existence of a singular individual, described by a proper name like "Socrates", should be associated an existential event (e.g. that of Socrates existing), then it should follow that at least some basis of open sets of the space correspond to individuals, and every other open set would correspond to sets / totalities of individuals. The difference here between the nominalist position and the realist one is that realism is mathematically more general, as it does not require us to equip the topological space of worlds with a basis of open sets which we arbitrarily take to be individuals. Nevertheless, if one does want to pursue the nominalist direction, it will probably still be consistent with the rest of what we have to say. 

If the premisses are fully accepted, it follows necessarily and trivially that, for all intents and purposes of any extensional ontological theory which takes existential equivalence as the criteria of identity, individuals ***are*** open sets of a topological space of possible worlds. We shall see shortly that this assumption is also very fruitful for the mathematical modeling of metaphysical systems, and take its applicability as further proof of its validity.

## **Dense entities as Substances**

If it is accepted as reasonable to model extensional possible entities (truthmakers) as open sets of a space of possible worlds, we must ask which possible entities are substances and which are accidents. And for this it is better to move the argument to a purely topological setting. Henceforth we shall also use the terms "entity" and "truthmaker" interchangeably, and these will always refer to non-empty open sets of possible worlds.

<!-- specially since the monadic logic $S4$ will not be enough to define a dense set (altough it could be achieved using multimodal logic, but this is an unimportant detail). [Maybe use as footnote] -->

The simplest argument we can provide to the extent that "substances", which we consider synonymous with "concrete objects" in modern parlance, must be considered dense open events is to rely on a characterization Aristotle himself has made of them in the *Categories*. There he says:

[**TODO**]


## **Physical and Metaphysical substances**

We must consider also in our topological exposition of metaphysics the ontological meaning of many other topological properties. **TODO**

## **When can we say that a necessary being is God?**

## **Some examples of ontologies**

## **Truthmakers and Intuitionism**

It should perhaps not have escaped the attentive reader with a background in logic, that our truthmaker interpretation of the $S4$ box operator
is but a minor variant of the intuitionist interpretation of this operator. **TODO**

## Conclusion

**TODO**

A major feature of our system that we have left out of this discussion is that substances have *possible states* they can be in. It is already possible, given our discussion, to give a precise definition of the state space of a singular substance as a quotient space of the space of possible worlds in a natural way. This opens up the possibility for a category-theoretical analysis of the state spaces so generated, and the definition of many other interesting (Aristotelian) philosophical concepts can be taken up based on this approach. This shall be the subject of our next article. As an aside from the philosophical discussion, it is quite possible that this sort of interpretation could have some importance in the theoretical development of databases, as we could interpret dense truthmakers to be possible objects in an object oriented database, possible worlds as states of the database, and states of objects as the particular attribute values that an object has in a given state of the database, e.g. a single row in a data table. This idea will probably have some merit if we can extend the semantics of propositional $S4$ to a quantified version of $S4$, so that we can use predicate logic as a description logic for database schemas.

<!-- Talking point: point out here this is an extensional ontological theory, and that maybe some things could be done with intensional theories that could expand this one while remaining consistent with it, for any intensional theory will be able to generate an extensional theory based on existential equivalence as identity criteria. -->

<!-- Talking point: talk about ontological counterparts. Justify the name "counterpart" by analogy with Lewis and how his relation of "resemblance" has something to do with the "adequacy" relation between the intellect and the "thing", i.e. between truthbearer and truthmaker. -->