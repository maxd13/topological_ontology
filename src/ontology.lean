import math.alexandroff_space
open set topological_space classical
local attribute [instance] prop_decidable

/-! 

# A topological formal ontology and foundation of philosophy

The purpose of this work is to implement in the Lean Theorem Prover an 
upper level ontology that minimizes the number of primitive concepts and axioms,
while maximizing explanatory power with regards to the interpretability of 
philosophical concepts in the theory. We seek to give to the whole of philosophy the same sort
of rigorous foundation that set/type theory gave to mathematics, without having to rely
on the introduction of a primitive concept for almost every new concept of philosophy. 
The most basic version of our theory admits of only two primitives: possible worlds and existential events,
everything else being defined in terms of those, in much the same way that everything in mathematics can be
defined in terms of the primitive notions of set and set-membership. 
We name our theory simply as the **Topological Ontology**.

Among other things, we seek to precisely define in our theory the concepts of: substance, simple substance, 
composite substance, physical substance, metaphysical substance, accident, property, positive property,
essence and existence, causality, parthood, God, theism,
atheism, physicalism, monism, pantheism, eleaticism, platonism, modal realism, etc...
We also seek to formalize theories of: causality, counterfactuals, mereology,
epistemology, ethics, philosophy of nature, metaphysics and natural theology. 

And in a higher order extension of our theory, we also seek to define: concept/abstract object, 
the process of abstraction, universal, matter, form, the categories of being, the predicaments, etc...

All of it based on the foundation of possible worlds and existential events. Pretty audacious, ain't it?

## Ontologies and Events

The fundamental concept upon which all of our work is based, is the concept of an *ontology of possible worlds*.
Which is to be comprised of a Type of possible worlds equipped with some fundamental topological structure, 
the philosophical significance of which shall be made clear shortly.

The notion of possible world is of course a primitive one, and you may interpret it as you will. 
We take a possible world in our theory to be a point in the phase space of the whole of possible reality,
a fully qualified description of a possible state of existence, 
an outcome of the most general random experiment one could possible think of, etc... 

For simplicity, we  will also consider that possible worlds are *atomic truth-indexers*. This is to say that 
they are truth-indexers, i.e. things with respect to which propositions are said to be true or false 
(*tertium non datur*) but which cannot be thought to be composed of further things which have this property. 
In particular, our possible worlds will not have any intrinsic temporal or spatial structure, so it will simply
*not make sense* at first to say that some event like "Socrates is sitting" will occur in 
the future of a possible world `w`, it will not make sense to claim "Socrates will sit in the future" is true at `w`,
at least initially. Later on, by equipping our topological space of possible worlds with additional temporal structure,
we *will* be able to make sense of these claims by defining timelines in terms of continuous paths of possible worlds.
In this manner we can think of possible worlds as being possible spatio-temporal locations in possible space-times
rather than as being space-times themselves; since if they were space-times they could be thought to be composed 
of points which would themselves be truth-indexers, and so our possible worlds would not be atomic truth-indexers. 
This seems to be a much simpler foundation to build upon than assuming that, somehow,
possible worlds should have some intrinsic temporal structure, which would be very hard 
to define right from the start.  

Perhaps more importantly, given this primitive notion we can readily define the notion of an ontological 
**Event** as simply a set of possible worlds; the notion should be familiar to those acquainted 
with probability theory (probability spaces). An (not necessarily "random") event is something that "happens" or "occurs", 
precisely in the possible worlds which are its elements, i.e. an event is the set of all possible worlds in which
the event occurs. We would like to talk a little bit about events before delving into the mathematical definitions.

Another way to see an event is as the semantic content of a proposition. 
Not all events are necessarily propositions because,
perhaps, we could have uncountably many events, but countably many propositions.
However every proposition is to be associated with an event: 
the set of all possible worlds in which the proposition is true.
For instance the proposition "Socrates exists" corresponds to the event {w : world | Socrates exists in w}.

Now, it is quite clear that some propositions "talk about" or postulate one or more things existing, while others do not. 
"Socrates exists" clearly postulates the existence of Socrates, just as "Humans exist" postulates the existence of 
Human beings, and "Socrates and Plato exist" postulates the existence of both Plato and Socrates, etc... 
On the other hand, "Unicorns do not exist", does not seem to postulate or "talk about" 
the existence of anything, but merely about the *absence* of an existence. 
So there is quite clearly a primitive notion of which propositions 
talk about existence and which do not. I would not want to reduce this notion
to merely "using an existential quantifier in formal language X" because I do 
not want to assume anything about the syntactical makeup of propositions in the first
place.

For the sake of generality, simplicity, and removing from our formal system the unnecessary concept of what a 
"proposition" is supposed to be, we can take this notion to apply to all events regardless
of whether they are propositions or not, and stop talking about propositions altogether.
So an event will be **existential** or **open** 
precisely when its occurrence postulates that one or more entities from a set of entities must exist,
which is to say that the event can only occur in a possible world if those entities it postulates 
do exist in that possible world.

Now, as we have already exemplified, we should expect that arbitrary set unions of existential 
events be existential events, since the event "(Some)Humans exist" is the union of all events of the form
"X exists" for any possible human X. The same should apply for intersections, since "All possible humans exist" 
is the intersection of "X exists" for any possible human X. And generally speaking, regardless of the 
particular notion of "existential event" that we adopt, we should expect the set of all existential events to be 
closed by arbitrary unions and intersections. 

However, although plausible,
this amounts to assuming more than what we actually need to develop our theory. 
For the purposes of our theory, we will only really be committed to the claim that 
*finite* intersections of existential events are existential events, rather than
claiming that this works for *arbitrarily large* intersections. 
This latter assumption we will denominate, for very sound mathematical reasons, the **Alexandroff Postulate**,
and we will neither affirm nor deny it, though we might occasionally derive some conclusions from its assumption.

Furthermore, we should also assume that both the set of all possible worlds, i.e. the **necessary event**
and the empty set of worlds, i.e. the **impossible event**, are both
existential events. There are many ways to argue this point, the simplest one seems to consist in the
consideration that the proposition "Something (whatsoever) exists" should be associated to the necessary event,
and that the proposition "A squared-circle exists" should be associated to the impossible event. In that case,
it is clear that these events postulate the existence of some things.

It is however clear that we need not assume that the set complements of existential events are existential for, as we 
have previously exemplified, "Unicorns do not exist" is not existential, even though it is the complement, or negation, of 
"Unicorns exist", which is clearly existential.

We are also going to assume, as the only real axiom in our theory, that there is an extensionality
principle for possible worlds: possible worlds worlds in which exactly the same existential events occur
are equal. This will allow us to think of possible worlds as the sets of possible entities which exist
in that particular world, so that if two worlds are to be distinct, at least one entity would have to exist in one
which does not exist in the other. This can be seen as the "identity of indiscernibles" principle
applied to possible worlds. It might turn out however that for many applications we won't even need this axiom,
so we might consider turning it into a postulate if the need arises, but as of now it looks like such a simple
assumption that it makes sense to include it as an axiom.

Now, we shall not explain here the mathematics involved, but 
a competent mathematician should already be able to conclude that what
we are assuming is that existential events constitute a T₀-topology of 
possible worlds. 
This leads us to the very first formal definitions of our theory:

-/

/-- An `ontology` is a nonempty T₀ topological space
of possible worlds. -/
class ontology :=
    (world : Type*)
    [wne : nonempty world]
    [t : topological_space world]
    -- identity of indiscernibles for possible worlds
    [axiom₀ : @t0_space world t]

instance ontology_top  (ω : ontology)  : topological_space ω.world := ω.t
instance ontology_ne  (ω : ontology)  : nonempty ω.world := ω.wne
instance ontology_t0  (ω : ontology)  : t0_space ω.world := ω.axiom₀

/-- **Events** in an ontology are simply sets of possible worlds.
 Events (informally) are said to **occur** precisely in their element worlds. -/
@[reducible]
def ontology.event (ω : ontology) := set ω.world

/-- **Existential** `events` in an ontology are open sets of possible worlds. -/
@[reducible]
def ontology.event.existential {ω : ontology} (e : ω.event) := is_open e

/-! 

# Intensionality and Extensionality

A fundamental question in any ontological theory is that of
whether the basic entities that the theory postulates have a clearly
defined identity criteria or whether their identity should be assumed 
to be a primitive concept. This amounts to asking whether the entities
in the theory admit an *extensionality* principle, such as the
one admitted for sets, or whether no such extensionality principle is admitted.
We can readily call 

-/


-- intensional ontologies
structure iontology extends ontology :=
    (entity : Type*)
    [ene : nonempty entity . tactic.apply_instance]
    (map : entity → to_ontology.event)
    (axiom₁ : t = (generate_from $ range map))

-- (algebraic) realism for intensional ontologies
class iontology.realist (Ω : iontology) : Prop :=
    (postulate₀ : Ω.t.is_open = (range Ω.map))

namespace ontology

section ontology
 
 variable (ω : ontology)

 -- However the least we should assume for an ontology to be worthy of consideration as being
 -- the true ontology is that we can add or remove entities from its worlds, therefore, we add
 -- the following definitions:
 
 class viable : Prop :=
     (postulate₁ : ∀ w : ω.world, ∃ w', w < w' ∨ w' < w)
 
 -- common (sensical) ontologies
 class common extends viable ω : Prop :=
     (postulate₂ : uncountable ω.world)
 
 def alexandroff_discrete := alexandroff_space ω.world
 
 class alexandroff extends common ω:=
     (postulate₃ : ω.alexandroff_discrete)

--  -- ω is generated by the intensional map.
-- class ontology.intensional (ω : ontology) (f : intensional_map) : Prop :=
--     (intensional : ∃ h : f.world = ω.world, 
--                     let t := f.top
--                     in by rw h at t; exact t = ω.t
--     )

-- -- ω is an extensional interpretation of a pre-existing ontology
-- class ontology.intensionalizable (ω : ontology) (intensional_entities : Type*) : Prop:=
--     ( intensionalizable : ∃ f : intensional_map, 
--       f.entity = intensional_entities ∧ 
--       ω.intensional f
--     ) 

end ontology

variable {ω : ontology}

-- We introduce first the notion of events. 
section events
 
 variable (e : ω.event)
 
 -- We define the related topological notions for events:
 @[reducible]
 def event.interior := interior e
 @[reducible]
 def event.closure  := closure e
 @[reducible]
 def event.dense := closure e = univ
 @[reducible]
 def event.exterior : ω.event := interior (-e)
 @[reducible]
 def event.regular := e = e.exterior.exterior
 /-- also called `boundary` -/
 @[reducible]
 def event.frontier := frontier e

 -- necessity, contingency, impossibility
 @[reducible]
 def event.contingent := e ≠ univ
 @[reducible]
 def event.necessary := e = univ
 @[reducible]
 def event.impossible := e = ∅

  
end events

-- And we prove some simple useful lemmas about them 
section event_lemmas

 variable {e : ω.event} 
 lemma event_union_exterior_open : is_open e → is_open (e ∪ e.exterior) :=
    begin
      intro h,
      apply is_open_union h,
      simp [event.exterior],
    end

 -- For some reason in the standard library there is a lemma
 -- like this for finsets but not one for sets.
 lemma event_nonempty_of_ne_empty : e ≠ ∅ → e.nonempty :=
    begin
        intro h,
        simp [set.nonempty],
        classical,
        by_contradiction h₂,
        replace h₂ := forall_not_of_not_exists h₂,
        simp at h₂,
        replace h₂ := eq_empty_iff_forall_not_mem.2 h₂,
        contradiction,
    end

 lemma event_union_exterior_nonempty : (e ∪ e.exterior).nonempty :=
    begin
       apply event_nonempty_of_ne_empty,
       intro h,
       simp at h,
       obtain ⟨h₁, h₂⟩ := h,
       rw h₁ at h₂,
       simp [event.exterior] at h₂,
       have c := ω.wne,
       contradiction,
    end

end event_lemmas

-- We define entities to be particular kinds of events.
section entities 
 
 -- Particular (possible) `entities` in the ontology are nonempty open sets of worlds.
 -- An entity is said to `exist` precisely in those worlds which are its elements.
 structure entity (ω : ontology) :=
      -- the event of the entity existing
      (exist : ω.event)
      (is_open : is_open exist)
      (ne : exist.nonempty)

 -- main extensionality lemma for entities.
 @[ext]
 lemma entity.ext {e₁ e₂ : ω.entity} (h : e₁.exist = e₂.exist) : e₁ = e₂ := sorry
  
 variables (e e₁ e₂ : ω.entity)
 
 -- Two entities are `contrary` if their intersection (as sets) is empty,
 -- they are otherwise `compatible`.
 @[reducible]
 def entity.contrary := e₁.exist ∩ e₂.exist = ∅
 @[reducible]
 def entity.compatible := (e₁.exist ∩ e₂.exist).nonempty
 
 -- Some very important entities have no contraries
 @[reducible]
 def entity.nocontrary := ¬ ∃ y, e.contrary y
 
 -- Entity x is said to existentially entail entity y,
 -- or to existentially depend on y,
 -- if in every possible world in which x exists, y exists.
 -- For this relation we use the subset notation.
 
 instance entity.has_subset : has_subset ω.entity := 
      ⟨λ x y : ω.entity, x.exist ⊆ y.exist⟩

 -- The necessary being (entity) is the entity which exists in
 -- every possible world.
 def nbe (ω : ontology) : ω.entity := ⟨univ,is_open_univ, by simp [empty_ne_univ]⟩
 
 -- An entity is `contingent` if it is not the necessary being.
 def entity.contingent := e ≠ ω.nbe
 -- And otherwise necessary
 def entity.necessary := e = ω.nbe

 -- Here are some definitions which look more like lemmas,
 -- these ones are more philosophical.
 
 -- Arbitrary nonempty unions of entities are entities.
 def entity_Sup (s : set ω.entity) (h : s.nonempty) : ω.entity :=
   begin
      fsplit,
          exact ⋃ i ∈ s, entity.exist i,
      apply is_open_bUnion,
      intros i H,
      exact i.is_open,
          simp [set.nonempty],

      let i := h.some,
      let w := i.ne.some,
      existsi w,
      existsi i,
      constructor,
        exact h.some_mem,
        exact i.ne.some_mem,
   end
  
 -- Nonempty finite intersections of entities are entities
 def entity.inter (h : e₁.compatible e₂) : ω.entity :=
      ⟨  e₁.exist ∩ e₂.exist
      , is_open_inter e₁.is_open e₂.is_open
      , h
      ⟩
  
 -- We can also talk about an entity existing in a world
 -- as belonging to it, so we can use the notation e ∈ w.
 @[reducible]
 instance world.has_mem : has_mem ω.entity ω.world := ⟨λe w, w ∈ e.exist⟩
 @[reducible]
 def world.entities (w : ω.world) := {e : ω.entity | e ∈ w}

end entities

-- We now talk about analogical (fuzzy) events, or "avents".
-- OBSERVATION: We could have called them aevents, which would be in keeping with our naming style.
-- But then since in Latin this just sounds like "events" we preferred to invent a new word.
section avents

-- [0, 1] interval
def I := Icc (0 : ℝ) 1

@[reducible, alias]
def avent (ω : ontology) :=  ω.world → I 

end avents

end ontology

