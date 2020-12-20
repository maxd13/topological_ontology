import alexandroff_space
universe u
open set topological_space classical
local attribute [instance] prop_decidable

/-! 

# A topological formal ontology and foundation of philosophy

The purpose of this work is to implement an 
upper level ontology that minimizes the number of primitive terms and axioms,
while maximizing explanatory power with regards to the interpretability of 
philosophical concepts in the theory. We seek to give to the whole of philosophy the same sort
of rigorous foundation that set theory gives to mathematics, in terms of possible entities and possible
worlds.

Among other things, we seek to precisely define in our theory the concepts of: substance, physical substance,
metaphysical substance, accident, concept, universal, property, positive property, the process of abstraction,
matter, form, the categories of being, the predicaments, essence and existence, causality, parthood, God, theism,
atheism, physicalism, monism, pantheism, eleaticism, platonism, modal realism.
We also seek to formalize theories of: causality, mereology,
epistemology, ethics, philosophy of nature, metaphysics and natural theology. 
All of it based on the foundation of possible worlds and possible entities.

Pretty audacious, ain't it?

I am actually undecided about whether I need a theory of counterfactuals. 
But anyone should be able to create his own theory of counterfactuals based on these foundations,
if he so wishes.

## Ontologies and Events

The fundamental concept on which all of our work is based upon, is the concept of an *ontology of possible worlds*.
Which is to be comprised of a Type of possible worlds equipped with some fundamental topological structure, 
the philosophical significance of which shall be made clear shortly.

The notion of possible world is of course a primitive one, and you may interpret it as you will. 
We take a possible world in our theory to be a point in the phase space of the whole of possible reality,
a fully qualified description of a possible state of existence, 
the outcomes of the most general random experiment one could possible make, etc...

More importantly, given this primitive notion we can readily define the notion of an ontological 
**Event** as simply a set of possible worlds; the notion should be familiar to those acquainted 
with probability theory (probability spaces). An event is something that "happens" or "occurs", 
precisely in the possible worlds which compose it, i.e. an event is the set of all possible worlds in which
the event occurs. We would like to talk a little bit about events before delving into the mathematical definitions.

Another way to see an event is as (the semantic content of) a proposition. 
Not all events are necessarily propositions 
(because we could have uncountably many events, but countably many propositions) 
but every proposition is to be associated with an event: 
the set of all possible worlds in which the proposition is true.
For instance the proposition "Socrates exists" corresponds to the event {w : world | Socrates exists in w}.

Now, it is quite clear that some propositions "talk about" or postulate one or more things existing, while others do not. 
"Socrates exists" clearly postulates the existence of Socrates, just as "Humans exist" postulates the existence of 
Human beings, and "Socrates and Plato exist" postulates the existence of both Plato and Socrates, etc... 
On the other hand, "Unicorns do not exist", does not seem to postulate or "talk about" 
the existence of anything, but merely about the *absence* of an existence. 
So there is quite clearly a primitive notion of which propositions 
talk about existence and which do not. 

For the sake of generality we can take this notion to apply to all events regardless
of whether they are proposition or not, and stop talking about propositions altogether.
So an event will be **existential** or **open** 
precisely when its occurrence postulates that one or more entities from a set of entities must exist,
which is to say that the event can only occur in a possible world if those entities it postulates 
do exist in that possible world.

Now, as we have already exemplified, we should expect that arbitrary set unions of existential 
events be existential events, since the event "(Some)Humans exist" is the union of all events of the form
"X exists" for any possible human X. The same should apply for intersections, since "All possible humans exist" 
is the intersection of "X exists" for any possible human X. An generally speaking, for any arbitrary family
of existential events, we should exp


-/

-- An `ontology` is a nonempty T0 topological space
-- of possible worlds.
class ontology :=
    (world : Type*)
    [wne : nonempty world . tactic.apply_instance]
    [t : topological_space world . tactic.apply_instance]
    -- identity of indiscernibles for possible worlds
    [axiom₀ : t0_space world . tactic.apply_instance]


instance ontology_top  (ω : ontology)  : topological_space ω.world := ω.t
instance ontology_ne  (ω : ontology)  : nonempty ω.world := ω.wne
instance ontology_t0  (ω : ontology)  : t0_space ω.world := ω.axiom₀

-- Events in an ontology are simply sets of worlds.
-- Events (informally) are said to `occur` precisely in their element worlds.
@[reducible, alias]
def ontology.event (ω : ontology) := set ω.world 

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
     (postulate₃ : alexandroff_discrete ω)

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
 
 -- We define the related topological notions for events.
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
 -- also called boundary
 @[reducible]
 def event.frontier := frontier e

 -- necessity and contingency
 def event.contingent := e ≠ univ
 def event.necessary := e = univ
  
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

