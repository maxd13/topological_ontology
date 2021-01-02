import math.alexandroff_space math.notation
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
structure ontology :=
    (world : Type*)
    [wne : nonempty world]
    [t : topological_space world]
    -- identity of indiscernibles for possible worlds
    [axiom₀ : @t0_space world t]

instance ontology_top  (ω : ontology)  : topological_space ω.world := ω.t
instance ontology_ne  (ω : ontology)  : nonempty ω.world := ω.wne
instance ontology_t0  (ω : ontology)  : t0_space ω.world := ω.axiom₀

/-- **Events** in an ontology are simply sets of possible worlds.
 Events are said to **occur** at their element worlds. -/
@[reducible]
def ontology.event (ω : ontology) := set ω.world

/-- **Existential** `events` in an ontology are open sets of possible worlds. -/
@[reducible, simp]
def ontology.event.existential {ω : ontology} (e : ω.event) := is_open e

-- We will start developing the most basic conclusions of the theory:
namespace ontology

variable {ω : ontology}

-- We develop further the notion of events. 
section events
 
  variable (e : ω.event)

  @[reducible, simp]
  def event.occurs (w : ω.world) := w ∈ e

  -- We define the related topological notions for events:

  /-- the **ground**, or *ontological counterpart* of an `event e` is its interior, 
      i.e. the largest existential event below `e` -/
  @[reducible, simp]
  def event.ground : ω.event := interior e
  @[reducible, simp]
  def event.closure : ω.event := closure e
  @[reducible, simp]
  def event.dense : Prop := closure e = univ
  @[reducible, simp]
  def event.exterior : ω.event := interior (-e)
  @[reducible, simp]
  def event.regular : Prop := e = e.exterior.exterior
  /-- also called `boundary` -/
  @[reducible, simp]
  def event.frontier : ω.event := frontier e
  /-- also called `frontier` -/
  @[reducible, simp, alias]
  def event.boundary : ω.event := e.frontier
  @[reducible, simp]
  def event.connected : Prop := is_connected e

  -- necessity, possibility, impossibility, contingency
  @[reducible, simp]
  def event.necessary := e = univ
  @[reducible, simp]
  def event.possible := e.nonempty
  @[reducible, simp]
  def event.impossible := ¬e.possible
  @[reducible, simp]
  def event.contingent := e.possible ∧ ¬e.necessary

  /-- An `event` is **groundable** if its ground is `possible` -/
  @[reducible, simp]
  def event.groundable := e.ground.possible

  -- Setting up notation:

  /-- Use `□e` for "`e` is necessary" -/
  @[reducible, simp]
  instance has_box_event : has_box ω.event := ⟨event.necessary⟩

  /-- Use `◾e` for "the ground of `e`" -/
  @[reducible, simp]
  instance has_black_box_event : has_black_box ω.event := ⟨event.ground⟩

  /-- Use `⋄e` for "`e` is possible" -/
  @[reducible, simp]
  instance has_diamond_event : has_diamond ω.event := ⟨event.possible⟩

  /-- Use `✦e` for "the event of nothing precluding `e` from happening", or `-◾-e` -/
  @[reducible, simp]
  instance has_black_diamond_event : has_black_diamond ω.event := ⟨event.closure⟩

  /-- Use `~e` for "the exterior of `e`" -/
  @[reducible, simp]
  instance has_tilde_event : has_tilde ω.event := ⟨event.exterior⟩

  /-- Use `e₁ ⇒ e₂` instead of `e₁ ⊆ e₂`, replace with `⇒'` for `⊂` -/
  @[reducible, simp]
  instance has_entailment_event : has_entailment ω.event := ⟨set.subset⟩

  /-- Use `e₁ ▹ e₂` instead of `-e₁ ∪ e₂` 
      Use `e₁ ≡ e₂` instead of `(e₁ ▹ e₂) ∩ (e₂ ▹ e₁)`
      Use `e₁ ≢ e₂` instead of `-(e₁ ≡ e₂)` -/
  @[reducible, simp]
  instance has_local_entailment_event : has_local_entailment ω.event := ⟨λ e₁ e₂, -e₁ ∪ e₂⟩

  --tests:
  -- variables (e₁ e₂ : ω.event)
  -- #check □e
  -- #check ◾e
  -- #check ⋄e
  -- #check ✦e
  -- #check ~e
  -- #check e₁ ⇒ e₂
  -- #check e₁ ⇒' e₂
  -- #check e₁ ▹ e₂
  -- #check e₁ ≡ e₂
  -- #check e₁ ≢ e₂
  -- example : e.groundable ↔ ⋄◾e := by simp

end events

-- And we prove some simple useful lemmas about them 
section event_lemmas

  variable {e : ω.event} 
  lemma event_union_exterior_open : e.existential → (e ∪ ~e).existential :=
    by intro h; apply is_open_union h; simp

  -- For some reason in the standard library there is a lemma
  -- like this for finsets but not one for sets.
  lemma event_possible_of_ne_empty : e ≠ ∅ → ⋄e :=
    begin
        intro h,
        simp [set.nonempty],
        by_contradiction h₂,
        push_neg at h₂,
        replace h₂ := eq_empty_iff_forall_not_mem.2 h₂,
        contradiction,
    end

  lemma event_union_exterior_possible : ⋄(e ∪ ~e) :=
    begin
        apply event_possible_of_ne_empty,
        intro h,
        simp at h,
        obtain ⟨h₁, h₂⟩ := h,
        rw h₁ at h₂,
        simp at h₂,
        have c := ω.wne,
        contradiction,
    end

  @[simp]
  lemma existential_iff_ground_eq : e.existential ↔ e = e.ground := 
    begin 
      simp, 
      symmetry, 
      constructor; intros h,
        symmetry' at h,
        exact interior_eq_iff_open.mp h,
      symmetry,
      exact interior_eq_iff_open.2 h,
    end

end event_lemmas

-- We define (extensional) possible entities to be particular kinds of events, so
-- that existence is a special case of occurrence. 
-- We defer full philosophical explanation to the "Intensionality and Extensionality" section.
section entities
 
  /-- Particular (possible, extensional) `entities` in the ontology are nonempty open sets of possible worlds.
      An entity is said to `exist` precisely at the worlds which are its elements. -/
  structure entity (ω : ontology) :=
    -- the event of the entity existing ("exists" is a reserved word)
    («exists» : ω.event)
    (existential : exists.existential)
    (possible : ⋄«exists»)

  /-- the event of the `entity` existing -/
  add_decl_doc entity.exists

 /-- main extensionality lemma for entities. -/
 @[ext]
 lemma entity.ext {e₁ e₂ : ω.entity} (h : e₁.exists = e₂.exists) : e₁ = e₂ := 
    by casesm* ω.entity; simp at h; simpa
  
 variables (e e₁ e₂ : ω.entity)
 
 -- Two entities are `contrary` if their intersection (as sets) is empty,
 -- they are otherwise `compatible`.
 @[reducible]
 def entity.contrary := e₁.exists ∩ e₂.exists = ∅
 @[reducible]
 def entity.compatible := (e₁.exists ∩ e₂.exists).nonempty
 
 -- Some very important entities have no contraries
 @[reducible]
 def entity.nocontrary := ¬ ∃ y, e.contrary y
 
 -- Entity x is said to existentially entail entity y,
 -- or to existentially depend on y,
 -- if in every possible world in which x exists, y exists.
 -- For this relation we use the subset notation.
 
 instance entity.has_subset : has_subset ω.entity := 
      ⟨λ x y : ω.entity, x.exists ⊆ y.exists⟩

 -- The necessary being (entity) is the entity which exists in
 -- every possible world.
 def nbe (ω : ontology) : ω.entity := ⟨univ,is_open_univ, by simp [empty_ne_univ]⟩

 -- An entity is `contingent` if it is not the necessary being.
 -- TODO: revise whether mayber we shouldn't define this in terms of the definition for events.
 -- and see if this change doesn't break anything.
 def entity.contingent := e ≠ ω.nbe
 -- And otherwise necessary
 def entity.necessary := e = ω.nbe

 lemma nbe_unique : ∃! e : ω.entity, e.necessary := sorry


 -- Here are some definitions which look more like lemmas,
 -- these ones are more philosophical.
 
 -- Arbitrary nonempty unions of entities are entities.
 def entity_Sup (s : set ω.entity) (h : s.nonempty) : ω.entity :=
   begin
      fsplit,
          exact ⋃ i ∈ s, entity.exists i,
      apply is_open_bUnion,
      intros i H,
      exact i.existential,
          simp [set.nonempty],

      let i := h.some,
      let w := i.possible.some,
      existsi w,
      existsi i,
      constructor,
        exact h.some_mem,
        exact i.possible.some_mem,
   end

   noncomputable instance has_Sup_entity : has_Sup ω.entity := 
    ⟨λ s, if h : s.nonempty then entity_Sup s h else ω.nbe⟩
  
 -- Nonempty finite intersections of entities are entities
 def entity.inter (h : e₁.compatible e₂) : ω.entity :=
      ⟨  e₁.exists ∩ e₂.exists
      , is_open_inter e₁.existential e₂.existential
      , h
      ⟩

end entities

-- We discuss some properties of possible worlds
section worlds

  variables (w w₁ w₂ : ω.world)

  -- We can also talk about an entity existing in a world
  -- as belonging to it, so we can use the notation e ∈ w.
  @[reducible]
  instance world.has_mem : has_mem ω.entity ω.world := ⟨λe w, w ∈ e.exists⟩
  @[reducible]
  def world.entities := {e : ω.entity | e ∈ w}

  -- extensionality principle for possible worlds
  @[ext]
  lemma world.ext {w₁ w₂ : ω.world} (h : w₁.entities = w₂.entities) : w₁ = w₂ :=
    begin
      by_contradiction contra,
      have c₀ := ω.axiom₀.t0,
      obtain ⟨U, U_open, ⟨hU₁, hU₂⟩|⟨hU₁, hU₂⟩⟩ := c₀ w₁ w₂ contra;
      clear c₀;
      have ne := nonempty_of_mem hU₁;
      let e : ω.entity := ⟨U, U_open, ne⟩,
      replace h : w₁.entities ⊆ w₂.entities, finish,
      swap,
      replace h : w₂.entities ⊆ w₁.entities, finish,
      all_goals {
        simp [world.entities, entity.exists] at h,
        specialize h e,
        simp [e, hU₁, hU₂] at h,
        contradiction,
      },
    end


end worlds

-- Here we discuss basic general properties of ontologies themselves.
section ontology
 
 variable (ω)

 -- However the least we should assume for an ontology to be worthy of consideration as being
 -- the true ontology is that we can add or remove entities from its worlds, therefore, we add
 -- the following definitions:
 
 class viable : Prop :=
     (postulate₁ : ∀ w : ω.world, ∃ w', w < w' ∨ w' < w)
 
 -- common (sensical) ontologies
 class common extends viable ω : Prop :=
     (postulate₂ : uncountable ω.world)

 def alexandroff_discrete := alexandroff_space ω.world
 
 class alexandroff extends common ω : Prop :=
    (postulate₃ : ω.alexandroff_discrete)


end ontology

/-! ## Intensionality and Extensionality

  A fundamental question in any ontological theory is that of
  whether the basic entities that the theory postulates have a clearly
  defined identity criteria or whether their identity should be assumed 
  to be a primitive relation. This amounts to asking whether the entities
  in the theory admit an *extensionality* principle, such as the
  one admitted for sets, or whether no such extensionality principle is admitted.
  We can readily call the basic entities in an extensional ontological theory 
  *extensional* entities, and likewise name the entities in an intensional theory
  *intensional* entities.

  As can be seen from the previous section, it is easy to turn our ontology into an extensional theory
  by identifying non-empty existential events to be possible extensional entities. Their
  extensionality principle is then naturally deduced from the extensionality
  principle for sets. We will indeed be primarily focusing on these entities for much of our work,
  but to demonstrate the generality of our theory we must 
  also discuss shortly the introduction of primitive intensional entities via 
  an intensional extension to our theory.

  It might indeed look somewhat controversial, to some,
  that we so readily move from existential events to "entities". 
  It may look like we are saying that entities, or at least our particular kind of
  "extensional" entities, are *nothing but* sets of possible worlds, or that nothing but
  sets of possible worlds are supposed to "exist" in our theory. This of course seems implausible
  among other things because sets are abstract mathematical objects, not concretely existing "things".
  This objection can however be resolved by understanding that, this being a mathematical theory,
  we are not really claiming that possible entities *are* nothing other than sets of possible worlds, 
  but only that these entities can be *represented* as the sets of possible worlds in which they exist.
  We are also not really committed to claiming that existence really just *is* a particular special case
  of the occurrence of events, but only that for all mathematical intents and purposes it can be so *represented*.
  We will look shortly into a way to make this representation formal by showing that any intensional ontological theory
  of possible entities naturally gives rise to our extensional topological theory in a mathematically well understood way.

-/

/-- An **Intensional ontology** is an ontology generated by a mapping of intensional entities to existential events -/
structure iontology (ω : ontology) :=
  (ientity : Type*)
  [iene : nonempty ientity]
  (map : ientity → ω.event)
  (axiom₁ : ∀ ie, (map ie).possible)
  (axiom₂ : ω.t = (generate_from $ range map))
  (axiom₃ : □ ⋃₀ range map)

namespace iontology

  section ientity

    variables {Ω : ω.iontology} (ie : Ω.ientity)

    /-- the `event` of an intensional entity existing -/
    @[reducible]
    def ientity.exists := Ω.map ie

    /-! **...**

      As can be seen, we can define an intensional ontology as a particular kind of ontology whose 
      topological structure was generated as the least topology containing the image of a map from some
      type of intensional entities to events. These events will provably be extensional entities, as we
      show bellow:

    -/
    
    lemma iexists_possible : ie.exists.possible := Ω.axiom₁ ie

    lemma iexists_existential : ie.exists.existential :=
      begin
        simp [event.existential, iontology.ientity.exists],
        dunfold is_open ontology_top,
        rw Ω.axiom₂,
        dunfold generate_from, simp,
        apply generate_open.basic,
        use ie,
      end 

    -- "up" is used for informal inheritance here
    /-- cast from `ientity` to `entity` -/
    def ientity.up : ω.entity := ⟨ie.exists, iexists_existential ie, iexists_possible ie⟩

  end ientity
  
end iontology

-- We discuss whether extensional entities are real or mere abstracta. 
section realism

  variables (e : ω.entity) (Ω : ω.iontology)

  /-! ## Real and Virtual Entities
  
    Some philosophers might furthermore be skeptical with the prospect that, for example,
    the existential event "human beings exist" 
    corresponds to some particular, unique, "extensional entity"
    which may possibly exist concretely in the world;
    i.e. the (not necessarily Platonic) universal of "Man", or Humanity.
    We make a concession to this sort of skepticism in order to make our
    system more general, and we will admit that some such extensional entities might be,
    in some sense, abstracta, figures of speech, concoctions of language, etc...
    and these we will call **virtual** entities; all other entities we shall call **real** entities. 
    Formally what will make a non-empty existential event a real entity is its belonging 
    to the image of the representation function which maps intensional possible entities to 
    their extensional representations.

  -/

  /-- An `entity` `e` is real with respect to an iontology `Ω` if there is an `Ω.ientity`
      which exists in the same possible worlds as `e`  -/
  def entity.real : Prop := ∃ ie : Ω.ientity, ie.up = e
  /-- an `entity` is virtual with respect to an iontology `Ω` if its is not real with respect to `Ω` -/
  @[reducible]
  def entity.virtual : Prop := ¬ e.real Ω

  /-! **Example**
  
    To give an example, the extensional entity "Socrates"
    defined as the existential event "(the set of all possible worlds in which) Socrates exists"
    is real because there is some possible intensional entity Socrates such that the event of 
    this Socrates existing is precisely the same event which defines the extensional "Socrates".
    However one could consistently hold that the event "Humans exist" does not represent some
    distinct intensional entity over and above the individual intensional human beings from whose
    representations it is constructed. In this case, the associated extensional entity, "Humanity",
    would be a virtual entity. This is compatible with doctrines of mereological nihilism and such.

    We assume that talk of "virtual entities" is just a figure of speech for talk about 
    existential events which talk about the existence of more than a single intensional entity,
    and as such we can conclude that the jump from existential events to extensional entities
    does not indeed commits us to any novel metaphysical thesis, nor to anything which could possibly
    be controversial.

  -/

  /-! **Absolutely Real Entities**
    
      One important notion that will arise out of intensionality will be the property 
      of an entity being absolutely real, i.e. real regardless of the underlying intensional ontology used
      to generate the ontological structure. This will allow us to think about intensional ontologies much 
      in the same way that geometers think about a choice of "basis", or "chart", so that we --like them-- 
      shall be most interested in proving only the results which do not depend on an arbitrary choice of
      intensional ontology.

  -/

  /-- An `entity` is absolutely real if it is real regardless of the choice of iontology -/
  def entity.absolutely_real := ∀ Ω : ω.iontology, e.real Ω

  section algebraic_realism

    /-! **Algebraic Realism**

      We shall name the theory which claims that all extensional entities are real **algebraic realism**,
      and we can also prove that both this theory and its denial are logically consistent. 
      The theory is to be so called because it is realistic about the set theoretic constructions
      of extensional entities (unions and intersections), which are algebraic constructions 
      in a complete Heyting algebra, or topological frame. 
      Because we are not committed to algebraic realism from the outset,
      we intend our identification of existential events with extensional entities to be metaphysically neutral.
  
    -/

    /-- **Algebraic realism** for intensional ontologies claims that all 
    extensional entities are real.   
    It is realist about the algebraic operations of topological frames. -/
    class realist : Prop :=
      (postulate₀ : ∀ e : ω.entity, e.real Ω)

    /-! **Final remarks about Intensionality**
  
      Even though we are not assuming algebraic realism, our general intention is indeed to avoid talking about 
      intensional entities as most as possible. If we completely abstract away talk of intensional entities from
      our system, we will be left simply with a topological space of possible worlds from which the distinction 
      between real and virtual entities cannot be defined. In order to define it we would at the very least have 
      to equip the space with an additional sub-basis to stand in for the events which are used to represent the
      intensional entities we intend to abstract, and then claim that an entity is real only if it belong to the sub-basis.
      As such, in order to make the distinction we would need to introduce this sub-basis as a new unwanted and 
      unneeded primitive concept to which our system would have to be committed. 
      In order to eschew this primitive, we must say that the distinction between real and virtual entities is,
      for the most part, not really useful in our system, and we have introduced it,
      along with the discussion of intensional entities, only in order to anticipate some 
      objections which might be leveled against our theory 
      (e.g. that it is committed to algebraic realism, or to an universal extensionality principle for the most 
      basic sort of possible entities). Because of this, in what follows we will simply be talking about 
      extensional entities and will pay no attention to whether they are real or virtual unless 
      it becomes important (and in general it won't be).

    -/
  
  end algebraic_realism

end realism

-- We discuss prime entities and how the topological notion of (sub-)basis relates to iontologies.
-- TODO: define different notions prime entities  
-- and prove equivalences between this notion, the notion of belonging to sub-basis,
-- and the notion of reality.
section prime
end prime

end ontology

