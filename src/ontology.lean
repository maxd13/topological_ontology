import math.alexandroff_space math.notation
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable
noncomputable theory
universe u

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
  the process of abstraction, universal, matter, form, the categories of being, the post-predicaments, etc...

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
  we are assuming is that existential events constitute a T???-topology of 
  possible worlds. 
  
  This leads us to the very first formal definitions of our theory:

-/

/-- An `ontology` is a nonempty T??? topological space
of possible worlds. -/
structure ontology :=
    (world : Type u)
    [wne : nonempty world]
    [t : topological_space world]
    -- identity of indiscernibles for possible worlds
    [axiom??? : @t0_space world t]

/-- identity of indiscernibles for possible worlds. -/
add_decl_doc ontology.axiom???

instance ontology_top  (?? : ontology)  : topological_space ??.world := ??.t
instance ontology_ne  (?? : ontology)  : nonempty ??.world := ??.wne
instance ontology_t0  (?? : ontology)  : t0_space ??.world := ??.axiom???

/-- **Events** in an ontology are simply sets of possible worlds.
 Events are said to **occur** at their element worlds. -/
@[reducible]
def ontology.event (?? : ontology) := set ??.world

/-- **Existential** `events` in an ontology are open sets of possible worlds. -/
@[reducible, simp]
def ontology.event.existential {?? : ontology} (e : ??.event) := is_open e

-- We will start developing the most basic conclusions of the theory:
namespace ontology

variable {?? : ontology}

-- We develop further the notion of events. 
section events
 
  variable (e : ??.event)

  @[reducible, simp]
  def event.occurs (w : ??.world) := w ??? e

  -- We define the related topological notions for events:

  @[reducible, simp]
  def event.closure : ??.event := closure e
  @[reducible, simp]
  def event.dense : Prop := closure e = univ
  @[reducible, simp]
  def event.exterior : ??.event := interior (-e)
  @[reducible, simp]
  def event.regular : Prop := e = e.exterior.exterior
  /-- also called `boundary` -/
  @[reducible, simp]
  def event.frontier : ??.event := frontier e
  /-- also called `frontier` -/
  @[reducible, simp, alias]
  def event.boundary : ??.event := e.frontier
  @[reducible, simp]
  def event.connected : Prop := is_connected e
  @[reducible, simp]
  def event.irreducible : Prop := is_irreducible e
  @[reducible, simp]
  def event.clopen : Prop := is_clopen e
  @[reducible, simp]
  def event.closed : Prop := is_closed e
  @[reducible, simp]
  def event.nnegative : Prop := ?? is_closed e
  /-- **Not Purely Negative** events -/
  @[reducible, simp]
  def event.npnegative : Prop := ?? is_closed e ??? is_clopen e
  @[reducible, simp]
  def event.compact : Prop := compact e

  -- necessity, possibility, impossibility, contingency
  @[reducible, simp]
  def event.necessary := e = univ
  @[reducible, simp]
  def event.possible := e.nonempty
  @[reducible, simp]
  def event.impossible := ??e.possible
  @[reducible, simp]
  def event.contingent := e.possible ??? ??e.necessary

  /-- The **ground**, or *ontological counterpart* of an `event e` is its interior, 
      i.e. the largest existential event below `e`.
      This will be the event of some entity existing whose
      existence necessitates the ocurrence of `e`. -/
  @[reducible, simp]
  def event.ground : ??.event := interior e

  /-- An `event` is **groundable** if its ground is `possible`. -/
  @[reducible, simp]
  def event.groundable := e.ground.possible

  /-- An `event` is **ungroundable** if it is not groundable. -/
  @[reducible, simp]
  def event.ungroundable := ??e.groundable

  -- Setting up notation:

  /-- Use `???e` for "`e` is necessary" -/
  @[reducible, simp]
  instance has_box_event : has_box ??.event := ???event.necessary???

  /-- Use `???e` for "the ground of `e`" -/
  @[reducible, simp]
  instance has_black_box_event : has_black_box ??.event := ???event.ground???

  /-- Use `???e` for "`e` is possible" -/
  @[reducible, simp]
  instance has_diamond_event : has_diamond ??.event := ???event.possible???

  /-- Use `???e` for "the event of nothing precluding `e` from happening", or `-???-e` -/
  @[reducible, simp]
  instance has_black_diamond_event : has_black_diamond ??.event := ???event.closure???

  /-- Use `~e` for "the exterior of `e`" -/
  @[reducible, simp]
  instance has_tilde_event : has_tilde ??.event := ???event.exterior???

  /-- Use `e??? ??? e???` instead of `e??? ??? e???`, replace with `???'` for `???`.
      Use `e??? ??? e???` instead of `?? e??? ??? e???`.
      Use `e??? ??? e???` instead of `e??? ??? e??? ??? e??? ??? e???`. 
      Use `e??? ??? e???` instead of `?? e??? ??? e???`.
  -/
  @[reducible, simp]
  instance has_entailment_event : has_entailment ??.event := ???set.subset???

  /-- Use `e??? ??? e???`  instead of `-e??? ??? e???`.
      Use `e??? !??? e???` instead of `-(e??? ??? e???)`.
      Use `e??? ??? e???`  instead of `(e??? ??? e???) ??? (e??? ??? e???)`. 
      Use `e??? !??? e???` instead of `-(e??? ??? e???)`. 
  -/
  @[reducible, simp]
  instance has_local_entailment_event : has_local_entailment ??.event := ????? e??? e???, -e??? ??? e??????

  --tests:
  -- variables (e??? e??? : ??.event)
  -- #check ???e
  -- #check ???e
  -- #check ???e
  -- #check ???e
  -- #check ~e
  -- #check e??? ??? e???
  -- #check e??? ???' e???
  -- #check e??? ??? e???
  -- #check e??? ??? e???
  -- #check e??? ??? e???
  -- #check e??? ??? e???
  -- #check e??? ??? e???
  -- #check e??? !??? e???
  -- #check e??? !??? e???
  -- example : e.groundable ??? ??????e := by simp

end events

-- And we prove some simple useful lemmas about them 
section event_lemmas

  variable {e : ??.event} 
  lemma event_union_exterior_open : e.existential ??? (e ??? ~e).existential :=
    by intro h; apply is_open_union h; simp

  -- For some reason in the standard library there is a lemma
  -- like this for finsets but not one for sets.
  lemma event_possible_of_ne_empty : e ??? ??? ??? ???e :=
    begin
        intro h,
        simp [set.nonempty],
        by_contradiction h???,
        push_neg at h???,
        replace h??? := eq_empty_iff_forall_not_mem.2 h???,
        contradiction,
    end

  lemma event_union_exterior_possible : ???(e ??? ~e) :=
    begin
        apply event_possible_of_ne_empty,
        intro h,
        simp at h,
        obtain ???h???, h?????? := h,
        rw h??? at h???,
        simp at h???,
        have c := ??.wne,
        contradiction,
    end

  @[simp]
  lemma existential_iff_ground_eq : e.existential ??? e = e.ground := 
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
 
  /-- The (possible, extensional) `entities` in the ontology are nonempty open sets of possible worlds.
      An entity is said to **exist** precisely at the worlds which are its elements. -/
  structure entity (?? : ontology) :=
    -- the event of the entity existing ("exists" is a reserved word)
    (??exists?? : ??.event)
    (existential : exists.existential)
    (possible : ?????exists??)

  /-- the event of the `entity` existing -/
  add_decl_doc entity.exists

  /-- Any groundable event `e` can be cast to an entity, 
      the existence of which is the ground of `e`. -/
  def event.entity (e : ??.event) (h : ??????e) : ??.entity := ??????e, is_open_interior, h???
  /-- An event is entitative if it is both existential and possible. -/
  def event.entitative (e : ??.event) : Prop := e.existential ??? ???e

  @[simp]
  lemma entity.entitative (e : ??.entity) : e.exists.entitative := ???e.existential, e.possible???
  @[reducible]
  lemma event.entitative.entity {e : ??.event} (h : e.entitative) : ??.entity := ???e, h.1, h.2???

  /-- main extensionality lemma for entities. -/
  @[ext]
  lemma entity_ext {e??? e??? : ??.entity} (h : e???.exists = e???.exists) : e??? = e??? := 
    by casesm* ??.entity; simp at h; simpa

  @[simp]
  lemma entity_ext_iff (e??? e??? : ??.entity) : e??? = e??? ??? e???.exists = e???.exists := 
    ???(?? h, by rw h), entity_ext???

  variables (e e??? e??? : ??.entity)

  lemma entity_exists_inj : function.injective (@entity.exists ??) :=
    ?? e??? e???, @entity_ext ?? e??? e???

  /-- Two entities are said to be `contrary` if there is no possible world
      in which both exist together.
      they are otherwise said to be `compatible`. -/
  @[reducible, simp]
  def entity.contrary := e???.exists ??? e???.exists = ???
  /-- Negation of `entity.contrary`. -/
  @[reducible, simp]
  def entity.compatible := ???(e???.exists ??? e???.exists)

  -- Some very important entities have no contraries
  @[reducible, simp]
  def entity.nocontrary := ?? ??? y, e.contrary y

  /-- Entity e??? is said to existentially entail entity e???,
      or to existentially depend on e???,
      if in every possible world in which e??? exists, e??? exists.
      For this relation we use the ` ??? ` notation.
      This is defined via coercion to events and 
      the `cross_entailment` typeclass instances. -/
  @[reducible, simp]
  instance has_coe_entity : has_coe ??.entity ??.event := ???entity.exists???

  -- tests:
  -- #reduce ?? (e??? : ??.entity) (e??? : ??.entity), e??? ??? e???
  -- #reduce ?? (e??? : ??.entity) (e??? : ??.event), e??? ??? e???
  -- #reduce ?? (e??? : ??.entity) (e??? : ??.event), e??? ??? e???

  /-- An entity is said to be a **truthmaker** for any event its existence entails. -/
  def entity.truthmaker (e : ??.entity) (ev : ??.event) : Prop := e ??? ev

  /-- The event of an entity being "removed" from a possible world. -/
  def entity.removed (w : ??.world) : ??.event := 
    {w' | e.exists w ??? w' < w ??? ?? e.exists w'}
  /-- The event of an entity being "added" to a possible world. -/
  def entity.added (w : ??.world) : ??.event := 
    {w' | ??e.exists w ??? w < w' ??? e.exists w'}
  /-- The set of all possible worlds from which an entity can be "removed". -/
  def entity.removable : ??.event := 
    {w | ???e.removed w}
  /-- The set of all possible worlds to which an entity can be "added". -/
  def entity.addable : ??.event := 
    {w | ???e.added w}

  /-- The necessary being (entity) is the entity which exists in
      every possible world. -/
  def nbe (?? : ontology) : ??.entity := ???univ, is_open_univ, by simp [empty_ne_univ]???
  instance entity_inhabited : inhabited ??.entity := ?????.nbe???

  /-- An entity is `contingent` if it is not the necessary being. -/
  @[reducible, simp]
  def entity.contingent := e ??? ??.nbe
  /-- An entity is `necessary` if it is the necessary being. -/
  @[reducible, simp]
  def entity.necessary := e = ??.nbe

  @[reducible, simp]
  def entity.compact := e.exists.compact

  /-- Use `???e` for "`e` is necessary" -/
  @[reducible, simp]
  instance has_box_entity : has_box ??.entity := ???entity.necessary???

  lemma nbe_unique : ???! e : ??.entity, ???e := by use ??.nbe; simp

  /-- A contingent entity is said to be **complemented** if 
      its existence is a clopen set.
      Complemented entities `e` are such that the event
      of their non-existence `-e.exists` is itself
      just as much of an entity as `e`.
      It can be proven that the possibility
      of the existence of complemented
      entities is logically equivalent to atheism. -/
  def entity.complemented : Prop := e.contingent ??? e.exists.clopen

  -- Here are some definitions which look more like lemmas:

  -- Arbitrary nonempty unions of entities are entities.
  def entity_Sup (s : set ??.entity) (h : s.nonempty) : ??.entity :=
    begin
      fsplit,
          exact ??? i ??? s, entity.exists i,
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

  -- so are pairwise unions, obviously
  def entity_sup (e??? e??? : ??.entity) : ??.entity := 
    begin
      fconstructor,
        exact e???.exists ??? e???.exists,
      apply is_open_union,
        exact e???.existential,
        exact e???.existential,
      simp, left,
      exact e???.possible,
    end

  -- @[reducible, simp]
  instance has_Sup_entity : has_Sup ??.entity := 
  ????? s, if h : s.nonempty then entity_Sup s h else ??.nbe???

  -- @[reducible, simp]
  instance has_sup_entity : has_sup ??.entity := ???entity_sup???

  @[simp]
  lemma Sup_sup (e??? e??? : ??.entity) : Sup {e???, e???} = e??? ??? e??? :=
    begin
      have c : ({e???, e???} : set ??.entity).nonempty, 
        use e???, simp,
      simp [Sup, has_Sup.Sup, entity_Sup, entity_sup, c],
      exact sup_comm,
    end

  /-- Intersections of compatible entities are entities.
      If `h` is a proof of the compatibility of the entities
      `e???` and `e???`, then `h.inter` is the intersection of
      `e???` and `e???`. -/
  def entity.compatible.inter {e??? e??? : ??.entity} (h : e???.compatible e???) : ??.entity :=
      ???  e???.exists ??? e???.exists
      , is_open_inter e???.existential e???.existential
      , h
      ???

  /-- possibly_not_exists_of_contingent -/
  lemma pnexists_of_contingent {e : ??.entity} : e.contingent ??? ???-e.exists :=
    begin
      intro h,
      simp [nbe, entity_ext_iff] at h,
      by_contradiction c,
      simp [has_neg.neg, compl, set.nonempty] at c,
      replace c := eq_univ_of_forall c,
      contradiction,
    end
  
  def entity.complement (h : e.complemented) : ??.entity :=
    ??? -e.exists
    , h.2.2
    , pnexists_of_contingent h.1 
    ???

end entities

-- We discuss some properties of possible worlds
section worlds

  variables (w w??? w??? : ??.world)

  -- We can also talk about an entity existing in a world
  -- as belonging to it, so we can use the notation e ??? w.
  @[reducible, simp]
  instance world.has_mem : has_mem ??.entity ??.world := ?????e w, w ??? e.exists???
  @[reducible, simp]
  def world.entities := {e : ??.entity | e ??? w}

  -- extensionality principle for possible worlds
  @[ext]
  lemma world.ext {w??? w??? : ??.world} (h : w???.entities = w???.entities) : w??? = w??? :=
    begin
      by_contradiction contra,
      have c??? := ??.axiom???.t0,
      obtain ???U, U_open, ???hU???, hU??????|???hU???, hU????????? := c??? w??? w??? contra;
      clear c???;
      have ne := nonempty_of_mem hU???;
      let e : ??.entity := ???U, U_open, ne???,
      replace h : w???.entities ??? w???.entities, finish,
      swap,
      replace h : w???.entities ??? w???.entities, finish,
      all_goals {
        simp [world.entities, entity.exists] at h,
        specialize h e,
        simp [e, hU???, hU???] at h,
        contradiction,
      },
    end

  @[reducible, simp]
  def world.ideal : ??.event := {w' | w' ??? w}
  def world.filter : ??.event := {w' | w ??? w'}
  def world.nonactuality : ??.event := {w' | w' ??? w}

  variable (??)

  def nonparmenidean : ??.event := {w | ??? e : ??.entity, e.contingent ??? e.exists w}
  def parmenidean : ??.event := {w | ??? e : ??.entity, e ??? w ??? ??? e}

  @[reducible, simp]
  def weakly_parmenidean : Prop := ?????.parmenidean
  @[reducible, simp]
  def strongly_parmenidean : Prop := ?????.parmenidean
  /-- A modal collapsing ontology is an ontology with a single possible world -/
  def mcollapse : Prop := ??? w??? w??? : ??.world, w??? = w???

  def Parmenides : ontology := { world := unit }
  def Sierpinski : ontology := { world := Prop }

  lemma mcollapse_iff_str_parme : ??.mcollapse ??? ??.strongly_parmenidean :=
    begin
      constructor; intro h;
        simp [strongly_parmenidean, nbe, ext_iff, parmenidean] at *,
        intros w??? e he w???,
        specialize h w??? w???,
        rwa h at he,
      intros w??? w???,
      ext e, constructor; intro h???,
        exact h w??? e h??? w???,
      exact h w??? e h??? w???,
    end

  -- #reduce Sierpinski.t.is_open {false}
  -- lemma weakly_parme_weaker : ??? ????? : ontology.{0}, ?????.weakly_parmenidean ??? ?? ?????.mcollapse :=
  --   begin
  --     use Sierpinski, constructor,
  --       use false, simp [parmenidean],
  --       intros e h, 
  --       by_cases hyp : e.exists = {false, true};
  --         simp [nbe, hyp, ext_iff],
  --         exact em,
  --       have c := e.existential,
  --       change (generate_open (?? (b : Prop ??? Prop), (b = ?? (b : Prop), b = true ??? false) ??? false) e.exists) at c,
  --       simp at c,
  --       intro w,
  --       apply generate_open.cases_on c,
  --       -- simp at d,
  --       -- induction c; try {simp},
  --       --   change (c_s = ?? (b : Prop), b) at c_H,
  --       --   rw c_H at h,
  --       --   change (false) at h, 
  --       --   contradiction,
        
        -- simp [set_of, set.mem] at c_H,
        --; simp [nbe],
        -- simp [sierpinski_space.is_open] at c,
  -- end


end worlds

-- Here we discuss basic general properties of ontologies themselves.
section ontology
 
  variable (??)

  /-- The least we should assume for an ontology to be worthy of consideration as being
      the true ontology is that we can add or remove entities from its worlds.
      A `viable` ontology is one satisfying this postulate. -/
  class viable : Prop :=
      (postulate??? : ??? w : ??.world, ??? w', w < w' ??? w' < w)

  -- common (sensical) ontologies
  class common extends viable ?? : Prop :=
      (postulate??? : uncountable ??.world)

  def alexandroff_discrete := alexandroff_space ??.world

  class alexandroff extends common ?? : Prop :=
    (postulate??? : ??.alexandroff_discrete)

  /-- A complemented ontology supports complemented entities. -/
  def complemented := ??? e : ??.entity, e.complemented

  /-- The **Principle of Non-Negative Nonactual Existence** claims
      that the nonactual (a.k.a. merely possible) existence of any entity is a non-negative event. -/
  def pnnnae : Prop := ??? (w : ??.world) (e : ??.entity), (???e ??? w.nonactuality).nnegative

end ontology


/- We introduce a custom notion of subbasis in an ontology. -/
section subbasis

  def {v} is_subbasis {?? : ontology.{v}} (B : set ??.event) : Prop :=
    (??? ev : ??.event, ev ??? B ??? ev.entitative) ???
    ??? e : ??.entity, ??? (I : Type v) (ne : nonempty I) (S : I ??? set ??.event),
    (??? i, (S i).finite ??? (S i).nonempty ??? (S i) ??? B) ???
    (??? i, ?????? S i) = e

  def is_subbasis' (B : set ??.entity) : Prop := is_subbasis $ entity.exists '' B

  variable {B : set ??.event}

  lemma is_subbasis.ne : is_subbasis B ??? B.nonempty :=
    begin
      intro h,
      by_contradiction contra,
      replace contra := not_nonempty_iff_eq_empty.mp contra,
      simp [is_subbasis, contra] at h,
      specialize h ??.nbe,
      obtain ???I, ne, S, h??? := h,
      replace h := (h.1 ne).2,
      obtain ???h???, h?????? := h,
      replace h??? := h???.not_subset_empty,
      contradiction,
    end
  
  lemma is_subbasis.ne_of_mem : is_subbasis B ??? ??? {b : ??.event}, b ??? B ??? ???b :=
    ?? h b hb, (h.1 b hb).2

  lemma is_subbasis.existential_of_mem : is_subbasis B ??? ??? {b : ??.event}, b ??? B ??? b.existential :=
    ?? h b hb, (h.1 b hb).1
  
  lemma is_subbasis.sUnion_necessary :  is_subbasis B ??? ??? ?????? B :=
    begin
      intro h,
      replace h := h.2 ??.nbe,
      obtain ???I, ne, S, ???h???, h????????? := h,
      unfold_coes at h???,
      simp [nbe, Union, ext_iff] at h???,
      simp [sUnion, ext_iff],
      intro w, specialize h??? w,
      obtain ???i, hi??? := h???,
      specialize h??? i,
      obtain ???h???, ???e,he???, h?????? := h???,
      specialize hi e he,
      specialize h??? he,
      exact ???e, h???, hi???,
    end

  lemma {v} default_subbasis (?? : ontology.{v}) : @is_subbasis ?? event.entitative := 
    begin
      refine ?????_,id, _???,
      intro e,
      refine ???(punit.{v+1} : Type v), ???punit.star???,(??_,{e.exists}), _???,
      unfold_coes, simp,
      refine ??????e.existential, e.possible???,_???,
      simp [Union],
    end

end subbasis

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
  among other reasons because sets are abstract mathematical objects, not concretely existing "things".
  This objection can however be resolved by understanding that, this being a mathematical theory,
  we are not really claiming that possible entities *are* nothing other than sets of possible worlds, 
  but only that these entities can be *represented* as the sets of possible worlds in which they exist.
  We are also not really committed to claiming that existence really just *is* a particular special case
  of the occurrence of events, but only that for all mathematical intents and purposes it can be so *represented*.
  We will look shortly into a way to make this representation formal by showing that any intensional ontological theory
  of possible entities naturally gives rise to our extensional topological theory in a mathematically well understood way.

-/

/-- An **Intensional ontology** is an ontology generated by a mapping of intensional entities to existential events -/
structure iontology (?? : ontology.{u}) :=
  (ientity : Type u)
  [iene : nonempty ientity]
  (??exists?? : ientity ??? ??.event)
  (axiom??? : is_subbasis $ range ??exists??)

namespace iontology

  section ientity

    variables {?? : ??.iontology} (ie : ??.ientity)

    /-- the `event` of an intensional entity existing -/
    def ientity.exists := ??.exists ie

    /-! **...**

      As can be seen, we can define an intensional ontology as a particular kind of ontology whose 
      topological structure was generated as the least topology containing the image of a map from some
      type of intensional entities to events. These events will provably be extensional entities, as we
      show bellow:

    -/
    
    lemma ientity.possible : ie.exists.possible := 
      ??.axiom???.ne_of_mem 
      (by simp [ientity.exists]; use ie)

    lemma ientity.existential : ie.exists.existential :=
      ??.axiom???.existential_of_mem
      (by simp [ientity.exists]; use ie)

    -- "up" is used for informal inheritance here
    /-- cast from `ientity` to `entity` -/
    def ientity.up : ??.entity := ???ie.exists, ie.existential, ie.possible???

    instance ientity_coe : has_coe ??.ientity ??.entity := ???ientity.up???

    -- #check ie ??? ie

  end ientity
  
end iontology

-- We discuss whether extensional entities, and other Lean types, are real or mere abstracta. 
section realism

  variables (e : ??.entity) (?? : ??.iontology)

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

  /-- An `entity` `e` is real with respect to an iontology `??` if there is an `??.ientity`
      which exists in the same possible worlds as `e`. -/
  def entity.real : Prop := ??? ie : ??.ientity, ie.up = e
  /-- An `entity` is virtual with respect to an iontology `??` if its is not real with respect to `??`. -/
  @[reducible]
  def entity.virtual : Prop := ?? e.real ??

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

  /-! In what follows, we speak of "realizations" instead of "instances" whenever we, informally, take the 
      type in question to be a kind of proof-relevant "proposition". -/

  -- Specific Forms of realism:

  /-- An intensional ontology is realist about a class `C` of entities, if every entity in `C` is real. -/
  def iontology.realist (C : set ??.entity) := ??? e : ??.entity, e ??? C ??? e.real ??

  /-- A *realization* of a position of **realism about instances of type `??`**, 
      relative to a mapping `??exists??` of the `??`s to their extensional representations,
      consists in an injective map associating every `x : ??` to some intensional entity, `map x`,
      such that `(map x).exists = ??exists?? x`. The default view is that all instances of `??`
      are necessary, such that (e.g.) `??.realism ???` correspond to the default view of realism about natural numbers 
      which take them to be necessary entities. -/
  structure iontology.realism (?? : ??.iontology) (?? : Type u) (??exists?? : ?? ??? ??.entity := ??_, ??.nbe) :=
    (map : ?? ??? ??.ientity)
    (h??? : function.injective map)
    (h??? : ??? x, ??.exists (map x) = ??exists?? x)

  /-- A *realization* of a position of **simplified realism about instances of type `??`**, 
      consists in an injective map associating every `x : ??` to some intensional entity, `map x`. -/
  structure iontology.srealism (?? : ??.iontology) (?? : Type u) :=
    (map : ?? ??? ??.ientity)
    (h??? : function.injective map)

  -- simplified realism can be cast to regular realism:
  def iontology.srealism.to_realism {?? : ??.iontology} {??} (h : ??.srealism ??) :  ??.realism ?? (iontology.ientity.up ??? h.map) :=
    by refine ???h.map, h.h???, _???; unfold_coes; simp [iontology.ientity.up, iontology.ientity.exists]

  /-- A *realization* of the position of **extensional realism** is a realization of `??.realism ??.entity id`.
      In other words, it consists of an injective map taking extensional entities to intensional entities
      which exist in the same possible worlds. It can be seem as associating to every equivalence class of intensional 
      entities a canonical representative which reifies the class itself and/or 
      the extensional entity corresponding to the class. The existence of a realization implies algebraic realism. -/
  def iontology.erealism := ??.realism ??.entity id

  /-- A *realization* of the position of **restricted extensional realism** for some class of entities `C`, 
      is a realization of `??.realism (subtype C) subtype.val`.
      In other words, it consists of an injective map, defined in `C`, 
      taking extensional entities to intensional entities
      which exist in the same possible worlds. It can be seem as associating to every equivalence class of intensional 
      entities represented by entities in `C`, a canonical representative which reifies 
      the class itself and/or the extensional entity corresponding to the class. 
      The existence of a realization implies realism about the `C`s. -/
  def iontology.rerealism (C : set ??.entity):= ??.realism (subtype C) subtype.val

  /-! Now, if a map of this sort is not injective, we can take the position in question to be a realization
      of a position of **grounding** rather than a position of realism. Since however a position of grounding 
      is just a (possibly partial) function, we do not define a new structure for it. -/

  /-! **Absolutely Real Entities**
    
      One important notion that will arise out of intensionality will be the property 
      of an entity being absolutely real, i.e. real regardless of the underlying intensional ontology used
      to generate the ontological structure. This will allow us to think about intensional ontologies much 
      in the same way that geometers think about a choice of "basis", or "chart", so that we --like them-- 
      shall be most interested in proving only the results which do not depend on an arbitrary choice of
      intensional ontology.

  -/

  /-- An `entity` is absolutely real if it is real regardless of the choice of iontology -/
  def entity.absolutely_real : Prop := ??? ?? : ??.iontology, e.real ??

end realism

section algebraic_realism

  variables (?? : ??.iontology)

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
  class iontology.arealist : Prop :=
    (postulate??? : ??? e : ??.entity, e.real ??)
  
  /-! We prove below that every ontology admits a canonical algebraic realist iontology. 
      In order to do so, we first show that it is possible to construct an iontology out of
      any subbasis, then we prove that for the default subbasis the generated iontology is
      indeed `arealist`.
  -/
  
  /-- The `iontology` generated by events in a subbasis. -/
  def is_subbasis.intensionalize {B : set ??.event} : is_subbasis B ??? ??.iontology :=
    ?? h, { ientity := subtype B
         , iene := let ???b, hb??? := h.ne in ??????b, hb??????
         , ??exists?? := subtype.val
         , axiom??? := by simpa [range, subtype.val] 
         }

  lemma natural_arealism : ??.default_subbasis.intensionalize.arealist :=
    begin
      constructor, intro e,
      use e; unfold_coes; simp [iontology.ientity.up],
      change (e.exists = e.exists), refl,
    end

end algebraic_realism

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

-- additional auxiliary lemmas involving compact events and entities
section compact
  -- It is annoying that mathlib doesn't export this
  -- sort of lemma using sets of sets instead of set families.
  lemma event.compact.elim {e : ??.event} : e.compact ??? (??? (S : set ??.event), 
                                                         (??? i ??? S, is_open i) ???
                                                         e ??? ?????? S ???
                                                         ??? s : set ??.event, s ??? S ??? finite s ??? e ??? ?????? s)
                                                         :=
    begin
      intros h S hS he,
      have c :=  @compact.elim_finite_subcover_image _ _ _ e S id h hS,
      specialize c _, swap,
        intros w hw,
        simp,
        specialize he hw,
        simp at he,
        exact he,
      simp at c,
      obtain ???s, h???, h???, h?????? := c,
      refine ???s, h???, h???, _???,
      intros w hw,
      specialize h??? hw,
      simp at h???,
      simp,
      exact h???,
    end

  lemma entity.compact.elim {e : ??.entity} : e.compact ??? (??? {S : set ??.entity}, S.nonempty ???
                                                         e ??? Sup S ???
                                                         ??? s : set ??.entity, s.nonempty ??? s ??? S ??? finite s ??? e ??? Sup s)
                                                         :=
    begin
      intros h S hS he,
      simp [Sup, has_Sup.Sup, hS, entity_Sup, has_entailment.entails] at he,
      have c := h.elim (entity.exists '' S),
      specialize c _, swap,
        intros i hi,
        simp at hi,
        obtain ???x, _, hx??? := hi,
        rw ???hx, exact x.existential,
      specialize c _, swap,
        simp [has_entailment.entails],
        exact he,
      obtain ???s, hs???, hs???, hs?????? := c,
      have sne : s.nonempty,
        simp [sUnion, set.subset] at hs???,
        obtain ???w, hw??? := e.possible,
        obtain ???ev, hev,_??? := hs??? hw,
        exact ???ev, hev???,
      replace sne : {e : ??.entity | e.exists ??? s}.nonempty,
        obtain ???ev, hev??? := sne,
        have c := hs??? hev, simp [image] at c,
        obtain ???e',_, he'??? := c,
        rw ???he' at hev,
        exact ???e', hev???,
      refine ???{e | e.exists ??? s}, sne, _???,
      constructor,
        intros e' he', simp at he',
        have c := hs??? he', simp [image] at c,
        obtain ???e'', goal, eq??? := c,
        replace eq := (entity_ext_iff e'' e').2 eq,
        rwa ???eq,
      constructor,
        set S' := {e : ??.entity | e.exists ??? s},
        have c : entity.exists '' S' = s,
          simp [image],
          ext, constructor; intro hyp,
            simp at hyp,
            obtain ???_, _, hyp??? := hyp,
            rwa ???hyp,
          simp,
          have c := hs??? hyp, simp [image] at c,
          obtain ???e', _, eq??? := c,
          rw ???eq at hyp,
          exact ???e', hyp, eq???,
        have c??? := entity_exists_inj.inj_on S',
        apply finite_of_finite_image c???,
        rwa c,
      simp [Sup, has_Sup.Sup, sne, entity_Sup, has_entailment.entails, set.subset],
      simp [has_entailment.entails, sUnion, set.subset] at hs???,
      intros w hw,
      obtain ???ev, hev???,hev?????? := hs??? hw,
      specialize hs??? hev???, simp [image] at hs???,
      obtain ???e', aux, he'??? := hs???, clear aux,
      rw ???he' at hev???,  
      rw ???he' at hev???,
      exact ???e', hev???, hev??????,
    end

end compact

end ontology

