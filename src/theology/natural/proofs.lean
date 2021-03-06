import theology.natural.god
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable

namespace ontology

variables {ω : ontology} (c : ω.cause)

lemma eps_stronger : c.eps ⇒ c.epcs ∩ c.epsc :=
  begin
    intros w hw,
    constructor,
      rintro ⟨e, he₁, he₂⟩,
      refine ⟨e.exists, e.existential, he₂, _⟩,
      refine ⟨_,hw e he₁ he₂⟩,
      simp [nbe] at he₁,
      exact ⟨e.possible, he₁⟩,
    intros h₁ e h₂ su h₃ h₄ h₅ h₆,
    apply h₂; try{assumption},
    refine ⟨h₄,_⟩,
    let s : ω.entity := ⟨su, h₅, nonempty_of_mem h₆⟩,
    apply hw s,
      simp [nbe],
      exact h₄.2,
    simpa [su],
  end


theorem aquinas_second (h' : c.entitative) : c.epcs ∩ c.epsc ∩ c.epc ∩ (c.epp (λe, c.csubstratum e)) ⇒ c.first_cause ω.nbe :=
  begin
    rintro w ⟨⟨⟨h₁, h₂⟩, pc⟩, pp⟩,
    by_cases h : ∃ e : ω.entity, e.contingent ∧ e.exists w, swap,
      exact c.first_cause_of_nocontingent h,
    specialize h₁ h, clear h,
    specialize h₂ h₁ univ, clear h₁,
    suffices c₀ : ∀ (su : event ω), cause.csubstratum c su →
                 su ≠ univ → event.existential su →
                 event.occurs su w → cause.causes c univ su w,
      specialize h₂ c₀,
      simp [cause.first_cause, nbe],
      refine ⟨by simp [univ],_⟩,
      unfold_coes, simp,
      intros e h₃ h₄,
      replace h₄ := ne.symm h₄,
      apply h₂; try{assumption},
        exact ⟨e.possible, h₄⟩,
      exact e.existential,
    clear h₂,
    intros ee h₃ h₄ h₅ h₆,
    let e : ω.entity := ⟨ee, h₅, nonempty_of_mem h₆⟩,
    have c₁ := pc e (by simpa [nbe]) h₆,
    have c₂ := pp e h₃ c₁,
    obtain ⟨ge, hg, cg⟩ := c₂,
    replace h₃ := h₃.2,
    specialize h₃ ge cg,
    convert cg,
    replace cg := h' (nonempty_of_mem ⟨ee, cg⟩),
    symmetry,
    by_contradiction h,
    let g : ω.entity := ⟨ge, cg, nonempty_of_mem h₃⟩,
    specialize pc g (by simpa [nbe]) h₃,
    unfold_coes at pc, simp [g] at pc,
    contradiction,
  end

theorem leibniz_second : (c.epcs (@entity.contingent ω) univ) ∩ (c.epsc univ) ∩ c.epsr ∩ (c.epp' (λe, c.csubstratum e)) ⇒ c.first_cause ω.nbe :=
  begin
    rintro w ⟨⟨⟨h₁, h₂⟩, psr⟩, pp⟩,
    by_cases h : ∃ e : ω.entity, e.contingent ∧ e.exists w, swap,
      exact c.first_cause_of_nocontingent h,
    specialize h₁ h, clear h,
    specialize h₂ h₁ univ, clear h₁,
    suffices c₀ : ∀ (su : event ω), cause.csubstratum c su →
                 su ≠ univ → univ su →
                 event.occurs su w → cause.causes c univ su w,
      specialize h₂ c₀,
      simp [cause.first_cause, nbe],
      refine ⟨by simp [univ],_⟩,
      unfold_coes, simp,
      intros e h₃ h₄,
      replace h₄ := ne.symm h₄,
      apply h₂; try{assumption},
        exact ⟨e.possible, h₄⟩,
      trivial,
    clear h₂,
    intros ee h₃ h₄ h₅ h₆,
    have c₁ := psr ee ⟨nonempty_of_mem h₆,h₄⟩ h₆,
    have c₂ := pp ee h₃ c₁,
    obtain ⟨g, hg, cg⟩ := c₂,
    replace h₃ := h₃.2,
    specialize h₃ g cg,
    convert cg,
    symmetry,
    by_contradiction h,
    specialize psr g ⟨nonempty_of_mem h₃,h⟩ h₃,
    obtain ⟨absurdity, insanity⟩ := psr,
    replace insanity := c.caused_causes insanity,
    contradiction,
  end

-- And of course we can get `dscotus` out of these proofs:
theorem scotus_second (h' : c.entitative) : ⋄(c.epcs ∩ c.epsc ∩ c.epc ∩ (c.epp (λe, c.csubstratum e))) → c.dscotus :=
  c.scotus_theorem $ aquinas_second c @h'

theorem scotus_second_psr : ⋄((c.epcs (@entity.contingent ω) univ) ∩ (c.epsc univ) ∩ c.epsr ∩ (c.epp' (λe, c.csubstratum e))) → c.dscotus :=
  c.scotus_theorem $ leibniz_second c


-- theorem material_substratum : ∀ {c' : ω.cause} (mc : c'.mcause), c.pcem mc ∩ mc.pis c ⇒ c.epcs (@entity.contingent ω) univ :=
--   begin
--     rintros c' mc w ⟨hw₁,hw₂⟩ ⟨e,he₁,he₂⟩,
--     by_cases h : mc.immaterial e w,
--       specialize hw₂ e h,
--       refine ⟨e, by trivial, _⟩,
--       refine ⟨he₂, _, hw₂⟩,
--       unfold_coes,
--       simp [nbe] at he₁,
--       exact ⟨e.possible, he₁⟩,
--     simp [cause.mcause.immaterial] at h,
--     replace h : ¬c'.uncaused e.exists w,
--       by_contradiction h₀,
--       apply h,
--       exact ⟨he₂,h₀⟩,
--     simp [cause.uncaused, cause.caused] at h,
--     simp [has_neg.neg, compl, set_of, has_mem.mem, set.mem] at h,
--     obtain ⟨m, hm⟩ := h,
--     replace hm := c'.caused_causes hm,
--     specialize hw₁ e hm,
--     obtain ⟨f, hf₁, hf₂, h⟩ := hw₁,
    
    -- use f.continues,
    -- push_neg at h,
      
    -- unfold_coes at h,
    -- simp [set_of] at h,
    
  -- end

theorem leibniz_BCCF (h : c.conjunctive₁') : c.epsr ∩ c.epss ⇒ c.first_cause ω.nbe :=
  begin
    rintros w ⟨psr, pss⟩,
    by_cases c₀ : ∀ w', w' = w,
      exact c.first_cause_of_parmenides c₀,
    push_neg at c₀,
    replace c₀ : ({w} : ω.event).contingent,
      simp [ext_iff], exact c₀,
    have c₁ := psr {w} c₀ (by simp),
    obtain ⟨g, hg⟩ := c₁,
    specialize pss g hg,
    have c₂ : c.causes univ {w} w,
      convert hg,
      symmetry,
      by_contradiction cg,
      have c₃ : {w} = g ∩ {w},
        ext w', simp,
        exact ⟨λh, ⟨by convert pss, h⟩, and.right⟩,
      rw c₃ at hg,
      have c₄ := h g g {w} ⟨nonempty_of_mem pss,cg⟩ c₀ hg,
      replace c₄ := nonempty_of_mem c₄.1,
      have c₅ := c.irreflexive g,
      contradiction,
    clear psr pss hg g,
    simp [cause.first_cause, nbe],
    refine ⟨by simp [univ],_⟩,
    unfold_coes, simp,
    intros e h₃ h₄,
    replace h₄ := ne.symm h₄,
    specialize h univ e {w} ⟨nonempty_of_mem h₃,h₄⟩ c₀,
    unfold_coes at h,
    specialize @h w _, swap,
      have c₃ : {w} = e.exists ∩ {w},
        ext w', simp,
        exact ⟨λh, ⟨by convert h₃, h⟩, and.right⟩,
      rw ←c₃,
      exact c₂,
    exact h.1,
  end

theorem scotus_leibniz_BCCF (h : c.conjunctive₁') : ⋄(c.epsr ∩ c.epss) → c.dscotus :=
  c.scotus_theorem $ leibniz_BCCF c h


theorem atheological_hylemorphism : (∃ c : ω.cause, ⋄(c.uhylemorphism ∩ ω.nonparmenidean)) → ω.atheism :=
  begin
    rintros ⟨c, ⟨w, ⟨⟨hc,hw⟩, nparm⟩⟩⟩,
    obtain ⟨e, ⟨he₁,he₂⟩⟩ := nparm,
    have c₀ : (∃ s : ω.substance, s.contingent ∧ s.exists w) ∨ ω.atheism,
      by_cases h₀ : e.perfect, swap,
        let a : ω.accident := ⟨e, h₀⟩,
        by_cases h₁ : a.owner.necessary,
          right,
          simp [accident.owner, nb] at h₁,
          intro theism,
          simp [ontology.theism, ext_iff] at theism,
          apply theism,
          refine ⟨a, _⟩,
          simp [accident.inheres, entity.subsists, nb],
          exact h₁,
        left,
        use a.owner,
        refine ⟨h₁,_⟩,
        have c₀ := a.inh_owner,
        replace c₀ := entails_of_inheres c₀,
        exact c₀ he₂,
      left,
      refine ⟨⟨e,h₀⟩,_,he₂⟩,
      simp [nb, -entity_ext_iff],
      exact he₁,
    cases c₀, swap, assumption,
    obtain ⟨s, h₁, h₂⟩ := c₀,
    have c₁ := hw s ⟨s.perfect,_⟩ h₂, swap,
      simp [nb] at h₁,
      unfold_coes, intro h,
      specialize h₁ _,swap,
        apply substance_ext,
        simp at h, exact h,
      contradiction,
    have c₂ := hc.axiom₈,
    simp [cause.pp, ext_iff] at c₂,
    replace c₁ := @c₂ w s (by trivial) c₁,
    clear c₂,
    obtain ⟨m, h₃, h₄⟩ := c₁,
    have c₁ := hc.axiom₀ ⟨w, nonempty_of_mem h₄⟩,
    let es : ω.entity := ⟨m, c₁.1.1, c₁.1.2⟩,
    let ms : ω.substance := ⟨es,c₁.2⟩,
    have c₂ : ms.necessary,
      by_contradiction contra,
      simp [nb, ms, -entity_ext_iff] at contra,
      specialize hw es ⟨ms.perfect, contra⟩,
      unfold_coes at hw,
      simp [es] at hw,
      suffices : c.caused m w,
        contradiction,
      apply hw,
      exact hc.axiom₃ ⟨s, h₄⟩,
    simp [ms,nb] at c₂,
    rw c₂ at h₄,
    replace h₄ : w ∈ c.is_cause ω.nbe.exists := ⟨s, h₄⟩,
    replace h₄ := nonempty_of_mem h₄,
    replace h₄ := hc.axiom₅ ω.nbe h₄,
    simp [atheism, theism, nb, ext_iff, accident.inheres],
    simp [-entity_ext_iff] at h₄,
    obtain ⟨e, h₄, h₅⟩ := h₄,
    let a : ω.accident, refine ⟨e, _⟩,
      exact imperfect_of_subsists_other h₄ h₅,
    exact ⟨a, h₄⟩,
  end

theorem theological_hylemorphism : ∀ (c' : ω.cause) (mc : c'.mcause), -c'.uhylemorphism ∩ mc.pis c ⇒ c.epcs :=
  begin
    rintros c' mc w ⟨h₁, h₂⟩,
    simp [cause.uhylemorphism, mc, cause.epc] at h₁,
    simp [set_of, has_mem.mem, set.mem] at h₁,
    obtain ⟨e, h₁, h₃, h₄, h₅⟩ := h₁,
    have c : mc.immaterial e w := ⟨h₄, h₅⟩,
    specialize h₂ e c,
    intro aux, clear aux,
    refine ⟨e.exists, e.existential, h₄, ⟨_,h₂⟩⟩,
    simp [nbe] at h₃,
    exact ⟨e.possible, h₃⟩,
  end


-- The argument from consubstantial causation.
theorem consub_cosmo : c.consubstantial → ⋄(c.epsr ∩ c.uncaused ω.nbe) → ω.theism :=
  begin
    simp [set.nonempty, cause.epsr],
    intros h w psr unc,
    dunfold theism substance.simple entity.simple,
    -- suppose God had an accident
    simp [substance.accidents, ext_iff, set.nonempty],
    intro a,
    by_contradiction contra,
    -- then He should also have an accident 'a' 
    -- in the world w in which psr is valid
    have : ω.nb.composite := ⟨a, contra⟩,
    clear contra a,
    obtain ⟨a, contra, h₁⟩ := nb_acc_actual this w, clear this,
    simp [substance.accidents] at contra,
    -- this accident has a cause in w, call it 's'.
    have : a.exists.contingent,
      refine ⟨a.possible, _⟩,
      have := a.contingent,
      simp [entity.contingent, nbe] at this,
      simpa [event.necessary],
    obtain ⟨s, hs⟩ := psr a this h₁, clear this,
    -- But this cause would in a sense have to be a
    -- cause of something that is going on in the necessary
    -- being.
    have c₁ : c.causes s ω.nbe.exists w,
        refine h s a hs ω.nbe _ (by simp [nbe]),
        simp [has_equiv.equiv, entity.cosubstantial],
        exact ⟨ω.nbe, self_subsist.mp ω.nb.perfect, contra⟩,
    -- However the necessary being admits no causes.
    simp [cause.uncaused, cause.caused] at unc,
    apply unc s, assumption,
    -- Therefore the necessary being 
    -- is what we call God (E.Q.D.D.).
  end

variable (ω)


/-- "It is contingent that there contingent things. "-/
def contingency_contingent : Prop := (∃ e : ω.entity, e.contingent) ∧ (Sup $ @entity.contingent ω).contingent

/-- It is it enough for it it to be contingent that there are
    contingent entities for we to get full blown classical theism
    without any extra auxiliary assumptions. -/
theorem ctheism_of_contingency : ω.contingency_contingent → ω.ctheism :=
  begin
    rintros ⟨h₁, h₂⟩,
    have c : set.nonempty entity.contingent := h₁,
    simp [Sup, c, entity_Sup, nbe, ext_iff] at h₂,
    -- clear c h₁,
    obtain ⟨w, hw⟩ := h₂,
    replace hw : ∀ e : ω.entity, e.exists w → e.necessary,
      intro e,
      simp [has_Sup.Sup, c, entity_Sup] at hw,
      specialize hw e,
      contrapose,
      exact hw,
    use w, intros e₁ e₂ h₃ h₄,
    have c₁ := hw e₁ h₃,
    have c₂ := hw e₂ h₄,
    clear hw h₃ h₄,
    simp [entity.necessary] at *,
    rw c₁, rw c₂,
  end

/-! # Aquinas's fourth way.
    
    The following proof is the best interpretation I could give of Aquinas's fourth way.
    However, admittedly, two additional assumptions, 
    though probably acceptable to Saint Thomas, 
    were not present in the original argument.
    The first could probably be replaced by any other premisse from which it 
    were possible to prove that if the necessary being's degree of perfection does 
    not vary across possible worlds then it can possibly exist alone or,
    for a weaker `ω.theism` argument, that it is simple.
    This premisse seemed intuitive enough for its intended application.
    The second might be even harder to replace, but it is even more
    intuitive. Please verify the formal definitions of all referenced
    concepts and lemmas before proposing an objection.

    The original text of the Summa Theologica reads:

      "**Quarta via** sumitur ex gradibus qui in rebus inveniuntur.
       Invenitur enim in rebus aliquid magis et minus bonum,
       et verum, et nobile, et sic de aliis huiusmodi.
       Sed magis et minus dicuntur de diversis secundum 
       quod appropinquant diversimode ad aliquid quod maxime est,
       sicut magis calidum est, quod magis appropinquat maxime calido.
       Est igitur aliquid quod est verissimum, et optimum, et nobilissimum,
       et per consequens maxime ens, nam quae sunt maxime vera, sunt maxime entia,
       ut dicitur II Metaphys. Quod autem dicitur maxime tale in aliquo genere, 
       est causa omnium quae sunt illius generis, sicut ignis, qui est maxime 
       calidus, est causa omnium calidorum, ut in eodem libro dicitur. 
       Ergo est aliquid quod omnibus entibus est causa esse, et bonitatis, 
       et cuiuslibet perfectionis, et hoc dicimus Deum."

       Reference: (https://www.corpusthomisticum.org/sth1002.html)
                  accessed in Jan 9, 2021.

    A translation reads:

      "The **fourth way** is taken from the gradation to be found in things.
      Among beings [rebus] there are some more and some less good, true, noble and the like.
      But "more" and "less" are predicated of different things, according as they 
      resemble in their different ways something which is the maximum, as a thing is 
      said to be hotter according as it more nearly resembles that which is hottest; 
      so that there is something which is truest, something best, something noblest and,
      consequently, something which is uttermost being; for those things that are greatest
      in truth are greatest in being, as it is written in Metaph. ii.
      Now the maximum in any genus is the cause of all in that genus; 
      as fire, which is the maximum heat, is the cause of all hot things. 
      Therefore there must also be something which is to all beings the cause of their being, goodness,
      and every other perfection; and this we call God." 
        
      Reference: (https://www.newadvent.org/summa/1002.htm#article3)
                 accessed in Jan 9, 2021.
    
    My formalization depends on the following
    assumptions and lemmas:
    
    0. (Analytical Premisse) There is a necessary being (`ω.nbe`), though it might in principle be a mere abstraction
        of the collection or multitude of all possible things/contingent things, i.e. the universe/cosmos.

        0.1. Notice that the conclusion `ω.ctheism` is incompatible with it being a mere 
            abstraction, and with it being the universe. See god.lean for details.
        0.2. Indeed, to say that God exists (`ω.theism`) is to say that the necessary being cannot be construed
            as a well-behaved materialistic universe, as the material universe has accidents. While
            to say that God has the attributes classically ascribed to Him (`ω.ctheism`) is to 
            say that the necessary being cannot *in any way* be construed as the universe,
            or as any collection of things, and that it cannot be taken to be a mere abstraction,
            *no matter one's underlying intensional position on which entities are real*, provide only it is a consistent
            position.
        0.3. The necessary being is unique up to existential equivalence (i.e. *qua* extensional entity)
            (`nbe_unique`).

    1. (Premisse) There are degrees of perfection, or greatness of being, in things (`b : ω.being`).

    2. (Premisse) If `e₁ ⇒ e₂` but not `e₂ ⇒ e₁`, 
        then `e₂` is strictly more perfect than `e₁` (`b.axiom₂`).

    3. (Minor Syllogistic Premisse) Some possible entity possibly attains the greatest
        conceivable degree of perfection (`b.ecaused`).

        3.1. We believe that in the original argument the notion of an **exemplary cause** is used
             to justify this premisse. Refer to the section "*The Intuition behind exemplary causes*" 
             in essence.lean for details.
        3.2. Supposing it were false, the necessary being could get arbitrarily close to the greatest
            conceivable degree of perfection, but never be able to reach it (`nbe_mperfectible`, `b.axiom₃`).
            This would be very strange, for at some possible world the difference between attaining and not
            attaining the greatest possible perfection would be negligible; e.g. there would
            be a possible world in which the necessary being would be 99.999999% perfect, but it
            would never be 100%.
        3.3. Alternatively we could also prove this premisse using `ecaused_of_phappy_and_wholesome` from:
            3.3.1. It is possible for some possible entity to attain the 
                    greatest degree of perfection **that it can have** (`b.wholesome`).
            3.3.2. No entity which attains the greatest degree of perfection that it can have, in a world `w`,
                    can entail the existence (`⇒`) of an entity which does not attain the greatest degree 
                    of perfection that it can have, at `w` (`b.phappy`).
        
    4. (Theorem) If **(3)** and **(2)**, then the necessary being can possibly attain 
        the greatest conceivable degree of perfection (`exemplar_nbe_of_ecaused`).

        4.1.1. For mere convenience we don't use `exemplar_nbe_of_ecaused` directly
              in our proof, but both `abs_exemplary_intro` and `nbe_eq1_of_abs_exemplary` instead.
        4.1.2. These lemmas have a dependency on `exemplar_nbe_of_ecaused`.
        4.1.3. `nbe_eq1_of_abs_exemplary` also depends on `b.axiom₃`, but this axiom is a mere
              convenience (allowing us to hardcode the number `1` in the proof)
              and could be completely removed without prejudice to the proof.
    
    5. (Major Syllogistic Premisse) It is *de re* necessary, (or essential) for an entity 
        to attain the greatest conceivable degree of perfection (if it is possible for it to do so). 
        I.e. "x attains the greatest conceivable degree of perfection" 
        is a *de re* necessary predicate (`b.eexemplary`).

    6. (Theorem) If **(5)**, then the necessary being necessarily attains the 
        greatest conceivable degree of perfection (`b.absolutely_exemplary`).

    Given **(6)** we can already conclude that the necessary being is maximally perfect (`entity.mperfect`),
    and that is probably the only conclusion that the original 4th way of Aquinas could manage to extract
    on its own without further assumptions. However, in order to prove the stronger result `ω.ctheism`, 
    which is what Aquinas would ultimately have wanted to prove, further premisses are needed. In
    a sense, the proof of `ω.ctheism` from **(6)** via additional premisses is a way to resolve
    the so called "gap problem" of proving the classical properties of God from the god-like entity
    obtained at the end of a typical proof of the existence of God. In Aquina's Summa Theologica,
    this is done along the 26 first questions of the *prima pars*. For the purpose of solving this
    problem, we then further introduce the following 2 assumptions:

    7. (Premisse) The multitude, collection, or whole of things (substances) of a given 
       kind varies in perfection across possible worlds in proportion to the number of 
       entities of that kind which exists in each respective world (`b.composable`).

       7.1. Strictly larger sets are strictly more perfect than the strictly smaller sets.
       7.2. Collections are strictly more perfect than their proper parts, 
            though it may or may not be the case that they are more perfect 
            than the *sum* of the perfections of their parts. 
            We are not here committed to either.

    8. (Premisse) Given any possible world `w`,
        there must be some world `w'` which is either strictly"larger" (`>`) than `w`, 
        or strictly "smaller" (`<`) than `w` (`ω.viable`).

        8.1. What `w < w'` means is that every entity which exists at `w` also exists at `w'`, but not vice-versa.
        8.2. See the definition of `ω.viable`, as well as the definitions of `specialization_order`
             and `specialization` (currently defined) at alexandroff.lean for further
             details on what "larger" and "smaller" mean.

    Since premisses **(1)**, **(3)**, **(5)** and **(7)** depend on an instance of `ω.being`,
    we pack them all together into the `ω.participated : Prop` definition. It turns
    out that it suffices to assume that it is logically consistent for there to be
    a `b : ω.being` with the aforementioned properties to prove `ω.ctheism`.
    The definition `ω.participated` can then reduce to our 4 premisses as the
    following example shows:
    
    example : ω.participated = ∃ b : ω.being, b.composable ∧ b.ecaused ∧ b.eexemplary := 
      by simp [participated, being.participated]

    Finally, we allow the proof to explain itself:

-/

-- WORK IN PROGRESS. ALMOST DONE.
-- MOST OF IT TYPE CHECKS AND CAN BE PROFITABLY READ.
-- INCOMPLETE PARTS ARE EXPLICIT. 
-- UNCOMMENT `ω.participated` IN `god.lean` AND THIS TO FOLLOW THE ARGUMENT.
-- /-- Aquinas's fourth way. -/
-- theorem aquinas_fourth : ω.participated → ω.viable → ω.ctheism :=
--   begin
--     intros participated viable,
--     obtain ⟨b, comp, h₁, h₂⟩ := participated,
--     obtain ⟨viable⟩ := viable,
--     -- the following step already concludes the proof that
--     -- the necessary being is maximally perfect (`entity.absolutely_exemplary`)
--     -- which is what the original
--     -- argument probably sough to show.
--     -- check the lemma for the proof.
--     have he := abs_exemplary_intro h₁ h₂,
--     clear h₁ h₂,
--     -- for simplicity, we ditch the "absolutely examplary/maximally perfect" conclusion
--     -- and work with the hardcoded number `1`.
--     replace he := nbe_eq1_of_abs_exemplary he,
--     dunfold ctheism,
--     -- suppose the classical theistic God doesn't exist.
--     by_contradiction c,
--     push_neg at c,
--     -- then in any possible world there must be
--     -- something contingent
--     replace c : ∀ w, ∃ e : ω.entity, e.contingent ∧ e.exists w,
--       intro w,
--       specialize c w,
--       obtain ⟨e₁,e₂,he₁,he₂,neq⟩ := c,
--       dunfold entity.contingent,
--       simp [nbe],
--       by_cases h : e₁.necessary;
--       simp [nbe] at h, swap,
--         exact ⟨e₁,h, he₁⟩,
--       rw ←h,
--       replace neq := ne.symm neq,
--       simp [entity_ext_iff] at neq,
--       exact ⟨e₂, neq, he₂⟩,
--     -- it then also follows that the necessary being 
--     -- can be expressed as the supremum of the set of all
--     -- contingent things. I.e. the necessary being's
--     -- existence is logically equivalent to "there exists something contingent",
--     -- so it can be thought of as the collection
--     -- of contingent things, or "the universe".
--     replace c : ω.nbe = Sup entity.contingent := sorry,
--     -- we can then specialize the compositionality of being
--     -- to the set of contingent entities and to the necessary being:
--     specialize comp (set_of $ @entity.contingent ω) ω.nbe,
--     -- We derive an auxiliary result before proceeding,
--     -- this was needed for purely bureocratic reasons.
--     have c' : ω.nbe ∉ (set_of $ @entity.contingent ω),
--       simp [set_of, has_mem.mem, set.mem],
--     -- We analyse the consequences of this for a single
--     -- possible world `w`:
--     obtain ⟨w⟩ := ω.wne,
--     -- because the ontology is viable, this world could be
--     -- made larger or smaller by some world `w'`.
--     -- This generates 2 proof goals for us corresponding to the
--     -- "larger" and "smaller" cases, respectively:
--     specialize viable w,
--     obtain ⟨w', ⟨hw'₁, hw'₂⟩|⟨hw'₁, hw'₂⟩⟩ := viable;
--     push_neg at hw'₂; simp [specialization] at hw'₂;
--     obtain ⟨s, open_s, hs₁, hs₂⟩ := hw'₂,
--     -- we then seek to prove that the degree of perfection of the
--     -- necessary being varies across worlds.
--     -- for the case w < w':
--       specialize comp w w',
--       swap,
--     -- for the case w' < w:
--     specialize comp w' w,
--     all_goals {
--       specialize comp c' c,
--       specialize comp _, swap,
--         constructor,
--           rintros e ⟨he₁,he₂⟩,
--           simp [world.entities] at he₁,
--           specialize hw'₁ e.exists e.existential he₁,
--           exact ⟨hw'₁, he₂⟩,
--         simp [world.entities, has_subset.subset, set.subset],
--         have ps : ⋄s, 
--           simp [has_diamond.diamond],
--           exact nonempty_of_mem hs₁,
--         let es : ω.entity := ⟨s, open_s, ps⟩,
--         use es,
--         constructor, simp [es, hs₁],
--         constructor, swap, simp [es, hs₂],
--         simp [ontology.nbe, es],
--         intro h, simp [ext_iff] at h,
--     },
--     specialize h w', contradiction,
--     swap,
--     specialize h w, contradiction,
--     -- finished specializing comp.
--     -- We have shown roughly that the perfection
--     -- of the necessary being varies across worlds,
--     -- now we need to show that, because the necessary
--     -- being is maximally perfect, this is impossible
--     all_goals {
--       have h := he w,
--       have h' := he w',
--       clear he,
--       rw h at comp,
--       rw h' at comp,
--       norm_num at comp,
--     },
--   end

-- WORK IN PROGRESS
-- /-- Using `being.axiom₄` we can also show 
--     composability + viability → nogap₂.
--     meaning classical theism follows from these assumptions under
--     the further assumption of theism. -/
-- theorem aquinas_fourth_nogap₂ : ω.composable → ω.viable → ω.nogap₂ := sorry

end ontology