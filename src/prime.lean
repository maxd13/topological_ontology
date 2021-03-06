import ontology
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable
noncomputable theory

namespace ontology

variable {ω : ontology}

-- We discuss prime entities, topological subbasis, basis, open covers and some definitions involving compact sets.
section prime

  variables (e : ω.entity)

  /-- An entity `e` is said to be **meet prime**, 
      or **meet irreducible**, if 
      for any entities `e₁, e₂` whose
      nonempty conjunction entails `e`,
      one of them must entail `e`. 
      This is equivalent to the principal ideal of `e` in
      the partial order of opens being prime. -/
  def entity.mprime := 
    ∀ ⦃e₁ e₂ : ω.entity⦄ ⦃h : e₁.compatible e₂⦄,
    (h.inter ⇒ e) → (e₁ ⇒ e ∨ e₂ ⇒ e)

  /-- An entity `e` is said to be **join prime**, 
      or **join irreducible**, if 
      for any entities `e₁, e₂` whose
      disjunction is entailed by `e`,
      `e` must entail one of them. 
      This is equivalent to the principal filter of `e`
      in the partial order of opens being prime. -/
  def entity.jprime := ∀ ⦃e₁ e₂ : ω.entity⦄, (e ⇒ e₁ ⊔ e₂) → (e ⇒ e₁ ∨ e ⇒ e₂)

  /-- An entity is **completely join prime** if it is join prime and compact.
      This is also occasionally known as the property of being **supercompact**. -/
  def entity.cjprime := e.jprime ∧ e.compact

  /-- An entity `e` is said to be **prime** if it is both join prime and meet prime. -/
  def entity.prime := e.jprime ∧ e.mprime

  /-- An entity `e` is said to be **completely prime** if it is both prime and compact. -/
  def entity.cprime := e.prime ∧ e.compact
  
  /-- An entity is said to be **absolutely basic** if it belongs to every topological basis
      of open sets. -/
  def entity.abasic := ∀ {B : set ω.event}, is_topological_basis B → e.exists ∈ B

  /-- An entity is said to be **absolutely sub-basic** if it belongs to every `subbasis` -/
  def entity.asubasic := ∀ {B : set ω.event}, is_subbasis B → e.exists ∈ B
  
  /-- Definition of **open cover**. -/
  def entity.cover (S : set ω.event) : Prop := 
    (∀ (ev : ω.event), ev ∈ S → ev.entitative) ∧
    e ⇒ ⋃₀ S
  
  /-- Definition of **Minimal open cover**. -/
  def entity.mcover (S : set ω.event) : Prop := 
    e.cover S ∧ ∀ ev ∈ S, ¬ e.cover (S-{ev})

  
  /-- Definition of **Exact Minimal open cover**. -/
  def entity.emcover (S : set ω.event) : Prop := 
    e.mcover S ∧ ⋃₀ S ⇒ e

  -- TODO: change the definitions below to use covers.
  -- Also consider getting rid of the uncoverable' definition.
  -- In order to do that, it is necessary to change some proofs that need it,
  -- and they become more annoying due to the necessity of casting 
  -- entitative events to entities.

  /-- An entity `e` is said to be **uncoverable** if all of its open covers contain a superset of `e`.
      Notice that if the cover is a subset cover this implies that the cover must contain `e`,
      so any cover of `e` by its subsets must be trivial in this sense. -/
  def entity.uncoverable := ∀ ⦃S : set ω.event⦄, (∀ (ev : ω.event), ev ∈ S → ev.entitative) → S.nonempty → e ⇒ ⋃₀ S → ∃ e₂ ∈ S, e ⇒ e₂
  def entity.uncoverable' := ∀ ⦃S : set ω.entity⦄, S.nonempty → e ⇒ Sup S → ∃ e₂ ∈ S, e ⇒ e₂

  
  /-- An entity `e` is said to be **minimally uncoverable** if all of its minimal open covers contain a superset of `e`.
      Notice that if the cover is a subset cover this implies that the cover must contain `e`,
      so any minimal cover of `e` by its subsets must be trivial in this sense. -/
  def entity.muncoverable := ∀ ⦃S : set ω.event⦄, e.mcover S → ∃ ev ∈ S, e ⇒ ev

  /-! # The following definitions concern entities which are prime in a substantial sense: -/

  /-- Definition of a **Minimal Substantial Cover** of an entity. -/
  def entity.mscover (S : set ω.event) : Prop :=
    e.mcover S ∧ ∀ (s : ω.event), s ∈ S → s.dense

  /-- An entity `e` is said to be **substantially meet prime**,
      or **substantially meet irreducible**, if 
      for any substances `s₁, s₂` whose
      conjunction entails `e`,
      one of them must entail `e`. -/
  def entity.smprime := 
    ∀ ⦃e₁ e₂ : ω.entity⦄, e₁.exists.dense → e₂.exists.dense →
    (e₁.exists ∩ e₂ ⇒ e) → (e₁ ⇒ e ∨ e₂ ⇒ e)

  /-- An entity `e` is said to be **substantially join prime**,
      or **substantially join irreducible**, if 
      for any substances `s₁, s₂` whose
      disjunction is entailed by `e`,
      `e` must entail one of them. -/
  def entity.sjprime := 
    ∀ ⦃e₁ e₂ : ω.entity⦄, e₁.exists.dense → e₂.exists.dense →
    (e ⇒ e₁.exists ∪ e₂.exists) → (e ⇒ e₁ ∨ e ⇒ e₂)

  /-- An entity `e` is said to be **substantially prime** if it is both substantially join prime and substantially meet prime. -/
  def entity.sprime := e.sjprime ∧ e.smprime

end prime

-- We prove important properties concerning prime entities and basis and relate them to iontologies. 
section prime_lemmas
  variables (e : ω.entity)

  @[simp]
  lemma uncoverable'_iff_uncoverable : e.uncoverable' ↔ e.uncoverable :=
    begin
      simp [ entity.uncoverable
           , entity.uncoverable'
           , Sup
           , has_Sup.Sup
           , entity_Sup
           ],
      constructor; intros,
        let S' := {e : ω.entity | e.exists ∈ S},
        obtain ⟨ev, hev⟩ := a_2,
        have c₀ := a_1 ev hev,
        have c : S'.nonempty := ⟨⟨ev, c₀.1, c₀.2⟩, hev⟩,
        specialize a c, simp [c, S'] at a,
        specialize a _, swap,
          cases e,
          simp [has_entailment.entails],
          convert a_3 using 1,
          simp [ext_iff, S'],
          clear_except a_1,
          intros w, constructor; intro h;
          obtain ⟨i, hi₁, hi₂⟩ := h,
            use i.exists, tauto,
          have c := a_1 i hi₁,
          use ⟨i, c.1, c.2⟩, tauto,
        obtain ⟨i, hi₁, hi₂⟩ := a,
        use i.exists, tauto,
      simp [a_1] at a_2,
      let S' := entity.exists '' S,
      obtain ⟨ev, hev⟩ := a_1,
      have c : S'.nonempty,
        refine ⟨ev.exists, _⟩,
        simp [S', set.image],
        use ev, tauto,
      specialize a _ c, swap,
        simp [S', set.image],
        clear_except,
        intros aux x _ h,
        cases h, simp [event.entitative],
        exact ⟨x.existential, x.possible⟩,
      specialize a _, swap, 
          cases e,
          simpa [has_entailment.entails],
      simp [S', set.image] at a, clear_except a,
      obtain ⟨i, ⟨e', he'₁, he'₂⟩, hi₂⟩ := a,
      cases he'₂, exact ⟨e', he'₁, hi₂⟩,
    end

  lemma entity.cprime.to_cjprime {e : ω.entity} : e.cprime → e.cjprime :=
    λ h, ⟨h.1.1, h.2⟩
  
  lemma entity.cjprime_to_cjprime (e : ω.entity) : (e.cjprime ∧ e.mprime) → e.cprime :=
    λ ⟨h₁, h₂⟩, ⟨⟨h₁.1, h₂⟩, h₁.2⟩

  lemma entity.mprime.induction {e : ω.entity} : e.mprime → ∀ {S : set ω.event}, S.nonempty →
                              (∀ ev : ω.event, ev ∈ S → ev.entitative) → finite S → (⋂₀ S).nonempty → ⋂₀ (S) ⇒ e → ∃ e₂ ∈ S, e₂ ⇒ e :=
    begin
      intros h₀ S ne h₁ h₂,
      revert ne h₁,
      apply h₂.induction_on,
        intro absurd,
        simp [set.nonempty] at absurd,
        contradiction,
      intros e₂ s h₃ h₄ h₅ h₆ h₁ h₇ h,
      simp [has_entailment.entails] at *,
      simp [h₆] at *, clear h₆ h₃,
      by_cases c : s.nonempty, swap,
        replace c := not_nonempty_iff_eq_empty.mp c,
        rw c, rw c at h, simp [set.image] at h,
        use e₂, tauto,
      specialize h₅ c _, swap,
        intros ev hev,
        apply h₁ ev, simp [hev],
      specialize h₅ _, swap,
        obtain ⟨w, _, hw⟩ := h₇,
        exact ⟨w, hw⟩,
      simp [entity.mprime] at h₀,
      set e₃ : ω.event := ⋂₀ s,
      have c₁ : event.existential e₃,
        clear_except h₄ h₁,
        apply is_open_sInter, assumption,
        intros ev hev,
        specialize h₁ ev, simp [hev] at h₁,
        exact h₁.1,
      have := h₇,
      obtain ⟨w, h₇₁, h₇₂⟩ := this,
      have : e₃.nonempty := ⟨w, h₇₂⟩,
      let e₃' : ω.entity := ⟨e₃, c₁, this⟩,
      have := h₁ e₂, simp at this,
      let e₂' : ω.entity := ⟨e₂, this.1, this.2⟩,
      specialize @h₀ e₂' e₃' h₇ _, swap,
        simpa [entity.compatible.inter, has_entailment.entails],
      simp [has_entailment.entails] at h₀,
      cases h₀, use e₂, simp [h₀],
      specialize h₅ h₀, clear_except h₅,
      obtain ⟨e', h₁, h₂⟩ := h₅,
      use e', simp [h₁, h₂],
    end


  lemma entity.jprime.induction {e : ω.entity} : e.jprime → ∀ {S : set ω.entity}, S.nonempty →
                              finite S → e ⇒ Sup S → ∃ e₂ ∈ S, e ⇒ e₂ :=
    begin
      intros h₀ S ne h₁,
      revert ne,
      apply h₁.induction_on,
        intro absurd,
        simp [set.nonempty] at absurd,
        contradiction,
      intros e₂ s h₃ h₄ h₅ h₆ h₇,
      simp [Sup, has_Sup.Sup, h₆] at *,
      simp [has_entailment.entails] at *,
      clear h₆,
      by_cases c : s.nonempty, swap,
        replace c := not_nonempty_iff_eq_empty.mp c,
        simp [entity_Sup] at h₇,
        rw c, rw c at h₇, simp at h₇,
        exact ⟨e₂, by simp, h₇⟩,
      specialize h₅ c,
      simp [c] at h₅,
      simp [entity.jprime, entity_sup] at h₀,
      simp [has_entailment.entails] at h₀,
      have aux : entity_Sup (insert e₂ s) h₆ = e₂ ⊔ entity_Sup s c, 
        simp [has_Sup.Sup, has_sup.sup, entity_Sup, entity_sup],
      rw aux at h₇,
      specialize h₀ h₇,
      cases h₀, exact ⟨e₂, by simp, h₀⟩,
      specialize h₅ h₀,
      obtain ⟨x, hx₁, hx₂⟩ := h₅,
      exact ⟨x, by simp [hx₁], hx₂⟩,
    end

  -- WORK IN PROGRESS. ONLY NEEDED TO DISCUSS PARTICULARS AND UNIVERSALS.
  -- lemma jprime_iff_muncoverable : e.jprime ↔ e.muncoverable := 
  --   begin
  --     constructor; intro h,
  --       rintros S ⟨⟨h₁,h₂⟩, h₃⟩,
  --       have ne : S.nonempty, admit,
  --       obtain ⟨ev, hev⟩ := ne,
  --       by_cases c₀ : (S-{ev}).nonempty, swap,
  --         admit,
  --       by_cases c₁ : e ⇒ ev,
  --         exact ⟨ev, hev, c₁⟩,
  --       have c : ⋃₀ S = ev ∪ ⋃₀ (S-{ev}),
  --         admit,
  --       rw c at h₂, clear c,
  --       exfalso,
  --       specialize h₃ ev hev, simp [entity.cover] at h₃,
  --       apply h₃; clear h₃,
  --         intros ev' hev' aux, clear aux,
  --         exact h₁ ev' hev',
  --       have c₁ := h₁ ev hev,
  --       have c₂ : event.entitative (⋃₀ (S-{ev})), admit,
  --       let e₁ : ω.entity := ⟨ev, c₁.1, c₁.2⟩,
  --       let e₂ : ω.entity := ⟨⋃₀ (S-{ev}), c₂.1, c₂.2⟩,
  --       specialize @h e₁ e₂ h₂, cases h;
  --       simp [e₁, e₂, has_entailment.entails] at h, clear e₁ e₂,
  --         contradiction,
  --       exact h,
  --     intros e₁ e₂ h₀,
  --     by_contradiction contra, push_neg at contra,
  --     obtain ⟨h₁, h₂⟩ := contra,
  --     let S : set ω.event := {e₁, e₂},
  --     suffices c : e.mcover S,
  --       specialize h c,
  --       simp [S] at h,
  --       obtain ⟨ev, ⟨rfl⟩|⟨rfl⟩, absurd⟩ := h;
  --       contradiction,
  --     clear h, constructor, constructor;
  --       simp [S], rintros ev (⟨rfl⟩|⟨rfl⟩);
  --       unfold_coes; simp, unfold_coes,
  --       simp [has_sup.sup, entity_sup, has_entailment.entails] at h₀,
  --       convert h₀ using 1, exact sup_comm,
  --     simp [S], rintros ev (⟨rfl⟩|⟨rfl⟩);
  --     intros h; unfold_coes at h; replace h := h.2,
  --     -- by_cases c : e₁ = e₂;
  --     --     try {
  --     --       cases c,
  --     --       simp [has_entailment.entails, has_sup.sup, entity_sup] at h₀,
  --     --       contradiction,
  --     --     },
  --     replace h : e ⇒ e₁,
  --       admit,
  --       -- simp [has_entailment.entails] at h,
  --       -- simp [has_entailment.entails],
  --       -- convert h using 1,
  --       -- simp [ext_iff],
  --     swap, replace h : e ⇒ e₂, admit,
  --     all_goals {contradiction},
  --   end

  lemma cjprime_iff_uncoverable' : e.cjprime ↔ e.uncoverable' :=
    begin
      constructor; intro h,
        obtain ⟨pe, ce⟩ := h,
        intros S neS hS,
        replace ce := ce.elim neS hS,
        obtain ⟨s, sne, h₁, h₂, h₃⟩ := ce,
        replace pe := pe.induction sne h₂ h₃,
        obtain ⟨e₂, h₄, h₅⟩ := pe,
        exact ⟨e₂, h₁ h₄, h₅⟩,
      constructor,
        intros e₁ e₂ h₁,
        let s : set ω.entity := {e₁, e₂},
        have c : s.nonempty, use e₁, simp,
        specialize h c, simp [s, -entity_ext_iff] at h,
        specialize h h₁,
        obtain ⟨e',h|h, h₂⟩ := h; rw h at h₂; simp [h₂],
      apply compact_of_finite_subcover,
      intros type U hU h₁,
      let S : set ω.entity := {e : ω.entity | ∃ i, U i = e.exists},
      have ne : S.nonempty,
        simp [S, set.nonempty],
        by_contradiction contra,
        push_neg at contra,
        have c : ∀ i, U i = ∅,
          by_contradiction contra₂,
          push_neg at contra₂,
          obtain ⟨i, hi⟩ := contra₂,
          replace hi := ne_empty_iff_nonempty.mp hi,
          let e' : ω.entity := ⟨U i, hU i, hi⟩,
          specialize contra e' i,
          simp [e'] at contra,
          contradiction,
        obtain ⟨w, hw⟩ := e.possible,
        specialize h₁ hw, simp at h₁,
        obtain ⟨i, hi⟩ := h₁,
        specialize c i,
        rw c at hi, simp at hi,
        contradiction,
      specialize h ne _, swap,
        simp [Sup, has_Sup.Sup, entity_Sup, ne, has_entailment.entails, S, set.subset],
        intros w hw,
        specialize h₁ hw, simp at h₁,
        obtain ⟨i, hi⟩ := h₁,
        let e' : ω.entity := ⟨U i, hU i, ⟨w, hi⟩⟩,
        refine ⟨e', ⟨i, _⟩, _⟩; simp [e'],
        assumption,
      obtain ⟨e₂, ⟨i, hi⟩, h⟩ := h,
      use ({i} : finset type), simp,
      rwa hi,
    end

  lemma cjprime_iff_uncoverable : e.cjprime ↔ e.uncoverable :=
    by convert cjprime_iff_uncoverable' e; ext; symmetry; exact uncoverable'_iff_uncoverable e

  lemma entity.non_disjoint_cover_of_uncoverable : ¬e.uncoverable → ∃ (S : set ω.event),
                                            (∀ (ev : ω.event), ev ∈ S → ev.entitative) ∧ 
                                            (∀ (ev : ω.event), ev ∈ S → (ev ∩ e.exists).nonempty) ∧
                                            S.nonempty ∧ e ⇒ ⋃₀ S ∧ 
                                            ∀ (x_1 : ω.event), x_1 ∈ S → ¬(e ⇒ x_1) :=
  begin
    intro h,
    simp [entity.uncoverable] at h,
    obtain ⟨S, h₁, neS, h₂, h₃⟩ := h,
    let S' := {ev : ω.event | ev ∈ S ∧ (ev ∩ e.exists).nonempty},
    use S', constructor,
      intros ev hev, specialize h₁ ev,
      apply h₁, exact hev.1,
    constructor, simp [S'],
    constructor,
      by_contradiction contra,
      unfold set.nonempty at contra,
      push_neg at contra,
      simp [S'] at contra,
      have : ⋃₀ S ∩ e = ∅,
        rw [sUnion_eq_bUnion, Union_inter],
        simp [ext_iff],
        intros w s hs h,
        specialize contra s hs,
        simp [set.nonempty] at contra,
        specialize contra w h,
        exact contra,
      obtain ⟨w, hw⟩ := e.possible,
      suffices c : e.exists ⊆ ⋃₀ S ∩ e.exists,
        unfold_coes at this, rw this at c,
        apply c hw,
      simp only [has_entailment.entails] at h₂,
      simp, exact ⟨h₂, by refl⟩,
    constructor,
      simp [has_entailment.entails],
      intros w hw,
      specialize h₂ hw, simp at h₂, simp,
      obtain ⟨ev, h₁, h₂⟩ := h₂,
      use ev, refine ⟨⟨h₁,_⟩, h₂⟩,
      exact ⟨w, ⟨h₂, hw⟩⟩,
    intros ev hev, apply h₃,
    exact hev.1,
  end

  /-! # Theorem Description. 
      The following is probably one of the hardest,
      if not the hardest, theorem we currently have in 
      our project. Hence for readability we provide here
      a sketch of how the proof works:

      **Theorem:** An entity `e` is absolutely sub-basic if and only if it is completely prime.  

      **Proof:** To prove the `→` side, assume `e` belongs to every subbasis, then supposing that `e`
      were not completely prime we can prove that `B = {e' : ω.entity | e' ≠ e}` 
      is a subbasis for the space, but this is absurd since `e` was assumed to belong to every subbasis.

      To prove that `B` is a subbasis, it suffices to show that there is some family of finite 
      intersections of entities distinct from `e` which exactly cover `e`, 
      for in this manner every entity would either belong to `B` or be exactly 
      covered by finite intersections of entities belonging to `B`, making `B` a subbasis. 
      Next we consider that if `e` is not completely prime, this must be either because 
      it is not meet prime or not uncoverable, and this is because "completely prime" 
      is equivalent to "meet prime and uncoverable" via the equivalence we 
      have proven between "completely join prime" and "uncoverable" via the `cjprime_iff_uncoverable'` 
      lemma, and the trivial equivalence between "completely prime" and "meet prime and completely join prime";
      we then proceed by cases. In what follows remember that `⊓ = ∩` and `⊔ = ∪` for the domain of entities, 
      i.e. when the sets being intersected or united are nonempty and open.

      If `e` is not meet prime, this entails that there are entities `e₁, e₂` such that `e₁ ⊓ e₂` 
      is nonempty and `e₁ ⊓ e₂ ⇒ e` but neither `e₁ ⇒ e` nor `e₂ ⇒ e`. 
      In particular it also follows that `(e₁ ⊔ e) ≠ e` and `e₂ ⊔ e ≠ e`, 
      for otherwise we would have `e₁ ⇒ e` and `e₂ ⇒ e`; 
      therefore both `e₁ ⊔ e` and `e₂ ⊔ e` belong to `B`. 
      Hence, because the singleton family `{(e₁ ⊔ e) ⊓ (e₂ ⊔ e)}` 
      exactly covers `e`, `B` is a subbasis. 
      The exact cover follows from `(e₁ ⊔ e) ⊓ (e₂ ⊔ e) = (e₁ ⊓ e₂) ⊔ e = e`,
      where the second equality is proven via `e₁ ⊓ e₂ ⇒ e`.

      If `e` is not uncoverable, this entails there is a nonempty cover `S` of `e` 
      such that for all `e' ∈ S` it is not the case that `e ⇒ e'`. 
      Without loss of generality (guaranteed by `non_disjoint_cover_of_uncoverable`), 
      we can also assume that `e' ⊓ e ≠ ∅` for all `e' ∈ S`. 
      Now, notice that it not being the case that`e ⇒ e'` implies `e' ⊓ e ≠ e`, 
      for otherwise we would have `e ⇒ e' ⊓ e`, and hence `e ⇒ e'`;
      hence `e' ⊓ e ∈ B` for all `e' ∈ S`. Then notice that `e = (⋃ S) ⊓ e = ⋃ e' ⊓ e`, 
      hence there is a union of elements of `B` which exactly cover `e`, 
      which proves that `B` is a subbasis. The first equality is obtained 
      from the fact `S` is a cover, while the second by distributing `⊓` over `⋃`.
      This concludes the first side of the proof.

      To prove the (`←`) side, assume `e` is completely prime and let `B` be an arbitrary subbasis, then we know
      there is a family `{Sᵢ}` of intersections of elements of `B`, such that `e = ⋃ i, Sᵢ`. 
      Since we know via `cjprime_iff_uncoverable'` that `e` is uncoverable, 
      it follows that there is some `i` such that `e ⇒ Sᵢ`, but we also know that `S_i ⇒ e`, as `Sᵢ ⇒ ⋃ i, Sᵢ = e`, 
      therefore `e = Sᵢ`. Furthermore, since `Sᵢ` is an intersection of a finite number of sets and 
      `e` is meet prime, we know via `entity.mprime.induction` that there is a `e'ᵢ ∈ Sᵢ` such that 
      `e'ᵢ ⇒ e`, and because `e = Sᵢ` we have also that `e ⇒ e'ᵢ`, as `Sᵢ ⇒ e'ᵢ` follows from the fact 
      `Sᵢ` is an intersection. As such we have `e = e'ᵢ`, but recall that `e'ᵢ ∈ B`, therefore `e ∈ B`.  
      `∎`
  -/
  
  theorem asubasic_iff_cprime : e.asubasic ↔ e.cprime :=
    begin
      constructor; intro h,
        by_contradiction contra,
        let B := {e' : ω.event | e' ≠ e ∧ e'.entitative},
        suffices c : is_subbasis B,
          specialize h c,
          simp [B] at h, unfold_coes at h,
          simp at h, contradiction,
        simp [is_subbasis],
        intros e', 
        by_cases hyp : e' = e, swap,
          use punit, use punit.star,
          use λ _, {e'}, unfold_coes, 
          simp [Union_const], unfold_coes,
          cases e, cases e', simp at hyp,
          simpa,
        cases hyp, clear hyp,
        have := e.cjprime_to_cjprime,
        simp only [contra, cjprime_iff_uncoverable'] at this,
        change ¬ (e.uncoverable' ∧ e.mprime) at this,
        push_neg at this, cases this, swap,
          simp [entity.mprime] at this,
          obtain ⟨e₁, e₂, ⟨h₁, h₂⟩, h₃⟩ := this,
          push_neg at h₃,
          obtain ⟨h₃, h₄⟩ := h₃,
          let x := (e₁ ⊔ e),
          let y := (e₂ ⊔ e),
          simp [has_entailment.entails] at h₃ h₄,
          use punit, use punit.star,
          use λ _, {x, y}, unfold_coes,
          constructor;
          simp [ Union_const, x, y], swap, 
            change (e₂.exists ∪ e.exists) ∩ (e₁.exists ∪ e.exists) = e.exists,
            rw ←inter_union_distrib_right,
            simp [has_entailment.entails, entity.compatible.inter] at h₂,
            apply union_eq_self_of_subset_left,
            rwa inter_comm,
          refine ⟨⟨x, _⟩, _⟩,
            unfold_coes, simp [x],
          simp [B, has_subset.subset, set.subset],
          rintro a (ha | ha); rw ha; simp; clear ha a;
          intros h; unfold_coes at h; rw ←h at *,
            change ¬set.subset e₂.exists (e₂.exists ∪ e.exists) at h₄,
            apply h₄, apply subset_union_left,
          change ¬set.subset e₁.exists (e₁.exists ∪ e.exists) at h₃,
          apply h₃, apply subset_union_left,
        simp [uncoverable'_iff_uncoverable] at this,
        replace this := e.non_disjoint_cover_of_uncoverable this,
        obtain ⟨S, h₁, h₂, neS, h₃, h₄⟩ := this,
        have : ∀ e' ∈ S, e' ∩ e.exists ≠ e.exists,
          intros e' he' absurdity,
          apply h₄; try{assumption},
          simp [has_entailment.entails, set.subset],
          rw ←absurdity, simp, tauto,
        obtain ⟨s, hs⟩ := neS,
        use S, use ⟨s, hs⟩,
        use λ s, {s.val ∩ e.exists},
        simp [this], constructor, 
          intros e' he', simp,
          refine ⟨this e' he', _⟩,
          refine ⟨_, h₂ e' he'⟩,
          apply topological_space.is_open_inter, swap,
            exact e.existential,
          exact (h₁ e' he').1,
        simp [has_entailment.entails] at h₃,
        rw ←Union_inter, apply eq_of_subset_of_subset,
          apply inter_subset_right,
        set aux := (⋃ (i : S), i.val),
        unfold_coes, simp,
        refine ⟨_, by refl⟩,
        convert h₃, simp [ext_iff],
      intros B h,
      obtain ⟨h₁, h₂⟩ := h,
      specialize h₂ e,
      obtain ⟨I, ne, S, ⟨h₂, h₃⟩⟩ := h₂,
      unfold_coes at h₃,
      have imp_e : ∀ i, ⋂₀ S i ⇒ e,
        intro i,
        have c := subset_Union (λ i, ⋂₀ S i) i,
        simp at c,
        rwa h₃ at c,
      have c := (cjprime_iff_uncoverable' e).mp h.to_cjprime,
      simp at c,
      rw ←sUnion_range at h₃,
      set B' := { s | s ∈ range (λ (x : I), ⋂₀ S x) ∧ s.nonempty},
      have neB' : B'.nonempty,
        simp [B', range, set.nonempty],
        by_contradiction contra,
        push_neg at contra,
        have c : ∀ i, ⋂₀ S i = ∅,
          intro i,
          specialize contra (⋂₀ S i),
          cases contra,
            specialize contra i,
            contradiction,
          apply not_nonempty_iff_eq_empty.mp,
          rintro ⟨w, hw⟩,
          specialize contra w,
          contradiction,
        replace c : (λ (x : I), ⋂₀ S x) = (λ (x : I), ∅),
          funext i, exact c i,
        rw c at h₃,
        simp [range, sUnion, ext_iff] at h₃,
        obtain ⟨w, hw⟩ := e.possible,
        specialize h₃ w, simp [hw] at h₃,
        obtain ⟨empty, ⟨i, absurd⟩, insanity⟩ := h₃,
        specialize absurd w,
        contradiction,
        clear ne,
      have hB' : ∀ (ev : ω.event), ev ∈ B' → ev.entitative,
        intros ev hev,
        simp [B', range] at hev,
        obtain ⟨⟨i, hi⟩, ne⟩ := hev,
        refine ⟨_, ne⟩,
        rw ←hi,
        apply is_open_sInter (h₂ i).1,
        intros t ht,
        replace ht := (h₂ i).2.2 ht,
        replace ht := h₁ t ht,
        exact ht.1,
      replace c := c hB' neB',
      specialize c _, swap,
        simp [has_entailment.entails],
        rw ←h₃,
        simp [sUnion, set.subset],
        intros w S' i hS' hw,
        exact ⟨S',⟨⟨i,hS'⟩,⟨w,hw⟩⟩,hw⟩,
      obtain ⟨e₂, H, he₂⟩ := c,
      simp [B', range] at H,
      obtain ⟨⟨i, hi⟩, aux⟩ := H, clear aux,
      rw ←hi at he₂, clear hi e₂,
      clear h₃ neB' hB' B',
      rename h₁ h₀,
      specialize h₂ i,
      obtain ⟨h₁, h₂, h₃⟩ := h₂,
      have c : (⋂₀ S i).nonempty,
        obtain ⟨w, hw⟩ := e.possible,
        replace hw := he₂ hw,
        exact ⟨w, hw⟩,
      replace h := h.1.2.induction h₂ _ h₁ c (imp_e i), swap,
        intros ev hev,
        apply h₀, apply h₃, assumption,
      clear c,
      obtain ⟨e₂, H, h⟩ := h,
      have c : e ⇒ e₂,
        have c := sInter_subset_of_mem H,
        exact subset.trans he₂ c,
      replace c := eq_of_subset_of_subset c h,
      unfold_coes at c,
      specialize h₃ H,
      rwa c,
    end

  lemma absolutely_real_iff_asubasic : e.absolutely_real ↔ e.asubasic :=
    begin
      constructor; intros h,
        intros B basis,
        specialize h basis.intensionalize,
        simp [entity.real, iontology.ientity.up] at h,
        obtain ⟨ie, hie⟩ := h,
        rw ←hie,
        change (subtype B) at ie,
        exact ie.property,
      intros Ω,
      simp [entity.real],
      specialize h Ω.axiom₁,
      simp [range] at h,
      simpa [entity.real, iontology.ientity.up, iontology.ientity.exists],
    end
  
  lemma absolutely_real_iff_cprime : e.absolutely_real ↔ e.cprime :=
    by convert (asubasic_iff_cprime e); ext; exact absolutely_real_iff_asubasic e

  -- theorem abasic_iff_cjprime : e.abasic ↔ e.cjprime :=
  --   begin
  --     simp [entity.abasic, entity.cjprime],
  --     constructor; intro h, swap,
  --       intros B hB,
  --   end
end prime_lemmas

-- lemmas involving prime entities and the necessary being
section nb_lemmas

  lemma nbe.mprime : ω.nbe.mprime :=
    by simp [entity.mprime]; intros; 
       simp [has_entailment.entails, nbe, set.subset]

  theorem weakly_parmenidean_iff₀ : ω.weakly_parmenidean ↔ ω.nbe.uncoverable :=
    begin
      simp,
      constructor; intro h,
        obtain ⟨w, hw⟩ := h,
        simp [parmenidean] at hw,
        intros S hS₁ hS₂ h, clear hS₂,
        simp [nbe, has_entailment.entails, set.subset] at h,
        specialize @h w,
        obtain ⟨ev, hev, h⟩ := h,
        specialize hS₁ ev hev,
        specialize hw ⟨ev, hS₁.1, hS₁.2⟩ h, simp at hw,
        refine ⟨ev, hev, _⟩, rw hw,
        simp [has_entailment.entails, set.subset],
      let S := {ev : ω.event | ev.contingent ∧ ev.entitative},
      specialize @h S _, swap,
        intros ev hev, exact hev.2,
      simp [nbe, has_entailment.entails, set.subset] at h,
      simp [set.nonempty, parmenidean],
      by_contradiction contra, push_neg at contra,
      by_cases c : S.nonempty, swap,
        simp [set.nonempty] at c,
        obtain ⟨w⟩ := ω.wne,
        specialize contra w,
        obtain ⟨e, hw, he⟩ := contra,
        simp [nbe] at he,
        specialize c e.exists w hw he,
        have absurdity := e.entitative,
        contradiction,
      specialize h c, clear c,
      specialize h _, swap,
        intro w, specialize contra w,
        obtain ⟨e, hw, he⟩ := contra,
        simp [nbe] at he,
        exact ⟨e.exists, ⟨⟨⟨e.possible,he⟩,e.entitative⟩,hw⟩⟩,
      clear contra,
      obtain ⟨insanity, ⟨⟨sophistry, illusion⟩, gibberish⟩, nonsense⟩ := h,
      have absurdity : insanity = univ,
        simpa [ext_iff],
      contradiction,
    end
  theorem weakly_parmenidean_iff₁ : ω.weakly_parmenidean ↔ ω.nbe.cprime :=
    begin
      convert weakly_parmenidean_iff₀,
      ext, constructor; intro h,
        replace h := h.to_cjprime,
        replace h := (cjprime_iff_uncoverable' ω.nbe).mp h,
        simp at h, assumption,
      replace h := (cjprime_iff_uncoverable ω.nbe).2 h,
      exact ⟨⟨h.1, nbe.mprime⟩, h.2⟩,
    end
  theorem weakly_parmenidean_iff₂ : ω.weakly_parmenidean ↔ ω.nbe.asubasic := 
    by convert weakly_parmenidean_iff₁; ext; exact asubasic_iff_cprime ω.nbe
  theorem weakly_parmenidean_iff₃ : ω.weakly_parmenidean ↔ ω.nbe.absolutely_real :=
    by convert weakly_parmenidean_iff₂; ext; exact absolutely_real_iff_asubasic ω.nbe


end nb_lemmas

-- We discuss particulars, universals, optional entities, and some unique notions of covering related to them; 
-- in terms of which the notions of exemplification and subjective parthood can be defined.
-- THIS SECTION IS VERY MUCH A WORK IN PROGRESS.
section particulars
  
  variable (e : ω.entity)

  /-- An entity is **particular** if it is substantially join prime. -/
  @[reducible, simp]
  def entity.particular := e.sjprime
  /-- An entity is a **(Neo-Aristotelian) universal** if it is not particular. -/
  @[reducible, simp]
  def entity.universal := ¬ e.sjprime
  /-- An entity is said to be a **proper particular** if it is substantially prime. -/
  @[reducible, simp]
  def entity.pparticular := e.sprime
  /-- An entity is said to be an **aggregate**, or an **improper particular**,
      if it is particular but not a proper particular. -/
  @[reducible, simp]
  def entity.aggregate := e.sjprime ∧ ¬ e.smprime
  /-- An entity is said to be an **ultra-particular** if it is prime. -/
  @[reducible, simp]
  def entity.uparticular := e.prime
  /-- An entity is said to be **monadic**, or **point-like**, if it is 
      completely prime. -/
  @[reducible, simp]
  def entity.monadic := e.cprime
  /-- An entity is said to be **angelic (or Divine)** if it is 
      both monadic and dense. -/
  @[reducible, simp]
  def entity.angelic := e.monadic ∧ e.exists.dense

   /-- An entity `e` is said to be **(strictly) directly covered** by an entity `e'`
      if `e ⇒' e'` and for every entity `e''` in between `e` and `e'`, 
       `e''` is either equal to `e` or to `e'`. -/
  def entity.dcovered (e' : ω.entity) := 
    e ⇒' e' ∧ ∀ e'' : ω.entity, 
    e ⇒ e'' → e'' ⇒ e' → e'' = e ∨ e'' = e'

  infixr ` :⇒ `:50 := entity.dcovered

  /-- An entity `e` is said to be **optionally covered** by an entity `e'` 
      if it is uniquely pre-covered by `e'`, i.e. if it is pre-coverd by `e'` but
      not pre-covered by anything else. -/
  def entity.ocovered (e' : ω.entity) := 
    e :⇒ e' ∧ ∀ e'', e :⇒ e'' → e'' = e'

  infixr ` !:⇒ `:50 := entity.ocovered

  /-- An entity is said to be **optional** if it is optionally covered by another. -/
  def entity.optional := ∃ e', e !:⇒ e'

  /-- Definition of **Particular Exact Minimal open cover**. -/
  def entity.pemcover (S : set ω.event) : Prop := 
    e.emcover S ∧ ∀ (s : ω.event), s ∈ S → 
    ∃ e' : ω.entity, e.particular ∧ e'.exists = s
  
  /-- Definition of **Infinite Particular Exact Minimal open cover**. -/
  def entity.ipemcover (S : set ω.event) : Prop := 
    e.pemcover S ∧ S.infinite

  /-- A particular entity `e` is said to **exemplify** another 
      universal entity `u`, just in case there is an unique ipemcover of
      `u` containing `e` which has only perfect elements if `e` is perfect,
      and only imperfect elements if `e` is imperfect. -/
  def entity.exemplifies (u : ω.entity) : Prop := 
    e.particular ∧ u.universal ∧
    ∃! S, u.ipemcover S ∧ e.exists ∈ S ∧
    (e.exists.dense → ∀ s : ω.event, s ∈ S → s.dense) ∧
    (¬ e.exists.dense → ∀ s : ω.event, s ∈ S → ¬ s.dense)

  /-- A particular entity `e` is said to be a **subjective part** of another 
      universal entity `u`, just in case there is an unique pemcover of
      `u` containing `e` which has only perfect elements if `e` is perfect,
      and only imperfect elements if `e` is imperfect.
      "Subjective" comes from the fact that `e` is the subject of
      a predication. -/
  def entity.spart (u : ω.entity) : Prop := 
    e.particular ∧ u.universal ∧
    ∃! S, u.pemcover S ∧ e.exists ∈ S ∧
    (e.exists.dense → ∀ s : ω.event, s ∈ S → s.dense) ∧
    (¬ e.exists.dense → ∀ s : ω.event, s ∈ S → ¬ s.dense)
  
  /-- An entity is said to be a **true universal** if it can be exemplified. -/
  def entity.tuniversal := ∃ e' : ω.entity, e'.exemplifies e

  /-- An universal is said to be a **subjective whole (collection, or set)** 
      if it has subjective parts. -/
  def entity.swhole := ∃ e' : ω.entity, e'.spart e

end particulars

-- lemmas about direct coverings and optional entities
-- THIS SECTION IS VERY MUCH A WORK IN PROGRESS.
section dcovered_lemmas

  variables (e₁ e₂ : ω.entity) (h₁ : e₁.exists.dense) (h₂ : e₂.exists.dense)
  include h₁ h₂

  -- lemma ocovered_of_dcovered_smprime : e₁.smprime → e₁ :⇒ e₂ → e₁ !:⇒ e₂ :=
  --   begin
  --     intros h₃ h₄,
  --     refine ⟨h₄, _⟩, 
  --     intros e₃ h₅,
  --     admit,
  --   end


end dcovered_lemmas


end ontology