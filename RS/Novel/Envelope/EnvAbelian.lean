import RS.Novel.Envelope.NilpotentMatTrace

/-!
# The envelope and its regularity

The envelope of the skein category is the Karoubi completion of
the matrix envelope of its Karoubi completion:
idempotent-complete by construction, with finite biproducts, and
with semisimple endomorphism algebras via the corner-trace
argument one level up.  Von Neumann regularity
of every morphism follows from semisimplicity of the biproduct
endomorphism algebra, and kernels are the splittings of the
regular idempotents.
-/

namespace RS

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits

universe u

/-! ### Regularity in semisimple rings -/

/-- Semisimple rings are von Neumann regular. -/
theorem exists_mul_mul_self {A : Type u} [Ring A]
    [IsSemisimpleRing A] (a : A) : ∃ b, a * b * a = a := by
  obtain ⟨e, he, hspan⟩ :=
    IsSemisimpleRing.ideal_eq_span_idempotent
      (Ideal.span {a})
  have hae : a ∈ Ideal.span {e} := by
    rw [← hspan]
    exact Ideal.subset_span rfl
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hae
  have hea : e ∈ Ideal.span {a} := by
    rw [hspan]
    exact Ideal.subset_span rfl
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hea
  refine ⟨s, ?_⟩
  calc a * s * a = a * (s * a) := by rw [mul_assoc]
    _ = a * e := by rw [hs]
    _ = r * e * e := by rw [hr]
    _ = r * (e * e) := by rw [mul_assoc]
    _ = r * e := by rw [he]
    _ = a := hr

/-! ### The envelope -/

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The envelope: the Karoubi completion of the matrix envelope of
the Karoubi completion of the skein category — `Kar(Add(Kar(𝒞_f)))`
where the accompanying paper's Cauchy completion `𝒟_f` (§3.4) is
`Kar(Add(𝒞_f))`.

The two agree up to equivalence, both being Cauchy completions of
`𝒞_f`, and the inner Karoubi carries its weight in the proofs: an
atom is the image of an atomic idempotent of a skein endomorphism
algebra, so atoms exist only where idempotents split, and the
nilpotent-trace argument for the matrix envelope reads the atomic
decomposition of each matrix entry
(`AtomicIdempotents.lean`, `AtomDichotomy.lean`,
`NilpotentMatTrace.lean`).  The outer Karoubi is still needed:
the additive envelope of an idempotent-complete category need not
be idempotent-complete. -/
@[reducible] def Env := Karoubi (Mat_ (Karoubi (SkeinObj f)))

/-! ### Linear structure (general Karoubi over a linear base) -/

section GeneralKaroubiLinear

variable (C : Type*) [Category C] [Preadditive C]
  [CategoryTheory.Linear ℂ C]

/-- Scaling a Karoubi morphism through its underlying morphism. -/
noncomputable instance karoubiHomSMul' (P Q : Karoubi C) :
    SMul ℂ (P ⟶ Q) where
  smul c g := ⟨c • g.f, by
    rw [CategoryTheory.Linear.smul_comp,
      CategoryTheory.Linear.comp_smul, g.comm]⟩

private def karoubiHomAddHom' (P Q : Karoubi C) :
    (P ⟶ Q) →+ (P.X ⟶ Q.X) where
  toFun g := g.f
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Karoubi hom-sets are ℂ-modules. -/
noncomputable instance karoubiHomModule' (P Q : Karoubi C) :
    Module ℂ (P ⟶ Q) :=
  Function.Injective.module ℂ (karoubiHomAddHom' C P Q)
    (fun _ _ h => Karoubi.Hom.ext h) (fun _ _ => rfl)

/-- Hence the Karoubi completion is ℂ-linear. -/
noncomputable instance karoubiLinear' :
    CategoryTheory.Linear ℂ (Karoubi C) where
  smul_comp P Q R' c g h := by
    apply Karoubi.hom_ext
    show (c • g.f) ≫ h.f = c • (g.f ≫ h.f)
    rw [CategoryTheory.Linear.smul_comp]
  comp_smul P Q R' g c h := by
    apply Karoubi.hom_ext
    show g.f ≫ (c • h.f) = c • (g.f ≫ h.f)
    rw [CategoryTheory.Linear.comp_smul]

end GeneralKaroubiLinear

/-! ### Semisimplicity of envelope endomorphism algebras -/

variable (E : Env f)

/-- The envelope corner trace. -/
noncomputable def envTrace : End E →ₗ[ℂ] ℂ where
  toFun x := matTrace f E.X x.f
  map_add' x y := by
    show matTrace f E.X (x + y).f = _
    rw [show (x + y).f = x.f + y.f from rfl]
    exact (matTrace f E.X).map_add _ _
  map_smul' c x := by
    show matTrace f E.X (c • x).f = _
    rw [show (c • x).f = c • x.f from rfl, RingHom.id_apply]
    exact (matTrace f E.X).map_smul _ _

/-- Corner-nilpotents are ambient-nilpotents (envelope
version). -/
private theorem envF_isNilpotent {x : End E}
    (hx : IsNilpotent x) :
    IsNilpotent (show End E.X from x.f) := by
  obtain ⟨k, hk⟩ := hx
  cases k with
  | zero =>
      refine ⟨1, ?_⟩
      have h10 : (1 : End E) = 0 := by
        rw [← pow_zero x, hk]
      have hx0 : x = 0 := by
        calc x = x * 1 := (mul_one x).symm
          _ = x * 0 := by rw [h10]
          _ = 0 := mul_zero x
      rw [hx0]
      rw [pow_one]
      rfl
  | succ k =>
      refine ⟨k + 1, ?_⟩
      have hmul : ∀ y z : End E,
          (show End E.X from (y * z).f) =
            (show End E.X from y.f) *
              (show End E.X from z.f) :=
        fun _ _ => rfl
      have hpow : (show End E.X from (x ^ (k + 1)).f) =
          (show End E.X from x.f) ^ (k + 1) := by
        clear hk
        induction k with
        | zero =>
            rw [pow_one, pow_one]
        | succ j ih =>
            rw [pow_succ, hmul, ih, ← pow_succ]
      rw [← hpow, hk]
      rfl

/-- **Semisimplicity of envelope endomorphism algebras.** -/
theorem envEnd_isSemisimpleRing (P : SchurPackage.{1}) :
    IsSemisimpleRing (End E) := by
  haveI : FiniteDimensional ℂ (End E) :=
    FiniteDimensional.of_injective
      (⟨⟨fun (x : End E) => x.f, fun _ _ => rfl⟩,
        fun _ _ => rfl⟩ :
        End E →ₗ[ℂ] (E.X ⟶ E.X))
      (fun _ _ h => Karoubi.Hom.ext h)
  refine isSemisimpleRing_of_trace (envTrace f E)
    (fun x hx =>
      matTrace_eq_zero_of_isNilpotent' P
        (envF_isNilpotent f E hx))
    (fun a ha => ?_)
  -- Nondegeneracy: sandwich ambient tests into the corner.
  apply Karoubi.hom_ext
  show a.f = 0
  apply matEnd_eq_zero_of_traces_vanish f
    (show End E.X from a.f)
  intro b
  have hb : E.p ≫ (E.p ≫ b ≫ E.p) ≫ E.p =
      E.p ≫ b ≫ E.p := by
    rw [show E.p ≫ (E.p ≫ b ≫ E.p) ≫ E.p =
      (E.p ≫ E.p) ≫ b ≫ (E.p ≫ E.p) from by
        simp only [Category.assoc]]
    rw [E.idem]
  have key := ha (⟨E.p ≫ b ≫ E.p, hb⟩ : End E)
  have hred : a.f ≫ (E.p ≫ b ≫ E.p) =
      (a.f ≫ b) ≫ E.p := by
    rw [show a.f ≫ (E.p ≫ b ≫ E.p) =
      (a.f ≫ E.p) ≫ b ≫ E.p from by
        simp only [Category.assoc]]
    rw [Karoubi.comp_p]
    simp only [Category.assoc]
  calc matTrace f E.X (b * (show End E.X from a.f))
      = matTrace f E.X (a.f ≫ b) := rfl
    _ = matTrace f E.X (E.p ≫ (a.f ≫ b)) := by
        rw [show E.p ≫ (a.f ≫ b) =
          (E.p ≫ a.f) ≫ b from by
            simp only [Category.assoc]]
        rw [Karoubi.p_comp]
    _ = matTrace f E.X ((a.f ≫ b) ≫ E.p) := by
        rw [matTrace_comp_comm f (E.p) (a.f ≫ b)]
    _ = matTrace f E.X (a.f ≫ (E.p ≫ b ≫ E.p)) := by
        rw [hred]
    _ = 0 := key

/-! ### Regularity of envelope morphisms -/

/-- Every envelope morphism is von Neumann regular. -/
theorem env_hom_regular (P : SchurPackage.{1})
    {M N : Env f} (u : M ⟶ N) :
    ∃ g : N ⟶ M, u ≫ g ≫ u = u := by
  haveI : HasFiniteBiproducts (Env f) := inferInstance
  haveI : HasBinaryBiproducts (Env f) :=
    hasBinaryBiproducts_of_finite_biproducts _
  haveI := envEnd_isSemisimpleRing f (M ⊞ N) P
  obtain ⟨G, hG⟩ := exists_mul_mul_self
    (A := End (M ⊞ N))
    ((biprod.fst ≫ u ≫ biprod.inr : End (M ⊞ N)))
  have hG' : (biprod.fst ≫ u ≫ biprod.inr) ≫ G ≫
      (biprod.fst ≫ u ≫ biprod.inr) =
      biprod.fst ≫ u ≫ biprod.inr := hG
  refine ⟨biprod.inr ≫ G ≫ biprod.fst, ?_⟩
  have h := congrArg
    (fun z => (biprod.inl : M ⟶ M ⊞ N) ≫ z ≫
      (biprod.snd : M ⊞ N ⟶ N)) hG'
  simpa using h

/-! ### Kernels -/

/-- The kernel idempotent of a regular pair. -/
private theorem env_ker_idem {M N : Env f} (u : M ⟶ N)
    (g : N ⟶ M) (hg : u ≫ g ≫ u = u) :
    (𝟙 M - u ≫ g) ≫ (𝟙 M - u ≫ g) = 𝟙 M - u ≫ g := by
  have h2 : (u ≫ g) ≫ u ≫ g = u ≫ g := by
    rw [show (u ≫ g) ≫ u ≫ g = (u ≫ g ≫ u) ≫ g from by
      simp only [Category.assoc]]
    rw [hg]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Category.comp_id, h2]
  abel

/-- Kernels exist in the envelope. -/
theorem env_hasKernels (P : SchurPackage.{1}) :
    HasKernels (Env f) := by
  constructor
  intro M N u
  obtain ⟨g, hg⟩ := env_hom_regular f P u
  obtain ⟨K, i, e, hie, hei⟩ :=
    IsIdempotentComplete.idempotents_split M (𝟙 M - u ≫ g)
      (env_ker_idem f u g hg)
  have hik : i ≫ (𝟙 M - u ≫ g) = i := by
    rw [← hei,
      show i ≫ e ≫ i = (i ≫ e) ≫ i from
        (Category.assoc _ _ _).symm,
      hie, Category.id_comp]
  have hku : (𝟙 M - u ≫ g) ≫ u = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp,
      show (u ≫ g) ≫ u = u from by
        rw [Category.assoc, hg],
      sub_self]
  have hiu : i ≫ u = 0 := by
    rw [← hik, Category.assoc, hku, Limits.comp_zero]
  exact HasLimit.mk ⟨KernelFork.ofι i hiu,
    KernelFork.IsLimit.ofι i hiu
      (fun {W'} g' _ => g' ≫ e)
      (fun {W'} g' hg' => by
        rw [Category.assoc, hei,
          Preadditive.comp_sub, Category.comp_id,
          show g' ≫ u ≫ g = (g' ≫ u) ≫ g from
            (Category.assoc _ _ _).symm,
          hg', Limits.zero_comp, sub_zero])
      (fun {W'} g' hg' m hm => by
        rw [← hm, Category.assoc, hie, Category.comp_id])⟩

/-! ### Cokernels -/

/-- Cokernels exist in the envelope. -/
theorem env_hasCokernels (P : SchurPackage.{1}) :
    HasCokernels (Env f) := by
  constructor
  intro M N u
  obtain ⟨g, hg⟩ := env_hom_regular f P u
  have hidem : (𝟙 N - g ≫ u) ≫ (𝟙 N - g ≫ u) =
      𝟙 N - g ≫ u := by
    have h2 : (g ≫ u) ≫ g ≫ u = g ≫ u := by
      rw [show (g ≫ u) ≫ g ≫ u = g ≫ (u ≫ g ≫ u) from by
        simp only [Category.assoc]]
      rw [hg]
    simp only [Preadditive.sub_comp, Preadditive.comp_sub,
      Category.id_comp, Category.comp_id, h2]
    abel
  obtain ⟨K', i', e', hie', hei'⟩ :=
    IsIdempotentComplete.idempotents_split N (𝟙 N - g ≫ u)
      hidem
  have hke : (𝟙 N - g ≫ u) ≫ e' = e' := by
    rw [← hei', Category.assoc, hie', Category.comp_id]
  have huk : u ≫ (𝟙 N - g ≫ u) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id,
      show u ≫ g ≫ u = u from hg, sub_self]
  have hue : u ≫ e' = 0 := by
    rw [← hke,
      show u ≫ (𝟙 N - g ≫ u) ≫ e' =
        (u ≫ (𝟙 N - g ≫ u)) ≫ e' from
        (Category.assoc _ _ _).symm,
      huk, Limits.zero_comp]
  exact HasColimit.mk ⟨CokernelCofork.ofπ e' hue,
    CokernelCofork.IsColimit.ofπ e' hue
      (fun {W'} g' _ => i' ≫ g')
      (fun {W'} g' hg' => by
        rw [show e' ≫ i' ≫ g' = (e' ≫ i') ≫ g' from
          (Category.assoc _ _ _).symm, hei',
          Preadditive.sub_comp, Category.id_comp,
          show (g ≫ u) ≫ g' = g ≫ (u ≫ g') from
            Category.assoc _ _ _,
          hg', Limits.comp_zero, sub_zero])
      (fun {W'} g' hg' m hm => by
        rw [← hm,
          show i' ≫ e' ≫ m = (i' ≫ e') ≫ m from
            (Category.assoc _ _ _).symm,
          hie', Category.id_comp])⟩

/-! ### Monomorphisms and epimorphisms split -/

/-- Monomorphisms split. -/
theorem env_mono_split (P : SchurPackage.{1})
    {M N : Env f} (m : M ⟶ N) [Mono m] :
    ∃ r : N ⟶ M, m ≫ r = 𝟙 M := by
  obtain ⟨g, hg⟩ := env_hom_regular f P m
  refine ⟨g, ?_⟩
  have h : (m ≫ g) ≫ m = 𝟙 M ≫ m := by
    rw [Category.id_comp, Category.assoc, hg]
  exact (cancel_mono m).mp h

/-- Epimorphisms split. -/
theorem env_epi_split (P : SchurPackage.{1})
    {M N : Env f} (e : M ⟶ N) [Epi e] :
    ∃ s : N ⟶ M, s ≫ e = 𝟙 N := by
  obtain ⟨g, hg⟩ := env_hom_regular f P e
  refine ⟨g, ?_⟩
  have h : e ≫ (g ≫ e) = e ≫ 𝟙 N := by
    rw [Category.comp_id, hg]
  exact (cancel_epi e).mp h

/-! ### Normality and the abelian structure -/

set_option warn.classDefReducibility false in
/-- Every mono is a kernel. -/
noncomputable def envNormalMono (P : SchurPackage.{1})
    {M N : Env f} (m : M ⟶ N) [Mono m] :
    NormalMono m := by
  have hex := env_mono_split f P m
  refine
    { Z := N
      g := 𝟙 N - hex.choose ≫ m
      w := ?_
      isLimit := KernelFork.IsLimit.ofι m ?_
        (fun {W'} t _ => t ≫ hex.choose)
        (fun {W'} t ht => ?_)
        (fun {W'} t ht m' hm' => ?_) }
  · rw [Preadditive.comp_sub, Category.comp_id,
      show m ≫ hex.choose ≫ m = (m ≫ hex.choose) ≫ m from
        (Category.assoc _ _ _).symm,
      hex.choose_spec, Category.id_comp, sub_self]
  · rw [Preadditive.comp_sub, Category.comp_id,
      show m ≫ hex.choose ≫ m = (m ≫ hex.choose) ≫ m from
        (Category.assoc _ _ _).symm,
      hex.choose_spec, Category.id_comp, sub_self]
  · have ht' : t ≫ hex.choose ≫ m = t := by
      have h0 := ht
      rw [Preadditive.comp_sub, Category.comp_id,
        sub_eq_zero] at h0
      rw [show t ≫ hex.choose ≫ m =
        t ≫ (hex.choose ≫ m) from rfl, ← h0]
    rw [Category.assoc]
    exact ht'
  · rw [← hm']
    rw [Category.assoc,
      show m ≫ hex.choose = 𝟙 M from hex.choose_spec,
      Category.comp_id]

set_option warn.classDefReducibility false in
/-- Every epi is a cokernel. -/
noncomputable def envNormalEpi (P : SchurPackage.{1})
    {M N : Env f} (e : M ⟶ N) [Epi e] :
    NormalEpi e := by
  have hex := env_epi_split f P e
  refine
    { W := M
      g := 𝟙 M - e ≫ hex.choose
      w := ?_
      isColimit := CokernelCofork.IsColimit.ofπ e ?_
        (fun {W'} t _ => hex.choose ≫ t)
        (fun {W'} t ht => ?_)
        (fun {W'} t ht m' hm' => ?_) }
  · rw [Preadditive.sub_comp, Category.id_comp,
      Category.assoc, hex.choose_spec, Category.comp_id,
      sub_self]
  · rw [Preadditive.sub_comp, Category.id_comp,
      Category.assoc, hex.choose_spec, Category.comp_id,
      sub_self]
  · have ht' : (e ≫ hex.choose) ≫ t = t := by
      have h0 := ht
      rw [Preadditive.sub_comp, Category.id_comp,
        sub_eq_zero] at h0
      exact h0.symm
    rw [show e ≫ hex.choose ≫ t =
      (e ≫ hex.choose) ≫ t from
      (Category.assoc _ _ _).symm]
    exact ht'
  · rw [← hm']
    rw [show hex.choose ≫ e ≫ m' =
      (hex.choose ≫ e) ≫ m' from
      (Category.assoc _ _ _).symm,
      hex.choose_spec, Category.id_comp]

set_option warn.classDefReducibility false in
/-- **The envelope is abelian** (conditional on the Schur
package). -/
@[reducible]
noncomputable def envAbelian (P : SchurPackage.{1}) :
    Abelian (Env f) := by
  haveI : HasFiniteBiproducts (Env f) := inferInstance
  haveI := env_hasKernels f P
  haveI := env_hasCokernels f P
  exact
    { normalMonoOfMono := fun m => ⟨envNormalMono f P m⟩
      normalEpiOfEpi := fun e => ⟨envNormalEpi f P e⟩ }

end RS
