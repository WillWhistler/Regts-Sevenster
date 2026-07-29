import RS.Novel.Envelope.SemisimpleAll

/-!
# Semisimplicity of Karoubi endomorphism algebras

The endomorphism algebra of any object of the Karoubi envelope of
the skein category is a corner `e·End(n)·e`, and the trace
criterion restricts: corner-nilpotents are ambient-nilpotents, and
cyclicity moves the idempotent across products, so ambient
nondegeneracy restricts to the corner.
-/

namespace RS

open CategoryTheory CategoryTheory.Idempotents

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### Linear structure on the Karoubi envelope -/

/-- The underlying-morphism map is additive. -/
private def karoubiHomAddHom (P Q : Karoubi (SkeinObj f)) :
    (P ⟶ Q) →+ (P.X ⟶ Q.X) where
  toFun g := g.f
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Scaling a Karoubi morphism through its underlying morphism. -/
noncomputable instance karoubiHomSMul
    (P Q : Karoubi (SkeinObj f)) : SMul ℂ (P ⟶ Q) where
  smul c g := ⟨c • g.f, by
    rw [CategoryTheory.Linear.smul_comp,
      CategoryTheory.Linear.comp_smul, g.comm]⟩

/-- Karoubi hom-sets are ℂ-modules. -/
noncomputable instance karoubiHomModule
    (P Q : Karoubi (SkeinObj f)) : Module ℂ (P ⟶ Q) :=
  Function.Injective.module ℂ (karoubiHomAddHom f P Q)
    (fun _ _ h => Karoubi.Hom.ext h) (fun _ _ => rfl)

/-- Hence the Karoubi envelope is ℂ-linear. -/
noncomputable instance karoubiLinear :
    CategoryTheory.Linear ℂ (Karoubi (SkeinObj f)) where
  smul_comp P Q R' c g h := by
    apply Karoubi.hom_ext
    show (c • g.f) ≫ h.f = c • (g.f ≫ h.f)
    rw [CategoryTheory.Linear.smul_comp]
  comp_smul P Q R' g c h := by
    apply Karoubi.hom_ext
    show g.f ≫ (c • h.f) = c • (g.f ≫ h.f)
    rw [CategoryTheory.Linear.comp_smul]

/-! ### The endomorphism algebras of Karoubi objects -/

variable (X : Karoubi (SkeinObj f))

/-- Endomorphisms of a Karoubi object form a ring. -/
noncomputable instance karoubiEndRing : Ring (End X) :=
  inferInstance

/-- And a ℂ-algebra — the corner `e·End(n)·e`. -/
noncomputable instance karoubiEndAlgebra : Algebra ℂ (End X) :=
  inferInstance

/-- The underlying-morphism map on endomorphisms, as a linear
map into the ambient strand algebra. -/
private noncomputable def endF :
    End X →ₗ[ℂ] skeinEnd f X.X.arity where
  toFun g := g.f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem endF_injective :
    Function.Injective (endF f X) := fun _ _ h =>
  Karoubi.Hom.ext h

/-- The underlying map is multiplicative (both `End`s compose in
reverse). -/
private theorem endF_mul (x y : End X) :
    endF f X (x * y) = endF f X x * endF f X y := rfl

/-- Finite-dimensional, as a subspace of the ambient skein
endomorphisms. -/
noncomputable instance karoubiEndFinite :
    FiniteDimensional ℂ (End X) :=
  FiniteDimensional.of_injective (endF f X)
    (endF_injective f X)

/-- The corner trace. -/
private noncomputable def cornerTrace : End X →ₗ[ℂ] ℂ :=
  (HomSpace.traceMap f.val X.X.arity).comp (endF f X)

/-- Corner-nilpotents are ambient-nilpotents. -/
private theorem endF_isNilpotent {x : End X}
    (hx : IsNilpotent x) : IsNilpotent (endF f X x) := by
  obtain ⟨k, hk⟩ := hx
  cases k with
  | zero =>
      refine ⟨1, ?_⟩
      have h10 : (1 : End X) = 0 := by
        rw [← pow_zero x, hk]
      have hx0 : x = 0 := by
        calc x = x * 1 := (mul_one x).symm
          _ = x * 0 := by rw [h10]
          _ = 0 := mul_zero x
      rw [hx0]
      simp
  | succ k =>
      refine ⟨k + 1, ?_⟩
      have : endF f X (x ^ (k + 1)) = (endF f X x) ^ (k + 1) := by
        clear hk
        induction k with
        | zero => simp
        | succ j ih =>
            rw [pow_succ, endF_mul, ih, ← pow_succ]
      rw [← this, hk, map_zero]

/-- **Semisimplicity of Karoubi endomorphism algebras.** -/
theorem karoubiEnd_isSemisimpleRing (P : SchurPackage.{1}) :
    IsSemisimpleRing (End X) := by
  refine isSemisimpleRing_of_trace (cornerTrace f X)
    (fun x hx =>
      skeinTrace_eq_zero_of_isNilpotent_all f P X.X.arity
        (endF_isNilpotent f X hx))
    (fun a ha => ?_)
  -- Nondegeneracy: sandwich an arbitrary ambient test morphism
  -- into the corner using cyclicity.
  have haf : a.f = 0 := by
    apply end_eq_zero_of_traces_vanish f X.X a.f
    intro b
    have hb : X.p ≫ (X.p ≫ b ≫ X.p) ≫ X.p =
        X.p ≫ b ≫ X.p := by
      simp only [Category.assoc]
      rw [show X.p ≫ X.p ≫ b ≫ X.p ≫ X.p =
        (X.p ≫ X.p) ≫ b ≫ (X.p ≫ X.p) from by
          simp only [Category.assoc]]
      rw [X.idem]
    have key := ha (⟨X.p ≫ b ≫ X.p, hb⟩ : End X)
    -- key computes the trace of `a.f ≫ (p ≫ b ≫ p)`, which is
    -- the trace of `a.f ≫ b` by absorption and cyclicity.
    have hred : a.f ≫ (X.p ≫ b ≫ X.p) =
        (a.f ≫ b) ≫ X.p := by
      rw [show a.f ≫ (X.p ≫ b ≫ X.p) =
        (a.f ≫ X.p) ≫ b ≫ X.p from by
          simp only [Category.assoc]]
      rw [Karoubi.comp_p]
      simp only [Category.assoc]
    have hcyc := HomSpace.traceMap_comp_comm f
      (t := X.X.arity) (u := X.X.arity)
      (a.f ≫ b) X.p
    have hfin : HomSpace.traceMap f.val X.X.arity
        (X.p ≫ (a.f ≫ b)) =
        HomSpace.traceMap f.val X.X.arity (a.f ≫ b) := by
      rw [show X.p ≫ (a.f ≫ b) =
        (X.p ≫ a.f) ≫ b from by
          simp only [Category.assoc]]
      rw [Karoubi.p_comp]
    calc HomSpace.traceMap f.val X.X.arity (a.f ≫ b)
        = HomSpace.traceMap f.val X.X.arity
            (X.p ≫ (a.f ≫ b)) := hfin.symm
      _ = HomSpace.traceMap f.val X.X.arity
            ((a.f ≫ b) ≫ X.p) := hcyc.symm
      _ = HomSpace.traceMap f.val X.X.arity
            (a.f ≫ (X.p ≫ b ≫ X.p)) := by rw [hred]
      _ = 0 := key
  exact Karoubi.Hom.ext haf

/-! ### Mixed-Hom nondegeneracy in the Karoubi envelope -/

/-- A Karoubi morphism all of whose composite traces against
reverse morphisms vanish is zero: the separation engine for the
simples. -/
theorem karoubiHom_eq_zero_of_traces_vanish
    {X Y : Karoubi (SkeinObj f)} (a : X ⟶ Y)
    (ha : ∀ b : Y ⟶ X,
      HomSpace.traceMap f.val X.X.arity (a.f ≫ b.f) = 0) :
    a = 0 := by
  apply Karoubi.hom_ext
  show a.f = 0
  apply hom_eq_zero_of_traces_vanish' f X.X Y.X a.f
  intro b
  have hb : Y.p ≫ (Y.p ≫ b ≫ X.p) ≫ X.p =
      Y.p ≫ b ≫ X.p := by
    rw [show Y.p ≫ (Y.p ≫ b ≫ X.p) ≫ X.p =
      (Y.p ≫ Y.p) ≫ b ≫ (X.p ≫ X.p) from by
        simp only [Category.assoc]]
    rw [Y.idem, X.idem]
  have key := ha (⟨Y.p ≫ b ≫ X.p, hb⟩ : Y ⟶ X)
  have hred : a.f ≫ (Y.p ≫ b ≫ X.p) =
      (a.f ≫ b) ≫ X.p := by
    rw [show a.f ≫ (Y.p ≫ b ≫ X.p) =
      (a.f ≫ Y.p) ≫ b ≫ X.p from by
        simp only [Category.assoc]]
    rw [Karoubi.comp_p]
    simp only [Category.assoc]
  have hcyc := HomSpace.traceMap_comp_comm f
    (t := X.X.arity) (u := X.X.arity)
    (a.f ≫ b) X.p
  have hfin : HomSpace.traceMap f.val X.X.arity
      (X.p ≫ (a.f ≫ b)) =
      HomSpace.traceMap f.val X.X.arity (a.f ≫ b) := by
    rw [show X.p ≫ (a.f ≫ b) = (X.p ≫ a.f) ≫ b from by
      simp only [Category.assoc]]
    rw [Karoubi.p_comp]
  calc HomSpace.traceMap f.val X.X.arity (a.f ≫ b)
      = HomSpace.traceMap f.val X.X.arity
          (X.p ≫ (a.f ≫ b)) := hfin.symm
    _ = HomSpace.traceMap f.val X.X.arity
          ((a.f ≫ b) ≫ X.p) := hcyc.symm
    _ = HomSpace.traceMap f.val X.X.arity
          (a.f ≫ (Y.p ≫ b ≫ X.p)) := by rw [hred]
    _ = 0 := key

end RS
