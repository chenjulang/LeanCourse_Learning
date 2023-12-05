import LeanCourse.Common
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.Minpoly.Basic
open BigOperators Function Ideal Polynomial Classical Matrix
noncomputable section
set_option linter.unusedVariables false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)


/- # Today: Abstract algebra

We cover section 8.2 from Mathematics in Lean and a bit of field theory and linear algebra. -/

/-
Last time we discussed projects and group theory
-/


/- # Rings -/

/- Lean uses `Ring` and `CommRing` for rings and commutative rings. -/
example : CommRing ℤ := by infer_instance

/- Also important are *semirings*, which are rings without postulating negation. -/
example : CommSemiring ℕ := by infer_instance


example : Field ℚ := by infer_instance


/- Note that the tactics for computation in a `Ring` vs `CommRing` is
`noncomm_ring` resp. `ring.-/
example {R : Type*} [CommRing R] (x y : R)
: (x + y)^2 = x^2 + y^2 + 2*x*y := by ring

example {R : Type*} [Semiring R] (x y : R)
: (x + y)^2 = x^2 + y^2 + x*y + y*x := by noncomm_ring

/- The binomial theorem. Note that the natural number `Nat.choose n m` is coerced to an element of `R` here. -/
example {R : Type*} [CommRing R] (x y : R) (n : ℕ) :
  (x + y) ^ n = ∑ m in Finset.range (n + 1), x ^ m * y ^ (n - m) * Nat.choose n m
  := by rw [@add_pow]

example {R : Type*} [Ring R] (x : R) : Prop := IsUnit x

/- We can write `Rˣ` for the units of a ring (i.e. the elements with a multiplicative inverse). -/
example (x : ℤˣ)
: x = 1 ∨ x = -1 := Int.units_eq_one_or x

example {R : Type*} [Ring R] : Group Rˣ := by
  infer_instance

/- We also have a predicate `IsUnit` stating whether an element of the ring is a unit. -/
example {R : Type*} [CommRing R] (x : R)
: IsUnit x ↔ ∃ y, x * y = 1
:= by exact isUnit_iff_exists_inv

/- We write ring homomorphisms with `→+*`. -/
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y ∧ f (x * y) = f x * f y ∧
    f 1 = 1 ∧ f 0 = 0 :=
  ⟨f.map_add x y, f.map_mul x y, f.map_one, f.map_zero⟩

/- A subring is a subset of `R` that is an additive subgroup and multiplicative submonoid.

As subgroups, subrings are bundled as a set with closure properties.
They are less useful, since we cannot quotient by a subring.  -/
example {R : Type*} [Ring R] (S : Subring R) : Ring S := by infer_instance



/- ## Ideals -/


section Ring
variable {R : Type*} [CommRing R] {I J : Ideal R}

/- Ideals are additive subgroups that are closed under arbitary multiplication. -/
example {x y : R} (hy : y ∈ I)
: x * y ∈ I :=
  I.mul_mem_left x hy

example {x y : R} (hx : x ∈ I)
: x * y ∈ I :=
  I.mul_mem_right y hx



/- There are various operations on ideals. -/

example : I + J = I ⊔ J := rfl

example {x : R}
: x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x
:= by
  simp [Submodule.mem_sup]

example : I * J ≤ I ⊓ J := mul_le_inf

example : CompleteLattice (Ideal R) := by infer_instance
example : Semiring (Ideal R) := by
  infer_instance




/- We write `Ideal.span s` for the smallest ideal containing `s`.
In particular, `Ideal.span {a}` is the principal ideal generated by `a`. -/

/- Exercise -/
example (n m : ℤ)
: span {n} ⊔ span {m} = span {gcd n m}
:= by sorry

/- Exercise -/
example (n m : ℤ)
: span {n} ⊓ span {m} = span {lcm n m}
:= by sorry

example (n m : ℤ)
: span {n} * span {m} = span {n * m}
:= by
  rw?

/- We can quotient a ring by an ideal. -/

example {R : Type*} [CommRing R] (I : Ideal R)
: R →+* R ⧸ I
:=
  Ideal.Quotient.mk I

example {R : Type*} [CommRing R] (I : Ideal R) [h : I.IsPrime]
: IsDomain (R ⧸ I)
:= by
  show_term infer_instance

example {R : Type*} [CommRing R] (I : Ideal R) [h : I.IsMaximal]
: Field (R ⧸ I)
:=
  Quotient.field I


/- We can prove the Chinese remainder theorem for ideals. -/

example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j))
    : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i
    :=
  Ideal.quotientInfRingEquivPiQuotient f hf

/- Note that we re-use the generic definition of `IsCoprime` here. -/
#print IsCoprime

/- From this we can easily get the traditional version for `ℤ/nℤ`. -/

example (n : ℕ)
: Ring (ZMod n)
:= by infer_instance

example {ι : Type*} [Fintype ι] (a : ι → ℕ) (ha : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
    ZMod (∏ i, a i) ≃+* ∀ i, ZMod (a i)
    :=
  ZMod.prodEquivPi a ha



example {R : Type*} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] (I : Ideal R) :
    ∃ x : R, I = span {x}
    := by exact?





#where
variable {A : Type*} [Semiring A] [Algebra R A]

/- # Algebras and polynomials -/

/- An *algebra* (or associative unital algebra) `A` over a ring `R`
is a semiring `A` equipped with a ring homomorphism `R →+* A`
whose image commutes with every element of `A`. -/
example
: R →+* A
:= algebraMap R A

example (r : R) (a : A)
: algebraMap R A r * a = a * algebraMap R A r
:= Algebra.commutes r a

/- We can also denote `algebraMap R A r * a` using scalar multiplication as `r • a`. -/
example (r : R) (a : A)
: r • a = algebraMap R A r * a
:= Algebra.smul_def r a

/- Note that if `F` and `E` are both fields,
then `[Algebra F E]` states exactly that `E` is a field extension of `F`. -/


/- An important algebra is the polynomial ring `R[X]` or `Polynomial R`. -/

example
: Algebra R R[X]
:= by infer_instance

example {R : Type*} [CommRing R]
: R[X] := X

example {R : Type*} [CommRing R] (r : R)
: R[X] :=
  X - C r

/- `C` is registered as a ring homomorphism. -/
#check C

example {R : Type*} [CommRing R] (r : R)
:
    (X + C r) * (X - C r) = X^2 - C (r ^ 2)
    := by
  ring
  rw [C.map_pow]

/- You can access coefficients using `Polynomial.coeff` -/

example {R : Type*} [CommRing R] (r : R) :
  (C r).coeff 0 = r
  := by simp

example {R : Type*} [CommRing R] : (X^2 + 2*X + C 3 : R[X]).coeff 1 = 2 := by simp

/- Defining the degree of a polynomial is tricky because of the special case of the zero polynomial. Mathlib has two variants -/
#check natDegree (R := R)
#check degree (R := R)

example [IsDomain R] (p q : R[X]) :
    degree (p * q) = degree p + degree q := by
  exact degree_mul

example [IsDomain R] (p q : R[X]) (hp : p ≠ 0)
    (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q := by
  refine natDegree_mul hp hq


/- `WithBot ℕ` can be seen as `ℕ ∪ {-∞}`, except that `-∞` is denoted `⊥`. -/

/- We can evaluate polynomials using `Polynomial.eval`. -/
#check eval (R := R)
example {R : Type*} [CommRing R] (P : R[X]) (x : R) : R := P.eval x

example {R : Type*} [CommRing R] (P : R[X]) (x : R) : R := eval x P

example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp

/- If `P : R[X]`, then we often want to evaluate `P` in algebras over `R`. E.g. we want to say that `X ^ 2 - 2 : ℚ[X]` has a root in `ℝ` -/
#check aeval (R := R) (A := A)

example : aeval Complex.I (X ^ 2 + 1 : ℝ[X]) = 0 := by simp



end Ring




/- # Fields

Lean's library contains various results field theory and Galois theory. -/

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/- Here are some important notions in field theory. -/

#check IntermediateField
#check IsSplittingField
#check IsAlgClosed
#check IsGalois
#check NumberField

example {x : L} (hx : IsAlgebraic K x) : aeval x (minpoly K x) = 0 := by rw [minpoly.aeval]

example : IsAlgClosed ℂ := by infer_instance

end Field






section LinearAlgebra

/- # Modules and vector spaces

Most results in linear algebra are not formulated in terms of vector spaces,
but instead they are generalized to modules over a (semi)ring.

A module `M` over a ring `R` is an abelian group `(M, +)` together with a scalar multiplication
`R → M → M` with appropriate associativity and distributivity laws. -/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

example (r : R) (x y : M) : r • (x + y) = r • x + r • y := by exact?
example (r s : R) (x : M) : (r + s) • x = r • x + s • x := by exact?
example (r s : R) (x : M) : (r * s) • x = r • s • x := by exact?
example (x : M) : (0 : R) • x = 0 := by exact?
example (x : M) : (1 : R) • x = x := by exact?
example (r : R) : r • (0 : M) = 0 := by exact?

/- We have linear maps between modules. -/
variable {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

#check M →ₗ[R] N

example (f : M →ₗ[R] N) (g : M →ₗ[R] N') :
  M →ₗ[R] N × N' where
    toFun := fun m ↦ (f m, g m)
    map_add' := by
      simp
    map_smul' := by
      dsimp
      simp

example : M × N →ₗ[R] M := sorry

example : M →ₗ[R] M × N := sorry

/- Linear maps themselves form a module over `R` (requires that `R` is commutative) -/
example : Module R (M →ₗ[R] N) := by infer_instance




/- Matrices are defined in Mathlib,
but generally we prefer to work abstractly with vector spaces (or modules) without choosing a basis. So we prefer working with linear maps directly, instead of working with matrices. -/
#check Matrix

example {m n : Type*} (M : Matrix m n M) : Mᵀᵀ = M := rfl

/- Bilinear maps are represented as an iterated linear maps. -/
example (f : M →ₗ[R] N →ₗ[R] N') : N →ₗ[R] M →ₗ[R] N' := f.flip


/- We use `ι → ℝ` to denote `ℝ^n` if `ι` has `n` elements. -/
example {ι : Type*} : Module ℝ (ι → ℝ) := by infer_instance

section product

variable {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/- We can also take a (infinitary) product of modules. -/
example : Module R (Π i, M i) := by infer_instance

example (f : Π i, M i) (i : ι) : M i := f i

example (f : Π i, M i) (i₀ : ι) (x : M i₀) :
  Π i, M i := fun j : ι ↦ Function.update f i₀ x j

example (r : R) (f : Π i, M i) (i : ι) :
  (r • f) i = r • f i := by simp

example (r : R) (f : Π i, M i) (i₀ : ι) (x : M i₀) :
    r • Function.update f i₀ x = Function.update (r • f) i₀ (r • x) := by
  ext j
  simp
  by_cases h : j = i₀
  · subst h
    simp
  · simp [h]

end product

example {ι : Type*} (b : Basis ι R M) : M ≃ₗ[R] ι →₀ R := b.repr

example {ι : Type*} {v : ι → M} (hli : LinearIndependent R v)
    (hsp : ⊤ ≤ Submodule.span R (Set.range v)) : Basis ι R M := by exact?

end LinearAlgebra

variable {R M : Type*}

/- # Exercises -/

theorem units_ne_neg_self [Ring R] [CharZero R] (u : Rˣ) : u ≠ -u := by sorry


example (n m : ℤ) : span {n} ⊔ span {m} = span {gcd n m} := by sorry

example (n m : ℤ) : span {n} ⊓ span {m} = span {lcm n m} := by sorry


/- Show that transposing a matrix gives rise to a linear equivalence. -/
example {m n : Type*} [Ring R] [AddCommGroup M] [Module R M] :
  Matrix m n M ≃ₗ[R] Matrix n m M where
    toFun := fun M ↦ Mᵀ
    map_add' := by sorry
    map_smul' := by sorry
    invFun := by sorry
    left_inv := by sorry
    right_inv := by sorry


/- In a module over a ring with characteristic 2, for every element `m` we have `m + m = 0`. -/
example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [CharP R 2] (m : M) :
    m + m = 0 := by sorry

section Frobenius

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] (x : K)
/- Let's define the Frobenius morphism. You can use lemmas from the library -/
def frobeniusMorphism : K →+* K :=
  { toFun := fun x ↦ x^p
    map_one' := by sorry
    map_mul' := by sorry
    map_zero' := by sorry
    map_add' := by sorry }

@[simp] lemma frobeniusMorphism_def (x : K) : frobeniusMorphism p K x = x ^ p := rfl

lemma iterate_frobeniusMorphism (n : ℕ) : (frobeniusMorphism p K)^[n] x = x ^ p ^ n := by sorry

lemma frobeniusMorphism_injective : Function.Injective (frobeniusMorphism p K) := by
  have : ∀ x : K, x ^ p = 0 → x = 0 := by exact?
  sorry

lemma frobeniusMorphism_bijective [Finite K] :
    Function.Bijective (frobeniusMorphism p K) := by sorry

example [Finite K] [CharP K 2] (x : K) : IsSquare x := by sorry

example (k : ℕ) (x : K) : x ^ p ^ k = 1 ↔ x = 1 := by sorry

open Nat Finset in
/- Let's prove that the Frobenius morphism is in fact additive, without using that
fact from the library. This exercise is challenging! -/
example (x y : K) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]
  sorry

end Frobenius



/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
  We have to additionally assume that `M` contains at least two elements, and
  `smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).-/
example {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by
  sorry
