0.全证明打印：
theorem IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots'.{u_4} : ∀ {R : Type u_4} [inst : CommRing R]
  [inst_1 : IsDomain R] {ζ : R} {n : ℕ+},
  IsPrimitiveRoot ζ ↑n → nthRootsFinset (↑n) R = Finset.biUnion (Nat.divisors ↑n) fun i ↦ primitiveRoots i R :=
fun {R} [CommRing R] [IsDomain R] {ζ} {n} h ↦
  (eq_of_subset_of_card_le
      (fun ⦃x⦄ ↦
        Eq.mpr
          (id
            (implies_congr
              («lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.34.trans
                (congrArg Exists
                  (_root_.funext fun a ↦
                    congrFun
                      (congrArg And
                        ((«lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.36.trans
                              (congrArg (And (a ∣ ↑n))
                                ((congrArg Not
                                      («lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.38
                                        n)).trans
                                  «lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.40))).trans
                          («lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.37 (a ∣ ↑n))))
                      (x ∈ primitiveRoots a R))))
              (((congrArg (Membership.mem x) (Multiset.toFinset_eq (nthRoots_nodup h)).symm).trans
                    «lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.28).trans
                («lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.35
                  (of_eq_true («lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.39 n))))))
          fun a ↦
          Exists.casesOn a fun a h ↦
            And.casesOn h fun left ha ↦
              Exists.casesOn left fun d hd ↦
                let_fun hazero :=
                  Mathlib.Tactic.Contrapose.mtr
                    (Eq.mpr (id (implies_congr (Mathlib.Tactic.PushNeg.not_lt_eq 0 a) (Eq.refl (↑n ≠ a * d)))) fun ha0 ↦
                      Eq.mpr
                        (id
                          (congrArg (Ne ↑n)
                            ((congrFun
                                  (congrArg HMul.hMul
                                    (id
                                      (Eq.mp «lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.41
                                        ha0)))
                                  d).trans
                              (zero_mul d))))
                        (PNat.ne_zero n))
                    hd;
                Eq.mpr (id (hd ▸ Eq.refl (x ^ ↑n = 1)))
                  (Eq.mpr (id (pow_mul x a d ▸ Eq.refl (x ^ (a * d) = 1)))
                    (Eq.mpr
                      (id
                        ((Eq.mp (propext (mem_primitiveRoots hazero) ▸ Eq.refl (x ∈ primitiveRoots a R))
                              ha).pow_eq_one ▸
                          Eq.refl ((x ^ a) ^ d = 1)))
                      (Eq.mpr (id (one_pow d ▸ Eq.refl (1 ^ d = 1))) (Eq.refl 1)))))
      (le_of_eq
        (Eq.mpr
          (id
            (card_nthRootsFinset h ▸
              Eq.refl
                (card (nthRootsFinset (↑n) R) = card (Finset.biUnion (Nat.divisors ↑n) fun i ↦ primitiveRoots i R))))
          (Eq.mpr
            (id
              ((card_biUnion fun i a j a hdiff ↦ disjoint hdiff) ▸
                Eq.refl (↑n = card (Finset.biUnion (Nat.divisors ↑n) fun i ↦ primitiveRoots i R))))
            (Eq.mpr (id ((Nat.sum_totient ↑n).symm ▸ Eq.refl (↑n = ∑ u in Nat.divisors ↑n, card (primitiveRoots u R))))
              (sum_congr rfl
                (Eq.mpr
                  (id
                    (forall_congr fun x ↦
                      implies_congr «lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.36
                        (Eq.refl (φ x = card (primitiveRoots x R)))))
                  fun k a ↦
                  And.casesOn a fun left right ↦
                    Exists.casesOn left fun d hd ↦
                      Eq.mpr
                        (id
                          (card_primitiveRoots (pow (PNat.pos n) h (Eq.mp (mul_comm k d ▸ Eq.refl (↑n = k * d)) hd)) ▸
                            Eq.refl (φ k = card (primitiveRoots k R))))
                        (Eq.refl (φ k))))))))).symm

1.命题描述：
  theorem nthRoots_one_eq_biUnion_primitiveRoots' {ζ : R} {n : ℕ+} (h : IsPrimitiveRoot ζ n) :
    nthRootsFinset n R = (Nat.divisors ↑n).biUnion fun i => primitiveRoots i R
2.IsPrimitiveRoot ζ n：ζ是本原的n-单位根；换句话说，ζ能生成所有的n-复数单位根。
3.nthRootsFinset n R：表示x^n=1 这个方程的所有复数根的集合。
  即e^(i2kπ/n)，k=1,2,3,4...。由于循环其实就只有n个。
4.primitiveRoots i R：指的是3中的集合（这里记为A）里面，是本原的那些元素；
  换句话说，能通过复合（自我相乘）生成集合A所有元素的那些元素。
5.(Nat.divisors n)：指的是n的所有因子的集合B。
6.(Nat.divisors ↑n).biUnion fun i => primitiveRoots i R：是3个新集合C1,C2,C3并集的结果。
    整个的意思是首先也是5中的集合B，
    对于B中所有元素比如有{b1,b2,b3},
    都通过映射fun i => primitiveRoots i R，各得到一个集合，共3个集合C1,C2,C3。
    将3个新集合C1,C2,C3并集结果。
证明阶段：
7.eq_of_subset_of_card_le反推法，只需2个条件：1.集合被别的包含，2.但是元素个数不小于别的。
  7.1.集合被别的包含：
    1.intro x 取出任意一个元素
    2.
  7.2.但是元素个数不小于别的：
