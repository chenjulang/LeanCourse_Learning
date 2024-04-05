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

定理相当于冯克勤的P.132 (6)
938-1161 拆解后从里往外看定理就行云流水了。形式化数学的魅力和优点：将学习已知数学的学习曲线无限拉平。
z^n = 1
e^(ix) = cos(x) + isin(x)
z = e^(i2k₂π/n) k₂=1,2,3,4...

n=3的复数根： e^(i2π/3)，e^(i4π/3)，e^(i2π)=e^(0)=1
//
n=1的本原根：e^(i2π)=1
n=3的本原根：e^(i2π/3)，e^(i4π/3)

n=4的复数根： e^(i2π/4)，e^(i4π/4)=e^(iπ)，e^(i6π/4), e^(i2π)=1
//
n=1的本原根：e^(i2π)=1
n=2的本原根：e^(i2π/2)=e^(iπ)
n=4的本原根：e^(i2π/4) , e^(i6π/4)





1.命题描述：
  theorem nthRoots_one_eq_biUnion_primitiveRoots' {ζ : R} {n : ℕ+} (h : IsPrimitiveRoot ζ n) :
    nthRootsFinset n R = (Nat.divisors ↑n).biUnion fun i => primitiveRoots i R
2.IsPrimitiveRoot ζ n：ζ是本原的n-单位根；换句话说，ζ能生成所有的n-复数单位根。
3.nthRootsFinset n R：表示x^n=1 这个方程的所有复数根的集合。
  即e^(i2kπ/n)，k=1,2,3,4...。由于循环其实就只有n个。
4.primitiveRoots i R：指的是"3."中的集合（这里记为A）里面，是本原的那些元素；
  换句话说，能通过复合（自我相乘）生成集合A所有元素的那些元素。
5.(Nat.divisors n)：指的是n的所有因子的集合B。
6.(Nat.divisors ↑n).biUnion fun i => primitiveRoots i R：是3个新集合C1,C2,C3并集的结果。
    整个的意思是首先B也是"5."中的集合B，
    对于B中所有元素比如有{b1,b2,b3},
    都通过映射fun i => primitiveRoots i R，各得到一个本原根集合，共3个集合C1,C2,C3。
    将3个新集合C1,C2,C3并集结果。
证明阶段：
7.eq_of_subset_of_card_le反推法，只需2个条件：1.s ⊆ t，2.s元素个数不小于t的。
  7.1 s ⊆ t：
    1.intro x 取出任意一个元素
    2.
  7.2 但是元素个数不小于别的：



theorem My_nthRoots_one_eq_biUnion_primitiveRoots' {ζ : R} {n : ℕ+} (h : IsPrimitiveRoot ζ n) :
    nthRootsFinset n R = (Nat.divisors ↑n).biUnion fun i => primitiveRoots i R
  := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x
    apply id
    apply Eq.mpr
    have h1:= (id
      (implies_congr (Eq.refl (x ∈ Finset.biUnion (Nat.divisors ↑n) fun i ↦ primitiveRoots i R))
        (congrArg (Membership.mem x) (Multiset.toFinset_eq (nthRoots_nodup h)).symm)))
    have auxlemma_34 : (x ∈ Finset.biUnion (Nat.divisors ↑n) fun i ↦ primitiveRoots i R) = ∃ a ∈ Nat.divisors ↑n, x ∈ primitiveRoots a R
      := by sorry
    have auxlemma_36 : ∀ {n m : ℕ}, (n ∈ Nat.divisors m) = (n ∣ m ∧ m ≠ 0)
      := by sorry
    have auxlemma_38 : ∀ (n : ℕ+), ( ((n:ℕ) = 0) = False)
      := by simp only [PNat.ne_zero, forall_const]
    -- have auxlemma_38_n := auxlemma_38 n -- 最终符合的是长这样的，
    -- have auxlemma_38_n : (¬(n : ℕ) = 0) = ¬False := by simp only [PNat.ne_zero,
    --   not_false_eq_true] -- 不报错，但不是想要的
    -- have test38: ∀ (n : ℕ+), (n = 0) = False -- 注意：这样写会报错:failed to synthesize instance
    -- have test38 (n : ℕ+) : (n : ℕ) ≠ 0 := n.2.ne' -- 这样写不会
    -- have test38 : ∀ (n : ℕ+), (n:ℕ) = 0 = False -- 这样也不会。总结就是：缺了条件,就报错failed to synthesize
    have auxlemma_40 : (¬False) = True
      := by simp only
    have auxlemma_37 : ∀ (p : Prop), (p ∧ True) = p
      := by simp only [and_true, forall_const]
    have auxlemma_28
    : ∀ {α : Type u_4} {a : α} {s : Multiset α} {nd : Multiset.Nodup s}, (@Membership.mem α (Finset α) instMembershipFinset a { val := s, nodup := nd } ) = (a ∈ s)  -- invalid notion {} 是因为缺少一些前缀，信息不详细
      := by simp only [mem_mk, implies_true, forall_const]
    -- (Multiset.toFinset_eq (nthRoots_nodup h)).symm
        -- ∀ {α : Type u_4} {a : α} {s : Multiset α} {nd : Multiset.Nodup s}, (a ∈ { val := s, nodup := nd }) = (a ∈ s)
          -- := by sorry
    have auxlemma_35: ∀ {R : Type u_4} [inst : CommRing R] [inst_2 : IsDomain R] {n : ℕ},
      0 < n → ∀ {a x : R}, (x ∈ nthRoots n a) = (x ^ n = a)
      := by
      simp only [eq_iff_iff]
      exact fun {R} [CommRing R] [IsDomain R] {n} a {a_1 x} ↦ mem_nthRoots a
    have auxlemma_39: ∀ (n : ℕ+), (0 < (n:ℕ )) = True
      := by simp only [PNat.pos, forall_const]
    have auxlemma_41 : ∀ {α : Type} [inst : CanonicallyOrderedAddCommMonoid α] {a : α}, (a ≤ 0) = (a = 0)
      := by simp only [nonpos_iff_eq_zero, forall_const, implies_true]

    -- 注意：分析print的时候，会发现有些参数可能是原证明中没出现的，要记下来，比如auxlemma_35'后面的"1 x"
    -- have testaaa1 := (of_eq_true (auxlemma_39 n)) -- : 0 < ↑n
    -- have testaaa2 := @auxlemma_35 R _ _ _ (of_eq_true (auxlemma_39 n)) -- : ∀ {a x : R}, (x ∈ nthRoots (↑n) a) = (x ^ ↑n = a)
    have auxlemma_35'_39 := @auxlemma_35 R _ _ _ (of_eq_true (auxlemma_39 n)) 1 x-- 注意：typeclass instance problem is stuck: 用全参数@来解决，要自动推断的写个“_”即可
    have auxlemma_28' := @auxlemma_28 R x (nthRoots (↑n) 1) (nthRoots_nodup h)
    -- @Eq.trans -- 验证:不用
    -- Prop  -- 验证:不用
    -- (x ∈ { val := nthRoots (↑n) 1, nodup := nthRoots_nodup h })  -- 验证:不用
    -- (x ∈ nthRoots (↑n) 1)  -- 验证:不用
    -- (x ^ ↑n = 1)  -- 验证:不用
    -- «lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.28 -- 验证：: (x ∈ { val := nthRoots (↑n) 1, nodup := (_ : Multiset.Nodup (nthRoots (↑n) 1)) }) = (x ∈ nthRoots (↑n) 1)，就是已知的auxlemma_28'
    -- («lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.35 -- 验证: (x ∈ nthRoots (↑n) 1) = (x ^ ↑n = 1)，也就是已知的auxlemma_35'_39
      -- (of_eq_true («lake-packages».mathlib.Mathlib.RingTheory.RootsOfUnity.Basic._auxLemma.39 n)))
    -- : (x ∈ { val := nthRoots (↑n) 1, nodup := (_ : Multiset.Nodup (nthRoots (↑n) 1)) }) = (x ^ ↑n = 1)
    have testaaa3 := @Eq.trans Prop
      (@Membership.mem R (Finset R) instMembershipFinset x { val := nthRoots (↑n) 1, nodup := @nthRoots_nodup R _ _ ζ (↑n) h }) -- 报错inst : inst全部替换成_即可
      (x ∈ nthRoots (↑n) 1)
      (@Eq R (@HPow.hPow R ℕ R instHPow x ↑n) 1 ) -- 报错就参照print信息写详细。
      auxlemma_28'
      auxlemma_35'_39
    have h2:=
      (Eq.mpr
        (id
          (implies_congr
            (auxlemma_34.trans
              (congrArg Exists
                (_root_.funext fun a ↦
                  congrFun
                    (congrArg And
                      ((auxlemma_36.trans
                            (congrArg (And (a ∣ ↑n))
                              ((congrArg Not (auxlemma_38 n)).trans -- 报错：function expected at , 是因为引理auxlemma_38写错了，少了很多括号，有括号请多写括号。
                                auxlemma_40))).trans
                        (auxlemma_37 (a ∣ ↑n))))
                    (x ∈ primitiveRoots a R))))
            (auxlemma_28.trans auxlemma_35'_39)))
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
                                    (Eq.mp auxlemma_41
                                      ha0)))
                                d).trans
                            (zero_mul d))))
                      (PNat.ne_zero n))
                  hd;
              Eq.mpr (id (hd ▸ Eq.refl (x ^ ↑n = 1)))
                (Eq.mpr (id (pow_mul x a d ▸ Eq.refl (x ^ (a * d) = 1)))
                  (Eq.mpr
                    (id
                      ((Eq.mp (propext (mem_primitiveRoots hazero) ▸ Eq.refl (x ∈ primitiveRoots a R)) ha).pow_eq_one ▸
                        Eq.refl ((x ^ a) ^ d = 1)))
                    (Eq.mpr (id (one_pow d ▸ Eq.refl (1 ^ d = 1))) (Eq.refl 1)))))

  · apply le_of_eq
    rw [h.card_nthRootsFinset, Finset.card_biUnion]
    · nth_rw 1 [← Nat.sum_totient n]
      refine' sum_congr rfl _
      simp only [Nat.mem_divisors]
      rintro k ⟨⟨d, hd⟩, -⟩
      rw [mul_comm] at hd
      rw [(h.pow n.pos hd).card_primitiveRoots]
    · intro i _ j _ hdiff
      exact disjoint hdiff
#print nthRoots_one_eq_biUnion_primitiveRoots'



正在处理：

-- 原证明：
exact (Eq.mpr

  (id
    (implies_congr

      (auxlemma_34.trans --
        (congrArg Exists
          (_root_.funext fun a ↦
            congrFun
              (congrArg And
                ((auxlemma_36.trans
                      (congrArg (And (a ∣ ↑n))
                        ((congrArg Not (auxlemma_38 n)).trans -- 报错：function expected at , 是因为引理auxlemma_38写错了，少了很多括号，有括号请多写括号。
                          auxlemma_40))).trans
                  (auxlemma_37 (a ∣ ↑n))))
              (x ∈ primitiveRoots a R))))

      (auxlemma_28.trans auxlemma_35'_39)) --

  )

  fun a ↦ --

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
                              (Eq.mp auxlemma_41
                                ha0)))
                          d).trans
                      (zero_mul d))))
                (PNat.ne_zero n))
            hd;
        let ha2 := @Eq.ndrec ℕ (↑n) (fun _a ↦ (@HPow.hPow R ℕ R instHPow x ↑n = 1) = (x ^ _a = 1)) (Eq.refl (@HPow.hPow R ℕ R instHPow x ↑n = 1)) (a * d) hd
        -- have ha2_2 : ((@HPow.hPow R ℕ R instHPow x ↑n = 1) = ((x ^ a) ^ d = 1)) ↔ ((fun _a ↦ (@HPow.hPow R ℕ R instHPow x ↑n = 1) = (x ^ _a = 1)) (a * d))
        --   := by
        --   constructor
        --   · intro eq1
        --     simp only [eq_iff_iff]
        --     rw [hd]
        --   · intro eq2
        --     rw [hd]
        --     rw [pow_mul]
        --   done
        -- Eq.mpr (id (@Eq.ndrec ℕ (↑n) (fun _a ↦ (x ^ ↑n = 1) = (x ^ _a = 1)) (Eq.refl (x ^ ↑n = 1)) (a * d) hd)) -- type mismatch
        let ha3 := @Eq.ndrec R (x ^ (a * d)) (fun _a ↦ (x ^ (a * d) = 1) = (_a = 1)) (Eq.refl (x ^ (a * d) = 1)) ((x ^ a) ^ d) (pow_mul x a d)
        let ha4 := @mem_primitiveRoots R a _ _ x hazero
        let ha5: IsPrimitiveRoot x a := by exact isPrimitiveRoot_of_mem_primitiveRoots ha
        let ha6_1 := @Eq.refl Prop ((x ^ a) ^ d = 1)
        -- let ha6 := @id (((x ^ a) ^ d = 1) = (1 ^ d = 1)) ((Eq.mp (propext ha4 ▸ Eq.refl (x ∈ primitiveRoots a R)) ha5).pow_eq_one ▸ Eq.refl ((x ^ a) ^ d = 1))
        let ha7_1 : (1 ^ d = 1) = (1 ^ d = 1) := (@Eq.refl Prop (1 ^ d = 1))
        -- let ha7 := @Eq.ndrec R (1 ^ d) (fun _a ↦ (1 ^ d = 1) = (_a = 1)) ha7_1 1 (one_pow d)
        let ha8 := @Eq.refl Prop ((x ^ a) ^ d = 1)
        -- let ha8':  ((x ^ a) ^ d = 1) = ((x ^ a) ^ d = 1) :=
        let ha9 := (@Eq.ndrec R (x ^ a) (fun _a ↦ ((x ^ a) ^ d = 1) = (_a ^ d = 1)) (Eq.refl ((x ^ a) ^ d = 1)) 1
                  (Eq.mp (@Eq.ndrec Prop (x ∈ primitiveRoots a R) (fun _a ↦ (x ∈ primitiveRoots a R) = _a) (Eq.refl (x ∈ primitiveRoots a R))
                    (IsPrimitiveRoot x a) (propext (mem_primitiveRoots hazero))) ha).pow_eq_one)
        let ha10:(1 ^ d = 1) = (1 ^ d = 1) := (@Eq.refl Prop (1 ^ d = 1))
        -- has type
        --   (1 ^ d = 1) = (1 ^ d = 1) : Prop
        -- but is expected to have type
        --   (1 ^ d = 1) = (1 ^ d = 1) : Prop -- 相同的type却出错了？
        Eq.mpr (id ha2) -- what? 替换简称就解决了？应该只是因为没写详细的问题。
          (Eq.mpr (id ha3)
            (Eq.mpr
            -- todo 这里开始出错：
              (
                @id (((x ^ a) ^ d = 1) = (1 ^ d = 1))
                ha9
              )
                -- ha4: typeclass instance problem is stuck, it is often due to metavariables  IsDomain ?m.3928398
                -- ha: application type mismatch ,  IsPrimitiveRoot x a 和 x ∈ primitiveRoots a R 同一个意思也要我写一下，服了～～
              (Eq.mpr (id (@Eq.ndrec R (1 ^ d) (fun _a ↦ (1 ^ d = 1) = (_a = 1)) (ha10) 1 (one_pow d))) (Eq.refl 1)))
          )

)
