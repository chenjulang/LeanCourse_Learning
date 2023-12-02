// Lean compiler output
// Module: LeanCourse.MIL.C06_Structures.solutions.Solutions_S03_Building_the_Gaussian_Integers
// Imports: Init Mathlib.Data.Int.Basic Mathlib.Algebra.EuclideanDomain.Basic Mathlib.RingTheory.PrincipalIdealDomain LeanCourse.Common
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_gaussInt_instCommRing___closed__4;
LEAN_EXPORT lean_object* l_gaussInt_instCommRing___lambda__2(lean_object*, lean_object*);
static lean_object* l_gaussInt_instCommRing___closed__6;
LEAN_EXPORT lean_object* l_Nat_cast___at_gaussInt_instCommRing___spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_norm___boxed(lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instCommRing___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_unaryCast___at_gaussInt_instCommRing___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instMulGaussInt___boxed(lean_object*, lean_object*);
static lean_object* l_npowRec___at_gaussInt_instCommRing___spec__3___closed__1;
lean_object* l_Int_emod(lean_object*, lean_object*);
static lean_object* l_gaussInt_instCommRing___closed__11;
LEAN_EXPORT lean_object* l_gaussInt_instEuclideanDomainGaussInt___lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l_gaussInt_instCommRing___closed__8;
LEAN_EXPORT lean_object* l_nsmulRec___at_gaussInt_instCommRing___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instOneGaussInt;
LEAN_EXPORT lean_object* l_gaussInt_instCommRing___lambda__2___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instEuclideanDomainGaussInt___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_gaussInt_instEuclideanDomainGaussInt___closed__3;
static lean_object* l_gaussInt_instZeroGaussInt___closed__2;
lean_object* l_Int_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_gaussInt_instCommRing___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_zsmulRec___at_gaussInt_instCommRing___spec__5(lean_object*, lean_object*);
static lean_object* l_gaussInt_instOneGaussInt___closed__1;
static lean_object* l_gaussInt_instCommRing___closed__7;
static lean_object* l_gaussInt_instCommRing___closed__13;
LEAN_EXPORT lean_object* l_zsmulRec___at_gaussInt_instCommRing___spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_unaryCast___at_gaussInt_instCommRing___spec__2___boxed(lean_object*);
static lean_object* l_gaussInt_instEuclideanDomainGaussInt___closed__2;
LEAN_EXPORT lean_object* l_gaussInt_instEuclideanDomainGaussInt___lambda__1(lean_object*, lean_object*);
static lean_object* l_gaussInt_instCommRing___closed__12;
LEAN_EXPORT lean_object* l_gaussInt_instCommRing___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instNegGaussInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instCommRing___lambda__3(lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instAddGaussInt(lean_object*, lean_object*);
static lean_object* l_gaussInt_instCommRing___closed__10;
LEAN_EXPORT lean_object* l_gaussInt_instDivGaussInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_npowRec___at_gaussInt_instCommRing___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_nsmulRec___at_gaussInt_instCommRing___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_mod_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instAddGaussInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_div_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instModGaussInt(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_object* l_gaussInt_instOneGaussInt___closed__2;
static lean_object* l_gaussInt_instCommRing___closed__3;
LEAN_EXPORT lean_object* l_gaussInt_instCommRing;
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
static lean_object* l_Int_div_x27___closed__1;
LEAN_EXPORT lean_object* l_gaussInt_norm(lean_object*);
LEAN_EXPORT lean_object* l_Int_div_x27(lean_object*, lean_object*);
static lean_object* l_gaussInt_instCommRing___closed__9;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_gaussInt_instCommRing___closed__5;
LEAN_EXPORT lean_object* l_npowRec___at_gaussInt_instCommRing___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instMulGaussInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instNegGaussInt(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_mod_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instDivGaussInt___boxed(lean_object*, lean_object*);
static lean_object* l_gaussInt_instEuclideanDomainGaussInt___closed__1;
static lean_object* l_gaussInt_instCommRing___closed__2;
LEAN_EXPORT lean_object* l_SubNegMonoid_sub_x27___at_gaussInt_instCommRing___spec__4___boxed(lean_object*, lean_object*);
static lean_object* l_gaussInt_instZeroGaussInt___closed__1;
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_SubNegMonoid_sub_x27___at_gaussInt_instCommRing___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instEuclideanDomainGaussInt;
LEAN_EXPORT lean_object* l_gaussInt_instModGaussInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instCommRing___lambda__3___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_conj(lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instEuclideanDomainGaussInt___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_gaussInt_instZeroGaussInt;
static lean_object* l_gaussInt_instCommRing___closed__1;
LEAN_EXPORT lean_object* l_Int_castDef___at_gaussInt_instCommRing___spec__6(lean_object*);
static lean_object* _init_l_gaussInt_instZeroGaussInt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_gaussInt_instZeroGaussInt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_gaussInt_instZeroGaussInt___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_gaussInt_instZeroGaussInt() {
_start:
{
lean_object* x_1; 
x_1 = l_gaussInt_instZeroGaussInt___closed__2;
return x_1;
}
}
static lean_object* _init_l_gaussInt_instOneGaussInt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_gaussInt_instOneGaussInt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_gaussInt_instOneGaussInt___closed__1;
x_2 = l_gaussInt_instZeroGaussInt___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_gaussInt_instOneGaussInt() {
_start:
{
lean_object* x_1; 
x_1 = l_gaussInt_instOneGaussInt___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instAddGaussInt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_add(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_int_add(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instAddGaussInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_gaussInt_instAddGaussInt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instNegGaussInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_int_neg(x_2);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_int_neg(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instNegGaussInt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_gaussInt_instNegGaussInt(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instMulGaussInt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_mul(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_int_mul(x_6, x_7);
x_9 = lean_int_sub(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
x_10 = lean_int_mul(x_3, x_7);
x_11 = lean_int_mul(x_6, x_4);
x_12 = lean_int_add(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instMulGaussInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_gaussInt_instMulGaussInt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_nsmulRec___at_gaussInt_instCommRing___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = l_nsmulRec___at_gaussInt_instCommRing___spec__1(x_6, x_2);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_int_add(x_8, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_int_add(x_11, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_gaussInt_instZeroGaussInt___closed__2;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Nat_unaryCast___at_gaussInt_instCommRing___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = l_Nat_unaryCast___at_gaussInt_instCommRing___spec__2(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_gaussInt_instOneGaussInt___closed__1;
x_9 = lean_int_add(x_7, x_8);
lean_dec(x_7);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_gaussInt_instZeroGaussInt___closed__1;
x_12 = lean_int_add(x_10, x_11);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_gaussInt_instZeroGaussInt___closed__2;
return x_14;
}
}
}
static lean_object* _init_l_npowRec___at_gaussInt_instCommRing___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_gaussInt_instOneGaussInt___closed__1;
x_2 = l_gaussInt_instZeroGaussInt___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_npowRec___at_gaussInt_instCommRing___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = l_npowRec___at_gaussInt_instCommRing___spec__3(x_6, x_2);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_int_mul(x_8, x_9);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_int_mul(x_11, x_12);
x_14 = lean_int_sub(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
x_15 = lean_int_mul(x_8, x_12);
lean_dec(x_12);
x_16 = lean_int_mul(x_11, x_9);
lean_dec(x_9);
x_17 = lean_int_add(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_npowRec___at_gaussInt_instCommRing___spec__3___closed__1;
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_SubNegMonoid_sub_x27___at_gaussInt_instCommRing___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_int_neg(x_3);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_int_neg(x_5);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_int_add(x_7, x_4);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_int_add(x_9, x_6);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_zsmulRec___at_gaussInt_instCommRing___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_gaussInt_instZeroGaussInt___closed__1;
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_nat_abs(x_1);
lean_dec(x_1);
x_6 = l_nsmulRec___at_gaussInt_instCommRing___spec__1(x_5, x_2);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_nat_abs(x_1);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = lean_nat_add(x_9, x_8);
lean_dec(x_9);
x_11 = l_nsmulRec___at_gaussInt_instCommRing___spec__1(x_10, x_2);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_int_neg(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_int_neg(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_gaussInt_instCommRing___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_unaryCast___at_gaussInt_instCommRing___spec__2(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_castDef___at_gaussInt_instCommRing___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_gaussInt_instZeroGaussInt___closed__1;
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_abs(x_1);
lean_dec(x_1);
x_5 = l_Nat_unaryCast___at_gaussInt_instCommRing___spec__2(x_4);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_nat_abs(x_1);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = lean_nat_add(x_8, x_7);
lean_dec(x_8);
x_10 = l_Nat_unaryCast___at_gaussInt_instCommRing___spec__2(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_int_neg(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_int_neg(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_gaussInt_instCommRing___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_add(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_int_add(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instCommRing___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_mul(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_int_mul(x_6, x_7);
x_9 = lean_int_sub(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
x_10 = lean_int_mul(x_3, x_7);
x_11 = lean_int_mul(x_6, x_4);
x_12 = lean_int_add(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instCommRing___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_int_neg(x_2);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_int_neg(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_gaussInt_instCommRing___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_nsmulRec___at_gaussInt_instCommRing___spec__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_gaussInt_instCommRing___closed__1;
x_2 = l_gaussInt_instZeroGaussInt___closed__2;
x_3 = l_gaussInt_instCommRing___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_gaussInt_instCommRing___lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_gaussInt_instCommRing___closed__3;
x_2 = l_gaussInt_instCommRing___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_unaryCast___at_gaussInt_instCommRing___spec__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_npowRec___at_gaussInt_instCommRing___spec__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_gaussInt_instCommRing___closed__5;
x_2 = l_npowRec___at_gaussInt_instCommRing___spec__3___closed__1;
x_3 = l_gaussInt_instCommRing___closed__6;
x_4 = l_gaussInt_instCommRing___closed__7;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_gaussInt_instCommRing___lambda__3___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_SubNegMonoid_sub_x27___at_gaussInt_instCommRing___spec__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_zsmulRec___at_gaussInt_instCommRing___spec__5___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_castDef___at_gaussInt_instCommRing___spec__6), 1, 0);
return x_1;
}
}
static lean_object* _init_l_gaussInt_instCommRing___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_gaussInt_instCommRing___closed__8;
x_2 = l_gaussInt_instCommRing___closed__9;
x_3 = l_gaussInt_instCommRing___closed__10;
x_4 = l_gaussInt_instCommRing___closed__11;
x_5 = l_gaussInt_instCommRing___closed__12;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_gaussInt_instCommRing() {
_start:
{
lean_object* x_1; 
x_1 = l_gaussInt_instCommRing___closed__13;
return x_1;
}
}
LEAN_EXPORT lean_object* l_nsmulRec___at_gaussInt_instCommRing___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_nsmulRec___at_gaussInt_instCommRing___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_unaryCast___at_gaussInt_instCommRing___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_unaryCast___at_gaussInt_instCommRing___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_npowRec___at_gaussInt_instCommRing___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_npowRec___at_gaussInt_instCommRing___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_SubNegMonoid_sub_x27___at_gaussInt_instCommRing___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_SubNegMonoid_sub_x27___at_gaussInt_instCommRing___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_zsmulRec___at_gaussInt_instCommRing___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_zsmulRec___at_gaussInt_instCommRing___spec__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_gaussInt_instCommRing___spec__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_cast___at_gaussInt_instCommRing___spec__7(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instCommRing___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_gaussInt_instCommRing___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instCommRing___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_gaussInt_instCommRing___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instCommRing___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_gaussInt_instCommRing___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_div_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_div_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Int_div_x27___closed__1;
x_4 = l_Int_ediv(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
x_6 = l_Int_ediv(x_5, x_2);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int_div_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_div_x27(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_mod_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Int_div_x27___closed__1;
x_4 = l_Int_ediv(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
x_6 = l_Int_emod(x_5, x_2);
lean_dec(x_5);
x_7 = lean_int_sub(x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_mod_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_mod_x27(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_gaussInt_norm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Int_pow(x_2, x_3);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Int_pow(x_5, x_3);
x_7 = lean_int_add(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_gaussInt_norm___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_gaussInt_norm(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_gaussInt_conj(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_int_neg(x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_int_neg(x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_gaussInt_instDivGaussInt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_2);
x_3 = l_gaussInt_conj(x_2);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_int_mul(x_4, x_5);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_int_mul(x_7, x_8);
x_10 = lean_int_sub(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_11 = lean_int_mul(x_4, x_8);
lean_dec(x_8);
x_12 = lean_int_mul(x_7, x_5);
lean_dec(x_5);
x_13 = lean_int_add(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_gaussInt_norm(x_2);
lean_dec(x_2);
x_15 = l_Int_div_x27(x_10, x_14);
lean_dec(x_10);
x_16 = l_Int_div_x27(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instDivGaussInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_gaussInt_instDivGaussInt(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instModGaussInt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_2);
x_3 = l_gaussInt_conj(x_2);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_int_mul(x_4, x_5);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_int_mul(x_7, x_8);
x_10 = lean_int_sub(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_11 = lean_int_mul(x_4, x_8);
lean_dec(x_8);
x_12 = lean_int_mul(x_7, x_5);
x_13 = lean_int_add(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_gaussInt_norm(x_2);
x_15 = l_Int_div_x27(x_10, x_14);
lean_dec(x_10);
x_16 = l_Int_div_x27(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_17 = lean_int_mul(x_5, x_15);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_int_mul(x_18, x_16);
x_20 = lean_int_sub(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = lean_int_mul(x_5, x_16);
lean_dec(x_16);
lean_dec(x_5);
x_22 = lean_int_mul(x_18, x_15);
lean_dec(x_15);
lean_dec(x_18);
x_23 = lean_int_add(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_SubNegMonoid_sub_x27___at_gaussInt_instCommRing___spec__4(x_1, x_24);
lean_dec(x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instModGaussInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_gaussInt_instModGaussInt(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instEuclideanDomainGaussInt___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_2);
x_3 = l_gaussInt_conj(x_2);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_int_mul(x_4, x_5);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_int_mul(x_7, x_8);
x_10 = lean_int_sub(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_11 = lean_int_mul(x_4, x_8);
lean_dec(x_8);
x_12 = lean_int_mul(x_7, x_5);
lean_dec(x_5);
x_13 = lean_int_add(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_gaussInt_norm(x_2);
lean_dec(x_2);
x_15 = l_Int_div_x27(x_10, x_14);
lean_dec(x_10);
x_16 = l_Int_div_x27(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instEuclideanDomainGaussInt___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_2);
x_3 = l_gaussInt_conj(x_2);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_int_mul(x_4, x_5);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_int_mul(x_7, x_8);
x_10 = lean_int_sub(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_11 = lean_int_mul(x_4, x_8);
lean_dec(x_8);
x_12 = lean_int_mul(x_7, x_5);
x_13 = lean_int_add(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_gaussInt_norm(x_2);
x_15 = l_Int_div_x27(x_10, x_14);
lean_dec(x_10);
x_16 = l_Int_div_x27(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_17 = lean_int_mul(x_5, x_15);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_int_mul(x_18, x_16);
x_20 = lean_int_sub(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = lean_int_mul(x_5, x_16);
lean_dec(x_16);
lean_dec(x_5);
x_22 = lean_int_mul(x_18, x_15);
lean_dec(x_15);
lean_dec(x_18);
x_23 = lean_int_add(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_SubNegMonoid_sub_x27___at_gaussInt_instCommRing___spec__4(x_1, x_24);
lean_dec(x_24);
return x_25;
}
}
static lean_object* _init_l_gaussInt_instEuclideanDomainGaussInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_gaussInt_instEuclideanDomainGaussInt___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_gaussInt_instEuclideanDomainGaussInt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_gaussInt_instEuclideanDomainGaussInt___lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_gaussInt_instEuclideanDomainGaussInt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_gaussInt_instCommRing;
x_2 = l_gaussInt_instEuclideanDomainGaussInt___closed__1;
x_3 = l_gaussInt_instEuclideanDomainGaussInt___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_gaussInt_instEuclideanDomainGaussInt() {
_start:
{
lean_object* x_1; 
x_1 = l_gaussInt_instEuclideanDomainGaussInt___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instEuclideanDomainGaussInt___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_gaussInt_instEuclideanDomainGaussInt___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_gaussInt_instEuclideanDomainGaussInt___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_gaussInt_instEuclideanDomainGaussInt___lambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Int_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_EuclideanDomain_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_RingTheory_PrincipalIdealDomain(uint8_t builtin, lean_object*);
lean_object* initialize_LeanCourse_Common(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanCourse_MIL_C06__Structures_solutions_Solutions__S03__Building__the__Gaussian__Integers(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Int_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_EuclideanDomain_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_RingTheory_PrincipalIdealDomain(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanCourse_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_gaussInt_instZeroGaussInt___closed__1 = _init_l_gaussInt_instZeroGaussInt___closed__1();
lean_mark_persistent(l_gaussInt_instZeroGaussInt___closed__1);
l_gaussInt_instZeroGaussInt___closed__2 = _init_l_gaussInt_instZeroGaussInt___closed__2();
lean_mark_persistent(l_gaussInt_instZeroGaussInt___closed__2);
l_gaussInt_instZeroGaussInt = _init_l_gaussInt_instZeroGaussInt();
lean_mark_persistent(l_gaussInt_instZeroGaussInt);
l_gaussInt_instOneGaussInt___closed__1 = _init_l_gaussInt_instOneGaussInt___closed__1();
lean_mark_persistent(l_gaussInt_instOneGaussInt___closed__1);
l_gaussInt_instOneGaussInt___closed__2 = _init_l_gaussInt_instOneGaussInt___closed__2();
lean_mark_persistent(l_gaussInt_instOneGaussInt___closed__2);
l_gaussInt_instOneGaussInt = _init_l_gaussInt_instOneGaussInt();
lean_mark_persistent(l_gaussInt_instOneGaussInt);
l_npowRec___at_gaussInt_instCommRing___spec__3___closed__1 = _init_l_npowRec___at_gaussInt_instCommRing___spec__3___closed__1();
lean_mark_persistent(l_npowRec___at_gaussInt_instCommRing___spec__3___closed__1);
l_gaussInt_instCommRing___closed__1 = _init_l_gaussInt_instCommRing___closed__1();
lean_mark_persistent(l_gaussInt_instCommRing___closed__1);
l_gaussInt_instCommRing___closed__2 = _init_l_gaussInt_instCommRing___closed__2();
lean_mark_persistent(l_gaussInt_instCommRing___closed__2);
l_gaussInt_instCommRing___closed__3 = _init_l_gaussInt_instCommRing___closed__3();
lean_mark_persistent(l_gaussInt_instCommRing___closed__3);
l_gaussInt_instCommRing___closed__4 = _init_l_gaussInt_instCommRing___closed__4();
lean_mark_persistent(l_gaussInt_instCommRing___closed__4);
l_gaussInt_instCommRing___closed__5 = _init_l_gaussInt_instCommRing___closed__5();
lean_mark_persistent(l_gaussInt_instCommRing___closed__5);
l_gaussInt_instCommRing___closed__6 = _init_l_gaussInt_instCommRing___closed__6();
lean_mark_persistent(l_gaussInt_instCommRing___closed__6);
l_gaussInt_instCommRing___closed__7 = _init_l_gaussInt_instCommRing___closed__7();
lean_mark_persistent(l_gaussInt_instCommRing___closed__7);
l_gaussInt_instCommRing___closed__8 = _init_l_gaussInt_instCommRing___closed__8();
lean_mark_persistent(l_gaussInt_instCommRing___closed__8);
l_gaussInt_instCommRing___closed__9 = _init_l_gaussInt_instCommRing___closed__9();
lean_mark_persistent(l_gaussInt_instCommRing___closed__9);
l_gaussInt_instCommRing___closed__10 = _init_l_gaussInt_instCommRing___closed__10();
lean_mark_persistent(l_gaussInt_instCommRing___closed__10);
l_gaussInt_instCommRing___closed__11 = _init_l_gaussInt_instCommRing___closed__11();
lean_mark_persistent(l_gaussInt_instCommRing___closed__11);
l_gaussInt_instCommRing___closed__12 = _init_l_gaussInt_instCommRing___closed__12();
lean_mark_persistent(l_gaussInt_instCommRing___closed__12);
l_gaussInt_instCommRing___closed__13 = _init_l_gaussInt_instCommRing___closed__13();
lean_mark_persistent(l_gaussInt_instCommRing___closed__13);
l_gaussInt_instCommRing = _init_l_gaussInt_instCommRing();
lean_mark_persistent(l_gaussInt_instCommRing);
l_Int_div_x27___closed__1 = _init_l_Int_div_x27___closed__1();
lean_mark_persistent(l_Int_div_x27___closed__1);
l_gaussInt_instEuclideanDomainGaussInt___closed__1 = _init_l_gaussInt_instEuclideanDomainGaussInt___closed__1();
lean_mark_persistent(l_gaussInt_instEuclideanDomainGaussInt___closed__1);
l_gaussInt_instEuclideanDomainGaussInt___closed__2 = _init_l_gaussInt_instEuclideanDomainGaussInt___closed__2();
lean_mark_persistent(l_gaussInt_instEuclideanDomainGaussInt___closed__2);
l_gaussInt_instEuclideanDomainGaussInt___closed__3 = _init_l_gaussInt_instEuclideanDomainGaussInt___closed__3();
lean_mark_persistent(l_gaussInt_instEuclideanDomainGaussInt___closed__3);
l_gaussInt_instEuclideanDomainGaussInt = _init_l_gaussInt_instEuclideanDomainGaussInt();
lean_mark_persistent(l_gaussInt_instEuclideanDomainGaussInt);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
